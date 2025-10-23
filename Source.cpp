// Integrated JMA Nowcast and GSI Map Viewer
// - Combines GSI map rendering (fractional zoom, Japan bounds)
// - With JMA Nowcast overlay (time step, animation, async download/cache)
//
// Build: /DUNICODE /D_UNICODE
// Link : d2d1.lib windowscodecs.lib winhttp.lib ole32.lib user32.lib gdi32.lib dwrite.lib

#define WIN32_LEAN_AND_MEAN
#define NOMINMAX
#include <windows.h>
#include <windowsx.h>
#include <d2d1.h>
#include <dwrite.h> // DirectWriteのために追加
#include <wincodec.h>
#include <winhttp.h>
#include <stdint.h>
#include <vector>
#include <unordered_map>
#include <deque>
#include <mutex>
#include <condition_variable>
#include <thread>
#include <atomic>
#include <cmath>
#include <algorithm>
#include <string>
#include <chrono>
#include <functional>
#include <queue>
#include <memory>
#include <sstream>
#include <iomanip>

#pragma comment(lib, "d2d1.lib")
#pragma comment(lib, "windowscodecs.lib")
#pragma comment(lib, "winhttp.lib")
#pragma comment(lib, "ole32.lib")
#pragma comment(lib, "dwrite.lib") // DirectWriteライブラリを追加

#ifndef SAFE_RELEASE
#define SAFE_RELEASE(p) do{ if(p){ (p)->Release(); (p)=nullptr; } }while(0)
#endif
#ifndef M_PI
#define M_PI 3.14159265358979323846
#endif

// -------------------- Constants --------------------
static const int TILE_SIZE = 256;
static const int MIN_MAP_ZOOM = 2; // GSIマップの最小ズームを広めに設定
static const int MAX_MAP_ZOOM = 18; // GSIマップの最大ズームを広めに設定
static const int MIN_DL_ZOOM = 4; // JMAタイルの最小ズームに合わせる
static const int MAX_DL_ZOOM = 13; // JMAタイルの最大ズームに合わせる
static const int DEFAULT_ZOOM = 6;
static const int WORKER_THREADS = 4;

static const wchar_t* K_GSI_HOST = L"cyberjapandata.gsi.go.jp";
static const wchar_t* K_GSI_TILE_FMT = L"/xyz/std/%d/%d/%d.png"; // GSI標準地図を使用
static const INTERNET_PORT GSI_PORT = INTERNET_DEFAULT_HTTPS_PORT;

static const wchar_t* K_JMA_HOST = L"www.jma.go.jp";
static const wchar_t* K_TIMES_URL_N1 = L"/bosai/jmatile/data/nowc/targetTimes_N1.json";
static const wchar_t* K_TIMES_URL_N2 = L"/bosai/jmatile/data/nowc/targetTimes_N2.json";
static const wchar_t* K_JMA_TILE_FMT = L"/bosai/jmatile/data/nowc/%s/none/%s/surf/hrpns/%d/%d/%d.png";

// -------------------- Bounding Box of Japan --------------------
static const double JAPAN_MIN_LON = 122.0;
static const double JAPAN_MAX_LON = 154.0;
static const double JAPAN_MIN_LAT = 20.0;
static const double JAPAN_MAX_LAT = 46.0;

static const float kOverlayAlpha = 0.90f;
static const float kAnimDurationSec = 0.65f;
static const float kAnimStepInterval = 0.70f;
static const size_t kCacheLimit = 256; // タイルキャッシュの上限

#define WM_TILE_READY (WM_APP+1)

// -------------------- Types (GSI View) --------------------
struct App {
	HINSTANCE hInst{};
	HWND hwnd{};
	ID2D1Factory* factory{};
	ID2D1HwndRenderTarget* rt{};
	IWICImagingFactory* wic{};
	HINTERNET session{}; // WinHttpセッションは全体で共有

	int clientW{ 1280 }, clientH{ 800 };
	double zoom{ (double)DEFAULT_ZOOM };
	double originWX{}, originWY{}; // ワールド座標の左上
	bool dragging{};
	POINT dragStart{};
	double dragStartWX{}, dragStartWY{};
};
static App g;

// -------------------- Types (JMA Overlay & Cache) --------------------
struct Img {
	std::vector<BYTE> bytes;
	ID2D1Bitmap* bmp{ nullptr };
	std::chrono::steady_clock::time_point lastUsed{};
};
struct NowcTime { std::wstring basetime, validtime; };

static std::mutex gCacheMtx;
static std::unordered_map<std::wstring, Img> gCache;
static std::vector<NowcTime> gTimes;
static bool gUseForecast = false;
static int gTimeIndex = 0;

static std::atomic<bool> gAnimPlaying(false);
static std::chrono::steady_clock::time_point gAnimStart{};
static int gAnimFrom = 0, gAnimTo = 0;
static float gAnimT = 0.0f;

// -------------------- Thread Pool (JMA) --------------------
class ThreadPool {
public:
	explicit ThreadPool(size_t n = WORKER_THREADS) {
		for (size_t i = 0; i < n; ++i)
			workers.emplace_back([this]() { WorkerLoop(); });
	}
	~ThreadPool() {
		{
			std::unique_lock<std::mutex> lk(mtx);
			stop = true;
		}
		cv.notify_all();
		for (auto& t : workers) if (t.joinable()) t.join();
	}
	void enqueue(std::function<void()> f) {
		{
			std::unique_lock<std::mutex> lk(mtx);
			tasks.push(std::move(f));
		}
		cv.notify_one();
	}
private:
	void WorkerLoop() {
		while (true) {
			std::function<void()> task;
			{
				std::unique_lock<std::mutex> lk(mtx);
				cv.wait(lk, [this]() { return stop || !tasks.empty(); });
				if (stop && tasks.empty()) return;
				task = std::move(tasks.front());
				tasks.pop();
			}
			task();
		}
	}
	std::vector<std::thread> workers;
	std::queue<std::function<void()>> tasks;
	std::mutex mtx;
	std::condition_variable cv;
	bool stop = false;
};
static std::unique_ptr<ThreadPool> gPool;


// -------------------- Math helpers (GSI) --------------------
static inline double LonLatToWorldX(double lon, int z) { return TILE_SIZE * (1 << z) * ((lon + 180.0) / 360.0); }
static inline double LonLatToWorldY(double lat_deg, int z) {
	double s = (double)TILE_SIZE * (1 << z);
	double lat = std::clamp(lat_deg, -85.05112878, 85.05112878);
	double rad = lat * M_PI / 180.0;
	double sy = std::log(std::tan(M_PI / 4.0 + rad / 2.0));
	return s * (1.0 - sy / M_PI) / 2.0;
}
static inline double WorldXToLon(double wx, int z) { return wx / (TILE_SIZE * (1 << z)) * 360.0 - 180.0; }
static inline double WorldYToLat(double wy, int z) {
	double s = TILE_SIZE * (1 << z);
	double y = 2.0 * (1.0 - wy / s);
	return 180.0 / M_PI * std::atan(std::sinh(y * M_PI));
}
static inline double Clamp(double v, double lo, double hi) {
	return std::min(std::max(v, lo), hi);
}

// -------------------- Network (JMA) --------------------
static bool HttpGet(const wchar_t* host, INTERNET_PORT port, bool https, const std::wstring& path, std::vector<BYTE>& out)
{
	HINTERNET s = WinHttpOpen(L"GSIMapViewer/1.0", WINHTTP_ACCESS_TYPE_DEFAULT_PROXY, 0, 0, 0);
	if (!s) return false;
	HINTERNET c = WinHttpConnect(s, host, port, 0);
	if (!c) { WinHttpCloseHandle(s); return false; }
	DWORD flags = https ? WINHTTP_FLAG_SECURE : 0;
	HINTERNET r = WinHttpOpenRequest(c, L"GET", path.c_str(), 0, 0, 0, flags);
	if (!r) { WinHttpCloseHandle(c); WinHttpCloseHandle(s); return false; }

	// TLS 1.2/1.3を強制
	DWORD tls = WINHTTP_FLAG_SECURE_PROTOCOL_TLS1_2 | WINHTTP_FLAG_SECURE_PROTOCOL_TLS1_3;
	WinHttpSetOption(r, WINHTTP_OPTION_SECURE_PROTOCOLS, &tls, sizeof(tls));

	bool ok = false;
	if (WinHttpSendRequest(r, 0, 0, 0, 0, 0, 0) && WinHttpReceiveResponse(r, 0)) {
		DWORD status = 0, len = sizeof(status);
		WinHttpQueryHeaders(r, WINHTTP_QUERY_STATUS_CODE | WINHTTP_QUERY_FLAG_NUMBER,
			WINHTTP_HEADER_NAME_BY_INDEX, &status, &len, WINHTTP_NO_HEADER_INDEX);
		if (status == 200) {
			DWORD sz = 0;
			do {
				DWORD dw = 0;
				if (!WinHttpQueryDataAvailable(r, &sz)) break;
				if (sz == 0) { ok = true; break; }
				size_t old = out.size(); out.resize(old + sz);
				if (!WinHttpReadData(r, out.data() + old, sz, &dw)) break;
				if (dw < sz) out.resize(old + dw);
			} while (true);
		}
	}
	WinHttpCloseHandle(r); WinHttpCloseHandle(c); WinHttpCloseHandle(s);
	return ok && !out.empty();
}

static bool FetchTimes(bool forecast, std::vector<NowcTime>& out)
{
	std::vector<BYTE> buf;
	const wchar_t* path = forecast ? K_TIMES_URL_N2 : K_TIMES_URL_N1;
	// JSON簡易パース
	if (!HttpGet(K_JMA_HOST, INTERNET_DEFAULT_HTTPS_PORT, true, path, buf)) return false;

	out.clear();
	std::string js(buf.begin(), buf.end());
	size_t pos = 0;
	while (true) {
		size_t b = js.find("\"basetime\"", pos);
		size_t v = js.find("\"validtime\"", pos);
		if (b == std::string::npos || v == std::string::npos) break;
		size_t bq1 = js.find('"', b + 10), bq2 = js.find('"', bq1 + 1);
		size_t vq1 = js.find('"', v + 11), vq2 = js.find('"', vq1 + 1);
		if (bq1 == std::string::npos || bq2 == std::string::npos || vq1 == std::string::npos || vq2 == std::string::npos) break;
		std::string bs = js.substr(bq1 + 1, bq2 - bq1 - 1);
		std::string vs = js.substr(vq1 + 1, vq2 - vq1 - 1);
		NowcTime t; t.basetime.assign(bs.begin(), bs.end()); t.validtime.assign(vs.begin(), vs.end());
		out.push_back(std::move(t));
		pos = vq2 + 1;
		if (out.size() > 120) break;
	}
	return !out.empty();
}

// -------------------- Cache & Decode (JMA) --------------------
static ID2D1Bitmap* LoadPngToD2D(const std::vector<BYTE>& png)
{
	IWICStream* s = nullptr; IWICBitmapDecoder* dec = nullptr;
	IWICBitmapFrameDecode* fr = nullptr; IWICFormatConverter* cvt = nullptr; ID2D1Bitmap* bmp = nullptr;
	if (FAILED(g.wic->CreateStream(&s))) goto done;
	if (FAILED(s->InitializeFromMemory((WICInProcPointer)png.data(), (DWORD)png.size()))) goto done;
	if (FAILED(g.wic->CreateDecoderFromStream(s, nullptr, WICDecodeMetadataCacheOnLoad, &dec))) goto done;
	if (FAILED(dec->GetFrame(0, &fr))) goto done;
	if (FAILED(g.wic->CreateFormatConverter(&cvt))) goto done;
	if (FAILED(cvt->Initialize(fr, GUID_WICPixelFormat32bppPBGRA, WICBitmapDitherTypeNone, nullptr, 0, WICBitmapPaletteTypeCustom))) goto done;
	if (FAILED(g.rt->CreateBitmapFromWicBitmap(cvt, nullptr, &bmp))) goto done;
done:
	SAFE_RELEASE(cvt); SAFE_RELEASE(fr); SAFE_RELEASE(dec); SAFE_RELEASE(s);
	return bmp;
}

static void PurgeOldTiles()
{
	if (gCache.size() <= kCacheLimit) return;
	std::vector<std::pair<std::wstring, std::chrono::steady_clock::time_point>> v;
	for (auto& kv : gCache) v.emplace_back(kv.first, kv.second.lastUsed);
	std::sort(v.begin(), v.end(), [](auto& a, auto& b) { return a.second < b.second; });
	size_t removeCount = v.size() - kCacheLimit;
	for (size_t i = 0; i < removeCount; ++i) {
		auto it = gCache.find(v[i].first);
		if (it != gCache.end()) {
			SAFE_RELEASE(it->second.bmp);
			it->second.bytes.clear();
			gCache.erase(it);
		}
	}
}

static bool GetOrFetchBitmap(const std::wstring& key, ID2D1Bitmap** outBmp, bool isOverlay)
{
	std::lock_guard<std::mutex> lk(gCacheMtx);
	auto it = gCache.find(key);
	if (it != gCache.end()) {
		it->second.lastUsed = std::chrono::steady_clock::now();
		if (!it->second.bmp && !it->second.bytes.empty()) {
			// WICデコードはメインスレッドでのみ行う
			it->second.bmp = LoadPngToD2D(it->second.bytes);
			it->second.bytes.clear(); // デコード後、バイト列は解放
		}
		*outBmp = it->second.bmp;
		return (*outBmp != nullptr);
	}
	*outBmp = nullptr;

	// キャッシュにない場合はプレースホルダーを追加し、非同期ダウンロードを開始
	Img im;
	im.lastUsed = std::chrono::steady_clock::now();
	gCache.emplace(key, std::move(im));
	PurgeOldTiles();

	if (gPool) {
		gPool->enqueue([key, isOverlay]() {
			std::vector<BYTE> buf;
			const wchar_t* host = isOverlay ? K_JMA_HOST : K_GSI_HOST;
			bool ok = HttpGet(host, INTERNET_DEFAULT_HTTPS_PORT, true, key, buf);

			std::lock_guard<std::mutex> lk(gCacheMtx);
			auto it_dl = gCache.find(key);
			if (it_dl != gCache.end()) {
				if (ok) {
					it_dl->second.bytes = std::move(buf);
					// メインスレッドにデコードを促す
					if (g.hwnd) PostMessage(g.hwnd, WM_TILE_READY, 0, 0);
				}
				else {
					// 失敗したタイルはキャッシュから削除
					gCache.erase(it_dl);
				}
			}
			});
	}
	return false;
}

// -------------------- View helpers (GSI) --------------------
static void ClampViewToJapan() {
	int z = (int)std::floor(g.zoom);
	double sc = std::pow(2.0, g.zoom - z);
	double wxMin = LonLatToWorldX(JAPAN_MIN_LON, z);
	double wxMax = LonLatToWorldX(JAPAN_MAX_LON, z);
	double wyMin = LonLatToWorldY(JAPAN_MAX_LAT, z);
	double wyMax = LonLatToWorldY(JAPAN_MIN_LAT, z);
	double viewW = g.clientW / sc;
	double viewH = g.clientH / sc;
	{
		double mapW = wxMax - wxMin;
		double mapH = wyMax - wyMin;

		if (viewW >= mapW) { g.originWX = (wxMin + wxMax - viewW) / 2.0; }
		else { g.originWX = std::clamp(g.originWX, wxMin, wxMax - viewW); }

		if (viewH >= mapH) { g.originWY = (wyMin + wyMax - viewH) / 2.0; }
		else { g.originWY = std::clamp(g.originWY, wyMin, wyMax - viewH); }
	}
}

static void CenterOnLonLat(double lon, double lat) {
	int z = (int)std::floor(g.zoom);
	double wx = LonLatToWorldX(lon, z);
	double wy = LonLatToWorldY(lat, z);
	double sc = std::pow(2.0, g.zoom - z);
	g.originWX = wx - g.clientW / (2.0 * sc);
	g.originWY = wy - g.clientH / (2.0 * sc);
}

static void UpdateTitle() {
	int zi = (int)std::floor(g.zoom);
	double sc = std::pow(2.0, g.zoom - zi);
	double cx = g.originWX + g.clientW / (2.0 * sc);
	double cy = g.originWY + g.clientH / (2.0 * sc);
	double lat = WorldYToLat(cy, zi);
	double lon = WorldXToLon(cx, zi);

	std::wstring timeStr;
	if (!gTimes.empty() && gTimeIndex >= 0 && gTimeIndex < gTimes.size()) {
		timeStr = L" | Time: " + gTimes[gTimeIndex].validtime.substr(4, 2) + L"/" + gTimes[gTimeIndex].validtime.substr(6, 2) +
			L" " + gTimes[gTimeIndex].validtime.substr(8, 2) + L":" + gTimes[gTimeIndex].validtime.substr(10, 2);
	}

	wchar_t title[256];
	swprintf(title, 256, L"JMA Nowcast & GSI Map - Lat: %.4f, Lon: %.4f, Zoom: %.2f%s (%s)",
		lat, lon, g.zoom, timeStr.c_str(), gUseForecast ? L"Forecast" : L"Observation");
	SetWindowTextW(g.hwnd, title);
}

static void ZoomAtCenter(double delta) {
	double old = g.zoom;
	double nz = std::clamp(old + delta, (double)MIN_MAP_ZOOM, (double)MAX_MAP_ZOOM); // GSIの最大ズームを使用

	int zOld = (int)std::floor(old), zNew = (int)std::floor(nz);
	int cx = g.clientW / 2, cy = g.clientH / 2;
	double sOld = std::pow(2.0, old - zOld);
	double wx = g.originWX + cx / sOld;
	double wy = g.originWY + cy / sOld;

	if (zNew != zOld) {
		double b = std::ldexp(1.0, zNew - zOld);
		g.originWX *= b; g.originWY *= b;
		wx *= b; wy *= b;
	}

	g.zoom = nz;
	double sNew = std::pow(2.0, nz - zNew);
	g.originWX = wx - cx / sNew;
	g.originWY = wy - cy / sNew;

	ClampViewToJapan();
	InvalidateRect(g.hwnd, nullptr, FALSE);
	UpdateTitle();
}

static void SwitchTimes(bool forecast)
{
	gUseForecast = forecast;
	std::vector<NowcTime> t;
	if (FetchTimes(gUseForecast, t)) {
		gTimes.swap(t);
		gTimeIndex = 0;
		gAnimPlaying = false;
	}
	InvalidateRect(g.hwnd, nullptr, FALSE);
	UpdateTitle();
}

static void StartAnimTo(int toIndex)
{
	if (toIndex < 0 || toIndex >= (int)gTimes.size() || toIndex == gTimeIndex) return;
	gAnimFrom = gTimeIndex; gAnimTo = toIndex;
	gAnimStart = std::chrono::steady_clock::now();
	gAnimPlaying = true;
}

static void StepTime(int delta)
{
	if (gTimes.empty()) return;
	int to = (int)Clamp(gTimeIndex + delta, 0.0, (double)gTimes.size() - 1);
	if (to == gTimeIndex) return;
	StartAnimTo(to);
	InvalidateRect(g.hwnd, nullptr, FALSE);
}


// -------------------- Draw --------------------
static void EnsureRT() {
	if (!g.rt) {
		RECT rc; GetClientRect(g.hwnd, &rc);
		D2D1_SIZE_U sz = D2D1::SizeU(rc.right, rc.bottom);
		HRESULT hr = g.factory->CreateHwndRenderTarget(D2D1::RenderTargetProperties(),
			D2D1::HwndRenderTargetProperties(g.hwnd, sz), &g.rt);
		if (FAILED(hr)) g.rt = nullptr;
	}
}

// JMAナウキャストに使用する最適なズームレベルを決定する
static int GetJmaZoomLevel(int zCurrent) {
	// 現在のズームがJMAの範囲外の場合、最も近いズームを使用
	return std::clamp(zCurrent, MIN_DL_ZOOM, MAX_DL_ZOOM);
}


static void DrawScene() {
	EnsureRT();
	if (!g.rt) return;

	g.rt->BeginDraw();
	g.rt->Clear(D2D1::ColorF(1.0f, 1.0f, 1.0f));

	// 描画するGSIタイルのズームレベル（zDL）
	int zDL = (int)std::floor(g.zoom); // 現在の分数ズームの整数部を使用
	zDL = std::clamp(zDL, MIN_MAP_ZOOM, MAX_MAP_ZOOM); // GSIタイルは広い範囲でクランプ

	double current_scale = std::pow(2.0, g.zoom - zDL);

	// 画面がカバーするワールド座標の範囲（zDL座標系）
	double wx0 = g.originWX;
	double wy0 = g.originWY;
	double wx1 = g.originWX + g.clientW / current_scale;
	double wy1 = g.originWY + g.clientH / current_scale;

	// GSIマップの描画ロジック
	auto drawGsiTiles = [&]() {
		int maxT = (1 << zDL);
		// 画面がカバーするタイル座標の範囲（zDL座標系）
		int tx0 = (int)std::floor(wx0 / TILE_SIZE);
		int ty0 = (int)std::floor(wy0 / TILE_SIZE);
		int tx1 = (int)std::floor(wx1 / TILE_SIZE);
		int ty1 = (int)std::floor(wy1 / TILE_SIZE);

		for (int ty = ty0; ty <= ty1; ++ty) {
			for (int tx = tx0; tx <= tx1; ++tx) {
				int nx = (tx % maxT + maxT) % maxT;
				int ny = std::clamp(ty, 0, maxT - 1);

				double wx_start = tx * TILE_SIZE;
				double wy_start = ty * TILE_SIZE;

				float sx = (float)((wx_start - g.originWX) * current_scale);
				float sy = (float)((wy_start - g.originWY) * current_scale);
				float ss = (float)(TILE_SIZE * current_scale);

				D2D1_RECT_F dst = D2D1::RectF(sx, sy, sx + ss, sy + ss);

				if (dst.right > 0 && dst.left < g.clientW && dst.bottom > 0 && dst.top < g.clientH) {
					wchar_t buf[512];
					swprintf_s(buf, K_GSI_TILE_FMT, zDL, nx, ny);
					std::wstring path = buf;

					ID2D1Bitmap* bmp = nullptr;
					if (GetOrFetchBitmap(path, &bmp, false) && bmp) {
						g.rt->DrawBitmap(bmp, dst, 1.0f, D2D1_BITMAP_INTERPOLATION_MODE_LINEAR);
					}
				}
			}
		}
		};

	// JMAナウキャストの描画ロジック
	auto drawJmaOverlay = [&](int timeIndex, float alpha) {
		if (gTimes.empty() || timeIndex < 0 || timeIndex >= gTimes.size()) return;

		// JMAが実際に利用するズームレベルを決定
		int current_floor_zoom = (int)std::floor(g.zoom);

		// 修正ロジック: ズームが整数に一致する場合 (例: 7.00)、一つ下のズームレベルを参照する
		int zJMA_candidate;
		if (g.zoom == current_floor_zoom) {
			// 整数ズームと一致する場合、フォールバック (例: Z=7.00 -> Z=6)
			zJMA_candidate = current_floor_zoom - 1;
		}
		else {
			// 分数ズームの場合、現在の整数部を使用 (例: Z=7.25 -> Z=7)
			zJMA_candidate = current_floor_zoom;
		}

		// JMAが実際に利用するズームレベルを決定 (最小/最大でクランプ)
		int zJMA = GetJmaZoomLevel(zJMA_candidate);

		int maxT_JMA = (1 << zJMA);
		NowcTime T = gTimes[timeIndex];

		// zJMAタイルが zDL座標系で持つべき辺の長さ (タイル数)
		double tile_count_factor = std::pow(2.0, zDL - zJMA); // 2^(zDL - zJMA)

		// 画面がカバーする JMA タイル座標の範囲 (zJMA座標系)
		// 境界問題を回避するため、1タイル分バッファを持たせて範囲を拡大する
		int tx0_JMA = (int)std::floor(wx0 / TILE_SIZE / tile_count_factor) - 1;
		int ty0_JMA = (int)std::floor(wy0 / TILE_SIZE / tile_count_factor) - 1;
		int tx1_JMA = (int)std::floor(wx1 / TILE_SIZE / tile_count_factor) + 1;
		int ty1_JMA = (int)std::floor(wy1 / TILE_SIZE / tile_count_factor) + 1;

		for (int ty_JMA = ty0_JMA; ty_JMA <= ty1_JMA; ++ty_JMA) {
			for (int tx_JMA = tx0_JMA; tx_JMA <= tx1_JMA; ++tx_JMA) {
				// JMAタイルの座標を正規化（X方向のみラップアラウンド）
				int nx = (tx_JMA % maxT_JMA + maxT_JMA) % maxT_JMA;
				// Y方向はクランプ処理
				int ny = std::clamp(ty_JMA, 0, maxT_JMA - 1);

				// JMAタイルのワールド座標での開始位置 (zDL座標系)
				double wx_jma_start = tx_JMA * TILE_SIZE * tile_count_factor;
				double wy_jma_start = ty_JMA * TILE_SIZE * tile_count_factor;

				// 画面座標への変換
				float sx = (float)((wx_jma_start - g.originWX) * current_scale);
				float sy = (float)((wy_jma_start - g.originWY) * current_scale);

				// 画面上の描画サイズ (JMAタイルのワールドサイズ * current_scale)
				float draw_size = (float)(TILE_SIZE * current_scale * tile_count_factor);

				D2D1_RECT_F dst = D2D1::RectF(sx, sy, sx + draw_size, sy + draw_size);

				if (dst.right > 0 && dst.left < g.clientW && dst.bottom > 0 && dst.top < g.clientH) {
					wchar_t buf[512];
					// パス生成には、決定された zJMA, nx, ny を使用
					swprintf_s(buf, K_JMA_TILE_FMT, T.basetime.c_str(), T.validtime.c_str(), zJMA, nx, ny);
					std::wstring path = buf;

					ID2D1Bitmap* bmp = nullptr;
					if (GetOrFetchBitmap(path, &bmp, true) && bmp) {
						g.rt->DrawBitmap(bmp, dst, alpha, D2D1_BITMAP_INTERPOLATION_MODE_LINEAR);
					}
				}
			}
		}
		};

	// 1. GSI Base Mapを描画
	drawGsiTiles();

	// 2. JMA Overlayを描画
	if (gAnimPlaying) {
		// アニメーションブレンド
		float t = std::chrono::duration<float>(std::chrono::steady_clock::now() - gAnimStart).count() / kAnimDurationSec;
		gAnimT = (float)Clamp(t, 0.0, 1.0);
		drawJmaOverlay(gAnimFrom, (1.0f - gAnimT) * kOverlayAlpha);
		drawJmaOverlay(gAnimTo, gAnimT * kOverlayAlpha);
		if (t >= 1.0f) { gAnimPlaying = false; gTimeIndex = gAnimTo; UpdateTitle(); }
		InvalidateRect(g.hwnd, nullptr, FALSE); // アニメ中は毎フレーム再描画
	}
	else {
		// 固定表示
		drawJmaOverlay(gTimeIndex, kOverlayAlpha);
	}


	// 3. 情報表示オーバーレイ (例: 現在時刻)
	if (!gTimes.empty()) {
		ID2D1SolidColorBrush* brush = nullptr;
		g.rt->CreateSolidColorBrush(D2D1::ColorF(D2D1::ColorF::Black), &brush);

		IDWriteFactory* writeFactory = nullptr;
		IDWriteTextFormat* textFormat = nullptr;
		// 修正: DWriteCreateFactoryを使用する前にdwrite.hがインクルードされていることを確認
		HRESULT hr = DWriteCreateFactory(DWRITE_FACTORY_TYPE_SHARED, __uuidof(IDWriteFactory),
			reinterpret_cast<IUnknown**>(&writeFactory));

		if (SUCCEEDED(hr) && writeFactory) {
			// 修正: DWRITE_FONT_WEIGHT_NORMALなどの識別子がDWriteCreateFactoryの成功後に使用されることを確認
			writeFactory->CreateTextFormat(L"Arial", nullptr, DWRITE_FONT_WEIGHT_NORMAL, DWRITE_FONT_STYLE_NORMAL,
				DWRITE_FONT_STRETCH_NORMAL, 16.0f, L"ja-jp", &textFormat);
		}

		if (brush && textFormat) {
			std::wstringstream ss;
			ss << (gUseForecast ? L"予測 (N2)" : L"観測 (N1)") << L"\n";

			if (gTimeIndex >= 0 && gTimeIndex < gTimes.size()) {
				const auto& t = gTimes[gTimeIndex].validtime;
				std::wstring formattedTime = t.substr(4, 2) + L"/" + t.substr(6, 2) + L" " + t.substr(8, 2) + L":" + t.substr(10, 2);
				ss << L"表示時刻: " << formattedTime << L" JST";
			}
			else {
				ss << L"表示時刻: データなし";
			}

			std::wstring text = ss.str();
			D2D1_RECT_F layoutRect = D2D1::RectF(10, 10, (float)g.clientW - 10, (float)g.clientH - 10);
			g.rt->DrawText(text.c_str(), (UINT32)text.length(), textFormat, layoutRect, brush);
		}

		SAFE_RELEASE(textFormat);
		SAFE_RELEASE(writeFactory);
		SAFE_RELEASE(brush);
	}

	g.rt->EndDraw();
}

// -------------------- Win32 --------------------
static LRESULT CALLBACK WndProc(HWND h, UINT m, WPARAM w, LPARAM l) {
	switch (m) {
	case WM_CREATE:
		// スレッドプール開始
		gPool = std::make_unique<ThreadPool>(WORKER_THREADS);
		// JMAの時間データ取得
		SwitchTimes(gUseForecast);
		SetTimer(h, 1, (UINT)(kAnimStepInterval * 1000), nullptr); // タイマー開始
		return 0;
	case WM_SIZE: {
		RECT rc; GetClientRect(h, &rc);
		g.clientW = rc.right; g.clientH = rc.bottom;
		if (g.rt) g.rt->Resize(D2D1::SizeU(g.clientW, g.clientH));
		ClampViewToJapan();
		InvalidateRect(h, nullptr, FALSE); return 0;
	}
	case WM_LBUTTONDOWN:
		g.dragging = true; SetCapture(h);
		g.dragStart.x = GET_X_LPARAM(l); g.dragStart.y = GET_Y_LPARAM(l);
		g.dragStartWX = g.originWX; g.dragStartWY = g.originWY; return 0;
	case WM_MOUSEMOVE:
		if (g.dragging) {
			int sx = GET_X_LPARAM(l), sy = GET_Y_LPARAM(l);
			int z = (int)std::floor(g.zoom);
			double sc = std::pow(2.0, g.zoom - z);
			g.originWX = g.dragStartWX - (sx - g.dragStart.x) / sc;
			g.originWY = g.dragStartWY - (sy - g.dragStart.y) / sc;
			ClampViewToJapan();
			InvalidateRect(h, nullptr, FALSE);
			UpdateTitle();
		}return 0;
	case WM_LBUTTONUP:g.dragging = false; ReleaseCapture(); return 0;
	case WM_MOUSEWHEEL: {
		int delta = GET_WHEEL_DELTA_WPARAM(w);
		ZoomAtCenter((delta > 0) ? 0.25 : -0.25); return 0;
	}
	case WM_KEYDOWN:
		if (w == '1') SwitchTimes(false); // 観測データ (N1)
		else if (w == '2') SwitchTimes(true); // 予測データ (N2)
		else if (w == VK_LEFT) StepTime(-1); // 前の時刻
		else if (w == VK_RIGHT) StepTime(+1); // 次の時刻
		else if (w == 'R') { CenterOnLonLat(139.767125, 35.681236); ZoomAtCenter(0); InvalidateRect(h, nullptr, FALSE); UpdateTitle(); } // 東京にリセット
		return 0;
	case WM_TIMER:
		if (w == 1 && !gAnimPlaying) StepTime(+1);
		return 0;
	case WM_PAINT: {
		PAINTSTRUCT ps; BeginPaint(h, &ps); DrawScene(); EndPaint(h, &ps); return 0;
	}
	case WM_TILE_READY: // ダウンロード完了、メインスレッドでのデコードを促す
		InvalidateRect(h, nullptr, FALSE); return 0;
	case WM_DESTROY:
		// スレッドプール停止
		gPool.reset();
		// キャッシュの解放
		{
			std::scoped_lock lk(gCacheMtx);
			for (auto& kv : gCache) SAFE_RELEASE(kv.second.bmp);
			gCache.clear();
		}
		SAFE_RELEASE(g.rt);
		SAFE_RELEASE(g.wic);
		SAFE_RELEASE(g.factory);
		PostQuitMessage(0); return 0;
	}
	return DefWindowProc(h, m, w, l);
}

static void UpdateClientSize() {
	RECT rc; GetClientRect(g.hwnd, &rc);
	g.clientW = rc.right - rc.left;
	g.clientH = rc.bottom - rc.top;
	if (g.rt) {
		g.rt->Resize(D2D1::SizeU(g.clientW, g.clientH));
	}
}

// -------------------- WinMain --------------------
int APIENTRY wWinMain(HINSTANCE hI, HINSTANCE, LPWSTR, int nCmd) {
	CoInitializeEx(nullptr, COINIT_APARTMENTTHREADED);
	D2D1CreateFactory(D2D1_FACTORY_TYPE_SINGLE_THREADED, &g.factory);
	CoCreateInstance(CLSID_WICImagingFactory, nullptr, CLSCTX_INPROC_SERVER, IID_PPV_ARGS(&g.wic));

	WNDCLASSEXW wc{ sizeof(wc) }; wc.lpfnWndProc = WndProc; wc.hInstance = hI;
	wc.hCursor = LoadCursor(nullptr, IDC_ARROW); wc.lpszClassName = L"JMAGSIMapViewerWnd"; RegisterClassExW(&wc);
	g.hwnd = CreateWindowW(wc.lpszClassName, L"JMA Nowcast & GSI Map Viewer", WS_OVERLAPPEDWINDOW,
		CW_USEDEFAULT, 0, 1280, 800, nullptr, nullptr, hI, nullptr);
	ShowWindow(g.hwnd, nCmd);
	UpdateWindow(g.hwnd);

	// 初期設定
	UpdateClientSize();
	CenterOnLonLat(139.767125, 35.681236); // 東京駅
	ClampViewToJapan();

	// 初回描画とタイトル更新
	InvalidateRect(g.hwnd, nullptr, FALSE);
	UpdateWindow(g.hwnd);
	DrawScene();
	UpdateTitle();

	// メッセージループ
	MSG msg;
	while (GetMessage(&msg, nullptr, 0, 0)) {
		TranslateMessage(&msg);
		DispatchMessage(&msg);
	}

	CoUninitialize();
	return 0;
}
