// PADDOCK GATE（Tauri 版の窓）
//
// 中身（コピー・目印・PowerPoint 操作など）はこれまでどおり Python のエンジン（runtime\app\sw_nas_operator.pyc）。
// この窓がエンジンを起動し、その画面（http://127.0.0.1:<ポート>/）を表示する。
//   ・タスクバー右下のアイコン（画面を開く・常に最前面・終了）。窓を閉じても裏で動く（コピーを続ける）
//   ・常に最前面：スライド・ファイルを開くときは外し、開いた窓を前に出せるようにする。GATE に戻ると戻す
//   ・2回目の起動は、開いている窓を前に出すだけ
//   ・WebView2 が無い PC では、これまでの形（Chrome / Edge の窓＋エンジンのアイコン）で動かす
#![cfg_attr(not(debug_assertions), windows_subsystem = "windows")]

use std::fs::{self, File, OpenOptions};
use std::io::{Read, Write};
use std::net::{SocketAddr, TcpStream};
use std::path::{Path, PathBuf};
use std::process::{Child, Command, Stdio};
use std::sync::atomic::{AtomicBool, AtomicU32, Ordering};
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::{Duration, Instant};

use tauri::menu::{CheckMenuItem, Menu, MenuItem, PredefinedMenuItem};
use tauri::tray::{MouseButton, MouseButtonState, TrayIconBuilder, TrayIconEvent};
use tauri::{AppHandle, Manager, State, WebviewUrl, WebviewWindow, WebviewWindowBuilder, WindowEvent};
use tauri_plugin_dialog::{DialogExt, MessageDialogButtons, MessageDialogKind};

const APP: &str = "PADDOCK GATE";
const VERSION: &str = env!("CARGO_PKG_VERSION");
const DEFAULT_PORT: u16 = 8797;
const HOME_ENV: &str = "SW_NAS_OPERATOR_HOME";
const CORE_EXE: &str = "PADDOCK_GATE_core.exe";
const APP_PYC: &str = "sw_nas_operator.pyc";

struct Shared {
    dir: PathBuf,              // exe の場所（runtime フォルダの親）
    port: u16,
    pinned: AtomicBool,        // 常に最前面（設定）
    dropped: AtomicBool,       // 開くために一時的に最前面を外している
    blurred: AtomicBool,       // 外したあと、ほかの窓に移った
    applied: AtomicBool,       // いま実際に最前面にしているか
    quitting: AtomicBool,
    restarts: AtomicU32,
    child: Mutex<Option<Child>>,
    log: Mutex<Option<File>>, // 窓側の記録（runtime\shell.log）
    selftest: bool,
    ipc_seen: AtomicBool,
}

impl Shared {
    fn runtime(&self) -> PathBuf {
        self.dir.join("runtime")
    }
    fn key_file(&self) -> PathBuf {
        self.runtime().join("shell.key")
    }
    fn settings_file(&self) -> PathBuf {
        self.runtime().join("shell.json")
    }
    fn url(&self) -> String {
        format!("http://127.0.0.1:{}/", self.port)
    }
    fn note(&self, msg: &str) {
        if let Ok(mut g) = self.log.lock() {
            if let Some(f) = g.as_mut() {
                let t = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).map(|d| d.as_secs()).unwrap_or(0);
                let _ = writeln!(f, "[{}] {}", t, msg);
                let _ = f.flush();
            }
        }
    }
    fn save_settings(&self) {
        let j = serde_json::json!({ "pinned": self.pinned.load(Ordering::SeqCst) });
        let _ = fs::write(self.settings_file(), j.to_string());
    }
}

fn exe_dir() -> PathBuf {
    if let Ok(d) = std::env::var("PADDOCK_DIR") {
        return PathBuf::from(d); // 開発・試験用
    }
    std::env::current_exe()
        .ok()
        .and_then(|p| p.parent().map(Path::to_path_buf))
        .unwrap_or_else(|| PathBuf::from("."))
}

// ---------------------------------------------------------------- エンジンとのやりとり（このPCの中だけ・素の HTTP）
fn http(port: u16, method: &str, path: &str, headers: &[(&str, &str)], timeout: Duration) -> Option<(u16, String)> {
    let addr = SocketAddr::from(([127, 0, 0, 1], port));
    let mut s = TcpStream::connect_timeout(&addr, timeout).ok()?;
    s.set_read_timeout(Some(timeout)).ok()?;
    s.set_write_timeout(Some(timeout)).ok()?;
    let mut req = format!("{} {} HTTP/1.0\r\nHost: 127.0.0.1:{}\r\nConnection: close\r\n", method, path, port);
    for (k, v) in headers {
        req.push_str(&format!("{}: {}\r\n", k, v));
    }
    if method == "POST" {
        req.push_str("Content-Type: application/json\r\nContent-Length: 2\r\n\r\n{}");
    } else {
        req.push_str("\r\n");
    }
    s.write_all(req.as_bytes()).ok()?;
    let mut buf = Vec::new();
    let _ = s.take(1 << 20).read_to_end(&mut buf);
    let text = String::from_utf8_lossy(&buf).to_string();
    let code = text.split_whitespace().nth(1)?.parse::<u16>().ok()?;
    let body = text.split_once("\r\n\r\n").map(|x| x.1.to_string()).unwrap_or_default();
    Some((code, body))
}

/// エンジンが応えるか（ほかのアプリが同じポートを使っていたら false）
fn ping(port: u16) -> bool {
    ping_version(port).is_some()
}

/// 応えたエンジンの版
fn ping_version(port: u16) -> Option<String> {
    match http(port, "GET", "/api/ping", &[], Duration::from_millis(1500)) {
        Some((200, body)) if body.contains(APP) => Some(
            serde_json::from_str::<serde_json::Value>(&body)
                .ok()
                .and_then(|v| v.get("version").and_then(|x| x.as_str()).map(String::from))
                .unwrap_or_default(),
        ),
        _ => None,
    }
}

/// 版の比べ方（1.12.0 → [1, 12, 0]）
fn vt(v: &str) -> Vec<u32> {
    v.split('.').map(|x| x.parse().unwrap_or(0)).collect()
}

/// 応えたエンジンを起動したプロセス（前の版の窓・ランチャー）
fn ping_ppid(port: u16) -> u32 {
    match http(port, "GET", "/api/ping", &[], Duration::from_millis(1500)) {
        Some((200, body)) => serde_json::from_str::<serde_json::Value>(&body)
            .ok()
            .and_then(|v| v.get("ppid").and_then(|x| x.as_u64()))
            .unwrap_or(0) as u32,
        _ => 0,
    }
}

/// プロセスが終わるのを待つ（最大 limit）。自分自身・分からないときは待たない
fn wait_exit(pid: u32, limit: Duration) {
    if pid == 0 || pid == std::process::id() {
        return;
    }
    #[cfg(windows)]
    unsafe {
        use windows_sys::Win32::Foundation::CloseHandle;
        use windows_sys::Win32::System::Threading::{OpenProcess, WaitForSingleObject, PROCESS_SYNCHRONIZE};
        let h = OpenProcess(PROCESS_SYNCHRONIZE, 0, pid);
        if !h.is_null() {
            WaitForSingleObject(h, limit.as_millis() as u32);
            CloseHandle(h);
        }
    }
    #[cfg(not(windows))]
    {
        let t0 = Instant::now();
        while Path::new(&format!("/proc/{}", pid)).exists() && t0.elapsed() < limit {
            thread::sleep(Duration::from_millis(300));
        }
    }
}

/// ポートが使われているか（応えないが動いている＝重い処理の最中、を見分ける）
fn port_busy(port: u16) -> bool {
    TcpStream::connect_timeout(&SocketAddr::from(([127, 0, 0, 1], port)), Duration::from_millis(800)).is_ok()
}

/// Tauri を使わずに知らせる（起動の前・WebView2 が無いとき）
fn plain_message(title: &str, msg: &str) {
    #[cfg(windows)]
    {
        use windows_sys::Win32::UI::WindowsAndMessaging::{MessageBoxW, MB_ICONWARNING, MB_OK, MB_SETFOREGROUND};
        let w = |s: &str| s.encode_utf16().chain(std::iter::once(0)).collect::<Vec<u16>>();
        let (t, m) = (w(title), w(msg));
        unsafe {
            MessageBoxW(std::ptr::null_mut(), m.as_ptr(), t.as_ptr(), MB_OK | MB_ICONWARNING | MB_SETFOREGROUND);
        }
    }
    #[cfg(not(windows))]
    eprintln!("{}: {}", title, msg);
}

fn log_tail(path: &Path) -> String {
    let t = fs::read(path).map(|b| String::from_utf8_lossy(&b).to_string()).unwrap_or_default();
    let n = t.chars().count();
    let tail: String = t.chars().skip(n.saturating_sub(900)).collect();
    tail.trim().to_string()
}

/// エンジンを起動する（窓が無い・黒い画面を出さない）。fallback=true は WebView2 が無いときのこれまでの形
fn spawn_engine(st: &Shared, fallback: bool) -> Result<(Child, PathBuf), String> {
    let rt = st.runtime();
    let (py, app): (PathBuf, PathBuf) = match (std::env::var("PADDOCK_PYTHON"), std::env::var("PADDOCK_APP")) {
        (Ok(p), Ok(a)) => (PathBuf::from(p), PathBuf::from(a)), // 開発・試験用
        _ => {
            let core = rt.join("python").join(CORE_EXE);
            let py = if core.is_file() { core } else { rt.join("python").join("python.exe") };
            (py, rt.join("app").join(APP_PYC))
        }
    };
    if !py.is_file() || !app.is_file() {
        return Err(format!(
            "runtime フォルダが見つかりません。\n\nZIPファイルを「すべて展開」してから、展開したフォルダの PADDOCK_GATE.exe を起動してください。\n\n（{}）",
            py.display()
        ));
    }
    let _ = fs::create_dir_all(&rt);
    if !fallback {
        let _ = fs::remove_file(st.key_file()); // 前に止まったときの鍵は使わない
    }
    // 記録：ほかで書いている最中のもの（起動中のもう1つ）は消さない
    let mut logp = rt.join("last_run.log");
    let mut out = None;
    for k in 1..=5 {
        if k > 1 {
            logp = rt.join(format!("last_run_{}.log", k));
        }
        if let Ok(f) = OpenOptions::new().write(true).create(true).truncate(true).open(&logp) {
            out = Some(f);
            break;
        }
    }
    let mut cmd = Command::new(&py);
    cmd.arg(&app).arg("--port").arg(st.port.to_string());
    if !fallback {
        cmd.arg("--no-browser");
        cmd.env("SW_NAS_TRAY", "0"); // アイコンはこの窓が出す
        cmd.env("SW_NAS_SHELL_KEYFILE", st.key_file());
    }
    cmd.env(HOME_ENV, &st.dir)
        .env("SW_NAS_AUTOQUIT", "1")
        .env("PYTHONIOENCODING", "utf-8")
        .env("PYTHONUNBUFFERED", "1")
        .current_dir(&st.dir)
        .stdin(Stdio::null());
    match out {
        Some(f) => {
            let e = f.try_clone().map(Stdio::from).unwrap_or_else(|_| Stdio::null());
            cmd.stdout(Stdio::from(f)).stderr(e);
        }
        None => {
            cmd.stdout(Stdio::null()).stderr(Stdio::null());
        }
    }
    #[cfg(windows)]
    {
        use std::os::windows::process::CommandExt;
        cmd.creation_flags(0x0800_0000); // CREATE_NO_WINDOW
    }
    let child = cmd.spawn().map_err(|e| format!("エンジンを起動できませんでした（{}）", e))?;
    Ok((child, logp))
}

// ---------------------------------------------------------------- 窓
fn main_window(app: &AppHandle) -> Option<WebviewWindow> {
    app.get_webview_window("main")
}

fn show_main(app: &AppHandle) {
    if let Some(w) = main_window(app) {
        let _ = w.unminimize();
        let _ = w.show();
        let _ = w.set_focus();
    }
}

/// 最前面にしてよいか：設定がオン・開いている最中でない・同じ画面に全画面の窓（スライドショーなど）が無い
fn want_top(st: &Shared, hwnd: isize) -> bool {
    st.pinned.load(Ordering::SeqCst) && !st.dropped.load(Ordering::SeqCst) && !fullscreen_beside(hwnd)
}

fn hwnd_of(w: &tauri::Window) -> isize {
    #[cfg(windows)]
    {
        w.hwnd().map(|h| h.0 as isize).unwrap_or(0)
    }
    #[cfg(not(windows))]
    {
        let _ = w;
        0
    }
}

/// いま実際に最前面か（Windows では窓の状態をじかに読む。ずれても次の見直しで直る）
fn is_top(st: &Shared, w: &tauri::Window) -> bool {
    #[cfg(windows)]
    {
        let _ = st;
        use windows_sys::Win32::UI::WindowsAndMessaging::{GetWindowLongPtrW, GWL_EXSTYLE, WS_EX_TOPMOST};
        let h = hwnd_of(w);
        h != 0 && unsafe { (GetWindowLongPtrW(h as _, GWL_EXSTYLE) as u32 & WS_EX_TOPMOST) != 0 }
    }
    #[cfg(not(windows))]
    {
        let _ = w;
        st.applied.load(Ordering::SeqCst)
    }
}

/// 最前面を、あるべき状態にそろえる（メインのスレッドで呼ぶ）
fn refresh_top(st: &Shared, w: &tauri::Window) {
    let on = want_top(st, hwnd_of(w));
    if is_top(st, w) != on {
        let _ = w.set_always_on_top(on);
    }
    st.applied.store(on, Ordering::SeqCst);
}

/// GATE と同じ画面に、全画面の窓（PowerPoint のスライドショー・動画の全画面など）があるか。
/// あれば最前面にしない（演者が自分で始めたスライドショーの上にも GATE を重ねない）
#[cfg(windows)]
fn fullscreen_beside(gate: isize) -> bool {
    use windows_sys::Win32::Foundation::{BOOL, HWND, LPARAM, RECT};
    use windows_sys::Win32::Graphics::Dwm::{DwmGetWindowAttribute, DWMWA_CLOAKED};
    use windows_sys::Win32::Graphics::Gdi::{GetMonitorInfoW, MonitorFromWindow, MONITORINFO, MONITOR_DEFAULTTONEAREST};
    use windows_sys::Win32::UI::WindowsAndMessaging::*;
    if gate == 0 {
        return false;
    }
    struct Ctx {
        gate: isize,
        grect: RECT,
        found: bool,
    }
    unsafe extern "system" fn cb(h: HWND, l: LPARAM) -> BOOL {
        let c = &mut *(l as *mut Ctx);
        if h as isize == c.gate || IsWindowVisible(h) == 0 || IsIconic(h) != 0 {
            return 1;
        }
        let ex = GetWindowLongPtrW(h, GWL_EXSTYLE) as u32;
        if ex & (WS_EX_TOOLWINDOW | WS_EX_TRANSPARENT) != 0 {
            return 1; // 重ね表示の道具（録画・オーバーレイなど）は数えない
        }
        let mut cloaked: u32 = 0;
        if DwmGetWindowAttribute(h, DWMWA_CLOAKED as u32, &mut cloaked as *mut u32 as *mut _, 4) == 0 && cloaked != 0 {
            return 1; // 見えていない（別の仮想デスクトップなど）
        }
        let mut cls = [0u16; 64];
        let n = GetClassNameW(h, cls.as_mut_ptr(), 64);
        let name = String::from_utf16_lossy(&cls[..n.max(0) as usize]);
        if matches!(name.as_str(), "Progman" | "WorkerW" | "Shell_TrayWnd" | "Shell_SecondaryTrayWnd") {
            return 1; // デスクトップ・タスクバー
        }
        let style = GetWindowLongPtrW(h, GWL_STYLE) as u32;
        if IsZoomed(h) != 0 && style & WS_CAPTION == WS_CAPTION {
            return 1; // 最大化しただけの普通の窓（編集中の PowerPoint・Explorer など）
        }
        let mut r: RECT = std::mem::zeroed();
        if GetWindowRect(h, &mut r) == 0 {
            return 1;
        }
        // その窓のある画面を、まるごと覆っているか
        let mut mi: MONITORINFO = std::mem::zeroed();
        mi.cbSize = std::mem::size_of::<MONITORINFO>() as u32;
        if GetMonitorInfoW(MonitorFromWindow(h, MONITOR_DEFAULTTONEAREST), &mut mi) == 0 {
            return 1;
        }
        let m = mi.rcMonitor;
        if !(r.left <= m.left && r.top <= m.top && r.right >= m.right && r.bottom >= m.bottom) {
            return 1;
        }
        // その画面と GATE の窓が重なっているか（GATE が2つの画面にまたがっていても見つける）
        let g = &c.grect;
        if g.left < m.right && g.right > m.left && g.top < m.bottom && g.bottom > m.top {
            c.found = true;
            return 0;
        }
        1
    }
    unsafe {
        let mut grect: RECT = std::mem::zeroed();
        if GetWindowRect(gate as HWND, &mut grect) == 0 {
            return false;
        }
        let mut c = Ctx { gate, grect, found: false };
        EnumWindows(Some(cb), &mut c as *mut Ctx as LPARAM);
        c.found
    }
}

#[cfg(not(windows))]
fn fullscreen_beside(_gate: isize) -> bool {
    false
}

/// 最前面の状態を 1 秒ごとに見直す（全画面の窓が出た・消えた）。そろえるのはメインのスレッドで
/// （開く前の「外す」・設定の切り替え・フォーカスの処理と順番がずれないように）
fn top_loop(app: AppHandle, st: Arc<Shared>) {
    loop {
        thread::sleep(Duration::from_secs(1));
        let (a, s2) = (app.clone(), Arc::clone(&st));
        let _ = app.run_on_main_thread(move || {
            if let Some(w) = main_window(&a) {
                refresh_top(&s2, &w.as_ref().window());
            }
        });
    }
}

/// 開く前：常に最前面を外し、エンジン（別のプロセス）が開いた窓を前に出せるようにする
fn drop_for_open(st: &Shared, w: &WebviewWindow) {
    if st.pinned.load(Ordering::SeqCst) {
        st.dropped.store(true, Ordering::SeqCst);
        st.blurred.store(false, Ordering::SeqCst);
        let _ = w.set_always_on_top(false);
    }
    #[cfg(windows)]
    unsafe {
        // いま前にいるのはこの窓なので、ほかのプロセスが前に出ることを許せる
        windows_sys::Win32::UI::WindowsAndMessaging::AllowSetForegroundWindow(u32::MAX); // ASFW_ANY
    }
}

fn restore_pin(st: &Shared, w: &WebviewWindow) {
    st.dropped.store(false, Ordering::SeqCst);
    st.blurred.store(false, Ordering::SeqCst);
    refresh_top(st, &w.as_ref().window());
}

#[tauri::command]
fn slide_opening(window: WebviewWindow, st: State<'_, Arc<Shared>>) {
    st.note("open: 最前面を外す");
    drop_for_open(&st, &window);
}

/// 開けなかったとき：すぐ最前面に戻す
#[tauri::command]
fn slide_open_failed(window: WebviewWindow, st: State<'_, Arc<Shared>>) {
    if st.dropped.load(Ordering::SeqCst) {
        restore_pin(&st, &window);
    }
}

#[tauri::command]
fn get_pinned(app: AppHandle, st: State<'_, Arc<Shared>>) -> bool {
    if !st.ipc_seen.swap(true, Ordering::SeqCst) {
        st.note("画面とつながりました（ipc）");
        if st.selftest {
            let st2 = Arc::clone(&st);
            thread::spawn(move || selftest(app, st2));
        }
    }
    st.pinned.load(Ordering::SeqCst)
}

#[tauri::command]
fn set_pinned(on: bool, app: AppHandle, st: State<'_, Arc<Shared>>) -> bool {
    let st: Arc<Shared> = Arc::clone(&st);
    st.pinned.store(on, Ordering::SeqCst);
    st.dropped.store(false, Ordering::SeqCst);
    st.save_settings();
    let (a, s2) = (app.clone(), Arc::clone(&st));
    let _ = app.run_on_main_thread(move || {
        if let Some(w) = main_window(&a) {
            refresh_top(&s2, &w.as_ref().window());
        }
    });
    if let Some(item) = app.try_state::<PinItem>() {
        let _ = item.0.set_checked(on);
    }
    on
}

struct PinItem(CheckMenuItem<tauri::Wry>);

// ---------------------------------------------------------------- 終了
fn ask_quit(app: &AppHandle) {
    let app2 = app.clone();
    show_main(app);
    app.dialog()
        .message("コピーも止まります（コピー中のファイルは次に起動したときにやり直します）。")
        .title(format!("{} を終了しますか？", APP))
        .kind(MessageDialogKind::Warning)
        .buttons(MessageDialogButtons::OkCancelCustom("終了".into(), "キャンセル".into()))
        .show(move |ok| {
            if ok {
                thread::spawn(move || do_quit(app2));
            }
        });
}

fn do_quit(app: AppHandle) {
    let st = app.state::<Arc<Shared>>().inner().clone();
    let key = fs::read_to_string(st.key_file()).unwrap_or_default();
    let key = key.trim();
    let r = http(st.port, "POST", "/api/shell/quit", &[("X-SW-Shell", key)], Duration::from_secs(5));
    match r {
        Some((200, _)) => {
            st.quitting.store(true, Ordering::SeqCst);
            st.note("終了：エンジンに終了を頼みました");
        }
        Some((409, body)) => {
            let msg = serde_json::from_str::<serde_json::Value>(&body)
                .ok()
                .and_then(|v| v.get("error").and_then(|e| e.as_str()).map(String::from))
                .unwrap_or(body);
            app.dialog().message(msg).title(APP).kind(MessageDialogKind::Info).show(|_| {});
            return;
        }
        None if !ping(st.port) => {
            st.quitting.store(true, Ordering::SeqCst); // エンジンがもう止まっている
        }
        other => {
            st.note(&format!("終了を頼めませんでした: {:?}", other.map(|x| x.0)));
            app.dialog()
                .message("終了できませんでした。画面の左下の［終了］（電源のボタン）で終了してください。")
                .title(APP)
                .kind(MessageDialogKind::Warning)
                .show(|_| {});
            return;
        }
    }
    // エンジンが止まるのを待ってから閉じる（最大 15 秒）
    let t0 = Instant::now();
    while t0.elapsed() < Duration::from_secs(15) && ping(st.port) {
        thread::sleep(Duration::from_millis(300));
    }
    app.exit(0);
}

// ---------------------------------------------------------------- エンジンを見守る
fn fail(app: &AppHandle, msg: String) {
    let app2 = app.clone();
    app.dialog()
        .message(msg)
        .title(format!("{} が止まりました", APP))
        .kind(MessageDialogKind::Error)
        .show(move |_| app2.exit(1));
}

fn start_and_watch(app: AppHandle, st: Arc<Shared>) {
    // 1. エンジンを起動して、応えるまで待つ（同じ版がもう動いていれば、それにつなぐ）
    let mut logp = st.runtime().join("last_run.log");
    let mut spawned = false;
    match ping_version(st.port) {
        Some(v) if v == VERSION => st.note("エンジンはもう動いています（つなぎます）"),
        _ => match spawn_engine(&st, false) {
            // 版の違うエンジンが動いていれば、新しいエンジンが入れ替える
            Ok((c, lp)) => {
                logp = lp;
                *st.child.lock().unwrap() = Some(c);
                spawned = true;
            }
            Err(e) => return fail(&app, e),
        },
    }
    let t0 = Instant::now();
    loop {
        if ping_version(st.port).map(|v| v == VERSION || !spawned).unwrap_or(false) {
            break;
        }
        let exited = {
            let mut g = st.child.lock().unwrap();
            let e = g.as_mut().and_then(|c| c.try_wait().ok().flatten());
            if e.is_some() {
                *g = None; // 終わったものは持ち続けない
            }
            e
        };
        if let Some(code) = exited {
            if !code.success() {
                thread::sleep(Duration::from_millis(300));
                return fail(&app, format!("（終了コード {:?}）\n\n{}\n\n記録: {}", code.code(), log_tail(&logp), logp.display()));
            }
            spawned = false; // 0 で終わった：同じ版がもう動いている（それにつなぐ）
        }
        if t0.elapsed() > Duration::from_secs(120) {
            return fail(&app, format!("エンジンが応えません（ポート {}）。\n\n{}\n\n記録: {}", st.port, log_tail(&logp), logp.display()));
        }
        thread::sleep(Duration::from_millis(250));
    }
    st.note(if spawned { "エンジンが起動しました" } else { "エンジンにつながりました" });
    navigate(&app, &st);

    // 2. 見守る
    //   止まったとき：きちんと終わった（鍵のファイルが消えている：画面の［終了］・新しい版への入れ替え）ならこの窓も閉じる。
    //   鍵が残ったまま止まった（異常終了）なら起動し直す。応えないがポートは使っている（重い処理の最中）なら待つ
    let mut misses = 0u32;
    let mut up_since = Instant::now();
    let mut need_nav = false; // 起動し直したが、まだ画面を開き直せていない
    loop {
        thread::sleep(Duration::from_secs(2));
        if ping(st.port) {
            misses = 0;
            if need_nav {
                need_nav = false;
                navigate(&app, &st);
            }
            if up_since.elapsed() > Duration::from_secs(600) {
                st.restarts.store(0, Ordering::SeqCst); // 10 分動き続けたら数え直す
            }
            continue;
        }
        misses += 1;
        if misses < 3 {
            continue;
        }
        if st.quitting.load(Ordering::SeqCst) {
            app.exit(0);
            return;
        }
        let gone = {
            let mut g = st.child.lock().unwrap();
            match g.as_mut().map(|c| c.try_wait()) {
                Some(Ok(None)) => false, // 自分が起動したエンジンがまだ動いている（応えないだけ）
                Some(_) => {
                    *g = None;
                    true
                }
                None => !port_busy(st.port), // 外で動いていたエンジン：ポートが空いたら止まった
            }
        };
        if !gone {
            if misses % 15 == 0 {
                st.note("エンジンが応えません（動いてはいます。待ちます）");
            }
            continue;
        }
        if !st.key_file().exists() {
            st.note("エンジンが終了しました（画面の［終了］など）");
            app.exit(0);
            return;
        }
        // 異常終了：起動し直す（続けて 10 回まで）
        let n = st.restarts.fetch_add(1, Ordering::SeqCst) + 1;
        st.note(&format!("エンジンが止まったため起動し直します（{} 回目）", n));
        if n > 10 {
            return fail(&app, format!("エンジンが何度も止まりました。\n\n{}\n\n記録: {}", log_tail(&logp), logp.display()));
        }
        match spawn_engine(&st, false) {
            Ok((c, lp)) => {
                logp = lp;
                *st.child.lock().unwrap() = Some(c);
            }
            Err(e) => return fail(&app, e),
        }
        let t1 = Instant::now();
        while !ping(st.port) && t1.elapsed() < Duration::from_secs(60) {
            thread::sleep(Duration::from_millis(300));
        }
        misses = 0;
        up_since = Instant::now();
        if ping(st.port) {
            navigate(&app, &st);
        } else {
            need_nav = true; // 応えたら開き直す
        }
    }
}

fn navigate(app: &AppHandle, st: &Shared) {
    if let Some(w) = main_window(app) {
        match tauri::Url::parse(&st.url()) {
            Ok(u) => {
                if let Err(e) = w.navigate(u) {
                    st.note(&format!("画面を開けません: {}", e));
                }
            }
            Err(e) => st.note(&format!("URL: {}", e)),
        }
    }
}

// ---------------------------------------------------------------- 試験（PADDOCK_SELFTEST=1）：Windows の CI で確かめる
fn selftest(app: AppHandle, st: Arc<Shared>) {
    let out = st.runtime().join("selftest.txt");
    let mut lines = vec!["IPC_OK".to_string()];
    let w = match main_window(&app) {
        Some(w) => w,
        None => return,
    };
    thread::sleep(Duration::from_millis(800));
    lines.push(format!("PINNED={}", st.pinned.load(Ordering::SeqCst)));
    #[cfg(windows)]
    {
        use windows_sys::Win32::UI::WindowsAndMessaging::*;
        let hwnd = w.hwnd().map(|h| h.0 as isize).unwrap_or(0);
        let topmost = |h: isize| unsafe { (GetWindowLongPtrW(h as _, GWL_EXSTYLE) as u32 & WS_EX_TOPMOST) != 0 };
        lines.push(format!("TOPMOST_BEFORE={}", topmost(hwnd)));
        drop_for_open(&st, &w);
        thread::sleep(Duration::from_millis(300));
        lines.push(format!("TOPMOST_DURING_OPEN={}", topmost(hwnd)));
        let _ = Command::new("notepad.exe").spawn();
        thread::sleep(Duration::from_secs(3));
        let fg = unsafe { GetForegroundWindow() } as isize;
        let mut buf = [0u16; 256];
        let n = unsafe { GetWindowTextW(fg as _, buf.as_mut_ptr(), 256) };
        lines.push(format!("FOREGROUND_IS_GATE={}", fg == hwnd));
        lines.push(format!("FOREGROUND_TITLE={}", String::from_utf16_lossy(&buf[..n.max(0) as usize])));
        // GATE に戻る → 最前面に戻る
        let _ = w.set_focus();
        thread::sleep(Duration::from_millis(1500));
        lines.push(format!("TOPMOST_AFTER_RETURN={}", topmost(hwnd)));
    }
    #[cfg(not(windows))]
    {
        drop_for_open(&st, &w);
        lines.push(format!("DROPPED={}", st.dropped.load(Ordering::SeqCst)));
        restore_pin(&st, &w);
        lines.push(format!("RESTORED={}", !st.dropped.load(Ordering::SeqCst)));
    }
    let _ = fs::write(&out, lines.join("\n") + "\n");
    st.note("試験の結果を書きました");
}

// ---------------------------------------------------------------- WebView2 が無いとき
fn webview_missing() -> bool {
    #[cfg(windows)]
    {
        tauri::webview_version().is_err()
    }
    #[cfg(not(windows))]
    {
        false
    }
}

fn main() {
    let dir = exe_dir();
    let port = std::env::var("PADDOCK_PORT").ok().and_then(|p| p.parse().ok()).unwrap_or(DEFAULT_PORT);
    let _ = fs::create_dir_all(dir.join("runtime"));
    let log = OpenOptions::new().create(true).append(true).open(dir.join("runtime").join("shell.log")).ok();
    let pinned = fs::read_to_string(dir.join("runtime").join("shell.json"))
        .ok()
        .and_then(|t| serde_json::from_str::<serde_json::Value>(&t).ok())
        .and_then(|v| v.get("pinned").and_then(|b| b.as_bool()))
        .unwrap_or(true); // 既定：常に最前面
    let st = Arc::new(Shared {
        dir,
        port,
        pinned: AtomicBool::new(pinned),
        dropped: AtomicBool::new(false),
        blurred: AtomicBool::new(false),
        applied: AtomicBool::new(pinned),
        quitting: AtomicBool::new(false),
        restarts: AtomicU32::new(0),
        child: Mutex::new(None),
        log: Mutex::new(log),
        selftest: std::env::var("PADDOCK_SELFTEST").map(|v| v == "1").unwrap_or(false),
        ipc_seen: AtomicBool::new(false),
    });
    st.note(&format!("{} v{} 起動（ポート {}）", APP, VERSION, port));

    if webview_missing() {
        // これまでの形で動かす（エンジンが Chrome / Edge の窓とタスクバーのアイコンを出す）
        st.note("WebView2 が無いため、これまでの形（Chrome / Edge の窓）で起動します");
        // すでに動いていれば、エンジンが自分で画面を開いて終わる
        if let Err(e) = spawn_engine(&st, true) {
            plain_message(APP, &e);
        }
        return;
    }

    // 別の版が動いているとき：前の版なら先に終わってもらう（前の版の窓もいっしょに閉じる）。新しい版なら、この古い版は起動しない
    if let Some(v) = ping_version(port) {
        if !v.is_empty() && vt(&v) > vt(VERSION) {
            plain_message(APP, &format!("新しい版（v{}）が動いています。この古い版（v{}）は起動しません。\n新しい版の PADDOCK_GATE.exe を使ってください。", v, VERSION));
            return;
        }
        if v != VERSION {
            let ppid = ping_ppid(port); // 前の版の窓（エンジンを起動したもの）
            st.note(&format!("別の版（v{}）が動いているため入れ替えます", v));
            match http(port, "POST", "/api/handover", &[("X-SW-Handover", VERSION)], Duration::from_secs(5)) {
                Some((200, _)) => {
                    let t0 = Instant::now();
                    while (ping(port) || port_busy(port)) && t0.elapsed() < Duration::from_secs(40) {
                        thread::sleep(Duration::from_millis(300));
                    }
                    wait_exit(ppid, Duration::from_secs(30)); // 前の版の窓が閉じるのを待つ（同じ窓が2つにならないように）
                }
                Some((409, body)) => {
                    let msg = serde_json::from_str::<serde_json::Value>(&body)
                        .ok()
                        .and_then(|j| j.get("error").and_then(|e| e.as_str()).map(String::from))
                        .unwrap_or(body);
                    plain_message(APP, &format!("前の版（v{}）が動いているため、入れ替えられませんでした。\n{}", v, msg));
                    return;
                }
                _ => {
                    plain_message(
                        APP,
                        &format!("PADDOCK GATE の前の版（v{}）が裏で動いています。\n前の版の画面の［終了］（電源のボタン）で終了してから、もう一度起動してください。", v),
                    );
                    return;
                }
            }
        }
    }

    let st_setup = Arc::clone(&st);
    tauri::Builder::default()
        .plugin(tauri_plugin_single_instance::init(|app, _argv, _cwd| show_main(app)))
        .plugin(tauri_plugin_dialog::init())
        .manage(Arc::clone(&st))
        .invoke_handler(tauri::generate_handler![slide_opening, slide_open_failed, get_pinned, set_pinned])
        .setup(move |app| {
            let st = st_setup;
            let w = WebviewWindowBuilder::new(app, "main", WebviewUrl::App("index.html".into()))
                .title(APP)
                .inner_size(1400.0, 900.0)
                .min_inner_size(960.0, 600.0)
                .always_on_top(st.pinned.load(Ordering::SeqCst))
                .build()?;
            st.applied.store(st.pinned.load(Ordering::SeqCst), Ordering::SeqCst);
            // 画面が小さい PC（1366×768 など）では、はみ出さない大きさにして真ん中へ（隣の画面＝プロジェクターにかからないように）
            if let Ok(Some(m)) = w.current_monitor() {
                let sf = m.scale_factor();
                let (mw, mh) = (m.size().width as f64 / sf, m.size().height as f64 / sf);
                if mw < 1460.0 || mh < 960.0 {
                    let _ = w.set_size(tauri::LogicalSize::new((mw * 0.92).max(800.0), (mh * 0.88).max(560.0)));
                    let _ = w.center();
                }
            }
            let _ = w.set_focus();

            // タスクバー右下のアイコン
            let title = MenuItem::with_id(app, "title", format!("{} v{}（動作中）", APP, VERSION), false, None::<&str>)?;
            let open = MenuItem::with_id(app, "open", "画面を開く", true, None::<&str>)?;
            let pin = CheckMenuItem::with_id(app, "pin", "常に最前面", true, st.pinned.load(Ordering::SeqCst), None::<&str>)?;
            let quit = MenuItem::with_id(app, "quit", "終了", true, None::<&str>)?;
            let sep = PredefinedMenuItem::separator(app)?;
            let menu = Menu::with_items(app, &[&title, &sep, &open, &pin, &quit])?;
            app.manage(PinItem(pin.clone()));
            let mut tb = TrayIconBuilder::with_id("main")
                .tooltip(format!("{} v{}\n動作中（ウィンドウを閉じても、コピーを続けます）", APP, VERSION))
                .menu(&menu)
                .show_menu_on_left_click(false)
                .on_menu_event(|app, ev| match ev.id().as_ref() {
                    "open" => show_main(app),
                    "pin" => {
                        let st = app.state::<Arc<Shared>>();
                        let on = !st.pinned.load(Ordering::SeqCst);
                        set_pinned(on, app.clone(), st);
                        if let Some(w) = main_window(app) {
                            let _ = w.eval("window.dispatchEvent(new Event('paddock-pin'))");
                        }
                    }
                    "quit" => ask_quit(app),
                    _ => {}
                })
                .on_tray_icon_event(|tray, ev| {
                    if let TrayIconEvent::Click { button: MouseButton::Left, button_state: MouseButtonState::Up, .. } = ev {
                        show_main(tray.app_handle());
                    }
                });
            if let Some(icon) = app.default_window_icon() {
                tb = tb.icon(icon.clone());
            }
            tb.build(app)?;

            let handle = app.handle().clone();
            let st2 = Arc::clone(&st);
            thread::spawn(move || start_and_watch(handle, st2));
            let handle = app.handle().clone();
            let st3 = Arc::clone(&st);
            thread::spawn(move || top_loop(handle, st3));
            Ok(())
        })
        .on_window_event(|window, event| {
            let st = window.state::<Arc<Shared>>();
            match event {
                WindowEvent::CloseRequested { api, .. } => {
                    if !st.quitting.load(Ordering::SeqCst) {
                        api.prevent_close(); // 閉じても裏で動く（コピーを続ける）
                        let _ = window.hide();
                        st.note("窓を隠しました（タスクバーのアイコンから開けます）");
                    }
                }
                WindowEvent::Focused(false) => {
                    if st.dropped.load(Ordering::SeqCst) {
                        st.blurred.store(true, Ordering::SeqCst);
                    }
                }
                WindowEvent::Focused(true) => {
                    // 開いたスライドから GATE に戻った → 常に最前面に戻す
                    if st.dropped.load(Ordering::SeqCst) && st.blurred.load(Ordering::SeqCst) {
                        st.dropped.store(false, Ordering::SeqCst);
                        st.blurred.store(false, Ordering::SeqCst);
                        refresh_top(&st, window);
                    }
                }
                _ => {}
            }
        })
        .run(tauri::generate_context!())
        .expect("PADDOCK GATE を起動できませんでした");
}
