fn main() {
    // 画面（このPCのエンジンの http://127.0.0.1:<ポート>/）から呼べるコマンド。capabilities/default.json で許可する
    tauri_build::try_build(tauri_build::Attributes::new().app_manifest(
        tauri_build::AppManifest::new().commands(&["slide_opening", "slide_open_failed", "get_pinned", "set_pinned"]),
    ))
    .expect("tauri-build に失敗しました");
}
