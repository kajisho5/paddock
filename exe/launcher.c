/* SW NAS WATCH launcher (SW_NAS_WATCH.exe)
 *
 * Copyright (c) 2026 SEVENTHWELL. All rights reserved.
 *
 * Starts the bundled Python runtime with the application:
 *   <exe dir>\runtime\python\python.exe  <exe dir>\runtime\app\sw_nas_watch.pyc  [args...]
 *
 * - Nothing is installed; no registry / system writes.
 * - Settings are kept next to the exe (SW_NAS_WATCH_HOME tells the app where).
 * - No console window. Output goes to runtime\\last_run.log; if the app stops with an error,
 *   the end of that log is shown in a message box. Closing the app window ends the app.
 */
#define WIN32_LEAN_AND_MEAN
#ifndef UNICODE
#define UNICODE
#endif
#ifndef _UNICODE
#define _UNICODE
#endif
#include <windows.h>
#include <wchar.h>

#define BUF 32768

/* アプリごとの名前（受付アプリなどは -D で上書きしてビルドする。既定は SW NAS WATCH） */
#ifndef APP_TITLE
#define APP_TITLE L"SW NAS WATCH"
#endif
#ifndef APP_PYC
#define APP_PYC L"sw_nas_watch.pyc"
#endif
#ifndef APP_EXE
#define APP_EXE L"SW_NAS_WATCH.exe"
#endif
#ifndef HOME_ENV
#define HOME_ENV L"SW_NAS_WATCH_HOME"
#endif

static wchar_t g_dir[BUF];

static void fatal(const wchar_t *msg)
{
    MessageBoxW(NULL, msg, APP_TITLE, MB_OK | MB_ICONWARNING | MB_SETFOREGROUND);
}

static const wchar_t *skip_argv0(const wchar_t *p)
{
    if (*p == L'"') {
        p++;
        while (*p && *p != L'"') p++;
        if (*p) p++;
    } else {
        while (*p && *p != L' ' && *p != L'\t') p++;
    }
    while (*p == L' ' || *p == L'\t') p++;
    return p;
}

/* 子プロセス（Python）に渡すハンドル（継承できるように作る） */
static HANDLE open_inherit(const wchar_t *path, DWORD access, DWORD disp, DWORD share)
{
    SECURITY_ATTRIBUTES sa;
    HANDLE h;
    sa.nLength = sizeof(sa);
    sa.lpSecurityDescriptor = NULL;
    sa.bInheritHandle = TRUE;
    h = CreateFileW(path, access, share, &sa, disp, FILE_ATTRIBUTE_NORMAL, NULL);
    return h == INVALID_HANDLE_VALUE ? NULL : h;
}

/* ログの最後の部分（エラーの内容）を読んで、メッセージとして見せる */
static void show_log_tail(const wchar_t *logp, DWORD code)
{
    static char buf[4097];
    static wchar_t wbuf[4200], msg[4600];
    HANDLE h = *logp ? CreateFileW(logp, GENERIC_READ, FILE_SHARE_READ | FILE_SHARE_WRITE | FILE_SHARE_DELETE, NULL, OPEN_EXISTING, FILE_ATTRIBUTE_NORMAL, NULL) : INVALID_HANDLE_VALUE;
    DWORD n = 0;
    LARGE_INTEGER sz;
    int len;
    wbuf[0] = 0;
    if (h != INVALID_HANDLE_VALUE) {
        if (GetFileSizeEx(h, &sz)) {
            LARGE_INTEGER off;
            off.QuadPart = sz.QuadPart > 4096 ? sz.QuadPart - 4096 : 0;
            SetFilePointerEx(h, off, NULL, FILE_BEGIN);
            if (!ReadFile(h, buf, 4096, &n, NULL)) n = 0;
        }
        CloseHandle(h);
    }
    buf[n] = 0;
    {   /* 途中から読んだときの、こわれた先頭の文字（UTF-8の途中）を飛ばす */
        DWORD i = 0;
        while (i < n && (buf[i] & 0xC0) == 0x80) i++;
        len = MultiByteToWideChar(CP_UTF8, 0, buf + i, -1, wbuf, 4200);
        if (len <= 0) wbuf[0] = 0;
    }
    {   /* 長いときは最後の 1200 文字だけ */
        size_t L = wcslen(wbuf);
        const wchar_t *t = L > 1200 ? wbuf + (L - 1200) : wbuf;
        if (!*logp)
            _snwprintf(msg, 4600, L"%ls が止まりました（終了コード %lu）。\r\n\r\n（記録を書けなかったため、内容を表示できません）",
                       APP_TITLE, (unsigned long)code);
        else
            _snwprintf(msg, 4600, L"%ls が止まりました（終了コード %lu）。\r\n\r\n%ls\r\n\r\n詳しくは次のファイルを見てください:\r\n%ls",
                       APP_TITLE, (unsigned long)code, *t ? t : L"（記録がありません）", logp);
        msg[4599] = 0;
    }
    MessageBoxW(NULL, msg, APP_TITLE, MB_OK | MB_ICONWARNING | MB_SETFOREGROUND);
}

static int exists_file(const wchar_t *p)
{
    DWORD a = GetFileAttributesW(p);
    return a != INVALID_FILE_ATTRIBUTES && !(a & FILE_ATTRIBUTE_DIRECTORY);
}

int WINAPI wWinMain(HINSTANCE hi, HINSTANCE hp, PWSTR cl, int show)
{
    static wchar_t py[BUF], app[BUF], cmd[BUF * 2], logp[BUF];
    DWORD n = GetModuleFileNameW(NULL, g_dir, BUF);
    wchar_t *slash;
    STARTUPINFOW si;
    PROCESS_INFORMATION pi;
    HANDLE job, hlog, hnul;
    DWORD code = 1, err;
    const wchar_t *rest;
    BOOL ok;
    (void)hi; (void)hp; (void)cl; (void)show;

    if (n == 0 || n >= BUF) {
        fatal(L"起動場所を取得できません。");
        return 1;
    }
    slash = wcsrchr(g_dir, L'\\');
    if (slash) *slash = 0;

    _snwprintf(py, BUF, L"%ls\\runtime\\python\\python.exe", g_dir);
    _snwprintf(app, BUF, L"%ls\\runtime\\app\\%ls", g_dir, APP_PYC);
    _snwprintf(logp, BUF, L"%ls\\runtime\\last_run.log", g_dir);
    py[BUF - 1] = app[BUF - 1] = logp[BUF - 1] = 0;
    if (!exists_file(py) || !exists_file(app)) {   /* ZIPの中から直接起動した／runtime が無い */
        fatal(L"runtime フォルダが見つかりません。\r\n\r\n"
              L"ZIPファイルを「すべて展開」してから、"
              L"展開したフォルダの " APP_EXE L" を起動してください。");
        return 1;
    }

    rest = skip_argv0(GetCommandLineW());
    if (_snwprintf(cmd, BUF * 2, L"\"%ls\" \"%ls\"%ls%ls", py, app, *rest ? L" " : L"", rest) < 0) {
        fatal(L"引数が長すぎます。");
        return 1;
    }
    cmd[BUF * 2 - 1] = 0;

    SetEnvironmentVariableW(HOME_ENV, g_dir);
    SetEnvironmentVariableW(L"SW_NAS_AUTOQUIT", L"1");        /* 画面のウィンドウを閉じたら終了する（コンソールを出さないため） */
    SetEnvironmentVariableW(L"PYTHONIOENCODING", L"utf-8");
    SetEnvironmentVariableW(L"PYTHONUNBUFFERED", L"1");

    /* If this launcher is killed, the app goes with it. Processes the app starts
       (the browser window) are not part of the job and are left alone. */
    job = CreateJobObjectW(NULL, NULL);
    if (job) {
        JOBOBJECT_EXTENDED_LIMIT_INFORMATION li;
        ZeroMemory(&li, sizeof(li));
        li.BasicLimitInformation.LimitFlags = JOB_OBJECT_LIMIT_KILL_ON_JOB_CLOSE | JOB_OBJECT_LIMIT_SILENT_BREAKAWAY_OK;
        if (!SetInformationJobObject(job, JobObjectExtendedLimitInformation, &li, sizeof(li))) {
            CloseHandle(job);
            job = NULL;
        }
    }

    /* コンソール（黒い画面）は出さない。出力は runtime\last_run.log に残す（書けないときは捨てる） */
    /* 記録は、ほかで書いている最中のもの（起動中のもう1つ）を消さないよう、書き込みの共有を許さずに開く。
       使われていたら last_run_2.log … を使う。どれも書けなければ捨てる（古い記録をエラーとして見せない） */
    {
        int k;
        hlog = NULL;
        for (k = 1; k <= 5 && !hlog; k++) {
            if (k > 1) _snwprintf(logp, BUF, L"%ls\\runtime\\last_run_%d.log", g_dir, k);
            logp[BUF - 1] = 0;
            hlog = open_inherit(logp, GENERIC_WRITE, CREATE_ALWAYS, FILE_SHARE_READ);
        }
        if (!hlog) {
            logp[0] = 0;
            hlog = open_inherit(L"NUL", GENERIC_WRITE, OPEN_EXISTING, FILE_SHARE_READ | FILE_SHARE_WRITE);
        }
    }
    hnul = open_inherit(L"NUL", GENERIC_READ, OPEN_EXISTING, FILE_SHARE_READ | FILE_SHARE_WRITE);

    ZeroMemory(&si, sizeof(si));
    si.cb = sizeof(si);
    si.dwFlags = STARTF_USESTDHANDLES;
    si.hStdInput = hnul;
    si.hStdOutput = hlog;
    si.hStdError = hlog;
    ZeroMemory(&pi, sizeof(pi));
    ok = CreateProcessW(py, cmd, NULL, NULL, TRUE, CREATE_SUSPENDED | CREATE_UNICODE_ENVIRONMENT | CREATE_NO_WINDOW,
                        NULL, g_dir, &si, &pi);
    err = GetLastError();
    if (hlog) CloseHandle(hlog);
    if (hnul) CloseHandle(hnul);
    if (!ok) {
        wchar_t msg[512];
        _snwprintf(msg, 512, L"Python を起動できませんでした。(error %lu)", (unsigned long)err);
        msg[511] = 0;
        fatal(msg);
        return 1;
    }
    if (job) AssignProcessToJobObject(job, pi.hProcess);   /* failure is harmless */
    ResumeThread(pi.hThread);
    CloseHandle(pi.hThread);

    WaitForSingleObject(pi.hProcess, INFINITE);
    GetExitCodeProcess(pi.hProcess, &code);
    CloseHandle(pi.hProcess);

    if (code != 0) show_log_tail(logp, code);   /* エラーで止まったときは内容を見せる */
    if (job) CloseHandle(job);
    return (int)code;
}
