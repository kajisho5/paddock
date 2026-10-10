/* SW NAS WATCH launcher (SW_NAS_WATCH.exe)
 *
 * Copyright (c) 2026 SEVENTHWELL. All rights reserved.
 *
 * Starts the bundled Python runtime with the application:
 *   <exe dir>\runtime\python\python.exe  <exe dir>\runtime\app\sw_nas_watch.pyc  [args...]
 *
 * - Nothing is installed; no registry / system writes.
 * - Settings are kept next to the exe (SW_NAS_WATCH_HOME tells the app where).
 * - The console window stays: closing it stops monitoring (same as the .bat version).
 */
#define WIN32_LEAN_AND_MEAN
#ifndef UNICODE
#define UNICODE
#endif
#ifndef _UNICODE
#define _UNICODE
#endif
#include <windows.h>
#include <conio.h>
#include <wchar.h>

#define BUF 32768

static wchar_t g_dir[BUF];

static void out(const wchar_t *s)
{
    HANDLE h = GetStdHandle(STD_OUTPUT_HANDLE);
    DWORD n;
    if (h && h != INVALID_HANDLE_VALUE && !WriteConsoleW(h, s, (DWORD)wcslen(s), &n, NULL)) {
        /* redirected: fall back to UTF-8 */
        char tmp[4096];
        int len = WideCharToMultiByte(CP_UTF8, 0, s, -1, tmp, sizeof(tmp), NULL, NULL);
        if (len > 1) WriteFile(h, tmp, (DWORD)(len - 1), &n, NULL);
    }
}

static void wait_key(void)
{
    HANDLE in = GetStdHandle(STD_INPUT_HANDLE);
    DWORD mode;
    if (!in || in == INVALID_HANDLE_VALUE || !GetConsoleMode(in, &mode)) return;  /* not interactive */
    out(L"\r\n  何かキーを押すと閉じます。\r\n");
    FlushConsoleInputBuffer(in);
    _getwch();
}

static void fatal(const wchar_t *msg)
{
    out(L"\r\n  [SW NAS WATCH] ");
    out(msg);
    out(L"\r\n");
    MessageBoxW(NULL, msg, L"SW NAS WATCH", MB_OK | MB_ICONWARNING | MB_SETFOREGROUND);
}

static BOOL WINAPI on_ctrl(DWORD type)
{
    /* Ctrl+C / Ctrl+Break: let the app (child) handle it and wait for it to exit. */
    if (type == CTRL_C_EVENT || type == CTRL_BREAK_EVENT) return TRUE;
    return FALSE;   /* close / logoff / shutdown: default handling */
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

/* Hand our standard handle to the child as an inheritable duplicate.
   (Relying on implicit inheritance fails when stdin/stdout are redirected, e.g. to NUL.) */
static HANDLE std_for_child(DWORD which, HANDLE *dup)
{
    HANDLE h = GetStdHandle(which);
    *dup = NULL;
    if (h == NULL || h == INVALID_HANDLE_VALUE) return NULL;
    if (DuplicateHandle(GetCurrentProcess(), h, GetCurrentProcess(), dup, 0, TRUE, DUPLICATE_SAME_ACCESS))
        return *dup;
    *dup = NULL;
    return h;
}

static int exists_file(const wchar_t *p)
{
    DWORD a = GetFileAttributesW(p);
    return a != INVALID_FILE_ATTRIBUTES && !(a & FILE_ATTRIBUTE_DIRECTORY);
}

int main(void)
{
    static wchar_t py[BUF], app[BUF], cmd[BUF * 2];
    DWORD n = GetModuleFileNameW(NULL, g_dir, BUF);
    wchar_t *slash;
    STARTUPINFOW si;
    PROCESS_INFORMATION pi;
    HANDLE job;
    DWORD code = 1, err;
    const wchar_t *rest;
    HANDLE dups[3];
    BOOL ok;
    int i;

    if (n == 0 || n >= BUF) {
        fatal(L"起動場所を取得できません。");
        wait_key();
        return 1;
    }
    slash = wcsrchr(g_dir, L'\\');
    if (slash) *slash = 0;

    SetConsoleTitleW(L"SW NAS WATCH");

    _snwprintf(py, BUF, L"%ls\\runtime\\python\\python.exe", g_dir);
    _snwprintf(app, BUF, L"%ls\\runtime\\app\\sw_nas_watch.pyc", g_dir);
    py[BUF - 1] = app[BUF - 1] = 0;
    if (!exists_file(py) || !exists_file(app)) {   /* ZIPの中から直接起動した／runtime が無い */
        fatal(L"runtime フォルダが見つかりません。\r\n\r\n"
              L"ZIPファイルを「すべて展開」してから、"
              L"展開したフォルダの SW_NAS_WATCH.exe を起動してください。");
        wait_key();
        return 1;
    }

    rest = skip_argv0(GetCommandLineW());
    if (_snwprintf(cmd, BUF * 2, L"\"%ls\" \"%ls\"%ls%ls", py, app, *rest ? L" " : L"", rest) < 0) {
        fatal(L"引数が長すぎます。");
        wait_key();
        return 1;
    }
    cmd[BUF * 2 - 1] = 0;

    SetEnvironmentVariableW(L"SW_NAS_WATCH_HOME", g_dir);
    SetConsoleCtrlHandler(on_ctrl, TRUE);

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

    ZeroMemory(&si, sizeof(si));
    si.cb = sizeof(si);
    si.dwFlags = STARTF_USESTDHANDLES;
    si.hStdInput = std_for_child(STD_INPUT_HANDLE, &dups[0]);
    si.hStdOutput = std_for_child(STD_OUTPUT_HANDLE, &dups[1]);
    si.hStdError = std_for_child(STD_ERROR_HANDLE, &dups[2]);
    ZeroMemory(&pi, sizeof(pi));
    ok = CreateProcessW(py, cmd, NULL, NULL, TRUE, CREATE_SUSPENDED | CREATE_UNICODE_ENVIRONMENT,
                        NULL, g_dir, &si, &pi);
    err = GetLastError();
    for (i = 0; i < 3; i++)
        if (dups[i]) CloseHandle(dups[i]);
    if (!ok) {
        wchar_t msg[512];
        _snwprintf(msg, 512, L"Python を起動できませんでした。(error %lu)", (unsigned long)err);
        msg[511] = 0;
        fatal(msg);
        wait_key();
        return 1;
    }
    if (job) AssignProcessToJobObject(job, pi.hProcess);   /* failure is harmless */
    ResumeThread(pi.hThread);
    CloseHandle(pi.hThread);

    WaitForSingleObject(pi.hProcess, INFINITE);
    GetExitCodeProcess(pi.hProcess, &code);
    CloseHandle(pi.hProcess);

    if (code != 0) wait_key();   /* keep the error visible (same as "if errorlevel 1 pause") */
    if (job) CloseHandle(job);
    return (int)code;
}
