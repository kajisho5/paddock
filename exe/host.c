/* アプリ名のついた Python 本体（runtime\python\<アプリ>_core.exe）
 *
 * python.exe と同じく Py_Main を呼ぶだけ。exe の名前・説明・アイコンをアプリのものにして、
 * タスクマネージャーや「その他のシステムトレイアイコン」に「Python」ではなくアプリ名が出るようにする。
 * python313.dll は同じフォルダのものを使う（python313._pth も DLL の横から読まれる）。
 */
#include <windows.h>
#include <wchar.h>

#ifndef PYDLL
#define PYDLL L"python313.dll"
#endif

typedef int (__cdecl *PYMAIN)(int, wchar_t **);

int wmain(int argc, wchar_t **argv)
{
    static wchar_t path[32768];
    DWORD n = GetModuleFileNameW(NULL, path, 32768);
    wchar_t *slash;
    HMODULE h;
    PYMAIN f;

    if (n == 0 || n >= 32768 - 64) return 9001;
    slash = wcsrchr(path, L'\\');
    if (!slash) return 9001;
    slash[1] = 0;
    wcscat(path, PYDLL);
    h = LoadLibraryExW(path, NULL, LOAD_WITH_ALTERED_SEARCH_PATH);
    if (!h) {
        fwprintf(stderr, L"%ls を読み込めませんでした (error %lu)\n", path, (unsigned long)GetLastError());
        return 9002;
    }
    f = (PYMAIN)(void *)GetProcAddress(h, "Py_Main");
    if (!f) {
        fwprintf(stderr, L"Py_Main が見つかりません\n");
        return 9003;
    }
    return f(argc, argv);
}
