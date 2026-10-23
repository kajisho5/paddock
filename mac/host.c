/* PADDOCK の Mac 版の本体（.app/Contents/MacOS/<アプリ>）
 *
 * Windows のランチャー（exe/launcher.c）＋ Python 本体（exe/host.c）と同じ役目を、1つでする：
 *   ・設定の保存先を ~/Library/Application Support/<アプリ名> にする（.app の中には書かない。署名が壊れるため）
 *   ・同梱の Python（Contents/Resources/python）を読み込み、Contents/Resources/app/<アプリ>.pyc を動かす
 *   ・動作の記録は保存先の last_run.log に残し、エラーで止まったときは内容を表示する
 * Python をこのプロセスの中で動かすので、アクティビティモニタやメニューバーにはアプリ名が出る。
 */
#include <dlfcn.h>
#include <errno.h>
#include <limits.h>
#include <mach-o/dyld.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <unistd.h>

#ifndef APP_TITLE
#define APP_TITLE "PADDOCK SCOUT"
#endif
#ifndef APP_PYC
#define APP_PYC "sw_nas_watch.pyc"
#endif
#ifndef HOME_ENV
#define HOME_ENV "SW_NAS_WATCH_HOME"
#endif
#ifndef PYLIB
#define PYLIB "libpython3.13.dylib"
#endif

typedef int (*PyBytesMain)(int, char **);

static char g_log[PATH_MAX];

static void mkdirs(const char *path)
{
    char tmp[PATH_MAX];
    char *p;
    snprintf(tmp, sizeof(tmp), "%s", path);
    for (p = tmp + 1; *p; p++) {
        if (*p == '/') {
            *p = 0;
            mkdir(tmp, 0755);
            *p = '/';
        }
    }
    mkdir(tmp, 0755);
}

/* エラーで止まったとき：記録の最後を見せる（Finder から起動すると、ほかに知る方法がない） */
static void show_error(const char *what)
{
    char tail[1500] = "";
    char cmd[4096];
    FILE *f = fopen(g_log, "r");
    size_t i, j = 0;
    if (f) {
        long size;
        fseek(f, 0, SEEK_END);
        size = ftell(f);
        fseek(f, size > 1200 ? size - 1200 : 0, SEEK_SET);
        j = fread(tail, 1, sizeof(tail) - 1, f);
        tail[j] = 0;
        fclose(f);
    }
    /* シェルの "..." に入れるため、" \ $ ` を外す */
    for (i = 0; tail[i]; i++)
        if (tail[i] == '"' || tail[i] == '\\' || tail[i] == '$' || tail[i] == '`') tail[i] = '\'';
    snprintf(cmd, sizeof(cmd),
             "/usr/bin/osascript -e 'on run argv' -e 'display alert (item 1 of argv) message (item 2 of argv) as warning' -e 'end run' "
             "\"%s が止まりました\" \"%s\n\n%s\n\n記録: %s\" >/dev/null 2>&1",
             APP_TITLE, what, tail, g_log);
    if (system(cmd) == -1) { /* 何もしない */ }
}

int main(int argc, char **argv)
{
    char exe[PATH_MAX], real[PATH_MAX], contents[PATH_MAX], res[PATH_MAX];
    char pyhome[PATH_MAX], lib[PATH_MAX], pyc[PATH_MAX], data[PATH_MAX], icon[PATH_MAX];
    uint32_t n = sizeof(exe);
    const char *home = getenv("HOME");
    char *slash;
    void *h;
    PyBytesMain py_main;
    char **nargv;
    int i, k = 0, code;

    if (_NSGetExecutablePath(exe, &n) != 0 || !realpath(exe, real)) {
        fprintf(stderr, "起動場所を取得できません\n");
        return 1;
    }
    /* .../X.app/Contents/MacOS/<exe> → .../X.app/Contents */
    snprintf(contents, sizeof(contents), "%s", real);
    if ((slash = strrchr(contents, '/'))) *slash = 0;
    if ((slash = strrchr(contents, '/'))) *slash = 0;
    snprintf(res, sizeof(res), "%s/Resources", contents);
    snprintf(pyhome, sizeof(pyhome), "%s/python", res);
    snprintf(lib, sizeof(lib), "%s/lib/%s", pyhome, PYLIB);
    snprintf(pyc, sizeof(pyc), "%s/app/%s", res, APP_PYC);
    snprintf(icon, sizeof(icon), "%s/menubar.png", res);
    snprintf(data, sizeof(data), "%s/Library/Application Support/%s", home ? home : "/tmp", APP_TITLE);
    mkdirs(data);
    snprintf(g_log, sizeof(g_log), "%s/last_run.log", data);

    setenv(HOME_ENV, data, 1);
    setenv("SW_NAS_AUTOQUIT", "1", 1);        /* PADDOCK SCOUT：画面を閉じたら終了（Windows と同じ） */
    setenv("SW_NAS_MENUBAR_ICON", icon, 1);
    setenv("PYTHONHOME", pyhome, 1);
    setenv("PYTHONNOUSERSITE", "1", 1);
    setenv("PYTHONIOENCODING", "utf-8", 1);
    setenv("PYTHONUNBUFFERED", "1", 1);
    setenv("PYTHONDONTWRITEBYTECODE", "1", 1); /* .app の中に書かない */
    unsetenv("PYTHONPATH");

    /* 端末から起動したとき（SW_NAS_CONSOLE=1）以外は、出力を記録ファイルへ */
    if (!getenv("SW_NAS_CONSOLE")) {
        if (freopen(g_log, "w", stdout)) dup2(fileno(stdout), fileno(stderr));
    }

    nargv = calloc((size_t)argc + 3, sizeof(char *));
    if (!nargv) return 1;
    nargv[k++] = real;
    nargv[k++] = pyc;
    for (i = 1; i < argc; i++) {
        if (strncmp(argv[i], "-psn_", 5) == 0) continue;   /* 古い macOS が付ける引数 */
        nargv[k++] = argv[i];
    }
    nargv[k] = NULL;

    h = dlopen(lib, RTLD_NOW | RTLD_GLOBAL);
    if (!h) {   /* 共有ライブラリの無い Python のときは、python を直接動かす */
        char pybin[PATH_MAX];
        snprintf(pybin, sizeof(pybin), "%s/bin/python3", pyhome);
        if (access(pybin, X_OK) == 0) {
            nargv[0] = pybin;
            execv(pybin, nargv);
        }
        fprintf(stderr, "Python を読み込めませんでした: %s\n", dlerror());
        fflush(stderr);
        show_error("同梱の Python を読み込めませんでした。");
        return 1;
    }
    py_main = (PyBytesMain)dlsym(h, "Py_BytesMain");
    if (!py_main) {
        fprintf(stderr, "Py_BytesMain が見つかりません\n");
        fflush(stderr);
        show_error("同梱の Python が壊れています。");
        return 1;
    }

    code = py_main(k, nargv);
    fflush(stdout);
    fflush(stderr);
    if (code != 0) show_error("エラーで止まりました。");
    return code;
}
