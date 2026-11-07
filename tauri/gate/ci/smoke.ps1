# Tauri 版 GATE の起動確認（GitHub Actions の Windows で）
#   起動・画面とのやりとり・常に最前面・開いた窓が前に出る・2回目の起動・窓を閉じても動く・終了
param([Parameter(Mandatory = $true)][string]$Zip, [string]$Out = "smoke")
$ErrorActionPreference = "Continue"
$fail = 0
function Bad($m) { Write-Host "::error::$m"; $script:fail = 1 }
function Ok($m) { Write-Host "OK $m" }

New-Item -ItemType Directory -Force $Out | Out-Null
$Out = (Resolve-Path $Out).Path
$dst = Join-Path $env:RUNNER_TEMP "試験 用 フォルダ"   # 日本語・空白の入った場所でも動くか
Remove-Item -Recurse -Force $dst -ErrorAction SilentlyContinue
Expand-Archive $Zip $dst
$dir = Join-Path $dst "PADDOCK_GATE"
$exe = Join-Path $dir "PADDOCK_GATE.exe"
$rt = Join-Path $dir "runtime"

Add-Type -AssemblyName System.Windows.Forms, System.Drawing
Add-Type @"
using System; using System.Runtime.InteropServices; using System.Text;
public static class W {
  public delegate bool EnumProc(IntPtr h, IntPtr l);
  [DllImport("user32.dll")] public static extern bool EnumWindows(EnumProc f, IntPtr l);
  [DllImport("user32.dll")] public static extern uint GetWindowThreadProcessId(IntPtr h, out uint pid);
  [DllImport("user32.dll", CharSet=CharSet.Unicode)] public static extern int GetWindowText(IntPtr h, StringBuilder s, int n);
  [DllImport("user32.dll")] public static extern bool IsWindowVisible(IntPtr h);
  [DllImport("user32.dll")] public static extern IntPtr PostMessage(IntPtr h, uint m, IntPtr w, IntPtr l);
  [DllImport("user32.dll")] public static extern IntPtr GetWindowLongPtr(IntPtr h, int i);
  public static IntPtr Find(uint want) {
    IntPtr found = IntPtr.Zero;
    EnumWindows((h, l) => { uint pid; GetWindowThreadProcessId(h, out pid); var sb = new StringBuilder(256); GetWindowText(h, sb, 256);
      if (pid == want && sb.ToString().Contains("PADDOCK GATE")) { found = h; return false; } return true; }, IntPtr.Zero);
    return found;
  }
  public static bool Top(IntPtr h) { return ((long)GetWindowLongPtr(h, -20) & 0x8) != 0; }
  [StructLayout(LayoutKind.Sequential)] public struct RECT { public int L, T, R, B; }
  [StructLayout(LayoutKind.Sequential)] public struct PT { public int X, Y; }
  [DllImport("user32.dll")] public static extern bool GetWindowRect(IntPtr h, out RECT r);
  [DllImport("user32.dll")] public static extern IntPtr WindowFromPoint(PT p);
  [DllImport("user32.dll")] public static extern IntPtr GetAncestor(IntPtr h, uint f);
  // GATE の窓の真ん中に見えているのが、GATE 自身か
  public static bool Visible(IntPtr h, uint pid) {
    RECT r; if (!GetWindowRect(h, out r)) return false;
    PT p; p.X = (r.L + r.R) / 2; p.Y = (r.T + r.B) / 2;
    IntPtr w = GetAncestor(WindowFromPoint(p), 2); uint q; GetWindowThreadProcessId(w, out q); return q == pid;
  }
}
"@
function Shot($name) {
  try {
    $b = [System.Windows.Forms.Screen]::PrimaryScreen.Bounds
    $bmp = New-Object System.Drawing.Bitmap $b.Width, $b.Height
    $g = [System.Drawing.Graphics]::FromImage($bmp); $g.CopyFromScreen($b.Location, [System.Drawing.Point]::Empty, $b.Size)
    $bmp.Save((Join-Path $Out "$name.png")); $g.Dispose(); $bmp.Dispose()
  } catch { Write-Host "（画面を撮れませんでした: $_）" }
}
function Ping() {
  try { $r = Invoke-WebRequest -UseBasicParsing http://127.0.0.1:8797/api/ping -TimeoutSec 2; return $r.Content } catch { return "" }
}
function Count($n) { @(Get-Process -Name $n -ErrorAction SilentlyContinue).Count }

$env:PADDOCK_SELFTEST = "1"
Start-Process $exe | Out-Null
$v = ""
for ($i = 0; $i -lt 90 -and -not ($v -match "PADDOCK GATE"); $i++) { Start-Sleep 1; $v = Ping }
if ($v -match "PADDOCK GATE") { Ok "エンジンが応える $v" } else { Bad "エンジンが応えない" }

for ($i = 0; $i -lt 60 -and -not (Test-Path "$rt\selftest.txt"); $i++) { Start-Sleep 1 }
Shot "1-start"
if (Test-Path "$rt\selftest.txt") {
  $t = Get-Content "$rt\selftest.txt" -Raw; Write-Host $t
  if ($t -match "IPC_OK") { Ok "画面と窓がやりとりできる" } else { Bad "画面と窓がやりとりできない" }
  if ($t -match "TOPMOST_BEFORE=true") { Ok "常に最前面（既定）" } else { Bad "常に最前面になっていない" }
  if ($t -match "TOPMOST_DURING_OPEN=false") { Ok "開くときは最前面を外す" } else { Bad "開くときに最前面が外れない" }
  if ($t -match "FOREGROUND_IS_GATE=false") { Ok "開いた窓が前に出た" } else { Bad "開いた窓が前に出ない" }
  if ($t -match "TOPMOST_AFTER_RETURN=true") { Ok "GATE に戻ると最前面に戻る" } else { Bad "GATE に戻っても最前面に戻らない" }
} else { Bad "画面とのやりとりの試験結果が無い" }
Get-Process notepad -ErrorAction SilentlyContinue | Stop-Process -Force

# 2回目の起動：新しく増えない（開いている窓が前に出るだけ）
Start-Process $exe | Out-Null
Start-Sleep 6
if ((Count "PADDOCK_GATE") -eq 1) { Ok "2回目の起動で増えない" } else { Bad "2回目の起動で窓が増えた（$(Count 'PADDOCK_GATE')）" }
if ((Count "PADDOCK_GATE_core") -eq 1) { Ok "エンジンは1つ" } else { Bad "エンジンが $(Count 'PADDOCK_GATE_core') 個" }

# 同じ画面に全画面の窓（スライドショーなど）が出たら、最前面をやめる。消えたら戻す
$gp = (Get-Process -Name PADDOCK_GATE | Select-Object -First 1).Id
$h = [W]::Find([uint32]$gp)
if ($h -ne [IntPtr]::Zero) {
  $fs = Start-Process pwsh -PassThru -WindowStyle Hidden -ArgumentList "-NoProfile", "-Command", "Add-Type -AssemblyName System.Windows.Forms; `$f = New-Object System.Windows.Forms.Form; `$f.Text='架空の全画面'; `$f.FormBorderStyle='None'; `$f.WindowState='Maximized'; `$f.Show(); `$t=[DateTime]::Now; while(([DateTime]::Now-`$t).TotalSeconds -lt 18){ [System.Windows.Forms.Application]::DoEvents(); Start-Sleep -Milliseconds 50 }"
  # 全画面の窓が出るまで待つ（CI の PC が遅いときもあるので、最大 15 秒）
  for ($i = 0; $i -lt 30 -and [W]::Top($h); $i++) { Start-Sleep -Milliseconds 500 }
  Start-Sleep 1
  Shot "3-fullscreen"
  if (-not [W]::Top($h)) { Ok "全画面の窓があると最前面をやめる" } else { Bad "全画面の窓があっても最前面のまま" }
  if (-not [W]::Visible($h, [uint32]$gp)) { Ok "全画面の窓の後ろに回る" } else { Bad "全画面の窓の上に GATE が見えている" }
  $fs | Wait-Process -Timeout 20 -ErrorAction SilentlyContinue
  Start-Sleep 3
  if ([W]::Top($h)) { Ok "全画面の窓が消えると最前面に戻る" } else { Bad "全画面の窓が消えても最前面に戻らない" }
}

# 窓を閉じても動いている（タスクバーのアイコンから開ける）
if ($h -ne [IntPtr]::Zero) {
  [W]::PostMessage($h, 0x0010, [IntPtr]::Zero, [IntPtr]::Zero) | Out-Null   # WM_CLOSE
  Start-Sleep 3
  if (-not [W]::IsWindowVisible($h) -and (Count "PADDOCK_GATE") -eq 1 -and (Ping) -match "PADDOCK GATE") { Ok "窓を閉じても裏で動く" } else { Bad "窓を閉じたら止まった／隠れない" }
  Start-Process $exe | Out-Null   # もう一度起動 → 窓が出る
  Start-Sleep 4
  if ([W]::IsWindowVisible($h)) { Ok "もう一度起動すると窓が出る" } else { Bad "もう一度起動しても窓が出ない" }
  Shot "2-reopen"
} else { Bad "PADDOCK GATE の窓が見つからない" }

# 終了（タスクバーのアイコンの［終了］と同じ頼み方）
$key = (Get-Content "$rt\shell.key" -Raw).Trim()
try { Invoke-WebRequest -UseBasicParsing -Method POST -Headers @{ "X-SW-Shell" = $key } -ContentType "application/json" -Body "{}" http://127.0.0.1:8797/api/shell/quit | Out-Null } catch { Bad "終了を頼めない: $_" }
for ($i = 0; $i -lt 30 -and ((Count "PADDOCK_GATE") + (Count "PADDOCK_GATE_core")) -gt 0; $i++) { Start-Sleep 1 }
if (((Count "PADDOCK_GATE") + (Count "PADDOCK_GATE_core")) -eq 0) { Ok "終了した" } else { Bad "終了しない" }

Copy-Item "$rt\shell.log", "$rt\last_run.log", "$rt\selftest.txt" $Out -ErrorAction SilentlyContinue
exit $fail
