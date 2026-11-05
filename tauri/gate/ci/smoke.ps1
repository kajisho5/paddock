# Tauri 版 GATE の起動確認（GitHub Actions の Windows で）
#   起動・画面とのやりとり・常に最前面・開いた窓が前に出る・2回目の起動・窓を閉じても動く・終了
param([Parameter(Mandatory = $true)][string]$Zip, [string]$Out = "smoke")
$ErrorActionPreference = "Continue"
$fail = 0
function Bad($m) { Write-Host "::error::$m"; $script:fail = 1 }
function Ok($m) { Write-Host "OK $m" }

New-Item -ItemType Directory -Force $Out | Out-Null
$Out = (Resolve-Path $Out).Path
$dst = Join-Path $env:RUNNER_TEMP "pg"
Remove-Item -Recurse -Force $dst -ErrorAction SilentlyContinue
Expand-Archive $Zip $dst
$dir = Join-Path $dst "PADDOCK_GATE"
$exe = Join-Path $dir "PADDOCK_GATE.exe"
$rt = Join-Path $dir "runtime"

Add-Type -AssemblyName System.Windows.Forms, System.Drawing
Add-Type @"
using System; using System.Runtime.InteropServices; using System.Text;
public static class W {
  [DllImport("user32.dll", CharSet=CharSet.Unicode)] public static extern IntPtr FindWindow(string c, string t);
  [DllImport("user32.dll")] public static extern bool IsWindowVisible(IntPtr h);
  [DllImport("user32.dll")] public static extern IntPtr PostMessage(IntPtr h, uint m, IntPtr w, IntPtr l);
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

# 窓を閉じても動いている（タスクバーのアイコンから開ける）
$h = [W]::FindWindow($null, "PADDOCK GATE")
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
