
$ErrorActionPreference = 'Stop'
$e = [Console]::OutputEncoding
function Out($o) { [Console]::OutputEncoding = [Text.Encoding]::UTF8; [Console]::Out.Write((ConvertTo-Json -InputObject $o -Compress)); [Console]::OutputEncoding = $e }
try {
  $req = [Text.Encoding]::UTF8.GetString([Convert]::FromBase64String($env:SWNAS_PPTREQ)) | ConvertFrom-Json
  $path = [IO.Path]::GetFullPath($req.path)
  $name = [IO.Path]::GetFileName($path)
  try { $pp = [Runtime.InteropServices.Marshal]::GetActiveObject('PowerPoint.Application') } catch { $pp = New-Object -ComObject PowerPoint.Application }
  try { $pp.Visible = -1 } catch {}
  # スライドショーのために窓なしで開いたもの（スライドショーが終わって見えなくなったもの）は閉じておく
  $inShow = @{}
  foreach ($sw in @($pp.SlideShowWindows)) { try { $inShow[$sw.Presentation.FullName] = 1 } catch {} }
  foreach ($p in @($pp.Presentations)) {
    try { if ($p.Windows.Count -eq 0 -and -not $inShow.ContainsKey($p.FullName) -and $p.FullName -ine $path) { $p.Close() } } catch {}
  }
  $pres = $null
  foreach ($p in @($pp.Presentations)) {
    $full = ''
    try { $full = [IO.Path]::GetFullPath($p.FullName) } catch { $full = $p.FullName }
    if ($full -ieq $path) { $pres = $p; break }
    if ($p.Name -ieq $name) { Out @{ err = 'samename'; other = $p.FullName }; exit 0 }
  }
  $ro = 0; if ($req.ro) { $ro = -1 }
  if ($req.show) {
    # スライドショー：編集画面を作らずに開く（編集画面が一瞬前に出てちらつかないように）
    if ($pres -eq $null) { $pres = $pp.Presentations.Open($path, $ro, 0, 0) }
    $w = $null
    foreach ($sw in @($pp.SlideShowWindows)) { if ($sw.Presentation.FullName -ieq $pres.FullName) { $w = $sw } }
    if ($w -eq $null) { $w = $pres.SlideShowSettings.Run() }
    Out @{ ok = 1; hwnd = [int64]$w.HWND }
  } else {
    if ($pres -eq $null) { $pres = $pp.Presentations.Open($path, $ro, 0, -1) }
    elseif ($pres.Windows.Count -eq 0) { try { [void]$pres.NewWindow() } catch {} }   # スライドショー用に窓なしで開いていたもの
    try { $pres.Windows.Item(1).Activate() } catch {}
    Out @{ ok = 1; hwnd = [int64]$pp.HWND }
  }
} catch { Out @{ err = 'com'; msg = $_.Exception.Message } }
