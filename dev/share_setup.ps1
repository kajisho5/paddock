param([string]$ParamJson, [string]$ParamFile)
# SW NAS OPERATOR : メインPC⇄バックアップPCのファイル共有をまとめて設定する／元に戻す
# ・利用者が画面で内容を確認して押したときだけ、管理者の確認（UAC）を経て実行される（このウィンドウに経過を表示）
# ・変更する前の状態を、変更するたびに記録し、［元に戻す］で戻す。フォルダとデータは消さない
# ・ネットワークの種類（パブリック／プライベート）は変えない。ファイアウォールは「有線・同じネットワーク内から」だけ許可
# ・Windows PowerShell 5.1 で動くこと（PowerShell 7 専用の書き方を使わない）
$global:ErrorActionPreference = 'Stop'     # モジュールのコマンド（New-SmbShare など）にも効かせる
$ErrorActionPreference = 'Stop'
$script:FwGroup = 'SW NAS OPERATOR'
$script:AcctDesc = 'SW NAS OPERATOR file sharing'
$script:ShareDesc = 'SW NAS OPERATOR'
$script:Steps = New-Object System.Collections.ArrayList
$script:Rec = $null
$script:RecDir = Join-Path $env:ProgramData 'SEVENTHWELL\SW_NAS_OPERATOR'
$script:RecPath = Join-Path $script:RecDir 'share_setup.json'
$script:ResPath = Join-Path $script:RecDir 'result.json'
$script:Services = @('LanmanServer', 'LanmanWorkstation', 'FDResPub', 'fdPHost')

function Add-Step([string]$Key, [string]$Label, $Ok, [string]$Msg) {
    [void]$script:Steps.Add([ordered]@{ key = $Key; label = $Label; ok = $Ok; msg = $Msg })
    $mark = '・'
    if ($Ok -eq $true) { $mark = 'OK' } elseif ($Ok -eq $false) { $mark = 'NG' }
    try { Write-Host ('  [{0}] {1}: {2}' -f $mark, $Label, $Msg) } catch { $null = $_ }
}

function ConvertTo-Hash($Obj) {
    $h = @{}
    if ($null -ne $Obj) {
        if ($Obj -is [System.Collections.IDictionary]) {
            foreach ($k in $Obj.Keys) { $h[$k] = $Obj[$k] }
        } else {
            foreach ($p in $Obj.PSObject.Properties) { $h[$p.Name] = $p.Value }
        }
    }
    return $h
}

function Get-List($Value) {
    $out = New-Object System.Collections.ArrayList
    if ($null -ne $Value) { foreach ($v in @($Value)) { if ($null -ne $v) { [void]$out.Add($v) } } }
    return , $out
}

function Read-JsonFile([string]$Path) {
    if (-not $Path -or -not (Test-Path -LiteralPath $Path)) { return $null }
    $t = [IO.File]::ReadAllText($Path, [Text.Encoding]::UTF8)
    if (-not $t.Trim()) { return $null }
    return ($t | ConvertFrom-Json)
}

function Write-JsonFile([string]$Path, $Obj) {
    $dir = Split-Path -Parent $Path
    if ($dir -and -not (Test-Path -LiteralPath $dir)) { [void][IO.Directory]::CreateDirectory($dir) }
    $json = ConvertTo-Json -InputObject $Obj -Depth 8
    $tmp = $Path + '.tmp'
    [IO.File]::WriteAllText($tmp, $json, (New-Object System.Text.UTF8Encoding($false)))
    Move-Item -LiteralPath $tmp -Destination $Path -Force
}

function Save-Record {
    # 変更するたびに記録する（途中で止まっても［元に戻す］で戻せるように）
    $script:Rec.updated = (Get-Date).ToString('s')
    $script:Rec.computer = [string]$env:COMPUTERNAME
    Write-JsonFile $script:RecPath $script:Rec
    Set-FileOwnerAdmins $script:RecPath
}

function Get-NormPath([string]$Path) {
    return ([IO.Path]::GetFullPath($Path)).TrimEnd('\').ToLowerInvariant()
}

function Test-SamePath([string]$A, [string]$B) {
    if (-not $A -or -not $B) { return $false }
    return ((Get-NormPath $A) -eq (Get-NormPath $B))
}

function Test-Under([string]$Child, [string]$Parent) {
    if (-not $Child -or -not $Parent) { return $false }
    $c = Get-NormPath $Child
    $p = Get-NormPath $Parent
    return ($c -eq $p -or $c.StartsWith($p + '\'))
}

function Get-DriveKind([string]$Path) {
    $drv = New-Object System.IO.DriveInfo($Path.Substring(0, 1))
    return [string]$drv.DriveType
}

function Test-Folder([string]$Path) {
    return (Test-Path -LiteralPath $Path -PathType Container)
}

function Initialize-Folder([string]$Path) {
    # 作ったら $true（すでにあれば $false）
    if (Test-Folder $Path) { return $false }
    [void][IO.Directory]::CreateDirectory($Path)
    return $true
}

function Invoke-Icacls([string[]]$IcaclsArgs) {
    & icacls.exe @IcaclsArgs | Out-Null
    return $LASTEXITCODE
}

function Protect-RecordDir {
    # 記録の置き場所（ProgramData\SEVENTHWELL と その中）：持ち主は管理者、管理者とSYSTEMだけが書ける（ふつうのユーザーは読むだけ）
    # 権限は丸ごと置き換える（前からある別の許可は残さない）
    $sddl = 'O:BAG:SYD:PAI(A;OICI;FA;;;SY)(A;OICI;FA;;;BA)(A;OICI;0x1200a9;;;BU)'
    foreach ($d in @((Split-Path -Parent $script:RecDir), $script:RecDir)) {
        [void][IO.Directory]::CreateDirectory($d)
        $sec = New-Object System.Security.AccessControl.DirectorySecurity
        $sec.SetSecurityDescriptorSddlForm($sddl)
        [IO.Directory]::SetAccessControl($d, $sec)
    }
    foreach ($f in @(Get-ChildItem -LiteralPath $script:RecDir -Force -ErrorAction SilentlyContinue)) {
        $null = Invoke-Icacls @($f.FullName, '/reset', '/C', '/Q')   # 中のファイルの権限も上に合わせる（持ち主は変えない）
    }
}

function Test-TrustedFile([string]$Path) {
    # 記録の持ち主が管理者（またはSYSTEM）か。ふつうのユーザーが置いた記録は信用しない
    try {
        $o = (Get-Acl -LiteralPath $Path).GetOwner([System.Security.Principal.SecurityIdentifier]).Value
        return ($o -eq 'S-1-5-32-544' -or $o -eq 'S-1-5-18')
    } catch { return $false }
}

function Set-FileOwnerAdmins([string]$Path) {
    $null = Invoke-Icacls @($Path, '/setowner', '*S-1-5-32-544', '/C', '/Q')
}

function Test-ExplicitAce([string]$Folder, [string]$Sid) {
    try {
        foreach ($a in @((Get-Acl -LiteralPath $Folder).Access)) {
            if (-not $a.IsInherited) {
                try { if ($a.IdentityReference.Translate([System.Security.Principal.SecurityIdentifier]).Value -eq $Sid) { return $true } } catch { $null = $_ }
            }
        }
    } catch { $null = $_ }
    return $false
}

function Get-FolderAccessSddl([string]$Folder) {
    return (Get-Acl -LiteralPath $Folder).GetSecurityDescriptorSddlForm('Access')
}

function Restore-FolderAccess([string]$Folder, [string]$Sddl) {
    $acl = Get-Acl -LiteralPath $Folder
    $acl.SetSecurityDescriptorSddlForm($Sddl, 'Access')
    Set-Acl -LiteralPath $Folder -AclObject $acl -ErrorAction Stop
}

function Get-ActiveProfileNames {
    # いまつながっているネットワークの種類（ファイアウォールのプロファイル名）
    $names = @()
    try {
        foreach ($cp in @(Get-NetConnectionProfile -ErrorAction Stop)) {
            $c = [string]$cp.NetworkCategory
            if ($c -eq 'DomainAuthenticated') { $c = 'Domain' }
            if ($names -notcontains $c) { $names += $c }
        }
    } catch { $null = $_ }
    return , $names
}

function Get-ActiveScheme {
    $o = (& powercfg.exe /getactivescheme) -join ' '
    $m = [regex]::Match($o, '[0-9a-fA-F]{8}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{12}')
    if (-not $m.Success) { return $null }
    return $m.Value
}

function Get-PowerAc([string]$Scheme, [string]$Setting) {
    # 数値の設定は「最小・最大・増分・AC・DC」の順に 0x… が並ぶ（表示言語に関係なく）
    $o = (& powercfg.exe /q $Scheme SUB_SLEEP $Setting) -join "`n"
    if ($LASTEXITCODE -ne 0) { return $null }
    $m = [regex]::Matches($o, '0x([0-9a-fA-F]{8})')
    if ($m.Count -lt 4) { return $null }
    return [Convert]::ToInt64($m[3].Groups[1].Value, 16)
}

function Set-PowerAc([string]$Scheme, [string]$Setting, [long]$Seconds) {
    & powercfg.exe /setacvalueindex $Scheme SUB_SLEEP $Setting $Seconds | Out-Null
    if ($LASTEXITCODE -ne 0) { throw ('powercfg {0}' -f $LASTEXITCODE) }
    if ($Scheme -eq (Get-ActiveScheme)) {
        & powercfg.exe /setactive $Scheme | Out-Null
        if ($LASTEXITCODE -ne 0) { throw ('powercfg {0}' -f $LASTEXITCODE) }
    }
}

function Get-AutoLogonUser {
    try {
        $v = Get-ItemProperty -Path 'HKLM:\SOFTWARE\Microsoft\Windows NT\CurrentVersion\Winlogon' -Name 'DefaultUserName' -ErrorAction Stop
        return [string]$v.DefaultUserName
    } catch { return '' }
}

function Test-LocalAdmin([string]$Name) {
    # 確かめられないときは「管理者」とみなす（既存のアカウントを使わない側に倒す）
    try {
        $g = Get-CimInstance -ClassName Win32_Group -Filter "LocalAccount=True AND SID='S-1-5-32-544'" -ErrorAction Stop
        $m = @(Get-CimAssociatedInstance -InputObject $g -ResultClassName Win32_UserAccount -ErrorAction Stop | Where-Object { $_.LocalAccount -and [string]$_.Name -eq $Name })
        return ($m.Count -gt 0)
    } catch { return $true }
}

function Get-StartType([string]$Mode) {
    switch ($Mode) { 'Auto' { return 'Automatic' } 'Manual' { return 'Manual' } 'Disabled' { return 'Disabled' } }
    return $null
}

function Get-AdminsName {
    $sid = New-Object System.Security.Principal.SecurityIdentifier('S-1-5-32-544')
    return $sid.Translate([System.Security.Principal.NTAccount]).Value
}

function Get-OpenFileCount([string]$Folder) {
    $n = 0
    foreach ($f in @(Get-SmbOpenFile -ErrorAction SilentlyContinue)) {
        if (Test-Under ([string]$f.Path) $Folder) { $n++ }
    }
    return $n
}

function Wait-Close {
    try { Write-Host ''; Write-Host '終わりました。このウィンドウは数秒で閉じます。'; Start-Sleep -Seconds 4 } catch { $null = $_ }
}

# ------------------------------------------------------------------ 設定
function Invoke-Setup($P) {
    $Rec = $script:Rec
    $uname = [string]$P.user
    $sname = [string]$P.share
    $folder = [string]$P.folder
    $acct = '{0}\{1}' -f $env:COMPUTERNAME, $uname

    # ---- 先に確かめる（ここで止まるときは何も変更しない）
    $pre = @()
    if ($folder -notmatch '^[A-Za-z]:\\.+') { $pre += '共有するフォルダは、このPCのドライブのフォルダを指定してください（例 D:\発表データ）' }
    else {
        try {
            if ((Get-DriveKind $folder) -ne 'Fixed') { $pre += 'このPCの内蔵ドライブ（固定ドライブ）のフォルダを指定してください' }
        } catch { $pre += ('ドライブを確認できません: ' + $_.Exception.Message) }
        foreach ($sys in @($env:SystemRoot, $env:ProgramFiles, ${env:ProgramFiles(x86)}, $env:ProgramData)) {
            if ($sys -and ((Test-Under $folder $sys) -or (Test-Under $sys $folder))) { $pre += 'Windows・アプリのフォルダは共有できません'; break }
        }
        if ($env:SystemDrive -and (Test-SamePath $folder ($env:SystemDrive + '\Users'))) { $pre += 'ユーザーのフォルダそのものは共有できません' }
    }
    if ($Rec.user) {
        $ru = ConvertTo-Hash $Rec.user
        if ($ru.name -and $ru.name -ne $uname) { $pre += ('前回はアカウント「{0}」で設定しています。名前を変えるときは、先に［元に戻す］をしてください' -f $ru.name) }
    }
    if ($Rec.share) {
        $rs = ConvertTo-Hash $Rec.share
        if (($rs.name -and $rs.name -ne $sname) -or ($rs.path -and -not (Test-SamePath $rs.path $folder))) {
            $pre += ('前回は「{0}」（{1}）を共有しています。変えるときは、先に［元に戻す］をしてください' -f $rs.name, $rs.path)
        }
    }
    try {
        $ex = Get-SmbShare -Name $sname -ErrorAction SilentlyContinue
        if ($ex -and -not (Test-SamePath ([string]$ex.Path) $folder)) { $pre += ('共有名「{0}」は別のフォルダ（{1}）で使われています。別の共有名にしてください' -f $sname, $ex.Path) }
    } catch { $pre += ('共有の一覧を読めません: ' + $_.Exception.Message) }
    $u0 = Get-LocalUser -Name $uname -ErrorAction SilentlyContinue
    $ours = $false
    if ($u0) {
        $ours = ([string]$u0.Description -eq $script:AcctDesc)
        if (-not $ours) {
            $who = @([string]$P.current_user, [string]$env:USERNAME, (Get-AutoLogonUser)) | Where-Object { $_ }
            if ($who -contains $uname) { $pre += ('アカウント「{0}」はこのPCにログインしているアカウントです。共有用には別の名前にしてください' -f $uname) }
            elseif (Test-LocalAdmin $uname) { $pre += ('アカウント「{0}」は管理者のアカウントです。共有用には別の名前にしてください' -f $uname) }
        }
    }
    if ($pre.Count) {
        foreach ($m in $pre) { Add-Step 'pre' '確認' $false $m }
        return $false
    }

    $allOk = $true

    # ---- 1. Windowsファイアウォール（このアプリ用の規則。有線（またはWi-Fiも）・同じネットワーク内からだけ）
    try {
        $ifType = 'Wired'
        if ($P.wifi) { $ifType = 'Any' }
        $remote = @(@($P.peer_ips) | Where-Object { [string]$_ -match '^\d{1,3}(\.\d{1,3}){3}$' } | ForEach-Object { [string]$_ })
        $from = '相手のPC（' + ($remote -join '・') + '）からだけ'
        if (-not $remote.Count) { $remote = @('LocalSubnet'); $from = '同じネットワーク内のPCからだけ' }
        $Rec.firewall = $true
        Save-Record
        Get-NetFirewallRule -Group $script:FwGroup -ErrorAction SilentlyContinue | Remove-NetFirewallRule -ErrorAction Stop
        $rules = @(
            @('SWNAS-SMB-TCP-445', 'ファイル共有 (SMB TCP 445)', 'TCP', '445'),
            @('SWNAS-NB-TCP-139', 'ファイル共有 (NetBIOS TCP 139)', 'TCP', '139'),
            @('SWNAS-NB-UDP-137', 'PC名の検索 (NetBIOS UDP 137)', 'UDP', '137'),
            @('SWNAS-NB-UDP-138', 'PC名の検索 (NetBIOS UDP 138)', 'UDP', '138'),
            @('SWNAS-LLMNR-UDP-5355', 'PC名の検索 (LLMNR UDP 5355)', 'UDP', '5355')
        )
        foreach ($r in $rules) {
            New-NetFirewallRule -Name $r[0] -DisplayName ('SW NAS OPERATOR - ' + $r[1]) -Group $script:FwGroup -Direction Inbound -Action Allow -Profile Any -InterfaceType $ifType -RemoteAddress $remote -Protocol $r[2] -LocalPort $r[3] -ErrorAction Stop | Out-Null
        }
        New-NetFirewallRule -Name 'SWNAS-ICMPv4-Echo' -DisplayName 'SW NAS OPERATOR - 応答確認 (ping)' -Group $script:FwGroup -Direction Inbound -Action Allow -Profile Any -InterfaceType $ifType -RemoteAddress $remote -Protocol ICMPv4 -IcmpType 8 -ErrorAction Stop | Out-Null
        $n = @(Get-NetFirewallRule -Group $script:FwGroup -ErrorAction SilentlyContinue).Count
        if ($n -ne 6) { throw ('規則を確認できませんでした（{0}/6）' -f $n) }
        $where = '有線LAN'
        if ($P.wifi) { $where = '有線LAN・Wi-Fi' }
        Add-Step 'firewall' 'Windowsファイアウォール' $true ('{0}、ファイル共有・PC名の検索・pingを許可（{1}）' -f $from, $where)
    } catch { Add-Step 'firewall' 'Windowsファイアウォール' $false ('設定できませんでした: ' + $_.Exception.Message); $allOk = $false }
    try {
        $blocked = @()
        $active = Get-ActiveProfileNames
        foreach ($fp in @(Get-NetFirewallProfile -PolicyStore ActiveStore -ErrorAction Stop)) {
            if ($active.Count -and $active -notcontains [string]$fp.Name) { continue }   # いまつながっているネットワークの種類だけ見る
            if ([string]$fp.Enabled -eq 'False') { continue }
            if ([string]$fp.AllowLocalFirewallRules -eq 'False' -or [string]$fp.AllowInboundRules -eq 'False') { $blocked += [string]$fp.Name }
        }
        if ($blocked.Count) {
            Add-Step 'firewall_gpo' 'ファイアウォールの方針' $false ('このPCの方針（グループポリシーなど）で、追加した規則が使われない設定になっています: ' + ($blocked -join '・') + '。PCの管理者に確認してください')
            $allOk = $false
        }
    } catch { $null = $_ }
    try {
        $fp3 = @(Get-CimInstance -Namespace 'root/SecurityCenter2' -ClassName 'FirewallProduct' -ErrorAction Stop | Where-Object { [string]$_.displayName -notmatch 'Windows' })
        if ($fp3.Count) {
            Add-Step 'firewall3' '他社のセキュリティソフト' $null ('「{0}」が入っています。そちらのファイアウォールでも、ファイル共有の許可が必要な場合があります' -f (($fp3 | ForEach-Object { [string]$_.displayName }) -join '」「'))
        }
    } catch { $null = $_ }

    # ---- 2. サービス（止めることはしない。自動起動にして、止まっていれば起動）
    $known = Get-List $Rec.services
    $bad = @()
    $labels = @{ LanmanServer = 'ファイル共有（Server）'; LanmanWorkstation = 'ほかのPCへの接続（Workstation）'; FDResPub = 'ネットワークにこのPCを表示（FDResPub）'; fdPHost = 'ネットワークのPCを探す（fdPHost）' }
    foreach ($name in $script:Services) {
        $must = ($name -eq 'LanmanServer' -or $name -eq 'LanmanWorkstation')
        try {
            $w = Get-CimInstance -ClassName Win32_Service -Filter ("Name='{0}'" -f $name) -ErrorAction Stop
            if (-not $w) { throw 'サービスが見つかりません' }
            $mode = [string]$w.StartMode
            if ($mode -ne 'Auto') {
                $hit = @($known | Where-Object { $_.name -eq $name })
                if (-not $hit.Count) { [void]$known.Add([ordered]@{ name = $name; start = $mode }); $Rec.services = $known.ToArray(); Save-Record }
                Set-Service -Name $name -StartupType Automatic -ErrorAction Stop
            }
            if ([string]$w.State -ne 'Running') { Start-Service -Name $name -ErrorAction Stop }
        } catch { if ($must) { $bad += ('{0}: {1}' -f $labels[$name], $_.Exception.Message) } }
    }
    $Rec.services = $known.ToArray()
    if ($bad.Count) { Add-Step 'services' 'ファイル共有のサービス' $false ($bad -join ' / '); $allOk = $false }
    else { Add-Step 'services' 'ファイル共有のサービス' $true '自動で起動するように設定（Server・Workstation など）' }

    # ---- 3. SMB2/3（SMB1 は使わない）
    try {
        $c = Get-SmbServerConfiguration -ErrorAction Stop
        if (-not $c.EnableSMB2Protocol) {
            if ($null -eq $Rec.smb2_prev) { $Rec.smb2_prev = $false; Save-Record }
            Set-SmbServerConfiguration -EnableSMB2Protocol $true -Force -ErrorAction Stop
            Add-Step 'smb' 'SMB' $true 'SMB2/3 を有効にしました'
        }
    } catch { Add-Step 'smb' 'SMB' $false ('確認できませんでした: ' + $_.Exception.Message) }

    # ---- 4. 共有用アカウント（普通のアカウント。管理者にはしない）
    $userOk = $false
    $ur = @{ name = $uname; sid = ''; created = $false; enabled_prev = $null; group_added = $false }
    if ($Rec.user) { $ur = ConvertTo-Hash $Rec.user }
    $expires = (Get-Date).AddDays(30)    # ［元に戻す］を忘れても、30日で使えなくなる（設定し直すと延びる）
    try {
        $sec = ConvertTo-SecureString ([string]$P.password) -AsPlainText -Force
        $u = Get-LocalUser -Name $uname -ErrorAction SilentlyContinue
        if (-not $u) {
            $ur.created = $true
            $Rec.user = $ur
            Save-Record
            New-LocalUser -Name $uname -Password $sec -PasswordNeverExpires -UserMayNotChangePassword -AccountExpires $expires -Description $script:AcctDesc -ErrorAction Stop | Out-Null
            $msg = ('アカウント「{0}」を作りました（管理者ではない普通のアカウント。{1}まで使えます）' -f $uname, $expires.ToString('M月d日'))
        } else {
            if ($ours) {
                Set-LocalUser -Name $uname -Password $sec -PasswordNeverExpires $true -AccountExpires $expires -ErrorAction Stop
                $msg = ('アカウント「{0}」のパスワードを設定しました（{1}まで使えます）' -f $uname, $expires.ToString('M月d日'))
            } elseif ($P.set_password) {
                Set-LocalUser -Name $uname -Password $sec -ErrorAction Stop
                $msg = ('アカウント「{0}」のパスワードを変えました' -f $uname)
            } else {
                $msg = ('アカウント「{0}」はすでにあるので、そのまま使います（パスワードは変えていません。両方のPCで同じパスワードにしてください）' -f $uname)
            }
            if (-not $u.Enabled) {
                if ($null -eq $ur.enabled_prev) { $ur.enabled_prev = $false; $Rec.user = $ur; Save-Record }
                Enable-LocalUser -Name $uname -ErrorAction Stop
            }
        }
        $u = Get-LocalUser -Name $uname -ErrorAction Stop
        $ur.sid = [string]$u.SID.Value
        $Rec.user = $ur
        Save-Record
        try {
            Add-LocalGroupMember -SID 'S-1-5-32-545' -Member $uname -ErrorAction Stop
            if (-not $ur.created) { $ur.group_added = $true; $Rec.user = $ur; Save-Record }
        } catch {
            if ([string]$_.FullyQualifiedErrorId -notlike '*MemberExists*') { throw }
        }
        $userOk = $true
        Add-Step 'user' '共有用アカウント' $true $msg
    } catch {
        Add-Step 'user' '共有用アカウント' $false ('作れませんでした: ' + $_.Exception.Message + '（パスワードがこのPCの規則に合わない場合は、長く・複雑にしてください）')
        $allOk = $false
    }

    # ---- 5. フォルダ・権限・共有
    if ($userOk) {
        try {
            $fr = @{ path = $folder; created = $false }
            if ($Rec.folder) { $fr = ConvertTo-Hash $Rec.folder }
            if ((Initialize-Folder $folder) -and -not $Rec.folder) { $fr.created = $true }
            $Rec.folder = $fr
            Save-Record
            $sid = [string]$ur.sid
            if (-not $Rec.acl) {
                $acl = [ordered]@{ path = $folder; sid = $sid; orig = $null }
                if (Test-ExplicitAce $folder $sid) { $acl.orig = Get-FolderAccessSddl $folder }   # 前から権限があれば、元の権限を丸ごと覚えておく
                $Rec.acl = $acl
                Save-Record
            }
            $rc = Invoke-Icacls @($folder, '/grant', ('*{0}:(OI)(CI)M' -f $sid))
            if ($rc -ne 0) { throw ('フォルダの権限を設定できませんでした（icacls {0}）' -f $rc) }

            $sr = @{ name = $sname; path = $folder; created = $false; granted = $null }
            if ($Rec.share) { $sr = ConvertTo-Hash $Rec.share }
            $sh = Get-SmbShare -Name $sname -ErrorAction SilentlyContinue
            if ($sh) {
                $acc = @(Get-SmbShareAccess -Name $sname -ErrorAction Stop | Where-Object { [string]$_.AccountName -eq $acct -and [string]$_.AccessControlType -eq 'Allow' -and [string]$_.AccessRight -eq 'Full' })
                if (-not $acc.Count) {
                    if (-not $sr.created) { $sr.granted = $acct; $Rec.share = $sr; Save-Record }
                    Grant-SmbShareAccess -Name $sname -AccountName $acct -AccessRight Full -Force -ErrorAction Stop | Out-Null
                }
                $smsg = ('「\\{0}\{1}」（{2}）はすでに共有されています。アカウント「{3}」が読み書きできます' -f $env:COMPUTERNAME, $sname, $folder, $uname)
            } else {
                $sr.created = $true
                $Rec.share = $sr
                Save-Record
                New-SmbShare -Name $sname -Path $folder -FullAccess @($acct, (Get-AdminsName)) -CachingMode None -Description $script:ShareDesc -ErrorAction Stop | Out-Null
                $smsg = ('「{0}」を「\\{1}\{2}」として共有しました（アカウント「{3}」が読み書きできます）' -f $folder, $env:COMPUTERNAME, $sname, $uname)
            }
            $Rec.share = $sr
            Save-Record
            $chk = Get-SmbShare -Name $sname -ErrorAction Stop
            if (-not (Test-SamePath ([string]$chk.Path) $folder)) { throw '共有を確認できませんでした' }
            $acc = @(Get-SmbShareAccess -Name $sname -ErrorAction Stop | Where-Object { [string]$_.AccountName -eq $acct -and [string]$_.AccessControlType -eq 'Allow' })
            if (-not $acc.Count) { throw '共有の権限を確認できませんでした' }
            Add-Step 'share' 'フォルダの共有' $true $smsg
        } catch { Add-Step 'share' 'フォルダの共有' $false ('共有できませんでした: ' + $_.Exception.Message); $allOk = $false }
    } else {
        Add-Step 'share' 'フォルダの共有' $false 'アカウントを作れなかったため、共有していません'
    }

    # ---- 6. スリープしない（電源接続時。いまの電源プランに対して。プランごとに元の値を覚える）
    if ($P.nosleep) {
        try {
            $scheme = Get-ActiveScheme
            if (-not $scheme) { throw '今の電源プランを読み取れませんでした（変更していません）' }
            $plist = Get-List $Rec.power
            $hit = @($plist | Where-Object { [string]$_.scheme -eq $scheme })
            if (-not $hit.Count) {
                $st = Get-PowerAc $scheme 'STANDBYIDLE'
                $hb = Get-PowerAc $scheme 'HIBERNATEIDLE'
                if ($null -eq $st) { throw '今の設定を読み取れませんでした（変更していません）' }
                [void]$plist.Add([ordered]@{ scheme = $scheme; standby_ac = $st; hibernate_ac = $hb })
                $Rec.power = $plist.ToArray()
                Save-Record
                $hb0 = $hb
            } else { $hb0 = $hit[0].hibernate_ac }
            Set-PowerAc $scheme 'STANDBYIDLE' 0
            if ($null -ne $hb0) { Set-PowerAc $scheme 'HIBERNATEIDLE' 0 }
            Add-Step 'power' 'スリープ' $true '電源につないでいる間はスリープ・休止状態にしない（いまの電源プラン）'
        } catch { Add-Step 'power' 'スリープ' $false ('設定できませんでした: ' + $_.Exception.Message) }
    }
    return $allOk
}

# ------------------------------------------------------------------ 元に戻す
function Test-ProtectedAccount([string]$Name, $P) {
    # ログイン中・自動ログオン・管理者のアカウントは、無効にしたりグループから外したりしない
    $who = @([string]$P.current_user, [string]$env:USERNAME, (Get-AutoLogonUser)) | Where-Object { $_ }
    if ($who -contains $Name) { return $true }
    return (Test-LocalAdmin $Name)
}

function Invoke-Undo($P) {
    $Rec = $script:Rec
    if (-not $Rec) {
        Add-Step 'undo' '元に戻す' $false '設定の記録がありません（このPCで［このPCを設定する］をしていないか、すでに元に戻しています）'
        return $false
    }
    if ([int]$Rec.version -ne 2) {
        Add-Step 'undo' '元に戻す' $false '設定の記録の形式が違うため、元に戻せません（何も変更していません）'
        return $false
    }
    $ok = $true
    $base = ''
    if ($Rec.share) { $base = [string](ConvertTo-Hash $Rec.share).path }
    if (-not $base -and $Rec.folder) { $base = [string](ConvertTo-Hash $Rec.folder).path }
    if ($Rec.share -and $base) {
        $n = Get-OpenFileCount $base
        if ($n -gt 0) {
            Add-Step 'open' '開いているファイル' $false ('ほかのPCが共有のファイルを開いています（{0}件）。閉じてから、もう一度［元に戻す］を押してください（何も変更していません）' -f $n)
            return $false
        }
    }
    if ($Rec.share) {
        try {
            $s = ConvertTo-Hash $Rec.share
            $w = Get-CimInstance -ClassName Win32_Service -Filter "Name='LanmanServer'" -ErrorAction Stop
            if ($w -and [string]$w.State -ne 'Running') { Start-Service -Name 'LanmanServer' -ErrorAction Stop }   # 止まっていると共有の一覧が読めず、やめられないため
            $cur = Get-SmbShare -Name $s.name -ErrorAction SilentlyContinue
            if ($cur -and -not (Test-SamePath ([string]$cur.Path) ([string]$s.path))) {
                Add-Step 'share' 'フォルダの共有' $null ('「{0}」は別のフォルダの共有になっているので、そのままにしました' -f $s.name)
            } elseif ($s.created) {
                if ($cur -and [string]$cur.Description -ne $script:ShareDesc) {
                    Add-Step 'share' 'フォルダの共有' $null ('「{0}」は作った共有と違うため、そのままにしました' -f $s.name)
                } else {
                    if ($cur) { Remove-SmbShare -Name $s.name -Force -ErrorAction Stop }
                    if (Get-SmbShare -Name $s.name -ErrorAction SilentlyContinue) { throw '共有をやめられませんでした' }
                    Add-Step 'share' 'フォルダの共有' $true ('「{0}」の共有をやめました（フォルダとデータはそのまま）' -f $s.name)
                }
            } elseif ($s.granted) {
                if ($cur) { Revoke-SmbShareAccess -Name $s.name -AccountName $s.granted -Force -ErrorAction Stop | Out-Null }
                Add-Step 'share' 'フォルダの共有' $true ('「{0}」に付けた権限を外しました' -f $s.name)
            }
        } catch { Add-Step 'share' 'フォルダの共有' $false $_.Exception.Message; $ok = $false }
    }
    if ($Rec.acl) {
        try {
            $a = ConvertTo-Hash $Rec.acl
            if ($a.sid -and $a.path -and (Test-SamePath ([string]$a.path) $base) -and (Test-Folder ([string]$a.path))) {
                if ($a.orig) {
                    Restore-FolderAccess ([string]$a.path) ([string]$a.orig)
                    Add-Step 'acl' 'フォルダの権限' $true 'フォルダの権限を元に戻しました'
                } else {
                    $rc = Invoke-Icacls @([string]$a.path, '/remove:g', ('*' + [string]$a.sid))
                    if ($rc -ne 0) { throw ('icacls {0}' -f $rc) }
                    Add-Step 'acl' 'フォルダの権限' $true '付けた権限を外しました'
                }
            }
        } catch { Add-Step 'acl' 'フォルダの権限' $false $_.Exception.Message; $ok = $false }
    }
    if ($Rec.user) {
        try {
            $u = ConvertTo-Hash $Rec.user
            $cur = Get-LocalUser -Name $u.name -ErrorAction SilentlyContinue
            if ($u.created) {
                if ($cur -and [string]$cur.Description -eq $script:AcctDesc -and (-not $u.sid -or [string]$cur.SID.Value -eq [string]$u.sid)) {
                    Remove-LocalUser -Name $u.name -ErrorAction Stop
                    Add-Step 'user' '共有用アカウント' $true ('アカウント「{0}」を削除しました' -f $u.name)
                } elseif ($cur) {
                    Add-Step 'user' '共有用アカウント' $null ('アカウント「{0}」は作ったものと違うため、残しました' -f $u.name)
                }
            } elseif ($cur -and ($u.group_added -or $u.enabled_prev -eq $false)) {
                if (Test-ProtectedAccount ([string]$u.name) $P) {
                    Add-Step 'user' '共有用アカウント' $null ('アカウント「{0}」はログイン・管理者に使われているため、そのままにしました' -f $u.name)
                } else {
                    if ($u.group_added) { try { Remove-LocalGroupMember -SID 'S-1-5-32-545' -Member $u.name -ErrorAction Stop } catch { $null = $_ } }
                    if ($u.enabled_prev -eq $false) { Disable-LocalUser -Name $u.name -ErrorAction Stop }
                    Add-Step 'user' '共有用アカウント' $true ('アカウント「{0}」は元からあったので残しました（無効・グループを元に戻しました）' -f $u.name)
                }
            } elseif ($cur) {
                Add-Step 'user' '共有用アカウント' $true ('アカウント「{0}」は元からあったので残しました' -f $u.name)
            }
        } catch { Add-Step 'user' '共有用アカウント' $false $_.Exception.Message; $ok = $false }
    }
    if ($Rec.firewall) {
        try {
            Get-NetFirewallRule -Group $script:FwGroup -ErrorAction SilentlyContinue | Remove-NetFirewallRule -ErrorAction Stop
            if (@(Get-NetFirewallRule -Group $script:FwGroup -ErrorAction SilentlyContinue).Count) { throw '規則を削除できませんでした' }
            Add-Step 'firewall' 'Windowsファイアウォール' $true '追加した規則を削除しました'
        } catch { Add-Step 'firewall' 'Windowsファイアウォール' $false $_.Exception.Message; $ok = $false }
    }
    $svc = Get-List $Rec.services
    if ($svc.Count) {
        $bad = @()
        $done = 0
        foreach ($s in $svc) {
            $name = [string]$s.name
            $st = Get-StartType ([string]$s.start)
            if (-not ($script:Services -contains $name) -or -not $st) { continue }
            if ($name -eq 'LanmanWorkstation' -and $st -eq 'Disabled') { continue }   # NASにつなぐのに使うので、無効には戻さない
            try { Set-Service -Name $name -StartupType $st -ErrorAction Stop; $done++ } catch { $bad += ('{0}: {1}' -f $name, $_.Exception.Message) }
        }
        if ($bad.Count) { Add-Step 'services' 'サービス' $false ($bad -join ' / '); $ok = $false }
        elseif ($done) { Add-Step 'services' 'サービス' $true '起動の設定を元に戻しました（いま動いているサービスは止めません。次の再起動から元どおり）' }
    }
    if ($Rec.smb2_prev -eq $false) {
        try { Set-SmbServerConfiguration -EnableSMB2Protocol $false -Force -ErrorAction Stop; Add-Step 'smb' 'SMB' $true 'SMB2/3 の設定を元に戻しました' }
        catch { Add-Step 'smb' 'SMB' $false $_.Exception.Message; $ok = $false }
    }
    $plist = Get-List $Rec.power
    if ($plist.Count) {
        try {
            foreach ($pw in $plist) {
                $sc = [string]$pw.scheme
                if ($sc -notmatch '^[0-9a-fA-F]{8}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{12}$') { continue }
                if ($null -ne $pw.standby_ac) { Set-PowerAc $sc 'STANDBYIDLE' ([long]$pw.standby_ac) }
                if ($null -ne $pw.hibernate_ac) { Set-PowerAc $sc 'HIBERNATEIDLE' ([long]$pw.hibernate_ac) }
            }
            Add-Step 'power' 'スリープ' $true 'スリープの設定を元に戻しました'
        } catch { Add-Step 'power' 'スリープ' $false $_.Exception.Message; $ok = $false }
    }
    if ($Rec.folder) {
        $f = ConvertTo-Hash $Rec.folder
        Add-Step 'folder' 'フォルダ' $null ('フォルダとデータは消していません: {0}' -f $f.path)
    }
    return $ok
}

# ------------------------------------------------------------------ 本体
function Invoke-Main([string]$Json, [string]$File) {
    if ($File) { try { Remove-Item -LiteralPath $File -Force -ErrorAction SilentlyContinue } catch { $null = $_ } }   # パスワードを含むので、すぐ消す
    $P = $Json | ConvertFrom-Json
    $result = [ordered]@{ id = [string]$P.job_id; action = [string]$P.action; ok = $false; steps = @(); finished = $null; computer = [string]$env:COMPUTERNAME }
    try { Write-Host 'SW NAS OPERATOR : ファイル共有の設定' ; Write-Host '' } catch { $null = $_ }
    $mtx = $null
    try {
        try { $mtx = New-Object System.Threading.Mutex($false, 'Global\SEVENTHWELL_SWNASOPERATOR_ShareSetup') } catch { $mtx = $null }
        $got = $true
        if ($mtx) { try { $got = $mtx.WaitOne(0) } catch [System.Threading.AbandonedMutexException] { $got = $true } }
        if (-not $got) { $mtx.Dispose(); $mtx = $null; throw '別の設定（または元に戻す）がまだ実行中です。そのウィンドウが閉じてから、もう一度押してください（何も変更していません）' }
        Protect-RecordDir
        if (Test-Path -LiteralPath $script:RecPath) {
            if (Test-TrustedFile $script:RecPath) {
                $raw = Read-JsonFile $script:RecPath
                if ($raw) { $script:Rec = ConvertTo-Hash $raw }
            } else {
                $stamp = (Get-Date).ToString('yyyyMMdd-HHmmss')
                Move-Item -LiteralPath $script:RecPath -Destination ($script:RecPath -replace '\.json$', ('.untrusted-' + $stamp + '.json')) -Force
                Add-Step 'record' '設定の記録' $null '管理者以外が置いた記録があったため、使わずに別の名前にしました'
            }
        }
        if ($P.action -eq 'setup') {
            if ($script:Rec -and [int]$script:Rec.version -ne 2) { throw '設定の記録の形式が違います（何も変更していません）' }
            if (-not $script:Rec) { $script:Rec = @{ version = 2; created = (Get-Date).ToString('s') } }
            $result.ok = Invoke-Setup $P
        } elseif ($P.action -eq 'undo') {
            $result.ok = Invoke-Undo $P
            if ($script:Rec -and $result.ok) {
                $stamp = (Get-Date).ToString('yyyyMMdd-HHmmss')
                Move-Item -LiteralPath $script:RecPath -Destination ($script:RecPath -replace '\.json$', ('.undone-' + $stamp + '.json')) -Force
            }
        } else {
            throw ('unknown action: ' + $P.action)
        }
    } catch {
        Add-Step 'error' 'エラー' $false $_.Exception.Message
        $result.ok = $false
    } finally {
        if ($mtx) { try { $mtx.ReleaseMutex() } catch { $null = $_ }; $mtx.Dispose() }
    }
    $result.steps = $script:Steps.ToArray()
    $result.finished = (Get-Date).ToString('s')
    try { Write-JsonFile $script:ResPath $result } catch { $null = $_ }
    Wait-Close
}

if ($ParamJson) { Invoke-Main $ParamJson $ParamFile }
