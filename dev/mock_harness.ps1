# share_setup.ps1 をLinuxのPowerShellで動かすための模擬環境（Windowsのコマンドを状態つきの関数に置き換える）
# 使い方: pwsh -File mock_harness.ps1 -Script share_setup.ps1 -State state.json -PF params.json -PD <ProgramDataの代わり>
param([string]$Script, [string]$State, [string]$PF, [string]$PD)
$ErrorActionPreference = 'Stop'
$env:COMPUTERNAME = 'MAIN-PC'
$env:USERNAME = '架空オペレーター'
$env:ProgramData = $PD
$env:SystemRoot = 'C:\Windows'
$env:ProgramFiles = 'C:\Program Files'
$env:SystemDrive = 'C:'
$global:M = (Get-Content -Raw -LiteralPath $State | ConvertFrom-Json -AsHashtable)
$global:CALLS = New-Object System.Collections.ArrayList
function global:Log($s) { [void]$global:CALLS.Add($s) }
function global:Fail($k) { if ($global:M.fail -contains $k) { throw "mock: $k failure" } }

function global:Get-NetConnectionProfile { [CmdletBinding()] param()
    foreach ($c in $global:M.netcats) { [pscustomobject]@{ NetworkCategory = $c } } }
function global:Get-NetFirewallRule { [CmdletBinding()] param($Group)
    foreach ($k in @($global:M.fw.Keys)) { if ($global:M.fw[$k].Group -eq $Group) { [pscustomobject]@{ Name = $k; Group = $Group } } } }
function global:Remove-NetFirewallRule { [CmdletBinding()] param([Parameter(ValueFromPipeline = $true)]$InputObject)
    process { if ($InputObject) { if ($global:M.fail -contains 'fwremove') { Write-Error 'mock: fwremove failure (non-terminating)'; return }; $global:M.fw.Remove($InputObject.Name); Log "Remove-NetFirewallRule $($InputObject.Name)" } } }
function global:New-NetFirewallRule { [CmdletBinding()] param($Name, $DisplayName, $Group, $Direction, $Action, $Profile, $InterfaceType, $RemoteAddress, $Protocol, $LocalPort, $IcmpType)
    Fail 'fw'
    if ($global:M.fw.ContainsKey($Name)) { throw "mock: duplicate rule $Name" }
    $global:M.fw[$Name] = @{ Group = $Group; Profile = ($Profile -join ','); InterfaceType = [string]$InterfaceType; RemoteAddress = $RemoteAddress; Protocol = $Protocol; LocalPort = $LocalPort }
    Log "New-NetFirewallRule $Name"; [pscustomobject]@{ Name = $Name } }
function global:Get-NetFirewallProfile { [CmdletBinding()] param($PolicyStore)
    foreach ($n in 'Domain', 'Private', 'Public') {
        $gpo = ($global:M.fwgpo -contains $n)
        [pscustomobject]@{ Name = $n; Enabled = 'True'; AllowLocalFirewallRules = $(if ($gpo) { 'False' } else { 'NotConfigured' }); AllowInboundRules = 'NotConfigured' } } }
function global:Get-CimInstance { [CmdletBinding()] param($ClassName, $Filter, $Namespace)
    if ($ClassName -eq 'FirewallProduct') { foreach ($n in $global:M.fwproducts) { [pscustomobject]@{ displayName = $n } }; return }
    if ($ClassName -eq 'Win32_Group') { return [pscustomobject]@{ Name = 'Administrators'; SID = 'S-1-5-32-544' } }
    if ($ClassName -eq 'Win32_Service') { $n = ([regex]::Match($Filter, "Name='([^']+)'")).Groups[1].Value
        if ($global:M.svc.ContainsKey($n)) { [pscustomobject]@{ Name = $n; StartMode = $global:M.svc[$n].StartMode; State = $global:M.svc[$n].State } } } }
function global:Get-CimAssociatedInstance { [CmdletBinding()] param($InputObject, $ResultClassName)
    foreach ($a in $global:M.admins) { [pscustomobject]@{ Name = $a; LocalAccount = $true } } }
function global:Set-Service { [CmdletBinding()] param($Name, $StartupType)
    $map = @{ Automatic = 'Auto'; Manual = 'Manual'; Disabled = 'Disabled' }
    $global:M.svc[$Name].StartMode = $map[[string]$StartupType]; Log "Set-Service $Name $StartupType" }
function global:Start-Service { [CmdletBinding()] param($Name) $global:M.svc[$Name].State = 'Running'; Log "Start-Service $Name" }
function global:Get-SmbServerConfiguration { [CmdletBinding()] param() [pscustomobject]@{ EnableSMB2Protocol = $global:M.smb2 } }
function global:Set-SmbServerConfiguration { [CmdletBinding()] param($EnableSMB2Protocol, [switch]$Force) $global:M.smb2 = [bool]$EnableSMB2Protocol; Log "Set-SmbServerConfiguration $EnableSMB2Protocol" }
function global:Get-LocalUser { [CmdletBinding()] param($Name)
    if ($global:M.users.ContainsKey($Name)) { $u = $global:M.users[$Name]
        [pscustomobject]@{ Name = $Name; Enabled = $u.Enabled; Description = $u.Description; SID = [pscustomobject]@{ Value = $u.SID } } } }
function global:New-LocalUser { [CmdletBinding()] param($Name, $Password, [switch]$PasswordNeverExpires, [switch]$UserMayNotChangePassword, $AccountExpires, $Description)
    Fail 'newuser'
    $pw = [System.Net.NetworkCredential]::new('', $Password).Password
    $global:M.seq = [int]$global:M.seq + 1
    $global:M.users[$Name] = @{ Enabled = $true; Password = $pw; Description = $Description; Expires = ([datetime]$AccountExpires).ToString('yyyy-MM-dd'); SID = ('S-1-5-21-1-2-3-{0}' -f (1000 + $global:M.seq)) }; Log "New-LocalUser $Name"; [pscustomobject]@{ Name = $Name } }
function global:Set-LocalUser { [CmdletBinding()] param($Name, $Password, $PasswordNeverExpires, $AccountExpires)
    $global:M.users[$Name].Password = [System.Net.NetworkCredential]::new('', $Password).Password
    if ($AccountExpires) { $global:M.users[$Name].Expires = ([datetime]$AccountExpires).ToString('yyyy-MM-dd') }
    Log "Set-LocalUser $Name" }
function global:Enable-LocalUser { [CmdletBinding()] param($Name) $global:M.users[$Name].Enabled = $true; Log "Enable-LocalUser $Name" }
function global:Disable-LocalUser { [CmdletBinding()] param($Name) $global:M.users[$Name].Enabled = $false; Log "Disable-LocalUser $Name" }
function global:Remove-LocalUser { [CmdletBinding()] param($Name)
    $global:M.users.Remove($Name); $global:M.users_group = @($global:M.users_group | Where-Object { $_ -ne $Name }); Log "Remove-LocalUser $Name" }
function global:Add-LocalGroupMember { [CmdletBinding()] param($SID, $Member)
    if ($global:M.users_group -contains $Member) {
        $er = [System.Management.Automation.ErrorRecord]::new([Exception]::new('already a member'), 'MemberExists', 'ResourceExists', $Member)
        $PSCmdlet.ThrowTerminatingError($er) }
    $global:M.users_group = @($global:M.users_group) + $Member; Log "Add-LocalGroupMember $Member" }
function global:Remove-LocalGroupMember { [CmdletBinding()] param($SID, $Member)
    $global:M.users_group = @($global:M.users_group | Where-Object { $_ -ne $Member }); Log "Remove-LocalGroupMember $Member" }
function global:Get-SmbShare { [CmdletBinding()] param($Name)
    if ($global:M.shares.ContainsKey($Name)) { [pscustomobject]@{ Name = $Name; Path = $global:M.shares[$Name].Path; Description = $global:M.shares[$Name].Description } } }
function global:New-SmbShare { [CmdletBinding()] param($Name, $Path, $FullAccess, $CachingMode, $Description)
    if ($global:M.fail -contains 'newshare') { Write-Error 'mock: newshare failure (non-terminating, like CDXML)'; return }
    $global:M.shares[$Name] = @{ Path = $Path; Access = @($FullAccess); CachingMode = [string]$CachingMode; Description = $Description }; Log "New-SmbShare $Name $Path"; [pscustomobject]@{ Name = $Name } }
function global:Remove-SmbShare { [CmdletBinding()] param($Name, [switch]$Force) Fail 'rmshare'; $global:M.shares.Remove($Name); Log "Remove-SmbShare $Name" }
function global:Get-SmbShareAccess { [CmdletBinding()] param($Name)
    foreach ($a in $global:M.shares[$Name].Access) { [pscustomobject]@{ AccountName = $a; AccessControlType = 'Allow'; AccessRight = 'Full' } } }
function global:Grant-SmbShareAccess { [CmdletBinding()] param($Name, $AccountName, $AccessRight, [switch]$Force)
    $global:M.shares[$Name].Access = @($global:M.shares[$Name].Access) + $AccountName; Log "Grant-SmbShareAccess $Name $AccountName" }
function global:Revoke-SmbShareAccess { [CmdletBinding()] param($Name, $AccountName, [switch]$Force)
    $global:M.shares[$Name].Access = @($global:M.shares[$Name].Access | Where-Object { $_ -ne $AccountName }); Log "Revoke-SmbShareAccess $Name $AccountName" }
function global:Get-SmbOpenFile { [CmdletBinding()] param() foreach ($p in $global:M.openfiles) { [pscustomobject]@{ Path = $p } } }

. $Script   # 関数だけ読み込む（-ParamJson なしなので本体は動かない）

# Windows の実行ファイル・ドライブ・レジストリ・ACLを使う関数を、模擬に置き換える
function Get-DriveKind([string]$Path) { if ($global:M.removable -contains $Path.Substring(0, 1)) { return 'Removable' }; return 'Fixed' }
function Test-Folder([string]$Path) { return ($global:M.folders -contains $Path) }
function Initialize-Folder([string]$Path) { if ($global:M.folders -contains $Path) { return $false }; $global:M.folders = @($global:M.folders) + $Path; Log "mkdir $Path"; return $true }
function Invoke-Icacls([string[]]$IcaclsArgs) {
    Log ('icacls ' + ($IcaclsArgs -join ' '))
    if ($IcaclsArgs[1] -eq '/grant') { $e = $IcaclsArgs[0] + '|' + $IcaclsArgs[2]; if (@($global:M.acl) -notcontains $e) { $global:M.acl = @($global:M.acl) + $e } }
    elseif ($IcaclsArgs[1] -eq '/remove:g') { $global:M.acl = @($global:M.acl | Where-Object { -not $_.StartsWith($IcaclsArgs[0] + '|' + $IcaclsArgs[2] + ':') }) }
    return 0 }
function Protect-RecordDir { [void][IO.Directory]::CreateDirectory($script:RecDir); Log 'protect-recdir' }
function Get-ActiveScheme { return [string]$global:M.scheme }
function Test-TrustedFile([string]$Path) { return (-not $global:M.untrusted) }
function Set-FileOwnerAdmins([string]$Path) { }
function Test-ExplicitAce([string]$Folder, [string]$Sid) { return (@($global:M.explicit_ace) -contains $Folder) }
function Get-FolderAccessSddl([string]$Folder) { return 'D:(A;OICI;0x1200a9;;;S-1-5-21-9)' }
function Restore-FolderAccess([string]$Folder, [string]$Sddl) { Log "restore-acl $Folder $Sddl"; $global:M.acl = @($global:M.acl | Where-Object { -not $_.StartsWith($Folder + '|') }) }
function Get-PowerAc([string]$Scheme, [string]$Setting) { return $global:M.power[$Scheme][$Setting] }
function Set-PowerAc([string]$Scheme, [string]$Setting, [long]$Seconds) { $global:M.power[$Scheme][$Setting] = $Seconds; Log "power $Scheme $Setting $Seconds" }
function Get-AdminsName { return 'BUILTIN\Administrators' }
function Get-AutoLogonUser { return [string]$global:M.autologon }
function Wait-Close { }

Invoke-Main ([IO.File]::ReadAllText($PF, [Text.Encoding]::UTF8)) $PF
$global:M.calls = $global:CALLS.ToArray()
[IO.File]::WriteAllText($State, (ConvertTo-Json -InputObject $global:M -Depth 8))
