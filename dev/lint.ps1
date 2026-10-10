param([string]$Target)
$env:PSModulePath = '/home/claude/tools/psmod' + [IO.Path]::PathSeparator + $env:PSModulePath
Import-Module PSScriptAnalyzer
$settings = @{
  Rules = @{
    PSUseCompatibleSyntax = @{ Enable = $true; TargetVersions = @('5.1') }
    PSUseCompatibleCommands = @{ Enable = $true; TargetProfiles = @('win-48_x64_10.0.17763.0_5.1.17763.316_x64_4.0.30319.42000_framework') }
    PSUseCompatibleTypes = @{ Enable = $true; TargetProfiles = @('win-48_x64_10.0.17763.0_5.1.17763.316_x64_4.0.30319.42000_framework') }
  }
  IncludeRules = @('PSUseCompatibleSyntax','PSUseCompatibleCommands','PSUseCompatibleTypes','PSAvoidUsingCmdletAliases','PSUseDeclaredVarsMoreThanAssignments','PSAvoidAssignmentToAutomaticVariable','PSPossibleIncorrectComparisonWithNull','PSAvoidUsingEmptyCatchBlock')
}
$r = Invoke-ScriptAnalyzer -Path $Target -Settings $settings
if ($r) { $r | ForEach-Object { '{0}:{1} [{2}] {3}' -f $_.ScriptName, $_.Line, $_.RuleName, $_.Message } } else { 'no findings' }
$errs = $null; [void][System.Management.Automation.Language.Parser]::ParseFile($Target, [ref]$null, [ref]$errs); if ($errs) { $errs | ForEach-Object { 'PARSE: ' + $_.Message + ' @' + $_.Extent.StartLineNumber } } else { 'parse ok' }
