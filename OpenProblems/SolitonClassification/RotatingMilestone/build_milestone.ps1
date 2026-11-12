$ErrorActionPreference = 'Stop'
$modules = @('RationalBall','FixedBall','Field','FixedField','CandidateInitial',
  'TaylorCoefficients','FixedTaylor','FirstPolynomial60','MetricReset','ResidualODE',
  'BanachRoot','ShootingRoot','CoreAudit')
$buildScript = Join-Path $PSScriptRoot 'check_module.ps1'
foreach ($module in $modules) {
  $logPath = Join-Path $PSScriptRoot ($module + '.build.log')
  & $buildScript ('SolitonClassification/Rotating/' + $module) *> $logPath
  $moduleExit = $LASTEXITCODE
  Write-Output ($module + ': exit ' + $moduleExit)
  if ($moduleExit -ne 0) {
    Get-Content -LiteralPath $logPath -Tail 40
    exit $moduleExit
  }
}
