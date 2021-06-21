[CmdletBinding()]
param(
        # Path to msbuild.exe
        [Parameter(Mandatory=$true)]
        $msbuild,
        
        # Path to nuget.exe
        [Parameter(Mandatory=$true)]
        $nuget,

        # Directory in which nuget should be created
        [Parameter(Mandatory=$true)]
        $outputDir,

        # Nuget.org Api Key
        [Parameter(Mandatory=$true)]
        $ApiKey,

        # A binary package version to use, in YYYY.MM.DD format
        [Parameter()]
        [AllowNull()]
        [string] $Version,

        # Should a pre-release or a release nuget be produced (pre-release by default)
        [switch]$PreRelease=$true
)

<#
    .SYNOPSIS
    Updates version number in nuspec
#>
function UpdateVersionInNuspec{
    [CmdletBinding()] param([string] $nuspecPath, [string] $version)

    $xml = New-Object XML
    $xml.Load($nuspecPath)
    
    $element = $xml.SelectSingleNode("//package/metadata/version")
    $element.InnerText = $version

    $xml.Save($nuspecPath)
}

<#
    .SYNOPSIS
    Finds latest F* windows binary package available on Github Releases.
#>
function FindBinaryPackage{
    [CmdletBinding()] param([string] $repo, [string]$version, [bool]$prerelease)
    
    $releasesUri = "https://api.github.com/repos/$repo/releases"
    $releases = 
        Invoke-WebRequest $releasesUri | 
        ConvertFrom-Json 
        
    # Assumption is that all binary packages as versioned with YYYY.MM.DD. By default they are 
    # produced as pre-release and some of them are manually marked as released. 
    $releases = 
        $releases | % {
            [PSCustomObject]@{
                name = $_.name
                tag_name = $_.tag_name
                pre_release = $_.prerelease
                # For some reason '\d{4}' or '[0-9]{4}' do not work
                asset = @($_.assets | Where-Object { $_.name -like 'fstar_[0-9][0-9][0-9][0-9].[0-9][0-9].[0-9][0-9]_Windows_x64*'} | % { [PSCustomObject]@{ name = $_.name; url = $_.browser_download_url }})
            } 
        } |
        Where-Object { $_.asset.Count -eq 1 }

    # pick a particular version or latest by default
    if ($version) {
        $releases = $releases | Where-Object { $_.asset.name.Substring(6,10) -ieq $version -and $_.pre_release -eq $prerelease }
    } else {
        $releases = $releases | Where-Object { $_.pre_release -eq $prerelease }
    }

    if ($releases.Count -eq 0) {
        throw "Could not find a suitable windows binary package"
    }

    $package = 
        [PSCustomObject]@{
            name = $releases[0].name
            tag_name = $releases[0].tag_name
            pre_release = $releases[0].pre_release
            version = "0.$($releases[0].asset.name.Substring(6, 10))" # The date part of the filename
            filename = $releases[0].asset.name
            downloadUrl = $releases[0].asset.url
        }

    $package
}

<#
    .SYNOPSIS
    Fetches latest available F* windows binary package from Github Releases.
#>
function GetWindowsBinaryPackage{
    [CmdletBinding()] param($package, [object] $outputDir)

    $zip = Join-Path -Path $outputDir -ChildPath $package.filename
    Write-Host "Downloading $package.downloadUrl to $zip"
    Invoke-WebRequest $package.downloadUrl -OutFile $zip
    
    Write-Host "Extracting $zip"
    Expand-Archive $zip -Force

    $localPath = Join-Path -Path ([IO.Path]::GetFileNameWithoutExtension($package.filename)) -ChildPath "fstar"
    $FStarRootPath = Join-Path -Path $outputDir -ChildPath $localPath
    return $FStarRootPath
}

<#
    .SYNOPSIS
    Compiles ulibfs.fsproj located in $FStarRootPath/ulib
#>
function CompileUlibfs{
    [CmdletBinding()] param([string] $MSBuildExe, [string] $FStarRootPath)
    $ulibfs = Join-Path -Path $FStarRootPath -ChildPath "ulib\ulibfs.fsproj"
    & $MSBuildExe @("/p:BuildProjectReferences=false", "/p:Configuration=Release", $ulibfs)
}

function PackageAsNuget{
    [CmdletBinding()] param([string] $NugetPath, [string] $FStarPath, [string] $outputDir, [string] $version)

    $nuget_dir = Join-Path -Path $outputDir -ChildPath "fstar"

    $fstarbin_path = Join-Path -Path $FStarPath -ChildPath "bin"
    $ulib_path = Join-Path -Path $FStarPath -ChildPath "ulib"
    $ulibfs_path = Join-Path -Path $FStarPath -ChildPath "bin\ulibfs.*" # we need to copy dll, pdb and xml

    $bin_files = 
        @("fstar.exe", "z3.exe", 
          "libgmp-10.dll", 
          "libz3.dll", "libz3.lib", "libz3java.dll", "libz3java.lib", "Microsoft.Z3.dll", 
          "msvcp120.dll", "msvcp120d.dll", "msvcr120.dll", "msvcr120d.dll", "vcomp120.dll", "vcomp120d.dll")

    Write-Host "Creating nuget structure"
    $nuget_dir_tools = Join-Path -Path $nuget_dir -ChildPath "tools"
    $nuget_dir_tools_bin = Join-Path -Path $nuget_dir -ChildPath "tools\bin"
    $nuget_dir_lib = Join-Path -Path $nuget_dir -ChildPath "lib"
    $nuget_dir_build = Join-Path -Path $nuget_dir -ChildPath "build"

    New-Item $nuget_dir -ItemType Directory -Force | Out-Null
    New-Item $nuget_dir_tools -ItemType Directory -Force | Out-Null
    New-Item $nuget_dir_tools_bin -ItemType Directory -Force | Out-Null
    New-Item $nuget_dir_lib -ItemType Directory -Force | Out-Null
    New-Item $nuget_dir_build -ItemType Directory -Force | Out-Null

    Write-Host "Copying files..."

    # Copy relevant contents of <FStar_root>/bin to tools/bin
    ForEach ($bin_file in $bin_files) {
        $bin_file_path = Join-Path -Path $fstarbin_path -ChildPath $bin_file
        Copy-Item -Path $bin_file_path -Destination $nuget_dir_tools_bin -Force
    }

    # Do not include ulibfs build artifacts in the ulib
    $ulib_obj = Join-Path -Path $ulib_path -ChildPath "obj"
    $ulib_bin = Join-Path -Path $ulib_path -ChildPath "bin"
    Remove-Item -Path $ulib_obj -Recurse -Force -ErrorAction Continue
    Remove-Item -Path $ulib_bin -Recurse -Force -ErrorAction Continue
        
    # Copy <FStar_root>/ulib to tools/ulib
    Copy-Item -Path $ulib_path -Destination "$nuget_dir_tools\ulib" -Recurse -Force
        
    # Copy <FStar_root>/bin/ulib.[dll|pdb|xml] to lib
    Copy-Item -Path $ulibfs_path -Destination $nuget_dir_lib -Force

    # Copy <FStar_root>/fsharp.extraction.targets to targets and rename it to $nuget_name.targets
    Copy-Item -Path "$FStarPath\fsharp.extraction.targets" -Destination "$nuget_dir_build\$nuget_name.targets" -Force
    Copy-Item -Path "$FStarPath\.nuget\$nuget_name.props" -Destination $nuget_dir_build -Force
    # copy nuspec file and set version
    Copy-Item -Path "$FStarPath\.nuget\$nuget_name.nuspec" -Destination $outputDir -Force

    # Copy license files
    # NOTE: Renaming LICENSE to LICENSE.txt as otherwise nuget is complaining about 'Part URI is empty'
    Copy-Item -Path "$FStarPath\LICENSE" -Destination "$nuget_dir\LICENSE.txt" -Force
    Copy-Item -Path "$FStarPath\LICENSE-fsharp.txt" -Destination "$nuget_dir\LICENSE-fsharp.txt" -Force
    Copy-Item -Path "$FStarPath\LICENSE-z3.txt" -Destination "$nuget_dir\LICENSE-z3.txt" -Force

    # Bump version in the copy of nuspec 
    UpdateVersionInNuspec "$outputDir\$nuget_name.nuspec" $version

    Write-Host "Packaging..."
    & $NugetPath @("pack", "$outputDir\$nuget_name.nuspec", "-OutputDirectory", $outputDir)

    Write-Host "Finished creating package"
}

function PushToNugetOrg{
    [CmdletBinding()] param([string] $NugetExe, [string] $ApiKey, [string] $FStarNugetPath)
    & $NugetExe @("push", $FStarNugetPath, "-ApiKey", $ApiKey)
}

$nuget_name = "FStar"
$repo = "FStarLang/FStar"

New-Item $outputDir -ItemType Directory -Force | Out-Null

$package = FindBinaryPackage -repo $repo -version $version -prerelease $PreRelease
Write-Host "Selected package: $package"
$FStarRootPath = GetWindowsBinaryPackage -package $package -outputDir $outputDir

CompileUlibfs -MSBuildExe $msbuild -FStarRootPath $FStarRootPath

$nugetVersionFinal = if ($PreRelease) { "$($package.version)-pre" } else { $package.version }
PackageAsNuget -NugetPath $nuget -FStarPath $FStarRootPath -outputDir $outputDir -version $nugetVersionFinal

$nuget_path = Join-Path -Path $outputDir -ChildPath "$nuget_name.$($package.version).nupkg"
PushToNugetOrg -NugetExe $nuget -ApiKey $ApiKey -FStarNugetPath $nuget_path










