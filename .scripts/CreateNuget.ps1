[CmdletBinding()]
param(
        # Directory in which nuget should be created
        [Parameter(Mandatory=$true)]
        $outputDir,

        # Nuget.org Api Key
        [Parameter(Mandatory=$true)]
        $ApiKey
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
        Fetches latest available F* windows binary package from Github Releases.
    #>
function PickLatestWindowsBinaryPackage{
    [CmdletBinding()] param([string] $outputDir)

    # TODO: implement
    $FStarRootPath = Join-Path -Path $outputDir -ChildPath "SomeSubFolderThatWillBeCreated"
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
    [CmdletBinding()] param([string] $FStarPath, [string] $outputDir)

    $nuget_dir = Join-Path -Path $outputDir -ChildPath "fstar"

    $fstarbin_path = Join-Path -Path $FStarPath -ChildPath "bin"
    $ulib_path = Join-Path -Path $FStarPath -ChildPath "ulib"
    $ulibfs_path = Join-Path -Path $FStarPath -ChildPath "bin\ulibfs.*" # we need to copy dll, pdb and xml

    $bin_files = 
        @("fstar.exe", "z3.exe", 
          "libgmp-10.dll", 
          "libz3.dll", "libz3.lib", "libz3java.dll", "libz3java.lib", "Microsoft.Z3.dll", 
          "msvcp120.dll", "msvcp120d.dll", "msvcr120.dll", "msvcr120d.dll", "vcomp120.dll", "vcomp120d.dll")

    try
    {
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

        # Copy <FStar_root>/ulib to tools/ulib
        Copy-Item -Path $ulib_path -Destination "$nuget_dir_tools\ulib" -Recurse -Force
        # Do not include ulibfs build artifacts in the ulib
        $ulib_obj = Join-Path -Path $ulib_path -ChildPath "obj"
        $ulib_bin = Join-Path -Path $ulib_path -ChildPath "bin"
        Remove-Item -Path $ulib_obj -Recurse -Force -ErrorAction Continue
        Remove-Item -Path $ulib_bin -Recurse -Force -ErrorAction Continue

        # Copy <FStar_root>/bin/ulib.[dll|pdb|xml] to lib
        Copy-Item -Path $ulibfs_path -Destination $nuget_dir_lib -Force

        # Copy <FStar_root>/fsharp.extraction.targets to targets and rename it to $nuget_name.targets
        Copy-Item -Path "$FStarPath\fsharp.extraction.targets" -Destination "$nuget_dir_build\$nuget_name.targets" -Force
        Copy-Item -Path "$FStarPath\.nuget\$nuget_name.props" -Destination $nuget_dir_build -Force
        # copy nuspec file and set version
        Copy-Item -Path "$FStarPath\.nuget\$nuget_name.nuspec" -Destination $outputDir -Force
        # Bump version in the copy of nuspec 
        UpdateVersionInNuspec "$outputDir\$nuget_name.nuspec" $version

        Write-Host "Packaging..."
        & $NugetPath @("pack", "$outputDir\$nuget_name.nuspec", "-OutputDirectory", $outputDir)

        Write-Host "Finished"
    }
    finally {
        Write-Host "Removing $nuget_dir"
        Remove-Item -Force -LiteralPath $nuget_dir -Recurse
        Remove-Item -Force -LiteralPath "$outputDir\$nuget_name.nuspec"
    }
}

function PushToNugetOrg{
    [CmdletBinding()] param([string] $NugetExe, [string] $ApiKey, [string] $FStarNugetPath)
    & $NugetExe @("push", $FStarNugetPath, "-ApiKey", $ApiKey)
}

$nuget_name = "FStar"

New-Item $outputDir -ItemType Directory -Force | Out-Null
$FStarBinPackagePath = Join-Path -Path $outputDir -ChildPath "fstar-binary"


$FStarPath = PickLatestWindowsBinaryPackage $FStarBinPackagePath
CompileUlibfs "msbuild.exe" $FStarPath

PackageAsNuget $FStarPath $outputDir

$nuget_path = Join-Path -Path $outputDir -ChildPath "FStar.nuget"
PushToNugetOrg "nuget.exe" $ApiKey $nuget_path










