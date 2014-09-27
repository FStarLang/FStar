#light "off"

module Microsoft.FStar.Platform

open Microsoft.FStar
open System

type sys =
| Windows
| Posix

let system : sys =
    match Environment.OSVersion.Platform with
    | PlatformID.MacOSX
    | PlatformID.Unix -> Posix
    | _ -> Windows

let exe (name : string) =
    match system with
    | Windows -> Util.format1 "%s.exe" name
    | Posix   -> name


