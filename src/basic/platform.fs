#light "off"

module Microsoft.FStar.Platform

open Microsoft.FStar
open System

type system =
| Windows
| Posix

let system : system =
    match Environment.OSVersion.Platform with
    | PlatformID.MacOSX
    | PlatformID.Unix -> Posix
    | _ -> Windows

let exe (name : string) =
    match system with
    | Windows -> Util.format1 "%s.exe" name
    | Posix   -> name


