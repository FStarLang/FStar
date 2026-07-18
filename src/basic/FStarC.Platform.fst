module FStarC.Platform

open FStarC.Effect
open FStarC.Platform.Base

instance showable_sys : showable sys = {
  show = (function
          | Unix -> "Unix"
          | Win32 -> "Win32"
          | Cygwin -> "Cygwin");
}

let windows =
  system = Win32

let cygwin =
  system = Cygwin

let unix =
  system = Unix || system = Cygwin

let exe s =
  if windows then s ^ ".exe" else s

let ocamlpath_sep =
  if windows then ";" else ":"
