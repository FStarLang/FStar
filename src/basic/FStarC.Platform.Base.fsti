module FStarC.Platform.Base

open FStarC.Effect

type sys =
  | Unix
  | Win32
  | Cygwin

val system : sys

(* Tries to read the output of the `uname` command. *)
val kernel () : string
