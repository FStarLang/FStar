module FStarC.Platform

open FStarC.Effect
include FStarC.Platform.Base

open FStarC.Class.Show
instance val showable_sys : showable sys

(* Running on Windows (not cygwin) *)
val windows : bool

(* Running on Cygwin. *)
val cygwin : bool

(* Running on a unix-like system *)
val unix : bool

(* Executable name for this platform, currently
just appends '.exe' on Windows. *)
val exe : string -> string

(* String used to separate paths in the OCAMLPATH environment variable. *)
val ocamlpath_sep : string
