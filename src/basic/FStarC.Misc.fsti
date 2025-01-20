module FStarC.Misc

open FStarC.Effect

(* This functions compare version numbers. E.g. "4.8.5" and "4.12.3".
NOTE: the versions cannot contain any alphabetic character, only numbers
are allowed for now. *)

val version_gt : string -> string -> bool
val version_ge : string -> string -> bool
