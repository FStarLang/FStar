open Fstarcompiler
open Prims

let elim_pure (wp : unit) (f : unit -> 'a) (p : unit) : 'a= f ()
