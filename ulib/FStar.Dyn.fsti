module FStar.Dyn
open FStar.All

(* Dynamic casts, realized by OCaml's Obj.
   This is type unsafe. *)

assume new type dyn
val mkdyn : 'a -> EXT dyn
val undyn : d:dyn{false} -> EXT 'a
