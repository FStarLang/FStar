module FStar.Dyn
open FStar.All

(* Dynamic casts, realized by OCaml's Obj *)

assume new type dyn
val mkdyn : 'a -> ML dyn
val undyn : dyn -> ML 'a
