module FStar.Compiler.Dyn
open FStar.Compiler.Effect

///  Dynamic casts, realized by OCaml's [Obj]
///
///  NOTE: THIS PROVIDES CASTS BETWEEN ARBITRARY TYPES
///  BUT ONLY IN [False] CONTEXTS. USE WISELY.
assume new
type dyn

(** Promoting a value of type ['a] to [dyn] *)
val mkdyn: 'a -> ML dyn

(** This coerces a value of type [dyn] to any type ['a],
    but only with [False] precondition *)
val undyn (d: dyn{false}) : ML 'a
