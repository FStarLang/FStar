module FStar.Tactics.TypeRepr

open FStar.Tactics.V2.Bare

private
let empty_elim (e:empty) (#a:Type) : a = match e with

(* Do not use directly. *)
[@@plugin]
val generate_repr_typ (params : binders) (ctors : list ctor)  : Tac typ

(* Do not use directly. *)
[@@plugin]
val generate_down () : Tac unit

(* Do not use directly. *)
[@@plugin]
val generate_up (nm:string) () : Tac unit

[@@plugin]
val entry (nm : string) : Tac decls
