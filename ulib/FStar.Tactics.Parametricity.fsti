module FStar.Tactics.Parametricity

open FStar.Tactics.Effect
open FStar.Stubs.Reflection.Types

(* May be raised by the translations. *)
exception Unsupported of string
exception NotFoundFV of fv

(* Translate a term or type *)
[@@plugin]
val param (t:term) : Tac term

(* Take a top-level declaration, of name nm, and generate
declarations for its parametricity translation. *)
[@@plugin]
val paramd (nm:string) : Tac decls

(* As above for several declarations at once. *)
[@@plugin]
val paramds (nms:list string) : Tac decls

(* Parametricity principle for some base types. We should use
a typeclass for this. *)
let param_of_eqtype (a:eqtype) : a -> a -> Type0 = (fun (x y : a) -> squash (x == y))
let int_param    = param_of_eqtype int
let bool_param   = param_of_eqtype bool
let unit_param   = param_of_eqtype unit
let string_param = param_of_eqtype string
