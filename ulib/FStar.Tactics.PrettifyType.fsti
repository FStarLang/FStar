module FStar.Tactics.PrettifyType

open FStar.Bijection {}
open FStar.Tactics.V2.Bare

(* The single thing you should call here is entry function,
as the body of a splice. The rest of the declarations in this
interface are only in support of running the tactic, don't call
them directly. *)

(* Use this alias to generate field and constructor names.
Place it around an atom for field name, and around (the outer) tuple2
of a case to choose a constructor name. *)
inline_for_extraction
type named (s:string) (a:Type) = a

let fakeunit = `unit

unfold
let f_inverses #a #b (f : b -> a) (g : a -> b) (x:a) =
  squash (f (g x) == x)

type atom = term

[@@plugin]
noeq
type parsed_type =
  | Atom   : atom -> parsed_type
  | Tuple2 : parsed_type -> parsed_type -> parsed_type
  | Either : parsed_type -> parsed_type -> parsed_type
  | Named  : string -> parsed_type -> parsed_type

[@@plugin]
val prove_left_right (at : parsed_type) : Tac unit

[@@plugin]
val prove_right_left () : Tac unit

(* suf: suffix to add to the name of the generated type (e.g. "_pretty")
   nm: name of the type to prettify e.g. (`%mytype)

   This will generate some names in scope (using _pretty for the suffix):
   - nm_pretty: a "pretty" version of the type as a non-recursive inductive
                with one constructor for each case of the original type,
                and one field in each for every tuple2 component of the case.
                e.g. either ((int & int) & (int & string)) bool
                  becomes
                    type t =
                     | Mkmytype_pretty0 : _x0:int -> _x1:int -> _x2:int -> _x3:string -> t
                     | Mkmytype_pretty1 : _x0:bool -> t

    - nm_pretty_bij: a bijection (FStar.Bijection.bijection) between
      the old type and the new pretty type.

    This bijection packages functions in each direction and proofs,
    see the FStar.Bijection module for more details. The components
    of the bijection also get top-level names:

    - nm_pretty_right: the right map of the bijection (old -> pretty)
    - nm_pretty_left: the left map of the bijection (pretty -> old)
    - nm_pretty_left_right: proof that left inverses right
                       (i.e. x:old -> squash (left (right x) == x))
    - nm_pretty_right_left: proof that right inverses left
                       (i.e. x:pretty -> squash (right (left x) == x))

    *)
[@@plugin]
val entry (suf nm : string) : Tac decls
