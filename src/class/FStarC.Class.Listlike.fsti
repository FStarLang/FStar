module FStarC.Class.Listlike

open FStarC.Effect

type view_t e s =
  | VNil  : view_t e s
  | VCons : e -> s -> view_t e s

[@@Tactics.Typeclasses.fundeps [0]]
class listlike (e:Type) (s:Type) = {
  empty         : s;
  cons          : e -> s -> s;
  view          : s -> view_t e s;
}

val is_empty (#e #s : Type) {| listlike e s |} (l : s) : bool

val singleton (#e #s : Type) {| listlike e s |} (x : e) : s

val to_list (#e #s : Type) {| listlike e s |} (l : s) : list e

val from_list (#e #s : Type) {| listlike e s |} (l : list e) : s
