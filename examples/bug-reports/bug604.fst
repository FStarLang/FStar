module Bug604

(* Inductive equality on integers *)
noeq type ieq : int -> int -> Type =
| Refl : x:int -> ieq x x

(* Some predicate on integers *)
assume type pred : int -> Type

val steps_preserves_red : e:int -> e':int -> b:ieq e e' -> pred e -> Tot (pred e')
let steps_preserves_red e e' heq hp =
  match heq with
  | Refl e'' -> assert(e == e'' /\ e == e'); (* -- these work fine *)
                hp                           (* -- but this doesn't *)

(* [hritcu@detained bug-reports]$ fstar.exe bug604.fst *)
(* ./bug604.fst(13,17-13,19) : Error *)
(* Expected expression of type "(Bug604.pred e')"; *)
(* got expression "hp" of type "(Bug604.pred e)" *)
