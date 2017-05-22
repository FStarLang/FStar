module Canon

#reset-options "--eager_inference"

//

open FStar.Mul
open FStar.Tactics
open FStar.Tactics.Arith
open FStar.Reflection.Arith

assume val x : int
assume val y : int
assume val z : int

(* val refl : (a:Type) -> (x:a) -> Lemma (x == x) *)
(* let refl a x = () *)

val congl : (#a:Type) -> (x : a) -> (y : a) -> (z : a) -> (x == y) -> (y == z) -> Lemma (x == z)
let congl #a x y z p1 p2 = ()

val congr : (#a:Type) -> (x : a) -> (y : a) -> (z : a) -> (x == y) -> (z == y) -> Lemma (z == x)
let congr #a x y z p1 p2 = ()

assume val p : (y + z == x + y)

val distr : (#x : int) -> (#y : int) -> (#z : int) -> Lemma (x `op_Multiply` (y + z) == x `op_Multiply` y + x `op_Multiply` z)
let distr #x #y #z = ()

val distl : (#x : int) -> (#y : int) -> (#z : int) -> Lemma ((x + y) `op_Multiply` z == x `op_Multiply` z + y `op_Multiply` z)
let distl #x #y #z = ()

(* // When taking a goal of the form *)
(* //   a * (b + c) = ?u *)
(* // it applies distl to cause ?u to unify to *)
(* //   a * b   +   a * c *)
(* // when it's a different shape, apply refl to unify it to the LHS *)
(* let tau : tactic unit = *)
(*     eg <-- cur_goal; *)
(*     let e, g = eg in *)
(*     match run_tm (is_arith_prop g) with *)
(*     | Inr (CompProp l C_Eq r) -> *)
(*         begin match l with *)
(*         | Mult (Plus a b) c -> *)
(*             apply_lemma (distl _ _ _) *)
(*         | _ -> *)
(*             apply_lemma refl *)
(*         end *)
(*     | _ -> *)
(*         apply_lemma refl *)

let canon : tactic unit =
    eg <-- cur_goal;
    let e, g = eg in
    match term_as_formula g with
    | Comp Eq t l r ->
        begin match run_tm (is_arith_expr l) with
        | Inl s ->
            refl

        | Inr (Mult (Plus a b) c) ->
            apply_lemma (quote distl)

        | Inr (Mult a (Plus b c)) ->
            apply_lemma (quote distr)

        | Inr _ ->
            refl
        end
    | _ ->
        fail "impossible"

let trytac' (tau : tactic 'a) : tactic unit =
    trytac tau;;
    return ()

let tau : tactic unit =
    seq (pointwise canon) (trytac' trivial)

let lem1 = assert_by_tactic (dump "BEFORE";; tau;; dump "AFTER") ((x + y) * z == z * (y + x))

(* let lem2 = assert_by_tactic (dump "BEFORE";; tau;; dump "AFTER") (x == x) *)
