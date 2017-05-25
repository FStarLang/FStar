module FStar.Tactics.Canon

unfold let op_Star = op_Multiply

open FStar.Tactics
open FStar.Tactics.Arith
open FStar.Reflection.Arith
module O = FStar.Order

val distr : (#x : int) -> (#y : int) -> (#z : int) -> Lemma (x * (y + z) == x * y + x * z)
let distr #x #y #z = ()

val distl : (#x : int) -> (#y : int) -> (#z : int) -> Lemma ((x + y) * z == x * z + y * z)
let distl #x #y #z = ()

val ass_plus_l : (#x : int) -> (#y : int) -> (#z : int) -> Lemma (x + (y + z) == (x + y) + z)
let ass_plus_l #x #y #z = ()

val ass_mult_l : (#x : int) -> (#y : int) -> (#z : int) -> Lemma (x * (y * z) == (x * y) * z)
let ass_mult_l #x #y #z = ()

val comm_plus : (#x : int) -> (#y : int) -> Lemma (x + y == y + x)
let comm_plus #x #y = ()

val sw_plus : (#x : int) -> (#y : int) -> (#z : int) -> Lemma ((x + y) + z == (x + z) + y)
let sw_plus #x #y #z = ()

val sw_mult : (#x : int) -> (#y : int) -> (#z : int) -> Lemma ((x * y) * z == (x * z) * y)
let sw_mult #x #y #z = ()

val comm_mult : (#x : int) -> (#y : int) -> Lemma (x * y == y * x)
let comm_mult #x #y = ()

val trans : (#a:Type) -> (#x:a) -> (#z:a) -> (#y:a) -> (x == y) -> (y == z) -> Lemma (x == z)
let trans #a #x #z #y e1 e2 = ()

val cong_plus : (#w:int) -> (#x:int) -> (#y:int) -> (#z:int) ->
                (w == y) -> (x == z) ->
                Lemma (w + x == y + z)
let cong_plus #w #x #y #z p q = ()

val cong_mult : (#w:int) -> (#x:int) -> (#y:int) -> (#z:int) ->
                (w == y) -> (x == z) ->
                Lemma (w * x == y * z)
let cong_mult #w #x #y #z p q = ()

let rec canon_point : unit -> Tac unit = fun () -> (
    norm [];; // to unfold
    eg <-- cur_goal;
    let (e, g), _ = eg in
    match term_as_formula g with
    | Comp Eq t l r ->
        begin match run_tm (is_arith_expr l) with
        | Inl s ->
            trefl

        | Inr (Plus (Lit _) (Lit _))
        | Inr (Mult (Lit _) (Lit _)) ->
            norm [Primops];; // TODO: primops won't reduce if given Simpl too, is that intentional?
            trefl

        | Inr (Plus a (Plus b c)) ->
            apply_lemma (quote trans);;
            apply_lemma (quote ass_plus_l);;
            apply_lemma (quote trans);;
            apply_lemma (quote cong_plus);;
            canon_point;;
            canon_point;;
            canon_point

        | Inr (Plus (Plus a b) c) ->
            if O.gt (compare_expr b c) then (
                apply_lemma (quote trans);;
                apply_lemma (quote sw_plus);;
                apply_lemma (quote cong_plus);;
                canon_point;;
                trefl
            ) else trefl

        | Inr (Mult (Mult a b) c) ->
            if O.gt (compare_expr b c) then (
                apply_lemma (quote trans);;
                apply_lemma (quote sw_mult);;
                apply_lemma (quote cong_mult);;
                canon_point;;
                trefl
            ) else trefl

        | Inr (Mult a (Mult b c)) ->
            apply_lemma (quote trans);;
            apply_lemma (quote ass_mult_l);;
            apply_lemma (quote trans);;
            apply_lemma (quote cong_mult);;
            canon_point;;
            canon_point;;
            canon_point

        | Inr (Mult (Plus a b) c) ->
            apply_lemma (quote trans);;
            apply_lemma (quote distl);; // now need to show a*c + b*c = ?u
            apply_lemma (quote trans);;
            apply_lemma (quote cong_plus);; // now two goals. |- a*c = ?u1 ; |- b*c = ?u2
            canon_point;;
            canon_point;;
            canon_point

        | Inr (Mult a (Plus b c)) ->
            apply_lemma (quote trans);;
            apply_lemma (quote distr);;
            apply_lemma (quote trans);;
            apply_lemma (quote cong_plus);;
            canon_point;;
            canon_point;;
            canon_point

        | Inr (Plus a b) ->
            if O.gt (compare_expr a b)
            then apply_lemma (quote comm_plus)
            else trefl

        | Inr (Mult a b) ->
            if O.gt (compare_expr a b)
            then apply_lemma (quote comm_mult)
            else trefl

        | Inr _ ->
            trefl
        end
    | _ ->
        fail ("impossible: " ^ term_to_string g)
    ) ()

let canon = pointwise canon_point
