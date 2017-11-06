module FStar.Tactics.Canon

open FStar.Tactics
open FStar.Reflection
open FStar.Reflection.Arith
open FStar.Mul
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

val trans : (#a:Type) -> (#x:a) -> (#z:a) -> (#y:a) ->
                    squash (x == y) -> squash (y == z) -> Lemma (x == z)
let trans #a #x #z #y e1 e2 = ()

val cong_plus : (#w:int) -> (#x:int) -> (#y:int) -> (#z:int) ->
                squash (w == y) -> squash (x == z) ->
                Lemma (w + x == y + z)
let cong_plus #w #x #y #z p q = ()

val cong_mult : (#w:int) -> (#x:int) -> (#y:int) -> (#z:int) ->
                squash (w == y) -> squash (x == z) ->
                Lemma (w * x == y * z)
let cong_mult #w #x #y #z p q = ()

val neg_minus_one : (#x:int) -> Lemma (-x == (-1) * x)
let neg_minus_one #x = ()

val mult1 : (#x:int) -> Lemma (x == 1 * x)
let mult1 #x = ()

val x_plus_zero : (#x:int) -> Lemma (x + 0 == x)
let x_plus_zero #x = ()

val zero_plus_x : (#x:int) -> Lemma (0 + x == x)
let zero_plus_x #x = ()

val x_mult_zero : (#x:int) -> Lemma (x * 0 == 0)
let x_mult_zero #x = ()

val zero_mult_x : (#x:int) -> Lemma (0 * x == 0)
let zero_mult_x #x = ()

val x_mult_one : (#x:int) -> Lemma (x * 1 == x)
let x_mult_one #x = ()

val one_mult_x : (#x:int) -> Lemma (1 * x == x)
let one_mult_x #x = ()

val minus_is_plus : (#x : int) -> (#y : int) -> Lemma (x - y == x + (-y))
let minus_is_plus #x #y = ()

let rec canon_point : unit -> Tac unit = fun () -> (
    let step (t : tactic unit) : tactic unit =
        apply_lemma (quote_lid ["FStar";"Tactics";"Canon";"trans"]);;
        t
    in
    let step_lemma (lem : tactic term) : tactic unit =
        step (apply_lemma lem)
    in
    let comm_r_plus : tactic unit =
        step_lemma (quote_lid ["FStar";"Tactics";"Canon";"sw_plus"]);;
        apply_lemma (quote_lid ["FStar";"Tactics";"Canon";"cong_plus"]);;
        canon_point;;
        trefl
    in
    let comm_r_mult : tactic unit =
        step_lemma (quote_lid ["FStar";"Tactics";"Canon";"sw_mult"]);;
        apply_lemma (quote_lid ["FStar";"Tactics";"Canon";"cong_mult"]);;
        canon_point;;
        trefl
    in
    norm [];;
    g <-- cur_goal;
    let f = term_as_formula g in
    match f with
    | Comp Eq t l r ->
        begin match run_tm (is_arith_expr l) with
        | Inl s ->
            trefl

        // Fold constants
        | Inr (Plus (Lit _) (Lit _))
        | Inr (Mult (Lit _) (Lit _)) ->
            norm [delta; primops];; // Need this to turn op_Star into op_Multiply, as there's no primop for it
            trefl

        // Forget about negations
        | Inr (Neg e) ->
            step_lemma (quote_lid ["FStar";"Tactics";"Canon";"neg_minus_one"]);;
            canon_point

        // Distribute
        | Inr (Mult a (Plus b c)) ->
            step_lemma (quote_lid ["FStar";"Tactics";"Canon";"distr"]);;
            step_lemma (quote_lid ["FStar";"Tactics";"Canon";"cong_plus"]);;
            canon_point;;
            canon_point;;
            canon_point

        | Inr (Mult (Plus a b) c) ->
            step_lemma (quote_lid ["FStar";"Tactics";"Canon";"distl"]);;
            step_lemma (quote_lid ["FStar";"Tactics";"Canon";"cong_plus"]);;
            canon_point;;
            canon_point;;
            canon_point

        // Associate to the left
        | Inr (Mult a (Mult b c)) ->
            step_lemma (quote_lid ["FStar";"Tactics";"Canon";"ass_mult_l"]);;
            step_lemma (quote_lid ["FStar";"Tactics";"Canon";"cong_mult"]);;
            canon_point;;
            canon_point;;
            canon_point

        | Inr (Plus a (Plus b c)) ->
            step_lemma (quote_lid ["FStar";"Tactics";"Canon";"ass_plus_l"]);;
            step_lemma (quote_lid ["FStar";"Tactics";"Canon";"cong_plus"]);;
            canon_point;;
            canon_point;;
            canon_point

        | Inr (Plus (Plus a b) c) ->
            let o = compare_expr b c in
            if O.gt o
            then comm_r_plus
            else trefl

        | Inr (Mult (Mult a b) c) ->
            if O.gt (compare_expr b c)
            then comm_r_mult
            else trefl

        | Inr (Plus a (Lit 0)) ->
            apply_lemma (quote_lid ["FStar";"Tactics";"Canon";"x_plus_zero"])

        | Inr (Plus (Lit 0) b) ->
            apply_lemma (quote_lid ["FStar";"Tactics";"Canon";"zero_plus_x"])

        | Inr (Plus a b) ->
            if O.gt (compare_expr a b)
            then apply_lemma (quote_lid ["FStar";"Tactics";"Canon";"comm_plus"])
            else trefl

        | Inr (Mult (Lit 0) _) ->
            apply_lemma (quote_lid ["FStar";"Tactics";"Canon";"zero_mult_x"])

        | Inr (Mult _ (Lit 0)) ->
            apply_lemma (quote_lid ["FStar";"Tactics";"Canon";"x_mult_zero"])

        | Inr (Mult (Lit 1) _) ->
            apply_lemma (quote_lid ["FStar";"Tactics";"Canon";"one_mult_x"])

        | Inr (Mult _ (Lit 1)) ->
            apply_lemma (quote_lid ["FStar";"Tactics";"Canon";"x_mult_one"])

        | Inr (Mult a b) ->
            if O.gt (compare_expr a b)
            then apply_lemma (quote_lid ["FStar";"Tactics";"Canon";"comm_mult"])
            else trefl

        // Forget about subtraction
        | Inr (Minus a b) ->
            step_lemma (quote_lid ["FStar";"Tactics";"Canon";"minus_is_plus"]);;
            step_lemma (quote_lid ["FStar";"Tactics";"Canon";"cong_plus"]);;
            trefl;;
            canon_point;;
            canon_point

        | Inr _ ->
            trefl
        end
    | _ ->
        fail ("impossible: " ^ term_to_string g)
    ) ()

let canon =
    seq (pointwise canon_point)
        (simpl;; trytac trivial;; idtac)
