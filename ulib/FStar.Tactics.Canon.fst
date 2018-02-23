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

// These two cannot be top-levels if we want to compile
let step (t : tactic unit) : tactic unit =
    apply_lemma (quote_lid ["FStar";"Tactics";"Canon";"trans"]);;
    t

let step_lemma (lem : tactic term) : tactic unit =
    step (apply_lemma lem)

val canon_point : expr -> unit -> Tac expr
let rec canon_point = fun e () ->
    // Need this stupid indirection or I get:
    //
    // ulib/FStar.Tactics.Canon.fst(105,8-107,28): (Error 54)
    // FStar.Tactics.Effect.Tac FStar.Reflection.Arith.expr
    // is not a subtype of the expected type
    // Prims.Tot ((*?u2035*) _ e uu___4175)
    //
    // This didn't happen before adding the `e` argument
    let x : tactic expr = (
    let skip : tactic expr = 
        trefl;;
        return e
    in
    match e with
    // Fold constants
    | Plus (Lit a) (Lit b) ->
        norm [primops];;
        trefl;;
        return (Lit (a + b))

    | Mult (Lit a) (Lit b) ->
        norm [delta; primops];; // Need delta to turn op_Star into op_Multiply, as there's no primop for it
        trefl;;
        return (Lit (a * b))

    // Forget about negations
    | Neg e ->
        step_lemma (quote_lid ["FStar";"Tactics";"Canon";"neg_minus_one"]);;
        canon_point (Mult (Lit (-1)) e)

    // Distribute
    | Mult a (Plus b c) ->
        step_lemma (quote_lid ["FStar";"Tactics";"Canon";"distr"]);;
        step_lemma (quote_lid ["FStar";"Tactics";"Canon";"cong_plus"]);;
        l <-- canon_point (Mult a b);
        r <-- canon_point (Mult a c);
        canon_point (Plus l r)

    | Mult (Plus a b) c ->
        step_lemma (quote_lid ["FStar";"Tactics";"Canon";"distl"]);;
        step_lemma (quote_lid ["FStar";"Tactics";"Canon";"cong_plus"]);;
        l <-- canon_point (Mult a c);
        r <-- canon_point (Mult b c);
        canon_point (Plus l r)

    // Associate to the left
    | Mult a (Mult b c) ->
        step_lemma (quote_lid ["FStar";"Tactics";"Canon";"ass_mult_l"]);;
        step_lemma (quote_lid ["FStar";"Tactics";"Canon";"cong_mult"]);;
        l <-- canon_point (Mult a b);
        r <-- canon_point c;
        canon_point (Mult l r)

    | Plus a (Plus b c) ->
        step_lemma (quote_lid ["FStar";"Tactics";"Canon";"ass_plus_l"]);;
        step_lemma (quote_lid ["FStar";"Tactics";"Canon";"cong_plus"]);;
        l <-- canon_point (Plus a b);
        r <-- canon_point c;
        canon_point (Plus l r)

    | Plus (Plus a b) c ->
        if O.gt (compare_expr b c)
        then begin
            step_lemma (quote_lid ["FStar";"Tactics";"Canon";"sw_plus"]);;
            apply_lemma (quote_lid ["FStar";"Tactics";"Canon";"cong_plus"]);;
            l <-- canon_point (Plus a c);
            trefl;;
            return (Plus l b)
        end
        else skip

    | Mult (Mult a b) c ->
        if O.gt (compare_expr b c)
        then begin
            step_lemma (quote_lid ["FStar";"Tactics";"Canon";"sw_mult"]);;
            apply_lemma (quote_lid ["FStar";"Tactics";"Canon";"cong_mult"]);;
            l <-- canon_point (Mult a c);
            trefl;;
            return (Mult l b)
        end
        else skip

    | Plus a (Lit 0) ->
        apply_lemma (quote_lid ["FStar";"Tactics";"Canon";"x_plus_zero"]);;
        return a

    | Plus (Lit 0) b ->
        apply_lemma (quote_lid ["FStar";"Tactics";"Canon";"zero_plus_x"]);;
        return b

    | Plus a b ->
        if O.gt (compare_expr a b)
        then (apply_lemma (quote_lid ["FStar";"Tactics";"Canon";"comm_plus"]);; return (Plus b a))
        else skip

    | Mult (Lit 0) _ ->
        apply_lemma (quote_lid ["FStar";"Tactics";"Canon";"zero_mult_x"]);;
        return (Lit 0)

    | Mult _ (Lit 0) ->
        apply_lemma (quote_lid ["FStar";"Tactics";"Canon";"x_mult_zero"]);;
        return (Lit 0)

    | Mult (Lit 1) r ->
        apply_lemma (quote_lid ["FStar";"Tactics";"Canon";"one_mult_x"]);;
        return r

    | Mult l (Lit 1) ->
        apply_lemma (quote_lid ["FStar";"Tactics";"Canon";"x_mult_one"]);;
        return l

    | Mult a b ->
        if O.gt (compare_expr a b)
        then (apply_lemma (quote_lid ["FStar";"Tactics";"Canon";"comm_mult"]);; return (Mult b a))
        else skip

    // Forget about subtraction
    | Minus a b ->
        step_lemma (quote_lid ["FStar";"Tactics";"Canon";"minus_is_plus"]);;
        step_lemma (quote_lid ["FStar";"Tactics";"Canon";"cong_plus"]);;
        trefl;;
        canon_point (Neg b);;
        canon_point (Plus a (Neg b))

    | _ ->
        skip
    ) in x ()

// On canon_point_entry, we interpret the LHS of the goal as an
// arithmetic expression, of which we keep track in canon_point so we
// avoid reinterpreting the goal, which gives a good speedup.
//
// However, we are repeating work between canon_point_entry calls, since
// in (L + R), we are called once for L, once for R, and once for the
// sum which traverses both (their canonized forms, actually).
//
// The proper way to solve this is have some state-passing in pointwise,
// maybe having the inner tactic be of type (list a -> tactic a), where
// the list is the collected results for all child calls.
let canon_point_entry : tactic unit =
    norm [];;
    g <-- cur_goal;
    let f = term_as_formula g in
    match f with
    | Comp (Eq _) l r ->
        begin match run_tm (is_arith_expr l) with
        | Inr e -> (canon_point e;; return ())
        | Inl _ -> trefl
        end
    | _ ->
        fail ("impossible: " ^ term_to_string g)

let canon =
    seq (pointwise canon_point_entry)
        (simpl;; trytac trivial;; idtac)
