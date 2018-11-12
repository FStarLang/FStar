module FStar.Tactics.Canon

open FStar.Tactics
open FStar.Reflection
open FStar.Reflection.Arith
open FStar.Mul
module O = FStar.Order

private
val distr : (#x : int) -> (#y : int) -> (#z : int) -> Lemma (x * (y + z) == x * y + x * z)
private
let distr #x #y #z = ()

private
val distl : (#x : int) -> (#y : int) -> (#z : int) -> Lemma ((x + y) * z == x * z + y * z)
private
let distl #x #y #z = ()

private
val ass_plus_l : (#x : int) -> (#y : int) -> (#z : int) -> Lemma (x + (y + z) == (x + y) + z)
private
let ass_plus_l #x #y #z = ()

private
val ass_mult_l : (#x : int) -> (#y : int) -> (#z : int) -> Lemma (x * (y * z) == (x * y) * z)
private
let ass_mult_l #x #y #z = ()

private
val comm_plus : (#x : int) -> (#y : int) -> Lemma (x + y == y + x)
private
let comm_plus #x #y = ()

private
val sw_plus : (#x : int) -> (#y : int) -> (#z : int) -> Lemma ((x + y) + z == (x + z) + y)
private
let sw_plus #x #y #z = ()

private
val sw_mult : (#x : int) -> (#y : int) -> (#z : int) -> Lemma ((x * y) * z == (x * z) * y)
private
let sw_mult #x #y #z = ()

private
val comm_mult : (#x : int) -> (#y : int) -> Lemma (x * y == y * x)
private
let comm_mult #x #y = ()

private
val trans : (#a:Type) -> (#x:a) -> (#z:a) -> (#y:a) ->
                    squash (x == y) -> squash (y == z) -> Lemma (x == z)
private
let trans #a #x #z #y e1 e2 = ()

private
val cong_plus : (#w:int) -> (#x:int) -> (#y:int) -> (#z:int) ->
                squash (w == y) -> squash (x == z) ->
                Lemma (w + x == y + z)
private
let cong_plus #w #x #y #z p q = ()

private
val cong_mult : (#w:int) -> (#x:int) -> (#y:int) -> (#z:int) ->
                squash (w == y) -> squash (x == z) ->
                Lemma (w * x == y * z)
private
let cong_mult #w #x #y #z p q = ()

private
val neg_minus_one : (#x:int) -> Lemma (-x == (-1) * x)
private
let neg_minus_one #x = ()

private
val x_plus_zero : (#x:int) -> Lemma (x + 0 == x)
private
let x_plus_zero #x = ()

private
val zero_plus_x : (#x:int) -> Lemma (0 + x == x)
private
let zero_plus_x #x = ()

private
val x_mult_zero : (#x:int) -> Lemma (x * 0 == 0)
private
let x_mult_zero #x = ()

private
val zero_mult_x : (#x:int) -> Lemma (0 * x == 0)
private
let zero_mult_x #x = ()

private
val x_mult_one : (#x:int) -> Lemma (x * 1 == x)
private
let x_mult_one #x = ()

private
val one_mult_x : (#x:int) -> Lemma (1 * x == x)
private
let one_mult_x #x = ()

private
val minus_is_plus : (#x : int) -> (#y : int) -> Lemma (x - y == x + (-y))
private
let minus_is_plus #x #y = ()

// These two cannot be top-levels if we want to compile
private
let step (t : unit -> Tac unit) : Tac unit =
    apply_lemma (`trans);
    t ()

private
let step_lemma (lem : term) : Tac unit =
    step (fun () -> apply_lemma lem)

private val canon_point : expr -> Tac expr
private let rec canon_point e =
    let skip () : Tac expr = 
        trefl (); e
    in
    match e with
    // Evaluate constants
    | Plus (Lit a) (Lit b) ->
        norm [primops];
        trefl ();
        Lit (a + b)

    | Mult (Lit a) (Lit b) ->
        norm [delta; primops]; // Need delta to turn op_Star into op_Multiply, as there's no primop for it
        trefl ();
        Lit (a * b)

    // Forget about negations
    | Neg e ->
        step_lemma (`neg_minus_one);
        canon_point (Mult (Lit (-1)) e)

    // Distribute
    | Mult a (Plus b c) ->
        step_lemma (`distr);
        step_lemma (`cong_plus);
        let l = canon_point (Mult a b) in
        let r = canon_point (Mult a c) in
        canon_point (Plus l r)

    | Mult (Plus a b) c ->
        step_lemma (`distl);
        step_lemma (`cong_plus);
        let l = canon_point (Mult a c) in
        let r = canon_point (Mult b c) in
        canon_point (Plus l r)

    // Associate to the left
    | Mult a (Mult b c) ->
        step_lemma (`ass_mult_l);
        step_lemma (`cong_mult);
        let l = canon_point (Mult a b) in
        let r = canon_point c in
        canon_point (Mult l r)

    | Plus a (Plus b c) ->
        step_lemma (`ass_plus_l);
        step_lemma (`cong_plus);
        let l = canon_point (Plus a b) in
        let r = canon_point c in
        canon_point (Plus l r)

    | Plus (Plus a b) c ->
        if O.gt (compare_expr b c)
        then begin
            step_lemma (`sw_plus);
            apply_lemma (`cong_plus);
            let l = canon_point (Plus a c) in
            trefl() ;
            Plus l b
        end
        else skip ()

    | Mult (Mult a b) c ->
        if O.gt (compare_expr b c)
        then begin
            step_lemma (`sw_mult);
            apply_lemma (`cong_mult);
            let l = canon_point (Mult a c) in
            trefl ();
            Mult l b
        end
        else skip ()

    | Plus a (Lit 0) ->
        apply_lemma (`x_plus_zero);
        a

    | Plus (Lit 0) b ->
        apply_lemma (`zero_plus_x);
        b

    | Plus a b ->
        if O.gt (compare_expr a b)
        then (apply_lemma (`comm_plus); Plus b a)
        else skip ()

    | Mult (Lit 0) _ ->
        apply_lemma (`zero_mult_x);
        Lit 0

    | Mult _ (Lit 0) ->
        apply_lemma (`x_mult_zero);
        Lit 0

    | Mult (Lit 1) r ->
        apply_lemma (`one_mult_x);
        r

    | Mult l (Lit 1) ->
        apply_lemma (`x_mult_one);
        l

    | Mult a b ->
        if O.gt (compare_expr a b)
        then (apply_lemma (`comm_mult); Mult b a)
        else skip ()

    // Forget about subtraction
    | Minus a b ->
        step_lemma (`minus_is_plus);
        step_lemma (`cong_plus);
        trefl ();
        let r = canon_point (Neg b) in
        canon_point (Plus a r)

    | _ ->
        skip ()

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
let canon_point_entry () : Tac unit =
    norm [];
    let g = cur_goal () in
    match term_as_formula g with
    | Comp (Eq _) l r ->
        begin match run_tm (is_arith_expr l) with
        | Inr e -> (let _e = canon_point e in ())
        | Inl _ -> trefl ()
        end
    | _ ->
        fail ("impossible: " ^ term_to_string g)

let canon () : Tac unit =
    seq (fun () -> pointwise canon_point_entry)
        (fun () -> simpl (); let _ = trytac trivial in ())
