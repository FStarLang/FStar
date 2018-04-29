module FStar.Tactics.Canon

open FStar.Tactics
open FStar.Reflection
open FStar.Reflection.Arith
open FStar.Mul
module O = FStar.Order

val distr: #x: int -> #y: int -> #z: int -> Lemma (x * (y + z) == x * y + x * z)
let distr #x #y #z = ()

val distl: #x: int -> #y: int -> #z: int -> Lemma ((x + y) * z == x * z + y * z)
let distl #x #y #z = ()

val ass_plus_l: #x: int -> #y: int -> #z: int -> Lemma (x + (y + z) == (x + y) + z)
let ass_plus_l #x #y #z = ()

val ass_mult_l: #x: int -> #y: int -> #z: int -> Lemma (x * (y * z) == (x * y) * z)
let ass_mult_l #x #y #z = ()

val comm_plus: #x: int -> #y: int -> Lemma (x + y == y + x)
let comm_plus #x #y = ()

val sw_plus: #x: int -> #y: int -> #z: int -> Lemma ((x + y) + z == (x + z) + y)
let sw_plus #x #y #z = ()

val sw_mult: #x: int -> #y: int -> #z: int -> Lemma ((x * y) * z == (x * z) * y)
let sw_mult #x #y #z = ()

val comm_mult: #x: int -> #y: int -> Lemma (x * y == y * x)
let comm_mult #x #y = ()

val trans: #a: Type -> #x: a -> #z: a -> #y: a -> squash (x == y) -> squash (y == z) ->
  Lemma (x == z)
let trans #a #x #z #y e1 e2 = ()

val cong_plus: #w: int -> #x: int -> #y: int -> #z: int -> squash (w == y) -> squash (x == z) ->
  Lemma (w + x == y + z)
let cong_plus #w #x #y #z p q = ()

val cong_mult: #w: int -> #x: int -> #y: int -> #z: int -> squash (w == y) -> squash (x == z) ->
  Lemma (w * x == y * z)
let cong_mult #w #x #y #z p q = ()

val neg_minus_one: #x: int -> Lemma (- x == (- 1) * x)
let neg_minus_one #x = ()

val x_plus_zero: #x: int -> Lemma (x + 0 == x)
let x_plus_zero #x = ()

val zero_plus_x: #x: int -> Lemma (0 + x == x)
let zero_plus_x #x = ()

val x_mult_zero: #x: int -> Lemma (x * 0 == 0)
let x_mult_zero #x = ()

val zero_mult_x: #x: int -> Lemma (0 * x == 0)
let zero_mult_x #x = ()

val x_mult_one: #x: int -> Lemma (x * 1 == x)
let x_mult_one #x = ()

val one_mult_x: #x: int -> Lemma (1 * x == x)
let one_mult_x #x = ()

val minus_is_plus: #x: int -> #y: int -> Lemma (x - y == x + (- y))
let minus_is_plus #x #y = ()

// These two cannot be top-levels if we want to compile
let step (t: (unit -> Tac unit)) : Tac unit = apply_lemma (`trans); t ()

let step_lemma (lem: term) : Tac unit = step (fun () -> apply_lemma lem)

val canon_point: expr -> Tac expr
let rec canon_point e =
  let skip () : Tac expr = trefl (); e in
  match e with
  | Plus (Lit a) (Lit b) ->
    // Evaluate constants
    norm [primops];
    trefl ();
    Lit (a + b)
  | Mult (Lit a) (Lit b) ->
    // Need delta to turn op_Star into op_Multiply, as there's no primop for it
    norm [delta; primops];
    trefl ();
    Lit (a * b)
  | Neg e ->
    // Forget about negations
    step_lemma (`neg_minus_one);
    canon_point (Mult (Lit (- 1)) e)
  | Mult a (Plus b c) ->
    // Distribute
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
  | Mult a (Mult b c) ->
    // Associate to the left
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
    then
      (step_lemma (`sw_plus);
        apply_lemma (`cong_plus);
        let l = canon_point (Plus a c) in
        trefl ();
        Plus l b)
    else skip ()
  | Mult (Mult a b) c ->
    if O.gt (compare_expr b c)
    then
      (step_lemma (`sw_mult);
        apply_lemma (`cong_mult);
        let l = canon_point (Mult a c) in
        trefl ();
        Mult l b)
    else skip ()
  | Plus a (Lit 0) -> apply_lemma (`x_plus_zero); a
  | Plus (Lit 0) b -> apply_lemma (`zero_plus_x); b
  | Plus a b -> if O.gt (compare_expr a b) then (apply_lemma (`comm_plus); Plus b a) else skip ()
  | Mult (Lit 0) _ -> apply_lemma (`zero_mult_x); Lit 0
  | Mult _ (Lit 0) -> apply_lemma (`x_mult_zero); Lit 0
  | Mult (Lit 1) r -> apply_lemma (`one_mult_x); r
  | Mult l (Lit 1) -> apply_lemma (`x_mult_one); l
  | Mult a b -> if O.gt (compare_expr a b) then (apply_lemma (`comm_mult); Mult b a) else skip ()
  | Minus a b ->
    // Forget about subtraction
    step_lemma (`minus_is_plus);
    step_lemma (`cong_plus);
    trefl ();
    let r = canon_point (Neg b) in
    canon_point (Plus a r)
  | _ -> skip ()

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
    (match run_tm (is_arith_expr l) with
      | Inr e ->
        (let _e = canon_point e in
          ())
      | Inl _ -> trefl ())
  | _ -> fail ("impossible: " ^ term_to_string g)

let canon () : Tac unit =
  seq (fun () -> pointwise canon_point_entry)
    (fun () ->
        simpl ();
        let _ = trytac trivial in
        ())

