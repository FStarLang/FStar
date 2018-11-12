module Normalization

open FStar.Tactics

(* A tactic that returns its argument after some steps of normalization *)
(* NOTE: This is relying on our unusual quote, which can inspect the shape of `x`
 * when the function is applied. This could be avoided by taking a `term` instead
 * and calling the tactic it with `quote` *)
let normalize (#t:Type) (steps : list norm_step) (x:t) : Tac unit =
  dup ();
  exact (quote x);
  norm steps;
  trefl ()

(* This tactic also depends on said behaviour of quote, and returns the definition of a top-level fvar *)
let def_of (#t:Type) (x:t) : Tac term =
  admit();
  let e = cur_env () in
  let t = quote x in
  match inspect t with
  | Tv_FVar fv -> begin
    let se = match lookup_typ e (inspect_fv fv) with
             | None -> fail "Not found..?"
             | Some se -> se
    in
    match inspect_sigelt se with
    | Sg_Let _ _ _ _ def -> def
    | _ -> fail "not a sig_let"
    end
  | _ -> fail "not an fvar"

let add_1 (x:int) : int = x + 1

(* add_2 is defined to be (x + 1) + 1 *)
let add_2 (x:int) : int = synth_by_tactic (fun () -> normalize [primops; delta] (add_1 (add_1 x)))

(* `four` is defined as `4` ... *)
let four : int = synth_by_tactic (fun () -> normalize [primops; delta] (add_2 2))

(* .. as we can check by inspecting its definition *)
let _ = assert_by_tactic True
                         (fun () ->
                            let t = def_of four in
                            if compare_term t (`4) = FStar.Order.Eq
                            then ()
                            else fail "Test 1")

(* If we only allow for Delta steps, then there's no primitive computation and we
 * end up with (2 + 1) + 1 *)
let four' : int = synth_by_tactic (fun () -> normalize [delta] (add_2 2))

let _ = assert_by_tactic True
                         (fun () ->
                            let t = def_of four' in
                            if compare_term t (`((2 + 1) + 1)) = FStar.Order.Eq
                            then ()
                            else fail "Test 2")

(* Here, we allow for primitive computation but don't allow for `add_2` to be expanded to
 * its definition, so the final result is `add_2 1` *)
let unfold_add_1: norm_step = delta_only ["Normalization.add_1"]

let three : int = synth_by_tactic
  (fun () -> normalize [delta; unfold_add_1; primops] (add_2 (add_1 0)))

let _ = assert_by_tactic True
                         (fun () ->
                            let t = def_of three in
                            if compare_term t (`(add_2 1)) = FStar.Order.Eq
                            then ()
                            else fail "Test 3")

(* Writing a function that normalizes its argument does not work! The tactic runs
 * when this definition is type-checked, and not when it's called. So, this function is just an
 * identity function with no special semantics. *)
let does_not_normalize (#t:Type) (x:t) : t =
  synth_by_tactic #t #unit (fun () -> normalize [primops; delta] x)

let four'' : int = does_not_normalize (2+2)

(* Now, four'' is defined as `does_not_normalize (2 + 2)`, with any tactic being run. This is indeed
 * *semantically* equal to 4, but not syntactically as the following tests show *)
let _ = assert (four'' == 4)

let _ = assert_by_tactic True
                         (fun () ->
                            let t = def_of four'' in
                            let s = `(does_not_normalize #int (2 + 2)) in
                            if compare_term t s = FStar.Order.Eq
                            then ()
                            else fail "Test 4")
