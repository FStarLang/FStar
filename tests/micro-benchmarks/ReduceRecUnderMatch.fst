module ReduceRecUnderMatch

(** An example adapted from one provided by Son Ho
    Demonstrates the use of the [zeta_full] option of the normalizer *)

module T = FStar.Tactics
open FStar.Tactics

(** A check to make sure that [t0] doesn't appear in the goal
    and to catch regressions.
    Thanks @guido *)
let checkno (t0:term) : Tac unit =
  let control (t:term) : Tac (bool & ctrl_flag) =
    if term_eq t t0
    then fail ("Found " ^ term_to_string t ^ " in the goal")
    else false, Skip
  in
  let rewrite () : Tac unit =
    fail "not reached"
  in
  ctrl_rewrite BottomUp control rewrite

let qname_as_term (x:string) : term =
  let qn = explode_qn x in
  let fv = pack_fv qn in
  let tv = Tv_FVar fv in
  pack_ln tv

(** This tactic unfolds only [t] and reduces matches and recursive
    functions fully *)
let unroll t () : Tac unit =
  T.norm [zeta_full; delta_only [t]; iota];
  checkno (qname_as_term t);
  T.trefl()

(* [n] is a "meta" parameter *)
assume val f1 (n : nat) (m : bool) :
  Dv bool

(** [l] is a "meta" parameter

    It's optional, but you can write it in this curried style to at
    least prove that the "meta-recursion" is terminating.
 *)
let rec f2 (l : list nat)
  : Tot (n : bool -> Dv bool)
        (decreases l)
  = fun n ->
    match l with
    | [] -> false
    | x :: l' ->
      let r = f1 x n in
      if r then f2 l' n else r

(** To partially evaluate all the recursion in [f2],
    postprocess the definition with the unroll tactic *)
[@(postprocess_with (unroll (`%f2)))]
let f3 (b:bool) : Dv bool =
    f2 [1;2;3;4] b

(** You can also do the same, but wait until extraction to unroll it *)
[@(postprocess_for_extraction_with (unroll (`%f2)))]
let f4 (b:bool) : Dv bool =
    f2 [1;2;3;4] b

(* Unfortunately, this style doesn't work yet because of a normalizer
   bug in the handling of Pervasives.norm. I'm trying to fix that, but
   meanwhile, you can use the above style *)
let g : (b:bool) -> Dv bool =
  Pervasives.norm [zeta_full; delta_only [`%f2]; iota] (f2 [1;2;3])
