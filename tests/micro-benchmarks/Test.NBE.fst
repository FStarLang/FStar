(*
   Copyright 2008-2018 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module Test.NBE
// [iota; zeta; simplify; primops; delta_attr [`%va_qattr]; delta_only normal_steps]
unfold let normal (#a:Type) (x:a) : a = norm [primops; nbe] x
val x : bool
let x = normal (true && false)

val easy : n:nat -> Lemma (n + 2 = n + normal (1 + 1))
let easy n = ()

let rec append_int (x y:list int) : Tot (list int) =
  match x with
  | [] -> y
  | hd::tl -> hd::append_int tl y


let test1 =
  assert (norm [primops; delta; zeta; nbe] (append_int [1;2;3;4;5;6;7] [8;9])
          = [1;2;3;4;5;6;7;8;9])


let rec append (#a:Type) (x y:list a) : Tot (list a) =
  match x with
  | [] -> y
  | hd::tl -> hd::append tl y


let test2 =
  assert (norm [primops; delta; zeta; nbe] (append [1;2;3;4;5;6;7] [8;9])
          = [1;2;3;4;5;6;7;8;9])

let test3 =
  assert (norm [primops; delta; zeta; nbe] (List.append [1;2;3;4;5;6;7] [8;9])
          = [1;2;3;4;5;6;7;8;9])

// #set-options "--debug NBE --fuel 0"

(***** Differential tests: NBE must agree with the normalizer *****)
(* --no_smt so that these really test the normalization, and not the solver. *)

let f_nbe (x:int) = x + 1
let g_nbe (x:int) = f_nbe x + 1

[@@"opaque_to_smt"]
let opaque_nbe (x:int) = 7

(* delta_once (used by reveal_opaque) used to make NBE crash with
   "Pattern matching failed" (Should_unfold_once was unhandled). *)
#push-options "--no_smt"
let test_delta_once =
  assert (norm [nbe; primops; delta_once [`%opaque_nbe]] (opaque_nbe 1) == 7)

#pop-options

let test_reveal_opaque () =
  reveal_opaque (`%opaque_nbe) opaque_nbe;
  assert (opaque_nbe 4 == 7)

(* delta_fully used to make NBE fail with "Not yet handled", and then, once
   handled, to only unfold the head (the modified cfg was dropped by the
   TopLevelLet node). *)
#push-options "--no_smt"
let test_delta_fully =
  assert (norm [nbe; primops; delta_fully [`%g_nbe]] (g_nbe 1) == 3)
#pop-options

(* NBE refuses to unfold a recursive definition when one of the arguments
   that may appear in its decreases clause is symbolic. When the type of the
   definition records no decreases clause (F* does not record inferred ones),
   *every* argument used to be considered recursion-relevant, so a symbolic
   type argument -- e.g. the not-yet-resolved implicit of a quoted term --
   would block all unfolding. Type arguments can never be a well-founded
   measure, so they are now excluded. *)
let rec myapp (#a:Type) (l1 l2: list a) : Tot (list a) =
  match l1 with | [] -> l2 | h::t -> h :: myapp t l2

let test_rec_symbolic_type_arg =
  assert True by (
    let open FStar.Tactics.V2 in
    let steps = [delta; zeta; iota; primops; unascribe] in
    let t = (`(myapp [1;2] [3])) in
    let a = norm_term steps t in
    let b = norm_term (nbe::steps) t in
    if term_to_string a = term_to_string b then () else
    fail ("NBE and the normalizer disagree: " ^ term_to_string a ^ " vs " ^ term_to_string b))

(* The NBE embedding of machine integers used to build a __uint_to_t node,
   whereas the reference normalizer builds a uint_to_t one. Since __uint_to_t
   is an `unfold` alias of uint_to_t, any delta step rewrites a source literal
   into the latter, so the two engines produced results that were not
   syntactically equal (only equal up to delta). *)
#push-options "--no_smt"
let test_machine_int_repr =
  assert (norm [nbe; primops] (FStar.UInt8.add_underspec 3uy 2uy) == 5uy)
#pop-options

(* Same conservatism, second instance: an argument whose type is a *variable*
   can never be the one consumed by the recursion, since NBE cannot scrutinize
   a value of an abstract type. Treating it as recursion-relevant meant that
   FStar.Calc.calc_chain_related was never unfolded once its two element
   arguments went symbolic, which silently broke *every* calc proof under
   --use_nbe. *)
let rec chain_nbe (#a:Type) (rs:list (a -> a -> prop)) (x y:a) : prop =
  match rs with
  | [] -> x == y
  | r::rs -> exists (w:a). chain_nbe rs x w /\ r w y

let test_rec_symbolic_abstract_arg (a:Type) (r:a -> a -> prop) (x y:a) =
  assert True by (
    let open FStar.Tactics.V2 in
    let steps = [nbe; delta_only [`%chain_nbe]; zeta; iota] in
    let t = (`(chain_nbe [(`#(quote r))] (`#(quote x)) (`#(quote y)))) in
    let hd, _ = collect_app (norm_term steps t) in
    match inspect hd with
    | Tv_FVar fv
    | Tv_UInst fv _ ->
      if implode_qn (inspect_fv fv) = `%chain_nbe
      then fail ("NBE did not unfold chain_nbe")
      else ()
    | _ -> ())

(* NBE used to drop the source name of a refinement binder on readback,
   producing `_: int{_ > 3}` where the normalizer produces `x: int{x > 3}`. *)
let refine_nbe (n:int) : Type0 = x:int{x > n}

let test_refinement_binder_name =
  assert True by (
    let open FStar.Tactics.V2 in
    let steps = [delta; zeta; iota; primops; unascribe] in
    let t = (`(refine_nbe 3)) in
    let a = norm_term steps t in
    let b = norm_term (nbe::steps) t in
    if term_to_string a = term_to_string b then () else
    fail ("NBE and the normalizer disagree: " ^ term_to_string a ^ " vs " ^ term_to_string b))

(* When a match is stuck, the normalizer reads back its branches with all the
   unfolding directives removed (cfg_exclude_zeta in FStarC.TypeChecker.Normalize),
   so `g` below is left alone under the stuck `match`. NBE only used to turn
   zeta off, and so kept unfolding inside the branches. *)
let g_stuck (x:int) : int = x + 1
let h_stuck (l:list int) : int = match l with | [] -> 0 | y::_ -> g_stuck y

let test_stuck_match_branches (l:list int) =
  assert True by (
    let open FStar.Tactics.V2 in
    let steps = [delta_only [`%h_stuck; `%g_stuck]; iota; zeta; unascribe] in
    let t = (`(h_stuck (`#(quote l)))) in
    let a = norm_term steps t in
    let b = norm_term (nbe::steps) t in
    if term_to_string a = term_to_string b then () else
    fail ("NBE and the normalizer disagree: " ^ term_to_string a ^ " vs " ^ term_to_string b))

(* A recursive definition applied to symbolic arguments must still be unfolded
   once, as the reference normalizer does, leaving a stuck match behind. NBE
   used to refuse to unfold at all, which left FStar.Calc.calc_chain_related
   completely unreduced and made FStar.Calc fail to verify under --use_nbe. *)
let rec len_nbe (#a:Type) (l:list a) : nat =
  match l with | [] -> 0 | _::tl -> 1 + len_nbe tl

let test_rec_unfold_symbolic (l:list int) =
  assert True by (
    let open FStar.Tactics.V2 in
    let steps = [delta_only [`%len_nbe]; iota; zeta; unascribe] in
    let t = (`(len_nbe (`#(quote l)))) in
    let a = norm_term steps t in
    let b = norm_term (nbe::steps) t in
    if term_to_string a = term_to_string b then () else
    fail ("NBE and the normalizer disagree: " ^ term_to_string a ^ " vs " ^ term_to_string b))

(* A TopLevelLet/TopLevelRec node remembers the definition it stands for but
   not the configuration it was created in, so it could escape that
   configuration as a first-class value and be unfolded where no unfolding
   should happen -- in particular under the branches of a stuck match.
   `allP` below passes `faithful_nbe` around as a value, exactly as
   FStar.Reflection.TermEq does. *)
let rec allP_nbe (#a:Type) (f:a -> prop) (l:list a) : prop =
  match l with | [] -> True | x::xs -> f x /\ allP_nbe f xs
let rec faithful_nbe (n:nat) : prop = if n = 0 then True else faithful_nbe (n-1)

let test_value_escapes_cfg (l:list nat) =
  assert True by (
    let open FStar.Tactics.V2 in
    let steps = [delta_only [`%allP_nbe; `%faithful_nbe]; iota; zeta; unascribe] in
    let t = (`(allP_nbe faithful_nbe (`#(quote l)))) in
    let a = norm_term steps t in
    let b = norm_term (nbe::steps) t in
    if term_to_string a = term_to_string b then () else
    fail ("NBE and the normalizer disagree: " ^ term_to_string a ^ " vs " ^ term_to_string b))

(* Same, for a definition whose arity is hidden behind a type abbreviation:
   `U.arrow_formals` cannot see through `parser_nbe`, so `no_ext_nbe` used to
   be translated (and thus unfolded) eagerly instead of being delayed. *)
type parser_nbe = list int -> option int
let no_ext_nbe : parser_nbe = fun l -> None
let use_ext_nbe (l:list int) (p:parser_nbe) : option int =
  match l with | [] -> None | _::tl -> p tl

let test_arity_behind_abbreviation (l:list int) =
  assert True by (
    let open FStar.Tactics.V2 in
    let steps = [delta_only [`%use_ext_nbe; `%no_ext_nbe]; iota; zeta; unascribe] in
    let t = (`(use_ext_nbe (`#(quote l)) no_ext_nbe)) in
    let a = norm_term steps t in
    let b = norm_term (nbe::steps) t in
    if term_to_string a = term_to_string b then () else
    fail ("NBE and the normalizer disagree: " ^ term_to_string a ^ " vs " ^ term_to_string b))
