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
