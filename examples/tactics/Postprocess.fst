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
module Postprocess

open FStar.Tactics.V2

assume val foo : int -> int
assume val lem : unit -> Lemma (foo 1 == foo 2)
let tau () = apply_lemma (`lem)

[@@(postprocess_with tau)]
let x : int = foo 1

[@@(postprocess_for_extraction_with tau)]
let y : int = foo 1

let _ = assert (x == foo 2)
let _ = assert (y == foo 1) // but `foo 2` in extracted code

(* More hardcore transformations *)

noeq
type t1 =
    | A1 : t1
    | B1 : int -> t1
    | C1 : (int -> t1) -> t1

noeq
type t2 =
    | A2 : t2
    | B2 : int -> t2
    | C2 : (int -> t2) -> t2

let rec lift : t1 -> t2 =
    function
    | A1 -> A2
    | B1 i -> B2 i
    | C1 f -> C2 (fun x -> lift (f x))

let lemA () : Lemma (lift A1 == A2) = ()
let lemB x : Lemma (lift (B1 x) == (B2 x)) = ()
let lemC ($f: int -> t1) : Lemma (lift (C1 f) == C2 (fun x -> lift (f x))) by (compute ()) = ()

(* These could really be polymorphic *)
let congB #i #j (_ : squash (i == j)) : Lemma (B2 i == B2 j) = ()
let congC #f #g (_ : squash (f == g)) : Lemma (C2 f == C2 g) = ()

let xx = C1 (function
             | 0 -> A1
             | 5 -> B1 42
             | x -> B1 24)

open FStar.FunctionalExtensionality

let q_as_lem (#a:Type) (#b:a -> Type) (p:squash (forall x. b x)) (x:a)
  : Lemma (b x)
  = ()

let congruence_fun #a (#b:a -> Type) (f g:(x:a -> b x)) (x:squash (forall x. f x == g x)) :
  Lemma (ensures (fun (x:a) -> f x) == (fun (x:a) -> g x)) =
  assert ((fun (x:a) -> f x) == (fun (x:a) -> g x))
      by (l_to_r [quote (q_as_lem x)];
          trefl())

let apply_feq_lem #a #b ($f $g : a -> b) : Lemma (requires (forall x. f x == g x))
                                                (ensures  ((fun x -> f x) == (fun x -> g x))) = congruence_fun f g ()

let fext () = apply_lemma (`apply_feq_lem); dismiss (); ignore (forall_intros ())

let _onL a b c (_ : squash (a == b)) (_ : squash (b == c)) : Lemma (a == c) = ()
let onL () = apply_lemma (`_onL)

// invariant: takes goals of shape squash (E == ?u) and solves them
let rec push_lifts' (u:unit) : Tac unit =
  match term_as_formula (cur_goal ()) with
  | Comp (Eq _) lhs rhs ->
    begin
    match inspect lhs with
    | Tv_App h t ->
      begin match inspect h with
      | Tv_FVar fv ->
        if fv_to_string fv = `%lift
        then case_analyze (fst t)
        else fail "not a lift (1)"
      | _ -> fail "not a lift (2)"
      end

    | Tv_Abs _ _ ->
      fext ();
      push_lifts' ()

    | _ -> fail "not a lift (3)"
    end
  | _ ->
    fail "not an equality"
and case_analyze (lhs:term) : Tac unit =
    let ap l =
      onL (); apply_lemma l
    in
    let lhs = norm_term [weak;hnf;primops;delta] lhs in
    let head, args = collect_app lhs in
    begin match inspect head with
    | Tv_FVar fv ->
           if fv_to_string fv = `%A1 then (apply_lemma (`lemA))
      else if fv_to_string fv = `%B1 then (ap (`lemB); apply_lemma (`congB); push_lifts' ())
      else if fv_to_string fv = `%C1 then (ap (`lemC); apply_lemma (`congC); push_lifts' ())
      else (tlabel "unknown fv"; trefl ())
    | _ ->
      tlabel "head unk";
      trefl ()
    end

let push_lifts () : Tac unit =
  push_lifts' ();
  (* dump "after"; *)
  ()

//#push-options "--tactic_trace_d 2"
[@@(postprocess_with push_lifts)]
let yy = lift xx

[@@(postprocess_with push_lifts)]
let zz1 = lift (C1 (fun y -> (C1 (fun x -> A1))))

[@@(postprocess_for_extraction_with push_lifts)]
let zz2 = lift (C1 (fun y -> (C1 (fun x -> A1))))
