(*
   Copyright 2008-2026 Microsoft Research

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
module LetRecNames

/// A name bound by an inner [let rec] goes out of scope with the [let rec], so
/// no inferred type may mention one. The typechecker enforces this by never
/// introducing such a name into a refinement in the first place (see
/// [Env.mentions_rec_name] and its uses in [TypeChecker.Util]).
///
/// If any of those guards is dropped, the name is introduced and then has to be
/// eliminated when it escapes; the only way to do that is to close over it
/// existentially, which leaves a higher-order existential that is true but
/// carries no information, e.g.
///
///   a1 : n:int -> _:int{exists (f: (x:int -> int)). _ == f n}
///
/// Each check below pins that no such existential appears.

open FStar.Tactics.V2

/// Fails if the type of [x] is an arrow whose result is a refinement stating an
/// existential -- the shape a leaked [let rec] name produces.
let no_leaked_rec_name (nm: string) (#a: Type) (x: a) : Tac unit =
  let t = tc (top_env ()) (quote x) in
  match inspect t with
  | Tv_Arrow _ c ->
    (match inspect_comp c with
     | C_Total r ->
       (match inspect r with
        | Tv_Refine _ phi ->
          let hd, _ = collect_app phi in
          (* [l_Exists] is universe-polymorphic, so its head is a [Tv_UInst]. *)
          let hd_name =
            match inspect hd with
            | Tv_FVar fv
            | Tv_UInst fv _ -> implode_qn (inspect_fv fv)
            | _ -> ""
          in
          if hd_name = `%(l_Exists)
          then fail ("the inferred type of " ^ nm ^
                     " existentially closes a let rec-bound name: " ^
                     term_to_string t)
          else ()
        | _ -> ())
     | _ -> fail ("expected " ^ nm ^ " to have a Tot comp"))
  | _ -> fail ("expected " ^ nm ^ " to be an arrow")

(* The body is an application of the recursive function. *)
let a1 (n: int) = let rec f (x: int) : int = x in f n

(* ... bound to a let first: the name arrives in the refinement by substitution,
   not by [maybe_assume_result_eq_pure_term], so guarding the latter alone does
   not suffice. *)
let a2 (n: int) = let rec f (x: int) : int = x in let y = f n in y

(* ... under a primitive operation. *)
let a3 (n: int) = let rec f (x: int) : int = x in f n + 1

(* The recursive function has a refined result type: the refinement is genuine
   information about the result and must survive, unlike the equation naming f. *)
let a4 (n: int) = let rec f (x: int) : y:int{y >= 0} = 0 in f n

(* Mutual-looking recursion on a nat. *)
let a5 (n: nat) = let rec ev (x: nat) : bool = if x = 0 then true else ev (x - 1) in ev n

(* Two recursive functions in scope. *)
let a6 (n: int) =
  let rec f (x: int) : int = x in
  let rec g (x: int) : int = x in
  g (f n)

(* The name appears under a data constructor. *)
let a7 (n: int) = let rec f (x: int) : int = x in [f n; n]

(* The application is in a branch. *)
let a8 (n: int) = let rec f (x: int) : int = x in if n > 0 then f n else n

let _ =
  assert True
    by (no_leaked_rec_name "a1" a1;
        no_leaked_rec_name "a2" a2;
        no_leaked_rec_name "a3" a3;
        no_leaked_rec_name "a4" a4;
        no_leaked_rec_name "a5" a5;
        no_leaked_rec_name "a6" a6;
        no_leaked_rec_name "a7" a7;
        no_leaked_rec_name "a8" a8)
