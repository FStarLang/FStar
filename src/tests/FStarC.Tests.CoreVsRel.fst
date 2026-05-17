(*
   Copyright 2025 Microsoft Research

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
module FStarC.Tests.CoreVsRel
(* Tests comparing FStarC.TypeChecker.Core and FStarC.TypeChecker.Rel
   on subtyping and equality of types without uvars.
   Related to GitHub issue #4239: Core produces incorrect guards for
   type abbreviation applications by treating them as injective. *)

open FStarC
open FStarC.Effect
open FStarC.Errors
open FStarC.Syntax.Syntax
open FStarC.Tests.Pars
module S = FStarC.Syntax.Syntax
module U = FStarC.Syntax.Util
module N = FStarC.TypeChecker.Normalize
module Rel = FStarC.TypeChecker.Rel
module Core = FStarC.TypeChecker.Core
module Env = FStarC.TypeChecker.Env
open FStarC.TypeChecker.Common
open FStarC.TypeChecker.Env
open FStarC.Tests.Util

open FStarC.Class.Show

let tcenv () : ML _ = Pars.init()

let success = mk_ref true

let fail msg : ML unit =
    Format.print_string msg;
    success := false

let guard_to_string env g : ML _ = match g with
    | Trivial -> "trivial"
    | NonTrivial f ->
      N.term_to_string env f

(* Run Core's check_term_subtyping, return guard or error *)
let run_core_subtyping (env:Env.env) (t0 t1:typ)
  : ML (either (option typ) string)
  = match Core.check_term_subtyping true true env t0 t1 with
    | Inl None -> Inl None
    | Inl (Some (g, _cb)) -> Inl (Some g)
    | Inr err -> Inr (Core.print_error err)

(* Run Core's check_term_equality, return guard or error *)
let run_core_equality (env:Env.env) (t0 t1:typ)
  : ML (either (option typ) string)
  = match Core.check_term_equality true true env t0 t1 with
    | Inl None -> Inl None
    | Inl (Some (g, _cb)) -> Inl (Some g)
    | Inr err -> Inr (Core.print_error err)

(* Run Rel's get_subtyping_prop, return guard_formula *)
let run_rel_subtyping (env:Env.env) (t0 t1:typ)
  : ML (option guard_formula)
  = match Rel.get_subtyping_prop env t0 t1 with
    | None -> None
    | Some g ->
      let g = Rel.simplify_guard env g in
      Some g.guard_f

(* Run Rel's try_teq (no SMT), return guard_formula *)
let run_rel_equality (env:Env.env) (t0 t1:typ)
  : ML (option guard_formula)
  = match Rel.try_teq false env t0 t1 with
    | None -> None
    | Some g ->
      let g = Rel.simplify_guard env g in
      Some g.guard_f

type outcome =
  | BothTrivial     (* both succeed with no guard *)
  | BothGuarded     (* both succeed with a guard *)
  | CoreTrivialRelGuarded (* Core trivial, Rel has guard *)
  | CoreGuardedRelTrivial (* Core has guard, Rel trivial *)
  | CoreFailRelSucceed    (* Core fails, Rel succeeds *)
  | RelFailCoreSucceed    (* Rel fails, Core succeeds *)
  | BothFail              (* both fail *)

let show_outcome o = match o with
  | BothTrivial -> "BothTrivial"
  | BothGuarded -> "BothGuarded"
  | CoreTrivialRelGuarded -> "CoreTrivialRelGuarded"
  | CoreGuardedRelTrivial -> "CoreGuardedRelTrivial"
  | CoreFailRelSucceed -> "CoreFailRelSucceed"
  | RelFailCoreSucceed -> "RelFailCoreSucceed"
  | BothFail -> "BothFail"

(* Compare subtyping of t0 <: t1 in Core vs Rel.
   Can optionally take a custom env (for tests with binders). *)
let compare_subtyping_env (i:int) (env:Env.env) (t0 t1:typ) (expected:outcome)
  : ML unit
  = Options.parse_cmd_line () |> ignore;
    Format.print1 "CoreVsRel subtyping test %s ... " (show i);
    let core_res = run_core_subtyping env t0 t1 in
    let rel_res = run_rel_subtyping env t0 t1 in
    let actual =
      match core_res, rel_res with
      | Inl None,    Some Trivial        -> BothTrivial
      | Inl None,    Some (NonTrivial _)  -> CoreTrivialRelGuarded
      | Inl None,    None                -> RelFailCoreSucceed
      | Inl (Some _), Some Trivial        -> CoreGuardedRelTrivial
      | Inl (Some _), Some (NonTrivial _) -> BothGuarded
      | Inl (Some _), None                -> RelFailCoreSucceed
      | Inr _,       Some _              -> CoreFailRelSucceed
      | Inr _,       None                -> BothFail
    in
    if actual = expected then (
      Format.print1 "ok [%s]\n" (show_outcome actual);
      (match actual with
       | BothGuarded ->
         (match core_res with
          | Inl (Some g) -> Format.print1 "  Core guard: %s\n" (show g)
          | _ -> ());
         (match rel_res with
          | Some (NonTrivial f) -> Format.print1 "  Rel guard:  %s\n" (N.term_to_string env f)
          | _ -> ())
       | _ -> ())
    ) else (
      fail (Format.fmt3 "FAILED: expected %s, got %s (test %s)\n"
              (show_outcome expected) (show_outcome actual) (show i));
      (match core_res with
       | Inl None -> Format.print_string "  Core: trivial\n"
       | Inl (Some g) -> Format.print1 "  Core guard: %s\n" (show g)
       | Inr err -> Format.print1 "  Core error: %s\n" err);
      (match rel_res with
       | None -> Format.print_string "  Rel: failed\n"
       | Some Trivial -> Format.print_string "  Rel: trivial\n"
       | Some (NonTrivial f) -> Format.print1 "  Rel guard:  %s\n" (N.term_to_string env f))
    );
    Options.init ()

let compare_subtyping (i:int) (t0 t1:typ) (expected:outcome) : ML unit =
  compare_subtyping_env i (tcenv ()) t0 t1 expected

(* Compare equality of t0 and t1 in Core vs Rel.
   Can optionally take a custom env (for tests with binders). *)
let compare_equality_env (i:int) (env:Env.env) (t0 t1:typ) (expected:outcome)
  : ML unit
  = Options.parse_cmd_line () |> ignore;
    Format.print1 "CoreVsRel equality test %s ... " (show i);
    let core_res = run_core_equality env t0 t1 in
    let rel_res = run_rel_equality env t0 t1 in
    let actual =
      match core_res, rel_res with
      | Inl None,    Some Trivial        -> BothTrivial
      | Inl None,    Some (NonTrivial _)  -> CoreTrivialRelGuarded
      | Inl None,    None                -> RelFailCoreSucceed
      | Inl (Some _), Some Trivial        -> CoreGuardedRelTrivial
      | Inl (Some _), Some (NonTrivial _) -> BothGuarded
      | Inl (Some _), None                -> RelFailCoreSucceed
      | Inr _,       Some _              -> CoreFailRelSucceed
      | Inr _,       None                -> BothFail
    in
    if actual = expected then (
      Format.print1 "ok [%s]\n" (show_outcome actual);
      (match actual with
       | BothGuarded ->
         (match core_res with
          | Inl (Some g) -> Format.print1 "  Core guard: %s\n" (show g)
          | _ -> ());
         (match rel_res with
          | Some (NonTrivial f) -> Format.print1 "  Rel guard:  %s\n" (N.term_to_string env f)
          | _ -> ())
       | _ -> ())
    ) else (
      fail (Format.fmt3 "FAILED: expected %s, got %s (test %s)\n"
              (show_outcome expected) (show_outcome actual) (show i));
      (match core_res with
       | Inl None -> Format.print_string "  Core: trivial\n"
       | Inl (Some g) -> Format.print1 "  Core guard: %s\n" (show g)
       | Inr err -> Format.print1 "  Core error: %s\n" err);
      (match rel_res with
       | None -> Format.print_string "  Rel: failed\n"
       | Some Trivial -> Format.print_string "  Rel: trivial\n"
       | Some (NonTrivial f) -> Format.print1 "  Rel guard:  %s\n" (N.term_to_string env f))
    );
    Options.init ()

let compare_equality (i:int) (t0 t1:typ) (expected:outcome) : ML unit =
  compare_equality_env i (tcenv ()) t0 t1 expected

(* Test that a fragment typechecks (uses Rel, not Core).
   Useful to verify that the full typechecker handles these cases. *)
let tc_fragment_ok (i:int) (frag:string) : ML unit =
  Format.print1 "CoreVsRel tc_fragment test %s ... " (show i);
  (try
    Pars.pars_and_tc_fragment frag;
    Format.print_string "ok\n"
  with
  | Error (_, msg, r, _) ->
    fail (Format.fmt2 "FAILED: %s: %s\n" (FStarC.Range.string_of_range r) (Errors.rendermsg msg))
  | e ->
    fail (Format.fmt1 "FAILED: unexpected exception: %s\n" (FStarC.Util.message_of_exn e)))

(* Test that a fragment fails to typecheck (expects a Core error) *)
let tc_fragment_fail (i:int) (frag:string) : ML unit =
  Format.print1 "CoreVsRel tc_fragment_fail test %s ... " (show i);
  (try
    Pars.pars_and_tc_fragment frag;
    fail "FAILED: expected error but succeeded\n"
  with
  | Error _ ->
    FStarC.Errors.report_all () |> ignore;
    Format.print_string "ok (failed as expected)\n"
  | _ ->
    FStarC.Errors.report_all () |> ignore;
    Format.print_string "ok (failed as expected)\n")

(* ============================================================ *)
(* Test suite *)
(* ============================================================ *)

let run_all () : ML bool =
    Format.print_string "\n=== Testing Core vs Rel agreement ===\n";

    (* ---- Setup type abbreviations used by multiple tests ---- *)
    let _ = Pars.pars_and_tc_fragment
      "let cvr_natlt (n: nat) = i:nat { i < n }\n\
       let cvr_ty0 n = x:int { x >= n }\n\
       let cvr_ty1 n = x:cvr_ty0 n { x > n }"
    in

    (* ----------------------------------------------------------
       Group 1: Syntactically identical types (control cases)
       Core and Rel should both return trivial.
       ---------------------------------------------------------- *)

    (* Test 100: natlt n =?= natlt n — identical type abbrev applications *)
    let _ =
      let t0 = tc "cvr_natlt 42" in
      let t1 = tc "cvr_natlt 42" in
      compare_equality 100 t0 t1 BothTrivial
    in

    (* Test 101: int =?= int — base type equality *)
    let _ =
      compare_equality 101 (tc "int") (tc "int") BothTrivial
    in

    (* Test 102: natlt 42 <: natlt 42 — identical abbrev subtyping *)
    let _ =
      let t0 = tc "cvr_natlt 42" in
      let t1 = tc "cvr_natlt 42" in
      compare_subtyping 102 t0 t1 BothTrivial
    in

    (* ----------------------------------------------------------
       Group 2: Simple refinement subtyping (no abbreviations)
       These should work the same in Core and Rel.
       ---------------------------------------------------------- *)

    (* Test 200: x:int{x > 0} <: int — refinement subtype of base *)
    let _ =
      compare_subtyping 200 (tc "x:int{ x > 0 }") (tc "int") BothTrivial
    in

    (* Test 201: int <: x:int{x > 0} — base to refinement, needs guard *)
    let _ =
      compare_subtyping 201 (tc "int") (tc "x:int{ x > 0 }") BothGuarded
    in

    (* Test 202: x:int{x > 0} <: x:int{x >= 0} — refinement to weaker refinement *)
    let _ =
      compare_subtyping 202 (tc "x:int{ x > 0 }") (tc "x:int{ x >= 0 }") BothGuarded
    in

    (* Test 203: nat <: int — nat is a refinement of int *)
    let _ =
      compare_subtyping 203 (tc "nat") (tc "int") BothTrivial
    in

    (* ----------------------------------------------------------
       Group 3: Type abbreviation subtyping with concrete args
       ---------------------------------------------------------- *)

    (* Test 300: cvr_natlt 5 <: cvr_natlt 10
       After unfolding: i:nat{i < 5} <: i:nat{i < 10} *)
    let _ =
      compare_subtyping 300 (tc "cvr_natlt 5") (tc "cvr_natlt 10") BothGuarded
    in

    (* Test 301: cvr_natlt 10 <: cvr_natlt 5 *)
    let _ =
      compare_subtyping 301 (tc "cvr_natlt 10") (tc "cvr_natlt 5") BothGuarded
    in

    (* Test 302: cvr_ty0 5 <: cvr_ty0 10 *)
    let _ =
      compare_subtyping 302 (tc "cvr_ty0 5") (tc "cvr_ty0 10") BothGuarded
    in

    (* Test 303: cvr_ty1 17 =?= x:cvr_ty0 17 { x > 17 } *)
    let _ =
      compare_equality 303 (tc "cvr_ty1 17") (tc "x:cvr_ty0 17 { x > 17 }") BothTrivial
    in

    (* Test 304: cvr_ty0 17 =?= x:int { x >= 17 } *)
    let _ =
      compare_equality 304 (tc "cvr_ty0 17") (tc "x:int { x >= 17 }") BothTrivial
    in

    (* ----------------------------------------------------------
       Group 4: Arrow types with type abbreviation domains
       ---------------------------------------------------------- *)

    (* Test 400: (cvr_natlt 10 -> bool) <: (cvr_natlt 5 -> bool)
       Contravariant domain: need cvr_natlt 5 <: cvr_natlt 10 *)
    let _ =
      compare_subtyping 400 (tc "cvr_natlt 10 -> bool") (tc "cvr_natlt 5 -> bool") BothGuarded
    in

    (* Test 401: (cvr_natlt 5 -> bool) <: (cvr_natlt 10 -> bool) *)
    let _ =
      compare_subtyping 401 (tc "cvr_natlt 5 -> bool") (tc "cvr_natlt 10 -> bool") BothGuarded
    in

    (* Test 402: (int -> cvr_natlt 10) <: (int -> cvr_natlt 5)
       Covariant in codomain *)
    let _ =
      compare_subtyping 402 (tc "int -> Tot (cvr_natlt 10)") (tc "int -> Tot (cvr_natlt 5)") BothGuarded
    in

    (* Test 403: (nat -> bool) <: (int -> bool) — contravariant domain needs guard *)
    let _ =
      compare_subtyping 403 (tc "nat -> bool") (tc "int -> bool") BothGuarded
    in

    (* Test 404: (int -> bool) <: (nat -> bool) — trivial *)
    let _ =
      compare_subtyping 404 (tc "int -> bool") (tc "nat -> bool") BothTrivial
    in

    (* ----------------------------------------------------------
       Group 5: Nested type abbreviation subtyping
       ---------------------------------------------------------- *)

    (* Test 500: cvr_ty1 17 <: cvr_ty0 17 — dropping outer refinement *)
    let _ =
      compare_subtyping 500 (tc "cvr_ty1 17") (tc "cvr_ty0 17") BothTrivial
    in

    (* Test 501: cvr_ty0 17 <: cvr_ty1 17 — needs refinement guard *)
    let _ =
      compare_subtyping 501 (tc "cvr_ty0 17") (tc "cvr_ty1 17") BothGuarded
    in

    (* Test 502: cvr_ty1 5 <: cvr_ty0 10 *)
    let _ =
      compare_subtyping 502 (tc "cvr_ty1 5") (tc "cvr_ty0 10") BothGuarded
    in

    (* ----------------------------------------------------------
       Group 6: Type abbreviation equality
       ---------------------------------------------------------- *)

    (* Test 600: cvr_natlt 5 =?= cvr_natlt 10
       Core can produce a guard (forall i. i < 5 == i < 10);
       Rel's try_teq with smt_ok=false can't solve this, so it fails.
       This is an expected divergence: equality of distinct type
       abbreviation applications is harder for Rel without SMT. *)
    let _ =
      compare_equality 600 (tc "cvr_natlt 5") (tc "cvr_natlt 10") RelFailCoreSucceed
    in

    (* Test 601: cvr_natlt 5 =?= i:nat{ i < 5 } — unfolding should yield equality *)
    let _ =
      compare_equality 601 (tc "cvr_natlt 5") (tc "i:nat{ i < 5 }") BothTrivial
    in

    (* ----------------------------------------------------------
       Group 7: Type abbreviation with binder variables (issue #4239)
       This is where the Core bug manifests.
       We push binder variables into the environment and then
       call Core/Rel directly with type applications using those vars.
       ---------------------------------------------------------- *)

    (* Helper: create an environment with binders n:nat, i:nat *)
    let env_with_n_i () : ML (Env.env & bv & bv) =
      let env = tcenv () in
      let nat_t = tc "nat" in
      let n_bv = S.gen_bv "n" None nat_t in
      let env = Env.push_bv env n_bv in
      let i_bv = S.gen_bv "i" None nat_t in
      let env = Env.push_bv env i_bv in
      (env, n_bv, i_bv)
    in

    let cvr_natlt_head = tc "cvr_natlt" in
    let cvr_ty0_head = tc "cvr_ty0" in

    (* Test 700: with n:nat, i:nat in env:
       cvr_natlt n <: cvr_natlt n — trivially equal *)
    let _ =
      let env, n_bv, _i_bv = env_with_n_i () in
      let n_name = S.bv_to_name n_bv in
      let t0 = S.mk_Tm_app cvr_natlt_head [(n_name, None)] FStarC.Range.dummyRange in
      compare_subtyping_env 700 env t0 t0 BothTrivial
    in

    (* Test 701: with n:nat, i:nat in env:
       cvr_natlt i <: cvr_natlt n
       Core should unfold to (x:nat{x < i}) <: (x:nat{x < n})
       and produce guard: forall x:nat. x < i ==> x < n
       BUG: Core may produce guard: i == n (injectivity) *)
    let _ =
      let env, n_bv, i_bv = env_with_n_i () in
      let n_name = S.bv_to_name n_bv in
      let i_name = S.bv_to_name i_bv in
      let t0 = S.mk_Tm_app cvr_natlt_head [(i_name, None)] FStarC.Range.dummyRange in
      let t1 = S.mk_Tm_app cvr_natlt_head [(n_name, None)] FStarC.Range.dummyRange in
      compare_subtyping_env 701 env t0 t1 BothGuarded
    in

    (* Test 702: with n:nat, i:nat in env:
       cvr_natlt n <: cvr_natlt i (reverse direction) *)
    let _ =
      let env, n_bv, i_bv = env_with_n_i () in
      let n_name = S.bv_to_name n_bv in
      let i_name = S.bv_to_name i_bv in
      let t0 = S.mk_Tm_app cvr_natlt_head [(n_name, None)] FStarC.Range.dummyRange in
      let t1 = S.mk_Tm_app cvr_natlt_head [(i_name, None)] FStarC.Range.dummyRange in
      compare_subtyping_env 702 env t0 t1 BothGuarded
    in

    (* Test 703: with n:nat, i:nat in env:
       cvr_ty0 i <: cvr_ty0 n *)
    let _ =
      let env, n_bv, i_bv = env_with_n_i () in
      let n_name = S.bv_to_name n_bv in
      let i_name = S.bv_to_name i_bv in
      let t0 = S.mk_Tm_app cvr_ty0_head [(i_name, None)] FStarC.Range.dummyRange in
      let t1 = S.mk_Tm_app cvr_ty0_head [(n_name, None)] FStarC.Range.dummyRange in
      compare_subtyping_env 703 env t0 t1 BothGuarded
    in

    (* Test 704: with n:nat, i:nat in env:
       cvr_natlt i =?= cvr_natlt n (equality with variables) *)
    let _ =
      let env, n_bv, i_bv = env_with_n_i () in
      let n_name = S.bv_to_name n_bv in
      let i_name = S.bv_to_name i_bv in
      let t0 = S.mk_Tm_app cvr_natlt_head [(i_name, None)] FStarC.Range.dummyRange in
      let t1 = S.mk_Tm_app cvr_natlt_head [(n_name, None)] FStarC.Range.dummyRange in
      (* Core produces guard i == n; Rel fails without SMT *)
      compare_equality_env 704 env t0 t1 RelFailCoreSucceed
    in

    (* Test 705: with n:nat, i:nat in env:
       cvr_ty0 n <: cvr_ty0 n — reflexive subtyping with variables *)
    let _ =
      let env, n_bv, _i_bv = env_with_n_i () in
      let n_name = S.bv_to_name n_bv in
      let t0 = S.mk_Tm_app cvr_ty0_head [(n_name, None)] FStarC.Range.dummyRange in
      compare_subtyping_env 705 env t0 t0 BothTrivial
    in

    (* Test 706: with n:nat, i:nat in env:
       cvr_ty0 i =?= cvr_ty0 n (equality with variables)
       Same bug pattern as 704 but with different abbreviation. *)
    let _ =
      let env, n_bv, i_bv = env_with_n_i () in
      let n_name = S.bv_to_name n_bv in
      let i_name = S.bv_to_name i_bv in
      let t0 = S.mk_Tm_app cvr_ty0_head [(i_name, None)] FStarC.Range.dummyRange in
      let t1 = S.mk_Tm_app cvr_ty0_head [(n_name, None)] FStarC.Range.dummyRange in
      compare_equality_env 706 env t0 t1 RelFailCoreSucceed
    in

    (* ----------------------------------------------------------
       Group 8: Arrow types with variable type abbrev args (issue #4239)
       ---------------------------------------------------------- *)

    (* Test 800: with n:nat, i:nat in env:
       (cvr_natlt n -> bool) <: (cvr_natlt i -> bool)
       Contravariant: need cvr_natlt i <: cvr_natlt n
       This is the EXACT scenario from issue #4239. *)
    let _ =
      let env, n_bv, i_bv = env_with_n_i () in
      let n_name = S.bv_to_name n_bv in
      let i_name = S.bv_to_name i_bv in
      let dom0 = S.mk_Tm_app cvr_natlt_head [(n_name, None)] FStarC.Range.dummyRange in
      let dom1 = S.mk_Tm_app cvr_natlt_head [(i_name, None)] FStarC.Range.dummyRange in
      let bool_t = tc "bool" in
      let b0 = S.mk_binder (S.gen_bv "_" None dom0) in
      let c0 = S.mk_Total bool_t in
      let t0 = U.arrow [b0] c0 in
      let b1 = S.mk_binder (S.gen_bv "_" None dom1) in
      let c1 = S.mk_Total bool_t in
      let t1 = U.arrow [b1] c1 in
      compare_subtyping_env 800 env t0 t1 BothGuarded
    in

    (* Test 801: with n:nat, i:nat in env:
       (cvr_natlt i -> bool) <: (cvr_natlt n -> bool)
       Contravariant: need cvr_natlt n <: cvr_natlt i *)
    let _ =
      let env, n_bv, i_bv = env_with_n_i () in
      let n_name = S.bv_to_name n_bv in
      let i_name = S.bv_to_name i_bv in
      let dom0 = S.mk_Tm_app cvr_natlt_head [(i_name, None)] FStarC.Range.dummyRange in
      let dom1 = S.mk_Tm_app cvr_natlt_head [(n_name, None)] FStarC.Range.dummyRange in
      let bool_t = tc "bool" in
      let b0 = S.mk_binder (S.gen_bv "_" None dom0) in
      let c0 = S.mk_Total bool_t in
      let t0 = U.arrow [b0] c0 in
      let b1 = S.mk_binder (S.gen_bv "_" None dom1) in
      let c1 = S.mk_Total bool_t in
      let t1 = U.arrow [b1] c1 in
      compare_subtyping_env 801 env t0 t1 BothGuarded
    in

    (* Test 802: with n:nat, i:nat in env:
       (cvr_ty0 n -> bool) <: (cvr_ty0 i -> bool)
       Contravariant: need cvr_ty0 i <: cvr_ty0 n
       Same bug pattern as 800 but with cvr_ty0 *)
    let _ =
      let env, n_bv, i_bv = env_with_n_i () in
      let n_name = S.bv_to_name n_bv in
      let i_name = S.bv_to_name i_bv in
      let dom0 = S.mk_Tm_app cvr_ty0_head [(n_name, None)] FStarC.Range.dummyRange in
      let dom1 = S.mk_Tm_app cvr_ty0_head [(i_name, None)] FStarC.Range.dummyRange in
      let bool_t = tc "bool" in
      let b0 = S.mk_binder (S.gen_bv "_" None dom0) in
      let c0 = S.mk_Total bool_t in
      let t0 = U.arrow [b0] c0 in
      let b1 = S.mk_binder (S.gen_bv "_" None dom1) in
      let c1 = S.mk_Total bool_t in
      let t1 = U.arrow [b1] c1 in
      compare_subtyping_env 802 env t0 t1 BothGuarded
    in

    (* Test 803: with n:nat, i:nat in env:
       (int -> cvr_natlt n) <: (int -> cvr_natlt i)
       Covariant codomain with variable args *)
    let _ =
      let env, n_bv, i_bv = env_with_n_i () in
      let n_name = S.bv_to_name n_bv in
      let i_name = S.bv_to_name i_bv in
      let int_t = tc "int" in
      let cod0 = S.mk_Tm_app cvr_natlt_head [(n_name, None)] FStarC.Range.dummyRange in
      let cod1 = S.mk_Tm_app cvr_natlt_head [(i_name, None)] FStarC.Range.dummyRange in
      let b = S.mk_binder (S.gen_bv "_" None int_t) in
      let t0 = U.arrow [b] (S.mk_Total cod0) in
      let t1 = U.arrow [b] (S.mk_Total cod1) in
      compare_subtyping_env 803 env t0 t1 BothGuarded
    in

    (* ----------------------------------------------------------
       Group 9: Multi-argument type abbreviation applications
       ---------------------------------------------------------- *)

    let _ = Pars.pars_and_tc_fragment
      "let cvr_defn (x:nat) : nat -> nat -> Type0 = fun y z -> a:int { a + x == y + z }"
    in

    (* Test 900: cvr_defn 0 1 2 =?= cvr_defn 0 1 2 — identical *)
    let _ =
      compare_equality 900 (tc "cvr_defn 0 1 2") (tc "cvr_defn 0 1 2") BothTrivial
    in

    (* Test 901: cvr_defn 0 1 2 =?= a:int { a + 0 == 1 + 2 } — unfolded form *)
    let _ =
      compare_equality 901 (tc "cvr_defn 0 1 2") (tc "a:int { a + 0 == 1 + 2 }") BothTrivial
    in

    (* Helper: create env with a:nat, b:nat, c:nat for multi-arg tests *)
    let env_with_abc () : ML (Env.env & bv & bv & bv) =
      let env = tcenv () in
      let nat_t = tc "nat" in
      let a_bv = S.gen_bv "a" None nat_t in
      let env = Env.push_bv env a_bv in
      let b_bv = S.gen_bv "b" None nat_t in
      let env = Env.push_bv env b_bv in
      let c_bv = S.gen_bv "c" None nat_t in
      let env = Env.push_bv env c_bv in
      (env, a_bv, b_bv, c_bv)
    in
    let cvr_defn_head = tc "cvr_defn" in

    (* Test 902: with a:nat, b:nat, c:nat in env:
       cvr_defn a b c =?= cvr_defn a b c — reflexive *)
    let _ =
      let env, a_bv, b_bv, c_bv = env_with_abc () in
      let args = [(S.bv_to_name a_bv, None); (S.bv_to_name b_bv, None); (S.bv_to_name c_bv, None)] in
      let t0 = S.mk_Tm_app cvr_defn_head args FStarC.Range.dummyRange in
      compare_equality_env 902 env t0 t0 BothTrivial
    in

    (* Test 903: with a:nat, b:nat, c:nat in env:
       cvr_defn a b c <: cvr_defn a c b — swapped args
       Core will produce equational guard b == c && c == b;
       Rel should unfold and compare refinement formulas. *)
    let _ =
      let env, a_bv, b_bv, c_bv = env_with_abc () in
      let t0 = S.mk_Tm_app cvr_defn_head
        [(S.bv_to_name a_bv, None); (S.bv_to_name b_bv, None); (S.bv_to_name c_bv, None)]
        FStarC.Range.dummyRange in
      let t1 = S.mk_Tm_app cvr_defn_head
        [(S.bv_to_name a_bv, None); (S.bv_to_name c_bv, None); (S.bv_to_name b_bv, None)]
        FStarC.Range.dummyRange in
      compare_subtyping_env 903 env t0 t1 BothGuarded
    in

    (* ----------------------------------------------------------
       Group 10: Dependent tuple / dtuple2 types
       ---------------------------------------------------------- *)

    (* Test 1000: dtuple2 refinement subtyping *)
    let _ =
      let t0 = tc "dp:((dtuple2 int (fun (y:int) -> z:int{ z > y })) <: Type0) { let (| x, _ |) = dp in x > 17 }" in
      let t1 = tc "(dtuple2 int (fun (y:int) -> z:int{ z > y }))" in
      compare_subtyping 1000 t0 t1 BothTrivial
    in

    (* ----------------------------------------------------------
       Group 11: Ascription / type cast subtyping
       ---------------------------------------------------------- *)

    (* Test 1100: int <: refined nat with ascription *)
    let _ =
      let t0 = tc "int" in
      let t1 = tc "j:(i:nat{ i > 17 } <: Type0){j > 42}" in
      compare_subtyping 1100 t0 t1 BothGuarded
    in

    (* ----------------------------------------------------------
       Group 12: Record field projection types
       ---------------------------------------------------------- *)

    let _ = Pars.pars_and_tc_fragment
      "type cvr_vprop' = { cvr_t:Type0 ; cvr_n:nat }"
    in

    (* Test 1200: record field proj equality *)
    let _ =
      let t0 = tc "x:(({ cvr_t=bool; cvr_n=0 }).cvr_t <: Type0) { x == false }" in
      let t1 = tc "x:bool{ x == false }" in
      compare_equality 1200 t0 t1 BothTrivial
    in

    (* ----------------------------------------------------------
       Group 13: Arrow type equality
       ---------------------------------------------------------- *)

    (* Test 1300: (int -> bool) =?= (int -> bool) — trivial *)
    let _ =
      compare_equality 1300 (tc "int -> bool") (tc "int -> bool") BothTrivial
    in

    (* Test 1301: (nat -> bool) =?= (int -> bool) — different domains
       Rel can't prove arrow equality without SMT.
       Core produces a guard (which is also buggy — equates refinement
       formulas via injectivity: l_True == (i >= 0 == true)). *)
    let _ =
      compare_equality 1301 (tc "nat -> bool") (tc "int -> bool") RelFailCoreSucceed
    in

    (* Test 1302: with n:nat, i:nat in env:
       (cvr_natlt n -> bool) =?= (cvr_natlt i -> bool) (arrow equality with var args)
       Core will produce equational guard; Rel fails without SMT. *)
    let _ =
      let env, n_bv, i_bv = env_with_n_i () in
      let n_name = S.bv_to_name n_bv in
      let i_name = S.bv_to_name i_bv in
      let dom0 = S.mk_Tm_app cvr_natlt_head [(n_name, None)] FStarC.Range.dummyRange in
      let dom1 = S.mk_Tm_app cvr_natlt_head [(i_name, None)] FStarC.Range.dummyRange in
      let bool_t = tc "bool" in
      let b0 = S.mk_binder (S.gen_bv "_" None dom0) in
      let b1 = S.mk_binder (S.gen_bv "_" None dom1) in
      let t0 = U.arrow [b0] (S.mk_Total bool_t) in
      let t1 = U.arrow [b1] (S.mk_Total bool_t) in
      compare_equality_env 1302 env t0 t1 RelFailCoreSucceed
    in

    (* ----------------------------------------------------------
       Group 14: Full typechecker fragment tests (uses Rel, not Core)
       These verify the reported issue #4239 examples work in
       the full typechecker (which uses Rel for subtyping).
       ---------------------------------------------------------- *)

    (* Test 1400: Nested type abbreviation coercion *)
    tc_fragment_ok 1400
      "let cvr_nested_ok (n:nat) (x: cvr_ty0 n) : int = x";

    (* Test 1401: Arrow subtyping with type abbrev domains *)
    tc_fragment_ok 1401
      "let cvr_arrow_ok (n:nat) (x: cvr_natlt n -> bool) (i:nat{ i < n }) : cvr_natlt i -> bool = x";

    (* Test 1402: Nested type abbreviation with variable args — full checker *)
    tc_fragment_ok 1402
      "let cvr_ty1_sub (n:nat) (x: cvr_ty1 n) : cvr_ty0 n = x";

    (* Test 1403: cvr_natlt subtyping to nat — full checker *)
    tc_fragment_ok 1403
      "let cvr_natlt_to_nat (n:nat) (x: cvr_natlt n) : nat = x";

    (* Test 1404: Concrete arg abbreviation subtyping — full checker *)
    tc_fragment_ok 1404
      "let cvr_concrete_ok (x: cvr_natlt 5) : cvr_natlt 10 = x";

    (* ----------------------------------------------------------
       Group 15: Non-refinement type abbreviation applications
       These test the structural fallback (step 3 of compare_head_and_args):
       type abbreviations that expand to non-refinement types
       (e.g., function types, pairs) should succeed with arg-level
       guards when unfolding fails or produces complex terms.
       ---------------------------------------------------------- *)

    let _ = Pars.pars_and_tc_fragment
      "let cvr_nonref_arr (n:int) (m:int) : Type = (x:int{x > n}) -> (y:int{y > m})\n\
       let cvr_nonref_wrap (n:int) : Type = (x:int{x > n}) -> int"
    in

    let cvr_nonref_arr_head = tc "cvr_nonref_arr" in
    let cvr_nonref_wrap_head = tc "cvr_nonref_wrap" in

    (* Helper: create environment with a:int, b:int *)
    let env_with_ab_ints () : ML (Env.env & bv & bv) =
      let env = tcenv () in
      let int_t = tc "int" in
      let a_bv = S.gen_bv "a" None int_t in
      let env = Env.push_bv env a_bv in
      let b_bv = S.gen_bv "b" None int_t in
      let env = Env.push_bv env b_bv in
      (env, a_bv, b_bv)
    in

    (* Test 1500: cvr_nonref_arr 1 2 =?= cvr_nonref_arr 1 2 — identical *)
    let _ =
      compare_equality 1500 (tc "cvr_nonref_arr 1 2") (tc "cvr_nonref_arr 1 2") BothTrivial
    in

    (* Test 1501: with a:int, b:int in env:
       cvr_nonref_arr a b <: cvr_nonref_arr b a — swapped args.
       Not a refinement type (it's an arrow), so structural fallback should
       produce arg-level guards rather than failing. *)
    let _ =
      let env, a_bv, b_bv = env_with_ab_ints () in
      let a_name = S.bv_to_name a_bv in
      let b_name = S.bv_to_name b_bv in
      let t0 = S.mk_Tm_app cvr_nonref_arr_head [(a_name, None); (b_name, None)] FStarC.Range.dummyRange in
      let t1 = S.mk_Tm_app cvr_nonref_arr_head [(b_name, None); (a_name, None)] FStarC.Range.dummyRange in
      compare_subtyping_env 1501 env t0 t1 BothGuarded
    in

    (* Test 1502: with a:int, b:int in env:
       cvr_nonref_arr a b <: cvr_nonref_arr a b — reflexive, should be trivial *)
    let _ =
      let env, a_bv, b_bv = env_with_ab_ints () in
      let a_name = S.bv_to_name a_bv in
      let b_name = S.bv_to_name b_bv in
      let t0 = S.mk_Tm_app cvr_nonref_arr_head [(a_name, None); (b_name, None)] FStarC.Range.dummyRange in
      compare_subtyping_env 1502 env t0 t0 BothTrivial
    in

    (* Test 1503: with a:int in env:
       cvr_nonref_wrap a =?= cvr_nonref_wrap a — reflexive *)
    let _ =
      let env, a_bv, _b_bv = env_with_ab_ints () in
      let a_name = S.bv_to_name a_bv in
      let t0 = S.mk_Tm_app cvr_nonref_wrap_head [(a_name, None)] FStarC.Range.dummyRange in
      compare_equality_env 1503 env t0 t0 BothTrivial
    in

    (* Test 1504: with a:int, b:int in env:
       cvr_nonref_wrap a =?= cvr_nonref_wrap b — different args
       Should produce arg-level guard a == b via structural fallback. *)
    let _ =
      let env, a_bv, b_bv = env_with_ab_ints () in
      let a_name = S.bv_to_name a_bv in
      let b_name = S.bv_to_name b_bv in
      let t0 = S.mk_Tm_app cvr_nonref_wrap_head [(a_name, None)] FStarC.Range.dummyRange in
      let t1 = S.mk_Tm_app cvr_nonref_wrap_head [(b_name, None)] FStarC.Range.dummyRange in
      compare_equality_env 1504 env t0 t1 RelFailCoreSucceed
    in

    (* ----------------------------------------------------------
       Group 16: Non-refinement type abbreviation with constant args
       These test the third fallback in compare_head_and_args:
       when args are non-equatable constants (like 2, 3), structural
       comparison can't produce guards. The unfolded comparison with
       guards handles this by exposing equatable functions (like
       op_Equality) in the unfolded form.
       ---------------------------------------------------------- *)

    let _ = Pars.pars_and_tc_fragment
      "let cvr_const_app (m:nat) (n:nat) : Type = b:bool{ b == (m = n) }"
    in

    (* Test 1600: cvr_const_app 2 2 =?= cvr_const_app 2 2 — identical *)
    let _ =
      compare_equality 1600 (tc "cvr_const_app 2 2") (tc "cvr_const_app 2 2") BothTrivial
    in

    (* Test 1601: cvr_const_app 2 2 <: cvr_const_app 2 3 — different constant args.
       This is the Bug4256 pattern: args are constants (non-equatable),
       so the unfolded-with-guards fallback is needed. *)
    let _ =
      compare_subtyping 1601 (tc "cvr_const_app 2 2") (tc "cvr_const_app 2 3") BothGuarded
    in

    (* Test 1602: cvr_const_app 2 3 =?= cvr_const_app 2 3 — identical *)
    let _ =
      compare_equality 1602 (tc "cvr_const_app 2 3") (tc "cvr_const_app 2 3") BothTrivial
    in

    (* Test 1603: full checker integration — coercion between
       non-refinement type abbrevs with constant args should work *)
    tc_fragment_ok 1603
      "let cvr_const_ok (x: cvr_const_app 2 2) : cvr_const_app 2 2 = x";

    (* ----------------------------------------------------------
       Summary
       ---------------------------------------------------------- *)

    if !success
    then Format.print_string "Core vs Rel tests ok\n"
    else Format.print_string "Core vs Rel tests FAILED\n";
    !success
