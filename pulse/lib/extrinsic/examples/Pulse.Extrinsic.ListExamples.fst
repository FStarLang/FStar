module Pulse.Extrinsic.ListExamples

(** Allocate an exact finite list using the source-level list interface.
    build is a syntax generator: recursion is on the mathematical input list,
    producing a finite AST of allocations, not a host computation executed
    by the source semantics. let! names each freshly allocated tail pointer.
    build_correct follows that input induction, applying cons_correct and the
    source let rule. The postcondition retains every allocated node and states
    the exact contents; the concrete example builds [3;5;8]. *)

open Pulse.Extrinsic.HeapLang
open Pulse.Extrinsic.HeapLang.Notation
module H = PulseCore.Heap
module S = PulseCore.IndirectionTheorySep
module P = Pulse.Extrinsic.HeapLang.Proof
module R = Pulse.Extrinsic.Rules
module LL = Pulse.Extrinsic.HeapLang.List

let rec build (xs:list int) : Tot (expr [] TRef) (decreases xs) =
  match xs with
  | [] -> null
  | x :: tail ->
      let! head = build tail in
      node (int_ x) head

let rec build_correct (xs:list int)
  : Lemma (P.hoare S.emp (build xs) (LL.list_post xs)) (decreases xs)
  = match xs with
    | [] ->
        R.entails_fact S.emp (H.core_ref_null == H.core_ref_null);
        P.value_rule S.emp H.core_ref_null (LL.list_post [])
    | x :: tail ->
        build_correct tail;
        introduce forall next. P.hoare (LL.is_list next tail)
          (substitute next (NewNode (Val x) (Var Here))) (LL.list_post (x :: tail))
        with (
          LL.cons_correct x next tail;
          assert_norm (substitute #[] next (NewNode (Val x) (Var Here)) == NewNode (Val x) (Val next))
        );
        P.let_rule S.emp (build tail) (NewNode (Val x) (Var Here))
          (LL.list_post tail) (LL.list_post (x :: tail))

let program = build [3; 5; 8]
let program_correct ()
  : Lemma (P.hoare S.emp program (LL.list_post [3; 5; 8]))
  = build_correct [3; 5; 8]
