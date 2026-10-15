module BvModelAgreesWithZ3

// Exhaustive width-3 cases keep the Cartesian operation groups tractable.

open FStar.List.Tot
open FStar.Tactics.V2

module BV = FStar.BV
module I = FStar.Int
module TU = FStar.Tactics.Util
module NS = FStar.NormSteps

let unsigned3 = [0; 1; 2; 3; 4; 5; 6; 7]
let signed3 = [-4; -3; -2; -1; 0; 1; 2; 3]
let nonzero3 = [1; 2; 3; 4; 5; 6; 7]

// Keep SMT operands symbolic while exposing their concrete values by refinement.
irreducible
let opaque_param (i:int) : Tot (r:int{r == i}) = i

let int_term (n:int) : Tac term =
  pack (Tv_Const (C_Int n (FStar.Sealed.seal Dec)))

let opaque_int_term (n:int) : Tac term =
  let n = int_term n in
  `(opaque_param (`#n))

let bv_term (n:int) : Tac term =
  if n < 0
  then
    let n = int_term n in
    `(BV.int2bv #3 (I.to_uint #3 (`#n)))
  else
    let n = int_term n in
    `(BV.int2bv #3 (`#n))

let opaque_bv_term (n:int) : Tac term =
  if n < 0
  then
    let n = opaque_int_term n in
    `(BV.int2bv #3 (I.to_uint #3 (`#n)))
  else
    let n = opaque_int_term n in
    `(BV.int2bv #3 (`#n))

let argument_name (n:int) : string =
  if n < 0 then "m" ^ string_of_int (-n) else string_of_int n

let model_normal_form (t:term) : Tac term =
  norm_term [NS.delta; NS.iota; NS.zeta_full; NS.primops; NS.unascribe] t

let lemma_decl (name:string) (lhs model:term) : Tac sigelt =
  let rhs = model_normal_form model in
  let typ = `(squash ((`#lhs) == (`#rhs))) in
  let lb = {
    lb_fv = pack_fv (cur_module () @ [name]);
    lb_us = [];
    lb_typ = typ;
    lb_def = `();
  } in
  pack_sigelt (Sg_Let {isrec=false; lbs=[lb]})

let vector_result (value:term) : Tac term = `(BV.bv2int (`#value))
let direct_result (value:term) : Tac term = value

let test_op1
  (values:list int)
  (argument opaque_argument:int -> Tac term)
  (project:term -> Tac term)
  (op:term)
  (prefix:string)
  : Tac decls =
  TU.map
    (fun n ->
      let a = argument n in
      let opaque_a = opaque_argument n in
      let model = `((`#op) (`#a)) in
      let lhs = `((`#op) (`#opaque_a)) in
      lemma_decl
        (prefix ^ "_" ^ argument_name n)
        (project lhs)
        (project model))
    values

let test_op2
  (left_values right_values:list int)
  (left_argument right_argument:int -> Tac term)
  (opaque_left_argument opaque_right_argument:int -> Tac term)
  (project:term -> Tac term)
  (op:term)
  (prefix:string)
  : Tac decls =
  TU.concatMap
    (fun x ->
      TU.map
        (fun y ->
          let a = left_argument x in
          let b = right_argument y in
          let opaque_a = opaque_left_argument x in
          let opaque_b = opaque_right_argument y in
          let model = `((`#op) (`#a) (`#b)) in
          let lhs = `((`#op) (`#opaque_a) (`#opaque_b)) in
          lemma_decl
            (prefix ^ "_" ^ argument_name x ^ "_" ^ argument_name y)
            (project lhs)
            (project model))
        right_values)
    left_values

let test_bvop1 values op =
  test_op1 values bv_term opaque_bv_term vector_result op
let test_bvop2 left right op =
  test_op2 left right bv_term bv_term opaque_bv_term opaque_bv_term
    vector_result op
let test_bvresult1 values op =
  test_op1 values bv_term opaque_bv_term direct_result op
let test_bvpred2 left right op =
  test_op2 left right bv_term bv_term opaque_bv_term opaque_bv_term
    direct_result op
let test_intop1 values op =
  test_op1 values int_term opaque_int_term direct_result op
let test_bvnatop2 vectors naturals op =
  test_op2 vectors naturals bv_term int_term opaque_bv_term opaque_int_term
    vector_result op

let run_test (prefix:string) (test:string -> Tac decls) : Tac decls =
  test prefix

let check_nbe () : Tac unit =
  norm [NS.nbe; NS.primops];
  match term_as_formula (cur_goal ()) with
  | Comp (Eq _) left right ->
    if term_eq left right then trefl () else fail "not syntactically equal"
  | _ -> fail "unexpected goal"

let _ = assert
  (BV.bv2int (BV.bv_extract #4
    (BV.bvadd (BV.int2bv #4 7) (BV.int2bv #4 6)) 2 1) == 2)
  by (check_nbe ())

%splice[] (run_test "bvnot_3" (test_bvop1 unsigned3 (`(fun (a:BV.bv_t 3) -> BV.bvnot a))))
%splice[] (run_test "bvneg_3" (test_bvop1 unsigned3 (`(fun (a:BV.bv_t 3) -> BV.bvneg a))))
%splice[] (run_test "bvand_3" (test_bvop2 unsigned3 unsigned3 (`(fun (a b:BV.bv_t 3) -> BV.bvand a b))))
%splice[] (run_test "bvxor_3" (test_bvop2 unsigned3 unsigned3 (`(fun (a b:BV.bv_t 3) -> BV.bvxor a b))))
%splice[] (run_test "bvor_3" (test_bvop2 unsigned3 unsigned3 (`(fun (a b:BV.bv_t 3) -> BV.bvor a b))))
%splice[] (run_test "bvnand_3" (test_bvop2 unsigned3 unsigned3 (`(fun (a b:BV.bv_t 3) -> BV.bvnand a b))))
%splice[] (run_test "bvnor_3" (test_bvop2 unsigned3 unsigned3 (`(fun (a b:BV.bv_t 3) -> BV.bvnor a b))))
%splice[] (run_test "bvxnor_3" (test_bvop2 unsigned3 unsigned3 (`(fun (a b:BV.bv_t 3) -> BV.bvxnor a b))))
%splice[] (run_test "bvcomp_3" (test_bvop2 unsigned3 unsigned3 (`(fun (a b:BV.bv_t 3) -> BV.bvcomp a b))))
%splice[] (run_test "bvadd_3" (test_bvop2 unsigned3 unsigned3 (`(fun (a b:BV.bv_t 3) -> BV.bvadd a b))))
%splice[] (run_test "bvsub_3" (test_bvop2 unsigned3 unsigned3 (`(fun (a b:BV.bv_t 3) -> BV.bvsub a b))))
%splice[] (run_test "bvmul_vector_3" (test_bvop2 unsigned3 unsigned3 (`(fun (a b:BV.bv_t 3) -> BV.bvmul' a b))))
%splice[] (run_test "bvshl_vector_3" (test_bvop2 unsigned3 unsigned3 (`(fun (a b:BV.bv_t 3) -> BV.bvshl' a b))))
%splice[] (run_test "bvshr_vector_3" (test_bvop2 unsigned3 unsigned3 (`(fun (a b:BV.bv_t 3) -> BV.bvshr' a b))))
%splice[] (run_test "bvrol_vector_3" (test_bvop2 unsigned3 unsigned3 (`(fun (a b:BV.bv_t 3) -> BV.bvrol' a b))))
%splice[] (run_test "bvror_vector_3" (test_bvop2 unsigned3 unsigned3 (`(fun (a b:BV.bv_t 3) -> BV.bvror' a b))))
%splice[] (run_test "bvdiv_unsafe_3" (test_bvop2 unsigned3 unsigned3 (`(fun (a b:BV.bv_t 3) -> BV.bvdiv_unsafe a b))))
%splice[] (run_test "bvmod_unsafe_3" (test_bvop2 unsigned3 unsigned3 (`(fun (a b:BV.bv_t 3) -> BV.bvmod_unsafe a b))))
%splice[] (run_test "bvsdiv_3" (test_bvop2 signed3 signed3 (`(fun (a b:BV.bv_t 3) -> BV.bvsdiv a b))))
%splice[] (run_test "bvsrem_3" (test_bvop2 signed3 signed3 (`(fun (a b:BV.bv_t 3) -> BV.bvsrem a b))))
%splice[] (run_test "bvsmod_3" (test_bvop2 signed3 signed3 (`(fun (a b:BV.bv_t 3) -> BV.bvsmod a b))))
%splice[] (run_test "bvashr_3" (test_bvop2 signed3 unsigned3 (`(fun (a b:BV.bv_t 3) -> BV.bvashr a b))))
%splice[] (run_test "bvult_3" (test_bvpred2 unsigned3 unsigned3 (`(fun (a b:BV.bv_t 3) -> BV.bvult a b))))
%splice[] (run_test "bvule_3" (test_bvpred2 unsigned3 unsigned3 (`(fun (a b:BV.bv_t 3) -> BV.bvule a b))))
%splice[] (run_test "bvugt_3" (test_bvpred2 unsigned3 unsigned3 (`(fun (a b:BV.bv_t 3) -> BV.bvugt a b))))
%splice[] (run_test "bvuge_3" (test_bvpred2 unsigned3 unsigned3 (`(fun (a b:BV.bv_t 3) -> BV.bvuge a b))))
%splice[] (run_test "bvuaddo_3" (test_bvpred2 unsigned3 unsigned3 (`(fun (a b:BV.bv_t 3) -> BV.bvuaddo a b))))
%splice[] (run_test "bvumulo_3" (test_bvpred2 unsigned3 unsigned3 (`(fun (a b:BV.bv_t 3) -> BV.bvumulo a b))))
%splice[] (run_test "bvusubo_3" (test_bvpred2 unsigned3 unsigned3 (`(fun (a b:BV.bv_t 3) -> BV.bvusubo a b))))
%splice[] (run_test "bvslt_3" (test_bvpred2 signed3 signed3 (`(fun (a b:BV.bv_t 3) -> BV.bvslt a b))))
%splice[] (run_test "bvsle_3" (test_bvpred2 signed3 signed3 (`(fun (a b:BV.bv_t 3) -> BV.bvsle a b))))
%splice[] (run_test "bvsgt_3" (test_bvpred2 signed3 signed3 (`(fun (a b:BV.bv_t 3) -> BV.bvsgt a b))))
%splice[] (run_test "bvsge_3" (test_bvpred2 signed3 signed3 (`(fun (a b:BV.bv_t 3) -> BV.bvsge a b))))
%splice[] (run_test "bvsaddo_3" (test_bvpred2 signed3 signed3 (`(fun (a b:BV.bv_t 3) -> BV.bvsaddo a b))))
%splice[] (run_test "bvsmulo_3" (test_bvpred2 signed3 signed3 (`(fun (a b:BV.bv_t 3) -> BV.bvsmulo a b))))
%splice[] (run_test "bvssubo_3" (test_bvpred2 signed3 signed3 (`(fun (a b:BV.bv_t 3) -> BV.bvssubo a b))))
%splice[] (run_test "bvsdivo_3" (test_bvpred2 signed3 signed3 (`(fun (a b:BV.bv_t 3) -> BV.bvsdivo a b))))
%splice[] (run_test "bvnego_3" (test_bvresult1 signed3 (`(fun (a:BV.bv_t 3) -> BV.bvnego a))))
%splice[] (run_test "bvshl_natural_3" (test_bvnatop2 unsigned3 unsigned3 (`(fun (a:BV.bv_t 3) (n:nat) -> BV.bvshl a n))))
%splice[] (run_test "bvshr_natural_3" (test_bvnatop2 unsigned3 unsigned3 (`(fun (a:BV.bv_t 3) (n:nat) -> BV.bvshr a n))))
%splice[] (run_test "bvrol_natural_3" (test_bvnatop2 unsigned3 unsigned3 (`(fun (a:BV.bv_t 3) (n:nat) -> BV.bvrol a n))))
%splice[] (run_test "bvror_natural_3" (test_bvnatop2 unsigned3 unsigned3 (`(fun (a:BV.bv_t 3) (n:nat) -> BV.bvror a n))))
%splice[] (run_test "bvdiv_uint_3" (test_bvnatop2 unsigned3 nonzero3 (`(fun (a:BV.bv_t 3) (n:FStar.UInt.uint_t 3{b2t (n <> 0)}) -> BV.bvdiv a n))))
%splice[] (run_test "bvmod_uint_3" (test_bvnatop2 unsigned3 nonzero3 (`(fun (a:BV.bv_t 3) (n:FStar.UInt.uint_t 3{b2t (n <> 0)}) -> BV.bvmod a n))))
%splice[] (run_test "bvmul_uint_3" (test_bvnatop2 unsigned3 unsigned3 (`(fun (a:BV.bv_t 3) (n:FStar.UInt.uint_t 3) -> BV.bvmul a n))))
%splice[] (run_test "bv2int_3" (test_bvresult1 unsigned3 (`(fun (a:BV.bv_t 3) -> BV.bv2int a))))
%splice[] (run_test "int2bv_3" (test_intop1 unsigned3 (`(fun (n:FStar.UInt.uint_t 3) -> BV.bv2int #3 (BV.int2bv #3 n)))))
%splice[] (run_test "sbv_to_int_3" (test_bvresult1 signed3 (`(fun (a:BV.bv_t 3) -> BV.sbv_to_int a))))
%splice[] (run_test "bv_uext_1_3" (test_bvop1 unsigned3 (`(fun (a:BV.bv_t 3) -> BV.bv_uext #3 #1 a))))
%splice[] (run_test "bv_uext_2_3" (test_bvop1 unsigned3 (`(fun (a:BV.bv_t 3) -> BV.bv_uext #3 #2 a))))
%splice[] (run_test "bv_uext_3_3" (test_bvop1 unsigned3 (`(fun (a:BV.bv_t 3) -> BV.bv_uext #3 #3 a))))
%splice[] (run_test "bv_sext_1_3" (test_bvop1 unsigned3 (`(fun (a:BV.bv_t 3) -> BV.bv_sext #3 #1 a))))
%splice[] (run_test "bv_sext_2_3" (test_bvop1 unsigned3 (`(fun (a:BV.bv_t 3) -> BV.bv_sext #3 #2 a))))
%splice[] (run_test "bv_sext_3_3" (test_bvop1 unsigned3 (`(fun (a:BV.bv_t 3) -> BV.bv_sext #3 #3 a))))
%splice[] (run_test "bv_repeat_1_3" (test_bvop1 unsigned3 (`(fun (a:BV.bv_t 3) -> BV.bv_repeat #3 #1 a))))
%splice[] (run_test "bv_repeat_2_3" (test_bvop1 unsigned3 (`(fun (a:BV.bv_t 3) -> BV.bv_repeat #3 #2 a))))
%splice[] (run_test "bv_repeat_3_3" (test_bvop1 unsigned3 (`(fun (a:BV.bv_t 3) -> BV.bv_repeat #3 #3 a))))
%splice[] (run_test "bv_concat_3" (test_bvop2 unsigned3 unsigned3 (`(fun (a b:BV.bv_t 3) -> BV.bv_concat #3 #3 a b))))
%splice[] (run_test "bv_extract_0_0_3" (test_bvop1 unsigned3 (`(fun (a:BV.bv_t 3) -> BV.bv_extract #3 a 0 0))))
%splice[] (run_test "bv_extract_1_0_3" (test_bvop1 unsigned3 (`(fun (a:BV.bv_t 3) -> BV.bv_extract #3 a 1 0))))
%splice[] (run_test "bv_extract_1_1_3" (test_bvop1 unsigned3 (`(fun (a:BV.bv_t 3) -> BV.bv_extract #3 a 1 1))))
%splice[] (run_test "bv_extract_2_0_3" (test_bvop1 unsigned3 (`(fun (a:BV.bv_t 3) -> BV.bv_extract #3 a 2 0))))
%splice[] (run_test "bv_extract_2_1_3" (test_bvop1 unsigned3 (`(fun (a:BV.bv_t 3) -> BV.bv_extract #3 a 2 1))))
%splice[] (run_test "bv_extract_2_2_3" (test_bvop1 unsigned3 (`(fun (a:BV.bv_t 3) -> BV.bv_extract #3 a 2 2))))
