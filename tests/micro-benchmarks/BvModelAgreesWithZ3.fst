module BvModelAgreesWithZ3

// Width 2 is exhaustive; width 3 uses a small set of nontrivial values.

friend FStar.BV
friend FStar.Seq.Base

open FStar.List.Tot
open FStar.Tactics.V2

module BV = FStar.BV
module I = FStar.Int
module TU = FStar.Tactics.Util
module NS = FStar.NormSteps

let unsigned2 = [0; 1; 2; 3]
let signed2 = [-2; -1; 0; 1]
let nonzero2 = [1; 2; 3]
let unsigned3 = [3; 5]
let signed3 = [-3; 2]
let nonzero3 = [3; 5]

// Keep SMT operands symbolic while exposing their concrete values by refinement.
irreducible
let opaque_param (i:int) : Tot (r:int{r == i}) = i

let int_term (n:int) : Tac term =
  pack (Tv_Const (C_Int n (FStar.Sealed.seal Dec)))

let opaque_int_term (n:int) : Tac term =
  let n = int_term n in
  `(opaque_param (`#n))

let bv_term (width n:int) : Tac term =
  let negative = n < 0 in
  let n = int_term n in
  match width, negative with
  | 2, true -> `(BV.int2bv #2 (I.to_uint #2 (`#n)))
  | 2, false -> `(BV.int2bv #2 (`#n))
  | 3, true -> `(BV.int2bv #3 (I.to_uint #3 (`#n)))
  | 3, false -> `(BV.int2bv #3 (`#n))
  | _ -> fail "unsupported bit-vector width"

let opaque_bv_term (width n:int) : Tac term =
  let negative = n < 0 in
  let n = opaque_int_term n in
  match width, negative with
  | 2, true -> `(BV.int2bv #2 (I.to_uint #2 (`#n)))
  | 2, false -> `(BV.int2bv #2 (`#n))
  | 3, true -> `(BV.int2bv #3 (I.to_uint #3 (`#n)))
  | 3, false -> `(BV.int2bv #3 (`#n))
  | _ -> fail "unsupported bit-vector width"

let argument_name (n:int) : string =
  if n < 0 then "m" ^ string_of_int (-n) else string_of_int n

let model_normal_form (t:term) : Tac term =
  norm_term [NS.iota; NS.zeta_full; NS.primops; NS.unascribe] t

let bv_definitions =
  [`%FStar.BV.bv_uext; `%FStar.BV.bv_sext; `%FStar.BV.bv_repeat; `%FStar.BV.bv_concat;
   `%FStar.BV.bv_extract; `%FStar.BV.bvnot; `%FStar.BV.bvneg; `%FStar.BV.bvand; `%FStar.BV.bvor;
   `%FStar.BV.bvxor; `%FStar.BV.bvnand; `%FStar.BV.bvnor; `%FStar.BV.bvxnor; `%FStar.BV.bvcomp;
   `%FStar.BV.bvadd; `%FStar.BV.bvsub; `%FStar.BV.bvmul'; `%FStar.BV.bvmul; `%FStar.BV.bvshl;
   `%FStar.BV.bvshl'; `%FStar.BV.bvshr; `%FStar.BV.bvshr'; `%FStar.BV.bvashr; `%FStar.BV.bvrol;
   `%FStar.BV.bvrol'; `%FStar.BV.bvror; `%FStar.BV.bvror'; `%FStar.BV.bvdiv;
   `%FStar.BV.bvdiv_unsafe; `%FStar.BV.bvmod; `%FStar.BV.bvmod_unsafe; `%FStar.BV.bvsdiv;
   `%FStar.BV.bvsrem; `%FStar.BV.bvsmod; `%FStar.BV.bvult; `%FStar.BV.bvule; `%FStar.BV.bvugt;
   `%FStar.BV.bvuge; `%FStar.BV.bvslt; `%FStar.BV.bvsle; `%FStar.BV.bvsgt; `%FStar.BV.bvsge;
   `%FStar.BV.bvuaddo; `%FStar.BV.bvsaddo; `%FStar.BV.bvumulo; `%FStar.BV.bvsmulo;
   `%FStar.BV.bvusubo; `%FStar.BV.bvssubo; `%FStar.BV.bvsdivo; `%FStar.BV.bvnego;
   `%FStar.BV.int2bv; `%FStar.BV.bv2int; `%FStar.BV.sbv_to_int]

let unfolded_model_normal_form (t:term) : Tac term =
  // Unfold BV before enabling primops, then compute the exposed implementation.
  let unfolded =
    norm_term
      [NS.delta_only bv_definitions; NS.iota; NS.zeta_full; NS.unascribe]
      t
  in
  norm_term
    [NS.delta; NS.iota; NS.zeta_full; NS.primops; NS.unascribe]
    unfolded

let lemma_decl (name:string) (lhs rhs:term) : Tac sigelt =
  let typ = `(squash ((`#lhs) == (`#rhs))) in
  let lb = {
    lb_fv = pack_fv (cur_module () @ [name]);
    lb_us = [];
    lb_typ = typ;
    lb_def = `();
  } in
  pack_sigelt (Sg_Let {isrec=false; lbs=[lb]})

let unfolded_lemma_decl (name:string) (lhs model:term) : Tac sigelt =
  lemma_decl (name ^ "_unfolded") lhs (unfolded_model_normal_form model)

let vector_result (value:term) : Tac term = `(BV.bv2int (`#value))
let direct_result (value:term) : Tac term = value

let test_op1
  (values:list int)
  (argument opaque_argument:int -> Tac term)
  (project:term -> Tac term)
  (op:term)
  (prefix:string)
  : Tac decls =
  TU.concatMap
    (fun n ->
      let a = argument n in
      let opaque_a = opaque_argument n in
      let model = `((`#op) (`#a)) in
      let lhs = `((`#op) (`#opaque_a)) in
      let name = prefix ^ "_" ^ argument_name n in
      [lemma_decl name (project lhs) (model_normal_form (project model));
       unfolded_lemma_decl name (project lhs) (project model)])
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
      TU.concatMap
        (fun y ->
          let a = left_argument x in
          let b = right_argument y in
          let opaque_a = opaque_left_argument x in
          let opaque_b = opaque_right_argument y in
          let model = `((`#op) (`#a) (`#b)) in
          let lhs = `((`#op) (`#opaque_a) (`#opaque_b)) in
          let name =
            prefix ^ "_" ^ argument_name x ^ "_" ^ argument_name y
          in
          [lemma_decl name (project lhs) (model_normal_form (project model));
           unfolded_lemma_decl name (project lhs) (project model)])
        right_values)
    left_values

let test_bvop1 width values op =
  test_op1 values (bv_term width) (opaque_bv_term width) vector_result op
let test_bvop2 width left right op =
  test_op2 left right (bv_term width) (bv_term width)
    (opaque_bv_term width) (opaque_bv_term width) vector_result op
let test_bvresult1 width values op =
  test_op1 values (bv_term width) (opaque_bv_term width) direct_result op
let test_bvpred2 width left right op =
  test_op2 left right (bv_term width) (bv_term width)
    (opaque_bv_term width) (opaque_bv_term width) direct_result op
let test_intop1 values op =
  test_op1 values int_term opaque_int_term direct_result op
let test_bvnatop2 width vectors naturals op =
  test_op2 vectors naturals (bv_term width) int_term (opaque_bv_term width)
    opaque_int_term vector_result op

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

%splice[] (run_test "bvnot_2" (test_bvop1 2 unsigned2 (`(fun (a:BV.bv_t 2) -> BV.bvnot a))))
%splice[] (run_test "bvneg_2" (test_bvop1 2 unsigned2 (`(fun (a:BV.bv_t 2) -> BV.bvneg a))))
%splice[] (run_test "bvand_2" (test_bvop2 2 unsigned2 unsigned2 (`(fun (a b:BV.bv_t 2) -> BV.bvand a b))))
%splice[] (run_test "bvxor_2" (test_bvop2 2 unsigned2 unsigned2 (`(fun (a b:BV.bv_t 2) -> BV.bvxor a b))))
%splice[] (run_test "bvor_2" (test_bvop2 2 unsigned2 unsigned2 (`(fun (a b:BV.bv_t 2) -> BV.bvor a b))))
%splice[] (run_test "bvnand_2" (test_bvop2 2 unsigned2 unsigned2 (`(fun (a b:BV.bv_t 2) -> BV.bvnand a b))))
%splice[] (run_test "bvnor_2" (test_bvop2 2 unsigned2 unsigned2 (`(fun (a b:BV.bv_t 2) -> BV.bvnor a b))))
%splice[] (run_test "bvxnor_2" (test_bvop2 2 unsigned2 unsigned2 (`(fun (a b:BV.bv_t 2) -> BV.bvxnor a b))))
%splice[] (run_test "bvcomp_2" (test_bvop2 2 unsigned2 unsigned2 (`(fun (a b:BV.bv_t 2) -> BV.bvcomp a b))))
%splice[] (run_test "bvadd_2" (test_bvop2 2 unsigned2 unsigned2 (`(fun (a b:BV.bv_t 2) -> BV.bvadd a b))))
%splice[] (run_test "bvsub_2" (test_bvop2 2 unsigned2 unsigned2 (`(fun (a b:BV.bv_t 2) -> BV.bvsub a b))))
%splice[] (run_test "bvmul_vector_2" (test_bvop2 2 unsigned2 unsigned2 (`(fun (a b:BV.bv_t 2) -> BV.bvmul' a b))))
%splice[] (run_test "bvshl_vector_2" (test_bvop2 2 unsigned2 unsigned2 (`(fun (a b:BV.bv_t 2) -> BV.bvshl' a b))))
%splice[] (run_test "bvshr_vector_2" (test_bvop2 2 unsigned2 unsigned2 (`(fun (a b:BV.bv_t 2) -> BV.bvshr' a b))))
%splice[] (run_test "bvrol_vector_2" (test_bvop2 2 unsigned2 unsigned2 (`(fun (a b:BV.bv_t 2) -> BV.bvrol' a b))))
%splice[] (run_test "bvror_vector_2" (test_bvop2 2 unsigned2 unsigned2 (`(fun (a b:BV.bv_t 2) -> BV.bvror' a b))))
%splice[] (run_test "bvdiv_unsafe_2" (test_bvop2 2 unsigned2 unsigned2 (`(fun (a b:BV.bv_t 2) -> BV.bvdiv_unsafe a b))))
%splice[] (run_test "bvmod_unsafe_2" (test_bvop2 2 unsigned2 unsigned2 (`(fun (a b:BV.bv_t 2) -> BV.bvmod_unsafe a b))))
%splice[] (run_test "bvsdiv_2" (test_bvop2 2 signed2 signed2 (`(fun (a b:BV.bv_t 2) -> BV.bvsdiv a b))))
%splice[] (run_test "bvsrem_2" (test_bvop2 2 signed2 signed2 (`(fun (a b:BV.bv_t 2) -> BV.bvsrem a b))))
%splice[] (run_test "bvsmod_2" (test_bvop2 2 signed2 signed2 (`(fun (a b:BV.bv_t 2) -> BV.bvsmod a b))))
%splice[] (run_test "bvashr_2" (test_bvop2 2 signed2 unsigned2 (`(fun (a b:BV.bv_t 2) -> BV.bvashr a b))))
%splice[] (run_test "bvult_2" (test_bvpred2 2 unsigned2 unsigned2 (`(fun (a b:BV.bv_t 2) -> BV.bvult a b))))
%splice[] (run_test "bvule_2" (test_bvpred2 2 unsigned2 unsigned2 (`(fun (a b:BV.bv_t 2) -> BV.bvule a b))))
%splice[] (run_test "bvugt_2" (test_bvpred2 2 unsigned2 unsigned2 (`(fun (a b:BV.bv_t 2) -> BV.bvugt a b))))
%splice[] (run_test "bvuge_2" (test_bvpred2 2 unsigned2 unsigned2 (`(fun (a b:BV.bv_t 2) -> BV.bvuge a b))))
%splice[] (run_test "bvuaddo_2" (test_bvpred2 2 unsigned2 unsigned2 (`(fun (a b:BV.bv_t 2) -> BV.bvuaddo a b))))
%splice[] (run_test "bvumulo_2" (test_bvpred2 2 unsigned2 unsigned2 (`(fun (a b:BV.bv_t 2) -> BV.bvumulo a b))))
%splice[] (run_test "bvusubo_2" (test_bvpred2 2 unsigned2 unsigned2 (`(fun (a b:BV.bv_t 2) -> BV.bvusubo a b))))
%splice[] (run_test "bvslt_2" (test_bvpred2 2 signed2 signed2 (`(fun (a b:BV.bv_t 2) -> BV.bvslt a b))))
%splice[] (run_test "bvsle_2" (test_bvpred2 2 signed2 signed2 (`(fun (a b:BV.bv_t 2) -> BV.bvsle a b))))
%splice[] (run_test "bvsgt_2" (test_bvpred2 2 signed2 signed2 (`(fun (a b:BV.bv_t 2) -> BV.bvsgt a b))))
%splice[] (run_test "bvsge_2" (test_bvpred2 2 signed2 signed2 (`(fun (a b:BV.bv_t 2) -> BV.bvsge a b))))
%splice[] (run_test "bvsaddo_2" (test_bvpred2 2 signed2 signed2 (`(fun (a b:BV.bv_t 2) -> BV.bvsaddo a b))))
%splice[] (run_test "bvsmulo_2" (test_bvpred2 2 signed2 signed2 (`(fun (a b:BV.bv_t 2) -> BV.bvsmulo a b))))
%splice[] (run_test "bvssubo_2" (test_bvpred2 2 signed2 signed2 (`(fun (a b:BV.bv_t 2) -> BV.bvssubo a b))))
%splice[] (run_test "bvsdivo_2" (test_bvpred2 2 signed2 signed2 (`(fun (a b:BV.bv_t 2) -> BV.bvsdivo a b))))
%splice[] (run_test "bvnego_2" (test_bvresult1 2 signed2 (`(fun (a:BV.bv_t 2) -> BV.bvnego a))))
%splice[] (run_test "bvshl_natural_2" (test_bvnatop2 2 unsigned2 unsigned2 (`(fun (a:BV.bv_t 2) (n:nat) -> BV.bvshl a n))))
%splice[] (run_test "bvshr_natural_2" (test_bvnatop2 2 unsigned2 unsigned2 (`(fun (a:BV.bv_t 2) (n:nat) -> BV.bvshr a n))))
%splice[] (run_test "bvrol_natural_2" (test_bvnatop2 2 unsigned2 unsigned2 (`(fun (a:BV.bv_t 2) (n:nat) -> BV.bvrol a n))))
%splice[] (run_test "bvror_natural_2" (test_bvnatop2 2 unsigned2 unsigned2 (`(fun (a:BV.bv_t 2) (n:nat) -> BV.bvror a n))))
%splice[] (run_test "bvdiv_uint_2" (test_bvnatop2 2 unsigned2 nonzero2 (`(fun (a:BV.bv_t 2) (n:FStar.UInt.uint_t 2{b2t (n <> 0)}) -> BV.bvdiv a n))))
%splice[] (run_test "bvmod_uint_2" (test_bvnatop2 2 unsigned2 nonzero2 (`(fun (a:BV.bv_t 2) (n:FStar.UInt.uint_t 2{b2t (n <> 0)}) -> BV.bvmod a n))))
%splice[] (run_test "bvmul_uint_2" (test_bvnatop2 2 unsigned2 unsigned2 (`(fun (a:BV.bv_t 2) (n:FStar.UInt.uint_t 2) -> BV.bvmul a n))))
%splice[] (run_test "bv2int_2" (test_bvresult1 2 unsigned2 (`(fun (a:BV.bv_t 2) -> BV.bv2int a))))
%splice[] (run_test "int2bv_2" (test_intop1 unsigned2 (`(fun (n:FStar.UInt.uint_t 2) -> BV.bv2int #2 (BV.int2bv #2 n)))))
%splice[] (run_test "sbv_to_int_2" (test_bvresult1 2 signed2 (`(fun (a:BV.bv_t 2) -> BV.sbv_to_int a))))
%splice[] (run_test "bv_uext_1_2" (test_bvop1 2 unsigned2 (`(fun (a:BV.bv_t 2) -> BV.bv_uext #2 #1 a))))
%splice[] (run_test "bv_uext_2_2" (test_bvop1 2 unsigned2 (`(fun (a:BV.bv_t 2) -> BV.bv_uext #2 #2 a))))
%splice[] (run_test "bv_sext_1_2" (test_bvop1 2 unsigned2 (`(fun (a:BV.bv_t 2) -> BV.bv_sext #2 #1 a))))
%splice[] (run_test "bv_sext_2_2" (test_bvop1 2 unsigned2 (`(fun (a:BV.bv_t 2) -> BV.bv_sext #2 #2 a))))
%splice[] (run_test "bv_repeat_1_2" (test_bvop1 2 unsigned2 (`(fun (a:BV.bv_t 2) -> BV.bv_repeat #2 #1 a))))
%splice[] (run_test "bv_repeat_2_2" (test_bvop1 2 unsigned2 (`(fun (a:BV.bv_t 2) -> BV.bv_repeat #2 #2 a))))
%splice[] (run_test "bv_concat_2" (test_bvop2 2 unsigned2 unsigned2 (`(fun (a b:BV.bv_t 2) -> BV.bv_concat #2 #2 a b))))
%splice[] (run_test "bv_extract_0_0_2" (test_bvop1 2 unsigned2 (`(fun (a:BV.bv_t 2) -> BV.bv_extract #2 a 0 0))))
%splice[] (run_test "bv_extract_1_0_2" (test_bvop1 2 unsigned2 (`(fun (a:BV.bv_t 2) -> BV.bv_extract #2 a 1 0))))
%splice[] (run_test "bv_extract_1_1_2" (test_bvop1 2 unsigned2 (`(fun (a:BV.bv_t 2) -> BV.bv_extract #2 a 1 1))))

%splice[] (run_test "bvnot_3" (test_bvop1 3 unsigned3 (`(fun (a:BV.bv_t 3) -> BV.bvnot a))))
%splice[] (run_test "bvneg_3" (test_bvop1 3 unsigned3 (`(fun (a:BV.bv_t 3) -> BV.bvneg a))))
%splice[] (run_test "bvand_3" (test_bvop2 3 unsigned3 unsigned3 (`(fun (a b:BV.bv_t 3) -> BV.bvand a b))))
%splice[] (run_test "bvxor_3" (test_bvop2 3 unsigned3 unsigned3 (`(fun (a b:BV.bv_t 3) -> BV.bvxor a b))))
%splice[] (run_test "bvor_3" (test_bvop2 3 unsigned3 unsigned3 (`(fun (a b:BV.bv_t 3) -> BV.bvor a b))))
%splice[] (run_test "bvnand_3" (test_bvop2 3 unsigned3 unsigned3 (`(fun (a b:BV.bv_t 3) -> BV.bvnand a b))))
%splice[] (run_test "bvnor_3" (test_bvop2 3 unsigned3 unsigned3 (`(fun (a b:BV.bv_t 3) -> BV.bvnor a b))))
%splice[] (run_test "bvxnor_3" (test_bvop2 3 unsigned3 unsigned3 (`(fun (a b:BV.bv_t 3) -> BV.bvxnor a b))))
%splice[] (run_test "bvcomp_3" (test_bvop2 3 unsigned3 unsigned3 (`(fun (a b:BV.bv_t 3) -> BV.bvcomp a b))))
%splice[] (run_test "bvadd_3" (test_bvop2 3 unsigned3 unsigned3 (`(fun (a b:BV.bv_t 3) -> BV.bvadd a b))))
%splice[] (run_test "bvsub_3" (test_bvop2 3 unsigned3 unsigned3 (`(fun (a b:BV.bv_t 3) -> BV.bvsub a b))))
%splice[] (run_test "bvmul_vector_3" (test_bvop2 3 unsigned3 unsigned3 (`(fun (a b:BV.bv_t 3) -> BV.bvmul' a b))))
%splice[] (run_test "bvshl_vector_3" (test_bvop2 3 unsigned3 unsigned3 (`(fun (a b:BV.bv_t 3) -> BV.bvshl' a b))))
%splice[] (run_test "bvshr_vector_3" (test_bvop2 3 unsigned3 unsigned3 (`(fun (a b:BV.bv_t 3) -> BV.bvshr' a b))))
%splice[] (run_test "bvrol_vector_3" (test_bvop2 3 unsigned3 unsigned3 (`(fun (a b:BV.bv_t 3) -> BV.bvrol' a b))))
%splice[] (run_test "bvror_vector_3" (test_bvop2 3 unsigned3 unsigned3 (`(fun (a b:BV.bv_t 3) -> BV.bvror' a b))))
%splice[] (run_test "bvdiv_unsafe_3" (test_bvop2 3 unsigned3 unsigned3 (`(fun (a b:BV.bv_t 3) -> BV.bvdiv_unsafe a b))))
%splice[] (run_test "bvmod_unsafe_3" (test_bvop2 3 unsigned3 unsigned3 (`(fun (a b:BV.bv_t 3) -> BV.bvmod_unsafe a b))))
%splice[] (run_test "bvsdiv_3" (test_bvop2 3 signed3 signed3 (`(fun (a b:BV.bv_t 3) -> BV.bvsdiv a b))))
%splice[] (run_test "bvsrem_3" (test_bvop2 3 signed3 signed3 (`(fun (a b:BV.bv_t 3) -> BV.bvsrem a b))))
%splice[] (run_test "bvsmod_3" (test_bvop2 3 signed3 signed3 (`(fun (a b:BV.bv_t 3) -> BV.bvsmod a b))))
%splice[] (run_test "bvashr_3" (test_bvop2 3 signed3 unsigned3 (`(fun (a b:BV.bv_t 3) -> BV.bvashr a b))))
%splice[] (run_test "bvult_3" (test_bvpred2 3 unsigned3 unsigned3 (`(fun (a b:BV.bv_t 3) -> BV.bvult a b))))
%splice[] (run_test "bvule_3" (test_bvpred2 3 unsigned3 unsigned3 (`(fun (a b:BV.bv_t 3) -> BV.bvule a b))))
%splice[] (run_test "bvugt_3" (test_bvpred2 3 unsigned3 unsigned3 (`(fun (a b:BV.bv_t 3) -> BV.bvugt a b))))
%splice[] (run_test "bvuge_3" (test_bvpred2 3 unsigned3 unsigned3 (`(fun (a b:BV.bv_t 3) -> BV.bvuge a b))))
%splice[] (run_test "bvuaddo_3" (test_bvpred2 3 unsigned3 unsigned3 (`(fun (a b:BV.bv_t 3) -> BV.bvuaddo a b))))
%splice[] (run_test "bvumulo_3" (test_bvpred2 3 unsigned3 unsigned3 (`(fun (a b:BV.bv_t 3) -> BV.bvumulo a b))))
%splice[] (run_test "bvusubo_3" (test_bvpred2 3 unsigned3 unsigned3 (`(fun (a b:BV.bv_t 3) -> BV.bvusubo a b))))
%splice[] (run_test "bvslt_3" (test_bvpred2 3 signed3 signed3 (`(fun (a b:BV.bv_t 3) -> BV.bvslt a b))))
%splice[] (run_test "bvsle_3" (test_bvpred2 3 signed3 signed3 (`(fun (a b:BV.bv_t 3) -> BV.bvsle a b))))
%splice[] (run_test "bvsgt_3" (test_bvpred2 3 signed3 signed3 (`(fun (a b:BV.bv_t 3) -> BV.bvsgt a b))))
%splice[] (run_test "bvsge_3" (test_bvpred2 3 signed3 signed3 (`(fun (a b:BV.bv_t 3) -> BV.bvsge a b))))
%splice[] (run_test "bvsaddo_3" (test_bvpred2 3 signed3 signed3 (`(fun (a b:BV.bv_t 3) -> BV.bvsaddo a b))))
%splice[] (run_test "bvsmulo_3" (test_bvpred2 3 signed3 signed3 (`(fun (a b:BV.bv_t 3) -> BV.bvsmulo a b))))
%splice[] (run_test "bvssubo_3" (test_bvpred2 3 signed3 signed3 (`(fun (a b:BV.bv_t 3) -> BV.bvssubo a b))))
%splice[] (run_test "bvsdivo_3" (test_bvpred2 3 signed3 signed3 (`(fun (a b:BV.bv_t 3) -> BV.bvsdivo a b))))
%splice[] (run_test "bvnego_3" (test_bvresult1 3 signed3 (`(fun (a:BV.bv_t 3) -> BV.bvnego a))))
%splice[] (run_test "bvshl_natural_3" (test_bvnatop2 3 unsigned3 unsigned3 (`(fun (a:BV.bv_t 3) (n:nat) -> BV.bvshl a n))))
%splice[] (run_test "bvshr_natural_3" (test_bvnatop2 3 unsigned3 unsigned3 (`(fun (a:BV.bv_t 3) (n:nat) -> BV.bvshr a n))))
%splice[] (run_test "bvrol_natural_3" (test_bvnatop2 3 unsigned3 unsigned3 (`(fun (a:BV.bv_t 3) (n:nat) -> BV.bvrol a n))))
%splice[] (run_test "bvror_natural_3" (test_bvnatop2 3 unsigned3 unsigned3 (`(fun (a:BV.bv_t 3) (n:nat) -> BV.bvror a n))))
%splice[] (run_test "bvdiv_uint_3" (test_bvnatop2 3 unsigned3 nonzero3 (`(fun (a:BV.bv_t 3) (n:FStar.UInt.uint_t 3{b2t (n <> 0)}) -> BV.bvdiv a n))))
%splice[] (run_test "bvmod_uint_3" (test_bvnatop2 3 unsigned3 nonzero3 (`(fun (a:BV.bv_t 3) (n:FStar.UInt.uint_t 3{b2t (n <> 0)}) -> BV.bvmod a n))))
%splice[] (run_test "bvmul_uint_3" (test_bvnatop2 3 unsigned3 unsigned3 (`(fun (a:BV.bv_t 3) (n:FStar.UInt.uint_t 3) -> BV.bvmul a n))))
%splice[] (run_test "bv2int_3" (test_bvresult1 3 unsigned3 (`(fun (a:BV.bv_t 3) -> BV.bv2int a))))
%splice[] (run_test "int2bv_3" (test_intop1 unsigned3 (`(fun (n:FStar.UInt.uint_t 3) -> BV.bv2int #3 (BV.int2bv #3 n)))))
%splice[] (run_test "sbv_to_int_3" (test_bvresult1 3 signed3 (`(fun (a:BV.bv_t 3) -> BV.sbv_to_int a))))
%splice[] (run_test "bv_uext_1_3" (test_bvop1 3 unsigned3 (`(fun (a:BV.bv_t 3) -> BV.bv_uext #3 #1 a))))
%splice[] (run_test "bv_uext_2_3" (test_bvop1 3 unsigned3 (`(fun (a:BV.bv_t 3) -> BV.bv_uext #3 #2 a))))
%splice[] (run_test "bv_uext_3_3" (test_bvop1 3 unsigned3 (`(fun (a:BV.bv_t 3) -> BV.bv_uext #3 #3 a))))
%splice[] (run_test "bv_sext_1_3" (test_bvop1 3 unsigned3 (`(fun (a:BV.bv_t 3) -> BV.bv_sext #3 #1 a))))
%splice[] (run_test "bv_sext_2_3" (test_bvop1 3 unsigned3 (`(fun (a:BV.bv_t 3) -> BV.bv_sext #3 #2 a))))
%splice[] (run_test "bv_sext_3_3" (test_bvop1 3 unsigned3 (`(fun (a:BV.bv_t 3) -> BV.bv_sext #3 #3 a))))
%splice[] (run_test "bv_repeat_1_3" (test_bvop1 3 unsigned3 (`(fun (a:BV.bv_t 3) -> BV.bv_repeat #3 #1 a))))
%splice[] (run_test "bv_repeat_2_3" (test_bvop1 3 unsigned3 (`(fun (a:BV.bv_t 3) -> BV.bv_repeat #3 #2 a))))
%splice[] (run_test "bv_repeat_3_3" (test_bvop1 3 unsigned3 (`(fun (a:BV.bv_t 3) -> BV.bv_repeat #3 #3 a))))
%splice[] (run_test "bv_concat_3" (test_bvop2 3 unsigned3 unsigned3 (`(fun (a b:BV.bv_t 3) -> BV.bv_concat #3 #3 a b))))
%splice[] (run_test "bv_extract_0_0_3" (test_bvop1 3 unsigned3 (`(fun (a:BV.bv_t 3) -> BV.bv_extract #3 a 0 0))))
%splice[] (run_test "bv_extract_1_0_3" (test_bvop1 3 unsigned3 (`(fun (a:BV.bv_t 3) -> BV.bv_extract #3 a 1 0))))
%splice[] (run_test "bv_extract_1_1_3" (test_bvop1 3 unsigned3 (`(fun (a:BV.bv_t 3) -> BV.bv_extract #3 a 1 1))))
%splice[] (run_test "bv_extract_2_0_3" (test_bvop1 3 unsigned3 (`(fun (a:BV.bv_t 3) -> BV.bv_extract #3 a 2 0))))
%splice[] (run_test "bv_extract_2_1_3" (test_bvop1 3 unsigned3 (`(fun (a:BV.bv_t 3) -> BV.bv_extract #3 a 2 1))))
%splice[] (run_test "bv_extract_2_2_3" (test_bvop1 3 unsigned3 (`(fun (a:BV.bv_t 3) -> BV.bv_extract #3 a 2 2))))
