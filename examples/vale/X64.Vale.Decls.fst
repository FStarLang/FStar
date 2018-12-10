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
module X64.Vale.Decls
open X64.Machine_s
open X64.Vale
open X64.Vale.State_i
open X64.Vale.StateLemmas_i
open FStar.UInt
module S = X64.Semantics_s
module P = X64.Print_s

#reset-options "--z3cliopt smt.arith.nl=true --using_facts_from Prims --using_facts_from FStar.Math"
let lemma_mul_nat (x:nat) (y:nat) : Lemma (ensures 0 <= (x `op_Multiply` y)) = ()
#reset-options "--initial_fuel 2 --max_fuel 2"

let cf = Lemmas_i.cf
let ins = S.ins
type ocmp = S.ocmp

let va_cmp_eq o1 o2 = S.OEq o1 o2
let va_cmp_ne o1 o2 = S.ONe o1 o2
let va_cmp_le o1 o2 = S.OLe o1 o2
let va_cmp_ge o1 o2 = S.OGe o1 o2
let va_cmp_lt o1 o2 = S.OLt o1 o2
let va_cmp_gt o1 o2 = S.OGt o1 o2

let eval_code = Lemmas_i.eval_code
let eval_while = Lemmas_i.eval_while
let eval_ocmp = Lemmas_i.eval_ocmp

let lemma_cmp_eq s o1 o2 = ()
let lemma_cmp_ne s o1 o2 = ()
let lemma_cmp_le s o1 o2 = ()
let lemma_cmp_ge s o1 o2 = ()
let lemma_cmp_lt s o1 o2 = ()
let lemma_cmp_gt s o1 o2 = ()

let va_lemma_block = Lemmas_i.lemma_block
let va_lemma_empty = Lemmas_i.lemma_empty
let va_lemma_ifElse = Lemmas_i.lemma_ifElse
let va_lemma_while = Lemmas_i.lemma_while
let va_lemma_whileTrue = Lemmas_i.lemma_whileTrue
let va_lemma_whileFalse = Lemmas_i.lemma_whileFalse

let logxor64 (x:nat64) (y:nat64) : nat64 =
  S.logxor x y

let logand64 (x:nat64) (y:nat64) : nat64 =
  S.logand x y

let logand128 (x:nat128) (y:nat128) : nat128 =
  FStar.UInt.logand #128 x y
(*
  if FStar.UInt.fits x 64
  && FStar.UInt.fits y 64
  then FStar.UInt.logand #64 x y
  else 0
*)

let shift_left64 (x:nat64) (amt:nat64) : nat64 =
  S.shift_left x amt

let shift_right64 (x:nat64) (amt:nat64) : nat64 =
  S.shift_right x amt

let reveal_logand128 (x y:nat128) = ()

let printer = P.printer
let print_string = FStar.IO.print_string
let print_header = P.print_header
let print_proc = P.print_proc
let print_footer = P.print_footer
let masm = P.masm
let gcc = P.gcc

#set-options "--initial_fuel 2 --max_fuel 2 --z3rlimit 20"

val va_transparent_code_Mov64 : dst:va_dst_operand -> src:va_operand -> Tot va_code
let va_transparent_code_Mov64 dst src =
  (Ins (S.Mov64 dst src))
let va_code_Mov64 dst src =
  (va_make_opaque (va_transparent_code_Mov64 dst src))

irreducible val va_irreducible_lemma_Mov64 : va_b0:va_codes -> va_s0:va_state -> va_sN:va_state ->
  dst:va_dst_operand -> src:va_operand
  -> Ghost ((va_bM:va_codes) * (va_sM:va_state))
  (requires ((va_require va_b0 (va_code_Mov64 dst src) va_s0 va_sN) /\
    (va_is_dst_dst_operand_uint64 dst va_s0) /\ (va_is_src_operand_uint64 src va_s0) /\ (va_get_ok
    va_s0)))
  (ensures (fun ((va_bM:va_codes), (va_sM:va_state)) -> ((va_ensure va_b0 va_bM va_s0 va_sM va_sN)
    /\ (va_get_ok va_sM) /\ (va_eval_dst_operand_uint64 va_sM dst) == (va_eval_operand_uint64 va_s0
    src) /\ (va_state_eq va_sM (va_update_ok va_sM (va_update_dst_operand dst va_sM va_s0))))))
irreducible let va_irreducible_lemma_Mov64 va_b0 va_s0 va_sN dst src =
  (va_reveal_opaque (va_transparent_code_Mov64 dst src));
  let (va_old_s:va_state) = va_s0 in
  let (va_sM, (va_cM:va_code), va_bM) = (va_lemma_block va_b0 va_s0 va_sN) in
  (va_bM, va_sM)
let va_lemma_Mov64 = va_irreducible_lemma_Mov64

val va_transparent_code_Load64 : dst:va_dst_operand -> src:va_reg_operand -> offset:int -> Tot
  va_code
let va_transparent_code_Load64 dst src offset =
  (Ins (S.Mov64 dst (OMem (MReg (get_reg src) offset))))
let va_code_Load64 dst src offset =
  (va_make_opaque (va_transparent_code_Load64 dst src offset))

irreducible val va_irreducible_lemma_Load64 : va_b0:va_codes -> va_s0:va_state -> va_sN:va_state ->
  dst:va_dst_operand -> src:va_reg_operand -> offset:int
  -> Ghost ((va_bM:va_codes) * (va_sM:va_state))
  (requires ((va_require va_b0 (va_code_Load64 dst src offset) va_s0 va_sN) /\
    (va_is_dst_dst_operand_uint64 dst va_s0) /\ (va_is_src_reg_operand_uint64 src va_s0) /\
    (va_get_ok va_s0) /\ (valid_src_addr (va_get_mem va_s0) ((va_eval_reg_operand_uint64 va_s0 src)
    + offset))))
  (ensures (fun ((va_bM:va_codes), (va_sM:va_state)) -> ((va_ensure va_b0 va_bM va_s0 va_sM va_sN)
    /\ (va_get_ok va_sM) /\ (va_eval_dst_operand_uint64 va_sM dst) == (va_subscript (va_get_mem
    va_sM) ((va_eval_reg_operand_uint64 va_s0 src) + offset)) /\ (va_state_eq va_sM (va_update_ok
    va_sM (va_update_dst_operand dst va_sM va_s0))))))
irreducible let va_irreducible_lemma_Load64 va_b0 va_s0 va_sN dst src offset =
  (va_reveal_opaque (va_transparent_code_Load64 dst src offset));
  let (va_old_s:va_state) = va_s0 in
  let (va_sM, (va_cM:va_code), va_bM) = (va_lemma_block va_b0 va_s0 va_sN) in
  (va_bM, va_sM)
let va_lemma_Load64 = va_irreducible_lemma_Load64

val va_transparent_code_Store64 : dst:va_reg_operand -> src:va_operand -> offset:int -> Tot va_code
let va_transparent_code_Store64 dst src offset =
  (Ins (S.Mov64 (OMem (MReg (get_reg dst) offset)) src))
let va_code_Store64 dst src offset =
  (va_make_opaque (va_transparent_code_Store64 dst src offset))

irreducible val va_irreducible_lemma_Store64 : va_b0:va_codes -> va_s0:va_state -> va_sN:va_state
  -> dst:va_reg_operand -> src:va_operand -> offset:int
  -> Ghost ((va_bM:va_codes) * (va_sM:va_state))
  (requires ((va_require va_b0 (va_code_Store64 dst src offset) va_s0 va_sN) /\
    (va_is_src_reg_operand_uint64 dst va_s0) /\ (va_is_src_operand_uint64 src va_s0) /\ (va_get_ok
    va_s0) /\ (valid_dst_addr (va_get_mem va_s0) ((va_eval_reg_operand_uint64 va_s0 dst) +
    offset))))
  (ensures (fun ((va_bM:va_codes), (va_sM:va_state)) -> ((va_ensure va_b0 va_bM va_s0 va_sM va_sN)
    /\ (va_get_ok va_sM) /\ (va_get_mem va_sM) == (va_update (va_get_mem va_s0)
    ((va_eval_reg_operand_uint64 va_s0 dst) + offset) (va_eval_operand_uint64 va_s0 src)) /\
    (va_state_eq va_sM (va_update_mem va_sM (va_update_ok va_sM va_s0))))))
irreducible let va_irreducible_lemma_Store64 va_b0 va_s0 va_sN dst src offset =
  (va_reveal_opaque (va_transparent_code_Store64 dst src offset));
  let (va_old_s:va_state) = va_s0 in
  let (va_sM, (va_cM:va_code), va_bM) = (va_lemma_block va_b0 va_s0 va_sN) in
  assert (Map.equal (va_get_mem va_sM) (va_update (va_get_mem va_old_s)
    ((va_eval_reg_operand_uint64 va_old_s dst) + offset) (va_eval_operand_uint64 va_old_s src)));
  (va_bM, va_sM)
let va_lemma_Store64 = va_irreducible_lemma_Store64

val va_transparent_code_Add64 : dst:va_dst_operand -> src:va_operand -> Tot va_code
let va_transparent_code_Add64 dst src =
  (Ins (S.Add64 dst src))
let va_code_Add64 dst src =
  (va_make_opaque (va_transparent_code_Add64 dst src))

irreducible val va_irreducible_lemma_Add64 : va_b0:va_codes -> va_s0:va_state -> va_sN:va_state ->
  dst:va_dst_operand -> src:va_operand
  -> Ghost ((va_bM:va_codes) * (va_sM:va_state))
  (requires ((va_require va_b0 (va_code_Add64 dst src) va_s0 va_sN) /\
    (va_is_dst_dst_operand_uint64 dst va_s0) /\ (va_is_src_operand_uint64 src va_s0) /\ (va_get_ok
    va_s0) /\ (va_eval_operand_uint64 va_s0 src) + (va_eval_dst_operand_uint64 va_s0 dst) <
    nat64_max))
  (ensures (fun ((va_bM:va_codes), (va_sM:va_state)) -> ((va_ensure va_b0 va_bM va_s0 va_sM va_sN)
    /\ (va_get_ok va_sM) /\ (eq_int (va_eval_dst_operand_uint64 va_sM dst)
    ((va_eval_dst_operand_uint64 va_s0 dst) + (va_eval_operand_uint64 va_s0 src))) /\ (va_state_eq
    va_sM (va_update_flags va_sM (va_update_ok va_sM (va_update_dst_operand dst va_sM va_s0)))))))
irreducible let va_irreducible_lemma_Add64 va_b0 va_s0 va_sN dst src =
  (va_reveal_opaque (va_transparent_code_Add64 dst src));
  let (va_old_s:va_state) = va_s0 in
  let (va_sM, (va_cM:va_code), va_bM) = (va_lemma_block va_b0 va_s0 va_sN) in
  (va_bM, va_sM)
let va_lemma_Add64 = va_irreducible_lemma_Add64

val va_transparent_code_Add64Wrap : dst:va_dst_operand -> src:va_operand -> Tot va_code
let va_transparent_code_Add64Wrap dst src =
  (Ins (S.Add64 dst src))
let va_code_Add64Wrap dst src =
  (va_make_opaque (va_transparent_code_Add64Wrap dst src))

irreducible val va_irreducible_lemma_Add64Wrap : va_b0:va_codes -> va_s0:va_state -> va_sN:va_state
  -> dst:va_dst_operand -> src:va_operand
  -> Ghost ((va_bM:va_codes) * (va_sM:va_state))
  (requires ((va_require va_b0 (va_code_Add64Wrap dst src) va_s0 va_sN) /\
    (va_is_dst_dst_operand_uint64 dst va_s0) /\ (va_is_src_operand_uint64 src va_s0) /\ (va_get_ok
    va_s0)))
  (ensures (fun ((va_bM:va_codes), (va_sM:va_state)) -> ((va_ensure va_b0 va_bM va_s0 va_sM va_sN)
    /\ (va_get_ok va_sM) /\ (va_eval_dst_operand_uint64 va_sM dst) == (add_wrap
    (va_eval_dst_operand_uint64 va_s0 dst) (va_eval_operand_uint64 va_s0 src)) /\ (cf (va_get_flags
    va_sM)) == ((va_eval_dst_operand_uint64 va_s0 dst) + (va_eval_operand_uint64 va_s0 src) >=
    nat64_max) /\ (va_state_eq va_sM (va_update_flags va_sM (va_update_ok va_sM
    (va_update_dst_operand dst va_sM va_s0)))))))
irreducible let va_irreducible_lemma_Add64Wrap va_b0 va_s0 va_sN dst src =
  (va_reveal_opaque (va_transparent_code_Add64Wrap dst src));
  let (va_old_s:va_state) = va_s0 in
  let (va_sM, (va_cM:va_code), va_bM) = (va_lemma_block va_b0 va_s0 va_sN) in
  (va_bM, va_sM)
let va_lemma_Add64Wrap = va_irreducible_lemma_Add64Wrap

val va_transparent_code_AddLea64 : dst:va_dst_operand -> src1:va_operand -> src2:va_operand -> Tot
  va_code
let va_transparent_code_AddLea64 dst src1 src2 =
  (Ins (S.AddLea64 dst src1 src2))
let va_code_AddLea64 dst src1 src2 =
  (va_make_opaque (va_transparent_code_AddLea64 dst src1 src2))

irreducible val va_irreducible_lemma_AddLea64 : va_b0:va_codes -> va_s0:va_state -> va_sN:va_state
  -> dst:va_dst_operand -> src1:va_operand -> src2:va_operand
  -> Ghost ((va_bM:va_codes) * (va_sM:va_state))
  (requires ((va_require va_b0 (va_code_AddLea64 dst src1 src2) va_s0 va_sN) /\
    (va_is_dst_dst_operand_uint64 dst va_s0) /\ (va_is_src_operand_uint64 src1 va_s0) /\
    (va_is_src_operand_uint64 src2 va_s0) /\ (va_get_ok va_s0) /\ (va_eval_operand_uint64 va_s0
    src1) + (va_eval_operand_uint64 va_s0 src2) < nat64_max))
  (ensures (fun ((va_bM:va_codes), (va_sM:va_state)) -> ((va_ensure va_b0 va_bM va_s0 va_sM va_sN)
    /\ (va_get_ok va_sM) /\ (eq_int (va_eval_dst_operand_uint64 va_sM dst) ((va_eval_operand_uint64
    va_s0 src1) + (va_eval_operand_uint64 va_s0 src2))) /\ (va_state_eq va_sM (va_update_ok va_sM
    (va_update_dst_operand dst va_sM va_s0))))))
irreducible let va_irreducible_lemma_AddLea64 va_b0 va_s0 va_sN dst src1 src2 =
  (va_reveal_opaque (va_transparent_code_AddLea64 dst src1 src2));
  let (va_old_s:va_state) = va_s0 in
  let (va_sM, (va_cM:va_code), va_bM) = (va_lemma_block va_b0 va_s0 va_sN) in
  (va_bM, va_sM)
let va_lemma_AddLea64 = va_irreducible_lemma_AddLea64

val va_transparent_code_Adc64Wrap : dst:va_dst_operand -> src:va_operand -> Tot va_code
let va_transparent_code_Adc64Wrap dst src =
  (Ins (S.AddCarry64 dst src))
let va_code_Adc64Wrap dst src =
  (va_make_opaque (va_transparent_code_Adc64Wrap dst src))

irreducible val va_irreducible_lemma_Adc64Wrap : va_b0:va_codes -> va_s0:va_state -> va_sN:va_state
  -> dst:va_dst_operand -> src:va_operand
  -> Ghost ((va_bM:va_codes) * (va_sM:va_state))
  (requires ((va_require va_b0 (va_code_Adc64Wrap dst src) va_s0 va_sN) /\
    (va_is_dst_dst_operand_uint64 dst va_s0) /\ (va_is_src_operand_uint64 src va_s0) /\ (va_get_ok
    va_s0)))
  (ensures (fun ((va_bM:va_codes), (va_sM:va_state)) -> ((va_ensure va_b0 va_bM va_s0 va_sM va_sN)
    /\ (va_get_ok va_sM) /\ (va_eval_dst_operand_uint64 va_sM dst) == (add_wrap (add_wrap
    (va_eval_dst_operand_uint64 va_s0 dst) (va_eval_operand_uint64 va_s0 src)) (if (cf
    (va_get_flags va_s0)) then 1 else 0)) /\ (cf (va_get_flags va_sM)) ==
    ((va_eval_dst_operand_uint64 va_s0 dst) + (va_eval_operand_uint64 va_s0 src) + (if (cf
    (va_get_flags va_s0)) then 1 else 0) >= nat64_max) /\ (va_state_eq va_sM (va_update_flags va_sM
    (va_update_ok va_sM (va_update_dst_operand dst va_sM va_s0)))))))
irreducible let va_irreducible_lemma_Adc64Wrap va_b0 va_s0 va_sN dst src =
  (va_reveal_opaque (va_transparent_code_Adc64Wrap dst src));
  let (va_old_s:va_state) = va_s0 in
  let (va_sM, (va_cM:va_code), va_bM) = (va_lemma_block va_b0 va_s0 va_sN) in
  (va_bM, va_sM)
let va_lemma_Adc64Wrap = va_irreducible_lemma_Adc64Wrap

val va_transparent_code_Sub64 : dst:va_dst_operand -> src:va_operand -> Tot va_code
let va_transparent_code_Sub64 dst src =
  (Ins (S.Sub64 dst src))
let va_code_Sub64 dst src =
  (va_make_opaque (va_transparent_code_Sub64 dst src))

irreducible val va_irreducible_lemma_Sub64 : va_b0:va_codes -> va_s0:va_state -> va_sN:va_state ->
  dst:va_dst_operand -> src:va_operand
  -> Ghost ((va_bM:va_codes) * (va_sM:va_state))
  (requires ((va_require va_b0 (va_code_Sub64 dst src) va_s0 va_sN) /\
    (va_is_dst_dst_operand_uint64 dst va_s0) /\ (va_is_src_operand_uint64 src va_s0) /\ (va_get_ok
    va_s0) /\ 0 <= (va_eval_dst_operand_uint64 va_s0 dst) - (va_eval_operand_uint64 va_s0 src)))
  (ensures (fun ((va_bM:va_codes), (va_sM:va_state)) -> ((va_ensure va_b0 va_bM va_s0 va_sM va_sN)
    /\ (va_get_ok va_sM) /\ (eq_int (va_eval_dst_operand_uint64 va_sM dst)
    ((va_eval_dst_operand_uint64 va_s0 dst) - (va_eval_operand_uint64 va_s0 src))) /\ (va_state_eq
    va_sM (va_update_flags va_sM (va_update_ok va_sM (va_update_dst_operand dst va_sM va_s0)))))))
irreducible let va_irreducible_lemma_Sub64 va_b0 va_s0 va_sN dst src =
  (va_reveal_opaque (va_transparent_code_Sub64 dst src));
  let (va_old_s:va_state) = va_s0 in
  let (va_sM, (va_cM:va_code), va_bM) = (va_lemma_block va_b0 va_s0 va_sN) in
  (va_bM, va_sM)
let va_lemma_Sub64 = va_irreducible_lemma_Sub64

val va_transparent_code_Sub64Wrap : dst:va_dst_operand -> src:va_operand -> Tot va_code
let va_transparent_code_Sub64Wrap dst src =
  (Ins (S.Sub64 dst src))
let va_code_Sub64Wrap dst src =
  (va_make_opaque (va_transparent_code_Sub64Wrap dst src))

irreducible val va_irreducible_lemma_Sub64Wrap : va_b0:va_codes -> va_s0:va_state -> va_sN:va_state
  -> dst:va_dst_operand -> src:va_operand
  -> Ghost ((va_bM:va_codes) * (va_sM:va_state))
  (requires ((va_require va_b0 (va_code_Sub64Wrap dst src) va_s0 va_sN) /\
    (va_is_dst_dst_operand_uint64 dst va_s0) /\ (va_is_src_operand_uint64 src va_s0) /\ (va_get_ok
    va_s0)))
  (ensures (fun ((va_bM:va_codes), (va_sM:va_state)) -> ((va_ensure va_b0 va_bM va_s0 va_sM va_sN)
    /\ (va_get_ok va_sM) /\ (va_eval_dst_operand_uint64 va_sM dst) == ((va_eval_dst_operand_uint64
    va_s0 dst) - (va_eval_operand_uint64 va_s0 src)) `op_Modulus` nat64_max /\ (va_state_eq va_sM
    (va_update_flags va_sM (va_update_ok va_sM (va_update_dst_operand dst va_sM va_s0)))))))
irreducible let va_irreducible_lemma_Sub64Wrap va_b0 va_s0 va_sN dst src =
  (va_reveal_opaque (va_transparent_code_Sub64Wrap dst src));
  let (va_old_s:va_state) = va_s0 in
  let (va_sM, (va_cM:va_code), va_bM) = (va_lemma_block va_b0 va_s0 va_sN) in
  (va_bM, va_sM)
let va_lemma_Sub64Wrap = va_irreducible_lemma_Sub64Wrap

val va_transparent_code_Mul64Wrap : src:va_operand -> Tot va_code
let va_transparent_code_Mul64Wrap src =
  (Ins (S.Mul64 src))
let va_code_Mul64Wrap src =
  (va_make_opaque (va_transparent_code_Mul64Wrap src))

irreducible val va_irreducible_lemma_Mul64Wrap : va_b0:va_codes -> va_s0:va_state -> va_sN:va_state
  -> src:va_operand
  -> Ghost ((va_bM:va_codes) * (va_sM:va_state))
  (requires ((va_require va_b0 (va_code_Mul64Wrap src) va_s0 va_sN) /\ (va_is_src_operand_uint64
    src va_s0) /\ (va_get_ok va_s0)))
  (ensures (fun ((va_bM:va_codes), (va_sM:va_state)) -> ((va_ensure va_b0 va_bM va_s0 va_sM va_sN)
    /\ (va_get_ok va_sM) /\ nat64_max `op_Multiply` (va_get_reg Rdx va_sM) + (va_get_reg Rax va_sM)
    == (va_get_reg Rax va_s0) `op_Multiply` (va_eval_operand_uint64 va_s0 src) /\ (va_state_eq
    va_sM (va_update_reg Rdx va_sM (va_update_reg Rax va_sM (va_update_flags va_sM (va_update_ok
    va_sM va_s0))))))))
irreducible let va_irreducible_lemma_Mul64Wrap va_b0 va_s0 va_sN src =
  (va_reveal_opaque (va_transparent_code_Mul64Wrap src));
  let (va_old_s:va_state) = va_s0 in
  let (va_sM, (va_cM:va_code), va_bM) = (va_lemma_block va_b0 va_s0 va_sN) in
  (va_bM, va_sM)
let va_lemma_Mul64Wrap = va_irreducible_lemma_Mul64Wrap

val va_transparent_code_IMul64 : dst:va_dst_operand -> src:va_operand -> Tot va_code
let va_transparent_code_IMul64 dst src =
  (Ins (S.IMul64 dst src))
let va_code_IMul64 dst src =
  (va_make_opaque (va_transparent_code_IMul64 dst src))

irreducible val va_irreducible_lemma_IMul64 : va_b0:va_codes -> va_s0:va_state -> va_sN:va_state ->
  dst:va_dst_operand -> src:va_operand
  -> Ghost ((va_bM:va_codes) * (va_sM:va_state))
  (requires ((va_require va_b0 (va_code_IMul64 dst src) va_s0 va_sN) /\
    (va_is_dst_dst_operand_uint64 dst va_s0) /\ (va_is_src_operand_uint64 src va_s0) /\ (va_get_ok
    va_s0) /\ (va_eval_dst_operand_uint64 va_s0 dst) `op_Multiply` (va_eval_operand_uint64 va_s0
    src) < nat64_max))
  (ensures (fun ((va_bM:va_codes), (va_sM:va_state)) -> ((va_ensure va_b0 va_bM va_s0 va_sM va_sN)
    /\ (va_get_ok va_sM) /\ (eq_int (va_eval_dst_operand_uint64 va_sM dst)
    ((va_eval_dst_operand_uint64 va_s0 dst) `op_Multiply` (va_eval_operand_uint64 va_s0 src))) /\
    (va_state_eq va_sM (va_update_flags va_sM (va_update_ok va_sM (va_update_dst_operand dst va_sM
    va_s0)))))))
irreducible let va_irreducible_lemma_IMul64 va_b0 va_s0 va_sN dst src =
  (va_reveal_opaque (va_transparent_code_IMul64 dst src));
  let (va_old_s:va_state) = va_s0 in
  let (va_sM, (va_cM:va_code), va_bM) = (va_lemma_block va_b0 va_s0 va_sN) in
  (lemma_mul_nat (va_eval_dst_operand_uint64 va_old_s dst) (va_eval_operand_uint64 va_old_s src));
  (va_bM, va_sM)
let va_lemma_IMul64 = va_irreducible_lemma_IMul64

val va_transparent_code_Xor64 : dst:va_dst_operand -> src:va_operand -> Tot va_code
let va_transparent_code_Xor64 dst src =
  (Ins (S.Xor64 dst src))
let va_code_Xor64 dst src =
  (va_make_opaque (va_transparent_code_Xor64 dst src))

irreducible val va_irreducible_lemma_Xor64 : va_b0:va_codes -> va_s0:va_state -> va_sN:va_state ->
  dst:va_dst_operand -> src:va_operand
  -> Ghost ((va_bM:va_codes) * (va_sM:va_state))
  (requires ((va_require va_b0 (va_code_Xor64 dst src) va_s0 va_sN) /\
    (va_is_dst_dst_operand_uint64 dst va_s0) /\ (va_is_src_operand_uint64 src va_s0) /\ (va_get_ok
    va_s0)))
  (ensures (fun ((va_bM:va_codes), (va_sM:va_state)) -> ((va_ensure va_b0 va_bM va_s0 va_sM va_sN)
    /\ (va_get_ok va_sM) /\ (va_eval_dst_operand_uint64 va_sM dst) == (logxor64
    (va_eval_dst_operand_uint64 va_s0 dst) (va_eval_operand_uint64 va_s0 src)) /\ (va_state_eq
    va_sM (va_update_flags va_sM (va_update_ok va_sM (va_update_dst_operand dst va_sM va_s0)))))))
irreducible let va_irreducible_lemma_Xor64 va_b0 va_s0 va_sN dst src =
  (va_reveal_opaque (va_transparent_code_Xor64 dst src));
  let (va_old_s:va_state) = va_s0 in
  let (va_sM, (va_cM:va_code), va_bM) = (va_lemma_block va_b0 va_s0 va_sN) in
  (va_bM, va_sM)
let va_lemma_Xor64 = va_irreducible_lemma_Xor64

val va_transparent_code_And64 : dst:va_dst_operand -> src:va_operand -> Tot va_code
let va_transparent_code_And64 dst src =
  (Ins (S.And64 dst src))
let va_code_And64 dst src =
  (va_make_opaque (va_transparent_code_And64 dst src))

irreducible val va_irreducible_lemma_And64 : va_b0:va_codes -> va_s0:va_state -> va_sN:va_state ->
  dst:va_dst_operand -> src:va_operand
  -> Ghost ((va_bM:va_codes) * (va_sM:va_state))
  (requires ((va_require va_b0 (va_code_And64 dst src) va_s0 va_sN) /\
    (va_is_dst_dst_operand_uint64 dst va_s0) /\ (va_is_src_operand_uint64 src va_s0) /\ (va_get_ok
    va_s0)))
  (ensures (fun ((va_bM:va_codes), (va_sM:va_state)) -> ((va_ensure va_b0 va_bM va_s0 va_sM va_sN)
    /\ (va_get_ok va_sM) /\ (va_eval_dst_operand_uint64 va_sM dst) == (logand64
    (va_eval_dst_operand_uint64 va_s0 dst) (va_eval_operand_uint64 va_s0 src)) /\ (va_state_eq
    va_sM (va_update_flags va_sM (va_update_ok va_sM (va_update_dst_operand dst va_sM va_s0)))))))
irreducible let va_irreducible_lemma_And64 va_b0 va_s0 va_sN dst src =
  (va_reveal_opaque (va_transparent_code_And64 dst src));
  let (va_old_s:va_state) = va_s0 in
  let (va_sM, (va_cM:va_code), va_bM) = (va_lemma_block va_b0 va_s0 va_sN) in
  (va_bM, va_sM)
let va_lemma_And64 = va_irreducible_lemma_And64

val va_transparent_code_Shl64 : dst:va_dst_operand -> amt:va_shift_amt -> Tot va_code
let va_transparent_code_Shl64 dst amt =
  (Ins (S.Shl64 dst amt))
let va_code_Shl64 dst amt =
  (va_make_opaque (va_transparent_code_Shl64 dst amt))

irreducible val va_irreducible_lemma_Shl64 : va_b0:va_codes -> va_s0:va_state -> va_sN:va_state ->
  dst:va_dst_operand -> amt:va_shift_amt
  -> Ghost ((va_bM:va_codes) * (va_sM:va_state))
  (requires ((va_require va_b0 (va_code_Shl64 dst amt) va_s0 va_sN) /\
    (va_is_dst_dst_operand_uint64 dst va_s0) /\ (va_is_src_shift_amt_uint64 amt va_s0) /\
    (va_get_ok va_s0)))
  (ensures (fun ((va_bM:va_codes), (va_sM:va_state)) -> ((va_ensure va_b0 va_bM va_s0 va_sM va_sN)
    /\ (va_get_ok va_sM) /\ (va_eval_dst_operand_uint64 va_sM dst) == (shift_left64
    (va_eval_dst_operand_uint64 va_s0 dst) (va_eval_shift_amt_uint64 va_s0 amt)) /\ (va_state_eq
    va_sM (va_update_flags va_sM (va_update_ok va_sM (va_update_dst_operand dst va_sM va_s0)))))))
irreducible let va_irreducible_lemma_Shl64 va_b0 va_s0 va_sN dst amt =
  (va_reveal_opaque (va_transparent_code_Shl64 dst amt));
  let (va_old_s:va_state) = va_s0 in
  let (va_sM, (va_cM:va_code), va_bM) = (va_lemma_block va_b0 va_s0 va_sN) in
  (va_bM, va_sM)
let va_lemma_Shl64 = va_irreducible_lemma_Shl64

val va_transparent_code_Shr64 : dst:va_dst_operand -> amt:va_shift_amt -> Tot va_code
let va_transparent_code_Shr64 dst amt =
  (Ins (S.Shr64 dst amt))
let va_code_Shr64 dst amt =
  (va_make_opaque (va_transparent_code_Shr64 dst amt))

irreducible val va_irreducible_lemma_Shr64 : va_b0:va_codes -> va_s0:va_state -> va_sN:va_state ->
  dst:va_dst_operand -> amt:va_shift_amt
  -> Ghost ((va_bM:va_codes) * (va_sM:va_state))
  (requires ((va_require va_b0 (va_code_Shr64 dst amt) va_s0 va_sN) /\
    (va_is_dst_dst_operand_uint64 dst va_s0) /\ (va_is_src_shift_amt_uint64 amt va_s0) /\
    (va_get_ok va_s0)))
  (ensures (fun ((va_bM:va_codes), (va_sM:va_state)) -> ((va_ensure va_b0 va_bM va_s0 va_sM va_sN)
    /\ (va_get_ok va_sM) /\ (va_eval_dst_operand_uint64 va_sM dst) == (shift_right64
    (va_eval_dst_operand_uint64 va_s0 dst) (va_eval_shift_amt_uint64 va_s0 amt)) /\ (va_state_eq
    va_sM (va_update_flags va_sM (va_update_ok va_sM (va_update_dst_operand dst va_sM va_s0)))))))
irreducible let va_irreducible_lemma_Shr64 va_b0 va_s0 va_sN dst amt =
  (va_reveal_opaque (va_transparent_code_Shr64 dst amt));
  let (va_old_s:va_state) = va_s0 in
  let (va_sM, (va_cM:va_code), va_bM) = (va_lemma_block va_b0 va_s0 va_sN) in
  (va_bM, va_sM)
let va_lemma_Shr64 = va_irreducible_lemma_Shr64
