module X64.Poly1305
#reset-options "--z3rlimit 20"
open X64.Machine_s
open X64.Vale.State_i
open X64.Vale.Decls
open X64.Vale.StrongPost_i
open X64.Poly1305.Spec_s
open X64.Poly1305.Math_i
open Opaque_i
open FStar.Tactics

val va_transparent_code_poly1305_multiply : va_dummy:unit -> Tot va_code
let va_transparent_code_poly1305_multiply () =
  (va_Block (va_CCons (va_Block (va_CCons (va_code_Mul64Wrap (va_op_operand_reg R14)) (va_CCons
    (va_code_Mov64 (va_op_dst_operand_reg R9) (va_op_operand_reg Rax)) (va_CCons (va_code_Mov64
    (va_op_dst_operand_reg Rax) (va_op_operand_reg R11)) (va_CCons (va_code_Mov64
    (va_op_dst_operand_reg R10) (va_op_operand_reg Rdx)) (va_CCons (va_code_Mul64Wrap
    (va_op_operand_reg R14)) (va_CCons (va_code_Mov64 (va_op_dst_operand_reg R14)
    (va_op_operand_reg Rax)) (va_CCons (va_code_Mov64 (va_op_dst_operand_reg Rax)
    (va_op_operand_reg R11)) (va_CCons (va_code_Mov64 (va_op_dst_operand_reg R8) (va_op_operand_reg
    Rdx)) (va_CCons (va_code_Mul64Wrap (va_op_operand_reg Rbx)) (va_CCons (va_code_Add64Wrap
    (va_op_dst_operand_reg R9) (va_op_operand_reg Rax)) (va_CCons (va_code_Mov64
    (va_op_dst_operand_reg Rax) (va_op_operand_reg R13)) (va_CCons (va_code_Adc64Wrap
    (va_op_dst_operand_reg R10) (va_op_operand_reg Rdx)) (va_CCons (va_code_Mul64Wrap
    (va_op_operand_reg Rbx)) (va_CCons (va_code_Mov64 (va_op_dst_operand_reg Rbx)
    (va_op_operand_reg Rbp)) (va_CCons (va_code_Add64Wrap (va_op_dst_operand_reg R14)
    (va_op_operand_reg Rax)) (va_CCons (va_code_Adc64Wrap (va_op_dst_operand_reg R8)
    (va_op_operand_reg Rdx)) (va_CCons (va_code_IMul64 (va_op_dst_operand_reg Rbx)
    (va_op_operand_reg R13)) (va_CCons (va_code_Add64Wrap (va_op_dst_operand_reg R9)
    (va_op_operand_reg Rbx)) (va_CCons (va_code_Mov64 (va_op_dst_operand_reg Rbx)
    (va_op_operand_reg R8)) (va_CCons (va_code_Adc64Wrap (va_op_dst_operand_reg R10)
    (va_const_operand 0)) (va_CCons (va_code_IMul64 (va_op_dst_operand_reg Rbp) (va_op_operand_reg
    R11)) (va_CCons (va_code_Add64Wrap (va_op_dst_operand_reg Rbx) (va_op_operand_reg R9))
    (va_CCons (va_code_Mov64 (va_op_dst_operand_reg Rax) (va_const_operand 18446744073709551612))
    (va_CCons (va_code_Adc64Wrap (va_op_dst_operand_reg R10) (va_op_operand_reg Rbp)) (va_CNil
    ())))))))))))))))))))))))))) (va_CNil ())))
let va_code_poly1305_multiply () =
  (va_make_opaque (va_transparent_code_poly1305_multiply ()))

let va_ins_1_poly1305_multiply () =
  [(va_fast_ins_Mul64Wrap (va_op_operand_reg R14)); (va_fast_ins_Mov64 (va_op_dst_operand_reg R9)
    (va_op_operand_reg Rax)); (va_fast_ins_Mov64 (va_op_dst_operand_reg Rax) (va_op_operand_reg
    R11)); (va_fast_ins_Mov64 (va_op_dst_operand_reg R10) (va_op_operand_reg Rdx));
    (va_fast_ins_Mul64Wrap (va_op_operand_reg R14)); (va_fast_ins_Mov64 (va_op_dst_operand_reg R14)
    (va_op_operand_reg Rax)); (va_fast_ins_Mov64 (va_op_dst_operand_reg Rax) (va_op_operand_reg
    R11)); (va_fast_ins_Mov64 (va_op_dst_operand_reg R8) (va_op_operand_reg Rdx));
    (va_fast_ins_Mul64Wrap (va_op_operand_reg Rbx)); (va_fast_ins_Add64Wrap (va_op_dst_operand_reg
    R9) (va_op_operand_reg Rax)); (va_fast_ins_Mov64 (va_op_dst_operand_reg Rax) (va_op_operand_reg
    R13)); (va_fast_ins_Adc64Wrap (va_op_dst_operand_reg R10) (va_op_operand_reg Rdx));
    (va_fast_ins_Mul64Wrap (va_op_operand_reg Rbx)); (va_fast_ins_Mov64 (va_op_dst_operand_reg Rbx)
    (va_op_operand_reg Rbp)); (va_fast_ins_Add64Wrap (va_op_dst_operand_reg R14) (va_op_operand_reg
    Rax)); (va_fast_ins_Adc64Wrap (va_op_dst_operand_reg R8) (va_op_operand_reg Rdx));
    (va_fast_ins_IMul64 (va_op_dst_operand_reg Rbx) (va_op_operand_reg R13));
    (va_fast_ins_Add64Wrap (va_op_dst_operand_reg R9) (va_op_operand_reg Rbx)); (va_fast_ins_Mov64
    (va_op_dst_operand_reg Rbx) (va_op_operand_reg R8)); (va_fast_ins_Adc64Wrap
    (va_op_dst_operand_reg R10) (va_const_operand 0)); (va_fast_ins_IMul64 (va_op_dst_operand_reg
    Rbp) (va_op_operand_reg R11)); (va_fast_ins_Add64Wrap (va_op_dst_operand_reg Rbx)
    (va_op_operand_reg R9)); (va_fast_ins_Mov64 (va_op_dst_operand_reg Rax) (va_const_operand
    18446744073709551612)); (va_fast_ins_Adc64Wrap (va_op_dst_operand_reg R10) (va_op_operand_reg
    Rbp))]

irreducible val va_irreducible_lemma_poly1305_multiply : va_b0:va_codes -> va_s0:va_state ->
  va_sN:va_state -> r1:nat64
  -> Ghost ((va_bM:va_codes) * (va_sM:va_state) * (hh:int))
  (requires ((va_require va_b0 (va_code_poly1305_multiply ()) va_s0 va_sN) /\ (va_get_ok va_s0) /\
    (let n = nat64_max in let p = n `op_Multiply` n `op_Multiply` 4 - 5 in let r = r1 `op_Multiply`
    n + (va_get_reg R11 va_s0) in let h = (va_get_reg Rbp va_s0) `op_Multiply` (n `op_Multiply` n)
    + (va_get_reg Rbx va_s0) `op_Multiply` n + (va_get_reg R14 va_s0) in r1 `op_Modulus` 4 == 0 /\
    (eq_int (va_get_reg R13 va_s0) (r1 + r1 `op_Division` 4)) /\ (va_get_reg Rbp va_s0)
    `op_Multiply` (va_get_reg R11 va_s0) < 7 `op_Multiply` (n `op_Division` 16) /\ (va_get_reg R14
    va_s0) `op_Multiply` r1 < n `op_Multiply` (n `op_Division` 16) /\ (va_get_reg Rbx va_s0)
    `op_Multiply` (va_get_reg R11 va_s0) < n `op_Multiply` (n `op_Division` 16) /\ (va_get_reg Rbp
    va_s0) `op_Multiply` (va_get_reg R13 va_s0) < n `op_Multiply` (n `op_Division` 8) /\
    (va_get_reg R14 va_s0) `op_Multiply` (va_get_reg R11 va_s0) < n `op_Multiply` (n `op_Division`
    16) /\ (va_get_reg Rbx va_s0) `op_Multiply` (va_get_reg R13 va_s0) < n `op_Multiply` (n
    `op_Division` 8) /\ (va_get_reg Rbp va_s0) `op_Multiply` (va_get_reg R13 va_s0) < 7
    `op_Multiply` (5 `op_Multiply` n `op_Division` 64) /\ (va_get_reg Rax va_s0) == r1)))
  (ensures (fun ((va_bM:va_codes), (va_sM:va_state), (hh:int)) -> ((va_ensure va_b0 va_bM va_s0
    va_sM va_sN) /\ (va_get_ok va_sM) /\ (let n = nat64_max in let p = n `op_Multiply` n
    `op_Multiply` 4 - 5 in let r = r1 `op_Multiply` n + (va_get_reg R11 va_s0) in let h =
    (va_get_reg Rbp va_s0) `op_Multiply` (n `op_Multiply` n) + (va_get_reg Rbx va_s0) `op_Multiply`
    n + (va_get_reg R14 va_s0) in hh == n `op_Multiply` n `op_Multiply` (va_get_reg R10 va_sM) + n
    `op_Multiply` (va_get_reg Rbx va_sM) + (va_get_reg R14 va_sM) /\ h `op_Multiply` r `op_Modulus`
    p == hh `op_Modulus` p /\ (va_get_reg R10 va_sM) `op_Division` 4 `op_Multiply` 4 + (va_get_reg
    R10 va_sM) `op_Division` 4 < 18446744073709551616 /\ (va_get_reg Rax va_sM) ==
    18446744073709551612) /\ (va_state_eq va_sM (va_update_flags va_sM (va_update_reg Rdx va_sM
    (va_update_reg Rax va_sM (va_update_reg Rbp va_sM (va_update_reg Rbx va_sM (va_update_reg R14
    va_sM (va_update_reg R10 va_sM (va_update_reg R9 va_sM (va_update_reg R8 va_sM (va_update_ok
    va_sM va_s0))))))))))))))
irreducible let va_irreducible_lemma_poly1305_multiply va_b0 va_s0 va_sN r1 =
  (va_reveal_opaque (va_transparent_code_poly1305_multiply ()));
  let (va_old_s:va_state) = va_s0 in
  let (va_sM, (va_cM:va_code), va_bM) = (va_lemma_block va_b0 va_s0 va_sN) in
  let (va_b1:va_codes) = (va_get_block va_cM) in
  let n = nat64_max in
  let p = (n `op_Multiply` n `op_Multiply` 4 - 5) in
  let r = (r1 `op_Multiply` n + (va_get_reg R11 va_s0)) in
  let h = ((va_get_reg Rbp va_s0) `op_Multiply` (n `op_Multiply` n) + (va_get_reg Rbx va_s0)
    `op_Multiply` n + (va_get_reg R14 va_s0)) in
  assert ((va_get_reg R14 va_s0) `op_Multiply` r1 == r1 `op_Multiply` (va_get_reg R14 va_s0));
  assert ((va_get_reg R11 va_s0) `op_Multiply` (va_get_reg R14 va_s0) == (va_get_reg R14 va_s0)
    `op_Multiply` (va_get_reg R11 va_s0));
  assert ((va_get_reg R11 va_s0) `op_Multiply` (va_get_reg Rbx va_s0) == (va_get_reg Rbx va_s0)
    `op_Multiply` (va_get_reg R11 va_s0));
  assert ((va_get_reg R13 va_s0) `op_Multiply` (va_get_reg Rbx va_s0) == (va_get_reg Rbx va_s0)
    `op_Multiply` (va_get_reg R13 va_s0));
  let gd0 = ((va_get_reg R14 va_s0) `op_Multiply` (va_get_reg R11 va_s0) + (va_get_reg Rbx va_s0)
    `op_Multiply` (va_get_reg R13 va_s0)) in
  let gd1 = ((va_get_reg R14 va_s0) `op_Multiply` r1 + (va_get_reg Rbx va_s0) `op_Multiply`
    (va_get_reg R11 va_s0) + (va_get_reg Rbp va_s0) `op_Multiply` (va_get_reg R13 va_s0)) in
  let gd2 = ((va_get_reg Rbp va_s0) `op_Multiply` (va_get_reg R11 va_s0)) in
  let (va_s21, va_c21, va_b21) = (va_lemma_block va_b1 va_s0 va_sM) in
  (va_lemma_weakest_pre_norm (va_ins_1_poly1305_multiply ()) va_s0 va_s21);
  let hh = (n `op_Multiply` n `op_Multiply` (va_get_reg R10 va_s21) + n `op_Multiply` (va_get_reg
    Rbx va_s21) + (va_get_reg R14 va_s21)) in
  (lemma_poly_multiply n p r h (va_get_reg R11 va_s21) r1 (va_get_reg R14 va_old_s) (va_get_reg Rbx
    va_old_s) (va_get_reg Rbp va_old_s) (va_get_reg R13 va_s21) gd0 gd1 gd2 hh);
  let va_sM = (va_lemma_empty va_s21 va_sM) in
  (va_bM, va_sM, hh)
let va_lemma_poly1305_multiply = va_irreducible_lemma_poly1305_multiply

val va_transparent_code_poly1305_reduce : d3:va_dst_operand -> h0:va_dst_operand ->
  h1:va_dst_operand -> h2:va_dst_operand -> Tot va_code
let va_transparent_code_poly1305_reduce d3 h0 h1 h2 =
  (va_Block (va_CCons (va_code_And64 (va_op_dst_operand_reg Rax) (va_coerce_dst_operand_to_operand
    d3)) (va_CCons (va_code_Mov64 h2 (va_coerce_dst_operand_to_operand d3)) (va_CCons
    (va_code_Shr64 d3 (va_const_shift_amt 2)) (va_CCons (va_code_And64 h2 (va_const_operand 3))
    (va_CCons (va_code_Add64Wrap (va_op_dst_operand_reg Rax) (va_coerce_dst_operand_to_operand d3))
    (va_CCons (va_code_Add64Wrap h0 (va_op_operand_reg Rax)) (va_CCons (va_code_Adc64Wrap h1
    (va_const_operand 0)) (va_CCons (va_code_Adc64Wrap h2 (va_const_operand 0)) (va_CNil
    ()))))))))))
let va_code_poly1305_reduce d3 h0 h1 h2 =
  (va_make_opaque (va_transparent_code_poly1305_reduce d3 h0 h1 h2))

irreducible val va_irreducible_lemma_poly1305_reduce : va_b0:va_codes -> va_s0:va_state ->
  va_sN:va_state -> d3:va_dst_operand -> h0:va_dst_operand -> h1:va_dst_operand ->
  h2:va_dst_operand -> hd:int -> p:int
  -> Ghost ((va_bM:va_codes) * (va_sM:va_state) * (hh:int))
  (requires ((va_require va_b0 (va_code_poly1305_reduce d3 h0 h1 h2) va_s0 va_sN) /\
    (va_is_dst_dst_operand_uint64 d3 va_s0) /\ (va_is_dst_dst_operand_uint64 h0 va_s0) /\
    (va_is_dst_dst_operand_uint64 h1 va_s0) /\ (va_is_dst_dst_operand_uint64 h2 va_s0) /\
    (va_get_ok va_s0) /\ d3 == (OReg R10) /\ h0 == (OReg R14) /\ h1 == (OReg Rbx) /\ h2 == (OReg
    Rbp) /\ p == n `op_Multiply` n `op_Multiply` 4 - 5 /\ hd == n `op_Multiply` n `op_Multiply`
    (va_eval_dst_operand_uint64 va_s0 d3) + n `op_Multiply` (va_eval_dst_operand_uint64 va_s0 h1) +
    (va_eval_dst_operand_uint64 va_s0 h0) /\ (va_eval_dst_operand_uint64 va_s0 d3) `op_Division` 4
    `op_Multiply` 4 + (va_eval_dst_operand_uint64 va_s0 d3) `op_Division` 4 < 18446744073709551616
    /\ (va_get_reg Rax va_s0) == 18446744073709551612))
  (ensures (fun ((va_bM:va_codes), (va_sM:va_state), (hh:int)) -> ((va_ensure va_b0 va_bM va_s0
    va_sM va_sN) /\ (va_get_ok va_sM) /\ p > 0 /\ hh == n `op_Multiply` n `op_Multiply`
    (va_eval_dst_operand_uint64 va_sM h2) + n `op_Multiply` (va_eval_dst_operand_uint64 va_sM h1) +
    (va_eval_dst_operand_uint64 va_sM h0) /\ hd `op_Modulus` p == hh `op_Modulus` p /\
    (va_eval_dst_operand_uint64 va_sM h2) < 5 /\ (va_state_eq va_sM (va_update_flags va_sM
    (va_update_reg Rax va_sM (va_update_ok va_sM (va_update_dst_operand h2 va_sM
    (va_update_dst_operand h1 va_sM (va_update_dst_operand h0 va_sM (va_update_dst_operand d3 va_sM
    va_s0)))))))))))
irreducible let va_irreducible_lemma_poly1305_reduce va_b0 va_s0 va_sN d3 h0 h1 h2 hd p =
  (va_reveal_opaque (va_transparent_code_poly1305_reduce d3 h0 h1 h2));
  let (va_old_s:va_state) = va_s0 in
  let (va_sM, (va_cM:va_code), va_bM) = (va_lemma_block va_b0 va_s0 va_sN) in
  let (va_b1:va_codes) = (va_get_block va_cM) in
  (lemma_poly_bits64 ());
  let (va_b3, va_s3) = (va_lemma_And64 va_b1 va_s0 va_sM (va_op_dst_operand_reg Rax)
    (va_coerce_dst_operand_to_operand d3)) in
  let (va_b4, va_s4) = (va_lemma_Mov64 va_b3 va_s3 va_sM h2 (va_coerce_dst_operand_to_operand d3))
    in
  let (va_b5, va_s5) = (va_lemma_Shr64 va_b4 va_s4 va_sM d3 (va_const_shift_amt 2)) in
  let (va_b6, va_s6) = (va_lemma_And64 va_b5 va_s5 va_sM h2 (va_const_operand 3)) in
  let (va_b7, va_s7) = (va_lemma_Add64Wrap va_b6 va_s6 va_sM (va_op_dst_operand_reg Rax)
    (va_coerce_dst_operand_to_operand d3)) in
  let (va_b8, va_s8) = (va_lemma_Add64Wrap va_b7 va_s7 va_sM h0 (va_op_operand_reg Rax)) in
  let (va_b9, va_s9) = (va_lemma_Adc64Wrap va_b8 va_s8 va_sM h1 (va_const_operand 0)) in
  let (va_b10, va_s10) = (va_lemma_Adc64Wrap va_b9 va_s9 va_sM h2 (va_const_operand 0)) in
  let h10 = (n `op_Multiply` (va_eval_dst_operand_uint64 va_old_s h1) + (va_eval_dst_operand_uint64
    va_old_s h0)) in
  let hh = (h10 + (va_get_reg Rax va_s10) + (va_eval_dst_operand_uint64 va_old_s d3) `op_Modulus` 4
    `op_Multiply` (n `op_Multiply` n)) in
  (lemma_poly_reduce n p hd (va_eval_dst_operand_uint64 va_old_s d3) h10 (va_get_reg Rax va_s10)
    hh);
  let va_sM = (va_lemma_empty va_s10 va_sM) in
  (va_bM, va_sM, hh)
let va_lemma_poly1305_reduce = va_irreducible_lemma_poly1305_reduce

val va_transparent_code_poly1305_reduce_regs : va_dummy:unit -> Tot va_code
let va_transparent_code_poly1305_reduce_regs () =
  (va_Block (va_CCons (va_code_And64 (va_op_dst_operand_reg Rax) (va_op_operand_reg R10)) (va_CCons
    (va_code_Mov64 (va_op_dst_operand_reg Rbp) (va_op_operand_reg R10)) (va_CCons (va_code_Shr64
    (va_op_dst_operand_reg R10) (va_const_shift_amt 2)) (va_CCons (va_code_And64
    (va_op_dst_operand_reg Rbp) (va_const_operand 3)) (va_CCons (va_code_Add64Wrap
    (va_op_dst_operand_reg Rax) (va_op_operand_reg R10)) (va_CCons (va_code_Add64Wrap
    (va_op_dst_operand_reg R14) (va_op_operand_reg Rax)) (va_CCons (va_code_Adc64Wrap
    (va_op_dst_operand_reg Rbx) (va_const_operand 0)) (va_CCons (va_code_Adc64Wrap
    (va_op_dst_operand_reg Rbp) (va_const_operand 0)) (va_CNil ()))))))))))
let va_code_poly1305_reduce_regs () =
  (va_make_opaque (va_transparent_code_poly1305_reduce_regs ()))

irreducible val va_irreducible_lemma_poly1305_reduce_regs : va_b0:va_codes -> va_s0:va_state ->
  va_sN:va_state -> hd:int -> p:int
  -> Ghost ((va_bM:va_codes) * (va_sM:va_state) * (hh:int))
  (requires ((va_require va_b0 (va_code_poly1305_reduce_regs ()) va_s0 va_sN) /\ (va_get_ok va_s0)
    /\ p == n `op_Multiply` n `op_Multiply` 4 - 5 /\ hd == n `op_Multiply` n `op_Multiply`
    (va_get_reg R10 va_s0) + n `op_Multiply` (va_get_reg Rbx va_s0) + (va_get_reg R14 va_s0) /\
    (va_get_reg R10 va_s0) `op_Division` 4 `op_Multiply` 4 + (va_get_reg R10 va_s0) `op_Division` 4
    < 18446744073709551616 /\ (va_get_reg Rax va_s0) == 18446744073709551612))
  (ensures (fun ((va_bM:va_codes), (va_sM:va_state), (hh:int)) -> ((va_ensure va_b0 va_bM va_s0
    va_sM va_sN) /\ (va_get_ok va_sM) /\ p > 0 /\ hh == n `op_Multiply` n `op_Multiply` (va_get_reg
    Rbp va_sM) + n `op_Multiply` (va_get_reg Rbx va_sM) + (va_get_reg R14 va_sM) /\ hd `op_Modulus`
    p == hh `op_Modulus` p /\ (va_get_reg Rbp va_sM) < 5 /\ (va_state_eq va_sM (va_update_reg Rbp
    va_sM (va_update_reg Rbx va_sM (va_update_reg R14 va_sM (va_update_reg R10 va_sM
    (va_update_flags va_sM (va_update_reg Rax va_sM (va_update_ok va_sM va_s0)))))))))))
irreducible let va_irreducible_lemma_poly1305_reduce_regs va_b0 va_s0 va_sN hd p =
  (va_reveal_opaque (va_transparent_code_poly1305_reduce_regs ()));
  let (va_old_s:va_state) = va_s0 in
  let (va_sM, (va_cM:va_code), va_bM) = (va_lemma_block va_b0 va_s0 va_sN) in
  let (va_b1:va_codes) = (va_get_block va_cM) in
  (lemma_poly_bits64 ());
  let (va_b3, va_s3) = (va_lemma_And64 va_b1 va_s0 va_sM (va_op_dst_operand_reg Rax)
    (va_op_operand_reg R10)) in
  let (va_b4, va_s4) = (va_lemma_Mov64 va_b3 va_s3 va_sM (va_op_dst_operand_reg Rbp)
    (va_op_operand_reg R10)) in
  let (va_b5, va_s5) = (va_lemma_Shr64 va_b4 va_s4 va_sM (va_op_dst_operand_reg R10)
    (va_const_shift_amt 2)) in
  let (va_b6, va_s6) = (va_lemma_And64 va_b5 va_s5 va_sM (va_op_dst_operand_reg Rbp)
    (va_const_operand 3)) in
  let (va_b7, va_s7) = (va_lemma_Add64Wrap va_b6 va_s6 va_sM (va_op_dst_operand_reg Rax)
    (va_op_operand_reg R10)) in
  let (va_b8, va_s8) = (va_lemma_Add64Wrap va_b7 va_s7 va_sM (va_op_dst_operand_reg R14)
    (va_op_operand_reg Rax)) in
  let (va_b9, va_s9) = (va_lemma_Adc64Wrap va_b8 va_s8 va_sM (va_op_dst_operand_reg Rbx)
    (va_const_operand 0)) in
  let (va_b10, va_s10) = (va_lemma_Adc64Wrap va_b9 va_s9 va_sM (va_op_dst_operand_reg Rbp)
    (va_const_operand 0)) in
  let rbx0 = (n `op_Multiply` (va_get_reg Rbx va_old_s) + (va_get_reg R14 va_old_s)) in
  let hh = (rbx0 + (va_get_reg Rax va_s10) + (va_get_reg R10 va_old_s) `op_Modulus` 4 `op_Multiply`
    (n `op_Multiply` n)) in
  (lemma_poly_reduce n p hd (va_get_reg R10 va_old_s) rbx0 (va_get_reg Rax va_s10) hh);
  let va_sM = (va_lemma_empty va_s10 va_sM) in
  (va_bM, va_sM, hh)
let va_lemma_poly1305_reduce_regs = va_irreducible_lemma_poly1305_reduce_regs

val va_transparent_code_poly1305_reduce_regs_fast_block : va_dummy:unit -> Tot va_code
let va_transparent_code_poly1305_reduce_regs_fast_block () =
  (va_Block (va_CCons (va_Block (va_CCons (va_code_And64 (va_op_dst_operand_reg Rax)
    (va_op_operand_reg R10)) (va_CCons (va_code_Mov64 (va_op_dst_operand_reg Rbp)
    (va_op_operand_reg R10)) (va_CCons (va_code_Shr64 (va_op_dst_operand_reg R10)
    (va_const_shift_amt 2)) (va_CCons (va_code_And64 (va_op_dst_operand_reg Rbp) (va_const_operand
    3)) (va_CCons (va_code_Add64Wrap (va_op_dst_operand_reg Rax) (va_op_operand_reg R10)) (va_CCons
    (va_code_Add64Wrap (va_op_dst_operand_reg R14) (va_op_operand_reg Rax)) (va_CCons
    (va_code_Adc64Wrap (va_op_dst_operand_reg Rbx) (va_const_operand 0)) (va_CCons
    (va_code_Adc64Wrap (va_op_dst_operand_reg Rbp) (va_const_operand 0)) (va_CNil ()))))))))))
    (va_CNil ())))
let va_code_poly1305_reduce_regs_fast_block () =
  (va_make_opaque (va_transparent_code_poly1305_reduce_regs_fast_block ()))

let va_ins_1_poly1305_reduce_regs_fast_block () =
  [(va_fast_ins_And64 (va_op_dst_operand_reg Rax) (va_op_operand_reg R10)); (va_fast_ins_Mov64
    (va_op_dst_operand_reg Rbp) (va_op_operand_reg R10)); (va_fast_ins_Shr64 (va_op_dst_operand_reg
    R10) (va_const_shift_amt 2)); (va_fast_ins_And64 (va_op_dst_operand_reg Rbp) (va_const_operand
    3)); (va_fast_ins_Add64Wrap (va_op_dst_operand_reg Rax) (va_op_operand_reg R10));
    (va_fast_ins_Add64Wrap (va_op_dst_operand_reg R14) (va_op_operand_reg Rax));
    (va_fast_ins_Adc64Wrap (va_op_dst_operand_reg Rbx) (va_const_operand 0));
    (va_fast_ins_Adc64Wrap (va_op_dst_operand_reg Rbp) (va_const_operand 0))]

irreducible val va_irreducible_lemma_poly1305_reduce_regs_fast_block : va_b0:va_codes ->
  va_s0:va_state -> va_sN:va_state -> hd:int -> p:int
  -> Ghost ((va_bM:va_codes) * (va_sM:va_state) * (hh:int))
  (requires ((va_require va_b0 (va_code_poly1305_reduce_regs_fast_block ()) va_s0 va_sN) /\
    (va_get_ok va_s0) /\ p == n `op_Multiply` n `op_Multiply` 4 - 5 /\ hd == n `op_Multiply` n
    `op_Multiply` (va_get_reg R10 va_s0) + n `op_Multiply` (va_get_reg Rbx va_s0) + (va_get_reg R14
    va_s0) /\ (va_get_reg R10 va_s0) `op_Division` 4 `op_Multiply` 4 + (va_get_reg R10 va_s0)
    `op_Division` 4 < 18446744073709551616 /\ (va_get_reg Rax va_s0) == 18446744073709551612))
  (ensures (fun ((va_bM:va_codes), (va_sM:va_state), (hh:int)) -> ((va_ensure va_b0 va_bM va_s0
    va_sM va_sN) /\ (va_get_ok va_sM) /\ p > 0 /\ hh == n `op_Multiply` n `op_Multiply` (va_get_reg
    Rbp va_sM) + n `op_Multiply` (va_get_reg Rbx va_sM) + (va_get_reg R14 va_sM) /\ hd `op_Modulus`
    p == hh `op_Modulus` p /\ (va_get_reg Rbp va_sM) < 5 /\ (va_state_eq va_sM (va_update_reg Rbp
    va_sM (va_update_reg Rbx va_sM (va_update_reg R14 va_sM (va_update_reg R10 va_sM
    (va_update_flags va_sM (va_update_reg Rax va_sM (va_update_ok va_sM va_s0)))))))))))
irreducible let va_irreducible_lemma_poly1305_reduce_regs_fast_block va_b0 va_s0 va_sN hd p =
  (va_reveal_opaque (va_transparent_code_poly1305_reduce_regs_fast_block ()));
  let (va_old_s:va_state) = va_s0 in
  let (va_sM, (va_cM:va_code), va_bM) = (va_lemma_block va_b0 va_s0 va_sN) in
  let (va_b1:va_codes) = (va_get_block va_cM) in
  (lemma_poly_bits64 ());
  let (va_s3, va_c3, va_b3) = (va_lemma_block va_b1 va_s0 va_sM) in
  (va_lemma_weakest_pre_norm (va_ins_1_poly1305_reduce_regs_fast_block ()) va_s0 va_s3);
  let rbx0 = (n `op_Multiply` (va_get_reg Rbx va_old_s) + (va_get_reg R14 va_old_s)) in
  let hh = (rbx0 + (va_get_reg Rax va_s3) + (va_get_reg R10 va_old_s) `op_Modulus` 4 `op_Multiply`
    (n `op_Multiply` n)) in
  (lemma_poly_reduce n p hd (va_get_reg R10 va_old_s) rbx0 (va_get_reg Rax va_s3) hh);
  let va_sM = (va_lemma_empty va_s3 va_sM) in
  (va_bM, va_sM, hh)
let va_lemma_poly1305_reduce_regs_fast_block = va_irreducible_lemma_poly1305_reduce_regs_fast_block

val va_transparent_code_poly1305_iteration : d1:va_dst_operand -> d2:va_dst_operand ->
  d3:va_dst_operand -> r0:va_operand -> s1:va_operand -> h0:va_dst_operand -> h1:va_dst_operand ->
  h2:va_dst_operand -> Tot va_code
let va_transparent_code_poly1305_iteration d1 d2 d3 r0 s1 h0 h1 h2 =
  (va_Block (va_CCons (va_code_poly1305_multiply ()) (va_CCons (va_code_poly1305_reduce d3 h0 h1
    h2) (va_CNil ()))))
let va_code_poly1305_iteration d1 d2 d3 r0 s1 h0 h1 h2 =
  (va_make_opaque (va_transparent_code_poly1305_iteration d1 d2 d3 r0 s1 h0 h1 h2))

irreducible val va_irreducible_lemma_poly1305_iteration : va_b0:va_codes -> va_s0:va_state ->
  va_sN:va_state -> d1:va_dst_operand -> d2:va_dst_operand -> d3:va_dst_operand -> r0:va_operand ->
  s1:va_operand -> h0:va_dst_operand -> h1:va_dst_operand -> h2:va_dst_operand -> r1:nat64
  -> Ghost ((va_bM:va_codes) * (va_sM:va_state) * (hh:int))
  (requires ((va_require va_b0 (va_code_poly1305_iteration d1 d2 d3 r0 s1 h0 h1 h2) va_s0 va_sN) /\
    (va_is_dst_dst_operand_uint64 d1 va_s0) /\ (va_is_dst_dst_operand_uint64 d2 va_s0) /\
    (va_is_dst_dst_operand_uint64 d3 va_s0) /\ (va_is_src_operand_uint64 r0 va_s0) /\
    (va_is_src_operand_uint64 s1 va_s0) /\ (va_is_dst_dst_operand_uint64 h0 va_s0) /\
    (va_is_dst_dst_operand_uint64 h1 va_s0) /\ (va_is_dst_dst_operand_uint64 h2 va_s0) /\
    (va_get_ok va_s0) /\ (let p = n `op_Multiply` n `op_Multiply` 4 - 5 in let r = r1 `op_Multiply`
    n + (va_eval_operand_uint64 va_s0 r0) in let h = (va_eval_dst_operand_uint64 va_s0 h2)
    `op_Multiply` (n `op_Multiply` n) + (va_eval_dst_operand_uint64 va_s0 h1) `op_Multiply` n +
    (va_eval_dst_operand_uint64 va_s0 h0) in d1 == (OReg R8) /\ d2 == (OReg R9) /\ d3 == (OReg R10)
    /\ r0 == (OReg R11) /\ s1 == (OReg R13) /\ h0 == (OReg R14) /\ h1 == (OReg Rbx) /\ h2 == (OReg
    Rbp)) /\ (let p = n `op_Multiply` n `op_Multiply` 4 - 5 in let r = r1 `op_Multiply` n +
    (va_eval_operand_uint64 va_s0 r0) in let h = (va_eval_dst_operand_uint64 va_s0 h2)
    `op_Multiply` (n `op_Multiply` n) + (va_eval_dst_operand_uint64 va_s0 h1) `op_Multiply` n +
    (va_eval_dst_operand_uint64 va_s0 h0) in (va_eval_operand_uint64 va_s0 r0) < n `op_Division` 16
    /\ r1 < n `op_Division` 16 /\ r1 `op_Modulus` 4 == 0 /\ (va_eval_operand_uint64 va_s0 s1) == r1
    + r1 `op_Division` 4 /\ (va_eval_dst_operand_uint64 va_s0 h2) < 7 /\ (va_get_reg Rax va_s0) ==
    r1)))
  (ensures (fun ((va_bM:va_codes), (va_sM:va_state), (hh:int)) -> ((va_ensure va_b0 va_bM va_s0
    va_sM va_sN) /\ (va_get_ok va_sM) /\ (let p = n `op_Multiply` n `op_Multiply` 4 - 5 in let r =
    r1 `op_Multiply` n + (va_eval_operand_uint64 va_s0 r0) in let h = (va_eval_dst_operand_uint64
    va_s0 h2) `op_Multiply` (n `op_Multiply` n) + (va_eval_dst_operand_uint64 va_s0 h1)
    `op_Multiply` n + (va_eval_dst_operand_uint64 va_s0 h0) in p > 0 /\ hh == n `op_Multiply` n
    `op_Multiply` (va_eval_dst_operand_uint64 va_sM h2) + n `op_Multiply`
    (va_eval_dst_operand_uint64 va_sM h1) + (va_eval_dst_operand_uint64 va_sM h0) /\ (modp (h
    `op_Multiply` r)) == (modp hh) /\ (va_eval_dst_operand_uint64 va_sM h2) < 5) /\ (va_state_eq
    va_sM (va_update_flags va_sM (va_update_reg Rdx va_sM (va_update_reg Rax va_sM (va_update_reg
    Rbp va_sM (va_update_reg Rbx va_sM (va_update_reg R14 va_sM (va_update_reg R10 va_sM
    (va_update_reg R9 va_sM (va_update_reg R8 va_sM (va_update_ok va_sM (va_update_dst_operand h2
    va_sM (va_update_dst_operand h1 va_sM (va_update_dst_operand h0 va_sM (va_update_dst_operand d3
    va_sM (va_update_dst_operand d2 va_sM (va_update_dst_operand d1 va_sM va_s0))))))))))))))))))))
irreducible let va_irreducible_lemma_poly1305_iteration va_b0 va_s0 va_sN d1 d2 d3 r0 s1 h0 h1 h2
  r1 =
  (va_reveal_opaque (va_transparent_code_poly1305_iteration d1 d2 d3 r0 s1 h0 h1 h2));
  let (va_old_s:va_state) = va_s0 in
  let (va_sM, (va_cM:va_code), va_bM) = (va_lemma_block va_b0 va_s0 va_sN) in
  let (va_b1:va_codes) = (va_get_block va_cM) in
  let p = (n `op_Multiply` n `op_Multiply` 4 - 5) in
  let r = (r1 `op_Multiply` n + (va_eval_operand_uint64 va_s0 r0)) in
  let h = ((va_eval_dst_operand_uint64 va_s0 h2) `op_Multiply` (n `op_Multiply` n) +
    (va_eval_dst_operand_uint64 va_s0 h1) `op_Multiply` n + (va_eval_dst_operand_uint64 va_s0 h0))
    in
  (lemma_mul_strict_upper_bound (va_eval_dst_operand_uint64 va_s0 h2) 7 (va_eval_operand_uint64
    va_s0 r0) (n `op_Division` 16));
  (lemma_mul_strict_upper_bound (va_eval_dst_operand_uint64 va_s0 h0) n r1 (n `op_Division` 16));
  (lemma_mul_strict_upper_bound (va_eval_dst_operand_uint64 va_s0 h1) n (va_eval_operand_uint64
    va_s0 r0) (n `op_Division` 16));
  (lemma_mul_strict_upper_bound (va_eval_dst_operand_uint64 va_s0 h2) n (va_eval_operand_uint64
    va_s0 s1) (n `op_Division` 8));
  (lemma_mul_strict_upper_bound (va_eval_dst_operand_uint64 va_s0 h0) n (va_eval_operand_uint64
    va_s0 r0) (n `op_Division` 16));
  (lemma_mul_strict_upper_bound (va_eval_dst_operand_uint64 va_s0 h1) n (va_eval_operand_uint64
    va_s0 s1) (n `op_Division` 8));
  (lemma_mul_strict_upper_bound (va_eval_dst_operand_uint64 va_s0 h2) 7 (va_eval_operand_uint64
    va_s0 s1) (5 `op_Multiply` n `op_Division` 64));
  let (va_b12, va_s12, hd) = (va_lemma_poly1305_multiply va_b1 va_s0 va_sM r1) in
  let (va_b14, va_s14, hh) = (va_lemma_poly1305_reduce va_b12 va_s12 va_sM d3 h0 h1 h2 hd p) in
  (reveal_opaque modp');
  assert (hh == n `op_Multiply` n `op_Multiply` (va_eval_dst_operand_uint64 va_s14 h2) + n
    `op_Multiply` (va_eval_dst_operand_uint64 va_s14 h1) + (va_eval_dst_operand_uint64 va_s14 h0)
    /\ h `op_Multiply` r `op_Modulus` p == hh `op_Modulus` p);
  let va_sM = (va_lemma_empty va_s14 va_sM) in
  (va_bM, va_sM, hh)
let va_lemma_poly1305_iteration = va_irreducible_lemma_poly1305_iteration
#reset-options "--z3rlimit 160"

val va_transparent_code_poly1305_blocks : va_dummy:unit -> Tot va_code
let va_transparent_code_poly1305_blocks () =
  (va_Block (va_CCons (va_Block (va_CCons (va_code_Shr64 (va_op_dst_operand_reg Rdx)
    (va_const_shift_amt 4)) (va_CCons (va_code_Mov64 (va_op_dst_operand_reg R15) (va_op_operand_reg
    Rdx)) (va_CCons (va_code_Load64 (va_op_dst_operand_reg R11) (va_op_reg_operand_reg Rdi) 24)
    (va_CCons (va_code_Load64 (va_op_dst_operand_reg R13) (va_op_reg_operand_reg Rdi) 32) (va_CCons
    (va_code_Load64 (va_op_dst_operand_reg R14) (va_op_reg_operand_reg Rdi) 0) (va_CCons
    (va_code_Load64 (va_op_dst_operand_reg Rbx) (va_op_reg_operand_reg Rdi) 8) (va_CCons
    (va_code_Load64 (va_op_dst_operand_reg Rbp) (va_op_reg_operand_reg Rdi) 16) (va_CCons
    (va_code_Mov64 (va_op_dst_operand_reg R12) (va_op_operand_reg R13)) (va_CCons (va_code_Shr64
    (va_op_dst_operand_reg R13) (va_const_shift_amt 2)) (va_CCons (va_code_Mov64
    (va_op_dst_operand_reg Rax) (va_op_operand_reg R12)) (va_CNil ())))))))))))) (va_CCons
    (va_code_Add64 (va_op_dst_operand_reg R13) (va_op_operand_reg R12)) (va_CCons (va_While
    (va_cmp_ne (va_op_cmp_reg R15) (va_const_cmp 0)) (va_Block (va_CCons (va_Block (va_CCons
    (va_code_Add64Wrap (va_op_dst_operand_reg R14) (va_opr_code_Mem (va_op_operand_reg Rsi) 0))
    (va_CCons (va_code_Adc64Wrap (va_op_dst_operand_reg Rbx) (va_opr_code_Mem (va_op_operand_reg
    Rsi) 8)) (va_CNil ())))) (va_CCons (va_code_AddLea64 (va_op_dst_operand_reg Rsi)
    (va_op_operand_reg Rsi) (va_const_operand 16)) (va_CCons (va_code_Adc64Wrap
    (va_op_dst_operand_reg Rbp) (va_op_operand_reg Rcx)) (va_CCons (va_code_poly1305_iteration
    (va_op_dst_operand_reg R8) (va_op_dst_operand_reg R9) (va_op_dst_operand_reg R10)
    (va_op_operand_reg R11) (va_op_operand_reg R13) (va_op_dst_operand_reg R14)
    (va_op_dst_operand_reg Rbx) (va_op_dst_operand_reg Rbp)) (va_CCons (va_code_Mov64
    (va_op_dst_operand_reg Rax) (va_op_operand_reg R12)) (va_CCons (va_code_Sub64
    (va_op_dst_operand_reg R15) (va_const_operand 1)) (va_CNil ()))))))))) (va_CCons
    (va_code_Store64 (va_op_reg_operand_reg Rdi) (va_op_operand_reg R14) 0) (va_CCons
    (va_code_Store64 (va_op_reg_operand_reg Rdi) (va_op_operand_reg Rbx) 8) (va_CCons
    (va_code_Store64 (va_op_reg_operand_reg Rdi) (va_op_operand_reg Rbp) 16) (va_CNil ()))))))))
let va_code_poly1305_blocks () =
  (va_make_opaque (va_transparent_code_poly1305_blocks ()))

let va_ins_1_poly1305_blocks () =
  [(va_fast_ins_Shr64 (va_op_dst_operand_reg Rdx) (va_const_shift_amt 4)); (va_fast_ins_Mov64
    (va_op_dst_operand_reg R15) (va_op_operand_reg Rdx)); (va_fast_ins_Load64
    (va_op_dst_operand_reg R11) (va_op_reg_operand_reg Rdi) 24); (va_fast_ins_Load64
    (va_op_dst_operand_reg R13) (va_op_reg_operand_reg Rdi) 32); (va_fast_ins_Load64
    (va_op_dst_operand_reg R14) (va_op_reg_operand_reg Rdi) 0); (va_fast_ins_Load64
    (va_op_dst_operand_reg Rbx) (va_op_reg_operand_reg Rdi) 8); (va_fast_ins_Load64
    (va_op_dst_operand_reg Rbp) (va_op_reg_operand_reg Rdi) 16); (va_fast_ins_Mov64
    (va_op_dst_operand_reg R12) (va_op_operand_reg R13)); (va_fast_ins_Shr64 (va_op_dst_operand_reg
    R13) (va_const_shift_amt 2)); (va_fast_ins_Mov64 (va_op_dst_operand_reg Rax) (va_op_operand_reg
    R12))]

let va_ins_2_poly1305_blocks () =
  [(va_fast_ins_Add64Wrap (va_op_dst_operand_reg R14) (va_opr_code_Mem (va_op_operand_reg Rsi) 0));
    (va_fast_ins_Adc64Wrap (va_op_dst_operand_reg Rbx) (va_opr_code_Mem (va_op_operand_reg Rsi) 8))]

irreducible val va_irreducible_lemma_poly1305_blocks : va_b0:va_codes -> va_s0:va_state ->
  va_sN:va_state -> r:int -> h_in:int
  -> Ghost ((va_bM:va_codes) * (va_sM:va_state) * (h:int))
  (requires ((va_require va_b0 (va_code_poly1305_blocks ()) va_s0 va_sN) /\ (let p = n
    `op_Multiply` n `op_Multiply` 4 - 5 in (va_get_ok va_s0)) /\ (let p = n `op_Multiply` n
    `op_Multiply` 4 - 5 in (va_get_reg Rdx va_s0) `op_Modulus` 16 == 0 /\ (va_get_reg Rsi va_s0) +
    (va_get_reg Rdx va_s0) < nat64_max /\ (disjoint (va_get_reg Rdi va_s0) (24 `op_Multiply` 8)
    (va_get_reg Rsi va_s0) (va_get_reg Rdx va_s0)) /\ (validSrcAddrs (va_get_mem va_s0) (va_get_reg
    Rdi va_s0) 64 (24 `op_Multiply` 8)) /\ (validSrcAddrs (va_get_mem va_s0) (va_get_reg Rsi va_s0)
    64 (va_get_reg Rdx va_s0)) /\ (let h0_in = (va_subscript (va_get_mem va_s0) ((va_get_reg Rdi
    va_s0) + 0)) in let h1_in = (va_subscript (va_get_mem va_s0) ((va_get_reg Rdi va_s0) + 8)) in
    let h2_in = (va_subscript (va_get_mem va_s0) ((va_get_reg Rdi va_s0) + 16)) in let r0_in =
    (va_subscript (va_get_mem va_s0) ((va_get_reg Rdi va_s0) + 24)) in let r1_in = (va_subscript
    (va_get_mem va_s0) ((va_get_reg Rdi va_s0) + 32)) in h_in == h2_in `op_Multiply` (n
    `op_Multiply` n) + h1_in `op_Multiply` n + h0_in /\ r == r1_in `op_Multiply` n + r0_in /\ r0_in
    < n `op_Division` 16 /\ r1_in < n `op_Division` 16 /\ r1_in `op_Modulus` 4 == 0 /\ h2_in < 5 /\
    (va_get_reg Rcx va_s0) < 2))))
  (ensures (fun ((va_bM:va_codes), (va_sM:va_state), (h:int)) -> ((va_ensure va_b0 va_bM va_s0
    va_sM va_sN) /\ (let p = n `op_Multiply` n `op_Multiply` 4 - 5 in (va_get_ok va_sM)) /\ (let p
    = n `op_Multiply` n `op_Multiply` 4 - 5 in (va_get_reg Rbp va_sM) < 5 /\ (validSrcAddrs
    (va_get_mem va_sM) (va_get_reg Rdi va_sM) 64 (24 `op_Multiply` 8)) /\ (validSrcAddrs
    (va_get_mem va_sM) (va_get_reg Rsi va_s0) 64 (va_get_reg Rdx va_s0)) /\ (memModified
    (va_get_mem va_s0) (va_get_mem va_sM) (va_get_reg Rdi va_s0) (3 `op_Multiply` 8)) /\
    (va_get_reg R14 va_sM) == (va_subscript (va_get_mem va_sM) ((va_get_reg Rdi va_sM) + 0)) /\
    (va_get_reg Rbx va_sM) == (va_subscript (va_get_mem va_sM) ((va_get_reg Rdi va_sM) + 8)) /\
    (va_get_reg Rbp va_sM) == (va_subscript (va_get_mem va_sM) ((va_get_reg Rdi va_sM) + 16)) /\
    (va_get_reg R11 va_sM) == (va_subscript (va_get_mem va_sM) ((va_get_reg Rdi va_sM) + 24)) /\
    (va_get_reg R12 va_sM) == (va_subscript (va_get_mem va_sM) ((va_get_reg Rdi va_sM) + 32)) /\
    (va_get_reg R13 va_sM) == (va_get_reg R12 va_sM) + (va_get_reg R12 va_sM) `op_Division` 4 /\
    (va_get_reg Rsi va_sM) == (va_get_reg Rsi va_s0) + (va_get_reg Rdx va_s0) /\ (va_get_reg Rcx
    va_sM) == (va_get_reg Rcx va_s0) /\ (va_get_reg Rdi va_sM) == (va_get_reg Rdi va_s0) /\ (forall
    i . (va_get_reg Rdi va_sM) + 24 <= i /\ i < (va_get_reg Rdi va_sM) + 24 `op_Multiply` 8 /\ (i -
    (va_get_reg Rdi va_sM)) `op_Modulus` 8 == 0 ==> (va_subscript (va_get_mem va_sM) i) ==
    (va_subscript (va_get_mem va_s0) i)) /\ (let r0_in = (va_subscript (va_get_mem va_sM)
    ((va_get_reg Rdi va_sM) + 24)) in let r1_in = (va_subscript (va_get_mem va_sM) ((va_get_reg Rdi
    va_sM) + 32)) in h == (va_get_reg Rbp va_sM) `op_Multiply` (nat64_max `op_Multiply` nat64_max)
    + (va_get_reg Rbx va_sM) `op_Multiply` nat64_max + (va_get_reg R14 va_sM) /\ ((va_get_reg Rsi
    va_s0) + (va_get_reg Rdx va_s0) - (va_get_reg Rsi va_s0)) `op_Modulus` 16 == 0 /\
    (validSrcAddrs (va_get_mem va_sM) (va_get_reg Rsi va_s0) 64 (va_get_reg Rdx va_s0)) /\ (modp h)
    == (poly1305_heap_blocks (modp h_in) ((va_get_reg Rcx va_sM) `op_Multiply` n `op_Multiply` n) r
    (va_get_mem va_sM) (va_get_reg Rsi va_s0) ((va_get_reg Rsi va_s0) + (va_get_reg Rdx
    va_s0))))))))
irreducible let va_irreducible_lemma_poly1305_blocks va_b0 va_s0 va_sN r h_in =
  (va_reveal_opaque (va_transparent_code_poly1305_blocks ()));
  let (va_old_s:va_state) = va_s0 in
  let (va_sM, (va_cM:va_code), va_bM) = (va_lemma_block va_b0 va_s0 va_sN) in
  let (va_b1:va_codes) = (va_get_block va_cM) in
  let p = (n `op_Multiply` n `op_Multiply` 4 - 5) in
  let h = 0 in
  (lemma_poly_bits64 ());
  let length = (va_get_reg Rdx va_s0) in
  let (va_s19, va_c19, va_b19) = (va_lemma_block va_b1 va_s0 va_sM) in
  (va_lemma_weakest_pre_norm (va_ins_1_poly1305_blocks ()) va_s0 va_s19);
  let (va_b20, va_s20) = (va_lemma_Add64 va_b19 va_s19 va_sM (va_op_dst_operand_reg R13)
    (va_op_operand_reg R12)) in
  let h = h_in in
  let va_forall_lemma () : Lemma
  (requires True)
  (ensures ((modp h) == (poly1305_heap_blocks (modp h_in) ((va_get_reg Rcx va_s20) `op_Multiply` n
    `op_Multiply` n) r (va_get_mem va_s20) (va_get_reg Rsi va_old_s) (va_get_reg Rsi va_s20))))
  =
  (
    (reveal_opaque modp');
    (reveal_poly1305_heap_blocks (modp h_in) ((va_get_reg Rcx va_s20) `op_Multiply` n `op_Multiply`
      n) r (va_get_mem va_s20) (va_get_reg Rsi va_old_s) (va_get_reg Rsi va_s20));
    ()
  ) in va_forall_lemma ();
  let (va_s23, va_c23, va_b23) = (va_lemma_block va_b20 va_s20 va_sM) in
  let va_sC24 = (va_get_whileCond va_c23) in
  let va_sB24 = (va_get_whileBody va_c23) in
  let ((va_n24:va_int), (va_sW24:va_state)) = (va_lemma_while va_sC24 va_sB24 va_s20 va_s23) in
  let ((h:int), (va_n24:va_int), (va_sW24:va_state)) =
  (
    let rec va_while (h:int) (va_n24:va_int) (va_sW24:va_state) : Ghost ((h:int) * (va_n24:va_int)
      * (va_sW24:va_state))
      (requires ((va_whileInv va_sC24 va_sB24 va_n24 va_sW24 va_s23) /\ (va_get_ok va_sW24) /\ n ==
        18446744073709551616 /\ r == (va_get_reg R12 va_sW24) `op_Multiply` n + (va_get_reg R11
        va_sW24) /\ h == (va_get_reg Rbp va_sW24) `op_Multiply` (nat64_max `op_Multiply` nat64_max)
        + (va_get_reg Rbx va_sW24) `op_Multiply` nat64_max + (va_get_reg R14 va_sW24) /\
        (va_get_reg R11 va_sW24) < n `op_Division` 16 /\ (va_get_reg R12 va_sW24) < n `op_Division`
        16 /\ (va_get_reg R12 va_sW24) `op_Modulus` 4 == 0 /\ (va_get_reg R13 va_sW24) ==
        (va_get_reg R12 va_sW24) + (va_get_reg R12 va_sW24) `op_Division` 4 /\ (va_get_reg Rbp
        va_sW24) < 5 /\ (va_get_reg Rax va_sW24) == (va_get_reg R12 va_sW24) /\ (va_get_reg Rsi
        va_sW24) + 16 `op_Multiply` (va_get_reg R15 va_sW24) == (va_get_reg Rsi va_old_s) + length
        /\ length == (va_get_reg Rdx va_old_s) /\ (va_get_reg R15 va_sW24) `op_Multiply` 16 <=
        length /\ (va_get_reg Rcx va_sW24) < 2 /\ (validSrcAddrs (va_get_mem va_sW24) (va_get_reg
        Rdi va_sW24) 64 (24 `op_Multiply` 8)) /\ (validSrcAddrs (va_get_mem va_sW24) (va_get_reg
        Rsi va_old_s) 64 length) /\ (va_get_reg Rdi va_sW24) == (va_get_reg Rdi va_old_s) /\
        (va_get_reg Rcx va_sW24) == (va_get_reg Rcx va_old_s) /\ (forall i . ((va_get_reg Rdi
        va_sW24) + 24 <= i /\ i < (va_get_reg Rdi va_sW24) + 24 `op_Multiply` 8) /\ (i -
        (va_get_reg Rdi va_sW24)) `op_Modulus` 8 == 0 ==> (va_subscript (va_get_mem va_sW24) i) ==
        (va_subscript (va_get_mem va_old_s) i)) /\ ((va_get_reg Rsi va_sW24) - (va_get_reg Rsi
        va_old_s)) `op_Modulus` 16 == 0 /\ (validSrcAddrs (va_get_mem va_sW24) (va_get_reg Rsi
        va_old_s) 64 ((va_get_reg Rsi va_sW24) - (va_get_reg Rsi va_old_s))) /\ (modp h) ==
        (poly1305_heap_blocks (modp h_in) ((va_get_reg Rcx va_sW24) `op_Multiply` n `op_Multiply`
        n) r (va_get_mem va_sW24) (va_get_reg Rsi va_old_s) (va_get_reg Rsi va_sW24)) /\
        (memModified (va_get_mem va_old_s) (va_get_mem va_sW24) (va_get_reg Rdi va_old_s) (3
        `op_Multiply` 8))))
      (ensures (fun (h, va_n24, va_sW24) -> ((va_whileInv va_sC24 va_sB24 va_n24 va_sW24 va_s23) /\
        (va_get_ok va_sW24) /\ n == 18446744073709551616 /\ r == (va_get_reg R12 va_sW24)
        `op_Multiply` n + (va_get_reg R11 va_sW24) /\ h == (va_get_reg Rbp va_sW24) `op_Multiply`
        (nat64_max `op_Multiply` nat64_max) + (va_get_reg Rbx va_sW24) `op_Multiply` nat64_max +
        (va_get_reg R14 va_sW24) /\ (va_get_reg R11 va_sW24) < n `op_Division` 16 /\ (va_get_reg
        R12 va_sW24) < n `op_Division` 16 /\ (va_get_reg R12 va_sW24) `op_Modulus` 4 == 0 /\
        (va_get_reg R13 va_sW24) == (va_get_reg R12 va_sW24) + (va_get_reg R12 va_sW24)
        `op_Division` 4 /\ (va_get_reg Rbp va_sW24) < 5 /\ (va_get_reg Rax va_sW24) == (va_get_reg
        R12 va_sW24) /\ (va_get_reg Rsi va_sW24) + 16 `op_Multiply` (va_get_reg R15 va_sW24) ==
        (va_get_reg Rsi va_old_s) + length /\ length == (va_get_reg Rdx va_old_s) /\ (va_get_reg
        R15 va_sW24) `op_Multiply` 16 <= length /\ (va_get_reg Rcx va_sW24) < 2 /\ (validSrcAddrs
        (va_get_mem va_sW24) (va_get_reg Rdi va_sW24) 64 (24 `op_Multiply` 8)) /\ (validSrcAddrs
        (va_get_mem va_sW24) (va_get_reg Rsi va_old_s) 64 length) /\ (va_get_reg Rdi va_sW24) ==
        (va_get_reg Rdi va_old_s) /\ (va_get_reg Rcx va_sW24) == (va_get_reg Rcx va_old_s) /\
        (forall i . ((va_get_reg Rdi va_sW24) + 24 <= i /\ i < (va_get_reg Rdi va_sW24) + 24
        `op_Multiply` 8) /\ (i - (va_get_reg Rdi va_sW24)) `op_Modulus` 8 == 0 ==> (va_subscript
        (va_get_mem va_sW24) i) == (va_subscript (va_get_mem va_old_s) i)) /\ ((va_get_reg Rsi
        va_sW24) - (va_get_reg Rsi va_old_s)) `op_Modulus` 16 == 0 /\ (validSrcAddrs (va_get_mem
        va_sW24) (va_get_reg Rsi va_old_s) 64 ((va_get_reg Rsi va_sW24) - (va_get_reg Rsi
        va_old_s))) /\ (modp h) == (poly1305_heap_blocks (modp h_in) ((va_get_reg Rcx va_sW24)
        `op_Multiply` n `op_Multiply` n) r (va_get_mem va_sW24) (va_get_reg Rsi va_old_s)
        (va_get_reg Rsi va_sW24)) /\ (memModified (va_get_mem va_old_s) (va_get_mem va_sW24)
        (va_get_reg Rdi va_old_s) (3 `op_Multiply` 8)))))
      (decreases ((va_get_reg R15 va_sW24)))
      =
      if (va_n24 > 0) then
        let (h, va_n24, va_sW24):(int * va_int * va_state) =
        (
          let ((va_s24:va_state), (va_sW25:va_state)) = (va_lemma_whileTrue va_sC24 va_sB24 va_n24
            va_sW24 va_s23) in
          let va_b26 = (va_get_block va_sB24) in
          let hp = h in
          let old_mem = (va_get_mem va_s24) in
          let h = (h + n `op_Multiply` n `op_Multiply` (va_get_reg Rcx va_s24) + n `op_Multiply`
            (va_subscript (va_get_mem va_s24) ((va_get_reg Rsi va_s24) + 8)) + (va_subscript
            (va_get_mem va_s24) (va_get_reg Rsi va_s24))) in
          let hq = h in
          let (va_s31, va_c31, va_b31) = (va_lemma_block va_b26 va_s24 va_sW25) in
          (va_lemma_weakest_pre_norm (va_ins_2_poly1305_blocks ()) va_s24 va_s31);
          let (va_b32, va_s32) = (va_lemma_AddLea64 va_b31 va_s31 va_sW25 (va_op_dst_operand_reg
            Rsi) (va_op_operand_reg Rsi) (va_const_operand 16)) in
          let (va_b33, va_s33) = (va_lemma_Adc64Wrap va_b32 va_s32 va_sW25 (va_op_dst_operand_reg
            Rbp) (va_op_operand_reg Rcx)) in
          let old_h = ((va_get_reg Rbp va_s33) `op_Multiply` (n `op_Multiply` n) + (va_get_reg Rbx
            va_s33) `op_Multiply` n + (va_get_reg R14 va_s33)) in
          assert (old_h == hq);
          let (va_b36, va_s36, h) = (va_lemma_poly1305_iteration va_b33 va_s33 va_sW25
            (va_op_dst_operand_reg R8) (va_op_dst_operand_reg R9) (va_op_dst_operand_reg R10)
            (va_op_operand_reg R11) (va_op_operand_reg R13) (va_op_dst_operand_reg R14)
            (va_op_dst_operand_reg Rbx) (va_op_dst_operand_reg Rbp) (va_get_reg R12 va_s33)) in
          let (va_b38, va_s38) = (va_lemma_Mov64 va_b36 va_s36 va_sW25 (va_op_dst_operand_reg Rax)
            (va_op_operand_reg R12)) in
          let (va_b39, va_s39) = (va_lemma_Sub64 va_b38 va_s38 va_sW25 (va_op_dst_operand_reg R15)
            (va_const_operand 1)) in
          let va_forall_lemma () : Lemma
          (requires True)
          (ensures ((modp h) == (poly1305_heap_blocks (modp h_in) ((va_get_reg Rcx va_s39)
            `op_Multiply` n `op_Multiply` n) r (va_get_mem va_s39) (va_get_reg Rsi va_old_s)
            (va_get_reg Rsi va_s39))))
          =
          (
            (reveal_poly1305_heap_blocks (modp h_in) ((va_get_reg Rcx va_s39) `op_Multiply` n
              `op_Multiply` n) r (va_get_mem va_s39) (va_get_reg Rsi va_old_s) (va_get_reg Rsi
              va_s39));
            (reveal_poly1305_heap_blocks (modp h_in) ((va_get_reg Rcx va_s39) `op_Multiply` n
              `op_Multiply` n) r (va_get_mem va_s39) (va_get_reg Rsi va_old_s) ((va_get_reg Rsi
              va_s39) - 16));
            (reveal_opaque modp');
            (lemma_poly_demod p hp (hq - hp) r);
            ()
          ) in va_forall_lemma ();
          let va_sW25 = (va_lemma_empty va_s39 va_sW25) in
          let va_sW24 = va_sW25 in
          let va_n24 = (va_n24 - 1) in
          (h, va_n24, va_sW24)
        )
        in va_while h va_n24 va_sW24
      else (h, va_n24, va_sW24)
    in va_while h va_n24 va_sW24
  ) in
  let va_s23 = (va_lemma_whileFalse va_sC24 va_sB24 va_sW24 va_s23) in
  (lemma_heap_blocks_preserved (va_get_mem va_s23) (modp h_in) ((va_get_reg Rcx va_s23)
    `op_Multiply` n `op_Multiply` n) r (va_get_reg Rdi va_s23) (24 `op_Multiply` 8) (va_get_reg Rsi
    va_old_s) (va_get_reg Rsi va_s23));
  let (va_b42, va_s42) = (va_lemma_Store64 va_b23 va_s23 va_sM (va_op_reg_operand_reg Rdi)
    (va_op_operand_reg R14) 0) in
  let (va_b43, va_s43) = (va_lemma_Store64 va_b42 va_s42 va_sM (va_op_reg_operand_reg Rdi)
    (va_op_operand_reg Rbx) 8) in
  let (va_b44, va_s44) = (va_lemma_Store64 va_b43 va_s43 va_sM (va_op_reg_operand_reg Rdi)
    (va_op_operand_reg Rbp) 16) in
  let va_sM = (va_lemma_empty va_s44 va_sM) in
  (va_bM, va_sM, h)
let va_lemma_poly1305_blocks = va_irreducible_lemma_poly1305_blocks
#reset-options "--z3rlimit 200"

val va_transparent_code_poly1305_last_block : h0:va_dst_operand -> h1:va_dst_operand ->
  h2:va_dst_operand -> r0:va_operand -> s1:va_operand -> nExtra:va_operand -> Tot va_code
let va_transparent_code_poly1305_last_block h0 h1 h2 r0 s1 nExtra =
  (va_Block (va_CCons (va_IfElse (va_cmp_lt (va_coerce_operand_to_cmp nExtra) (va_const_cmp 8))
    (va_Block (va_CCons (va_code_Mov64 (va_op_dst_operand_reg Rcx) nExtra) (va_CCons (va_code_Shl64
    (va_op_dst_operand_reg Rcx) (va_const_shift_amt 3)) (va_CCons (va_code_Mov64
    (va_op_dst_operand_reg Rdx) (va_const_operand 1)) (va_CCons (va_code_Shl64
    (va_op_dst_operand_reg Rdx) (va_op_shift_amt_reg Rcx)) (va_CCons (va_code_Mov64
    (va_op_dst_operand_reg Rcx) (va_op_operand_reg Rdx)) (va_CCons (va_code_Sub64
    (va_op_dst_operand_reg Rcx) (va_const_operand 1)) (va_CCons (va_code_And64
    (va_op_dst_operand_reg R8) (va_op_operand_reg Rcx)) (va_CCons (va_code_Mov64
    (va_op_dst_operand_reg R9) (va_const_operand 0)) (va_CCons (va_code_Add64Wrap h0
    (va_op_operand_reg R8)) (va_CCons (va_code_Adc64Wrap h1 (va_op_operand_reg R9)) (va_CCons
    (va_code_Adc64Wrap h2 (va_const_operand 0)) (va_CCons (va_code_Add64Wrap h0 (va_op_operand_reg
    Rdx)) (va_CCons (va_code_Adc64Wrap h1 (va_const_operand 0)) (va_CCons (va_code_Adc64Wrap h2
    (va_const_operand 0)) (va_CNil ())))))))))))))))) (va_Block (va_CCons (va_code_Mov64
    (va_op_dst_operand_reg Rcx) nExtra) (va_CCons (va_code_Sub64 (va_op_dst_operand_reg Rcx)
    (va_const_operand 8)) (va_CCons (va_code_Shl64 (va_op_dst_operand_reg Rcx) (va_const_shift_amt
    3)) (va_CCons (va_code_Mov64 (va_op_dst_operand_reg Rdx) (va_const_operand 1)) (va_CCons
    (va_code_Shl64 (va_op_dst_operand_reg Rdx) (va_op_shift_amt_reg Rcx)) (va_CCons (va_code_Mov64
    (va_op_dst_operand_reg Rcx) (va_op_operand_reg Rdx)) (va_CCons (va_code_Sub64
    (va_op_dst_operand_reg Rcx) (va_const_operand 1)) (va_CCons (va_code_And64
    (va_op_dst_operand_reg R9) (va_op_operand_reg Rcx)) (va_CCons (va_code_Add64Wrap h0
    (va_op_operand_reg R8)) (va_CCons (va_code_Adc64Wrap h1 (va_op_operand_reg R9)) (va_CCons
    (va_code_Adc64Wrap h2 (va_const_operand 0)) (va_CCons (va_code_Add64Wrap h0 (va_const_operand
    0)) (va_CCons (va_code_Adc64Wrap h1 (va_op_operand_reg Rdx)) (va_CCons (va_code_Adc64Wrap h2
    (va_const_operand 0)) (va_CNil ()))))))))))))))))) (va_CCons (va_code_poly1305_iteration
    (va_op_dst_operand_reg R8) (va_op_dst_operand_reg R9) (va_op_dst_operand_reg R10) r0 s1 h0 h1
    h2) (va_CNil ()))))
let va_code_poly1305_last_block h0 h1 h2 r0 s1 nExtra =
  (va_make_opaque (va_transparent_code_poly1305_last_block h0 h1 h2 r0 s1 nExtra))

irreducible val va_irreducible_lemma_poly1305_last_block : va_b0:va_codes -> va_s0:va_state ->
  va_sN:va_state -> h0:va_dst_operand -> h1:va_dst_operand -> h2:va_dst_operand -> r0:va_operand ->
  s1:va_operand -> nExtra:va_operand -> hBlocks:int -> r1:nat64 -> r:int -> inpLast:nat128 -> p:int
  -> Ghost ((va_bM:va_codes) * (va_sM:va_state))
  (requires ((va_require va_b0 (va_code_poly1305_last_block h0 h1 h2 r0 s1 nExtra) va_s0 va_sN) /\
    (va_is_dst_dst_operand_uint64 h0 va_s0) /\ (va_is_dst_dst_operand_uint64 h1 va_s0) /\
    (va_is_dst_dst_operand_uint64 h2 va_s0) /\ (va_is_src_operand_uint64 r0 va_s0) /\
    (va_is_src_operand_uint64 s1 va_s0) /\ (va_is_src_operand_uint64 nExtra va_s0) /\ (va_get_ok
    va_s0) /\ h0 == (OReg R14) /\ h1 == (OReg Rbx) /\ h2 == (OReg Rbp) /\ r0 == (OReg R11) /\ s1 ==
    (OReg R13) /\ nExtra == (OReg R15) /\ p == n `op_Multiply` n `op_Multiply` 4 - 5 /\
    (va_eval_dst_operand_uint64 va_s0 h2) < 5 /\ hBlocks == (lowerUpper192_opaque
    (lowerUpper128_opaque (va_eval_dst_operand_uint64 va_s0 h0) (va_eval_dst_operand_uint64 va_s0
    h1)) (va_eval_dst_operand_uint64 va_s0 h2)) /\ r == (lowerUpper128_opaque
    (va_eval_operand_uint64 va_s0 r0) r1) /\ (va_get_reg Rax va_s0) == r1 /\
    (va_eval_operand_uint64 va_s0 r0) < n `op_Division` 16 /\ r1 < n `op_Division` 16 /\ r1
    `op_Modulus` 4 == 0 /\ (va_eval_operand_uint64 va_s0 s1) == r1 + r1 `op_Division` 4 /\ inpLast
    == (lowerUpper128_opaque (va_get_reg R8 va_s0) (va_get_reg R9 va_s0)) /\ (1 <=
    (va_eval_operand_uint64 va_s0 nExtra) /\ (va_eval_operand_uint64 va_s0 nExtra) < 16)))
  (ensures (fun ((va_bM:va_codes), (va_sM:va_state)) -> ((va_ensure va_b0 va_bM va_s0 va_sM va_sN)
    /\ (va_get_ok va_sM) /\ (va_eval_dst_operand_uint64 va_sM h2) < 5 /\ (let padLast = (pow2
    ((va_eval_operand_uint64 va_sM nExtra) `op_Multiply` 8)) in let hLast = (lowerUpper192_opaque
    (lowerUpper128_opaque (va_eval_dst_operand_uint64 va_sM h0) (va_eval_dst_operand_uint64 va_sM
    h1)) (va_eval_dst_operand_uint64 va_sM h2)) in (modp hLast) == (modp (((modp hBlocks) + padLast
    + inpLast `op_Modulus` padLast) `op_Multiply` r))) /\ (va_state_eq va_sM (va_update_flags va_sM
    (va_update_reg R9 va_sM (va_update_reg Rdx va_sM (va_update_reg Rcx va_sM (va_update_reg Rax
    va_sM (va_update_reg Rbp va_sM (va_update_reg Rbx va_sM (va_update_reg R14 va_sM (va_update_reg
    R10 va_sM (va_update_reg R9 va_sM (va_update_reg R8 va_sM (va_update_ok va_sM
    (va_update_dst_operand h2 va_sM (va_update_dst_operand h1 va_sM (va_update_dst_operand h0 va_sM
    va_s0)))))))))))))))))))
irreducible let va_irreducible_lemma_poly1305_last_block va_b0 va_s0 va_sN h0 h1 h2 r0 s1 nExtra
  hBlocks r1 r inpLast p =
  (va_reveal_opaque (va_transparent_code_poly1305_last_block h0 h1 h2 r0 s1 nExtra));
  let (va_old_s:va_state) = va_s0 in
  let (va_sM, (va_cM:va_code), va_bM) = (va_lemma_block va_b0 va_s0 va_sN) in
  let (va_b1:va_codes) = (va_get_block va_cM) in
  let padLast = (pow2 ((va_eval_operand_uint64 va_s0 nExtra) `op_Multiply` 8)) in
  let (va_s3, va_c3, va_b3) = (va_lemma_block va_b1 va_s0 va_sM) in
  let (va_cond_c3, (va_s4:va_state)) = (va_lemma_ifElse (va_get_ifCond va_c3) (va_get_ifTrue va_c3)
    (va_get_ifFalse va_c3) va_s0 va_s3) in
  let (va_s3) =
  (
    if va_cond_c3 then
    (
      let va_b5 = (va_get_block (va_get_ifTrue va_c3)) in
      (lemma_bytes_shift_power2 (va_eval_operand_uint64 va_s4 nExtra));
      let (va_b7, va_s7) = (va_lemma_Mov64 va_b5 va_s4 va_s3 (va_op_dst_operand_reg Rcx) nExtra) in
      let (va_b8, va_s8) = (va_lemma_Shl64 va_b7 va_s7 va_s3 (va_op_dst_operand_reg Rcx)
        (va_const_shift_amt 3)) in
      let (va_b9, va_s9) = (va_lemma_Mov64 va_b8 va_s8 va_s3 (va_op_dst_operand_reg Rdx)
        (va_const_operand 1)) in
      let (va_b10, va_s10) = (va_lemma_Shl64 va_b9 va_s9 va_s3 (va_op_dst_operand_reg Rdx)
        (va_op_shift_amt_reg Rcx)) in
      assert ((va_get_reg Rdx va_s10) == padLast);
      (lemma_bytes_and_mod (va_get_reg R8 va_s10) (va_eval_operand_uint64 va_s10 nExtra));
      assert ((logand64 (va_get_reg R8 va_s10) ((shift_left64 1 (shift_left64
        (va_eval_operand_uint64 va_s10 nExtra) 3)) - 1)) == (va_get_reg R8 va_s10) `op_Modulus`
        (shift_left64 1 (shift_left64 (va_eval_operand_uint64 va_s10 nExtra) 3)));
      assert (padLast == (shift_left64 1 (shift_left64 (va_eval_operand_uint64 va_s10 nExtra) 3)));
      (lemma_mod_power2_lo (va_get_reg R8 va_s10) (va_get_reg R9 va_s10) (va_eval_operand_uint64
        va_s10 nExtra) (pow2 ((va_eval_operand_uint64 va_s10 nExtra) `op_Multiply` 8)));
      let (va_b16, va_s16) = (va_lemma_Mov64 va_b10 va_s10 va_s3 (va_op_dst_operand_reg Rcx)
        (va_op_operand_reg Rdx)) in
      let (va_b17, va_s17) = (va_lemma_Sub64 va_b16 va_s16 va_s3 (va_op_dst_operand_reg Rcx)
        (va_const_operand 1)) in
      let (va_b18, va_s18) = (va_lemma_And64 va_b17 va_s17 va_s3 (va_op_dst_operand_reg R8)
        (va_op_operand_reg Rcx)) in
      let (va_b19, va_s19) = (va_lemma_Mov64 va_b18 va_s18 va_s3 (va_op_dst_operand_reg R9)
        (va_const_operand 0)) in
      assert ((va_get_reg R8 va_s19) == (va_get_reg R8 va_old_s) `op_Modulus` padLast);
      assert ((lowerUpper128_opaque (va_get_reg R8 va_s19) (va_get_reg R9 va_s19)) == inpLast
        `op_Modulus` padLast);
      let (va_b22, va_s22) = (va_lemma_Add64Wrap va_b19 va_s19 va_s3 h0 (va_op_operand_reg R8)) in
      let (va_b23, va_s23) = (va_lemma_Adc64Wrap va_b22 va_s22 va_s3 h1 (va_op_operand_reg R9)) in
      let (va_b24, va_s24) = (va_lemma_Adc64Wrap va_b23 va_s23 va_s3 h2 (va_const_operand 0)) in
      let (va_b25, va_s25) = (va_lemma_Add64Wrap va_b24 va_s24 va_s3 h0 (va_op_operand_reg Rdx)) in
      let (va_b26, va_s26) = (va_lemma_Adc64Wrap va_b25 va_s25 va_s3 h1 (va_const_operand 0)) in
      let (va_b27, va_s27) = (va_lemma_Adc64Wrap va_b26 va_s26 va_s3 h2 (va_const_operand 0)) in
      let va_s3 = (va_lemma_empty va_s27 va_s3) in
      (va_s3)
    )
    else
    (
      let va_b28 = (va_get_block (va_get_ifFalse va_c3)) in
      (lemma_bytes_shift_power2 ((va_eval_operand_uint64 va_s4 nExtra) - 8));
      let (va_b30, va_s30) = (va_lemma_Mov64 va_b28 va_s4 va_s3 (va_op_dst_operand_reg Rcx) nExtra)
        in
      let (va_b31, va_s31) = (va_lemma_Sub64 va_b30 va_s30 va_s3 (va_op_dst_operand_reg Rcx)
        (va_const_operand 8)) in
      let (va_b32, va_s32) = (va_lemma_Shl64 va_b31 va_s31 va_s3 (va_op_dst_operand_reg Rcx)
        (va_const_shift_amt 3)) in
      let (va_b33, va_s33) = (va_lemma_Mov64 va_b32 va_s32 va_s3 (va_op_dst_operand_reg Rdx)
        (va_const_operand 1)) in
      let (va_b34, va_s34) = (va_lemma_Shl64 va_b33 va_s33 va_s3 (va_op_dst_operand_reg Rdx)
        (va_op_shift_amt_reg Rcx)) in
      let va_forall_lemma () : Lemma
      (requires True)
      (ensures (padLast == (lowerUpper128_opaque 0 (va_get_reg Rdx va_s34))))
      =
      (
        (lemma_power2_add64 (8 `op_Multiply` (va_eval_operand_uint64 va_s34 nExtra) - 64));
        (reveal_opaque lowerUpper128);
        ()
      ) in va_forall_lemma ();
      (lemma_bytes_and_mod (va_get_reg R9 va_s34) ((va_eval_operand_uint64 va_s34 nExtra) - 8));
      (lemma_mod_hi (va_get_reg R8 va_s34) (va_get_reg R9 va_s34) (pow2 (8 `op_Multiply`
        ((va_eval_operand_uint64 va_s34 nExtra) - 8))));
      let (va_b38, va_s38) = (va_lemma_Mov64 va_b34 va_s34 va_s3 (va_op_dst_operand_reg Rcx)
        (va_op_operand_reg Rdx)) in
      let (va_b39, va_s39) = (va_lemma_Sub64 va_b38 va_s38 va_s3 (va_op_dst_operand_reg Rcx)
        (va_const_operand 1)) in
      let (va_b40, va_s40) = (va_lemma_And64 va_b39 va_s39 va_s3 (va_op_dst_operand_reg R9)
        (va_op_operand_reg Rcx)) in
      assert ((lowerUpper128_opaque (va_get_reg R8 va_s40) (va_get_reg R9 va_s40)) == inpLast
        `op_Modulus` padLast);
      let (va_b42, va_s42) = (va_lemma_Add64Wrap va_b40 va_s40 va_s3 h0 (va_op_operand_reg R8)) in
      let (va_b43, va_s43) = (va_lemma_Adc64Wrap va_b42 va_s42 va_s3 h1 (va_op_operand_reg R9)) in
      let (va_b44, va_s44) = (va_lemma_Adc64Wrap va_b43 va_s43 va_s3 h2 (va_const_operand 0)) in
      let (va_b45, va_s45) = (va_lemma_Add64Wrap va_b44 va_s44 va_s3 h0 (va_const_operand 0)) in
      let (va_b46, va_s46) = (va_lemma_Adc64Wrap va_b45 va_s45 va_s3 h1 (va_op_operand_reg Rdx)) in
      let (va_b47, va_s47) = (va_lemma_Adc64Wrap va_b46 va_s46 va_s3 h2 (va_const_operand 0)) in
      let va_s3 = (va_lemma_empty va_s47 va_s3) in
      (va_s3)
    )
  ) in
  let h = (hBlocks + inpLast `op_Modulus` padLast + padLast) in
  let va_forall_lemma () : Lemma
  (requires True)
  (ensures (h == (va_eval_dst_operand_uint64 va_s3 h2) `op_Multiply` (n `op_Multiply` n) +
    (va_eval_dst_operand_uint64 va_s3 h1) `op_Multiply` n + (va_eval_dst_operand_uint64 va_s3 h0)))
  =
  (
    (reveal_opaque lowerUpper192);
    (reveal_opaque lowerUpper128);
    ()
  ) in va_forall_lemma ();
  let va_forall_lemma () : Lemma
  (requires True)
  (ensures (r == r1 `op_Multiply` n + (va_eval_operand_uint64 va_s3 r0)))
  =
  (
    (reveal_opaque lowerUpper128);
    ()
  ) in va_forall_lemma ();
  let (va_b51, va_s51, hLast) = (va_lemma_poly1305_iteration va_b3 va_s3 va_sM
    (va_op_dst_operand_reg R8) (va_op_dst_operand_reg R9) (va_op_dst_operand_reg R10) r0 s1 h0 h1
    h2 r1) in
  let va_forall_lemma () : Lemma
  (requires True)
  (ensures (hLast == (lowerUpper192_opaque (lowerUpper128_opaque (va_eval_dst_operand_uint64 va_s51
    h0) (va_eval_dst_operand_uint64 va_s51 h1)) (va_eval_dst_operand_uint64 va_s51 h2))))
  =
  (
    (reveal_opaque lowerUpper192);
    (reveal_opaque lowerUpper128);
    ()
  ) in va_forall_lemma ();
  (lemma_poly_demod p hBlocks (inpLast `op_Modulus` padLast + padLast) r);
  let va_forall_lemma () : Lemma
  (requires True)
  (ensures ((modp hLast) == (modp (((modp hBlocks) + padLast + inpLast `op_Modulus` padLast)
    `op_Multiply` r))))
  =
  (
    (reveal_opaque modp');
    ()
  ) in va_forall_lemma ();
  let va_sM = (va_lemma_empty va_s51 va_sM) in
  (va_bM, va_sM)
let va_lemma_poly1305_last_block = va_irreducible_lemma_poly1305_last_block
#reset-options "--z3rlimit 20"

val va_transparent_code_poly1305_reduce_last : h0:va_dst_operand -> h1:va_dst_operand ->
  h2:va_operand -> Tot va_code
let va_transparent_code_poly1305_reduce_last h0 h1 h2 =
  (va_Block (va_CCons (va_code_Mov64 (va_op_dst_operand_reg R8) (va_coerce_dst_operand_to_operand
    h0)) (va_CCons (va_code_Mov64 (va_op_dst_operand_reg R9) (va_coerce_dst_operand_to_operand h1))
    (va_CCons (va_code_Mov64 (va_op_dst_operand_reg R10) h2) (va_CCons (va_code_Add64Wrap
    (va_op_dst_operand_reg R8) (va_const_operand 5)) (va_CCons (va_code_Adc64Wrap
    (va_op_dst_operand_reg R9) (va_const_operand 0)) (va_CCons (va_code_Adc64Wrap
    (va_op_dst_operand_reg R10) (va_const_operand 0)) (va_CCons (va_code_Shr64
    (va_op_dst_operand_reg R10) (va_const_shift_amt 2)) (va_CCons (va_code_Mov64
    (va_op_dst_operand_reg Rax) (va_op_operand_reg R10)) (va_CCons (va_code_Sub64Wrap
    (va_op_dst_operand_reg Rax) (va_const_operand 1)) (va_CCons (va_code_And64 h0
    (va_op_operand_reg Rax)) (va_CCons (va_code_And64 h1 (va_op_operand_reg Rax)) (va_CCons
    (va_code_Mov64 (va_op_dst_operand_reg Rax) (va_const_operand 0)) (va_CCons (va_code_Sub64Wrap
    (va_op_dst_operand_reg Rax) (va_op_operand_reg R10)) (va_CCons (va_code_And64
    (va_op_dst_operand_reg R8) (va_op_operand_reg Rax)) (va_CCons (va_code_And64
    (va_op_dst_operand_reg R9) (va_op_operand_reg Rax)) (va_CCons (va_code_Add64 h0
    (va_op_operand_reg R8)) (va_CCons (va_code_Add64 h1 (va_op_operand_reg R9)) (va_CNil
    ())))))))))))))))))))
let va_code_poly1305_reduce_last h0 h1 h2 =
  (va_make_opaque (va_transparent_code_poly1305_reduce_last h0 h1 h2))

irreducible val va_irreducible_lemma_poly1305_reduce_last : va_b0:va_codes -> va_s0:va_state ->
  va_sN:va_state -> h0:va_dst_operand -> h1:va_dst_operand -> h2:va_operand -> h:int
  -> Ghost ((va_bM:va_codes) * (va_sM:va_state))
  (requires ((va_require va_b0 (va_code_poly1305_reduce_last h0 h1 h2) va_s0 va_sN) /\
    (va_is_dst_dst_operand_uint64 h0 va_s0) /\ (va_is_dst_dst_operand_uint64 h1 va_s0) /\
    (va_is_dst_operand_uint64 h2 va_s0) /\ (va_get_ok va_s0) /\ h0 == (OReg R14) /\ h1 == (OReg
    Rbx) /\ h2 == (OReg Rbp) /\ (va_eval_operand_uint64 va_s0 h2) < 5 /\ h == (lowerUpper192_opaque
    (lowerUpper128_opaque (va_eval_dst_operand_uint64 va_s0 h0) (va_eval_dst_operand_uint64 va_s0
    h1)) (va_eval_operand_uint64 va_s0 h2))))
  (ensures (fun ((va_bM:va_codes), (va_sM:va_state)) -> ((va_ensure va_b0 va_bM va_s0 va_sM va_sN)
    /\ (va_get_ok va_sM) /\ (lowerUpper128_opaque (va_eval_dst_operand_uint64 va_sM h0)
    (va_eval_dst_operand_uint64 va_sM h1)) == (mod2_128 (modp h)) /\ (va_state_eq va_sM
    (va_update_flags va_sM (va_update_reg Rax va_sM (va_update_reg R10 va_sM (va_update_reg R9
    va_sM (va_update_reg R8 va_sM (va_update_ok va_sM (va_update_operand h2 va_sM
    (va_update_dst_operand h1 va_sM (va_update_dst_operand h0 va_sM va_s0)))))))))))))
irreducible let va_irreducible_lemma_poly1305_reduce_last va_b0 va_s0 va_sN h0 h1 h2 h =
  (va_reveal_opaque (va_transparent_code_poly1305_reduce_last h0 h1 h2));
  let (va_old_s:va_state) = va_s0 in
  let (va_sM, (va_cM:va_code), va_bM) = (va_lemma_block va_b0 va_s0 va_sN) in
  let (va_b1:va_codes) = (va_get_block va_cM) in
  (lemma_poly_bits64 ());
  let (va_b3, va_s3) = (va_lemma_Mov64 va_b1 va_s0 va_sM (va_op_dst_operand_reg R8)
    (va_coerce_dst_operand_to_operand h0)) in
  let (va_b4, va_s4) = (va_lemma_Mov64 va_b3 va_s3 va_sM (va_op_dst_operand_reg R9)
    (va_coerce_dst_operand_to_operand h1)) in
  let (va_b5, va_s5) = (va_lemma_Mov64 va_b4 va_s4 va_sM (va_op_dst_operand_reg R10) h2) in
  let (va_b6, va_s6) = (va_lemma_Add64Wrap va_b5 va_s5 va_sM (va_op_dst_operand_reg R8)
    (va_const_operand 5)) in
  let (va_b7, va_s7) = (va_lemma_Adc64Wrap va_b6 va_s6 va_sM (va_op_dst_operand_reg R9)
    (va_const_operand 0)) in
  let (va_b8, va_s8) = (va_lemma_Adc64Wrap va_b7 va_s7 va_sM (va_op_dst_operand_reg R10)
    (va_const_operand 0)) in
  let va_forall_lemma () : Lemma
  (requires True)
  (ensures (h + 5 == (lowerUpper192_opaque (lowerUpper128_opaque (va_get_reg R8 va_s8) (va_get_reg
    R9 va_s8)) (va_get_reg R10 va_s8))))
  =
  (
    (reveal_opaque lowerUpper128);
    (reveal_opaque lowerUpper192);
    ()
  ) in va_forall_lemma ();
  (lemma_reduce128 h (va_eval_operand_uint64 va_old_s h2) (va_eval_dst_operand_uint64 va_old_s h1)
    (va_eval_dst_operand_uint64 va_old_s h0) (h + 5) (va_get_reg R10 va_s8) (va_get_reg R9 va_s8)
    (va_get_reg R8 va_s8));
  let (va_b11, va_s11) = (va_lemma_Shr64 va_b8 va_s8 va_sM (va_op_dst_operand_reg R10)
    (va_const_shift_amt 2)) in
  let (va_b12, va_s12) = (va_lemma_Mov64 va_b11 va_s11 va_sM (va_op_dst_operand_reg Rax)
    (va_op_operand_reg R10)) in
  let (va_b13, va_s13) = (va_lemma_Sub64Wrap va_b12 va_s12 va_sM (va_op_dst_operand_reg Rax)
    (va_const_operand 1)) in
  let (va_b14, va_s14) = (va_lemma_And64 va_b13 va_s13 va_sM h0 (va_op_operand_reg Rax)) in
  let (va_b15, va_s15) = (va_lemma_And64 va_b14 va_s14 va_sM h1 (va_op_operand_reg Rax)) in
  let (va_b16, va_s16) = (va_lemma_Mov64 va_b15 va_s15 va_sM (va_op_dst_operand_reg Rax)
    (va_const_operand 0)) in
  let (va_b17, va_s17) = (va_lemma_Sub64Wrap va_b16 va_s16 va_sM (va_op_dst_operand_reg Rax)
    (va_op_operand_reg R10)) in
  let (va_b18, va_s18) = (va_lemma_And64 va_b17 va_s17 va_sM (va_op_dst_operand_reg R8)
    (va_op_operand_reg Rax)) in
  let (va_b19, va_s19) = (va_lemma_And64 va_b18 va_s18 va_sM (va_op_dst_operand_reg R9)
    (va_op_operand_reg Rax)) in
  let (va_b20, va_s20) = (va_lemma_Add64 va_b19 va_s19 va_sM h0 (va_op_operand_reg R8)) in
  let (va_b21, va_s21) = (va_lemma_Add64 va_b20 va_s20 va_sM h1 (va_op_operand_reg R9)) in
  let va_sM = (va_lemma_empty va_s21 va_sM) in
  (va_bM, va_sM)
let va_lemma_poly1305_reduce_last = va_irreducible_lemma_poly1305_reduce_last

val va_transparent_code_poly1305_add_key_s : h0:va_dst_operand -> h1:va_dst_operand ->
  key_s0:va_operand -> key_s1:va_operand -> Tot va_code
let va_transparent_code_poly1305_add_key_s h0 h1 key_s0 key_s1 =
  (va_Block (va_CCons (va_code_Add64Wrap h0 key_s0) (va_CCons (va_code_Adc64Wrap h1 key_s1)
    (va_CNil ()))))
let va_code_poly1305_add_key_s h0 h1 key_s0 key_s1 =
  (va_make_opaque (va_transparent_code_poly1305_add_key_s h0 h1 key_s0 key_s1))

irreducible val va_irreducible_lemma_poly1305_add_key_s : va_b0:va_codes -> va_s0:va_state ->
  va_sN:va_state -> h0:va_dst_operand -> h1:va_dst_operand -> key_s0:va_operand ->
  key_s1:va_operand -> h_in:int -> key_s:nat128
  -> Ghost ((va_bM:va_codes) * (va_sM:va_state))
  (requires ((va_require va_b0 (va_code_poly1305_add_key_s h0 h1 key_s0 key_s1) va_s0 va_sN) /\
    (va_is_dst_dst_operand_uint64 h0 va_s0) /\ (va_is_dst_dst_operand_uint64 h1 va_s0) /\
    (va_is_src_operand_uint64 key_s0 va_s0) /\ (va_is_src_operand_uint64 key_s1 va_s0) /\
    (va_get_ok va_s0) /\ h0 == (OReg R14) /\ h1 == (OReg Rbx) /\ key_s0 == (OReg Rax) /\ key_s1 ==
    (OReg Rdx) /\ h_in == (lowerUpper128_opaque (va_eval_dst_operand_uint64 va_s0 h0)
    (va_eval_dst_operand_uint64 va_s0 h1)) /\ key_s == (lowerUpper128_opaque
    (va_eval_operand_uint64 va_s0 key_s0) (va_eval_operand_uint64 va_s0 key_s1))))
  (ensures (fun ((va_bM:va_codes), (va_sM:va_state)) -> ((va_ensure va_b0 va_bM va_s0 va_sM va_sN)
    /\ (va_get_ok va_sM) /\ (lowerUpper128_opaque (va_eval_dst_operand_uint64 va_sM h0)
    (va_eval_dst_operand_uint64 va_sM h1)) == (mod2_128 (h_in + key_s)) /\ (va_state_eq va_sM
    (va_update_flags va_sM (va_update_ok va_sM (va_update_dst_operand h1 va_sM
    (va_update_dst_operand h0 va_sM va_s0))))))))
irreducible let va_irreducible_lemma_poly1305_add_key_s va_b0 va_s0 va_sN h0 h1 key_s0 key_s1 h_in
  key_s =
  (va_reveal_opaque (va_transparent_code_poly1305_add_key_s h0 h1 key_s0 key_s1));
  let (va_old_s:va_state) = va_s0 in
  let (va_sM, (va_cM:va_code), va_bM) = (va_lemma_block va_b0 va_s0 va_sN) in
  let (va_b1:va_codes) = (va_get_block va_cM) in
  let (va_b2, va_s2) = (va_lemma_Add64Wrap va_b1 va_s0 va_sM h0 key_s0) in
  let (va_b3, va_s3) = (va_lemma_Adc64Wrap va_b2 va_s2 va_sM h1 key_s1) in
  (lemma_add_key (va_eval_dst_operand_uint64 va_old_s h0) (va_eval_dst_operand_uint64 va_old_s h1)
    h_in (va_eval_operand_uint64 va_s3 key_s0) (va_eval_operand_uint64 va_s3 key_s1) key_s
    (va_eval_dst_operand_uint64 va_s3 h0) (va_eval_dst_operand_uint64 va_s3 h1));
  let va_sM = (va_lemma_empty va_s3 va_sM) in
  (va_bM, va_sM)
let va_lemma_poly1305_add_key_s = va_irreducible_lemma_poly1305_add_key_s
let retain_only (nss:list string) : Tac unit =
  prune ""; //removes every top-level assertion which has "" as a prefix; so prune everything
  addns "Prims" ; //keep prims always
  let _ = FStar.Tactics.map addns nss in  //add back only things in nss
  ()

let retain_only_modp () = 
    retain_only ["Opaque_i"; "X64.Poly1305.Spec_s"; "X64.Poly1305"; "X64.Poly1305.Math_i"] //; "FStar.Seq"]`

let modp_0 () : Lemma
  (requires True)
  (ensures modp 0 == 0)
    =
    reveal_opaque modp';
    ()

let bare_r (key_r:nat128) = FStar.UInt.logand #128 key_r 0x0ffffffc0ffffffc0ffffffc0fffffff 

#reset-options "--z3rlimit 200"


val va_transparent_code_poly1305_impl : va_dummy:unit -> Tot va_code
let va_transparent_code_poly1305_impl () =
  (va_Block (va_CCons (va_Block (va_CCons (va_code_Mov64 (va_op_dst_operand_reg Rax)
    (va_const_operand 0)) (va_CCons (va_code_Store64 (va_op_reg_operand_reg Rdi) (va_op_operand_reg
    Rax) 0) (va_CCons (va_code_Store64 (va_op_reg_operand_reg Rdi) (va_op_operand_reg Rax) 8)
    (va_CCons (va_code_Store64 (va_op_reg_operand_reg Rdi) (va_op_operand_reg Rax) 16) (va_CCons
    (va_code_Load64 (va_op_dst_operand_reg R11) (va_op_reg_operand_reg Rdi) 24) (va_CCons
    (va_code_Load64 (va_op_dst_operand_reg R12) (va_op_reg_operand_reg Rdi) 32) (va_CCons
    (va_code_Mov64 (va_op_dst_operand_reg Rcx) (va_const_operand 1152921487695413247)) (va_CCons
    (va_code_And64 (va_op_dst_operand_reg R11) (va_op_operand_reg Rcx)) (va_CCons (va_code_Mov64
    (va_op_dst_operand_reg Rcx) (va_const_operand 1152921487695413244)) (va_CCons (va_code_And64
    (va_op_dst_operand_reg R12) (va_op_operand_reg Rcx)) (va_CCons (va_code_Store64
    (va_op_reg_operand_reg Rdi) (va_op_operand_reg R11) 24) (va_CCons (va_code_Store64
    (va_op_reg_operand_reg Rdi) (va_op_operand_reg R12) 32) (va_CNil ())))))))))))))) (va_CCons
    (va_Block (va_CCons (va_code_Mov64 (va_op_dst_operand_reg Rax) (va_op_operand_reg Rdx))
    (va_CCons (va_code_And64 (va_op_dst_operand_reg Rax) (va_const_operand 15)) (va_CCons
    (va_code_Sub64 (va_op_dst_operand_reg Rdx) (va_op_operand_reg Rax)) (va_CCons (va_code_Store64
    (va_op_reg_operand_reg Rdi) (va_op_operand_reg Rax) 56) (va_CCons (va_code_Store64
    (va_op_reg_operand_reg Rdi) (va_op_operand_reg Rdx) 64) (va_CCons (va_code_Mov64
    (va_op_dst_operand_reg Rcx) (va_const_operand 1)) (va_CNil ())))))))) (va_CCons
    (va_code_poly1305_blocks ()) (va_CCons (va_code_Load64 (va_op_dst_operand_reg R15)
    (va_op_reg_operand_reg Rdi) 56) (va_CCons (va_IfElse (va_cmp_ne (va_op_cmp_reg R15)
    (va_const_cmp 0)) (va_Block (va_CCons (va_code_Load64 (va_op_dst_operand_reg Rax)
    (va_op_reg_operand_reg Rdi) 32) (va_CCons (va_code_Load64 (va_op_dst_operand_reg R8)
    (va_op_reg_operand_reg Rsi) 0) (va_CCons (va_code_Load64 (va_op_dst_operand_reg R9)
    (va_op_reg_operand_reg Rsi) 8) (va_CCons (va_code_poly1305_last_block (va_op_dst_operand_reg
    R14) (va_op_dst_operand_reg Rbx) (va_op_dst_operand_reg Rbp) (va_op_operand_reg R11)
    (va_op_operand_reg R13) (va_op_operand_reg R15)) (va_CNil ())))))) (va_Block (va_CNil ())))
    (va_CCons (va_code_poly1305_reduce_last (va_op_dst_operand_reg R14) (va_op_dst_operand_reg Rbx)
    (va_op_operand_reg Rbp)) (va_CCons (va_code_Load64 (va_op_dst_operand_reg Rax)
    (va_op_reg_operand_reg Rdi) 40) (va_CCons (va_code_Load64 (va_op_dst_operand_reg Rdx)
    (va_op_reg_operand_reg Rdi) 48) (va_CCons (va_code_poly1305_add_key_s (va_op_dst_operand_reg
    R14) (va_op_dst_operand_reg Rbx) (va_op_operand_reg Rax) (va_op_operand_reg Rdx)) (va_CNil
    ())))))))))))
let va_code_poly1305_impl () =
  (va_make_opaque (va_transparent_code_poly1305_impl ()))

let va_ins_1_poly1305_impl () =
  [(va_fast_ins_Mov64 (va_op_dst_operand_reg Rax) (va_const_operand 0)); (va_fast_ins_Store64
    (va_op_reg_operand_reg Rdi) (va_op_operand_reg Rax) 0); (va_fast_ins_Store64
    (va_op_reg_operand_reg Rdi) (va_op_operand_reg Rax) 8); (va_fast_ins_Store64
    (va_op_reg_operand_reg Rdi) (va_op_operand_reg Rax) 16); (va_fast_ins_Load64
    (va_op_dst_operand_reg R11) (va_op_reg_operand_reg Rdi) 24); (va_fast_ins_Load64
    (va_op_dst_operand_reg R12) (va_op_reg_operand_reg Rdi) 32); (va_fast_ins_Mov64
    (va_op_dst_operand_reg Rcx) (va_const_operand 1152921487695413247)); (va_fast_ins_And64
    (va_op_dst_operand_reg R11) (va_op_operand_reg Rcx)); (va_fast_ins_Mov64 (va_op_dst_operand_reg
    Rcx) (va_const_operand 1152921487695413244)); (va_fast_ins_And64 (va_op_dst_operand_reg R12)
    (va_op_operand_reg Rcx)); (va_fast_ins_Store64 (va_op_reg_operand_reg Rdi) (va_op_operand_reg
    R11) 24); (va_fast_ins_Store64 (va_op_reg_operand_reg Rdi) (va_op_operand_reg R12) 32)]

let va_ins_2_poly1305_impl () =
  [(va_fast_ins_Mov64 (va_op_dst_operand_reg Rax) (va_op_operand_reg Rdx)); (va_fast_ins_And64
    (va_op_dst_operand_reg Rax) (va_const_operand 15)); (va_fast_ins_Sub64 (va_op_dst_operand_reg
    Rdx) (va_op_operand_reg Rax)); (va_fast_ins_Store64 (va_op_reg_operand_reg Rdi)
    (va_op_operand_reg Rax) 56); (va_fast_ins_Store64 (va_op_reg_operand_reg Rdi)
    (va_op_operand_reg Rdx) 64); (va_fast_ins_Mov64 (va_op_dst_operand_reg Rcx) (va_const_operand
    1))]

irreducible val va_irreducible_lemma_poly1305_impl : va_b0:va_codes -> va_s0:va_state ->
  va_sN:va_state -> key_r:nat128 -> key_s:nat128
  -> Ghost ((va_bM:va_codes) * (va_sM:va_state) * (h:int))
  (requires ((va_require va_b0 (va_code_poly1305_impl ()) va_s0 va_sN) /\ (let n = nat64_max in let
    p = n `op_Multiply` n `op_Multiply` 4 - 5 in (va_get_ok va_s0)) /\ (let n = nat64_max in let p
    = n `op_Multiply` n `op_Multiply` 4 - 5 in (disjoint (va_get_reg Rdi va_s0) (24 `op_Multiply`
    8) (va_get_reg Rsi va_s0) (((va_get_reg Rdx va_s0) + 15) `op_Division` 16 `op_Multiply` 16)) /\
    (validSrcAddrs (va_get_mem va_s0) (va_get_reg Rdi va_s0) 64 (24 `op_Multiply` 8)) /\
    (validSrcAddrs (va_get_mem va_s0) (va_get_reg Rsi va_s0) 64 (((va_get_reg Rdx va_s0) + 15)
    `op_Division` 16 `op_Multiply` 16)) /\ (va_get_reg Rsi va_s0) + (va_get_reg Rdx va_s0) <
    nat64_max /\ (let key_r0 = (va_subscript (va_get_mem va_s0) ((va_get_reg Rdi va_s0) + 24)) in
    let key_r1 = (va_subscript (va_get_mem va_s0) ((va_get_reg Rdi va_s0) + 32)) in let key_s0 =
    (va_subscript (va_get_mem va_s0) ((va_get_reg Rdi va_s0) + 40)) in let key_s1 = (va_subscript
    (va_get_mem va_s0) ((va_get_reg Rdi va_s0) + 48)) in key_r == (lowerUpper128_opaque key_r0
    key_r1) /\ key_s == (lowerUpper128_opaque key_s0 key_s1)))))
  (ensures (fun ((va_bM:va_codes), (va_sM:va_state), (h:int)) -> ((va_ensure va_b0 va_bM va_s0
    va_sM va_sN) /\ (let n = nat64_max in let p = n `op_Multiply` n `op_Multiply` 4 - 5 in
    (va_get_ok va_sM)) /\ (let n = nat64_max in let p = n `op_Multiply` n `op_Multiply` 4 - 5 in
    (validSrcAddrs (va_get_mem va_sM) (va_get_reg Rdi va_sM) 64 (24 `op_Multiply` 8)) /\
    (validSrcAddrs (va_get_mem va_sM) (va_get_reg Rsi va_s0) 64 (((va_get_reg Rdx va_s0) + 15)
    `op_Division` 16 `op_Multiply` 16)) /\ (memModified (va_get_mem va_s0) (va_get_mem va_sM)
    (va_get_reg Rdi va_s0) (9 `op_Multiply` 8)) /\ h == (lowerUpper128_opaque (va_get_reg R14
    va_sM) (va_get_reg Rbx va_sM)) /\ (let inp_mem = (heapletTo128 (va_get_mem va_sM) (va_get_reg
    Rsi va_s0) (va_get_reg Rdx va_s0)) in h == (poly1305_hash key_r key_s inp_mem (va_get_reg Rsi
    va_s0) (va_get_reg Rdx va_s0)) /\ (va_get_reg Rdi va_sM) == (va_get_reg Rdi va_s0))))))
irreducible let va_irreducible_lemma_poly1305_impl va_b0 va_s0 va_sN key_r key_s =
  (va_reveal_opaque (va_transparent_code_poly1305_impl ()));
  let (va_old_s:va_state) = va_s0 in
  let (va_sM, (va_cM:va_code), va_bM) = (va_lemma_block va_b0 va_s0 va_sN) in
  let (va_b1:va_codes) = (va_get_block va_cM) in
  let n = nat64_max in
  let p = (n `op_Multiply` n `op_Multiply` 4 - 5) in
  let inp_in = (va_get_reg Rsi va_s0) in
  let len_in = (va_get_reg Rdx va_s0) in
  let key_r0 = (va_subscript (va_get_mem va_s0) ((va_get_reg Rdi va_s0) + 24)) in
  let key_r1 = (va_subscript (va_get_mem va_s0) ((va_get_reg Rdi va_s0) + 32)) in
  (lemma_poly_bits64 ());
  let (va_s17, va_c17, va_b17) = (va_lemma_block va_b1 va_s0 va_sM) in
  (va_lemma_weakest_pre_norm (va_ins_1_poly1305_impl ()) va_s0 va_s17);
  let (r:nat128) = (lowerUpper128_opaque (va_get_reg R11 va_s17) (va_get_reg R12 va_s17)) in
  let va_forall_lemma () : Lemma
  (requires True)
  (ensures (r == (va_get_reg R11 va_s17) + n `op_Multiply` (va_get_reg R12 va_s17)))
  =
  (
    (reveal_opaque lowerUpper128);
    ()
  ) in va_forall_lemma ();
  let va_forall_lemma () : Lemma
  (requires True)
  (ensures (r == (logand128 key_r 21267647620597763993911028882763415551)))
  =
  (
    (reveal_opaque lowerUpper128);
    (lemma_lowerUpper128_and key_r key_r0 key_r1 21267647620597763993911028882763415551
      1152921487695413247 1152921487695413244 r (va_get_reg R11 va_s17) (va_get_reg R12 va_s17));
    ()
  ) in va_forall_lemma ();
  let (va_s21, va_c21, va_b21) = (va_lemma_block va_b17 va_s17 va_sM) in
  (va_lemma_weakest_pre_norm (va_ins_2_poly1305_impl ()) va_s17 va_s21);
  let (va_b22, va_s22, h) = (va_lemma_poly1305_blocks va_b21 va_s21 va_sM r 0) in
  let va_forall_lemma () : Lemma
  (requires True)
  (ensures ((modp 0) == 0))
  =
  (
    (modp_0 ());
    ()
  ) in va_forall_lemma ();
  (lemma_poly1305_heap_hash_blocks 0 (n `op_Multiply` n) r (va_get_mem va_s22) inp_in (inp_in +
    len_in `op_Division` 16 `op_Multiply` 16) len_in);
  (reveal_logand128 key_r 21267647620597763993911028882763415551);
  assert (r == (bare_r key_r));
  let va_forall_lemma () : Lemma
  (requires True)
  (ensures (h == (lowerUpper192_opaque (lowerUpper128_opaque (va_get_reg R14 va_s22) (va_get_reg
    Rbx va_s22)) (va_get_reg Rbp va_s22))))
  =
  (
    (reveal_opaque lowerUpper192);
    (reveal_opaque lowerUpper128);
    ()
  ) in va_forall_lemma ();
  let (va_b29, va_s29) = (va_lemma_Load64 va_b22 va_s22 va_sM (va_op_dst_operand_reg R15)
    (va_op_reg_operand_reg Rdi) 56) in
  assert ((va_get_reg R15 va_s29) == len_in `op_Modulus` 16);
  let (va_s31, va_c31, va_b31) = (va_lemma_block va_b29 va_s29 va_sM) in
  let (va_cond_c31, (va_s32:va_state)) = (va_lemma_ifElse (va_get_ifCond va_c31) (va_get_ifTrue
    va_c31) (va_get_ifFalse va_c31) va_s29 va_s31) in
  let ((h:int), va_s31) =
  (
    if va_cond_c31 then
    (
      let va_b33 = (va_get_block (va_get_ifTrue va_c31)) in
      let (va_b34, va_s34) = (va_lemma_Load64 va_b33 va_s32 va_s31 (va_op_dst_operand_reg Rax)
        (va_op_reg_operand_reg Rdi) 32) in
      let (va_b35, va_s35) = (va_lemma_Load64 va_b34 va_s34 va_s31 (va_op_dst_operand_reg R8)
        (va_op_reg_operand_reg Rsi) 0) in
      let (va_b36, va_s36) = (va_lemma_Load64 va_b35 va_s35 va_s31 (va_op_dst_operand_reg R9)
        (va_op_reg_operand_reg Rsi) 8) in
      let a = (applyHeapletTo128 (va_get_mem va_s36) inp_in len_in (va_get_reg Rsi va_s36)) in
      let va_forall_lemma () : Lemma
      (requires True)
      (ensures ((lowerUpper128_opaque (va_get_reg R8 va_s36) (va_get_reg R9 va_s36)) == a))
      =
      (
        (reveal_opaque lowerUpper128);
        ()
      ) in va_forall_lemma ();
      let (va_b39, va_s39) = (va_lemma_poly1305_last_block va_b36 va_s36 va_s31
        (va_op_dst_operand_reg R14) (va_op_dst_operand_reg Rbx) (va_op_dst_operand_reg Rbp)
        (va_op_operand_reg R11) (va_op_operand_reg R13) (va_op_operand_reg R15) h (va_get_reg R12
        va_s36) r (lowerUpper128_opaque (va_get_reg R8 va_s36) (va_get_reg R9 va_s36)) p) in
      let h = (lowerUpper192_opaque (lowerUpper128_opaque (va_get_reg R14 va_s39) (va_get_reg Rbx
        va_s39)) (va_get_reg Rbp va_s39)) in
      let va_s31 = (va_lemma_empty va_s39 va_s31) in
      (h, va_s31)
    )
    else
    (
      let va_b41 = (va_get_block (va_get_ifFalse va_c31)) in
      let va_s31 = (va_lemma_empty va_s32 va_s31) in
      (h, va_s31)
    )
  ) in
  (lemma_add_mod128 (modp h) key_s);
  let (va_b43, va_s43) = (va_lemma_poly1305_reduce_last va_b31 va_s31 va_sM (va_op_dst_operand_reg
    R14) (va_op_dst_operand_reg Rbx) (va_op_operand_reg Rbp) h) in
  let h = (lowerUpper128_opaque (va_get_reg R14 va_s43) (va_get_reg Rbx va_s43)) in
  let (va_b45, va_s45) = (va_lemma_Load64 va_b43 va_s43 va_sM (va_op_dst_operand_reg Rax)
    (va_op_reg_operand_reg Rdi) 40) in
  let (va_b46, va_s46) = (va_lemma_Load64 va_b45 va_s45 va_sM (va_op_dst_operand_reg Rdx)
    (va_op_reg_operand_reg Rdi) 48) in
  let (va_b47, va_s47) = (va_lemma_poly1305_add_key_s va_b46 va_s46 va_sM (va_op_dst_operand_reg
    R14) (va_op_dst_operand_reg Rbx) (va_op_operand_reg Rax) (va_op_operand_reg Rdx) h key_s) in
  let h = (lowerUpper128_opaque (va_get_reg R14 va_s47) (va_get_reg Rbx va_s47)) in
  let va_forall_lemma () : Lemma
  (requires True)
  (ensures (h == (poly1305_hash key_r key_s (heapletTo128 (va_get_mem va_s47) inp_in len_in) inp_in
    len_in)))
  =
  (
    (reveal_opaque mod2_128');
    (reveal_opaque modp');
    ()
  ) in va_forall_lemma ();
  let va_sM = (va_lemma_empty va_s47 va_sM) in
  (va_bM, va_sM, h)
let va_lemma_poly1305_impl = va_irreducible_lemma_poly1305_impl

val va_transparent_code_poly1305 : win:bool -> Tot va_code
let va_transparent_code_poly1305 win =
  (va_Block (va_CCons (va_code_Mov64 (va_op_dst_operand_reg Rax) (va_op_operand_reg Rdi)) (va_CCons
    (va_code_Mov64 (va_op_dst_operand_reg R9) (va_op_operand_reg Rsi)) (va_CCons (if win then
    (va_Block (va_CCons (va_code_Mov64 (va_op_dst_operand_reg Rdi) (va_op_operand_reg Rcx))
    (va_CCons (va_code_Mov64 (va_op_dst_operand_reg Rsi) (va_op_operand_reg Rdx)) (va_CCons
    (va_code_Mov64 (va_op_dst_operand_reg Rdx) (va_op_operand_reg R8)) (va_CNil ()))))) else
    (va_Block (va_CNil ()))) (va_CCons (va_Block (va_CCons (va_code_Store64 (va_op_reg_operand_reg
    Rdi) (va_op_operand_reg Rbx) 72) (va_CCons (va_code_Store64 (va_op_reg_operand_reg Rdi)
    (va_op_operand_reg Rbp) 80) (va_CCons (va_code_Store64 (va_op_reg_operand_reg Rdi)
    (va_op_operand_reg Rax) 88) (va_CCons (va_code_Store64 (va_op_reg_operand_reg Rdi)
    (va_op_operand_reg R9) 96) (va_CCons (va_code_Store64 (va_op_reg_operand_reg Rdi)
    (va_op_operand_reg R12) 104) (va_CCons (va_code_Store64 (va_op_reg_operand_reg Rdi)
    (va_op_operand_reg R13) 112) (va_CCons (va_code_Store64 (va_op_reg_operand_reg Rdi)
    (va_op_operand_reg R14) 120) (va_CCons (va_code_Store64 (va_op_reg_operand_reg Rdi)
    (va_op_operand_reg R15) 128) (va_CNil ())))))))))) (va_CCons (va_code_poly1305_impl ())
    (va_CCons (va_Block (va_CCons (va_code_Store64 (va_op_reg_operand_reg Rdi) (va_op_operand_reg
    R14) 0) (va_CCons (va_code_Store64 (va_op_reg_operand_reg Rdi) (va_op_operand_reg Rbx) 8)
    (va_CCons (va_code_Load64 (va_op_dst_operand_reg Rbx) (va_op_reg_operand_reg Rdi) 72) (va_CCons
    (va_code_Load64 (va_op_dst_operand_reg Rbp) (va_op_reg_operand_reg Rdi) 80) (va_CCons
    (va_code_Load64 (va_op_dst_operand_reg Rax) (va_op_reg_operand_reg Rdi) 88) (va_CCons
    (va_code_Load64 (va_op_dst_operand_reg Rsi) (va_op_reg_operand_reg Rdi) 96) (va_CCons
    (va_code_Load64 (va_op_dst_operand_reg R12) (va_op_reg_operand_reg Rdi) 104) (va_CCons
    (va_code_Load64 (va_op_dst_operand_reg R13) (va_op_reg_operand_reg Rdi) 112) (va_CCons
    (va_code_Load64 (va_op_dst_operand_reg R14) (va_op_reg_operand_reg Rdi) 120) (va_CCons
    (va_code_Load64 (va_op_dst_operand_reg R15) (va_op_reg_operand_reg Rdi) 128) (va_CCons
    (va_code_Mov64 (va_op_dst_operand_reg Rdi) (va_op_operand_reg Rax)) (va_CNil ())))))))))))))
    (va_CNil ()))))))))
let va_code_poly1305 win =
  (va_make_opaque (va_transparent_code_poly1305 win))

let va_ins_1_poly1305 win =
  [(va_fast_ins_Store64 (va_op_reg_operand_reg Rdi) (va_op_operand_reg Rbx) 72);
    (va_fast_ins_Store64 (va_op_reg_operand_reg Rdi) (va_op_operand_reg Rbp) 80);
    (va_fast_ins_Store64 (va_op_reg_operand_reg Rdi) (va_op_operand_reg Rax) 88);
    (va_fast_ins_Store64 (va_op_reg_operand_reg Rdi) (va_op_operand_reg R9) 96);
    (va_fast_ins_Store64 (va_op_reg_operand_reg Rdi) (va_op_operand_reg R12) 104);
    (va_fast_ins_Store64 (va_op_reg_operand_reg Rdi) (va_op_operand_reg R13) 112);
    (va_fast_ins_Store64 (va_op_reg_operand_reg Rdi) (va_op_operand_reg R14) 120);
    (va_fast_ins_Store64 (va_op_reg_operand_reg Rdi) (va_op_operand_reg R15) 128)]

let va_ins_2_poly1305 win =
  [(va_fast_ins_Store64 (va_op_reg_operand_reg Rdi) (va_op_operand_reg R14) 0);
    (va_fast_ins_Store64 (va_op_reg_operand_reg Rdi) (va_op_operand_reg Rbx) 8);
    (va_fast_ins_Load64 (va_op_dst_operand_reg Rbx) (va_op_reg_operand_reg Rdi) 72);
    (va_fast_ins_Load64 (va_op_dst_operand_reg Rbp) (va_op_reg_operand_reg Rdi) 80);
    (va_fast_ins_Load64 (va_op_dst_operand_reg Rax) (va_op_reg_operand_reg Rdi) 88);
    (va_fast_ins_Load64 (va_op_dst_operand_reg Rsi) (va_op_reg_operand_reg Rdi) 96);
    (va_fast_ins_Load64 (va_op_dst_operand_reg R12) (va_op_reg_operand_reg Rdi) 104);
    (va_fast_ins_Load64 (va_op_dst_operand_reg R13) (va_op_reg_operand_reg Rdi) 112);
    (va_fast_ins_Load64 (va_op_dst_operand_reg R14) (va_op_reg_operand_reg Rdi) 120);
    (va_fast_ins_Load64 (va_op_dst_operand_reg R15) (va_op_reg_operand_reg Rdi) 128);
    (va_fast_ins_Mov64 (va_op_dst_operand_reg Rdi) (va_op_operand_reg Rax))]

irreducible val va_irreducible_lemma_poly1305 : va_b0:va_codes -> va_s0:va_state -> va_sN:va_state
  -> win:bool -> key_r:nat128 -> key_s:nat128 -> p:int -> ctx_in:nat64 -> inp_in:nat64 ->
  len_in:nat64
  -> Ghost ((va_bM:va_codes) * (va_sM:va_state) * (h:int))
  (requires ((va_require va_b0 (va_code_poly1305 win) va_s0 va_sN) /\ (va_get_ok va_s0) /\ (ctx_in
    == (if win then (va_get_reg Rcx va_s0) else (va_get_reg Rdi va_s0)) /\ inp_in == (if win then
    (va_get_reg Rdx va_s0) else (va_get_reg Rsi va_s0)) /\ len_in == (if win then (va_get_reg R8
    va_s0) else (va_get_reg Rdx va_s0)) /\ p == n `op_Multiply` n `op_Multiply` 4 - 5 /\ (disjoint
    ctx_in (24 `op_Multiply` 8) inp_in ((len_in + 15) `op_Division` 16 `op_Multiply` 16)) /\
    (validSrcAddrs (va_get_mem va_s0) ctx_in 64 (24 `op_Multiply` 8)) /\ (validSrcAddrs (va_get_mem
    va_s0) inp_in 64 ((len_in + 15) `op_Division` 16 `op_Multiply` 16)) /\ inp_in + len_in <
    nat64_max /\ (let key_r0 = (va_subscript (va_get_mem va_s0) (ctx_in + 24)) in let key_r1 =
    (va_subscript (va_get_mem va_s0) (ctx_in + 32)) in let key_s0 = (va_subscript (va_get_mem
    va_s0) (ctx_in + 40)) in let key_s1 = (va_subscript (va_get_mem va_s0) (ctx_in + 48)) in key_r
    == (lowerUpper128_opaque key_r0 key_r1) /\ key_s == (lowerUpper128_opaque key_s0 key_s1)))))
  (ensures (fun ((va_bM:va_codes), (va_sM:va_state), (h:int)) -> ((va_ensure va_b0 va_bM va_s0
    va_sM va_sN) /\ (va_get_ok va_sM) /\ ((validSrcAddrs (va_get_mem va_sM) ctx_in 64 (24
    `op_Multiply` 8)) /\ (validSrcAddrs (va_get_mem va_sM) inp_in 64 ((len_in + 15) `op_Division`
    16 `op_Multiply` 16)) /\ (memModified (va_get_mem va_s0) (va_get_mem va_sM) ctx_in (24
    `op_Multiply` 8)) /\ (let h0_out = (va_subscript (va_get_mem va_sM) ctx_in) in let h1_out =
    (va_subscript (va_get_mem va_sM) (ctx_in + 8)) in h == (lowerUpper128_opaque h0_out h1_out) /\
    (let inp_mem = (heapletTo128 (va_get_mem va_sM) inp_in len_in) in h == (poly1305_hash key_r
    key_s inp_mem inp_in len_in) /\ (va_get_reg Rbx va_sM) == (va_get_reg Rbx va_s0) /\ (va_get_reg
    Rbp va_sM) == (va_get_reg Rbp va_s0) /\ (va_get_reg Rdi va_sM) == (va_get_reg Rdi va_s0) /\
    (va_get_reg Rsi va_sM) == (va_get_reg Rsi va_s0) /\ (va_get_reg R12 va_sM) == (va_get_reg R12
    va_s0) /\ (va_get_reg R13 va_sM) == (va_get_reg R13 va_s0) /\ (va_get_reg R14 va_sM) ==
    (va_get_reg R14 va_s0) /\ (va_get_reg R15 va_sM) == (va_get_reg R15 va_s0)))))))
irreducible let va_irreducible_lemma_poly1305 va_b0 va_s0 va_sN win key_r key_s p ctx_in inp_in
  len_in =
  (va_reveal_opaque (va_transparent_code_poly1305 win));
  let (va_old_s:va_state) = va_s0 in
  let (va_sM, (va_cM:va_code), va_bM) = (va_lemma_block va_b0 va_s0 va_sN) in
  let (va_b1:va_codes) = (va_get_block va_cM) in
  let h = 0 in
  let (va_b11, va_s11) = (va_lemma_Mov64 va_b1 va_s0 va_sM (va_op_dst_operand_reg Rax)
    (va_op_operand_reg Rdi)) in
  let (va_b12, va_s12) = (va_lemma_Mov64 va_b11 va_s11 va_sM (va_op_dst_operand_reg R9)
    (va_op_operand_reg Rsi)) in
  let (va_s13, va_c13, va_b13) = (va_lemma_block va_b12 va_s12 va_sM) in
  let (va_s13) =
  (
    if win then
    (
      let va_b14 = (va_get_block va_c13) in
      let (va_b15, va_s15) = (va_lemma_Mov64 va_b14 va_s12 va_s13 (va_op_dst_operand_reg Rdi)
        (va_op_operand_reg Rcx)) in
      let (va_b16, va_s16) = (va_lemma_Mov64 va_b15 va_s15 va_s13 (va_op_dst_operand_reg Rsi)
        (va_op_operand_reg Rdx)) in
      let (va_b17, va_s17) = (va_lemma_Mov64 va_b16 va_s16 va_s13 (va_op_dst_operand_reg Rdx)
        (va_op_operand_reg R8)) in
      let va_s13 = (va_lemma_empty va_s17 va_s13) in
      (va_s13)
    )
    else
    (
      let va_b18 = (va_get_block va_c13) in
      let va_s13 = (va_lemma_empty va_s12 va_s13) in
      (va_s13)
    )
  ) in
  let (va_s19, va_c19, va_b19) = (va_lemma_block va_b13 va_s13 va_sM) in
  (va_lemma_weakest_pre_norm (va_ins_1_poly1305 win) va_s13 va_s19);
  let old_inp = (va_get_reg Rsi va_s19) in
  let old_len = (va_get_reg Rdx va_s19) in
  let (va_b22, va_s22, h) = (va_lemma_poly1305_impl va_b19 va_s19 va_sM key_r key_s) in
  (heapletTo128_all_preserved (va_get_mem va_s22) (va_get_reg Rdi va_s22) (9 `op_Multiply` 8)
    old_inp old_len);
  let (va_s25, va_c25, va_b25) = (va_lemma_block va_b22 va_s22 va_sM) in
  (va_lemma_weakest_pre_norm (va_ins_2_poly1305 win) va_s22 va_s25);
  let va_sM = (va_lemma_empty va_s25 va_sM) in
  (va_bM, va_sM, h)
let va_lemma_poly1305 = va_irreducible_lemma_poly1305

let print_poly1305 (p:printer) : FStar.All.ML unit =
  let poly_code = va_code_poly1305 false in
  print_header p;
  print_proc "poly1305" poly_code 0 p;
  print_footer p

let main () : FStar.All.ML unit =
  print_poly1305 masm;
  print_string "\n\n";
  print_poly1305 gcc

