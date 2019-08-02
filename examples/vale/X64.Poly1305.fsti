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

unfold let n = nat64_max


val va_code_poly1305_multiply : va_dummy:unit -> Tot va_code


val va_lemma_poly1305_multiply : va_b0:va_codes -> va_s0:va_state -> va_sN:va_state -> r1:nat64
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

val va_code_poly1305_reduce : d3:va_dst_operand -> h0:va_dst_operand -> h1:va_dst_operand ->
  h2:va_dst_operand -> Tot va_code

val va_lemma_poly1305_reduce : va_b0:va_codes -> va_s0:va_state -> va_sN:va_state ->
  d3:va_dst_operand -> h0:va_dst_operand -> h1:va_dst_operand -> h2:va_dst_operand -> hd:int ->
  p:int
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

val va_code_poly1305_reduce_regs : va_dummy:unit -> Tot va_code

val va_lemma_poly1305_reduce_regs : va_b0:va_codes -> va_s0:va_state -> va_sN:va_state -> hd:int ->
  p:int
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

val va_code_poly1305_reduce_regs_fast_block : va_dummy:unit -> Tot va_code


val va_lemma_poly1305_reduce_regs_fast_block : va_b0:va_codes -> va_s0:va_state -> va_sN:va_state
  -> hd:int -> p:int
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

val va_code_poly1305_iteration : d1:va_dst_operand -> d2:va_dst_operand -> d3:va_dst_operand ->
  r0:va_operand -> s1:va_operand -> h0:va_dst_operand -> h1:va_dst_operand -> h2:va_dst_operand ->
  Tot va_code

val va_lemma_poly1305_iteration : va_b0:va_codes -> va_s0:va_state -> va_sN:va_state ->
  d1:va_dst_operand -> d2:va_dst_operand -> d3:va_dst_operand -> r0:va_operand -> s1:va_operand ->
  h0:va_dst_operand -> h1:va_dst_operand -> h2:va_dst_operand -> r1:nat64
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

val va_code_poly1305_blocks : va_dummy:unit -> Tot va_code



val va_lemma_poly1305_blocks : va_b0:va_codes -> va_s0:va_state -> va_sN:va_state -> r:int ->
  h_in:int
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

val va_code_poly1305_last_block : h0:va_dst_operand -> h1:va_dst_operand -> h2:va_dst_operand ->
  r0:va_operand -> s1:va_operand -> nExtra:va_operand -> Tot va_code

val va_lemma_poly1305_last_block : va_b0:va_codes -> va_s0:va_state -> va_sN:va_state ->
  h0:va_dst_operand -> h1:va_dst_operand -> h2:va_dst_operand -> r0:va_operand -> s1:va_operand ->
  nExtra:va_operand -> hBlocks:int -> r1:nat64 -> r:int -> inpLast:nat128 -> p:int
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

val va_code_poly1305_reduce_last : h0:va_dst_operand -> h1:va_dst_operand -> h2:va_operand -> Tot
  va_code

val va_lemma_poly1305_reduce_last : va_b0:va_codes -> va_s0:va_state -> va_sN:va_state ->
  h0:va_dst_operand -> h1:va_dst_operand -> h2:va_operand -> h:int
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

val va_code_poly1305_add_key_s : h0:va_dst_operand -> h1:va_dst_operand -> key_s0:va_operand ->
  key_s1:va_operand -> Tot va_code

val va_lemma_poly1305_add_key_s : va_b0:va_codes -> va_s0:va_state -> va_sN:va_state ->
  h0:va_dst_operand -> h1:va_dst_operand -> key_s0:va_operand -> key_s1:va_operand -> h_in:int ->
  key_s:nat128
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

val va_code_poly1305_impl : va_dummy:unit -> Tot va_code



val va_lemma_poly1305_impl : va_b0:va_codes -> va_s0:va_state -> va_sN:va_state -> key_r:nat128 ->
  key_s:nat128
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

val va_code_poly1305 : win:bool -> Tot va_code



val va_lemma_poly1305 : va_b0:va_codes -> va_s0:va_state -> va_sN:va_state -> win:bool ->
  key_r:nat128 -> key_s:nat128 -> p:int -> ctx_in:nat64 -> inp_in:nat64 -> len_in:nat64
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
