module X64.Vale.State_i
// This interface should not refer to Semantics_s

open X64.Machine_s
open X64.Vale

unfold let mem = Map.t int nat64

noeq type state = {
  ok: bool;
  regs: Regs_i.t;
  flags: nat64;
  mem: mem;
}

let reg_to_int (r:reg) : int =
  match r with
  | Rax -> 0
  | Rbx -> 1
  | Rcx -> 2
  | Rdx -> 3
  | Rsi -> 4
  | Rdi -> 5
  | Rbp -> 6
  | Rsp -> 7
  | R8 -> 8
  | R9 -> 9
  | R10 -> 10
  | R11 -> 11
  | R12 -> 12
  | R13 -> 13
  | R14 -> 14
  | R15 -> 15

unfold let eval_reg (r:reg) (s:state) : nat64 = s.regs r
unfold let eval_mem (ptr:int) (s:state) : nat64 = Map.sel s.mem ptr

let eval_maddr (m:maddr) (s:state) : int =
  let open FStar.Mul in
    match m with
    | MConst n -> n
    | MReg reg offset -> eval_reg reg s + offset
    | MIndex base scale index offset -> eval_reg base s + scale * (eval_reg index s) + offset

let eval_operand (o:operand) (s:state) : nat64 =
  match o with
  | OConst n -> int_to_nat64 n
  | OReg r -> eval_reg r s
  | OMem m -> eval_mem (eval_maddr m s) s

let update_reg (r:reg) (v:nat64) (s:state) : state =
  { s with regs = fun r' -> if  r = r' then v else s.regs r' }

let update_mem (ptr:int) (v:nat64) (s:state) : state = { s with mem = Map.upd s.mem ptr v }

let valid_maddr (m:maddr) (s:state) : Type0 =
  s.mem `Map.contains` (eval_maddr m s)

let valid_operand (o:operand) (s:state) : Type0 =
  match o with
  | OConst n -> 0 <= n /\ n < nat64_max
  | OReg r -> True
  | OMem m -> valid_maddr m s

let state_eq (s0:state) (s1:state) : Type0 = 
  s0.ok == s1.ok /\
  Regs_i.equal s0.regs s1.regs /\
  s0.flags == s1.flags /\
  Map.equal s0.mem s1.mem

let add_wrap (x:int) (y:int) = if x + y < nat64_max then x + y else x + y - nat64_max

unfold let eq_int (i1:int) (i2:int) = i1 == i2

