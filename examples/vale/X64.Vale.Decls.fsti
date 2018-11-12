module X64.Vale.Decls

// This interface should hide all of Semantics_s.
// (It should not refer to Semantics_s, directly or indirectly.)
// It should not refer to StateLemmas_i, Lemmas_i, or Print_s,
// because they refer to Semantics_s.
// Regs_i and State_i are ok, because they do not refer to Semantics_s.

open X64.Machine_s
open X64.Vale.State_i

val cf : (flags:int) -> bool

//unfold let va_subscript = Map.sel
unfold let va_subscript (#a:eqtype) (#b:Type) (x:Map.t a b) (y:a) : Tot b = Map.sel x y
unfold let va_update = Map.upd
unfold let va_make_opaque = Opaque_i.make_opaque
unfold let va_reveal_opaque = Opaque_i.reveal_opaque

(* Type aliases *)
unfold let va_bool = bool
unfold let va_int = int
val ins : Type0
val ocmp : Type0
unfold let va_code = precode ins ocmp
unfold let va_codes = list va_code
unfold let va_state = state
unfold let va_operand = operand
let va_reg_operand = o:operand{OReg? o}
unfold let va_dst_operand = dst_op
unfold let va_shift_amt = operand
unfold let va_cmp = operand
unfold let va_register = reg

(* Constructors *)
unfold let va_op_operand_reg (r:reg) : va_operand = OReg r
unfold let va_const_operand (n:int) = OConst n
unfold let va_const_shift_amt (n:int) : va_shift_amt = OConst n
unfold let va_op_shift_amt_reg(r:reg) : va_shift_amt = OReg r
unfold let va_op_cmp_reg (r:reg) : va_cmp = OReg r
unfold let va_const_cmp (n:int) : va_cmp = OConst n
unfold let va_coerce_register_to_operand (r:va_register) : va_operand = OReg r
unfold let va_coerce_operand_to_reg_operand (o:va_operand{OReg? o}) : va_reg_operand = o
unfold let va_coerce_dst_operand_to_reg_operand (o:va_dst_operand{OReg? o}) : va_reg_operand = o
unfold let va_coerce_operand_to_cmp(o:va_operand) : va_cmp = o
unfold let va_op_register (r:reg) : va_register = r
unfold let va_op_reg_operand_reg (r:reg) : va_reg_operand = OReg r
unfold let va_op_dst_operand_reg (r:reg{not (Rsp? r)}) : va_dst_operand = OReg r
unfold let va_coerce_operand_to_dst_operand (o:va_operand{valid_dst o}) : va_dst_operand = o
unfold let va_coerce_dst_operand_to_operand (o:va_dst_operand) : va_operand = o
unfold let va_opr_code_Mem (o:operand) (offset:int) : operand =
  match o with
  | OConst n -> OConst (n + offset)
  | OReg r -> OMem (MReg r offset)
  | _ -> OConst 42

unfold let va_opr_lemma_Mem (s:va_state) (base:va_operand) (offset:int) : operand =
  va_opr_code_Mem base offset

(*
function method va_opr_lemma_Mem(s:va_state, base:va_operand, offset:int, taint:taint, id:heaplet_id):va_mem_operand
    requires x86_ValidState(s)
    requires base.OReg?
    requires ValidMemAddr(MReg(base.r, offset))
    requires ValidSrcAddr(s.heaplets, id, va_get_reg64(base.r, s) + offset, 64, taint)
    ensures  Valid64BitSourceOperand(to_state(s), OHeap(MReg(base.r, offset), taint))
    ensures  eval_op64(to_state(s), OHeap(MReg(base.r, offset), taint)) == s.heaplets[id].mem64[va_get_reg64(base.r, s) + offset].v
{
    reveal_x86_ValidState();
    va_opr_code_Mem(base, offset, taint)
}
*)


(* Predicates *)
unfold let va_is_src_operand_uint64 (o:operand) (s:va_state) = valid_operand o s
unfold let va_is_dst_operand_uint64 (o:operand) (s:va_state) = valid_dst o
unfold let va_is_dst_dst_operand_uint64 (o:va_dst_operand) (s:va_state) = valid_operand o s
unfold let va_is_src_register_int (r:reg) (s:va_state) = True
unfold let va_is_dst_register (r:reg) (s:va_state) = True
unfold let va_is_src_shift_amt_uint64 (o:operand) (s:va_state) = True
unfold let va_is_src_reg_operand_uint64 (o:operand) (s:va_state) = OReg? o
unfold let valid_src_addr (m:mem) (addr:int) : bool = m `Map.contains` addr
unfold let valid_dst_addr (m:mem) (addr:int) : bool = m `Map.contains` addr 

(* Getters *)
unfold let va_get_ok (s:va_state) : bool = s.ok
unfold let va_get_flags (s:va_state) : int = s.flags
unfold let va_get_reg (r:reg) (s:va_state) : nat64 = eval_reg r s
unfold let va_get_mem (s:va_state) : mem = s.mem
unfold let get_reg (o:va_reg_operand) : reg = OReg?.r o

(* Framing: va_update_foo means the two states are the same except for foo *)
unfold let va_update_ok (sM:va_state) (sK:va_state) : va_state  = { sK with ok = sM.ok }
unfold let va_update_flags  (sM:va_state) (sK:va_state) : va_state  = { sK with flags = sM.flags }

unfold
let va_update_reg (r:reg) (sM:va_state) (sK:va_state) : va_state =
  update_reg r (eval_reg r sM) sK

unfold let va_update_mem (sM:va_state) (sK:va_state) : va_state = { sK with mem = sM.mem }

let va_update_operand (o:operand) (sM:va_state) (sK:va_state) : va_state =
  match o with
  | OConst n -> sK
  | OReg r -> va_update_reg r sM sK
  | OMem m -> va_update_mem sM sK 

unfold
let va_update_dst_operand (o:dst_op) (sM:va_state) (sK:va_state) : va_state =
  va_update_operand o sM sK   

unfold
let va_update_register (r:reg) (sM:va_state) (sK:va_state) : va_state =
  va_update_reg r sM sK

(* Evaluation *)
unfold let va_eval_operand_uint64     (s:va_state) (o:va_operand)     : nat64 = eval_operand o s
unfold let va_eval_dst_operand_uint64 (s:va_state) (o:va_dst_operand) : nat64 = eval_operand o s
unfold let va_eval_shift_amt_uint64   (s:va_state) (o:va_shift_amt)   : nat64 = eval_operand o s
unfold let va_eval_cmp_uint64         (s:va_state) (r:va_cmp)         : nat64 = eval_operand r s
unfold let va_eval_register_uint64    (s:va_state) (r:va_register)    : nat64 = eval_reg r s
unfold let va_eval_reg_operand_uint64 (s:va_state) (o:va_reg_operand) : nat64 = eval_reg (OReg?.r o) s

(** Constructors for va_codes *)
unfold let va_CNil () : va_codes = []
unfold let va_CCons (hd:va_code) (tl:va_codes) : va_codes = hd::tl

(** Constructors for va_code *)
unfold let va_Block (block:va_codes) : va_code = Block block
unfold let va_IfElse (ifCond:ocmp) (ifTrue:va_code) (ifFalse:va_code) : va_code = IfElse ifCond ifTrue ifFalse
unfold let va_While (whileCond:ocmp) (whileBody:va_code) : va_code = While whileCond whileBody

val va_cmp_eq (o1:va_operand) (o2:va_operand) : ocmp
val va_cmp_ne (o1:va_operand) (o2:va_operand) : ocmp
val va_cmp_le (o1:va_operand) (o2:va_operand) : ocmp
val va_cmp_ge (o1:va_operand) (o2:va_operand) : ocmp
val va_cmp_lt (o1:va_operand) (o2:va_operand) : ocmp
val va_cmp_gt (o1:va_operand) (o2:va_operand) : ocmp

unfold let va_get_block (c:va_code{Block? c}) : va_codes = Block?.block c
unfold let va_get_ifCond (c:va_code{IfElse? c}) : ocmp = IfElse?.ifCond c
unfold let va_get_ifTrue (c:va_code{IfElse? c}) : va_code = IfElse?.ifTrue c
unfold let va_get_ifFalse (c:va_code{IfElse? c}) : va_code = IfElse?.ifFalse c
unfold let va_get_whileCond (c:va_code{While? c}) : ocmp = While?.whileCond c
unfold let va_get_whileBody (c:va_code{While? c}) : va_code = While?.whileBody c


val eval_code : c:va_code -> s0:va_state -> s1:va_state -> Type0
val eval_while : b:ocmp -> c:va_code -> n:nat -> s0:va_state -> s1:va_state -> Type0

(* ok for now but no need to actually expose the definition.
   instead expose lemmas about it *)
let va_state_eq (s0:va_state) (s1:va_state) : Type0 = state_eq s0 s1

let va_require (block:va_codes) (c:va_code) (s0:va_state) (s1:va_state) : Type0 =
  Cons? block /\
  Cons?.hd block == c /\
  eval_code (va_Block block) s0 s1

let va_ensure (b0:va_codes) (b1:va_codes) (s0:va_state) (s1:va_state) (sN:va_state) : Type0 =
  Cons? b0 /\
  Cons?.tl b0 == b1 /\
  eval_code (Cons?.hd b0) s0 s1 /\
  eval_code (va_Block b1) s1 sN

val eval_ocmp : s:va_state -> c:ocmp -> GTot bool

val lemma_cmp_eq : s:va_state -> o1:va_operand -> o2:va_operand -> Lemma
  (requires True)
  (ensures  (eval_ocmp s (va_cmp_eq o1 o2)) <==> (va_eval_operand_uint64 s o1 == va_eval_operand_uint64 s o2))
  [SMTPat (eval_ocmp s (va_cmp_eq o1 o2))]

val lemma_cmp_ne : s:va_state -> o1:va_operand -> o2:va_operand -> Lemma
  (requires True)
  (ensures  (eval_ocmp s (va_cmp_ne o1 o2)) <==> (va_eval_operand_uint64 s o1 <> va_eval_operand_uint64 s o2))
  [SMTPat (eval_ocmp s (va_cmp_ne o1 o2))]

val lemma_cmp_le : s:va_state -> o1:va_operand -> o2:va_operand -> Lemma
  (requires True)
  (ensures  (eval_ocmp s (va_cmp_le o1 o2)) <==> (va_eval_operand_uint64 s o1 <= va_eval_operand_uint64 s o2))
  [SMTPat (eval_ocmp s (va_cmp_le o1 o2))]

val lemma_cmp_ge : s:va_state -> o1:va_operand -> o2:va_operand -> Lemma
  (requires True)
  (ensures  (eval_ocmp s (va_cmp_ge o1 o2)) <==> (va_eval_operand_uint64 s o1 >= va_eval_operand_uint64 s o2))
  [SMTPat (eval_ocmp s (va_cmp_ge o1 o2))]

val lemma_cmp_lt : s:va_state -> o1:va_operand -> o2:va_operand -> Lemma
  (requires True)
  (ensures  (eval_ocmp s (va_cmp_lt o1 o2)) <==> (va_eval_operand_uint64 s o1 < va_eval_operand_uint64 s o2))
  [SMTPat (eval_ocmp s (va_cmp_lt o1 o2))]

val lemma_cmp_gt : s:va_state -> o1:va_operand -> o2:va_operand -> Lemma
  (requires True)
  (ensures  (eval_ocmp s (va_cmp_gt o1 o2)) <==> (va_eval_operand_uint64 s o1 > va_eval_operand_uint64 s o2))
  [SMTPat (eval_ocmp s (va_cmp_gt o1 o2))]

val va_lemma_block : (b0:va_codes) -> (s0:va_state) -> (sN:va_state) ->
  Ghost (va_state * va_code * va_codes)
  (requires (Cons? b0 /\ eval_code (va_Block b0) s0 sN))
  (ensures  (fun (s1, c_1, b1) ->
    b0 == va_CCons c_1 b1 /\
    eval_code c_1 s0 s1 /\
    eval_code (va_Block b1) s1 sN))

val va_lemma_empty : (s0:va_state) -> (sN:va_state) -> Ghost va_state
  (requires (eval_code (va_Block (va_CNil ())) s0 sN))
  (ensures  (fun sM -> sM == s0 /\ sM == sN))

val va_lemma_ifElse : ifb:ocmp -> ct:va_code -> cf:va_code -> s0:va_state -> sN:va_state -> Ghost (bool * va_state)
  (requires (eval_code (IfElse ifb ct cf) s0 sN))
  (ensures  (fun (cond, sM) ->
    cond == eval_ocmp s0 ifb /\
    sM == s0 /\
    (if cond then eval_code ct sM sN else eval_code cf sM sN)))

unfold let eval_while_va_code  (b:ocmp) (c:va_code) (n:nat) (s0:va_state) (sN:va_state) = s0.ok ==> eval_while b c n s0 sN

(* Temporary assumptions to get while loops working *)
let va_whileInv (b:ocmp) (c:va_code) (n:int) (s0:va_state) (sN:va_state) =
  n >= 0 /\ eval_while b c n s0 sN

val va_lemma_while : b:ocmp -> c:va_code -> s0:va_state -> sN:va_state -> Ghost (nat * va_state)
  (requires (eval_code (While b c) s0 sN))
  (ensures  (fun (n, s1) ->
    eval_while b c n s0 sN /\
    s1 == s0
  ))

val va_lemma_whileTrue : b:ocmp -> c:va_code -> n:nat -> s0:va_state -> sN:va_state -> Ghost (va_state * va_state)
  (requires
    n > 0 /\
    eval_while b c n s0 sN
  )
  (ensures (fun (s0', s1) ->
    n > 0 /\
    s0' == s0 /\
    eval_ocmp s0 b /\
    eval_code c s0' s1 /\
    (if s1.ok then eval_while b c (n - 1) s1 sN else s1 == sN)
  ))

val va_lemma_whileFalse : b:ocmp -> c:va_code -> s0:va_state -> sN:va_state -> Ghost va_state
   (requires True)        // BUG: Temporary hack, pending a fix in Vale
//  (requires (eval_while b c 0 s0 sN))
  (ensures (fun s1 ->
    s1 == s0 /\
    s1 == sN /\
    not (eval_ocmp s0 b)
  ))

(* maybe we want these to be transparent*)
val logxor64 : (x:nat64) -> (y:nat64) -> nat64
val logand64 : (x:nat64) -> (y:nat64) -> nat64
val logand128 : (x:nat128) -> (y:nat128) -> nat128
val shift_left64 : (x:nat64) -> (amt:nat64) -> nat64
val shift_right64 : (x:nat64) -> (amt:nat64) -> nat64

val reveal_logand128 (x y:nat128) : Lemma
    (requires True)
    (ensures logand128 x y == FStar.UInt.logand #128 x y)

val printer : Type0
val print_string : string -> FStar.All.ML unit
val print_header : printer -> FStar.All.ML unit
val print_proc : (name:string) -> (code:va_code) -> (label:int) -> (p:printer) -> FStar.All.ML unit
val print_footer : printer -> FStar.All.ML unit
val masm : printer
val gcc : printer

val va_code_Mov64 : dst:va_dst_operand -> src:va_operand -> Tot va_code

val va_lemma_Mov64 : va_b0:va_codes -> va_s0:va_state -> va_sN:va_state -> dst:va_dst_operand ->
  src:va_operand
  -> Ghost ((va_bM:va_codes) * (va_sM:va_state))
  (requires ((va_require va_b0 (va_code_Mov64 dst src) va_s0 va_sN) /\
    (va_is_dst_dst_operand_uint64 dst va_s0) /\ (va_is_src_operand_uint64 src va_s0) /\ (va_get_ok
    va_s0)))
  (ensures (fun ((va_bM:va_codes), (va_sM:va_state)) -> ((va_ensure va_b0 va_bM va_s0 va_sM va_sN)
    /\ (va_get_ok va_sM) /\ (va_eval_dst_operand_uint64 va_sM dst) == (va_eval_operand_uint64 va_s0
    src) /\ (va_state_eq va_sM (va_update_ok va_sM (va_update_dst_operand dst va_sM va_s0))))))

val va_code_Load64 : dst:va_dst_operand -> src:va_reg_operand -> offset:int -> Tot va_code

val va_lemma_Load64 : va_b0:va_codes -> va_s0:va_state -> va_sN:va_state -> dst:va_dst_operand ->
  src:va_reg_operand -> offset:int
  -> Ghost ((va_bM:va_codes) * (va_sM:va_state))
  (requires ((va_require va_b0 (va_code_Load64 dst src offset) va_s0 va_sN) /\
    (va_is_dst_dst_operand_uint64 dst va_s0) /\ (va_is_src_reg_operand_uint64 src va_s0) /\
    (va_get_ok va_s0) /\ (valid_src_addr (va_get_mem va_s0) ((va_eval_reg_operand_uint64 va_s0 src)
    + offset))))
  (ensures (fun ((va_bM:va_codes), (va_sM:va_state)) -> ((va_ensure va_b0 va_bM va_s0 va_sM va_sN)
    /\ (va_get_ok va_sM) /\ (va_eval_dst_operand_uint64 va_sM dst) == (va_subscript (va_get_mem
    va_sM) ((va_eval_reg_operand_uint64 va_s0 src) + offset)) /\ (va_state_eq va_sM (va_update_ok
    va_sM (va_update_dst_operand dst va_sM va_s0))))))

val va_code_Store64 : dst:va_reg_operand -> src:va_operand -> offset:int -> Tot va_code

val va_lemma_Store64 : va_b0:va_codes -> va_s0:va_state -> va_sN:va_state -> dst:va_reg_operand ->
  src:va_operand -> offset:int
  -> Ghost ((va_bM:va_codes) * (va_sM:va_state))
  (requires ((va_require va_b0 (va_code_Store64 dst src offset) va_s0 va_sN) /\
    (va_is_src_reg_operand_uint64 dst va_s0) /\ (va_is_src_operand_uint64 src va_s0) /\ (va_get_ok
    va_s0) /\ (valid_dst_addr (va_get_mem va_s0) ((va_eval_reg_operand_uint64 va_s0 dst) +
    offset))))
  (ensures (fun ((va_bM:va_codes), (va_sM:va_state)) -> ((va_ensure va_b0 va_bM va_s0 va_sM va_sN)
    /\ (va_get_ok va_sM) /\ (va_get_mem va_sM) == (va_update (va_get_mem va_s0)
    ((va_eval_reg_operand_uint64 va_s0 dst) + offset) (va_eval_operand_uint64 va_s0 src)) /\
    (va_state_eq va_sM (va_update_mem va_sM (va_update_ok va_sM va_s0))))))

val va_code_Add64 : dst:va_dst_operand -> src:va_operand -> Tot va_code

val va_lemma_Add64 : va_b0:va_codes -> va_s0:va_state -> va_sN:va_state -> dst:va_dst_operand ->
  src:va_operand
  -> Ghost ((va_bM:va_codes) * (va_sM:va_state))
  (requires ((va_require va_b0 (va_code_Add64 dst src) va_s0 va_sN) /\
    (va_is_dst_dst_operand_uint64 dst va_s0) /\ (va_is_src_operand_uint64 src va_s0) /\ (va_get_ok
    va_s0) /\ (va_eval_operand_uint64 va_s0 src) + (va_eval_dst_operand_uint64 va_s0 dst) <
    nat64_max))
  (ensures (fun ((va_bM:va_codes), (va_sM:va_state)) -> ((va_ensure va_b0 va_bM va_s0 va_sM va_sN)
    /\ (va_get_ok va_sM) /\ (eq_int (va_eval_dst_operand_uint64 va_sM dst)
    ((va_eval_dst_operand_uint64 va_s0 dst) + (va_eval_operand_uint64 va_s0 src))) /\ (va_state_eq
    va_sM (va_update_flags va_sM (va_update_ok va_sM (va_update_dst_operand dst va_sM va_s0)))))))

val va_code_Add64Wrap : dst:va_dst_operand -> src:va_operand -> Tot va_code

val va_lemma_Add64Wrap : va_b0:va_codes -> va_s0:va_state -> va_sN:va_state -> dst:va_dst_operand
  -> src:va_operand
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

val va_code_AddLea64 : dst:va_dst_operand -> src1:va_operand -> src2:va_operand -> Tot va_code

val va_lemma_AddLea64 : va_b0:va_codes -> va_s0:va_state -> va_sN:va_state -> dst:va_dst_operand ->
  src1:va_operand -> src2:va_operand
  -> Ghost ((va_bM:va_codes) * (va_sM:va_state))
  (requires ((va_require va_b0 (va_code_AddLea64 dst src1 src2) va_s0 va_sN) /\
    (va_is_dst_dst_operand_uint64 dst va_s0) /\ (va_is_src_operand_uint64 src1 va_s0) /\
    (va_is_src_operand_uint64 src2 va_s0) /\ (va_get_ok va_s0) /\ (va_eval_operand_uint64 va_s0
    src1) + (va_eval_operand_uint64 va_s0 src2) < nat64_max))
  (ensures (fun ((va_bM:va_codes), (va_sM:va_state)) -> ((va_ensure va_b0 va_bM va_s0 va_sM va_sN)
    /\ (va_get_ok va_sM) /\ (eq_int (va_eval_dst_operand_uint64 va_sM dst) ((va_eval_operand_uint64
    va_s0 src1) + (va_eval_operand_uint64 va_s0 src2))) /\ (va_state_eq va_sM (va_update_ok va_sM
    (va_update_dst_operand dst va_sM va_s0))))))

val va_code_Adc64Wrap : dst:va_dst_operand -> src:va_operand -> Tot va_code

val va_lemma_Adc64Wrap : va_b0:va_codes -> va_s0:va_state -> va_sN:va_state -> dst:va_dst_operand
  -> src:va_operand
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

val va_code_Sub64 : dst:va_dst_operand -> src:va_operand -> Tot va_code

val va_lemma_Sub64 : va_b0:va_codes -> va_s0:va_state -> va_sN:va_state -> dst:va_dst_operand ->
  src:va_operand
  -> Ghost ((va_bM:va_codes) * (va_sM:va_state))
  (requires ((va_require va_b0 (va_code_Sub64 dst src) va_s0 va_sN) /\
    (va_is_dst_dst_operand_uint64 dst va_s0) /\ (va_is_src_operand_uint64 src va_s0) /\ (va_get_ok
    va_s0) /\ 0 <= (va_eval_dst_operand_uint64 va_s0 dst) - (va_eval_operand_uint64 va_s0 src)))
  (ensures (fun ((va_bM:va_codes), (va_sM:va_state)) -> ((va_ensure va_b0 va_bM va_s0 va_sM va_sN)
    /\ (va_get_ok va_sM) /\ (eq_int (va_eval_dst_operand_uint64 va_sM dst)
    ((va_eval_dst_operand_uint64 va_s0 dst) - (va_eval_operand_uint64 va_s0 src))) /\ (va_state_eq
    va_sM (va_update_flags va_sM (va_update_ok va_sM (va_update_dst_operand dst va_sM va_s0)))))))

val va_code_Sub64Wrap : dst:va_dst_operand -> src:va_operand -> Tot va_code

val va_lemma_Sub64Wrap : va_b0:va_codes -> va_s0:va_state -> va_sN:va_state -> dst:va_dst_operand
  -> src:va_operand
  -> Ghost ((va_bM:va_codes) * (va_sM:va_state))
  (requires ((va_require va_b0 (va_code_Sub64Wrap dst src) va_s0 va_sN) /\
    (va_is_dst_dst_operand_uint64 dst va_s0) /\ (va_is_src_operand_uint64 src va_s0) /\ (va_get_ok
    va_s0)))
  (ensures (fun ((va_bM:va_codes), (va_sM:va_state)) -> ((va_ensure va_b0 va_bM va_s0 va_sM va_sN)
    /\ (va_get_ok va_sM) /\ (va_eval_dst_operand_uint64 va_sM dst) == ((va_eval_dst_operand_uint64
    va_s0 dst) - (va_eval_operand_uint64 va_s0 src)) `op_Modulus` nat64_max /\ (va_state_eq va_sM
    (va_update_flags va_sM (va_update_ok va_sM (va_update_dst_operand dst va_sM va_s0)))))))

val va_code_Mul64Wrap : src:va_operand -> Tot va_code

val va_lemma_Mul64Wrap : va_b0:va_codes -> va_s0:va_state -> va_sN:va_state -> src:va_operand
  -> Ghost ((va_bM:va_codes) * (va_sM:va_state))
  (requires ((va_require va_b0 (va_code_Mul64Wrap src) va_s0 va_sN) /\ (va_is_src_operand_uint64
    src va_s0) /\ (va_get_ok va_s0)))
  (ensures (fun ((va_bM:va_codes), (va_sM:va_state)) -> ((va_ensure va_b0 va_bM va_s0 va_sM va_sN)
    /\ (va_get_ok va_sM) /\ nat64_max `op_Multiply` (va_get_reg Rdx va_sM) + (va_get_reg Rax va_sM)
    == (va_get_reg Rax va_s0) `op_Multiply` (va_eval_operand_uint64 va_s0 src) /\ (va_state_eq
    va_sM (va_update_reg Rdx va_sM (va_update_reg Rax va_sM (va_update_flags va_sM (va_update_ok
    va_sM va_s0))))))))

val va_code_IMul64 : dst:va_dst_operand -> src:va_operand -> Tot va_code

val va_lemma_IMul64 : va_b0:va_codes -> va_s0:va_state -> va_sN:va_state -> dst:va_dst_operand ->
  src:va_operand
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

val va_code_Xor64 : dst:va_dst_operand -> src:va_operand -> Tot va_code

val va_lemma_Xor64 : va_b0:va_codes -> va_s0:va_state -> va_sN:va_state -> dst:va_dst_operand ->
  src:va_operand
  -> Ghost ((va_bM:va_codes) * (va_sM:va_state))
  (requires ((va_require va_b0 (va_code_Xor64 dst src) va_s0 va_sN) /\
    (va_is_dst_dst_operand_uint64 dst va_s0) /\ (va_is_src_operand_uint64 src va_s0) /\ (va_get_ok
    va_s0)))
  (ensures (fun ((va_bM:va_codes), (va_sM:va_state)) -> ((va_ensure va_b0 va_bM va_s0 va_sM va_sN)
    /\ (va_get_ok va_sM) /\ (va_eval_dst_operand_uint64 va_sM dst) == (logxor64
    (va_eval_dst_operand_uint64 va_s0 dst) (va_eval_operand_uint64 va_s0 src)) /\ (va_state_eq
    va_sM (va_update_flags va_sM (va_update_ok va_sM (va_update_dst_operand dst va_sM va_s0)))))))

val va_code_And64 : dst:va_dst_operand -> src:va_operand -> Tot va_code

val va_lemma_And64 : va_b0:va_codes -> va_s0:va_state -> va_sN:va_state -> dst:va_dst_operand ->
  src:va_operand
  -> Ghost ((va_bM:va_codes) * (va_sM:va_state))
  (requires ((va_require va_b0 (va_code_And64 dst src) va_s0 va_sN) /\
    (va_is_dst_dst_operand_uint64 dst va_s0) /\ (va_is_src_operand_uint64 src va_s0) /\ (va_get_ok
    va_s0)))
  (ensures (fun ((va_bM:va_codes), (va_sM:va_state)) -> ((va_ensure va_b0 va_bM va_s0 va_sM va_sN)
    /\ (va_get_ok va_sM) /\ (va_eval_dst_operand_uint64 va_sM dst) == (logand64
    (va_eval_dst_operand_uint64 va_s0 dst) (va_eval_operand_uint64 va_s0 src)) /\ (va_state_eq
    va_sM (va_update_flags va_sM (va_update_ok va_sM (va_update_dst_operand dst va_sM va_s0)))))))

val va_code_Shl64 : dst:va_dst_operand -> amt:va_shift_amt -> Tot va_code

val va_lemma_Shl64 : va_b0:va_codes -> va_s0:va_state -> va_sN:va_state -> dst:va_dst_operand ->
  amt:va_shift_amt
  -> Ghost ((va_bM:va_codes) * (va_sM:va_state))
  (requires ((va_require va_b0 (va_code_Shl64 dst amt) va_s0 va_sN) /\
    (va_is_dst_dst_operand_uint64 dst va_s0) /\ (va_is_src_shift_amt_uint64 amt va_s0) /\
    (va_get_ok va_s0)))
  (ensures (fun ((va_bM:va_codes), (va_sM:va_state)) -> ((va_ensure va_b0 va_bM va_s0 va_sM va_sN)
    /\ (va_get_ok va_sM) /\ (va_eval_dst_operand_uint64 va_sM dst) == (shift_left64
    (va_eval_dst_operand_uint64 va_s0 dst) (va_eval_shift_amt_uint64 va_s0 amt)) /\ (va_state_eq
    va_sM (va_update_flags va_sM (va_update_ok va_sM (va_update_dst_operand dst va_sM va_s0)))))))

val va_code_Shr64 : dst:va_dst_operand -> amt:va_shift_amt -> Tot va_code

val va_lemma_Shr64 : va_b0:va_codes -> va_s0:va_state -> va_sN:va_state -> dst:va_dst_operand ->
  amt:va_shift_amt
  -> Ghost ((va_bM:va_codes) * (va_sM:va_state))
  (requires ((va_require va_b0 (va_code_Shr64 dst amt) va_s0 va_sN) /\
    (va_is_dst_dst_operand_uint64 dst va_s0) /\ (va_is_src_shift_amt_uint64 amt va_s0) /\
    (va_get_ok va_s0)))
  (ensures (fun ((va_bM:va_codes), (va_sM:va_state)) -> ((va_ensure va_b0 va_bM va_s0 va_sM va_sN)
    /\ (va_get_ok va_sM) /\ (va_eval_dst_operand_uint64 va_sM dst) == (shift_right64
    (va_eval_dst_operand_uint64 va_s0 dst) (va_eval_shift_amt_uint64 va_s0 amt)) /\ (va_state_eq
    va_sM (va_update_flags va_sM (va_update_ok va_sM (va_update_dst_operand dst va_sM va_s0)))))))
