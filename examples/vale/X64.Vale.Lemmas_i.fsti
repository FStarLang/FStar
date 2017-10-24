module X64.Vale.Lemmas_i
open X64.Machine_s
open X64.Vale.State_i
open X64.Vale.StateLemmas_i
open FStar.UInt
module S = X64.Semantics_s

unfold let code = S.code
unfold let codes = S.codes

let cf (flags:int) : bool = S.cf (S.u (int_to_nat64 flags))

let eval_code (c:code) (s0:state) (s1:state) : Type0 =
  exists (fuel:nat).{:pattern (S.eval_code c fuel (state_to_S s0))}
    Some (state_to_S s1) == S.eval_code c fuel (state_to_S s0)

val eval_while : b:S.ocmp -> c:code -> n:nat -> s0:state -> s1:state -> Type0

let eval_ocmp (s:state) (c:S.ocmp) : bool = S.eval_ocmp (state_to_S s) c

val lemma_cmp_eq : s:state -> o1:operand -> o2:operand -> Lemma
  (ensures eval_ocmp s (S.OEq o1 o2) <==> eval_operand o1 s == eval_operand o2 s)
  [SMTPat (eval_ocmp s (S.OEq o1 o2))]

val lemma_cmp_ne : s:state -> o1:operand -> o2:operand -> Lemma
  (ensures eval_ocmp s (S.ONe o1 o2) <==> eval_operand o1 s <> eval_operand o2 s)
  [SMTPat (eval_ocmp s (S.ONe o1 o2))]

val lemma_cmp_le : s:state -> o1:operand -> o2:operand -> Lemma
  (ensures eval_ocmp s (S.OLe o1 o2) <==> eval_operand o1 s <= eval_operand o2 s)
  [SMTPat (eval_ocmp s (S.OLe o1 o2))]

val lemma_cmp_ge : s:state -> o1:operand -> o2:operand -> Lemma
  (ensures eval_ocmp s (S.OGe o1 o2) <==> eval_operand o1 s >= eval_operand o2 s)
  [SMTPat (eval_ocmp s (S.OGe o1 o2))]

val lemma_cmp_lt : s:state -> o1:operand -> o2:operand -> Lemma
  (ensures eval_ocmp s (S.OLt o1 o2) <==> eval_operand o1 s < eval_operand o2 s)
  [SMTPat (eval_ocmp s (S.OLt o1 o2))]

val lemma_cmp_gt : s:state -> o1:operand -> o2:operand -> Lemma
  (ensures eval_ocmp s (S.OGt o1 o2) <==> eval_operand o1 s > eval_operand o2 s)
  [SMTPat (eval_ocmp s (S.OGt o1 o2))]

val lemma_block : (b0:codes) -> (s0:state) -> (sN:state) ->
  Ghost (state * code * codes)
  (requires (Cons? b0 /\ eval_code (Block b0) s0 sN))
  (ensures  (fun (s1, c1, b1) ->
    b0 == c1::b1 /\
    eval_code c1 s0 s1 /\
    eval_code (Block b1) s1 sN))

val lemma_empty : (s0:state) -> (sN:state) -> Ghost state
  (requires (eval_code (Block []) s0 sN))
  (ensures  (fun sM -> sM == s0 /\ sM == sN))

val lemma_ifElse : ifb:S.ocmp -> ct:code -> cf:code -> s0:state -> sN:state -> Ghost (bool * state)
  (requires (eval_code (IfElse ifb ct cf) s0 sN))
  (ensures  (fun (cond, sM) ->
    cond == eval_ocmp s0 ifb /\
    sM == s0 /\
    (if cond then eval_code ct sM sN else eval_code cf sM sN)))

val lemma_while : b:S.ocmp -> c:code -> s0:state -> sN:state -> Ghost (nat * state)
  (requires (eval_code (While b c) s0 sN))
  (ensures  (fun (n, s1) ->
    eval_while b c n s0 sN /\
    s1 == s0
  ))

val lemma_whileTrue : b:S.ocmp -> c:code -> n:nat -> s0:state -> sN:state -> Ghost (state * state)
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

val lemma_whileFalse : b:S.ocmp -> c:code -> s0:state -> sN:state -> Ghost state
  (requires True)        // BUG: Temporary hack, pending a fix in Vale
//  (requires (eval_while b c 0 s0 sN))
  (ensures (fun s1 ->
    s1 == s0 /\
    s1 == sN /\
    not (eval_ocmp s0 b)
  ))
