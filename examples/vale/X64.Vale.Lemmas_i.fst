module X64.Vale.Lemmas_i
open X64.Machine_s
open X64.Vale.State_i
open FStar.UInt
module S = X64.Semantics_s

#reset-options "--initial_fuel 2 --max_fuel 2"

let eval_while b c n s0 s1 : Type0 = admit ()

let lemma_cmp_eq s o1 o2 = ()
let lemma_cmp_ne s o1 o2 = ()
let lemma_cmp_le s o1 o2 = ()
let lemma_cmp_ge s o1 o2 = ()
let lemma_cmp_lt s o1 o2 = ()
let lemma_cmp_gt s o1 o2 = ()

let lemma_block (b0:codes) (s0:state) (sN:state) =
  let c1::b1 = b0 in
  let s0' = state_to_S s0 in
  // let Some s1' = S.eval_code c1 fuel s0' in
  // let s1 = state_of_S s1' in
  // (s1, c1, b1)
  admit () // TODO

let lemma_empty (s0:state) (sN:state) =
  assume False; // TODO
  s0

let lemma_ifElse (ifb:S.ocmp) (ct:code) (cf:code) (s0:state) (sN:state) =
  (eval_ocmp s0 ifb, s0)

let lemma_while b c s0 sN = admit () // TODO
let lemma_whileTrue b c n s0 sN = admit () // TODO
let lemma_whileFalse b c s0 sN = admit () // TODO

