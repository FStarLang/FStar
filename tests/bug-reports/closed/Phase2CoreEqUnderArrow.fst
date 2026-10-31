module Phase2CoreEqUnderArrow

(* Relating [pspec #(dfst (mk r)) sz] to [pspec #s sz] needs [dfst (reveal (hide (|s, r|))) == s],
   an SMT fact: Core proves the arguments equal, rather than the whole types, whose
   arrow-typed implicits ([reveal #(dfst .. -> nat) sz]) the SMT solver cannot relate. *)
open FStar.Ghost
let mk (#s:Type0) (r: s -> int) : erased (t:Type0 & (t -> int)) = hide (| s, r |)
assume val pspec (#s:Type0) (sz: s -> nat) : Type0
noeq type rec_t (spec: erased (t:Type0 & (t -> int))) = {
  sz: erased (dfst spec -> nat);
  ps: erased (pspec #(dfst spec) sz)
}
let mkr (#s:Type0) (r: s -> int) (sz: erased (s -> nat)) (ps: erased (pspec #s sz)) : rec_t (mk r) =
  { sz = sz; ps = ps }
