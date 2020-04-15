module Bug855b

module HST = FStar.HyperStack.ST
module I32 = FStar.Int32
module Seq = FStar.Seq

noeq
type wf_Q = 
  | Q_Cons :
    e : Seq.seq int ->
    h : (me:Seq.seq (int -> int -> HST.St int){ Seq.length e = Seq.length me}) ->
  wf_Q

let main() : HST.St I32.t =
  let q : wf_Q = Q_Cons Seq.empty Seq.empty in
  0l

