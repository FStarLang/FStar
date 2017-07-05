module Benton2004.Aux

let holds (#t: Type0) (p: rel t) (s s' : t) : GTot Type0 =
  p s s'
let holds_equiv (#t: Type0) (p: rel t) (s s' : t) : Lemma
  (holds p s s' <==> p s s')
= ()
