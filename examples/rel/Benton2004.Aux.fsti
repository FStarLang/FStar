module Benton2004.Aux

type rel (t: Type0) = t -> t -> GTot Type0

(* NOTE: I declare this `holds` here to prevent Z3 from looping. (`abstract` is not enough.) *)

val holds (#t: Type0) (p: rel t) (s s' : t) : GTot Type0
val holds_equiv (#t: Type0) (p: rel t) (s s' : t) : Lemma
  (holds p s s' <==> p s s')
