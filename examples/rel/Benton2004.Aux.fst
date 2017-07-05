module Benton2004.Aux

type rel (t: Type0) = t -> t -> GTot Type0

(* NOTE: I define this `holds` abstract here to prevent Z3 from looping. *)

abstract let holds (#t: Type0) (p: rel t) (s s' : t) : GTot Type0 =
  p s s'
abstract let holds_equiv (#t: Type0) (p: rel t) (s s' : t) : Lemma
  (holds p s s' <==> p s s')
= ()
