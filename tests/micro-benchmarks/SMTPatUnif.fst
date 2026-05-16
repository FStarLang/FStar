module SMTPatUnif

(* Regression test for ignoring SMT patterns when relating two Lemma
   computations by equality during subcomp.  *)

assume val f (x:int) : int
assume val g (x:int) : int

let lem_ty (k:int -> int) = x:int -> Lemma (x == x) [SMTPat (k x)]

noeq
type cell (a:Type) = { get : a }

let coerce (c : cell (lem_ty f)) : cell (lem_ty g) = c
