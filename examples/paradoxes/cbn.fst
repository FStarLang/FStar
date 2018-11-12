module CBN

(* The first example here taken from LiquidHaskell:
- http://goto.ucsd.edu/~nvazou/refinement_types_for_haskell.pdf
- http://goto.ucsd.edu/~rjhala/liquid/haskell/blog/blog/2013/11/23/telling_lies.lhs/

Evaluation order matters:
- under CBV reduction explode loops, which is fine, it's in Dv
- under CBN reduction explode does a division by zero, which is
  not OK, since the only effect here is supposed to be divergence

So what this shows is that CBN I-reduction would be unsound.

 *)

val diverge : int -> Div int (requires (True)) (ensures (fun _ -> False))
let rec diverge x = diverge x

val explode : int -> Dv int
let explode x = let _ = diverge 1 in x / 0

(* 

For P-reduction (strong reduction, i.e. under binders), the type of
diverge2 below is necessarily uninhabited in a consistent system. The
type system can't prove that this type is uninhabited though.

What explode2 shows is that in a CBN system the type soundness of the
system would need to rely termination and other inherently semantic
arguments like type inhabitance of Pure types.

 *)

val explode2 : diverge2:(unit -> Lemma (ensures False)) ->
               int -> Tot int
let explode2 diverge2 x = let _ = diverge2 () in x / 0

val explode3 : diverge3:(unit -> Lemma (ensures False)) ->
               Lemma (ensures False)
let explode3 diverge3 = diverge3 ()

(* This is all very similar to Nik's example from March *)

val g : unit -> Tot unit
let g x = ()

val xxx : f:(unit -> Lemma (ensures False)) -> Lemma (ensures False)
let xxx f = f (); g ()   (* same as: g (f ()) *)

(*
val yyy : f:(unit -> Lemma (ensures False)) -> Lemma (ensures False)
let yyy f = ()  <-- type error in the tool (now allowed in meta-theory!)
*)

(*
assume val f : (unit -> Tot (u:unit{False}))
let yyy = assert(False)
 *)

(*
Although xxx -strong-CBN-> yyy, yyy doesn't have the same type as xxx,
which breaks type preservation. F* can't automatically reason about
the fact that f is uninhabited and exploit that for typing ().

Under (strong) CBV reduction xxx is stuck, because f is a variable
(and in fact it can't be instantiated because the type is uninhabited)
*)

(* This example can be ported one level up to type reduction *)

val diverge' : unit -> Pure bool (requires False) (ensures (fun _ -> True))
let rec diverge' x = diverge' x

type tg (u:unit{False}) = u':unit{diverge'()}

type txxx (f:(unit -> Lemma (ensures False))) =
  tg (f ())

(*
type tyyy (f:(unit -> Lemma (ensures False))) =
  u':unit{diverge'()} <-- type error
*)

(*
Although txxx -strong-CBN-> tyyy, tyyy is not well-kinded, which
breaks preservation for type reduction (conversion). Again, under
(strong) CBV reduction txxx is stuck because f is a variable.
 *)
