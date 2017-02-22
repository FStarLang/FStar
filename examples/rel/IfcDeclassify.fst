module IfcDeclassify

open FStar.DM4F.ST
open Rel

(* Simple example illustrating an IFC property that needs to be stated
   in terms of an instrumented monad. *)

(* We define a variant of the state effect where the state has 3 fields:
   - a secret integer cell
   - a public integer cell
   - a boolean: when this is set the secret integer is declassified
                and allowed to leak to the public cell *)

type state = {secret:int;
              public:int;
              release:bool}

reifiable reflectable new_effect_for_free STATE = STATE_h state

unfold let lift_pure_stint (a:Type) (wp:pure_wp a) (s:state) (p:STATE?.post a) =
  wp (fun a -> p (a, s))
sub_effect PURE ~> STATE = lift_pure_stint

effect ST (a:Type) (pre: STATE?.pre) (post: (state -> a -> state -> GTot Type0)) =
  STATE a (fun n0 p -> pre n0 /\
            (forall a n1. pre n0 /\ post n0 a n1 ==> p (a, n1)))

effect St (a:Type) =
  STATE a (fun (_:state) (p:(a * state) -> Type0) -> forall (x:(a * state)). p x)

(* equivalence *)

type low_equiv (s : rel state) = (R?.l s).public == (R?.r s).public

let reif (f:unit -> St unit) (s:state) = snd (reify (f ()) s)

let ni (f:unit -> St unit) = (s:rel state) ->
  Lemma (requires (low_equiv s))
        (ensures (let sl = snd (reify (f ()) (R?.l s)) in
                  let sr = snd (reify (f ()) (R?.r s)) in
                  (sl.release \/ sr.release \/ low_equiv (R sl sr))))

reifiable let p1 () = STATE?.put (STATE?.get())

let ni_p1 : ni p1 = fun s -> () (* nop is noninterferent *)

reifiable let p2 () =
  let s = STATE?.get() in
  STATE?.put ({secret=s.public; public=s.public; release=s.release})

let ni_p2 : ni p2 = fun s -> () (* allowed flow *)

reifiable let p3 () =
  let s = STATE?.get() in
  STATE?.put ({secret=s.secret; public=s.secret; release=s.release})

(* let ni_p3 : ni p3 = fun s -> () -- this leak fails as it should *)

reifiable let p4 () =
  let s = STATE?.get() in
  STATE?.put ({secret=s.secret; public=s.secret; release=true})

let ni_p4 : ni p4 = fun s -> () (* this leak is an allowed declassification *)
