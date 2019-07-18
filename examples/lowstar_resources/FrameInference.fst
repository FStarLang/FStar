module FrameInference
module T = FStar.Tactics
assume
val resource : Type u#1

assume
val emp : resource

assume
val ptr (a:Type0) : Type0

assume
val ptr_resource (x:ptr 'a) : resource

assume
val ( ** ) (r1 r2:resource) : resource

assume
val emp_unit (r1 :resource)
  : Lemma (r1 ** emp == r1)

assume
val commutative (r1 r2:resource)
  : Lemma (r1 ** r2 == r2 ** r1)

assume
val associative (r1 r2 r3:resource)
  : Lemma (r1 ** (r2 ** r3) == (r1 ** r2) ** r3)

[@unifier_hint_injective]
assume
val cmd (r1:resource) (r2:resource) : Type

assume
val seq (#p #q #r : resource) (f:cmd p q) (g:cmd q r)
  : cmd p r

assume
val frame (#frame #p #q : resource) (f:cmd p q)
  : cmd (frame ** p) (frame ** q)

assume
val frame_delta (pre p post q : resource) : Type

assume
val frame2
    (#pre #post #p #q : resource)
    // (#delta:frame_delta pre p post q)
    (f:cmd p q)
  : cmd pre post


////////////////////////////////////////////////////////////////////////////////

assume val r1 : resource
assume val r2 : resource
assume val r3 : resource
assume val r4 : resource
assume val r5 : resource

assume val f1: cmd r1 r1
assume val f2: cmd r2 r2
assume val f3: cmd r3 r3
assume val f4: cmd r4 r4
assume val f5: cmd r5 r5


let test0 : cmd (r1 ** r2) (r1 ** r2) =
  seq (frame f2)
      (frame f2)


// let test1
//   : cmd (r1 ** r2) (r1 ** r2)
//   by (T.dump "A")
//   =
//   seq (frame2 #_ #_ #_ #_ f1)
//       (frame2 f2)
