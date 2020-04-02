module ResolveImplicitsHook
open FStar.Tactics
module T = FStar.Tactics
irreducible
let marker : unit = ()

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
val ( >> ) (#p #q #r : resource) (f:cmd p q) (g:cmd q r)
  : cmd p r

assume
val frame (#frame #p #q : resource) (f:cmd p q)
  : cmd (frame ** p) (frame ** q)

assume
val frame_delta (pre p post q : resource) : Type

assume
val frame2
    (#[@marker]pre #[@marker]post #[@marker]p #[@marker]q : resource)
    (#[@marker]delta:frame_delta pre p post q)
    (f:cmd p q)
  : cmd pre post


assume
val frame_delta_refl (pre p q : resource) : frame_delta pre p pre q

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
  frame f2 >>
  frame f2

// let test1 : cmd (r1 ** r2) (r1 ** r2) =
//   frame f1 >>
//   frame f2

[@(resolve_implicits)
  (marker)]
let resolve_tac () : Tac unit =
  T.dump "Start!";
  let _ = T.repeat (fun () ->
    T.apply (`frame_delta_refl);
    T.dump "Next")
  in
  ()


// let test1 (b:bool)
//   : cmd (r1 ** r2 ** r3 ** r4 ** r5)
//         (r1 ** r2 ** r3 ** r4 ** r5)
//   =
//   frame2 f1 >>
//   frame2 f2 >>
//   frame2 f3 >>
//   frame2 f4 >>
//   frame2 f5

//   // >>
//   // (if b then
//   //   frame2 f3 >>
//   //   frame2 f4
//   //  else frame2 f5)


// #set-options "--print_implicits"


assume
val frame3
    (#pre #post #p #q : resource)
    (#[T.apply (`frame_delta_refl)] delta:frame_delta pre p post q)
    (f:cmd p q)
  : cmd pre post

let test2
  : cmd (r1 ** r2) (r1 ** r2)
  =
  frame3 f1 >>
  frame3 f2 >>
  frame3 f3 >>
  frame3 f4 >>
  frame3 f5
