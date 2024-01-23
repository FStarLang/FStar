module PulseCore.Atomic
open PulseCore.InstantiatedSemantics
open PulseCore.Action
open FStar.Ghost

type observability =
  | Observable
  | Unobservable

let at_most_one_observable o1 o2 =
  match o1, o2 with
  | Observable, Observable -> false
  | _ -> true

let join_obs o1 o2 =
  match o1, o2 with
  | Observable, _
  | _, Observable -> Observable
  | _ -> Unobservable

(* stt_unobservable a opens pre post: The type of a pulse computation
   that when run in a state satisfying `pre`
   takes an unobservable atomic step
   potentially opening invariants in `opens`
   and returns `x:a`
   such that the final state satisfies `post x` *)
[@@extract_as_impure_effect]
val stt_atomic
    (a:Type u#a)
    (#obs:observability)
    (opens:inames)
    (pre:slprop)
    (post:a -> slprop)
: Type u#(max 2 a)

val return_atomic
    (#a:Type u#a)
    (x:a)
    (p:a -> slprop)
: stt_atomic a #Unobservable emp_inames (p x) (fun r -> p r ** pure (r == x))

val bind_atomic
    (#a:Type u#a)
    (#b:Type u#b)
    (#obs1:_)
    (#obs2:observability { at_most_one_observable obs1 obs2 })
    (#opens:inames)
    (#pre1:slprop)
    (#post1:a -> slprop)
    (#post2:b -> slprop)
    (e1:stt_atomic a #obs1 opens pre1 post1)
    (e2:(x:a -> stt_atomic b #obs2 opens (post1 x) post2))
: stt_atomic b #(join_obs obs1 obs2) opens pre1 post2

val lift_atomic0
    (#a:Type u#0)
    (#obs:_)
    (#opens:inames)
    (#pre:slprop)
    (#post:a -> slprop)
    (e:stt_atomic a #obs opens pre post)
: stt a pre post

val lift_atomic1
    (#a:Type u#1)
    (#obs:_)
    (#opens:inames)
    (#pre:slprop)
    (#post:a -> slprop)
    (e:stt_atomic a #obs opens pre post)
: stt a pre post

val lift_atomic2
    (#a:Type u#2)
    (#obs:_)
    (#opens:inames)
    (#pre:slprop)
    (#post:a -> slprop)
    (e:stt_atomic a #obs opens pre post)
: stt a pre post

val frame_atomic
    (#a:Type u#a)
    (#obs: observability)
    (#opens:inames)
    (#pre:slprop)
    (#post:a -> slprop)
    (frame:slprop)
    (e:stt_atomic a #obs opens pre post)
: stt_atomic a #obs opens (pre ** frame) (fun x -> post x ** frame)

val sub_atomic
    (#a:Type u#a)
    (#obs:_)
    (#opens:inames)
    (#pre1:slprop)
    (pre2:slprop)
    (#post1:a -> slprop)
    (post2:a -> slprop)
    (pf1 : slprop_equiv pre1 pre2)
    (pf2 : slprop_post_equiv post1 post2)
    (e:stt_atomic a #obs opens pre1 post1)
: stt_atomic a #obs opens pre2 post2

val sub_invs_stt_atomic
    (#a:Type u#a)
    (#obs:_)
    (#opens1 #opens2:inames)
    (#pre:slprop)
    (#post:a -> slprop)
    (e:stt_atomic a #obs opens1 pre post)
    (_ : squash (inames_subset opens1 opens2))
: stt_atomic a #obs opens2 pre post

(* stt_ghost a opens pre post: The type of a pulse computation
   that when run in a state satisfying `pre`
   takes a single ghost atomic step (i.e. a step that does not modify the heap, and does not get extracted)
   potentially opening invariants in `opens`
   and returns `x:a`
   such that the final state satisfies `post x` *)
[@@ erasable]
val stt_ghost
    (a:Type u#a)
    (opens:inames)
    (pre:slprop)
    (post:a -> slprop)
: Type u#(max 2 a)

val return_ghost
    (#a:Type u#a)
    (x:a)
    (p:a -> slprop)
: stt_ghost a emp_inames (p x) (fun r -> p r ** pure (r == x))

val bind_ghost
    (#a:Type u#a)
    (#b:Type u#b)
    (#opens:inames)
    (#pre1:slprop)
    (#post1:a -> slprop)
    (#post2:b -> slprop)
    (e1:stt_ghost a opens pre1 post1)
    (e2:(x:a -> stt_ghost b opens (post1 x) post2))
: stt_ghost b opens pre1 post2

type non_informative_witness (a:Type u#a) =
  x:Ghost.erased a -> y:a{y == Ghost.reveal x}

val lift_ghost
    (#a:Type u#a)
    (#opens:inames)
    (#pre:slprop)
    (#post:a -> slprop)
    (e:stt_ghost a opens pre post)
    (reveal_a:non_informative_witness a)
: stt_atomic a #Unobservable opens pre post

val frame_ghost
    (#a:Type u#a)
    (#opens:inames)
    (#pre:slprop)
    (#post:a -> slprop)
    (frame:slprop)
    (e:stt_ghost a opens pre post)
: stt_ghost a opens (pre ** frame) (fun x -> post x ** frame)
 
//////////////////////////////////////////////////////////////////

val new_invariant
    (p:slprop)
: stt_atomic (inv p) #Unobservable emp_inames p (fun _ -> emp)

val with_invariant
    (#a:Type)
    (#obs:_)
    (#fp:slprop)
    (#fp':a -> slprop)
    (#f_opens:inames)
    (#p:slprop)
    (i:inv p{not (mem_inv f_opens i)})
    ($f:unit -> stt_atomic a #obs f_opens
                            (p ** fp)
                            (fun x -> p ** fp' x))
: stt_atomic a #obs (add_inv f_opens i) fp fp'
