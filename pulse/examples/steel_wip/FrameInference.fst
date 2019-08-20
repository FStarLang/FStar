module FrameInference
open FStar.Tactics
module T = FStar.Tactics
module U32 = FStar.UInt32

module R = LowStar.Resource
module A = LowStar.Array
module AR = LowStar.RST.Array
module RST = LowStar.RST
module Tac = LowStar.RST.Tactics

let cmd (r1:R.resource) (r2:R.resource) = unit -> RST.RST unit r1 (fun _ -> r2) (fun _ -> True) (fun _ _ _ -> True)

let compose (#p #q #r : R.resource)
  (f: cmd p q)
  (g: cmd q r)
  : cmd p r
  = fun _ -> g (f ())

let ( >> ) (#p #q #r : R.resource)
  (f: cmd p q)
  (g: cmd q r)
  : cmd p r
  = compose f g

let frame (#frame #p #q : R.resource) (f:cmd p q) : cmd R.(frame <*> p) R.(frame <*> q)
  = fun _ ->
   RST.rst_frame
     R.(frame <*> p)
     #p
     #unit
     (fun _ -> R.(frame <*> q))
     #(fun _ -> q)
     #frame
     #(fun _ -> True)
     #(fun _ _ _ -> True)
     (fun _ -> f ())


let frame2
    (#pre #post #p #q : R.resource)
    (#delta: R.resource{Tac.frame_delta pre p (fun _ -> post) (fun _ -> q) delta})
    (f:cmd p q)
  : cmd pre post
= fun _ ->
   RST.rst_frame
     pre
     #p
     #unit
     (fun _ -> post)
     #(fun _ -> q)
     #(magic ())//TODO: replace by delta
     #(fun _ -> True)
     #(fun _ _ _ -> True)
     (fun _ -> f ())

let f (b: A.array U32.t) : cmd (AR.array_resource b) (AR.array_resource b) =
  (fun _ -> ignore (AR.index b 0ul))

let test0 (b1: A.array U32.t) (b2: A.array U32.t)
  : cmd R.(AR.array_resource b1 <*> AR.array_resource b2) R.(AR.array_resource b1 <*> AR.array_resource b2)
 =
  compose (frame (f b2)) (frame  (f b2))


[@expect_failure]
let test1 (b1: A.array U32.t) (b2: A.array U32.t)
  : cmd R.(AR.array_resource b1 <*> AR.array_resource b2) R.(AR.array_resource b1 <*> AR.array_resource b2)
 =
  compose #R.(AR.array_resource b1 <*> AR.array_resource b2) # R.(AR.array_resource b1 <*> AR.array_resource b2)
  (frame #(AR.array_resource b2) #(AR.array_resource b1) #(AR.array_resource b1) (f b1))
  (frame #(AR.array_resource b1) #(AR.array_resource b2) #(AR.array_resource b2) (f b2))

[@resolve_implicits]
let resolve_tac () : Tac unit =
  T.dump "Start!";
  let _ = T.repeat (fun () ->
    T.apply (`Tac.resolve_frame_delta);
    T.dump "Next")
  in
  ()

// TODO: Should not expected failure
[@expect_failure]
let test2 (b1: A.array U32.t) (b2: A.array U32.t) (b3: A.array U32.t) (b4: A.array U32.t) (b5: A.array U32.t)
  : cmd R.(AR.array_resource b1 <*> AR.array_resource b2 <*> AR.array_resource b3 <*> AR.array_resource b4 <*> AR.array_resource b5)
        R.(AR.array_resource b1 <*> AR.array_resource b2 <*> AR.array_resource b3 <*> AR.array_resource b4 <*> AR.array_resource b5)
  =
  frame2 (f b1) >>
  frame2 (f b2) >>
  frame2 (f b3) >>
  frame2 (f b4) >>
  frame2 (f b5)

#set-options "--print_implicits"


let frame3
    (#pre #post #p #q : R.resource)
    (#[T.apply (`Tac.resolve_delta)] delta:R.resource{Tac.frame_delta pre p (fun _ -> post) (fun _ -> q) delta})
    (f:cmd p q)
  : cmd pre post
  =
   fun _ ->
   RST.rst_frame
     pre
     #p
     #unit
     (fun _ -> post)
     #(fun _ -> q)
     #(magic ())//TODO: replace by delta
     #(fun _ -> True)
     #(fun _ _ _ -> True)
     (fun _ -> f ())

// TODO: should not expect failure
[@expect_failure]
let test3 (b1: A.array U32.t) (b2: A.array U32.t) (b3: A.array U32.t) (b4: A.array U32.t) (b5: A.array U32.t)
  : cmd R.(AR.array_resource b1 <*> AR.array_resource b2 <*> AR.array_resource b3 <*> AR.array_resource b4 <*> AR.array_resource b5)
        R.(AR.array_resource b1 <*> AR.array_resource b2 <*> AR.array_resource b3 <*> AR.array_resource b4 <*> AR.array_resource b5)
  =
  frame3 (f b1) >>
  frame3 (f b2) >>
  frame3 (f b3) >>
  frame3 (f b4) >>
  frame3 (f b5)
