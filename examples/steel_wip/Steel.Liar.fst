module Steel.Liar
(* This is an assumed abstraction layer on top of LowStar.RST

   It anticipates what we expect will be provided by LowStar.RST once
   we have layered effects to seal its abstraction.

   As such, this layer is temporary and it lies about what we can
   actually prove in the current model. Hence the name.
*)
include Steel.RST
module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack

effect ST (a:Type) (pre:ST.st_pre) (post: (m0:HS.mem -> Tot (ST.st_post' a (pre m0)))) =
       ST.STATE a
             (fun (p:ST.st_post a) (h:HS.mem) -> pre h /\ (forall a h1. (pre h /\ post h a h1) ==> p a h1)) (* WP *)


effect Steel
  (a: Type)
  (res0: resource)
  (res1: a -> resource)
  (pre: rprop res0)
  (post: rmem res0 -> (x:a) -> rprop (res1 x))
= ST
  a
  (fun h0 ->
    inv res0 h0 /\
    pre (mk_rmem res0 h0))
  (fun h0 x h1 ->
    inv res0 h0 /\
    pre (mk_rmem res0 h0) /\
    inv (res1 x) h1 /\
    post (mk_rmem res0 h0) x (mk_rmem (res1 x) h1)
  )

effect St (a:Type) (pre:resource) (post: a -> resource) =
  Steel a pre post (fun _ -> True) (fun _ _ _ -> True)

module RTac = Steel.Tactics

assume
val frame
  (outer0:resource)
  (#inner0:resource)
  (#a:Type)
  (outer1:a -> resource)
  (#inner1:a -> resource)
  (#[RTac.resolve_delta ()]
     delta:resource{
       FStar.Tactics.with_tactic
         RTac.resolve_frame_delta
         (RTac.frame_delta outer0 inner0 outer1 inner1 delta)
     }
   )
  (#pre:rprop inner0)
  (#post:rmem inner0 -> (x:a) -> rprop (inner1 x))
   ($f:unit -> Steel a inner0 inner1 pre post)
  : Steel a outer0 outer1
    (// FStar.Tactics.by_tactic_seman RTac.resolve_frame_delta
     //  (RTac.frame_delta outer0 inner0 outer1 inner1 delta);
     assume (inner0 `is_subresource_of` outer0);
      fun h ->
        pre (focus_rmem h inner0)
    )
    (reveal_can_be_split_into ();
      fun h0 x h1 ->
        assume (inner1 x `is_subresource_of` outer1 x);
        post
          (focus_rmem h0 inner0)
          x
          (focus_rmem h1 (inner1 x)) /\
        (assume(delta `is_subresource_of` outer0);
         assume(delta `is_subresource_of` outer1 x);
         focus_rmem h0 delta == focus_rmem h1 delta)
    )

assume
val as_steel (#a:_) (#inner0:_) (#inner1:_) (#pre:_) (#post:_)
             ($f:unit -> RST a inner0 inner1 pre post)
   : Steel a inner0 inner1 pre post


let resource_assertion (r:resource)
  : Steel unit
        r
        (fun _ -> r)
        (fun _ -> True)
        (fun _ _ _ -> True)
  = ()
