module PulseCore.Action
module I = PulseCore.InstantiatedSemantics
module PP = PulseCore.Preorder
open PulseCore.InstantiatedSemantics
open FStar.PCM
open FStar.Ghost

type reifiability =
 | Ghost
 | Reifiable
 | UsesInvariants

let ( ^^ ) (r1 r2 : reifiability) : reifiability =
  if r1 = r2 then r1
  else (
   match r1, r2 with
   | Ghost, Reifiable
   | Reifiable, Ghost -> Reifiable
   | _ -> UsesInvariants
  )

val iname : eqtype

let inames = Ghost.erased (FStar.Set.set iname)

let emp_inames : inames = Ghost.hide Set.empty

let join_inames (is1 is2 : inames) : inames =
  Set.union is1 is2

let inames_subset (is1 is2 : inames) : Type0 =
  Set.subset is1 is2

let (/!) (is1 is2 : inames) : Type0 =
  Set.disjoint is1 is2

unfold
let inames_disj (ictx:inames) : Type = is:inames{is /! ictx}

val act 
    (a:Type u#a)
    (tag:reifiability)
    (opens:inames)
    (pre:slprop)
    (post:a -> slprop)
: Type u#(max a 2)

val return 
    (#a:Type u#a)
    (#r:_)
    (#post:a -> slprop)
    (x:a)
: act a r emp_inames (post x) post

val bind
     (#a:Type u#a)
     (#b:Type u#b)
     (#r:reifiability)
     (#opens:inames)
     (#pre1 #post1 #post2:_)
     (f:act a r opens pre1 post1)
     (g:(x:a -> act b r opens (post1 x) post2))
: act b r opens pre1 post2

val frame
     (#a:Type u#a)
     (#r:reifiability)
     (#opens:inames)
     (#pre #post #frame:_)
     (f:act a r opens pre post)
: act a r opens (pre ** frame) (fun x -> post x ** frame)

val lift_ghost_reifiable
    (#a:Type)
    (#pre:slprop)
    (#post:a -> slprop)
    (#opens:inames)
    (f:act a Ghost opens pre post)
: act a Reifiable opens pre post

val lift_reifiability 
    (#a:Type)
    (#r:_)
    (#pre:slprop)
    (#post:a -> slprop)
    (#opens:inames)
    (f:act a r opens pre post)
: act a UsesInvariants opens pre post

val weaken 
    (#a:Type)
    (#pre:slprop)
    (#post:a -> slprop)
    (#r0 #r1:reifiability)
    (#opens opens':inames)
    (f:act a r0 opens pre post)
: act a (r0 ^^ r1) (Set.union opens opens') pre post


val sub 
    (#a:Type)
    (#pre:slprop)
    (#post:a -> slprop)
    (#r:reifiability)
    (#opens:inames)
    (pre':slprop { slprop_equiv pre pre' })
    (post':a -> slprop { forall x. slprop_equiv (post x) (post' x) })
    (f:act a r opens pre post)
: act a r opens pre' post'

val lift (#a:Type u#100) #r #opens (#pre:slprop) (#post:a -> slprop)
         (m:act a r opens pre post)
: I.stt a pre post

val lift0 (#a:Type u#0) #r #opens #pre #post
          (m:act a r opens pre post)
: I.stt a pre post

val lift1 (#a:Type u#1) #r #opens #pre #post
          (m:act a r opens pre post)
: I.stt a pre post

val lift2 (#a:Type u#2) #r #opens #pre #post
          (m:act a r opens pre post)
: I.stt a pre post

//////////////////////////////////////////////////////////////////////
// Invariants
//////////////////////////////////////////////////////////////////////

val inv (p:slprop) : Type0

val allocated_name : Type0

val allocated_name_of_inv (#p:_) (i:inv p)
: allocated_name

val name_of_allocated_name (n:allocated_name)
: GTot iname

let name_of_inv #p (i:inv p)
: GTot iname
= name_of_allocated_name (allocated_name_of_inv i)

let mem_inv (#p:_) (opens:inames) (i:inv p)
: GTot bool
= Set.mem (name_of_inv i) opens

let add_inv (#p:_) (opens:inames) (i:inv p)
: inames
= Set.union (Set.singleton (name_of_inv i)) opens

val new_invariant (p:slprop)
: act (inv p) UsesInvariants emp_inames p (fun _ -> emp)

let fresh_wrt (i:iname)
              (ctx:list allocated_name)
: prop
= forall i'. List.Tot.memP i' ctx ==> name_of_allocated_name i' <> i

val fresh_invariant (ctx:list allocated_name) (p:slprop)
: act (i:inv p { name_of_inv i `fresh_wrt` ctx }) UsesInvariants emp_inames p (fun _ -> emp)

val with_invariant
    (#a:Type)
    (#r:_)
    (#fp:slprop)
    (#fp':a -> slprop)
    (#f_opens:inames)
    (#p:slprop)
    (i:inv p{not (mem_inv f_opens i)})
    (f:unit -> act a r f_opens (p ** fp) (fun x -> p ** fp' x))
: act a UsesInvariants (add_inv f_opens i) fp fp'

val distinct_invariants_have_distinct_names
    (#p:slprop)
    (#q:slprop)
    (i:inv p)
    (j:inv q)
    (_:squash (p =!= q))
: act (squash (name_of_inv i =!= name_of_inv j))
    UsesInvariants
    emp_inames 
    emp
    (fun _ -> emp)

val invariant_name_identifies_invariant
      (p q:slprop)
      (i:inv p)
      (j:inv q { name_of_inv i == name_of_inv j } )
: act (squash (p == q /\ i == j)) UsesInvariants emp_inames emp (fun _ -> emp)

////////////////////////////////////////////////////////////////////////
// References
////////////////////////////////////////////////////////////////////////
val ref ([@@@unused] a:Type u#a) ([@@@unused] p:pcm a) : Type u#0

val ref_null (#a:Type u#a) (p:pcm a) : ref a p

val is_ref_null (#a:Type) (#p:FStar.PCM.pcm a) (r:ref a p)
: b:bool { b <==> r == ref_null p }

val pts_to (#a:Type u#1) (#p:pcm a) (r:ref a p) (v:a) : slprop

val pts_to_not_null (#a:Type) (#p:FStar.PCM.pcm a) (r:ref a p) (v:a)
: act (squash (not (is_ref_null r)))
    Ghost
    emp_inames 
    (pts_to r v)
    (fun _ -> pts_to r v)

val alloc
    (#a:Type u#1)
    (#pcm:pcm a)
    (x:a{pcm.refine x})
: act (ref a pcm)
      Reifiable
      emp_inames
      emp
      (fun r -> pts_to r x)

val read
    (#a:Type)
    (#p:pcm a)
    (r:ref a p)
    (x:erased a)
    (f:(v:a{compatible p x v}
        -> GTot (y:a{compatible p y v /\
                     FStar.PCM.frame_compatible p x v y})))
: act (v:a{compatible p x v /\ p.refine v})
      Reifiable
      emp_inames
      (pts_to r x)
      (fun v -> pts_to r (f v))

val write
    (#a:Type)
    (#p:pcm a)
    (r:ref a p)
    (x y:Ghost.erased a)
    (f:FStar.PCM.frame_preserving_upd p x y)
: act unit
    Reifiable
    emp_inames
    (pts_to r x)
    (fun _ -> pts_to r y)

val share
    (#a:Type)
    (#pcm:pcm a)
    (r:ref a pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a{composable pcm v0 v1})
: act unit
    Ghost
    emp_inames
    (pts_to r (v0 `op pcm` v1))
    (fun _ -> pts_to r v0 ** pts_to r v1)

val gather
    (#a:Type)
    (#pcm:pcm a)
    (r:ref a pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a)
: act (squash (composable pcm v0 v1))
    Ghost
    emp_inames
    (pts_to r v0 ** pts_to r v1)
    (fun _ -> pts_to r (op pcm v0 v1))

let property (a:Type)
  = a -> prop

val witnessed (#a:Type u#1)
              (#pcm:pcm a)
              (r:ref a pcm)
              (fact:property a)
  : Type0

let stable_property (#a:Type) (pcm:pcm a)
  = fact:property a {
       FStar.Preorder.stable fact (PP.preorder_of_pcm pcm)
    }

val witness
    (#a:Type)
    (#pcm:pcm a)
    (r:erased (ref a pcm))
    (fact:stable_property pcm)
    (v:Ghost.erased a)
    (pf:squash (forall z. compatible pcm v z ==> fact z))
: act (witnessed r fact) UsesInvariants emp_inames (pts_to r v) (fun _ -> pts_to r v)

val recall
    (#a:Type u#1)
    (#pcm:pcm a)
    (#fact:property a)
    (r:erased (ref a pcm))
    (v:Ghost.erased a)
    (w:witnessed r fact)
: act (v1:Ghost.erased a{compatible pcm v v1})
    UsesInvariants
    emp_inames
    (pts_to r v)
    (fun v1 -> pts_to r v ** pure (fact v1))

///////////////////////////////////////////////////////////////////
// pure
///////////////////////////////////////////////////////////////////
val pure_true ()
: slprop_equiv (pure True) emp

val intro_pure (p:prop) (pf:squash p)
: act unit Ghost emp_inames emp (fun _ -> pure p)

val elim_pure (p:prop)
: act (squash p) Ghost emp_inames (pure p) (fun _ -> emp)

///////////////////////////////////////////////////////////////////
// exists*
///////////////////////////////////////////////////////////////////
val intro_exists (#a:Type u#a) (p:a -> slprop) (x:erased a)
: act unit Ghost emp_inames (p x) (fun _ -> exists* x. p x)

val elim_exists (#a:Type u#a) (p:a -> slprop)
: act (erased a) Ghost emp_inames (exists* x. p x) (fun x -> p x)

///////////////////////////////////////////////////////////////////
// Other utils
///////////////////////////////////////////////////////////////////
val drop (p:slprop)
: act unit Ghost emp_inames p (fun _ -> emp)

////////////////////////////////////////////////////////////////////////
// Ghost References
////////////////////////////////////////////////////////////////////////
[@@erasable]
val ghost_ref (#[@@@unused] a:Type u#a) ([@@@unused] p:pcm a) : Type u#0
val ghost_pts_to (#a:Type u#1) (#p:pcm a) (r:ghost_ref p) (v:a) : slprop

val ghost_alloc
    (#a:Type u#1)
    (#pcm:pcm a)
    (x:erased a{pcm.refine x})
: act (ghost_ref pcm) Ghost emp_inames
    emp 
    (fun r -> ghost_pts_to r x)

val ghost_read
    (#a:Type)
    (#p:pcm a)
    (r:ghost_ref p)
    (x:erased a)
    (f:(v:a{compatible p x v}
        -> GTot (y:a{compatible p y v /\
                     FStar.PCM.frame_compatible p x v y})))
: act (erased (v:a{compatible p x v /\ p.refine v})) Ghost emp_inames
    (ghost_pts_to r x)
    (fun v -> ghost_pts_to r (f v))

val ghost_write
    (#a:Type)
    (#p:pcm a)
    (r:ghost_ref p)
    (x y:Ghost.erased a)
    (f:FStar.PCM.frame_preserving_upd p x y)
: act unit Ghost emp_inames 
    (ghost_pts_to r x)
    (fun _ -> ghost_pts_to r y)

val ghost_share
    (#a:Type)
    (#pcm:pcm a)
    (r:ghost_ref pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a{composable pcm v0 v1})
: act unit Ghost emp_inames
    (ghost_pts_to r (v0 `op pcm` v1))
    (fun _ -> ghost_pts_to r v0 ** ghost_pts_to r v1)

val ghost_gather
    (#a:Type)
    (#pcm:pcm a)
    (r:ghost_ref pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a)
: act (squash (composable pcm v0 v1)) Ghost emp_inames
    (ghost_pts_to r v0 ** ghost_pts_to r v1)
    (fun _ -> ghost_pts_to r (op pcm v0 v1))

let non_informative a = x:erased a -> y:a { reveal x == y}

val lift_erased 
    (#a:Type)
    (ni_a:non_informative a)
    (#opens:inames)
    (#pre:slprop)
    (#post:a -> slprop)
    (f:erased (act a Ghost opens pre post))
: act a Ghost opens pre post