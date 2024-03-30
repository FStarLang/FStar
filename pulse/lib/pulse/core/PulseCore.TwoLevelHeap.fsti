module PulseCore.TwoLevelHeap
open FStar.Ghost
open FStar.PCM
open PulseCore.Tags
module T = FStar.Tactics
module H2 = PulseCore.Heap2
(**** The base : partial heaps *)

(**
  Abstract type of heaps. Can conceptually be thought of as a map from addresses to
  contents of memory cells.
*)
val heap  : Type u#(a + 2)
val core_heap : Type u#(a + 2)
val concrete (h:heap u#a) : core_heap u#a
val ghost (h:heap u#a) : erased (core_heap u#a)
val upd_ghost_heap
      (h0:heap u#a)
      (h1:erased (heap u#a) { concrete h0 == concrete h1 })
: h2:heap u#a { h2 == reveal h1 }

(* An empty heap *)
val empty_heap : heap

(** A [core_ref] is a key into the [heap] or [null] *)
val core_ref : Type u#0

(** We index a [core_ref] by the type of its heap contents
    and a [pcm] governing it, for ease of type inference *)
let ref (a:Type u#a) (pcm:pcm a) : Type u#0 = core_ref

val core_ref_null : core_ref

(** [null] is a specific reference, that is not associated to any value
*)
let null (#a:Type u#a) (#pcm:pcm a) : ref a pcm = core_ref_null

(** Checking whether [r] is the null pointer is decidable through [is_null]
*)
val core_ref_is_null (r:core_ref) : b:bool { b <==> r == core_ref_null }

(** Checking whether [r] is the null pointer is decidable through [is_null]
*)
let is_null (#a:Type u#a) (#pcm:pcm a) (r:ref a pcm) : (b:bool{b <==> r == null}) = core_ref_is_null r

(** The predicate describing non-overlapping heaps *)
val disjoint (h0 h1:heap u#a) : prop

(** Disjointness is symmetric *)
val disjoint_sym (h0 h1:heap u#a)
  : Lemma (disjoint h0 h1 <==> disjoint h1 h0)
          [SMTPat (disjoint h0 h1)]

(** Disjoint heaps can be combined into a bigger heap*)
val join (h0:heap u#a) (h1:heap u#a{disjoint h0 h1}) : heap u#a

(** The join operation is commutative *)
val join_commutative (h0 h1:heap u#a)
  : Lemma
    (requires
      disjoint h0 h1)
    (ensures
      (disjoint h1 h0 /\
       join h0 h1 == join h1 h0))

(** Disjointness distributes over join *)
val disjoint_join (h0 h1 h2:heap u#a)
  : Lemma (disjoint h1 h2 /\
           disjoint h0 (join h1 h2) ==>
           disjoint h0 h1 /\
           disjoint h0 h2 /\
           disjoint (join h0 h1) h2 /\
           disjoint (join h0 h2) h1)

(** Join is associative *)
val join_associative (h0 h1 h2:heap u#a)
  : Lemma
    (requires
      disjoint h1 h2 /\
      disjoint h0 (join h1 h2))
    (ensures
      (disjoint h0 h1 /\
       disjoint (join h0 h1) h2 /\
       join h0 (join h1 h2) == join (join h0 h1) h2))

val join_empty (h:heap u#a)
  : Lemma (disjoint h empty_heap /\
           join h empty_heap == h)

(**** Separation logic over heaps *)

(**
  An affine heap proposition or affine heap predicate is a proposition whose validity does not
  change if the heap on which it is valid grows. In other terms, it is a proposition that is
  compatible with the disjoint/join operations for partial heaps. These affine heap predicates
  are the base of our separation logic.
*)
let heap_prop_is_affine (p:heap -> prop) : prop =
  forall (h0 h1: heap). p h0 /\ disjoint h0 h1 ==> p (join h0 h1)

(**
  An affine heap proposition
  *)
let a_heap_prop = p:(heap -> prop) { heap_prop_is_affine p }

(**
  [slprop] is an abstract "separation logic proposition"

  The [erasable] attribute says that it is computationally irrelevant
  and will be extracted to [()]
*)
[@@erasable]
val slprop : Type u#(a + 2)

(**
  [slprop]s can be "interpreted" over any heap, yielding a [prop]
*)
val interp (p:slprop u#a) (m:heap u#a) : prop

(**
  Promoting an affine heap proposition to an slprop
  *)
val as_slprop (f:a_heap_prop) : p:slprop{forall h.interp p h <==> f h}

(**
  An [hprop] is heap predicate indexed by a footprint [fp:slprop].
  Its validity depends only on the fragment of the heap that satisfies [fp].
  Note, it is unrelated to affinity, since the forward implication only applies
  to heaps [h0] that validate [fp]
*)
let hprop (fp:slprop) =
  q:(heap -> prop){
    forall (h0:heap{interp fp h0}) (h1:heap{disjoint h0 h1}).
      q h0 <==> q (join h0 h1)
  }


(** A common abbreviation: [hheap p] is a heap on which [p] is valid *)
let hheap (p:slprop) = m:heap {interp p m}

(**
  The interpretation of a separation logic proposition [hp] is itself an [hprop] of footprint
  [hp]
*)
val interp_depends_only_on (hp:slprop)
    : Lemma
      (forall (h0:hheap hp) (h1:heap{disjoint h0 h1}).
        interp hp h0 <==> interp hp (join h0 h1))


(**
  Equivalence relation on [slprop]s is just
  equivalence of their interpretations
*)
let equiv (p1 p2:slprop) =
  forall m. interp p1 m <==> interp p2 m

(**
  An extensional equivalence principle for slprop
 *)
val slprop_extensionality (p q:slprop)
  : Lemma
    (requires p `equiv` q)
    (ensures p == q)

[@@erasable]
val small_slprop : Type u#(a + 1)
val down (s:slprop u#a) : small_slprop u#a
val up (s:small_slprop u#a) : slprop u#a
let is_small (s:slprop u#a) = s == up (down s)
let vprop = s:slprop { is_small s }

(** [emp] is the empty [slprop], valid on all heaps. It acts as the unit element *)
val emp : vprop
val pure (p:prop) : vprop
val star  (p1 p2:slprop u#a) : slprop u#a
val h_exists (#[@@@strictly_positive] a:Type u#b)
             ([@@@strictly_positive]  f: (a -> slprop u#a))
  : slprop u#a


(** [p ~~ p * emp] *)
val emp_unit (p:slprop)
  : Lemma (p `equiv` (p `star` emp))

(** [emp] is trivial *)
val intro_emp (h:heap)
  : Lemma (interp emp h)


(** Equivalence of pure propositions is the equivalence of the underlying propositions *)
val pure_equiv (p q:prop)
  : Lemma ((p <==> q) ==> (pure p `equiv` pure q))

(** And the interpretation of pure propositions is their underlying propositions *)
val pure_interp (q:prop) (h:heap)
   : Lemma (interp (pure q) h <==> q)

(** A helper lemma for interpreting a pure proposition with another [slprop] *)
val pure_star_interp (p:slprop) (q:prop) (h:heap)
   : Lemma (interp (p `star` pure q) h <==>
            interp (p `star` emp) h /\ q)

(** If [p * q] is valid on [h], then [p] and [q] are valid on [h] *)
val affine_star (p q:slprop) (h:heap)
  : Lemma ((interp (p `star` q) h ==> interp p h /\ interp q h))


(** The separating conjunction [star] arises from the disjointness of partial heaps *)
val intro_star (p q:slprop) (hp:hheap p) (hq:hheap q)
    : Lemma
      (requires disjoint hp hq)
      (ensures interp (p `star` q) (join hp hq))

val elim_star (p q:slprop) (h:hheap (p `star` q))
    : Lemma
      (requires interp (p `star` q) h)
    (ensures exists hl hr.
      disjoint hl hr /\
      h == join hl hr /\
      interp p hl /\
      interp q hr)

(** [star] is commutative *)
val star_commutative (p1 p2:slprop)
    : Lemma ((p1 `star` p2) `equiv` (p2 `star` p1))

(** [star] is associative *)
val star_associative (p1 p2 p3:slprop)
    : Lemma (
      (p1 `star` (p2 `star` p3))
      `equiv`
      ((p1 `star` p2) `star` p3)
    )

(** If [p1 ~ p3] and [p2 ~ p4], then [p1 * p2 ~ p3 * p4] *)
val star_congruence (p1 p2 p3 p4:slprop)
  : Lemma (requires p1 `equiv` p3 /\ p2 `equiv` p4)
          (ensures (p1 `star` p2) `equiv` (p3 `star` p4))


val vprop_star (p1 p2:vprop)
  : Lemma (is_small (p1 `star` p2))


(** Introduction rule for equivalence of [h_exists] propositions *)
val h_exists_cong (#a:Type) (p q : a -> slprop)
    : Lemma
      (requires (forall x. p x `equiv` q x))
      (ensures (h_exists p `equiv` h_exists q))

(** Introducing [h_exists] by presenting a witness *)
val intro_h_exists (#a:_) (x:a) (p:a -> slprop) (h:heap)
  : Lemma (interp (p x) h ==> interp (h_exists p) h)

(** Eliminate an existential by simply getting a proposition. *)
val elim_h_exists (#a:_) (p:a -> slprop) (h:heap)
  : Lemma (interp (h_exists p) h ==> (exists x. interp (p x) h))

val vprop_exists_alt (a:Type) (p:a -> slprop)
  : Lemma
    (requires forall x. is_small (p x))
    (ensures is_small (h_exists p))

val vprop_exists (a:Type) (p:a -> vprop)
  : Lemma (is_small (h_exists p))


(** We can define a [stronger] relation on [slprops], defined by interpretation implication *)
let stronger (p q:slprop) =
  forall h. interp p h ==> interp q h

(** [stronger] is stable when adding another starred [slprop] *)
val stronger_star (p q r:slprop)
  : Lemma (stronger q r ==> stronger (p `star` q) (p `star` r))

(** If [q > r] and [p * q] is valid, then [p * r] is valid *)
val weaken (p q r:slprop) (h:heap)
  : Lemma (q `stronger` r /\ interp (p `star` q) h ==> interp (p `star` r) h)

(**** Actions *)

(** An abstract predicate classifying a "full" heap, i.e., the entire
    heap of the executing program, not just a fragment of it *)
val full_heap_pred : heap -> prop

let full_heap = h:heap { full_heap_pred h }

let full_hheap fp = h:hheap fp { full_heap_pred h }

(**
  This modules exposes a preorder that is respected for every well-formed update of the heap.
  The preorder represents the fact that once a reference is allocated, its type and PCM cannot
  change and the trace of values contained in the PCM respects the preorder induced by the
  PCM (see Steel.Preorder).
*)
val heap_evolves : FStar.Preorder.preorder full_heap

(**
  This predicate allows us to maintain an allocation counter, as all references above [a]
  in [h] are free.
*)
val free_above_addr (t:tag) (h:heap) (a:nat) : prop

(** [free_above_addr] is abstract but can be weakened consistently with its intended behavior *)
val weaken_free_above (t:tag) (h:heap) (a b:nat)
  : Lemma (free_above_addr t h a /\ a <= b ==> free_above_addr t h b)

(**
  The base type for an action is indexed by two separation logic propositions, representing
  the heap specification of the action before and after.
*)
let trivial_pre (h:heap) : prop = True

let pre_action (#[T.exact (`trivial_pre)]pre:heap u#a -> prop)
               (#[T.exact (`trivial_pre)]post:heap u#a -> prop)
               (fp:slprop u#a)
               (a:Type u#b)
               (fp':a -> slprop u#a)
  = h0:full_hheap fp { pre h0 } -> res:(x:a & full_hheap (fp' x)) { post (dsnd res) }

(**
  This is how the heaps before and after the action relate:
  - evolving the heap according to the heap preorder;
  - not allocating any new references;
  - preserving the validity of any heap proposition affecting any frame
*)
let no_allocs : option tag = None
let does_not_allocate (t:tag) (h0 h1:heap) =
    forall ctr. free_above_addr t h0 ctr ==> free_above_addr t h1 ctr
let maybe_allocates (t:option tag) (h0 h1:heap) =
  match t with
  | None ->
    does_not_allocate CONCRETE h0 h1 /\
    does_not_allocate GHOST h0 h1
  | Some CONCRETE ->
    does_not_allocate GHOST h0 h1
  | Some GHOST ->
    does_not_allocate CONCRETE h0 h1
  
unfold
let action_related_heaps 
      (#[T.exact (`MUTABLE)] m:mutability)
      (#[T.exact (`no_allocs)] allocates:option tag)
      (h0 h1:full_heap) =
  heap_evolves h0 h1 /\
  maybe_allocates allocates h0 h1 /\
  (match m with
  | ONLY_GHOST ->
    concrete h0 == concrete h1
  | IMMUTABLE ->
    h0 == h1
  | _ -> True)


(**
  We only want to consider heap updates that are "frame-preserving", meaning that they only
  modify the portion of the heap that they're allowed to, without messing with any other
  partial view of the heap that is compatible with the one you own. This includes :
  - preserving correct interpretation in presence of a frame;
  - heaps are related as defined above
*)
let is_frame_preserving
  (#a: Type)
  (#pre #post:_)
  (#fp: slprop)
  (#fp': a -> slprop)
  (immut:mutability)
  (allocates:option tag)
  (f:pre_action #pre #post fp a fp')
  =
  forall (frame: slprop) (h0:full_hheap (fp `star` frame) { pre h0 }).
     (affine_star fp frame h0;
      let (| x, h1 |) = f h0 in
      interp (fp' x `star` frame) h1 /\
      action_related_heaps #immut #allocates h0 h1)

(** Every action is frame-preserving *)
let action (#[T.exact (`MUTABLE)] mut:mutability)
           (#[T.exact (`no_allocs)] allocates:option tag)
           (#[T.exact (`trivial_pre)]pre:heap -> prop)
           (#[T.exact (`trivial_pre)]post:heap -> prop)
           (fp:slprop) (a:Type) (fp':a -> slprop) =
  f:pre_action #pre #post fp a fp'{ is_frame_preserving mut allocates f }

(**
  We define a second, but equivalent, type for actions that
  instead of quantifying over the frame, are explicitly passed a frame
  from outside

  This notion of action is useful for defining actions like witness_h_exists, see comments at the declaration of witness_h_exists
*)
let action_with_frame
  (fp:slprop)
  (a:Type)
  (fp':a -> slprop)
  = frame:slprop ->
    h0:full_hheap (fp `star` frame) ->
    Pure (x:a & full_hheap (fp' x `star` frame))
      (requires True)
      (ensures fun (| x, h1 |) -> action_related_heaps #IMMUTABLE #no_allocs h0 h1)

(**
  Two heaps [h0] and [h1] are frame-related if you can get from [h0] to [h1] with a
  frame-preserving update.
*)
let frame_related_heaps (h0 h1:full_heap) (fp0 fp1 frame:slprop)
                        (mut:mutability) (allocates:option tag) =
  interp (fp0 `star` frame) h0 ==>
  interp (fp1 `star` frame) h1 /\
  action_related_heaps #mut #allocates h0 h1


(**
  A frame-preserving action applied on [h0] produces an [h1] such that [h0] and [h1] are
  frame-related
*)
let action_framing
  (#a: Type)
  (#mut #allocates:_)
  (#fp: slprop)
  (#fp': a -> slprop)
  ($f:action #mut #allocates fp a fp')
  (frame:slprop) (h0:full_hheap (fp `star` frame))
    : Lemma (
      affine_star fp frame h0;
      let (| x, h1 |) = f h0 in
      frame_related_heaps h0 h1 fp (fp' x) frame mut allocates
    )
  =
  affine_star fp frame h0;
  emp_unit fp

(*********** Some generic actions *)


val frame (#a:Type)
          #immut #allocates #hpre #hpost
          (#pre:slprop)
          (#post:a -> slprop)
          (frame:slprop)
          ($f:action #immut #allocates #hpre #hpost pre a post)
  : action #immut #allocates #hpre #hpost (pre `star` frame) a (fun x -> post x `star` frame)

val change_slprop (p q:slprop)
                  (proof: (h:heap -> Lemma (requires interp p h) (ensures interp q h)))
  : action #IMMUTABLE #no_allocs p unit (fun _ -> q)

(**
  witness_h_exists is defined with action_with_frame as it allows us to define it with any p

  With the quantified frame actions, it creates an issue, since we have to prove that the witness is ok for all frames
    whereas with an explicit frame, we can pick the witness for that particular frame
*)
val elim_exists (#a:_) (p:a -> slprop)
  : action_with_frame (h_exists p) (erased a) (fun x -> p x)

val intro_exists (#a:_) (p:a -> slprop) (x:erased a)
  : action_with_frame (p x) unit (fun _ -> h_exists p)
  
val lift_exists (#a:_) (p:a -> slprop)
  : action #IMMUTABLE #no_allocs (h_exists p) unit
           (fun _a -> h_exists #(FStar.Universe.raise_t a) (FStar.Universe.lift_dom p))

val elim_pure (p:prop)
  : action #IMMUTABLE #no_allocs (pure p) (u:unit{p}) (fun _ -> emp)

val intro_pure (p:prop) (_:squash p)
  : action #IMMUTABLE #no_allocs emp unit (fun _ -> pure p)

val drop (p:slprop)
  : action #IMMUTABLE #no_allocs p unit (fun _ -> emp)


(*** Actions on the small heap *)

(* Small concrete references *)

(***** [pts_to]: Ownership of a concrete reference on the small heap *)
val pts_to (#a:Type u#a) (#pcm:_) (r:ref a pcm) (v:a) : vprop u#a

(**
  The action variant of [sel], returning the "true" value inside the heap. This "true" value
  can be different of the [pts_to] value you assumed at the beginning, because of the PCM structure
*)
val sel_action
  (#a:Type u#a)
  (#pcm:pcm a)
  (r:ref a pcm)
  (v0:erased a)
    : action #IMMUTABLE #no_allocs
       (pts_to r v0) (v:a{compatible pcm v0 v}) (fun _ -> pts_to r v0)

(**
  A version of select that incorporates a ghost update of local
  knowledge of a ref cell based on the value that was read
 *)
val select_refine (#a:_) (#p:_)
                  (r:ref a p)
                  (x:erased a)
                  (f:(v:a{compatible p x v}
                      -> GTot (y:a{compatible p y v /\
                                  FStar.PCM.frame_compatible p x v y})))
   : action #IMMUTABLE #no_allocs (pts_to r x)
            (v:a{compatible p x v /\ p.refine v})
            (fun v -> pts_to r (f v))


(** Updating a ref cell for a user-defined PCM *)
val upd_gen_action (#a:Type) (#p:pcm a) (r:ref a p) (x y:Ghost.erased a)
                   (f:FStar.PCM.frame_preserving_upd p x y)
  : action #MUTABLE #no_allocs (pts_to r x)
           unit
           (fun _ -> pts_to r y)

(**
  The update action needs you to prove that the mutation from [v0] to [v1] is frame-preserving
  with respect to the individual PCM governing the reference [r]. See [FStar.PCM.frame_preserving]
*)
val upd_action
  (#a:Type u#a)
  (#pcm:pcm a)
  (r:ref a pcm)
  (v0:FStar.Ghost.erased a)
  (v1:a {FStar.PCM.frame_preserving pcm v0 v1 /\ pcm.refine v1})
  : action #MUTABLE #no_allocs (pts_to r v0) unit (fun _ -> pts_to r v1)

(** Deallocating a reference, by actually replacing its value by the unit of the PCM *)
val free_action
  (#a:Type u#a)
  (#pcm:pcm a)
  (r:ref a pcm)
  (v0:FStar.Ghost.erased a {exclusive pcm v0 /\ pcm.refine pcm.FStar.PCM.p.one})
  : action #MUTABLE #no_allocs (pts_to r v0) unit (fun _ -> pts_to r pcm.FStar.PCM.p.one)


(** Splitting a permission on a composite resource into two separate permissions *)
val split_action
  (#a:Type u#a)
  (#pcm:pcm a)
  (r:ref a pcm)
  (v0:FStar.Ghost.erased a)
  (v1:FStar.Ghost.erased a{composable pcm v0 v1})
  : action #IMMUTABLE #no_allocs (pts_to r (v0 `op pcm` v1)) unit (fun _ -> pts_to r v0 `star` pts_to r v1)

(** Combining separate permissions into a single composite permission *)
val gather_action
  (#a:Type u#a)
  (#pcm:pcm a)
  (r:ref a pcm)
  (v0:FStar.Ghost.erased a)
  (v1:FStar.Ghost.erased a)
  : action #IMMUTABLE #no_allocs
    (pts_to r v0 `star` pts_to r v1) (_:unit{composable pcm v0 v1}) (fun _ -> pts_to r (op pcm v0 v1))

val pts_to_not_null_action 
      (#a:Type u#a)
      (#pcm:pcm a)
      (r:erased (ref a pcm))
      (v:Ghost.erased a)
: action #IMMUTABLE #no_allocs
    (pts_to r v)
    (squash (not (is_null r)))
    (fun _ -> pts_to r v)

(** Allocating is a pseudo action here, the context needs to provide a fresh address *)
val extend
  (#a:Type u#a)
  (#pcm:pcm a)
  (x:a{pcm.refine x})
  (addr:nat)
  : action
      #MUTABLE #(Some CONCRETE)
      #(fun h -> h `free_above_addr CONCRETE` addr)
      #(fun h -> h `free_above_addr CONCRETE` (addr + 1))      
      emp 
      (ref a pcm)
      (fun r -> pts_to r x)

(* Small ghost references *)
[@@erasable]
val ghost_ref (#[@@@unused] a:Type u#a) ([@@@unused]p:pcm a) : Type0

(*** ghost_pts_to: Ownership of a ghost reference on the small heap *)
val ghost_pts_to (#a:Type u#a) (#p:pcm a) (r:ghost_ref p) (v:a) : vprop u#a

val ghost_extend
    (#a:Type u#a)
    (#pcm:pcm a)
    (x:erased a{pcm.refine x})
    (addr:erased nat)
: action #ONLY_GHOST #(Some GHOST)
      #(fun h -> h `free_above_addr GHOST` addr)
      #(fun h -> h `free_above_addr GHOST` (addr + 1))      
      emp 
      (ghost_ref pcm)
      (fun r -> ghost_pts_to r x)

val ghost_read
    (#a:Type)
    (#p:pcm a)
    (r:ghost_ref p)
    (x:erased a)
    (f:(v:a{compatible p x v}
        -> GTot (y:a{compatible p y v /\
                     FStar.PCM.frame_compatible p x v y})))
: action #IMMUTABLE
    (ghost_pts_to r x)
    (erased (v:a{compatible p x v /\ p.refine v}))
    (fun v -> ghost_pts_to r (f v))

val ghost_write
    (#a:Type)
    (#p:pcm a)
    (r:ghost_ref p)
    (x y:Ghost.erased a)
    (f:FStar.PCM.frame_preserving_upd p x y)
: action #ONLY_GHOST 
    (ghost_pts_to r x)
    unit
    (fun _ -> ghost_pts_to r y)

val ghost_share
    (#a:Type)
    (#pcm:pcm a)
    (r:ghost_ref pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a{composable pcm v0 v1})
: action #IMMUTABLE
    (ghost_pts_to r (v0 `op pcm` v1))
    unit
    (fun _ -> ghost_pts_to r v0 `star` ghost_pts_to r v1)

val ghost_gather
    (#a:Type)
    (#pcm:pcm a)
    (r:ghost_ref pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a)
: action #IMMUTABLE 
    (ghost_pts_to r v0 `star` ghost_pts_to r v1)
    (squash (composable pcm v0 v1))
    (fun _ -> ghost_pts_to r (op pcm v0 v1))

/////////////////////////////////////////////

(* Big concrete references *)

(***** [big_pts_to]: Ownership of a concrete reference on the small heap *)
val big_pts_to (#a:Type u#(ua + 1)) (#pcm:_) (r:ref a pcm) (v:a) : slprop u#ua

(**
  The action variant of [sel], returning the "true" value inside the heap. This "true" value
  can be different of the [big_pts_to] value you assumed at the beginning, because of the PCM structure
*)
val big_sel_action
  (#a:Type u#(ua + 1))
  (#pcm:pcm a)
  (r:ref a pcm)
  (v0:erased a)
    : action #IMMUTABLE #no_allocs
       (big_pts_to r v0) (v:a{compatible pcm v0 v}) (fun _ -> big_pts_to r v0)

(**
  A version of select that incorporates a ghost update of local
  knowledge of a ref cell based on the value that was read
 *)
val big_select_refine
  (#a:_) (#p:_)
  (r:ref a p)
  (x:erased a)
  (f:(v:a{compatible p x v}
      -> GTot (y:a{compatible p y v /\
                  FStar.PCM.frame_compatible p x v y})))
   : action #IMMUTABLE #no_allocs (big_pts_to r x)
            (v:a{compatible p x v /\ p.refine v})
            (fun v -> big_pts_to r (f v))


(** Updating a ref cell for a user-defined PCM *)
val big_upd_gen_action
  (#a:Type) (#p:pcm a) (r:ref a p) (x y:Ghost.erased a)
  (f:FStar.PCM.frame_preserving_upd p x y)
: action #MUTABLE #no_allocs (big_pts_to r x)
        unit
        (fun _ -> big_pts_to r y)

(**
  The update action needs you to prove that the mutation from [v0] to [v1] is frame-preserving
  with respect to the individual PCM governing the reference [r]. See [FStar.PCM.frame_preserving]
*)
val big_upd_action
  (#a:Type)
  (#pcm:pcm a)
  (r:ref a pcm)
  (v0:FStar.Ghost.erased a)
  (v1:a {FStar.PCM.frame_preserving pcm v0 v1 /\ pcm.refine v1})
: action #MUTABLE #no_allocs (big_pts_to r v0) unit (fun _ -> big_pts_to r v1)

(** Deallocating a reference, by actually replacing its value by the unit of the PCM *)
val big_free_action
  (#a:Type)
  (#pcm:pcm a)
  (r:ref a pcm)
  (v0:FStar.Ghost.erased a {exclusive pcm v0 /\ pcm.refine pcm.FStar.PCM.p.one})
: action #MUTABLE #no_allocs (big_pts_to r v0) unit (fun _ -> big_pts_to r pcm.FStar.PCM.p.one)


(** Splitting a permission on a composite resource into two separate permissions *)
val big_split_action
  (#a:Type)
  (#pcm:pcm a)
  (r:ref a pcm)
  (v0:FStar.Ghost.erased a)
  (v1:FStar.Ghost.erased a{composable pcm v0 v1})
: action #IMMUTABLE #no_allocs
    (big_pts_to r (v0 `op pcm` v1))
    unit
    (fun _ -> big_pts_to r v0 `star` big_pts_to r v1)

(** Combining separate permissions into a single composite permission *)
val big_gather_action
  (#a:Type)
  (#pcm:pcm a)
  (r:ref a pcm)
  (v0:FStar.Ghost.erased a)
  (v1:FStar.Ghost.erased a)
: action #IMMUTABLE #no_allocs
    (big_pts_to r v0 `star` big_pts_to r v1)
    (_:unit{composable pcm v0 v1})
    (fun _ -> big_pts_to r (op pcm v0 v1))

val big_pts_to_not_null_action 
      (#a:Type)
      (#pcm:pcm a)
      (r:erased (ref a pcm))
      (v:Ghost.erased a)
: action #IMMUTABLE #no_allocs
    (big_pts_to r v)
    (squash (not (is_null r)))
    (fun _ -> big_pts_to r v)

(** Allocating is a pseudo action here, the context needs to provide a fresh address *)
val big_extend
  (#a:Type)
  (#pcm:pcm a)
  (x:a{pcm.refine x})
  (addr:nat)
: action
    #MUTABLE #(Some CONCRETE)
    #(fun h -> h `free_above_addr CONCRETE` addr)
    #(fun h -> h `free_above_addr CONCRETE` (addr + 1))      
    emp 
    (ref a pcm)
    (fun r -> big_pts_to r x)

(** Big ghost references *)
val big_ghost_pts_to (#a:Type u#(ua + 1)) (#p:pcm a) (r:ghost_ref p) (v:a) : slprop u#ua

val big_ghost_extend
    (#a:Type)
    (#pcm:pcm a)
    (x:erased a{pcm.refine x})
    (addr:erased nat)
: action #ONLY_GHOST #(Some GHOST)
      #(fun h -> h `free_above_addr GHOST` addr)
      #(fun h -> h `free_above_addr GHOST` (addr + 1))      
      emp 
      (ghost_ref pcm)
      (fun r -> big_ghost_pts_to r x)

val big_ghost_read
    (#a:Type)
    (#p:pcm a)
    (r:ghost_ref p)
    (x:erased a)
    (f:(v:a{compatible p x v}
        -> GTot (y:a{compatible p y v /\
                     FStar.PCM.frame_compatible p x v y})))
: action #IMMUTABLE
    (big_ghost_pts_to r x)
    (erased (v:a{compatible p x v /\ p.refine v}))
    (fun v -> big_ghost_pts_to r (f v))

val big_ghost_write
    (#a:Type)
    (#p:pcm a)
    (r:ghost_ref p)
    (x y:Ghost.erased a)
    (f:FStar.PCM.frame_preserving_upd p x y)
: action #ONLY_GHOST 
    (big_ghost_pts_to r x)
    unit
    (fun _ -> big_ghost_pts_to r y)

val big_ghost_share
    (#a:Type)
    (#pcm:pcm a)
    (r:ghost_ref pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a{composable pcm v0 v1})
: action #IMMUTABLE
    (big_ghost_pts_to r (v0 `op pcm` v1))
    unit
    (fun _ -> big_ghost_pts_to r v0 `star` big_ghost_pts_to r v1)

val big_ghost_gather
    (#a:Type)
    (#pcm:pcm a)
    (r:ghost_ref pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a)
: action #IMMUTABLE 
    (big_ghost_pts_to r v0 `star` big_ghost_pts_to r v1)
    (squash (composable pcm v0 v1))
    (fun _ -> big_ghost_pts_to r (op pcm v0 v1))