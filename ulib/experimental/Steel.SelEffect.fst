module Steel.SelEffect

module Sem = Steel.Semantics.Hoare.MST
module Mem = Steel.Memory
open Steel.Memory
open Steel.Semantics.Instantiate
open Steel.Effect.Common
module FExt = FStar.FunctionalExtensionality

(* Normalization helpers *)

irreducible let __steel_reduce__ : unit = ()

unfold
let normal (#a:Type) (x:a) =
  norm [
    delta_attr [`%__steel_reduce__];
    iota;zeta;primops]
  x

(* Definition of a selector for a given slprop *)

let selector' (a:Type0) (hp:slprop) = hmem hp -> GTot a

let sel_depends_only_on (#a:Type) (#hp:slprop) (sel:selector' a hp) =
  forall (m0:hmem hp) (m1:mem{disjoint m0 m1}).
    (interp_depends_only_on hp; (
    sel m0 == sel (join m0 m1)))

let selector (a:Type) (hp:slprop) : Type =
  sel:selector' a hp{sel_depends_only_on sel}

/// The basis of our selector framework: Separation logic assertions enhanced with selectors
/// Note that selectors are "optional", it is always possible to use a non-informative selector,
/// such as fun _ -> () and to rely on the standard separation logic reasoning
noeq
type vprop' =
  { hp: slprop u#1;
    t:Type0;
    sel: selector t hp}

noeq
type vprop =
  | VUnit : vprop' -> vprop
  | VStar: vprop -> vprop -> vprop

[@__steel_reduce__]
let star = VStar

[@__steel_reduce__]
let rec hp_of (p:vprop) = match p with
  | VUnit p -> p.hp
  | VStar p1 p2 -> hp_of p1 `Mem.star` hp_of p2

[@__steel_reduce__]
let rec t_of (p:vprop) = match p with
  | VUnit p -> p.t
  | VStar p1 p2 -> t_of p1 * t_of p2

[@__steel_reduce__]
let rec sel_of (p:vprop) : selector (t_of p) (hp_of p) = match p with
  | VUnit p -> fun h -> p.sel h
  | VStar p1 p2 ->
     let sel1 = sel_of p1 in
     let sel2 = sel_of p2 in
     fun h -> (sel1 h, sel2 h)

let hmem (p:vprop) = hmem (hp_of p)

type pre_t = vprop
type post_t (a:Type) = a -> vprop

let can_be_split (p q:vprop) : prop = can_be_split (hp_of p) (hp_of q) /\ True
let can_be_split_forall (#a:Type) (p q:post_t a) : prop = forall x. can_be_split (p x) (q x)

(* Some properties about can_be_split that need to be exposed
   or derived from Steel.Effect.Common *)

assume
val can_be_split_star_l (p q:vprop)
: Lemma
  (ensures (p `star` q) `can_be_split` p)
  [SMTPat ((p `star` q) `can_be_split` p)]

assume
val can_be_split_star_r (p q:vprop)
: Lemma
  (ensures (p `star` q) `can_be_split` q)
  [SMTPat ((p `star` q) `can_be_split` q)]


assume
val can_be_split_trans (p q r:vprop)
: Lemma
  (requires p `can_be_split` q /\ q `can_be_split` r)
  (ensures p `can_be_split` r)

assume
val can_be_split_refl (p:vprop)
: Lemma (p `can_be_split` p)
  [SMTPat (p `can_be_split` p)]

assume
val can_be_split_forall_refl (#a:Type) (p:post_t a)
: Lemma (p `can_be_split_forall` p)
  [SMTPat (p `can_be_split_forall` p)]

let rmem (pre:pre_t) = FExt.restricted_g_t (r0:vprop{can_be_split pre r0}) (fun r0 -> normal (t_of r0))

unfold
let unrestricted_mk_rmem (r:vprop) (h:hmem r) = fun (r0:vprop{r `can_be_split` r0}) -> normal (sel_of r0 h)

val mk_rmem (r:vprop) (h:hmem r) : Tot (rmem r)

let mk_rmem r h =
   FExt.on_dom_g
     (r0:vprop{r `can_be_split` r0})
     (unrestricted_mk_rmem r h)

let reveal_mk_rmem (r:vprop) (h:hmem r) (r0:vprop{r `can_be_split` r0})
  : Lemma ((mk_rmem r h) r0 == sel_of r0 h)
  = FExt.feq_on_domain_g (unrestricted_mk_rmem r h)

type req_t (pre:pre_t) = rmem pre -> prop
type ens_t (pre:pre_t) (a:Type) (post:post_t a) =
  rmem pre -> (x:a) -> rmem (post x) -> prop

let rmem_depends_only_on' (pre:pre_t) (m0:hmem pre) (m1:mem{disjoint m0 m1})
  : Lemma (mk_rmem pre m0 == mk_rmem pre (join m0 m1))
  = Classical.forall_intro (reveal_mk_rmem pre m0);
    Classical.forall_intro (reveal_mk_rmem pre (join m0 m1));
    FExt.extensionality_g
      (r0:vprop{can_be_split pre r0})
      (fun r0 -> normal (t_of r0))
      (mk_rmem pre m0)
      (mk_rmem pre (join m0 m1))

let rmem_depends_only_on (pre:pre_t)
  : Lemma (forall (m0:hmem pre) (m1:mem{disjoint m0 m1}).
    mk_rmem pre m0 == mk_rmem pre (join m0 m1))
  = Classical.forall_intro_2 (rmem_depends_only_on' pre)

let rmem_depends_only_on_post' (#a:Type) (post:post_t a)
    (x:a) (m0:hmem (post x)) (m1:mem{disjoint m0 m1})
  : Lemma (mk_rmem (post x) m0 == mk_rmem (post x) (join m0 m1))
  = rmem_depends_only_on' (post x) m0 m1

let rmem_depends_only_on_post (#a:Type) (post:post_t a)
  : Lemma (forall (x:a) (m0:hmem (post x)) (m1:mem{disjoint m0 m1}).
    mk_rmem (post x) m0 == mk_rmem (post x) (join m0 m1))
  = Classical.forall_intro_3 (rmem_depends_only_on_post' post)

[@__steel_reduce__]
let req_to_act_req (#pre:pre_t) (req:req_t pre) : Sem.l_pre #state (hp_of pre) =
  rmem_depends_only_on pre;
  fun m0 -> interp (hp_of pre) m0 /\ req (mk_rmem pre m0)

unfold
let to_post (#a:Type) (post:post_t a) = fun x -> (hp_of (post x))

[@__steel_reduce__]
let ens_to_act_ens (#pre:pre_t) (#a:Type) (#post:post_t a) (ens:ens_t pre a post)
: Sem.l_post #state #a (hp_of pre) (to_post post)
= rmem_depends_only_on pre;
  rmem_depends_only_on_post post;
  fun m0 x m1 ->
    interp (hp_of pre) m0 /\ interp (hp_of (post x)) m1 /\ ens (mk_rmem pre m0) x (mk_rmem (post x) m1)

[@__steel_reduce__]
let unrestricted_focus_rmem (#r:vprop) (h:rmem r) (r0:vprop{r `can_be_split` r0})
  = fun (r':vprop{can_be_split r0 r'}) -> can_be_split_trans r r0 r'; h r'

val focus_rmem (#r: vprop) (h: rmem r) (r0: vprop{r `can_be_split` r0})
  : Tot (rmem r0)

[@__steel_reduce__]
let focus_rmem #r h r0 =
  FExt.on_dom_g
   (r':vprop{can_be_split r0 r'})
   (unrestricted_focus_rmem h r0)

let reveal_focus_rmem (#r:vprop) (h:rmem r) (r0:vprop{r `can_be_split` r0}) (r':vprop{r0 `can_be_split` r'})
  : Lemma (
    r `can_be_split` r' /\
    focus_rmem h r0 r' == h r')
  = can_be_split_trans r r0 r';
    FExt.feq_on_domain_g (unrestricted_focus_rmem h r0)

let focus_is_restrict_mk_rmem (fp0 fp1:vprop) (m:hmem fp0)
  : Lemma
    (requires fp0 `can_be_split` fp1)
    (ensures focus_rmem (mk_rmem fp0 m) fp1 == mk_rmem fp1 m)
  = let f0:rmem fp0 = mk_rmem fp0 m in
    let f1:rmem fp1 = mk_rmem fp1 m in
    let f2:rmem fp1 = focus_rmem f0 fp1 in

    let aux (r:vprop{can_be_split fp1 r}) : Lemma (f1 r == f2 r)
      = can_be_split_trans fp0 fp1 r;

        reveal_mk_rmem fp0 m r;
        reveal_mk_rmem fp1 m r;
        reveal_focus_rmem f0 fp1 r
    in Classical.forall_intro aux;

    FExt.extensionality_g
      (r0:vprop{can_be_split fp1 r0})
      (fun r0 -> normal (t_of r0))
      (mk_rmem fp1 m)
      (focus_rmem (mk_rmem fp0 m) fp1)

val can_be_split_3_interp (p1 p2 q r:slprop u#1) (m:mem)
: Lemma
  (requires p1 `sl_implies` p2)
  (ensures interp (p1 `Mem.star` q `Mem.star` r) m ==>  interp (p2 `Mem.star` q `Mem.star` r) m)

let can_be_split_3_interp p1 p2 q r m =
  star_associative p1 q r;
  star_associative p2 q r

val repr (a:Type) (pre:pre_t) (post:post_t a) (req:req_t pre) (ens:ens_t pre a post) : Type u#2

let repr (a:Type) (pre:pre_t) (post:post_t a) (req:req_t pre) (ens:ens_t pre a post) =
  Sem.action_t #state #a (hp_of pre) (to_post post)
    ((req_to_act_req req))
    ((ens_to_act_ens ens))

unfold
let return_req (p:vprop) : req_t p = fun _ -> True

unfold
let return_ens (#a:Type) (x:a) (p:a -> vprop) : ens_t (p x) a p = fun _ r _ -> r == x

val return (a:Type u#a) (x:a) (p:a -> vprop)
  : repr a (p x) p (return_req (p x)) (return_ens x p)

let return a x p = fun _ -> x

[@__steel_reduce__]
unfold
let bind_req (#a:Type) (#pre_f:vprop) (#post_f:a -> vprop)
             (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
             (req_g:(x:a -> req_t (post_f x)))
  : req_t pre_f
  = fun h -> req_f h /\ (forall (x:a) h1. ens_f h x h1 ==> req_g x h1)

[@__steel_reduce__]
unfold
let bind_ens (#a:Type) (#b:Type) (#pre_f:vprop) (#post_f:a -> vprop)
             (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
             (#post_g:b -> vprop) (ens_g:(x:a -> ens_t (post_f x) b post_g))
  : ens_t pre_f b post_g
  = fun h0 y h2 -> req_f h0 /\ (exists x h1. ens_f h0 x h1 /\ (ens_g x) h1 y h2)

val bind (a:Type)
         (b:Type)
         (pre_f:vprop)
         (post_f:a -> vprop)
         (req_f:req_t pre_f)
         (ens_f:ens_t pre_f a post_f)
         (post_g:b -> vprop)
         (req_g:(x:a -> req_t (post_f x)))
         (ens_g:(x:a -> ens_t (post_f x) b post_g))
         (f:repr a pre_f post_f req_f ens_f)
         (g:(x:a -> repr b (post_f x) post_g (req_g x) (ens_g x)))
   : repr b pre_f post_g
          (bind_req req_f ens_f req_g)
          (bind_ens req_f ens_f ens_g)

let bind a b pre_f post_f req_f ens_f post_g req_g ens_g f g
  = fun frame ->
      let x = f frame in
      g x frame

unfold
let subcomp_pre (#a:Type)
                (#pre:vprop)
                (#post:a -> vprop)
                (req_f:req_t pre)
                (ens_f:ens_t pre a post)
                (req_g:req_t pre)
                (ens_g:ens_t pre a post)
   : pure_pre
   = (forall h. req_g h ==> req_f h) /\
     (forall h0 x h1. (req_g h0 /\ ens_f h0 x h1) ==> ens_g h0 x h1)

val subcomp (a:Type)
            (pre:vprop)
            (post:a -> vprop)
            (req_f:req_t pre)
            (ens_f:ens_t pre a post)
            (req_g:req_t pre)
            (ens_g:ens_t pre a post)
            (f:repr a pre post req_f ens_f)
  : Pure (repr a pre post req_g ens_g)
         (requires subcomp_pre req_f ens_f req_g ens_g)
         (ensures fun _ -> True)

let subcomp a pre post req_f ens_f req_g ens_g f = f

[@@ allow_informative_binders]
reifiable reflectable
layered_effect {
  SteelSel : a:Type
        -> pre:pre_t
        -> post:post_t a
        -> req:req_t pre
        -> ens:ens_t pre a post
        -> Effect
  with
  repr = repr;
  return = return;
  bind = bind;
  subcomp = subcomp
}

unfold
let bind_pure_steel_req (#a:Type)
                        (wp:pure_wp a)
                        (#pre_g:vprop)
                        (req_g:a -> req_t pre_g)
  : req_t pre_g
  = FStar.Monotonic.Pure.wp_monotonic_pure ();
    fun h -> wp (fun x -> req_g x h) /\ wp (fun _ -> True)

unfold
let bind_pure_steel_ens (#a:Type)
                        (#b:Type)
                        (wp:pure_wp a)
                        (#pre_g:vprop)
                        (#post_g:b -> vprop)
                        (ens_g:a -> ens_t pre_g b post_g)
   : ens_t pre_g b post_g
   = fun h0 r h1 -> wp (fun _ -> True) /\ (exists x. (~ (wp (fun r -> r =!= x))) /\ ens_g x h0 r h1)

val bind_pure_steel (a:Type)
                    (b:Type)
                    (wp:pure_wp a)
                    (pre_g:vprop)
                    (post_g:b -> vprop)
                    (req_g:a -> req_t pre_g)
                    (ens_g:a -> ens_t pre_g b post_g)
                    (f:eqtype_as_type unit -> PURE a wp)
                    (g:(x:a -> repr b pre_g post_g (req_g x) (ens_g x)))
  : repr b pre_g post_g
         (bind_pure_steel_req wp req_g)
         (bind_pure_steel_ens wp ens_g)

let bind_pure_steel a b wp pre_g post_b req_g ens_g f g
  = FStar.Monotonic.Pure.wp_monotonic_pure ();
    fun frame ->
      let x = f () in
      g x frame

polymonadic_bind (PURE, SteelSel) |> SteelSel = bind_pure_steel

unfold
let bind_div_steel_req (#a:Type) (wp:pure_wp a)
  (#pre_g:pre_t) (req_g:a -> req_t pre_g)
: req_t pre_g
= FStar.Monotonic.Pure.wp_monotonic_pure ();
  fun h -> wp (fun _ -> True) /\ (forall x. (req_g x) h)

unfold
let bind_div_steel_ens (#a:Type) (#b:Type)
  (wp:pure_wp a)
  (#pre_g:pre_t) (#post_g:post_t b) (ens_g:a -> ens_t pre_g b post_g)
: ens_t pre_g b post_g
= fun h0 r h1 -> wp (fun _ -> True) /\ (exists x. ens_g x h0 r h1)

#push-options "--z3rlimit 20 --fuel 2 --ifuel 1"
let bind_div_steel (a:Type) (b:Type)
  (wp:pure_wp a)
  (pre_g:pre_t) (post_g:post_t b) (req_g:a -> req_t pre_g) (ens_g:a -> ens_t pre_g b post_g)
  (f:eqtype_as_type unit -> DIV a wp) (g:(x:a -> repr b pre_g post_g (req_g x) (ens_g x)))
: repr b pre_g post_g
    (bind_div_steel_req wp req_g)
    (bind_div_steel_ens wp ens_g)
= FStar.Monotonic.Pure.wp_monotonic_pure ();
  fun frame ->
  let x = f () in
  g x frame
#pop-options

polymonadic_bind (DIV, SteelSel) |> SteelSel = bind_div_steel

let nmst_get (#st:Sem.st) ()
  : Sem.Mst (Sem.full_mem st)
           (fun _ -> True)
           (fun s0 s s1 -> s0 == s /\ s == s1)
  = NMST.get ()

[@__steel_reduce__]
let rec frame_equalities
  (frame:vprop)
  (h0:rmem frame) (h1:rmem frame) : prop
  = match frame with
    | VUnit p -> h0 frame == h1 frame
    | VStar p1 p2 ->
        can_be_split_star_l p1 p2;
        can_be_split_star_r p1 p2;

        let h01 = focus_rmem h0 p1 in
        let h11 = focus_rmem h1 p1 in

        let h02 = focus_rmem h0 p2 in
        let h12 = focus_rmem h1 p2 in


        frame_equalities p1 h01 h11 /\
        frame_equalities p2 h02 h12

let rec lemma_frame_equalities_refl (frame:vprop) (h:rmem frame) : Lemma (frame_equalities frame h h) =
  match frame with
  | VUnit _ -> ()
  | VStar p1 p2 ->
        can_be_split_star_l p1 p2;
        can_be_split_star_r p1 p2;

        let h1 = focus_rmem h p1 in
        let h2 = focus_rmem h p2 in

        lemma_frame_equalities_refl p1 h1;
        lemma_frame_equalities_refl p2 h2

val get (#p:vprop) (_:unit) : SteelSel (rmem p)
  p (fun _ -> p)
  (requires fun _ -> True)
  (ensures fun h0 r h1 -> normal (frame_equalities p h0 h1 /\ frame_equalities p r h1))

let get0 (#p:vprop) (_:unit) : repr (rmem p)
  p (fun _ -> p)
  (requires fun _ -> True)
  (ensures fun h0 r h1 -> normal (frame_equalities p h0 h1 /\ frame_equalities p r h1))
  = fun frame ->
      let m0 = nmst_get () in
      let h0 = mk_rmem p (core_mem m0) in
      lemma_frame_equalities_refl p h0;
      h0

let get #r _ = SteelSel?.reflect (get0 #r ())

let respects_fp (#fp:vprop) (p:hmem fp -> prop) : prop =
  forall (m0:hmem fp) (m1:mem{disjoint m0 m1}). p m0 <==> p (join m0 m1)

let fp_mprop (fp:vprop) = p:(hmem fp -> prop) { respects_fp #fp p }


val req_frame (frame:vprop) (snap:rmem frame) : mprop (hp_of frame)

let req_frame' (frame:vprop) (snap:rmem frame) (m:mem) : prop =
  interp (hp_of frame) m /\ mk_rmem frame m == snap

let req_frame frame snap =
  rmem_depends_only_on frame;
  req_frame' frame snap

#push-options "--z3rlimit 20"
let frame00 (#a:Type)
          (#pre:pre_t)
          (#post:post_t a)
          (#req:req_t pre)
          (#ens:ens_t pre a post)
          (f:repr a pre post req ens)
          (frame:vprop)
  : repr a
    (pre `star` frame)
    (fun x -> post x `star` frame)
    (fun h -> req (focus_rmem h pre))
    (fun h0 r h1 -> req (focus_rmem h0 pre) /\ ens (focus_rmem h0 pre) r (focus_rmem h1 (post r)) /\
     frame_equalities frame (focus_rmem h0 frame) (focus_rmem h1 frame))
  = fun frame' ->
      let m0 = nmst_get () in

      let snap:rmem frame = mk_rmem frame (core_mem m0) in

      focus_is_restrict_mk_rmem (pre `star` frame) pre (core_mem m0);

      let x = Sem.run #state #_ #_ #_ #_ #_ frame' (Sem.Frame (Sem.Act f) (hp_of frame) (req_frame frame snap)) in

      let m1 = nmst_get () in

      can_be_split_star_r pre frame;
      focus_is_restrict_mk_rmem (pre `star` frame) frame (core_mem m0);
      can_be_split_star_r (post x) frame;
      focus_is_restrict_mk_rmem (post x `star` frame) frame (core_mem m1);

      focus_is_restrict_mk_rmem (post x `star` frame) (post x) (core_mem m1);

      // We proved focus_rmem h0 frame == focus_rmem h1 frame so far
      let h0:rmem (pre `star` frame) = mk_rmem (pre `star` frame) (core_mem m0) in
      let h1:rmem (post x `star` frame) = mk_rmem (post x `star` frame) (core_mem m1) in

      lemma_frame_equalities_refl frame (focus_rmem h0 frame);

      x
#pop-options

let frame0 (#a:Type)
          (#pre:pre_t)
          (#post:post_t a)
          (#req:req_t pre)
          (#ens:ens_t pre a post)
          (f:repr a pre post req ens)
          (frame:vprop)
  : SteelSel a
    (pre `star` frame)
    (fun x -> post x `star` frame)
    (fun h -> (req (focus_rmem h pre)))
    (fun h0 r h1 -> (req (focus_rmem h0 pre) /\ ens (focus_rmem h0 pre) r (focus_rmem h1 (post r))
      /\ frame_equalities frame (focus_rmem h0 frame) (focus_rmem h1 frame)))
  = SteelSel?.reflect (frame00 f frame)

val frame' (#a:Type)
          (#pre:pre_t)
          (#post:post_t a)
          (#req:req_t pre)
          (#ens:ens_t pre a post)
          ($f:unit -> SteelSel a pre post req ens)
          (frame:vprop)
  : SteelSel a
    (pre `star` frame)
    (fun x -> post x `star` frame)
    (fun h -> (req (focus_rmem h pre)))
    (fun h0 r h1 -> (req (focus_rmem h0 pre) /\ ens (focus_rmem h0 pre) r (focus_rmem h1 (post r))
      /\ frame_equalities frame (focus_rmem h0 frame) (focus_rmem h1 frame)))

let frame' f frame = frame0 (reify (f ())) frame

let to_normal
  (#a:Type) (#pre:pre_t) (#post:post_t a) (#req:req_t pre) (#ens:ens_t pre a post)
  ($f:unit -> SteelSel a pre post (fun h -> req h) (fun h0 x h1 -> ens h0 x h1))
  : SteelSel a pre post
 (fun h -> normal (req h)) (fun h0 x h1 -> normal (ens h0 x h1))
  = f ()

val frame (#a:Type)
          (#pre:pre_t)
          (#post:post_t a)
          (#req:req_t pre)
          (#ens:ens_t pre a post)
          ($f:unit -> SteelSel a pre post req ens)
          (frame:vprop)
  : SteelSel a
    (pre `star` frame)
    (fun x -> post x `star` frame)
    (fun h -> normal (req (focus_rmem h pre)))
    (fun h0 r h1 -> normal (req (focus_rmem h0 pre) /\ ens (focus_rmem h0 pre) r (focus_rmem h1 (post r))
      /\ frame_equalities frame (focus_rmem h0 frame) (focus_rmem h1 frame)))

let frame f fr = to_normal (fun _ -> frame' f fr)


val vemp :vprop
let vemp' = {hp = emp; t = unit; sel = fun _ -> ()}
let vemp = VUnit vemp'

open FStar.Ghost

(* Simple Reference library, only full permissions.
   AF: Permissions would likely need to be an index of the vprop ptr.
   It cannot be part of a selector, as it is not invariant when joining with a disjoint memory
   Using the value of the ref as a selector is ok because refs with fractional permissions
   all share the same value.
   Refs on PCM are more complicated, and likely not usable with selectors
*)

module R = Steel.Reference
open Steel.FractionalPermission

val ref (a:Type0) : Type0
let ref a = R.ref a

val ptr (#a:Type0) (r:ref a) : slprop u#1
let ptr r = h_exists (R.pts_to r full_perm)

val ptr_sel' (#a:Type0) (r: ref a) : selector' a (ptr r)
let ptr_sel' #a r = fun h ->
  let x = id_elim_exists #(erased a) (R.pts_to r full_perm) h in
  reveal reveal x

let ptr_sel_depends_only_on (#a:Type0) (r:ref a)
  (m0:Mem.hmem (ptr r)) (m1:mem{disjoint m0 m1})
  : Lemma (ptr_sel' r m0 == ptr_sel' r (join m0 m1))
  = let x = reveal (id_elim_exists #(erased a) (R.pts_to r full_perm) m0) in
    let y = reveal (id_elim_exists #(erased a) (R.pts_to r full_perm) (join m0 m1)) in
    R.pts_to_witinv r full_perm;
    elim_wi (R.pts_to r full_perm) x y (join m0 m1)

val ptr_sel (#a:Type0) (r:ref a) : selector a (ptr r)
let ptr_sel r =
  Classical.forall_intro_2 (ptr_sel_depends_only_on r);
  ptr_sel' r

val vptr (#a:Type0) (r:ref a) : vprop
[@__steel_reduce__]
let vptr' #a r : vprop' =
  {hp = ptr r;
   t = a;
   sel = ptr_sel r}
[@__steel_reduce__]
let vptr r = VUnit (vptr' r)

(* AF : Keeping these assumed for now, the implementation should be straightforward *)

assume
val alloc (#a:Type0) (x:a) : SteelSel (ref a)
  vemp (fun r -> vptr r)
  (requires fun _ -> True)
  (ensures fun _ r h1 -> h1 (vptr r) == x)

assume
val read (#a:Type0) (r:ref a) : SteelSel a
  (vptr r) (fun _ -> vptr r)
  (requires fun _ -> True)
  (ensures fun h0 x h1 -> h0 (vptr r) == h1 (vptr r) /\ x == h1 (vptr r))

assume
val write (#a:Type0) (r:ref a) (x:a) : SteelSel unit
  (vptr r) (fun _ -> vptr r)
  (requires fun _ -> True)
  (ensures fun _ _ h1 -> x == h1 (vptr r))

(* Should do this in a more princpled way once we have automated framing *)

assume
val rewrite_2 (#a:Type) (r1 r2:ref a) : SteelSel unit
  (vptr r1 `star` vptr r2) (fun _ -> vptr r2 `star` vptr r1)
  (requires fun _ -> True)
  (ensures fun h0 _ h1 -> h0 (vptr r1) == h1 (vptr r1) /\ h0 (vptr r2) == h1 (vptr r2))

(* Some tests *)

(* AF: Ultimately, the precondition should probably be a squashed implicit that can be resolved by tactic *)
unfold
let sel (#a:Type) (#p:vprop) (h:rmem p) (r:ref a)
  : Ghost a (requires can_be_split p (vptr r)) (ensures fun _ -> True)
  = h (vptr r)

val test (r:ref int) : SteelSel unit
  (vptr r) (fun _ -> vptr r)
  (requires fun _ -> True)
  (ensures fun _ _ h1 -> sel h1 r == 0)

let test r =
  write r 1;
  write r 0

val test2 (r1 r2:ref int) : SteelSel unit
  (vptr r1 `star` vptr r2) (fun _ -> vptr r1 `star` vptr r2)
  (requires fun _ -> True)
  (ensures fun h0 _ h1 -> sel h1 r1 == 0 /\ sel h0 r2 == sel h1 r2)


let test2 r1 r2 =
  frame (fun _ -> write r1 1) (vptr r2);
  frame (fun _ -> write r1 0) (vptr r2)

val test3 (r1 r2 r3:ref int) : SteelSel unit
  (vptr r1 `star` (vptr r2 `star` vptr r3)) (fun _ -> vptr r1 `star` (vptr r2 `star` vptr r3))
  (requires fun _ ->
    can_be_split (vptr r1 `star` vptr r2 `star` vptr r3) (vptr r1) /\
    can_be_split (vptr r1 `star` (vptr r2 `star` vptr r3)) (vptr r2))
  (ensures fun h0 _ h1 ->
    can_be_split (vptr r1 `star` vptr r2 `star` vptr r3) (vptr r1) /\
    can_be_split (vptr r1 `star` (vptr r2 `star` vptr r3)) (vptr r2) /\
    sel h1 r1 == 0 /\
    sel h0 r2 == sel h1 r2
  )

// AF: Should work with r3 if we specify the additional can_be_split
let test3 r1 r2 r3 =
  let h0 = get () in
  frame (fun _ -> write r1 1) (vptr r2 `star` vptr r3);
  let h1 = get() in
  assert (sel h1 r1 == 1);
  assert (sel h0 r2 == sel h1 r2);
  frame (fun _ -> write r1 0) (vptr r2 `star` vptr r3)


val swap (#a:Type0) (r1 r2:ref a) : SteelSel unit
  (vptr r1 `star` vptr r2)
  (fun _ -> vptr r1 `star` vptr r2)
  (requires fun _ -> True)
  (ensures fun h0 _ h1 ->
    sel h0 r1 == sel h1 r2 /\
    sel h0 r2 == sel h1 r1)

let swap #a r1 r2 =
  let x1 = frame (fun _ -> read r1) (vptr r2) in
  rewrite_2 r1 r2;
  let x2 = frame (fun _ -> read r2) (vptr r1) in
  frame (fun _ -> write r2 x1) (vptr r1);
  rewrite_2 r2 r1;
  frame (fun _ -> write r1 x2) (vptr r2)


(* Going towards automation. This already verifies *)

(*

unfold
let return_req (p:vprop) : req_t p = fun _ -> True

unfold
let return_ens (a:Type) (x:a) (p:a -> vprop) : ens_t (p x) a p = fun _ r _ -> r == x

(*
 * Return is parametric in post (cf. return-scoping.txt)
 *)
val return (a:Type) (x:a) (#[@@ framing_implicit] p:a -> vprop)
: repr a (p x) p (return_req (p x)) (return_ens a x p)

let return a x #p = fun _ -> x

unfold
let bind_req (#a:Type)
  (#pre_f:pre_t) (#post_f:post_t a)
  (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
  (#pre_g:a -> pre_t)
  (req_g:(x:a -> req_t (pre_g x)))
  (_:squash (can_be_split_forall post_f pre_g))
: req_t pre_f
= fun m0 ->
  req_f m0 /\
  (forall (x:a) (m1:rmem (post_f x)). ens_f m0 x m1 ==> (req_g x) (focus_rmem m1 (pre_g x)))

unfold
let bind_ens (#a:Type) (#b:Type)
  (#pre_f:pre_t) (#post_f:post_t a)
  (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
  (#pre_g:a -> pre_t) (#post_g:post_t b)
  (ens_g:(x:a -> ens_t (pre_g x) b post_g))
  (_:squash (can_be_split_forall post_f pre_g))
: ens_t pre_f b post_g
= fun m0 y m2 ->
  req_f m0 /\
  (exists (x:a) (m1:rmem (post_f x)). ens_f m0 x m1 /\ (ens_g x) (focus_rmem m1 (pre_g x)) y m2)

val bind (a:Type) (b:Type)
  (#[@@ framing_implicit] pre_f:pre_t) (#[@@ framing_implicit] post_f:post_t a)
  (#[@@ framing_implicit] req_f:req_t pre_f) (#[@@ framing_implicit] ens_f:ens_t pre_f a post_f)
  (#[@@ framing_implicit] pre_g:a -> pre_t) (#[@@ framing_implicit] post_g:post_t b)
  (#[@@ framing_implicit] req_g:(x:a -> req_t (pre_g x))) (#[@@ framing_implicit] ens_g:(x:a -> ens_t (pre_g x) b post_g))
  (#[@@ framing_implicit] p1:squash (can_be_split_forall post_f pre_g))
  (f:repr a pre_f post_f req_f ens_f)
  (g:(x:a -> repr b (pre_g x) post_g (req_g x) (ens_g x)))
: repr b
    pre_f
    post_g
    (bind_req req_f ens_f req_g p1)
    (bind_ens req_f ens_f ens_g p1)

let nmst_get (#st:Sem.st) ()
  : Sem.Mst (Sem.full_mem st)
           (fun _ -> True)
           (fun s0 s s1 -> s0 == s /\ s == s1)
  = NMST.get ()

let bind a b #pre_f #post_f #req_f #ens_f #pre_g #post_g #req_g #ens_g #p1 f g = fun frame ->

  let x = f frame in

  let m1 = nmst_get () in

  focus_is_restrict_mk_rmem (post_f x) (pre_g x) (core_mem m1);
  assert ((req_g x) (mk_rmem (pre_g x) (core_mem m1)));

  can_be_split_3_interp (post_f x).hp (pre_g x).hp frame (locks_invariant Set.empty m1) m1;

  g x frame


unfold
let subcomp_pre (#a:Type)
  (#pre_f:pre_t) (#post_f:post_t a) (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
  (#pre_g:pre_t) (#post_g:post_t a) (req_g:req_t pre_g) (ens_g:ens_t pre_g a post_g)
  (_:squash (can_be_split pre_g pre_f))
  (_:squash (can_be_split_forall post_f post_g))
: pure_pre
= (forall (m0:rmem pre_g). req_g m0 ==> req_f (focus_rmem m0 pre_f)) /\
  (forall (m0:rmem pre_g) (x:a) (m1:rmem (post_f x)). ens_f (focus_rmem m0 pre_f) x m1 ==> ens_g m0 x (focus_rmem m1 (post_g x)))

val subcomp (a:Type)
  (#[@@ framing_implicit] pre_f:pre_t) (#[@@ framing_implicit] post_f:post_t a)
  (#[@@ framing_implicit] req_f:req_t pre_f) (#[@@ framing_implicit] ens_f:ens_t pre_f a post_f)
  (#[@@ framing_implicit] pre_g:pre_t) (#[@@ framing_implicit] post_g:post_t a)
  (#[@@ framing_implicit] req_g:req_t pre_g) (#[@@ framing_implicit] ens_g:ens_t pre_g a post_g)
  (#[@@ framing_implicit] p1:squash (can_be_split pre_g pre_f))
  (#[@@ framing_implicit] p2:squash (can_be_split_forall post_f post_g))
  (f:repr a pre_f post_f req_f ens_f)
: Pure (repr a pre_g post_g req_g ens_g)
  (requires subcomp_pre req_f ens_f req_g ens_g p1 p2)
  (ensures fun _ -> True)

let subcomp a #pre_f #post_f #req_f #ens_f #pre_g #post_g #req_g #ens_g #p1 #p2 f =
  fun frame ->

    let m0 = nmst_get () in
    focus_is_restrict_mk_rmem pre_g pre_f (core_mem m0);

    let x = f frame in

    let m1 = nmst_get () in
    focus_is_restrict_mk_rmem (post_f x) (post_g x) (core_mem m1);

    can_be_split_3_interp (post_f x).hp (post_g x).hp frame (locks_invariant Set.empty m1) m1;

    x


[@@allow_informative_binders]
reifiable reflectable
layered_effect {
  SteelSel: a:Type -> pre:pre_t -> post:post_t a -> req_t pre -> ens_t pre a post -> Effect
  with repr = repr;
       return = return;
       bind = bind;
       subcomp = subcomp
}

unfold
let bind_pure_steel__req (#a:Type) (wp:pure_wp a)
  (#pre:pre_t) (req:a -> req_t pre)
: req_t pre
= fun m -> wp (fun x -> (req x) m) /\ as_requires wp

unfold
let bind_pure_steel__ens (#a:Type) (#b:Type)
  (wp:pure_wp a)
  (#pre:pre_t) (#post:post_t b) (ens:a -> ens_t pre b post)
: ens_t pre b post
= fun m0 r m1 -> as_requires wp /\ (exists (x:a). as_ensures wp x /\ (ens x) m0 r m1)

assume
val bind_pure_steel_ (a:Type) (b:Type)
  (wp:pure_wp a)
  (#[@@ framing_implicit] pre:pre_t) (#[@@ framing_implicit] post:post_t b)
  (#[@@ framing_implicit] req:a -> req_t pre) (#[@@ framing_implicit] ens:a -> ens_t pre b post)
  (f:eqtype_as_type unit -> PURE a wp) (g:(x:a -> repr b pre post (req x) (ens x)))
: repr b
    pre
    post
    (bind_pure_steel__req wp req)
    (bind_pure_steel__ens wp ens)

polymonadic_bind (PURE, SteelSel) |> SteelSel = bind_pure_steel_

unfold
let bind_div_steel_req (#a:Type) (wp:pure_wp a)
  (#pre_g:pre_t) (req_g:a -> req_t pre_g)
: req_t pre_g
= FStar.Monotonic.Pure.wp_monotonic_pure ();
  fun h -> wp (fun _ -> True) /\ (forall x. (req_g x) h)

unfold
let bind_div_steel_ens (#a:Type) (#b:Type)
  (wp:pure_wp a)
  (#pre_g:pre_t) (#post_g:post_t b) (ens_g:a -> ens_t pre_g b post_g)
: ens_t pre_g b post_g
= fun h0 r h1 -> wp (fun _ -> True) /\ (exists x. ens_g x h0 r h1)


assume
val bind_div_steel (a:Type) (b:Type)
  (wp:pure_wp a)
  (pre_g:pre_t) (post_g:post_t b) (req_g:a -> req_t pre_g) (ens_g:a -> ens_t pre_g b post_g)
  (f:eqtype_as_type unit -> DIV a wp) (g:(x:a -> repr b pre_g post_g (req_g x) (ens_g x)))
: repr b pre_g post_g
    (bind_div_steel_req wp req_g)
    (bind_div_steel_ens wp ens_g)

polymonadic_bind (DIV, SteelSel) |> SteelSel = bind_div_steel

*)



// unfold
// let bind_steel_steelf_req (#a:Type)
//   (#pre_f:pre_t) (#post_f:post_t a)
//   (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
//   (#pre_g:a -> pre_t)
//   (req_g:(x:a -> req_t (pre_g x)))
//   (frame_f:vprop)
//   (_:squash (can_be_split_forall (fun x -> post_f x `star` frame_f) pre_g))
// : req_t (pre_f `star` frame_f)
// = fun m0 ->
//   req_f (focus_rmem m0 pre_f) /\
//   (forall (x:a) (m1:rmem (post_f x `star` frame_f)). ens_f (focus_rmem m0 pre_f) x (focus_rmem m1 (post_f x)) ==> (req_g x) (focus_rmem m1 (pre_g x)))

// unfold
// let bind_steel_steelf_ens (#a:Type) (#b:Type)
//   (#pre_f:pre_t) (#post_f:post_t a)
//   (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
//   (#pre_g:a -> pre_t) (#post_g:post_t b)
//   (ens_g:(x:a -> ens_t (pre_g x) b post_g))
//   (frame_f:vprop)
//   (_:squash (can_be_split_forall (fun x -> post_f x `star` frame_f) pre_g))
// : ens_t (pre_f `star` frame_f) b post_g
// = fun m0 y m2 ->
//   req_f (focus_rmem m0 pre_f) /\
//   (exists (x:a) (m1:rmem (post_f x `star` frame_f)).
//     ens_f (focus_rmem m0 pre_f) x (focus_rmem m1 (post_f x)) /\ (ens_g x) (focus_rmem m1 (pre_g x)) y m2)

// val bind_steel_steelf (a:Type) (b:Type)
//   (#pre_f:pre_t) (#post_f:post_t a)
//   (#req_f:req_t pre_f) (#ens_f:ens_t pre_f a post_f)
//   (#pre_g:a -> pre_t) (#post_g:post_t b)
//   (#req_g:(x:a -> req_t (pre_g x))) (#ens_g:(x:a -> ens_t (pre_g x) b post_g))
//   (#frame_f:vprop)
//   (#p:squash (can_be_split_forall (fun x -> post_f x `star` frame_f) pre_g))
//   (f:repr a pre_f post_f req_f ens_f)
//   (g:(x:a -> repr b (pre_g x) post_g (req_g x) (ens_g x)))
// : repr b
//     (pre_f `star` frame_f)
//     post_g
//     (bind_steel_steelf_req req_f ens_f req_g frame_f p)
//     (bind_steel_steelf_ens req_f ens_f ens_g frame_f p)

// // let frame_aux (#a:Type)
// //   (#pre:pre_t) (#post:post_t a) (#req:req_t pre) (#ens:ens_t pre a post)
// //   ($f:repr a pre post req ens) (frame:vprop)
// // : repr a (pre `star` frame) (fun x -> post x `star` frame) req ens
// // = fun frame' ->
// //   Sem.run #state #_ #_ #_ #_ #_ frame' (Sem.Frame (Sem.Act f) frame (fun _ -> True))


// let bind_steel_steelf a b f g =
//   fun frame' -> admit()
