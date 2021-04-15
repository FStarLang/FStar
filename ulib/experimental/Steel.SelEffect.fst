module Steel.SelEffect

module Sem = Steel.Semantics.Hoare.MST
module Mem = Steel.Memory
module C = Steel.Effect.Common
open Steel.Semantics.Instantiate
module FExt = FStar.FunctionalExtensionality
module Eff = Steel.Effect

let _:squash (forall p q. can_be_split p q == Mem.slimp (hp_of p) (hp_of q)) = reveal_can_be_split ()

#set-options "--warn_error -330"  //turn off the experimental feature warning

let hmem (p:vprop) = hmem (hp_of p)

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

[@@ __steel_reduce__]
let req_to_act_req (#pre:pre_t) (req:req_t pre) : Sem.l_pre #state (hp_of pre) =
  rmem_depends_only_on pre;
  fun m0 -> interp (hp_of pre) m0 /\ req (mk_rmem pre m0)

unfold
let to_post (#a:Type) (post:post_t a) = fun x -> (hp_of (post x))

[@@ __steel_reduce__]
let ens_to_act_ens (#pre:pre_t) (#a:Type) (#post:post_t a) (ens:ens_t pre a post)
: Sem.l_post #state #a (hp_of pre) (to_post post)
= rmem_depends_only_on pre;
  rmem_depends_only_on_post post;
  fun m0 x m1 ->
    interp (hp_of pre) m0 /\ interp (hp_of (post x)) m1 /\ ens (mk_rmem pre m0) x (mk_rmem (post x) m1)

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

let focus_focus_is_focus (fp0 fp1 fp2:vprop) (m:hmem fp0)
  : Lemma
    (requires fp0 `can_be_split` fp1 /\ fp1 `can_be_split` fp2)
    (ensures focus_rmem (focus_rmem (mk_rmem fp0 m) fp1) fp2 == focus_rmem (mk_rmem fp0 m) fp2)
  = let f0:rmem fp0 = mk_rmem fp0 m in
    let f1:rmem fp1 = focus_rmem f0 fp1 in
    let f20:rmem fp2 = focus_rmem f0 fp2 in
    let f21:rmem fp2 = focus_rmem f1 fp2 in

    let aux (r:vprop{can_be_split fp2 r}) : Lemma (f20 r == f21 r)
      = reveal_mk_rmem fp0 m r;
        reveal_focus_rmem f0 fp1 r;
        reveal_focus_rmem f0 fp2 r;
        reveal_focus_rmem f1 fp2 r

    in Classical.forall_intro aux;

    FExt.extensionality_g
      (r0:vprop{can_be_split fp2 r0})
      (fun r0 -> normal (t_of r0))
      f20 f21

val can_be_split_3_interp (p1 p2 q r:slprop u#1) (m:mem)
: Lemma
  (requires p1 `slimp` p2 /\  interp (p1 `Mem.star` q `Mem.star` r) m)
  (ensures interp (p2 `Mem.star` q `Mem.star` r) m)

let can_be_split_3_interp p1 p2 q r m =
  Mem.star_associative p1 q r;
  Mem.star_associative p2 q r;
  slimp_star p1 p2 (q `Mem.star` r) (q `Mem.star` r)

let repr (a:Type) (_:bool) (pre:pre_t) (post:post_t a) (req:req_t pre) (ens:ens_t pre a post) =
  Sem.action_t #state #a (hp_of pre) (to_post post)
    ((req_to_act_req req))
    ((ens_to_act_ens ens))

let nmst_get (#st:Sem.st) ()
  : Sem.Mst (Sem.full_mem st)
           (fun _ -> True)
           (fun s0 s s1 -> s0 == s /\ s == s1)
  = NMST.get ()

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

let return a x #p = fun _ ->
      let m0 = nmst_get () in
      let h0 = mk_rmem (p x) (core_mem m0) in
      lemma_frame_equalities_refl (p x) h0;
      x

#push-options "--fuel 0 --ifuel 0"

let norm_repr (#a:Type) (#framed:bool)
 (#pre:pre_t) (#post:post_t a) (#req:req_t pre) (#ens:ens_t pre a post)
 (f:repr a framed pre post req ens) : repr a framed pre post (fun h -> normal (req h)) (fun h0 x h1 -> normal (ens h0 x h1))
 = f

unfold
let bind_req_unnormal (#a:Type)
  (#pre_f:pre_t) (#post_f:post_t a)
  (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
  (#pre_g:a -> pre_t)
  (#pr:a -> prop)
  (req_g:(x:a -> req_t (pre_g x)))
  (frame_f:vprop) (frame_g:a -> vprop)
  (_:squash (can_be_split_forall_dep pr
    (fun x -> post_f x `star` frame_f) (fun x -> pre_g x `star` frame_g x)))
  (m0:rmem (pre_f `star` frame_f))
= req_f (focus_rmem m0 pre_f) /\
  (forall (x:a) (m1:rmem (post_f x `star` frame_f)).
    (ens_f (focus_rmem m0 pre_f) x (focus_rmem m1 (post_f x)) /\
      frame_equalities frame_f (focus_rmem m0 frame_f) (focus_rmem m1 frame_f))
    ==>
      pr x /\
      (can_be_split_trans (post_f x `star` frame_f) (pre_g x `star` frame_g x) (pre_g x);
      (req_g x) (focus_rmem m1 (pre_g x))))

unfold
let bind_ens_unnormal (#a:Type) (#b:Type)
  (#pre_f:pre_t) (#post_f:post_t a)
  (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
  (#pre_g:a -> pre_t) (#post_g:a -> post_t b)
  (#pr:a -> prop)
  (ens_g:(x:a -> ens_t (pre_g x) b (post_g x)))
  (frame_f:vprop) (frame_g:a -> vprop)
  (post:post_t b)
  (_:squash (can_be_split_forall_dep pr
    (fun x -> post_f x `star` frame_f) (fun x -> pre_g x `star` frame_g x)))
  (_:squash (can_be_split_post (fun x y -> post_g x y `star` frame_g x) post))
  (m0:rmem (pre_f `star` frame_f))
  (y:b)
  (m2:rmem (post y))
= req_f (focus_rmem m0 pre_f) /\
  (exists (x:a) (m1:rmem (post_f x `star` frame_f)).
    pr x /\ (
    can_be_split_trans (post_f x `star` frame_f) (pre_g x `star` frame_g x) (pre_g x);
    can_be_split_trans (post_f x `star` frame_f) (pre_g x `star` frame_g x) (frame_g x);
    can_be_split_trans (post y) (post_g x y `star` frame_g x) (post_g x y);
    can_be_split_trans (post y) (post_g x y `star` frame_g x) (frame_g x);
    frame_equalities frame_f (focus_rmem m0 frame_f) (focus_rmem m1 frame_f) /\
    frame_equalities (frame_g x) (focus_rmem m1 (frame_g x)) (focus_rmem m2 (frame_g x)) /\
    ens_f (focus_rmem m0 pre_f) x (focus_rmem m1 (post_f x)) /\
    (ens_g x) (focus_rmem m1 (pre_g x)) y (focus_rmem m2 (post_g x y))))


val bind_aux (a:Type) (b:Type)
  (#framed_f:eqtype_as_type bool) (#framed_g:eqtype_as_type bool)
  (#pre_f:pre_t) (#post_f:post_t a)
  (#req_f:req_t pre_f) (#ens_f:ens_t pre_f a post_f)
  (#pre_g:a -> pre_t) (#post_g:a -> post_t b)
  (#req_g:(x:a -> req_t (pre_g x))) (#ens_g:(x:a -> ens_t (pre_g x) b (post_g x)))
  (#frame_f:vprop) (#frame_g:a -> vprop)
  (#post:post_t b)
  (#_ : squash (maybe_emp framed_f frame_f))
  (#_ : squash (maybe_emp_dep framed_g frame_g))
  (#pr:a -> prop)
  (#p:squash (can_be_split_forall_dep pr
    (fun x -> post_f x `star` frame_f) (fun x -> pre_g x `star` frame_g x)))
  (#p2:squash (can_be_split_post (fun x y -> post_g x y `star` frame_g x) post))
  (f:repr a framed_f pre_f post_f req_f ens_f)
  (g:(x:a -> repr b framed_g (pre_g x) (post_g x) (req_g x) (ens_g x)))
: repr b
    true
    (pre_f `star` frame_f)
    post
    (bind_req_unnormal req_f ens_f req_g frame_f frame_g p)
    (bind_ens_unnormal req_f ens_f ens_g frame_f frame_g post p p2)

val req_frame (frame:vprop) (snap:rmem frame) : mprop (hp_of frame)

let req_frame' (frame:vprop) (snap:rmem frame) (m:mem) : prop =
  interp (hp_of frame) m /\ mk_rmem frame m == snap

let req_frame frame snap =
  rmem_depends_only_on frame;
  req_frame' frame snap

#push-options "--z3rlimit 20 --fuel 1 --ifuel 1"

val frame00 (#a:Type)
          (#framed:bool)
          (#pre:pre_t)
          (#post:post_t a)
          (#req:req_t pre)
          (#ens:ens_t pre a post)
          ($f:repr a framed pre post req ens)
          (frame:vprop)
  : repr a
    true
    (pre `star` frame)
    (fun x -> post x `star` frame)
    (fun h -> req (focus_rmem h pre))
    (fun h0 r h1 -> req (focus_rmem h0 pre) /\ ens (focus_rmem h0 pre) r (focus_rmem h1 (post r)) /\
     frame_equalities frame (focus_rmem h0 frame) (focus_rmem h1 frame))

let frame00 #a #framed #pre #post #req #ens f frame =
  fun frame' ->
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
      lemma_frame_equalities_refl frame (focus_rmem h0 frame);

      x

#pop-options


#push-options "--z3rlimit 20"
let bind_aux a b #framed_f #framed_g #pre_f #post_f #req_f #ens_f #pre_g #post_g #req_g #ens_g #frame_f #frame_g #post #_ #_ #p #p2 f g =
  fun frame ->
    let m0 = nmst_get () in

    let h0 = mk_rmem (pre_f `star` frame_f) (core_mem m0) in

    let x = frame00 f frame_f frame  in

    let m1 = nmst_get () in

    let h1 = mk_rmem (post_f x `star` frame_f) (core_mem m1) in

    let h1' = mk_rmem (pre_g x `star` frame_g x) (core_mem m1) in

    can_be_split_trans (post_f x `star` frame_f) (pre_g x `star` frame_g x) (pre_g x);
    focus_is_restrict_mk_rmem
      (post_f x `star` frame_f)
      (pre_g x `star` frame_g x)
      (core_mem m1);
    focus_focus_is_focus
      (post_f x `star` frame_f)
      (pre_g x `star` frame_g x)
      (pre_g x)
      (core_mem m1);
    assert (focus_rmem h1' (pre_g x) == focus_rmem h1 (pre_g x));

    can_be_split_3_interp
      (hp_of (post_f x `star` frame_f))
      (hp_of (pre_g x `star` frame_g x))
      frame (locks_invariant Set.empty m1) m1;

    let y = frame00 (g x) (frame_g x) frame in

    let m2 = nmst_get () in

    can_be_split_trans (post_f x `star` frame_f) (pre_g x `star` frame_g x) (pre_g x);
    can_be_split_trans (post_f x `star` frame_f) (pre_g x `star` frame_g x) (frame_g x);
    can_be_split_trans (post y) (post_g x y `star` frame_g x) (post_g x y);
    can_be_split_trans (post y) (post_g x y `star` frame_g x) (frame_g x);

    let h2' = mk_rmem (post_g x y `star` frame_g x) (core_mem m2) in
    let h2 = mk_rmem (post y) (core_mem m2) in



    // assert (focus_rmem h1' (pre_g x) == focus_rmem h1 (pre_g x));

    focus_focus_is_focus
      (post_f x `star` frame_f)
      (pre_g x `star` frame_g x)
      (frame_g x)
      (core_mem m1);

    focus_is_restrict_mk_rmem
      (post_g x y `star` frame_g x)
      (post y)
      (core_mem m2);

    focus_focus_is_focus
      (post_g x y `star` frame_g x)
      (post y)
      (frame_g x)
      (core_mem m2);
    focus_focus_is_focus
      (post_g x y `star` frame_g x)
      (post y)
      (post_g x y)
      (core_mem m2);

    can_be_split_3_interp
      (hp_of (post_g x y `star` frame_g x))
      (hp_of (post y))
      frame (locks_invariant Set.empty m2) m2;


    y

#pop-options

let bind a b #framed_f #framed_g #pre_f #post_f #req_f #ens_f #pre_g #post_g #req_g #ens_g #post #_ #_ #pr #p1 #p2 f g =
  norm_repr (bind_aux a b f g)

unfold
let subcomp_pre_unnormal (#a:Type)
  (#pre_f:pre_t) (#post_f:post_t a) (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
  (#pre_g:pre_t) (#post_g:post_t a) (req_g:req_t pre_g) (ens_g:ens_t pre_g a post_g)
  (_:squash (can_be_split pre_g pre_f))
  (_:squash (equiv_forall post_f post_g))
: pure_pre
= ((forall (m0:rmem pre_g). req_g m0 ==> req_f (focus_rmem m0 pre_f)) /\
  (forall (m0:rmem pre_g) (x:a) (m1:rmem (post_g x)). ens_f (focus_rmem m0 pre_f) x (focus_rmem m1 (post_f x)) ==> ens_g m0 x m1))

let unnormal (p:prop) : Lemma (requires normal p) (ensures p) = ()

let subcomp a #framed_f #framed_g #pre_f #post_f #req_f #ens_f #pre_g #post_g #req_g #ens_g #p1 #p2 f =
  fun frame ->
    let m0 = nmst_get () in
    let h0 = mk_rmem pre_g (core_mem m0) in
    focus_is_restrict_mk_rmem pre_g pre_f (core_mem m0);

    can_be_split_3_interp (hp_of pre_g) (hp_of pre_f) frame (locks_invariant Set.empty m0) m0;

    let x = f frame in


    let m1 = nmst_get () in
    let h1 = mk_rmem (post_g x) (core_mem m1) in

    focus_is_restrict_mk_rmem (post_g x) (post_f x) (core_mem m1);

    unnormal (subcomp_pre_unnormal req_f ens_f req_g ens_g p1 p2);


    can_be_split_3_interp (hp_of (post_f x)) (hp_of (post_g x)) frame (locks_invariant Set.empty m1) m1;

    x

let bind_pure_steel_ a b #wp #pre #post #req #ens f g
  = FStar.Monotonic.Pure.wp_monotonic_pure ();
    fun frame ->
      let x = f () in
      g x frame

(* We need a bind with DIV to implement par, using reification *)

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
  (framed:eqtype_as_type bool)
  (pre_g:pre_t) (post_g:post_t b) (req_g:a -> req_t pre_g) (ens_g:a -> ens_t pre_g b post_g)
  (f:eqtype_as_type unit -> DIV a wp) (g:(x:a -> repr b framed pre_g post_g (req_g x) (ens_g x)))
: repr b framed pre_g post_g
    (bind_div_steel_req wp req_g)
    (bind_div_steel_ens wp ens_g)
= FStar.Monotonic.Pure.wp_monotonic_pure ();
  fun frame ->
  let x = f () in
  g x frame
#pop-options

polymonadic_bind (DIV, SteelSelBase) |> SteelSelBase = bind_div_steel
#pop-options

let noop0 (_:unit)
  : repr unit false vemp (fun _ -> vemp) (requires fun _ -> True) (ensures fun _ _ _ -> True)
  = fun frame -> ()

let noop () = SteelSel?.reflect (noop0 ())

let get0 (#p:vprop) (_:unit) : repr (rmem p)
  true p (fun _ -> p)
  (requires fun _ -> True)
  (ensures fun h0 r h1 -> normal (frame_equalities p h0 h1 /\ frame_equalities p r h1))
  = fun frame ->
      let m0 = nmst_get () in
      let h0 = mk_rmem p (core_mem m0) in
      lemma_frame_equalities_refl p h0;
      h0

let get #r _ = SteelSelF?.reflect (get0 #r ())

let intro_star (p q:vprop) (r:slprop) (vp:erased (t_of p)) (vq:erased (t_of q)) (m:mem)
  (proof:(m:mem) -> Lemma
    (requires interp (hp_of p) m /\ sel_of p m == reveal vp)
    (ensures interp (hp_of q) m)
  )
  : Lemma
   (requires interp ((hp_of p) `Mem.star` r) m /\ sel_of p m == reveal vp)
   (ensures interp ((hp_of q) `Mem.star` r) m)
= let p = hp_of p in
  let q = hp_of q in
  let intro (ml mr:mem) : Lemma
      (requires interp q ml /\ interp r mr /\ disjoint ml mr)
      (ensures disjoint ml mr /\ interp (q `Mem.star` r) (Mem.join ml mr))
  = intro_star q r ml mr
  in
  elim_star p r m;
  Classical.forall_intro (Classical.move_requires proof);
  Classical.forall_intro_2 (Classical.move_requires_2 intro)

#push-options "--z3rlimit 20 --fuel 1 --ifuel 0"
let change_slprop0 (p q:vprop) (vp:erased (t_of p)) (vq:erased (t_of q))
  (proof:(m:mem) -> Lemma
    (requires interp (hp_of p) m /\ sel_of p m == reveal vp)
    (ensures interp (hp_of q) m /\ sel_of q m == reveal vq)
  ) : repr unit false p (fun _ -> q) (fun h -> h p == reveal vp) (fun _ _ h1 -> h1 q == reveal vq)
  = fun frame ->
      let m = nmst_get () in
      proof (core_mem m);
      Classical.forall_intro (Classical.move_requires proof);
      intro_star p q (frame `Mem.star` locks_invariant Set.empty m) vp vq m proof
#pop-options

let change_slprop p q vp vq l  = SteelSel?.reflect (change_slprop0 p q vp vq l)

#push-options "--z3rlimit 20 --fuel 1 --ifuel 0"
let change_slprop_20 (p q:vprop) (vq:erased (t_of q))
  (proof:(m:mem) -> Lemma
    (requires interp (hp_of p) m)
    (ensures interp (hp_of q) m /\ sel_of q m == reveal vq)
  ) : repr unit false p (fun _ -> q) (fun _ -> True) (fun _ _ h1 -> h1 q == reveal vq)
  = fun frame ->
      let m = nmst_get () in
      proof (core_mem m);
      Classical.forall_intro (Classical.move_requires proof);
      intro_star p q (frame `Mem.star` locks_invariant Set.empty m) (sel_of p m) vq m proof
#pop-options

let change_slprop_2 p q vq l = SteelSel?.reflect (change_slprop_20 p q vq l)

let change_slprop_rel0 (p q:vprop)
  (rel : normal (t_of p) -> normal (t_of q) -> prop)
  (proof:(m:mem) -> Lemma
    (requires interp (hp_of p) m)
    (ensures
      interp (hp_of p) m /\
      interp (hp_of q) m /\
      rel (sel_of p m) (sel_of q m))
  ) : repr unit false p (fun _ -> q) (fun _ -> True) (fun h0 _ h1 -> rel (h0 p) (h1 q))
  = fun frame ->
      let m = nmst_get () in

      proof (core_mem m);
      let h0 = mk_rmem p (core_mem m) in
      let h1 = mk_rmem q (core_mem m) in
      reveal_mk_rmem p (core_mem m) p;
      reveal_mk_rmem q (core_mem m) q;
      intro_star p q (frame `Mem.star` locks_invariant Set.empty m) (sel_of p (core_mem m)) (sel_of q (core_mem m)) m proof

let change_slprop_rel p q rel proof = SteelSel?.reflect (change_slprop_rel0 p q rel proof)

let extract_info0 (p:vprop) (vp:erased (normal (t_of p))) (fact:prop)
  (l:(m:mem) -> Lemma
    (requires interp (hp_of p) m /\ sel_of p m == reveal vp)
    (ensures fact)
  ) : repr unit false p (fun _ -> p)
      (fun h -> h p == reveal vp)
      (fun h0 _ h1 -> normal (frame_equalities p h0 h1) /\ fact)
  = fun frame ->
      let m0 = nmst_get () in
      let h0 = mk_rmem p (core_mem m0) in
      lemma_frame_equalities_refl p h0;
      l (core_mem m0)

let extract_info p vp fact l = SteelSel?.reflect (extract_info0 p vp fact l)

let sladmit _ = SteelSelF?.reflect (fun _ -> NMST.nmst_admit ())

let reveal_star0 (p1 p2:vprop)
  : repr unit false (p1 `star` p2) (fun _ -> p1 `star` p2)
   (fun _ -> True)
   (fun h0 _ h1 ->
     h0 p1 == h1 p1 /\ h0 p2 == h1 p2 /\
     h0 (p1 `star` p2) == (h0 p1, h0 p2) /\
     h1 (p1 `star` p2) == (h1 p1, h1 p2)
   )
 = fun frame ->
     let m = nmst_get() in
     let h0 = mk_rmem (p1 `star` p2) (core_mem m) in
     reveal_mk_rmem (p1 `star` p2) m (p1 `star` p2);
     reveal_mk_rmem (p1 `star` p2) m p1;
     reveal_mk_rmem (p1 `star` p2) m p2

let reveal_star p1 p2 = SteelSel?.reflect (reveal_star0 p1 p2)

let reveal_star_30 (p1 p2 p3:vprop)
 : repr unit false (p1 `star` p2 `star` p3) (fun _ -> p1 `star` p2 `star` p3)
   (requires fun _ -> True)
   (ensures fun h0 _ h1 ->
     can_be_split (p1 `star` p2 `star` p3) p1 /\
     can_be_split (p1 `star` p2 `star` p3) p2 /\
     h0 p1 == h1 p1 /\ h0 p2 == h1 p2 /\ h0 p3 == h1 p3 /\
     h0 (p1 `star` p2 `star` p3) == ((h0 p1, h0 p2), h0 p3) /\
     h1 (p1 `star` p2 `star` p3) == ((h1 p1, h1 p2), h1 p3)
   )
 = fun frame ->
     let m = nmst_get () in
     let h0 = mk_rmem (p1 `star` p2 `star` p3) (core_mem m) in
     can_be_split_trans (p1 `star` p2 `star` p3) (p1 `star` p2) p1;
     can_be_split_trans (p1 `star` p2 `star` p3) (p1 `star` p2) p2;
     reveal_mk_rmem (p1 `star` p2 `star` p3) m (p1 `star` p2 `star` p3);
     reveal_mk_rmem (p1 `star` p2 `star` p3) m (p1 `star` p2);
     reveal_mk_rmem (p1 `star` p2 `star` p3) m p3

let reveal_star_3 p1 p2 p3 = SteelSel?.reflect (reveal_star_30 p1 p2 p3)

(* Simple Reference library, only full permissions.
   AF: Permissions would likely need to be an index of the vprop ptr.
   It cannot be part of a selector, as it is not invariant when joining with a disjoint memory
   Using the value of the ref as a selector is ok because refs with fractional permissions
   all share the same value.
   Refs on PCM are more complicated, and likely not usable with selectors
*)

module R = Steel.Reference
open Steel.FractionalPermission

val ptr_sel' (#a:Type0) (r: ref a) : selector' a (ptr r)
let ptr_sel' #a r = fun h ->
  let x = id_elim_exists #(erased a) (R.pts_to r full_perm) h in
  reveal (reveal x)

let ptr_sel_depends_only_on (#a:Type0) (r:ref a)
  (m0:Mem.hmem (ptr r)) (m1:mem{disjoint m0 m1})
  : Lemma (ptr_sel' r m0 == ptr_sel' r (Mem.join m0 m1))
  = let x = reveal (id_elim_exists #(erased a) (R.pts_to r full_perm) m0) in
    let y = reveal (id_elim_exists #(erased a) (R.pts_to r full_perm) (Mem.join m0 m1)) in
    R.pts_to_witinv r full_perm;
    elim_wi (R.pts_to r full_perm) x y (Mem.join m0 m1)

let ptr_sel_depends_only_on_core (#a:Type0) (r:ref a)
  (m0:Mem.hmem (ptr r))
  : Lemma (ptr_sel' r m0 == ptr_sel' r (core_mem m0))
  = let x = reveal (id_elim_exists #(erased a) (R.pts_to r full_perm) m0) in
    let y = reveal (id_elim_exists #(erased a) (R.pts_to r full_perm) (core_mem m0)) in
    R.pts_to_witinv r full_perm;
    elim_wi (R.pts_to r full_perm) x y (core_mem m0)


let ptr_sel r =
  Classical.forall_intro_2 (ptr_sel_depends_only_on r);
  Classical.forall_intro (ptr_sel_depends_only_on_core r);
  ptr_sel' r

let ptr_sel_interp #a r m = R.pts_to_witinv r full_perm

friend Steel.Effect

let as_steelsel0 (#a:Type)
  (#pre:pre_t) (#post:post_t a)
  (#req:prop) (#ens:a -> prop)
  ($f:Eff.repr a false (hp_of pre) (fun x -> hp_of (post x)) (fun h -> req) (fun _ x _ -> ens x))
: repr a false pre post (fun _ -> req) (fun _ x _ -> ens x)
  = fun frame -> f frame

let as_steelsel1 (#a:Type)
  (#pre:vprop) (#post:a -> vprop)
  (#req:prop) (#ens:a -> prop)
  ($f:Eff.repr a false (hp_of pre) (fun x -> hp_of (post x)) (fun h -> req) (fun _ x _ -> ens x))
: SteelSel a pre post (fun _ -> req) (fun _ x _ -> ens x)
  = SteelSel?.reflect (as_steelsel0 f)

let as_steelsel (#a:Type)
  (#pre:pre_t) (#post:post_t a)
  (#req:prop) (#ens:a -> prop)
  ($f:unit -> Eff.Steel a (hp_of pre) (fun x -> hp_of (post x)) (fun h -> req) (fun _ x _ -> ens x))
: SteelSel a pre post (fun _ -> req) (fun _ x _ -> ens x)
  = as_steelsel1 (reify (f ()))

let _:squash (hp_of vemp == emp /\ t_of vemp == unit) = reveal_vemp ()

unfold
let vptr_tmp' (#a:Type) (r:ref a) (p:perm) (v:erased a) : vprop' =
  { hp = R.pts_to r p v;
    t = unit;
    sel = fun _ -> ()}
unfold
let vptr_tmp r p v : vprop = VUnit (vptr_tmp' r p v)

val alloc0 (#a:Type0) (x:a) : SteelSel (ref a)
  vemp (fun r -> vptr_tmp r full_perm x)
  (requires fun _ -> True)
  (ensures fun _ r h1 -> True)

let alloc0 #a x = as_steelsel (fun _ -> R.alloc x)

let intro_vptr (#a:Type) (r:ref a) (v:erased a) (m:mem) : Lemma
  (requires interp (hp_of (vptr_tmp r full_perm v)) m)
  (ensures interp (hp_of (vptr r)) m /\ sel_of (vptr r) m == reveal v)
  = Mem.intro_h_exists v (R.pts_to r full_perm) m;
    R.pts_to_witinv r full_perm

let elim_vptr (#a:Type) (r:ref a) (v:erased a) (m:mem) : Lemma
  (requires interp (hp_of (vptr r)) m /\ sel_of (vptr r) m == reveal v)
  (ensures interp (hp_of (vptr_tmp r full_perm v)) m)
  = Mem.elim_h_exists (R.pts_to r full_perm) m;
    R.pts_to_witinv r full_perm

let alloc x =
  let r = alloc0 x in
  extract_info (vptr_tmp r full_perm x) () (~ (R.is_null r))
    (fun m -> R.pts_to_not_null r full_perm x m);
  change_slprop (vptr_tmp r full_perm x) (vptr r) () x (intro_vptr r x);
  r

let free r = change_slprop_2 (vptr r) vemp () intro_emp

val read0 (#a:Type0) (r:ref a) (v:erased a) : SteelSel a
  (vptr_tmp r full_perm v) (fun x -> vptr_tmp r full_perm x)
  (requires fun _ -> True)
  (ensures fun h0 x h1 -> x == reveal v)

let read0 #a r v = as_steelsel (fun _ -> R.read #a #full_perm #v r)

let read (#a:Type0) (r:ref a) : SteelSel a
  (vptr r) (fun _ -> vptr r)
  (requires fun _ -> True)
  (ensures fun h0 x h1 -> h0 (vptr r) == h1 (vptr r) /\ x == h1 (vptr r))
  = let h0 = get() in
    let v = hide (h0 (vptr r)) in
    change_slprop (vptr r) (vptr_tmp r full_perm v) v () (elim_vptr r v);
    let x = read0 r v in
    change_slprop (vptr_tmp r full_perm x) (vptr r) () x (intro_vptr r x);
    x

val write0 (#a:Type0) (v:erased a) (r:ref a) (x:a)
  : SteelSel unit
    (vptr_tmp r full_perm v) (fun _ -> vptr_tmp r full_perm x)
    (fun _ -> True) (fun _ _ _ -> True)

let write0 #a v r x = as_steelsel (fun _ -> R.write #a #v r x)

let write (#a:Type0) (r:ref a) (x:a) : SteelSel unit
  (vptr r) (fun _ -> vptr r)
  (requires fun _ -> True)
  (ensures fun _ _ h1 -> x == h1 (vptr r))
  = let h0 = get() in
    let v = hide (h0 (vptr r)) in
    change_slprop (vptr r) (vptr_tmp r full_perm v) v () (elim_vptr r v);
    write0 v r x;
    change_slprop (vptr_tmp r full_perm x) (vptr r) () x (intro_vptr r x)

let intro_vrefine v p =
  let m = get () in
  let x : Ghost.erased (t_of v) = Ghost.hide (m v) in
  let x' : Ghost.erased (vrefine_t v p) = Ghost.hide (Ghost.reveal x) in
  change_slprop
    v
    (vrefine v p)
    x
    x'
    (fun m ->
      interp_vrefine_hp v p m;
      vrefine_sel_eq v p m
    )

let elim_vrefine v p =
  let m = get () in
  let x : Ghost.erased (vrefine_t v p) = Ghost.hide (m (vrefine v p)) in
  let x' : Ghost.erased (t_of v) = Ghost.hide (Ghost.reveal x) in
  change_slprop
    (vrefine v p)
    v
    x
    x'
    (fun m ->
      interp_vrefine_hp v p m;
      vrefine_sel_eq v p m
    )
