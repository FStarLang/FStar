module Steel.SelectorEffect

open Steel.Memory

#set-options "--warn_error -330"

type projection' (a:Type) (fp:hprop u#1) = hmem fp -> GTot a
// TODO: Add value_depends_only_on restriction
type projection (a:Type) (fp:hprop u#1) = projection' a fp

noeq
type viewable = {
  fp: hprop u#1;
  a: Type0;
  sel:projection a fp;
}

noeq
type viewables =
| VUnit: viewable -> viewables
| VStar: viewables -> viewables -> viewables

let rec t_of (v:viewables) = match v with
  | VUnit v -> v.a
  | VStar v1 v2 -> t_of v1 * t_of v2

let rec fp_of (v:viewables) = match v with
  | VUnit v -> v.fp
  | VStar v1 v2 -> fp_of v1 `star` fp_of v2

let rec sel_of (v:viewables) : projection (t_of v) (fp_of v)  = admit()

let selector (r:viewables) = (r0:viewables) -> GTot (t_of r0)

let mk_selector (h:mem) (fp:viewables) =
  fun (r0:viewables) ->
    assume (interp (fp_of r0) h);
    (sel_of r0) h

type pre_t = viewables
type post_t (a:Type) = a -> viewables
type req_t (pre:pre_t) = selector pre -> GTot prop
type ens_t (pre:pre_t) (a:Type) (post:post_t a) =
  selector pre -> x:a -> selector (post x) -> GTot prop

type repr (a:Type) (pre:pre_t) (post:post_t a) (req:req_t pre) (ens:ens_t pre a post)
  = Steel.FramingEffect.repr a (fp_of pre) (fun x -> fp_of (post x))
         // TODO: Do pre/post correctly with mk_selector
         // Requires proving depend_only_on
         (fun _ -> True)
         (fun _ _ _ -> True)

assume val star (p q:viewables) : viewables

assume val sl_implies (p q:viewables) : Type0

assume val sl_implies_reflexive (p:viewables)
: Lemma (p `sl_implies` p)
  [SMTPat (p `sl_implies` p)]

irreducible let framing_implicit_sel : unit = ()

unfold
let return_req (p:viewables) : req_t p = fun _ -> True

unfold
let return_ens (a:Type) (x:a) (p:a -> viewables) : ens_t (p x) a p = fun h0 r h1 -> r == x /\ h0 == h1

let return (a:Type) (x:a) (#[@@ framing_implicit_sel] p:post_t a)
  : repr a (p x) p (return_req (p x)) (return_ens a x p)
  = fun _ -> x

let can_be_split (t1 t2:pre_t) = t1 `sl_implies` t2

let can_be_split_forall (#a:Type) (t1 t2:post_t a) =
  forall (x:a). t1 x `sl_implies` t2 x

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
  (forall (x:a) (m1:selector (post_f x)). ens_f m0 x m1 ==> (req_g x) m1)

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
  (exists (x:a) (m1:selector (post_f x)). ens_f m0 x m1 /\ (ens_g x) m1 y m2)

let bind (a:Type) (b:Type)
  // (pre_f:pre_t) (post_f:post_t a)
  (#[@@ framing_implicit_sel] pre_f:pre_t) (#[@@ framing_implicit_sel] post_f:post_t a)
  (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
  // (pre_g:a -> pre_t) (post_g:post_t b)
  (#[@@ framing_implicit_sel] pre_g:a -> pre_t) (#[@@ framing_implicit_sel] post_g:post_t b)
  (req_g:(x:a -> req_t (pre_g x))) (ens_g:(x:a -> ens_t (pre_g x) b post_g))
  // (p:squash (post_f == pre_g))
  (#[@@ framing_implicit_sel] p:squash (can_be_split_forall post_f pre_g))
  (f:repr a pre_f post_f req_f ens_f)
  (g:(x:a -> repr b (pre_g x) post_g (req_g x) (ens_g x)))
: repr b
    pre_f
    post_g
    (bind_req req_f ens_f req_g p)
    (bind_ens req_f ens_f ens_g p)
  = admit()
    // fun _ ->
    // let x = f () in
    // (g x) ()

// Currently using equalitis on pre_g/pre_f and post_f/post_g
// TODO: This should be can_be_splits
unfold
let subcomp_pre (#a:Type)
  (#pre_f:pre_t) (#post_f:post_t a) (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
  (#pre_g:pre_t) (#post_g:post_t a) (req_g:req_t pre_g) (ens_g:ens_t pre_g a post_g)
  (_:squash (can_be_split pre_g pre_f))
  (_:squash (can_be_split_forall post_f post_g))
: pure_pre
= (forall (m0:selector pre_g). req_g m0 ==> req_f m0) /\
  (forall (m0:selector pre_g) (x:a) (m1:selector (post_f x)). ens_f m0 x m1 ==> ens_g m0 x m1)

let delay (p:Type0) : Type0 = p
let annot_sub_post (p:Type0) : Type0 = p

let subcomp (a:Type)
  (#[@@ framing_implicit_sel] pre_f:pre_t) (#[@@ framing_implicit_sel] post_f:post_t a)
  (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
  (#[@@ framing_implicit_sel] pre_g:pre_t) (#[@@ framing_implicit_sel] post_g:post_t a)
  (req_g:req_t pre_g) (ens_g:ens_t pre_g a post_g)
  (#[@@ framing_implicit_sel] p1:squash (delay (can_be_split pre_g pre_f)))
  (#[@@ framing_implicit_sel] p2:squash (annot_sub_post (can_be_split_forall post_f post_g)))
  (f:repr a pre_f post_f req_f ens_f)
: Pure (repr a pre_g post_g req_g ens_g)
  (requires subcomp_pre req_f ens_f req_g ens_g p1 p2)
  (ensures fun _ -> True)
= admit() // f


unfold
let if_then_else_req (#pre:pre_t)
  (req_then:req_t pre) (req_else:req_t pre)
  (p:Type0)
: req_t pre
= fun h -> (p ==> req_then h) /\ ((~ p) ==> req_else h)

unfold
let if_then_else_ens (#a:Type) (#pre:pre_t) (#post:post_t a)
  (ens_then:ens_t pre a post) (ens_else:ens_t pre a post)
  (p:Type0)
: ens_t pre a post
= fun h0 x h1 -> (p ==> ens_then h0 x h1) /\ ((~ p) ==> ens_else h0 x h1)

let if_then_else (a:Type)
  (pre:pre_t) (post:post_t a)
  (req_then:req_t pre) (ens_then:ens_t pre a post)
  (req_else:req_t pre) (ens_else:ens_t pre a post)
  (f:repr a pre post req_then ens_then)
  (g:repr a pre post req_else ens_else)
  (p:Type0)
: Type
= repr a pre post
    (if_then_else_req req_then req_else p)
    (if_then_else_ens ens_then ens_else p)

reifiable reflectable
layered_effect {
  SteelF_Sel: a:Type -> pre:pre_t -> post:post_t a -> req_t pre -> ens_t pre a post -> Effect
  with repr = repr;
       return = return;
       bind = bind;
       subcomp = subcomp;
       if_then_else = if_then_else
}

new_effect Steel_Sel = SteelF_Sel

unfold
let bind_steel_steel_req (#a:Type)
  (#pre_f:pre_t) (#post_f:post_t a)
  (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
  (#pre_g:a -> pre_t)
  (req_g:(x:a -> req_t (pre_g x)))
  (frame_f:viewables) (frame_g:viewables)
  (_:squash (can_be_split_forall (fun x -> post_f x `star` frame_f) (fun x -> pre_g x `star` frame_g)))
: req_t (pre_f `star` frame_f)
= fun m0 ->
  req_f m0 /\
  (forall (x:a) (m1:selector (post_f x `star` frame_f)). ens_f m0 x m1 ==> (req_g x) m1)

unfold
let bind_steel_steel_ens (#a:Type) (#b:Type)
  (#pre_f:pre_t) (#post_f:post_t a)
  (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
  (#pre_g:a -> pre_t) (#post_g:post_t b)
  (ens_g:(x:a -> ens_t (pre_g x) b post_g))
  (frame_f:viewables) (frame_g:viewables)
  (_:squash (can_be_split_forall (fun x -> post_f x `star` frame_f) (fun x -> pre_g x `star` frame_g)))
: ens_t (pre_f `star` frame_f) b (fun y -> post_g y `star` frame_g)
= fun m0 y m2 ->
  req_f m0 /\
  (exists (x:a) (m1:selector (post_f x `star` frame_f)). ens_f m0 x m1 /\ (ens_g x) m1 y m2)

let bind_steel_steel (a:Type) (b:Type)
  (#[@@ framing_implicit_sel] pre_f:pre_t) (#[@@ framing_implicit_sel] post_f:post_t a)
  (#[@@ framing_implicit_sel] req_f:req_t pre_f) (#[@@ framing_implicit_sel] ens_f:ens_t pre_f a post_f)
  (#[@@ framing_implicit_sel] pre_g:a -> pre_t) (#[@@ framing_implicit_sel] post_g:post_t b)
  (#[@@ framing_implicit_sel] req_g:(x:a -> req_t (pre_g x))) (#[@@ framing_implicit_sel] ens_g:(x:a -> ens_t (pre_g x) b post_g))
  (#[@@ framing_implicit_sel] frame_f:viewables) (#[@@ framing_implicit_sel] frame_g:viewables)
  (#[@@ framing_implicit_sel] p:squash (can_be_split_forall
    (fun x -> post_f x `star` frame_f) (fun x -> pre_g x `star` frame_g)))
  (f:repr a pre_f post_f req_f ens_f)
  (g:(x:a -> repr b (pre_g x) post_g (req_g x) (ens_g x)))
: repr b
    (pre_f `star` frame_f)
    (fun y -> post_g y `star` frame_g)
    (bind_steel_steel_req req_f ens_f req_g frame_f frame_g p)
    (bind_steel_steel_ens req_f ens_f ens_g frame_f frame_g p)
= admit()
// fun _ ->
//   let x = frame_aux f frame_f () in
//   frame_aux (g x) frame_g ()


(*
 * Note that the output is a framed computation, hence SteelF
 *)

polymonadic_bind (Steel_Sel, Steel_Sel) |> SteelF_Sel = bind_steel_steel


(*
 * Steel, SteelF: frame the first computation
 *)

unfold
let bind_steel_steelf_req (#a:Type)
  (#pre_f:pre_t) (#post_f:post_t a)
  (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
  (#pre_g:a -> pre_t)
  (req_g:(x:a -> req_t (pre_g x)))
  (frame_f:viewables)
  (_:squash (can_be_split_forall (fun x -> post_f x `star` frame_f) pre_g))
: req_t (pre_f `star` frame_f)
= fun m0 ->
  req_f m0 /\
  (forall (x:a) (m1:selector (post_f x `star` frame_f)). ens_f m0 x m1 ==> (req_g x) m1)

unfold
let bind_steel_steelf_ens (#a:Type) (#b:Type)
  (#pre_f:pre_t) (#post_f:post_t a)
  (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
  (#pre_g:a -> pre_t) (#post_g:post_t b)
  (ens_g:(x:a -> ens_t (pre_g x) b post_g))
  (frame_f:viewables)
  (_:squash (can_be_split_forall (fun x -> post_f x `star` frame_f) pre_g))
: ens_t (pre_f `star` frame_f) b post_g
= fun m0 y m2 ->
  req_f m0 /\
  (exists (x:a) (m1:selector (post_f x `star` frame_f)). ens_f m0 x m1 /\ (ens_g x) m1 y m2)

let bind_steel_steelf (a:Type) (b:Type)
  (#[@@ framing_implicit_sel] pre_f:pre_t) (#[@@ framing_implicit_sel] post_f:post_t a)
  (#[@@ framing_implicit_sel] req_f:req_t pre_f) (#[@@ framing_implicit_sel] ens_f:ens_t pre_f a post_f)
  (#[@@ framing_implicit_sel] pre_g:a -> pre_t) (#[@@ framing_implicit_sel] post_g:post_t b)
  (#[@@ framing_implicit_sel] req_g:(x:a -> req_t (pre_g x))) (#[@@ framing_implicit_sel] ens_g:(x:a -> ens_t (pre_g x) b post_g))
  (#[@@ framing_implicit_sel] frame_f:viewables)
  (#[@@ framing_implicit_sel] p:squash (can_be_split_forall (fun x -> post_f x `star` frame_f) pre_g))
  (f:repr a pre_f post_f req_f ens_f)
  (g:(x:a -> repr b (pre_g x) post_g (req_g x) (ens_g x)))
: repr b
    (pre_f `star` frame_f)
    post_g
    (bind_steel_steelf_req req_f ens_f req_g frame_f p)
    (bind_steel_steelf_ens req_f ens_f ens_g frame_f p)
= admit()
  // fun _ ->
  // let x = frame_aux f frame_f () in
  // (g x) ()


polymonadic_bind (Steel_Sel, SteelF_Sel) |> SteelF_Sel = bind_steel_steelf


(*
 * SteelF, Steel: frame the second computation
 *)

unfold
let bind_steelf_steel_req (#a:Type)
  (#pre_f:pre_t) (#post_f:post_t a)
  (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
  (#pre_g:a -> pre_t)
  (req_g:(x:a -> req_t (pre_g x)))
  (frame_g:viewables)
  (_:squash (can_be_split_forall post_f (fun x -> pre_g x `star` frame_g)))
: req_t pre_f
= fun m0 ->
  req_f m0 /\
  (forall (x:a) (m1:selector (post_f x)). ens_f m0 x m1 ==> (req_g x) m1)

unfold
let bind_steelf_steel_ens (#a:Type) (#b:Type)
  (#pre_f:pre_t) (#post_f:post_t a)
  (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
  (#pre_g:a -> pre_t) (#post_g:post_t b)
  (ens_g:(x:a -> ens_t (pre_g x) b post_g))
  (frame_g:viewables)
  (_:squash (can_be_split_forall post_f (fun x -> pre_g x `star` frame_g)))
: ens_t pre_f b (fun y -> post_g y `star` frame_g)
= fun m0 y m2 ->
  req_f m0 /\
  (exists (x:a) (m1:selector (post_f x)). ens_f m0 x m1 /\ (ens_g x) m1 y m2)

let bind_steelf_steel (a:Type) (b:Type)
  (#[@@ framing_implicit_sel] pre_f:pre_t) (#[@@ framing_implicit_sel] post_f:post_t a)
  (#[@@ framing_implicit_sel] req_f:req_t pre_f) (#[@@ framing_implicit_sel] ens_f:ens_t pre_f a post_f)
  (#[@@ framing_implicit_sel] pre_g:a -> pre_t) (#[@@ framing_implicit_sel] post_g:post_t b)
  (#[@@ framing_implicit_sel] req_g:(x:a -> req_t (pre_g x))) (#[@@ framing_implicit_sel] ens_g:(x:a -> ens_t (pre_g x) b post_g))
  (#[@@ framing_implicit_sel] frame_g:viewables)
  (#[@@ framing_implicit_sel] p:squash (can_be_split_forall post_f (fun x -> pre_g x `star` frame_g)))
  (f:repr a pre_f post_f req_f ens_f)
  (g:(x:a -> repr b (pre_g x) post_g (req_g x) (ens_g x)))
: repr b
    pre_f
    (fun y -> post_g y `star` frame_g)
    (bind_steelf_steel_req req_f ens_f req_g frame_g p)
    (bind_steelf_steel_ens req_f ens_f ens_g frame_g p)
= admit()
  // fun _ ->
  // let x = f () in
  // frame_aux (g x) frame_g ()


polymonadic_bind (SteelF_Sel, Steel_Sel) |> SteelF_Sel = bind_steelf_steel



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


let bind_pure_steel_ (a:Type) (b:Type)
  (wp:pure_wp a)
  // (pre:pre_t) (post:post_t b)
  (#[@@ framing_implicit_sel] pre:pre_t) (#[@@ framing_implicit_sel] post:post_t b)
  (#[@@ framing_implicit_sel] req:a -> req_t pre)
  (#[@@ framing_implicit_sel] ens:a -> ens_t pre b post)
  (f:unit -> PURE a wp) (g:(x:a -> repr b pre post (req x) (ens x)))
: repr b
    pre
    post
    (bind_pure_steel__req wp req)
    (bind_pure_steel__ens wp ens)
= admit()

polymonadic_bind (PURE, Steel_Sel) |> Steel_Sel = bind_pure_steel_

polymonadic_bind (PURE, SteelF_Sel) |> SteelF_Sel = bind_pure_steel_

polymonadic_subcomp SteelF_Sel <: Steel_Sel = subcomp
