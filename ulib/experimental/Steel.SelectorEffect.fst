module Steel.SelectorEffect

open Steel.Memory
open Steel.FramingEffect

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
  = repr a (fp_of pre) (fun x -> fp_of (post x))
         // TODO: Do pre/post correctly with mk_selector
         // Requires proving depend_only_on
         (fun _ -> True)
         (fun _ _ _ -> True)

irreducible let framing_implicit_sel : unit = ()

unfold
let return_req (p:viewables) : req_t p = fun _ -> True

unfold
let return_ens (a:Type) (x:a) (p:a -> viewables) : ens_t (p x) a p = fun _ r _ -> r == x

let return (a:Type) (x:a) (p:post_t a) // (#[@@ framing_implicit_sel] p:post_t a)
  : repr a (p x) p (return_req (p x)) (return_ens a x p)
  = fun _ -> x

// Use equalities for now on post_f/pre_g
// TODO: Should be a can_be_split_into_forall
unfold
let bind_req (#a:Type)
  (#pre_f:pre_t) (#post_f:post_t a)
  (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
  (#pre_g:a -> pre_t)
  (req_g:(x:a -> req_t (pre_g x)))
  (_:squash (post_f == pre_g))
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
  (_:squash (post_f == pre_g))
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
  (#[@@ framing_implicit_sel] p:squash (post_f == pre_g))
  (f:repr a pre_f post_f req_f ens_f)
  (g:(x:a -> repr b (pre_g x) post_g (req_g x) (ens_g x)))
: repr b
    pre_f
    post_g
    (bind_req req_f ens_f req_g p)
    (bind_ens req_f ens_f ens_g p)
  = fun _ ->
    let x = f () in
    (g x) ()

// Currently using equalitis on pre_g/pre_f and post_f/post_g
// TODO: This should be can_be_splits
unfold
let subcomp_pre (#a:Type)
  (#pre_f:pre_t) (#post_f:post_t a) (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
  (#pre_g:pre_t) (#post_g:post_t a) (req_g:req_t pre_g) (ens_g:ens_t pre_g a post_g)
  (_:squash (pre_g == pre_f))
  (_:squash (post_f == post_g))
: pure_pre
= (forall (m0:selector pre_g). req_g m0 ==> req_f m0) /\
  (forall (m0:selector pre_g) (x:a) (m1:selector (post_f x)). ens_f m0 x m1 ==> ens_g m0 x m1)


let subcomp (a:Type)
  (#[@@ framing_implicit_sel] pre_f:pre_t) (#[@@ framing_implicit_sel] post_f:post_t a)
  (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
  (#[@@ framing_implicit_sel] pre_g:pre_t) (#[@@ framing_implicit_sel] post_g:post_t a)
  (req_g:req_t pre_g) (ens_g:ens_t pre_g a post_g)
  (#[@@ framing_implicit_sel] p1: squash (pre_g == pre_f))
  (#[@@ framing_implicit_sel] p2: squash (post_f == post_g))
  (f:repr a pre_f post_f req_f ens_f)
: Pure (repr a pre_g post_g req_g ens_g)
  (requires subcomp_pre req_f ens_f req_g ens_g p1 p2)
  (ensures fun _ -> True)
= f


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
  Steel_Sel: a:Type -> pre:pre_t -> post:post_t a -> req_t pre -> ens_t pre a post -> Effect
  with repr = repr;
       return = return;
       bind = bind;
       subcomp = subcomp;
       if_then_else = if_then_else
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


let bind_pure_steel_ (a:Type) (b:Type)
  (wp:pure_wp a)
  // (pre:pre_t) (post:post_t b)
  (#[@@ framing_implicit_sel] pre:pre_t) (#[@@ framing_implicit_sel] post:post_t b)
  (req:a -> req_t pre) (ens:a -> ens_t pre b post)
  (f:unit -> PURE a wp) (g:(x:a -> repr b pre post (req x) (ens x)))
: repr b
    pre
    post
    (bind_pure_steel__req wp req)
    (bind_pure_steel__ens wp ens)
= admit()

polymonadic_bind (PURE, Steel_Sel) |> Steel_Sel = bind_pure_steel_
