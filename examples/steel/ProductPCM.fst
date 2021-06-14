module ProductPCM

open FStar.PCM

/// Aseem's alternative definition of frame-preserving updates

type frame_preserving_upd (#a:Type u#a) (p:pcm a) (x y:a) =
  v:a{
     p.refine v /\
     compatible p x v
  } ->
  v_new:a{
    p.refine v_new /\
    compatible p y v_new /\
    (forall (frame:a{composable p x frame}).{:pattern composable p x frame}
       composable p y frame /\
       (op p x frame == v ==> op p y frame == v_new))}

/// The alternative definition satisfies 3 nice properties:

(* The identity function is a frame-preserving update *)
val no_op_is_frame_preserving :
  p: pcm 'a -> x: 'a ->
  frame_preserving_upd p x x
let no_op_is_frame_preserving p x = fun v -> v

(* Frame-preserving updates compose, and the composition is just
   function composition *)
val frame_preserving_updates_compose :
  p: pcm 'a -> x: 'a -> y: 'a -> z: 'a ->
  frame_preserving_upd p y z ->
  frame_preserving_upd p x y ->
  frame_preserving_upd p x z
let frame_preserving_updates_compose p x y z f g = fun v -> f (g v)

val compatible_subframe :
  p: pcm 'a -> x: 'a -> y: 'a {composable p x y} -> z: 'a ->
  Lemma (requires (compatible p (op p x y) z)) (ensures (compatible p x z))
let compatible_subframe p x y z =
  compatible_elim p (op p x y) z (compatible p x z) (fun frame ->
    p.comm x y;
    p.assoc frame y x)

(* A frame-preserving update from x to y is also a frame-preserving
   update from (x `op` subframe) to (y `op` subframe), for any subframe *)
open FStar.Classical
val frame_preserving_subframe : 
  p: pcm 'a -> x: 'a -> y: 'a -> subframe: 'a{composable p x subframe /\ composable p y subframe} ->
  frame_preserving_upd p x y ->
  frame_preserving_upd p (op p x subframe) (op p y subframe)
let frame_preserving_subframe #a p x y subframe f v =
  compatible_subframe p x subframe v;
  let w = f v in
  let aux (frame: a{composable p (op p x subframe) frame}):
    Lemma (composable p (op p y subframe) frame /\
           (op p (op p x subframe) frame == v ==> op p (op p y subframe) frame == w))
           [SMTPat (composable p (op p y subframe) frame)]
  = p.assoc_r x subframe frame;
    assert (composable p x (op p subframe frame));
    assert (composable p y (op p subframe frame));
    p.assoc y subframe frame
  in
  let lframe : squash (compatible p (op p x subframe) v) = () in
  exists_elim (compatible p (op p y subframe) w) lframe (fun frame -> 
    aux frame;
    assert (op p frame (op p x subframe) == v);
    p.comm frame (op p x subframe);
    assert (op p (op p y subframe) frame == w);
    p.comm (op p y subframe) frame);
  w

/// We can define a PCM for structs with two fields {a; b} by defining
/// a PCM for tuples (a & b) in terms of (potentially user-defined)
/// PCMs for a and b.

val tuple_comp : pcm 'a -> pcm 'b -> 'a & 'b -> 'a & 'b -> prop
let tuple_comp p q (xa, xb) (ya, yb) = composable p xa ya /\ composable q xb yb

val tuple_op : p: pcm 'a -> q: pcm 'b -> x:('a & 'b) -> y:('a & 'b){tuple_comp p q x y} -> 'a & 'b
let tuple_op p q (xa, xb) (ya, yb) = (op p xa ya, op q xb yb)

val tuple_pcm : pcm 'a -> pcm 'b -> pcm ('a & 'b)
let tuple_pcm #a #b p q = {
  p = {composable = tuple_comp p q; op = tuple_op p q; one = (p.p.one, q.p.one)};
  comm = (fun (xa, xb) (ya, yb) -> p.comm xa ya; q.comm xb yb);
  assoc = (fun (xa, xb) (ya, yb) (za, zb) -> p.assoc xa ya za; q.assoc xb yb zb);
  assoc_r = (fun (xa, xb) (ya, yb) (za, zb) -> p.assoc_r xa ya za; q.assoc_r xb yb zb);
  is_unit = (fun (xa, xb) -> p.is_unit xa; q.is_unit xb);
  refine = (fun (xa, xb) -> p.refine xa /\ q.refine xb)
}

open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect

module T = FStar.Tactics

/// With the alternative definition of frame-preserving updates and
/// compat_unit_unique, we can define frame-preserving updates for a
/// tuple PCM from frame-preserving updates on its components:

val compatible_tuple_l :
  p: pcm 'a -> q: pcm 'b ->
  x: 'a -> v: 'a -> y: 'b -> w: 'b ->
  Lemma 
    (requires compatible p x v /\ compatible q y w)
    (ensures compatible (tuple_pcm p q) (x, y) (v, w))
let compatible_tuple_l p q x v y w =
  let pq = tuple_pcm p q in
  let aux frame_x frame_y :
    Lemma 
      (requires composable pq (x, y) (frame_x, frame_y) /\
                op pq (frame_x, frame_y) (x, y) == (v, w))
      (ensures compatible pq (x, y) (v, w))
      [SMTPat (composable p x frame_x); SMTPat (composable q y frame_y)] = ()
  in ()

val upd_fst :
  p: pcm 'a -> q: pcm 'b ->
  x: 'a -> y: 'b -> x': 'a ->
  frame_preserving_upd p x x' ->
  frame_preserving_upd (tuple_pcm p q) (x, y) (x', y)
let upd_fst #a #b p q x y x' f (va, vb) =
  let wa = f va in
  let pq = tuple_pcm p q in
  compatible_tuple_l p q x' wa y vb;
  let aux (frame: (a & b) {composable pq (x, y) frame}):
    Lemma (composable pq (x', y) frame /\
           (op pq (x, y) frame == (va, vb) ==> op pq (x', y) frame == (wa, vb)))
    [SMTPat (composable pq (x, y) frame)] = ()
  in (wa, vb)

/// If no custom PCM is needed, p and q can be instantiated with an all-or-none PCM:

val opt_comp : option 'a -> option 'a -> prop
let opt_comp x y = match x, y with None, _ | _, None -> True | _ -> False

val opt_op : x:option 'a -> y:option 'a {opt_comp x y} -> option 'a
let opt_op x y = match x, y with None, z | z, None -> z

val opt_pcm : pcm (option 'a)
let opt_pcm #a = {
  p = {composable = opt_comp; op = opt_op; one = None};
  comm = (fun _ _ -> ());
  assoc = (fun _ _ _ -> ());
  assoc_r = (fun _ _ _ -> ());
  is_unit = (fun _ -> ());
  refine = (fun _ -> True);
}

/// We can generalize to 'a-ary products (k:'a -> f k), given a PCM for each k:

open FStar.FunctionalExtensionality

val prod_comp :
  #f:('a -> Type) -> (k:'a -> pcm (f k)) ->
  restricted_t 'a f -> restricted_t 'a f -> prop
let prod_comp p x y = forall k. composable (p k) (x k) (y k)

val prod_op :
  #f:('a -> Type) -> p:(k:'a -> pcm (f k)) -> 
  x:restricted_t 'a f -> y: restricted_t 'a f {prod_comp p x y} -> 
  restricted_t 'a f
let prod_op #a p x y = on_domain a (fun k -> op (p k) (x k) (y k))

val prod_one : #f:('a -> Type) -> (k:'a -> pcm (f k)) -> restricted_t 'a f
let prod_one #a p = on_domain a (fun k -> (p k).p.one)

val ext :
  #b: ('a -> Type) -> f: restricted_t 'a b -> g: restricted_t 'a b -> 
  (x: 'a -> Lemma (f x == g x)) ->
  Lemma (ensures (f == g))
let ext #a #b f g fg =
  extensionality a b f g;
  forall_intro fg

val prod_comm :
  #f:('a -> Type) -> p:(k:'a -> pcm (f k)) ->
  x:restricted_t 'a f ->
  y:restricted_t 'a f {prod_comp p x y} ->
  Lemma (prod_op p x y == prod_op p y x)
let prod_comm p x y =
  ext (prod_op p x y) (prod_op p y x) (fun k -> (p k).comm (x k) (y k))

val prod_assoc :
  #f:('a -> Type) -> p:(k:'a -> pcm (f k)) ->
  x:restricted_t 'a f -> y:restricted_t 'a f ->
  z:restricted_t 'a f {prod_comp p y z /\ prod_comp p x (prod_op p y z)} ->
  Lemma (prod_comp p x y /\
         prod_comp p (prod_op p x y) z /\
         prod_op p x (prod_op p y z) == prod_op p (prod_op p x y) z)
let prod_assoc p x y z =
  let aux k :
    Lemma (composable (p k) (x k) (y k) /\
           composable (p k) (op (p k) (x k) (y k)) (z k)) 
    [SMTPat (p k)] = (p k).assoc (x k) (y k) (z k)
  in
  ext (prod_op p x (prod_op p y z)) (prod_op p (prod_op p x y) z)
    (fun k -> (p k).assoc (x k) (y k) (z k))

val prod_assoc_r :
  #f:('a -> Type) -> p:(k:'a -> pcm (f k)) ->
  x:restricted_t 'a f -> y:restricted_t 'a f ->
  z:restricted_t 'a f {prod_comp p x y /\ prod_comp p (prod_op p x y) z} ->
  Lemma (prod_comp p y z /\
         prod_comp p x (prod_op p y z) /\
         prod_op p x (prod_op p y z) == prod_op p (prod_op p x y) z)
let prod_assoc_r #a p x y z =
  let aux k : 
    Lemma (composable (p k) (y k) (z k) /\
           composable (p k) (x k) (op (p k) (y k) (z k)))
    [SMTPat (p k)] = (p k).assoc_r (x k) (y k) (z k)
  in
  ext (prod_op p x (prod_op p y z)) (prod_op p (prod_op p x y) z)
    (fun k -> (p k).assoc (x k) (y k) (z k))

val prod_is_unit :
  #f:('a -> Type) -> p:(k:'a -> pcm (f k)) ->
  x:restricted_t 'a f ->
  Lemma (prod_comp p x (prod_one p) /\
         prod_op p x (prod_one p) == x)
let prod_is_unit #a p x =
  let is_unit k :
    Lemma (composable (p k) (x k) (prod_one p k))
    [SMTPat (p k)] = (p k).is_unit (x k)
  in ext (prod_op p x (prod_one p)) x (fun k -> (p k).is_unit (x k))

val prod_refine :
  #f:('a -> Type) -> (k:'a -> pcm (f k)) ->
  x: restricted_t 'a f -> prop
let prod_refine p x = forall k. (p k).refine (x k)

val prod_pcm : #f:('a -> Type) -> (k:'a -> pcm (f k)) -> pcm (restricted_t 'a f)
let prod_pcm #a #f p = {
  p = {composable = prod_comp p; op = prod_op p; one = prod_one p};
  comm = prod_comm p;
  assoc = prod_assoc p;
  assoc_r = prod_assoc_r p;
  is_unit = prod_is_unit p;
  refine = prod_refine p
}

/// Now, we can define frame-preserving updates of all components at once:

val update :
  #a:eqtype -> #f:(a -> Type) -> k:a -> x': f k ->
  restricted_t a f -> restricted_t a f
let update #a k x' f = on_domain a (fun k' -> if k = k' then x' else f k')

val prod_upd :
  #a:eqtype -> #f:(a -> Type) -> p:(k:a -> pcm (f k)) ->
  k:a -> xs: restricted_t a f -> x: f k -> x': f k ->
  frame_preserving_upd (p k) x x' ->
  frame_preserving_upd (prod_pcm p) xs (update k x' xs)

/// Similarly, given a PCM for each z:a, we can model a-ary unions with an PCM for option (x:a & f x), where
/// - None is the unit of the PCM
/// - Some (x, y) is a union with tag x and content y

let union (a:Type) (f:a -> Type) (p:(x:a -> pcm (f x))) = option (x:a & f x)

val union_comp :
  f:('a -> Type) -> p:(z:'a -> pcm (f z)) ->
  symrel (union 'a f p)
let union_comp f p x y = match x, y with
  | None, z | z, None -> True
  | Some (|xa, xb|), Some (|ya, yb|) -> xa == ya /\ composable (p xa) xb yb

val union_op :
  f:('a -> Type) -> p:(z:'a -> pcm (f z)) ->
  x:union 'a f p -> y:union 'a f p {union_comp f p x y} -> union 'a f p
let union_op f p x y = match x, y with
  | None, z | z, None -> z
  | Some (|xa, xb|), Some (|ya, yb|) -> Some (|xa, (p xa).p.op xb yb|)

val union_pcm : f:('a -> Type) -> p:(x: 'a -> pcm (f x)) -> pcm (union 'a f p)
let union_pcm #a f p = FStar.PCM.({
  p = {composable = union_comp f p; op = union_op f p; one = None};
  comm = (fun x y -> match x, y with
    | None, _ | _, None -> ()
    | Some (|xa, xb|), Some (|ya, yb|) -> (p xa).comm xb yb);
  assoc = (fun x y z -> match x, y, z with
    | None, _, _ | _, _, None | _, None, _ -> ()
    | Some (|xa, xb|), Some (|ya, yb|), Some (|za, zb|) -> (p xa).assoc xb yb zb);
  assoc_r = (fun x y z -> match x, y, z with
    | None, _, _ | _, _, None | _, None, _ -> ()
    | Some (|xa, xb|), Some (|ya, yb|), Some (|za, zb|) -> (p xa).assoc_r xb yb zb);
  is_unit = (fun _ -> ());
  refine = (fun x -> match x with None -> True | Some (|xa, xb|) -> (p xa).refine xb)
})

(*
// TODO
// move 2d point along x
// move 2d point along y
// given a function "incrementX" and "incrementY"; write a function that calls it in a loop

// union examples
// 2d & 3d point
// rgb / hsv

// next examples:
//   swap 2 3d points with a helper function
//   union where discrimnant is not just a tag, but some predicate

// { f field_x = Full .. }
// { p `pts_to` f } 
//   addr_of p field_x
// { fun q -> (p `pts_to` f \ x) `star` (q `pts_to` x) }
// 
// let q = addr_of p field_x
*)
