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

// val full : pcm' 'a -> 'a -> prop
// let full #a p x = forall (frame:a{p.composable frame x}). p.op frame x == x

(* This product construction needs some additional assumptions in order to work: *)
noeq type refined_pcm a = {
  u: pcm a;
  (* The unit is the unique "least element" of the preorder defined by
     [compatible]. (i.e., nothing can be "inside of" or "have less
     information than" the unit of the PCM) *)
  compat_unit_unique : x:a ->
    Lemma (compatible u x u.p.one ==> x == u.p.one);
// (* refine says that an element is either unit or a full value *)
// refine_unit_or_full : x:a ->
//   Lemma (u.refine x == (x == u.p.one \/ full u.p x));
}
  
val tuple_pcm : refined_pcm 'a -> refined_pcm 'b -> refined_pcm ('a & 'b)
let tuple_pcm #a #b p q =
  let p' = FStar.PCM.({
    composable = tuple_comp p.u q.u;
    op = tuple_op p.u q.u;
    one = (p.u.p.one, q.u.p.one)
  }) in
  let u = FStar.PCM.({
    p = p';
    comm = (fun (xa, xb) (ya, yb) -> p.u.comm xa ya; q.u.comm xb yb);
    assoc = (fun (xa, xb) (ya, yb) (za, zb) -> p.u.assoc xa ya za; q.u.assoc xb yb zb);
    assoc_r = (fun (xa, xb) (ya, yb) (za, zb) -> p.u.assoc_r xa ya za; q.u.assoc_r xb yb zb);
    is_unit = (fun (xa, xb) -> p.u.is_unit xa; q.u.is_unit xb);
    refine = (fun (xa, xb) -> (xa, xb) == p'.one \/ (p.u.refine xa /\ q.u.refine xb))
  }) in {
    u = u;
    compat_unit_unique = (fun (xa, xb) -> p.compat_unit_unique xa; q.compat_unit_unique xb)
  }

open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect

module T = FStar.Tactics

/// With the alternative definition of frame-preserving updates and
/// compat_unit_unique, we can define frame-preserving updates for a
/// tuple PCM from frame-preserving updates on its components:

val compatible_tuple_l :
  p: refined_pcm 'a -> q: refined_pcm 'b ->
  x: 'a -> v: 'a -> y: 'b -> w: 'b ->
  Lemma 
    (requires compatible p.u x v /\ compatible q.u y w)
    (ensures compatible (tuple_pcm p q).u (x, y) (v, w))
let compatible_tuple_l p q x v y w =
  let pqu = (tuple_pcm p q).u in
  let aux frame_x frame_y :
    Lemma 
      (requires composable pqu (x, y) (frame_x, frame_y) /\
                op pqu (frame_x, frame_y) (x, y) == (v, w))
      (ensures compatible pqu (x, y) (v, w))
      [SMTPat (composable p.u x frame_x); SMTPat (composable q.u y frame_y)] =
    ()
  in ()

val upd_fst :
  p: refined_pcm 'a -> q: refined_pcm 'b ->
  x: 'a {~ (x == p.u.p.one)} -> y: 'b -> x': 'a ->
  frame_preserving_upd p.u x x' ->
  frame_preserving_upd (tuple_pcm p q).u (x, y) (x', y)
let upd_fst #a #b p q x y x' f (va, vb) =
  p.compat_unit_unique x;
  let wa = f va in
  let pqu = (tuple_pcm p q).u in
  compatible_tuple_l p q x' wa y vb;
  let lemma (frame: (a & b) {composable pqu (x, y) frame}):
    Lemma (composable pqu (x', y) frame /\
           (op pqu (x, y) frame == (va, vb) ==> op pqu (x', y) frame == (wa, vb)))
    [SMTPat (composable pqu (x, y) frame)] = ()
  in (wa, vb)

(*
val upd_fst_0 :
  p: refined_pcm 'a -> q: refined_pcm 'b ->
  r: ref ('a & 'b) (tuple_pcm p q).u ->
  x: Ghost.erased 'a {~ (Ghost.reveal x == p.u.p.one)} -> y: Ghost.erased 'b -> x': 'a ->
  frame_preserving_upd p.u x x' ->
  frame_preserving_upd (tuple_pcm p q).u (Ghost.reveal x, Ghost.reveal y) (x', Ghost.reveal y)
let upd_fst_0 p q r x y x' upd_x (vx, vy) =
  assume (compatible (tuple_pcm p q).u (x', Ghost.reveal y) (upd_x vx, vy));
  // Since x != 1 and compatible x vx, vx != 1 by compat_unit_unique.
  assert (compatible p.u (Ghost.reveal x) vx);
  p.compat_unit_unique (Ghost.reveal x);
  assert (~ (vx == p.u.p.one));
  // Thus, if refine (vx, vy), vx and vy must be full values.
  assert ((tuple_pcm p q).u.refine (vx, vy) ==> full (tuple_pcm p q).u.p (vx, vy));
  full_tup p q vx vy;
  // A frame-preserving update sends full values to full values, so (upd_x vx, vy) is full too.
  assume ((tuple_pcm p q).u.refine (vx, vy) ==> full q.u.p vy); (* TODO why doesn't this work? *)
  assume ((tuple_pcm p q).u.refine (vx, vy) ==> full p.u.p vx); (* TODO why doesn't this work? *)
  assume (full p.u.p (upd_x vx)); (* can't be unit because upd_x is frame_preserving and vx != unit *)
  full_tup p q (upd_x vx) vy;
  assert ((tuple_pcm p q).u.refine (vx, vy) ==> full (tuple_pcm p q).u.p (upd_x vx, vy));
  assert ((tuple_pcm p q).u.refine (vx, vy) ==> (tuple_pcm p q).u.refine (upd_x vx, vy));
  assume ((tuple_pcm p q).u.refine (vx, vy) ==> frame_preserving (tuple_pcm p q).u (vx, vy) (upd_x vx, vy));
  (upd_x vx, vy)
*)

(*
val full_tup :
  p: refined_pcm 'a -> q: refined_pcm 'b -> x: 'a -> y: 'b ->
  full (tuple_pcm p q).u.p (x, y) == full p.u.p x /\ full q.u.p y
let full_tup p q x y =
  (* (forall (x', y') composable with (x, y). (x <> x', y <> y') = (x, y))
     <=> (forall x' comp w/ x and y' comp w/ y. x <> x' = x /\ y <> y' = y)
     <=> (forall x' comp w/ x. x <> x' = x) /\ (forall y' comp w/. y <> y' = y) *)
  admit() (* TODO how to prove this? *)
  *)

(*
val frame_preserving_full_value :
  p: refined_pcm 'a -> x: 'a -> y: 'a ->
  f:frame_preserving_upd_0 p.u x y ->
  Lemma (requires full p.u.p x) (ensures full p.u.p (f v))
let frame_preserving_full_value #a p x y f =
  compatible_refl p.u x;
  p.refine_unit_or_full x;
  assert (p.u.refine x);
  let z = f x in
  assert (p.u.refine z);
  assert (frame_preserving p.u x z);
  assume (forall (frame:a{composable p.u frame z}). op p.u frame z == z);
  admit()
  *)

(*
val upd_fst_0 :
  p: refined_pcm 'a -> q: refined_pcm 'b ->
  r: ref ('a & 'b) (tuple_pcm p q).u ->
  x: Ghost.erased 'a {~ (Ghost.reveal x == p.u.p.one)} -> y: Ghost.erased 'b -> x': 'a ->
  frame_preserving_upd_0 p.u x x' ->
  frame_preserving_upd_0 (tuple_pcm p q).u (Ghost.reveal x, Ghost.reveal y) (x', Ghost.reveal y)
let upd_fst_0 p q r x y x' upd_x (vx, vy) =
  assume (compatible (tuple_pcm p q).u (x', Ghost.reveal y) (upd_x vx, vy));
  // Since x != 1 and compatible x vx, vx != 1 by compat_unit_unique.
  assert (compatible p.u (Ghost.reveal x) vx);
  p.compat_unit_unique (Ghost.reveal x);
  assert (~ (vx == p.u.p.one));
  // Thus, if refine (vx, vy), vx and vy must be full values.
  assert ((tuple_pcm p q).u.refine (vx, vy) ==> full (tuple_pcm p q).u.p (vx, vy));
  full_tup p q vx vy;
  // A frame-preserving update sends full values to full values, so (upd_x vx, vy) is full too.
  assume ((tuple_pcm p q).u.refine (vx, vy) ==> full q.u.p vy); (* TODO why doesn't this work? *)
  assume ((tuple_pcm p q).u.refine (vx, vy) ==> full p.u.p vx); (* TODO why doesn't this work? *)
  assume (full p.u.p (upd_x vx)); (* can't be unit because upd_x is frame_preserving and vx != unit *)
  full_tup p q (upd_x vx) vy;
  assert ((tuple_pcm p q).u.refine (vx, vy) ==> full (tuple_pcm p q).u.p (upd_x vx, vy));
  assert ((tuple_pcm p q).u.refine (vx, vy) ==> (tuple_pcm p q).u.refine (upd_x vx, vy));
  assume ((tuple_pcm p q).u.refine (vx, vy) ==> frame_preserving (tuple_pcm p q).u (vx, vy) (upd_x vx, vy));
  (upd_x vx, vy)
  *)
  
  (*
  change_slprop (pts_to r (Ghost.reveal x, Ghost.reveal y)) (pts_to r (Ghost.reveal (Ghost.hide (Ghost.reveal x, Ghost.reveal y)))) (fun _ -> ());
  upd_gen r (Ghost.hide (Ghost.reveal x, Ghost.reveal y)) (Ghost.hide (Ghost.reveal x', Ghost.reveal y)) upd;
  change_slprop (pts_to r (Ghost.reveal (Ghost.hide (Ghost.reveal x', Ghost.reveal y)))) (pts_to r (Ghost.reveal x', Ghost.reveal y)) (fun _ -> ())*)

/// If no custom PCM is needed, p and q can be instantiated with an all-or-none PCM:

val opt_comp : option 'a -> option 'a -> prop
let opt_comp x y = match x, y with None, _ | _, None -> True | _ -> False

val opt_op : x:option 'a -> y:option 'a {opt_comp x y} -> option 'a
let opt_op x y = match x, y with None, z | z, None -> z

val opt_pcm : pcm (option 'a)
let opt_pcm #a = FStar.PCM.({
  p = {
    composable=opt_comp;
    op=opt_op;
    one=None
  };
  comm = (fun _ _ -> ());
  assoc = (fun _ _ _ -> ());
  assoc_r = (fun _ _ _ -> ());
  is_unit = (fun _ -> ());
  refine = (fun _ -> True);
})

/// We can generalize to 'a-ary products (z:'a -> f z), given a PCM for each z:

open FStar.FunctionalExtensionality

val prod_comp :
  f:('a -> Type) -> (z:'a -> pcm (f z)) ->
  restricted_t 'a f -> restricted_t 'a f -> prop
let prod_comp f p x y = forall z. composable (p z) (x z) (y z)

val prod_op :
  f:('a -> Type) -> p:(z:'a -> pcm (f z)) -> 
  x:restricted_t 'a f -> y: restricted_t 'a f {prod_comp f p x y} -> 
  restricted_t 'a f
let prod_op #a f p x y = on_domain a (fun z -> op (p z) (x z) (y z))

val prod_one : f:('a -> Type) -> (z:'a -> pcm (f z)) -> restricted_t 'a f
let prod_one f p = on_domain _ (fun z -> (p z).p.one)

let ext (a: Type) (b: (a -> Type)) (f g: restricted_t a b)
  : Lemma (ensures (feq #a #b f g <==> f == g))
= extensionality a b f g

val prod_pcm' : f:('a -> Type) -> (z:'a -> pcm (f z)) -> pcm' (restricted_t 'a f)
let prod_pcm' #a f p = FStar.PCM.({
  composable = prod_comp f p;
  op = prod_op f p;
  one = prod_one f p;
})

val prod_comm :
  f:('a -> Type) -> p:(z:'a -> pcm (f z)) ->
  x:restricted_t 'a f ->
  y:restricted_t 'a f {prod_comp f p x y} ->
  Lemma (prod_op f p x y == prod_op f p y x)
let prod_comm #a f p x y =
  let comm (z:a): Lemma ((p z).p.op (x z) (y z) == (p z).p.op (y z) (x z)) =
    (p z).comm (x z) (y z)
  in forall_intro comm;
  ext a f (prod_op f p x y) (prod_op f p y x)

val prod_assoc :
  f:('a -> Type) -> p:(w:'a -> pcm (f w)) ->
  x:restricted_t 'a f ->
  y:restricted_t 'a f ->
  z:restricted_t 'a f {prod_comp f p y z /\ prod_comp f p x (prod_op f p y z)} ->
  Lemma (prod_comp f p x y /\
         prod_comp f p (prod_op f p x y) z /\
         prod_op f p x (prod_op f p y z) == prod_op f p (prod_op f p x y) z)
let prod_assoc #a f p x y z =
  let assoc (w:a): 
    Lemma (composable (p w) (x w) (y w) /\
           composable (p w) (op (p w) (x w) (y w)) (z w) /\
           op (p w) (x w) (op (p w) (y w) (z w)) == op (p w) (op (p w) (x w) (y w)) (z w)) 
  = (p w).assoc (x w) (y w) (z w) in
  forall_intro assoc;
  ext a f (prod_op f p x (prod_op f p y z)) (prod_op f p (prod_op f p x y) z)

val prod_assoc_r :
  f:('a -> Type) -> p:(w:'a -> pcm (f w)) ->
  x:restricted_t 'a f ->
  y:restricted_t 'a f ->
  z:restricted_t 'a f {prod_comp f p x y /\ prod_comp f p (prod_op f p x y) z} ->
  Lemma (prod_comp f p y z /\
         prod_comp f p x (prod_op f p y z) /\
         prod_op f p x (prod_op f p y z) == prod_op f p (prod_op f p x y) z)
let prod_assoc_r #a f p x y z =
  let assoc_r (w:a): 
    Lemma (composable (p w) (y w) (z w) /\
           composable (p w) (x w) (op (p w) (y w) (z w)) /\
           op (p w) (x w) (op (p w) (y w) (z w)) == op (p w) (op (p w) (x w) (y w)) (z w)) 
  = (p w).assoc_r (x w) (y w) (z w) in
  forall_intro assoc_r;
  ext a f (prod_op f p x (prod_op f p y z)) (prod_op f p (prod_op f p x y) z)

val prod_is_unit :
  f:('a -> Type) -> p:(z:'a -> pcm (f z)) ->
  x:restricted_t 'a f ->
  Lemma (prod_comp f p x (prod_one f p) /\
         prod_op f p x (prod_one f p) == x)
let prod_is_unit #a f p x =
  let is_unit (y:a): 
    Lemma (composable (p y) (x y) (prod_one f p y) /\
           op (p y) (x y) (prod_one f p y) == x y)
  = (p y).is_unit (x y) in
  forall_intro is_unit;
  ext a f (prod_op f p x (prod_one f p)) x

val prod_pcm : f:('a -> Type) -> (z:'a -> pcm (f z)) -> pcm (restricted_t 'a f)
let prod_pcm #a f p = FStar.PCM.({
  p = prod_pcm' f p;
  comm = prod_comm f p;
  assoc = prod_assoc f p;
  assoc_r = prod_assoc_r f p;
  is_unit = prod_is_unit f p;
  refine = (fun x ->
    (forall z. x z == (p z).p.one) \/
    (forall z. (p z).refine (x z) /\ ~ (x z == (p z).p.one)))
})

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
  p = {
    composable=union_comp f p;
    op=union_op f p;
    one=None
  };
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
  refine = (fun x -> match x with
    | None -> True
    | Some (|xa, xb|) -> (p xa).refine xb /\ ~(xb == (p xa).p.one))
})


(*
val upd_gen (#a:Type) (#p:pcm a) (r:ref a p) (x y:Ghost.erased a)
            (f:FStar.PCM.frame_preserving_upd p x y)
  : SteelT unit
           (pts_to r x)
           (fun _ -> pts_to r y)
           *)

(*
let upd_first #a #b (r:ref (t a b) pcm_t) (x:Ghost.erased a) (y:a)
  : SteelT unit (pts_to r (First #a #b x)) (fun _ -> pts_to r (First #a #b y))
= let f : frame_preserving_upd_0 pcm_t (Ghost.hide (First #a #b x)) (First #a #b y) =
    fun old_v ->
      match old_v with
      | First _ -> First y
      | Both _ z -> Both y z
  in
  change_slprop (pts_to r (First (Ghost.reveal x))) (pts_to r (Ghost.reveal (Ghost.hide (First (Ghost.reveal x))))) (fun _ -> ());
  upd_gen r (Ghost.hide (First #a #b x)) (Ghost.hide (First #a #b y)) f;
  change_slprop (pts_to r (Ghost.reveal (Ghost.hide (First y)))) (pts_to r (First y)) (fun _ -> ())
  *)

(*
val prod_upd :
  #a:eqtype -> f:(a -> Type) -> 
  field:a -> y: f field -> xs: restricted_t a f -> 
  restricted_t a f
let prod_upd #a f field y xs =
  on_domain a (fun field' -> if field = field' then y else xs field')

let frame_preserving_upd #a (p:pcm a) (x y:a) =
  f: (v:a{compatible p x v}
      -> Tot (z:a{
                compatible p y z /\
                 (p.refine v ==> p.refine z) /\
                 (p.refine v ==> frame_preserving p v z)}))
  {
     forall (v:a{compatible p x v}).
         let z = f v in
         (forall (frame:a). {:pattern (composable p v frame)}
              composable p v frame ==>
              composable p z frame /\
              (compatible p x (op p v frame) ==> (op p z frame == f (op p v frame))))
  }

val frame_preserving_upd_field :
  #a:eqtype -> f:(a -> Type) -> p:(field:a -> pcm (f field)) ->
  field:a -> x: f field -> y: f field ->
  xs: restricted_t a f {xs field == x} ->
  frame_preserving_upd (p field) x y ->
  frame_preserving_upd (prod_pcm f p) xs (update f field y xs)
let frame_preserving_upd_field #a f p field x y xs upd =
  _
  *)

(*
val update : ...

val upd_field :
  f:('a -> Type) -> p:(z:'a -> pcm (f z)) ->
  r:ref (restricted_t 'a f) (prod_pcm f p) ->
  field: 'a -> values: Ghost.erased (restricted_t 'a f{defined only at one field}) ->
  x: Ghost.erased (f field) -> y: f field ->
  (frame_preserving_upd_0 (p field) x y) ->
  SteelT unit (pts_to r (Ghost.reveal values))
              (fun _ -> pts_to r (update field y values))

let upd_first #a #b (r:ref (t a b) pcm_t) (x:Ghost.erased a) (y:a)
  : SteelT unit (pts_to r (First #a #b x)) (fun _ -> pts_to r (First #a #b y))
let f : frame_preserving_upd_0 pcm_t (Ghost.hide (First #a #b x)) (First #a #b y) = fun old_v ->
    match old_v with
    | First _ -> First y
    | Both _ z -> Both y z
in change_slprop (pts_to r (First (Ghost.reveal x))) (pts_to r (Ghost.reveal (Ghost.hide (First (Ghost.reveal x))))) (fun _ -> ());
   upd_gen r (Ghost.hide (First #a #b x)) (Ghost.hide (First #a #b y)) f;
   change_slprop (pts_to r (Ghost.reveal (Ghost.hide (First y)))) (pts_to r (First y)) (fun _ -> ())


let upd_first #a #b (r:ref (t a b) pcm_t) (x:Ghost.erased a) (y:a)
  : SteelT unit (pts_to r (First #a #b x)) (fun _ -> pts_to r (First #a #b y))
= let f : frame_preserving_upd_0 pcm_t (Ghost.hide (First #a #b x)) (First #a #b y) = fun old_v ->
    match old_v with
    | First _ -> First y
    | Both _ z -> Both y z
in change_slprop (pts_to r (First (Ghost.reveal x))) (pts_to r (Ghost.reveal (Ghost.hide (First (Ghost.reveal x))))) (fun _ -> ());
   upd_gen r (Ghost.hide (First #a #b x)) (Ghost.hide (First #a #b y)) f;
   change_slprop (pts_to r (Ghost.reveal (Ghost.hide (First y)))) (pts_to r (First y)) (fun _ -> ())


let upd_first #a #b (r:ref (t a b) pcm_t) (x:Ghost.erased a) (y:a)
  : SteelT unit (pts_to r (First #a #b x)) (fun _ -> pts_to r (First #a #b y))
= let f : frame_preserving_upd_0 pcm_t (Ghost.hide (First #a #b x)) (First #a #b y) = fun old_v ->
    match old_v with
    | First _ -> First y
    | Both _ z -> Both y z
in change_slprop (pts_to r (First (Ghost.reveal x))) (pts_to r (Ghost.reveal (Ghost.hide (First (Ghost.reveal x))))) (fun _ -> ());
   upd_gen r (Ghost.hide (First #a #b x)) (Ghost.hide (First #a #b y)) f;
   change_slprop (pts_to r (Ghost.reveal (Ghost.hide (First y)))) (pts_to r (First y)) (fun _ -> ())


// TODO frame-preserving updates
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
