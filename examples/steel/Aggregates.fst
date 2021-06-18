module Aggregates

open FStar.PCM

/// We can define a PCM for structs with two fields {a; b} by defining
/// a PCM for tuples (a & b) in terms of (potentially user-defined)
/// PCMs for a and b.

let tuple_comp (p: pcm 'a) (q: pcm 'b) (x y: 'a & 'b) : prop =
  composable p (fst x) (fst y) /\ composable q (snd x) (snd y)

let tuple_op (p: pcm 'a) (q: pcm 'b) (x: 'a & 'b) (y: ('a & 'b){tuple_comp p q x y}) : 'a & 'b =
  (op p (fst x) (fst y), op q (snd x) (snd y))

let tuple_pcm (p: pcm 'a) (q: pcm 'b): pcm ('a & 'b) = {
  p = {composable = tuple_comp p q; op = tuple_op p q; one = (p.p.one, q.p.one)};
  comm = (fun (xa, xb) (ya, yb) -> p.comm xa ya; q.comm xb yb);
  assoc = (fun (xa, xb) (ya, yb) (za, zb) -> p.assoc xa ya za; q.assoc xb yb zb);
  assoc_r = (fun (xa, xb) (ya, yb) (za, zb) -> p.assoc_r xa ya za; q.assoc_r xb yb zb);
  is_unit = (fun (xa, xb) -> p.is_unit xa; q.is_unit xb);
  refine = (fun (xa, xb) -> p.refine xa /\ q.refine xb)
}

/// If no custom PCM is needed, p and q can be instantiated with an all-or-none PCM:

let opt_comp (x y: option 'a): prop = match x, y with
  | None, _ | _, None -> True
  | _, _ -> False

let opt_op (x: option 'a) (y: option 'a{opt_comp x y}): option 'a = match x, y with
  | None, z | z, None -> z

let opt_pcm #a : pcm (option a) = {
  p = {composable = opt_comp; op = opt_op; one = None};
  comm = (fun _ _ -> ());
  assoc = (fun _ _ _ -> ());
  assoc_r = (fun _ _ _ -> ());
  is_unit = (fun _ -> ());
  refine = (fun _ -> True);
}

/// We can define frame-preserving updates for a tuple PCM from
/// frame-preserving updates on its components. For example, to define
/// a frame-preserving update on the first component:

let compatible_tuple_l (p: pcm 'a) (q: pcm 'b) (x v: 'a) (y w: 'b)
: Lemma 
    (requires compatible p x v /\ compatible q y w)
    (ensures compatible (tuple_pcm p q) (x, y) (v, w))
= let pq = tuple_pcm p q in
  let aux frame_x frame_y :
    Lemma 
      (requires composable pq (x, y) (frame_x, frame_y) /\
                op pq (frame_x, frame_y) (x, y) == (v, w))
      (ensures compatible pq (x, y) (v, w))
      [SMTPat (composable p x frame_x); SMTPat (composable q y frame_y)] = ()
  in ()

let upd_fst (p: pcm 'a) (q: pcm 'b) (x: 'a) (y: 'b) (x': 'a)
  (f: frame_preserving_upd p x x')
: frame_preserving_upd (tuple_pcm p q) (x, y) (x', y)
= fun (va, vb) ->
  let wa = f va in
  let pq = tuple_pcm p q in
  compatible_tuple_l p q x' wa y vb;
  let aux (frame: _{composable pq (x, y) frame}):
    Lemma (composable pq (x', y) frame /\
           (op pq (x, y) frame == (va, vb) ==> op pq (x', y) frame == (wa, vb)))
    [SMTPat (composable pq (x, y) frame)] = ()
  in (wa, vb)

/// Frame-preserving updates on the second component can be done similarly.
/// To avoid having to write a frame-preserving update for each field separately,
/// we generalize to 'a-ary products (k:'a -> f k), given a PCM for each k:

open FStar.FunctionalExtensionality
open FStar.Classical
let ext #a #b (f g: restricted_t a b) (fg:(x:a -> Lemma (f x == g x))) : Lemma (f == g) =
  extensionality a b f g;
  forall_intro fg

let prod_comp #f (p:(k:'a -> pcm (f k))) (x y: restricted_t 'a f): prop =
  forall k. composable (p k) (x k) (y k)

let prod_op #a #f (p:(k:a -> pcm (f k)))
  (x: restricted_t a f) (y: restricted_t a f{prod_comp p x y})
: restricted_t a f
= on_domain a (fun k -> op (p k) (x k) (y k))

let prod_one #a #f (p:(k:a -> pcm (f k))): restricted_t a f =
  on_domain a (fun k -> (p k).p.one)

let prod_comm #f (p:(k:'a -> pcm (f k)))
  (x: restricted_t 'a f) (y: restricted_t 'a f{prod_comp p x y})
: Lemma (prod_op p x y == prod_op p y x)
= ext (prod_op p x y) (prod_op p y x) (fun k -> (p k).comm (x k) (y k))

let prod_assoc #f (p:(k:'a -> pcm (f k)))
  (x y: restricted_t 'a f)
  (z: restricted_t 'a f{prod_comp p y z /\ prod_comp p x (prod_op p y z)})
: Lemma (prod_comp p x y /\
         prod_comp p (prod_op p x y) z /\
         prod_op p x (prod_op p y z) == prod_op p (prod_op p x y) z)
= let aux k
  : Lemma (composable (p k) (x k) (y k) /\
           composable (p k) (op (p k) (x k) (y k)) (z k)) 
    [SMTPat (p k)]
  = (p k).assoc (x k) (y k) (z k)
  in
  ext (prod_op p x (prod_op p y z)) (prod_op p (prod_op p x y) z)
    (fun k -> (p k).assoc (x k) (y k) (z k))

let prod_assoc_r #f (p:(k:'a -> pcm (f k)))
  (x y: restricted_t 'a f)
  (z: restricted_t 'a f{prod_comp p x y /\ prod_comp p (prod_op p x y) z})
: Lemma (prod_comp p y z /\
         prod_comp p x (prod_op p y z) /\
         prod_op p x (prod_op p y z) == prod_op p (prod_op p x y) z)
= let aux k
  : Lemma (composable (p k) (y k) (z k) /\
           composable (p k) (x k) (op (p k) (y k) (z k)))
    [SMTPat (p k)]
  = (p k).assoc_r (x k) (y k) (z k)
  in
  ext (prod_op p x (prod_op p y z)) (prod_op p (prod_op p x y) z)
    (fun k -> (p k).assoc (x k) (y k) (z k))

let prod_is_unit #f (p:(k:'a -> pcm (f k))) (x: restricted_t 'a f)
: Lemma (prod_comp p x (prod_one p) /\
         prod_op p x (prod_one p) == x)
= let is_unit k
  : Lemma (composable (p k) (x k) (prod_one p k))
    [SMTPat (p k)]
  = (p k).is_unit (x k)
  in ext (prod_op p x (prod_one p)) x (fun k -> (p k).is_unit (x k))

let prod_refine #f (p:(k:'a -> pcm (f k))) (x: restricted_t 'a f): prop =
  forall k. (p k).refine (x k)

let prod_pcm #f (p:(k:'a -> pcm (f k))): pcm (restricted_t 'a f) = {
  p = {composable = prod_comp p; op = prod_op p; one = prod_one p};
  comm = prod_comm p;
  assoc = prod_assoc p;
  assoc_r = prod_assoc_r p;
  is_unit = prod_is_unit p;
  refine = prod_refine p
}

/// Now, we can define frame-preserving updates for all fields at once:

let fun_upd (#a:eqtype) #f_ty (k:a) (x':f_ty k)
  (f: restricted_t a f_ty)
: restricted_t a f_ty
= on_domain a (fun k' -> if k = k' then x' else f k')

let prod_upd (#a:eqtype) #f_ty (p:(k:a -> pcm (f_ty k))) (k:a)
  (xs: restricted_t a f_ty) (y: f_ty k) (f: frame_preserving_upd (p k) (xs k) y)
: frame_preserving_upd (prod_pcm p) xs (fun_upd k y xs)
= fun vs ->
  let ws_k = f (vs k) in
  let ws = fun_upd k ws_k vs in
  let aux (frame: _{composable (prod_pcm p) xs frame}) :
    Lemma
      (requires op (prod_pcm p) xs frame == vs)
      (ensures
         composable (prod_pcm p) (fun_upd k y xs) frame /\
         op (prod_pcm p) (fun_upd k y xs) frame == ws)
    [SMTPat (composable (prod_pcm p) xs frame)]
  = assert (composable (prod_pcm p) (fun_upd k y xs) frame);
    ext (op (prod_pcm p) (fun_upd k y xs) frame) ws (fun k' -> ())
  in
  let compat_ws_ty = squash (compatible (prod_pcm p) (fun_upd k y xs) ws) in
  compatible_elim (p k) y ws_k compat_ws_ty (fun frame_k ->
  compatible_elim (prod_pcm p) xs vs compat_ws_ty (fun frame_rest ->
  let frame = fun_upd k frame_k frame_rest in
  ext (op (prod_pcm p) frame (fun_upd k y xs)) ws (fun k' -> ())));
  ws
  
/// Similarly, given a PCM for each k:a, we can model a-ary unions
/// with an PCM for option (k:a & f k), where
/// - None is the unit of the PCM
/// - Some (k, x) is a union with tag k and content x

let union (f:'a -> Type) = option (k:'a & f k)

let union_comp #f (p:(k:'a -> pcm (f k))): symrel (union f) = fun x y -> match x, y with
  | None, z | z, None -> True
  | Some (|xa, xb|), Some (|ya, yb|) -> xa == ya /\ composable (p xa) xb yb

let union_op #f (p:(k:'a -> pcm (f k))) (x: union f) (y: union f{union_comp p x y}) : union f = match x, y with
  | None, z | z, None -> z
  | Some (|xa, xb|), Some (|ya, yb|) -> Some (|xa, (p xa).p.op xb yb|)

let union_pcm #f (p:(k:'a -> pcm (f k))): pcm (union f) = {
  p = {composable = union_comp p; op = union_op p; one = None};
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
}

/// Just like with structs, we can define frame-preserving updates on
/// unions from frame-preserving updates on a single case:

let union_upd (#a:eqtype) #f_ty (p:(k:a -> pcm (f_ty k))) (k:a)
  (x y:f_ty k) (f: frame_preserving_upd (p k) x y)
: frame_preserving_upd (union_pcm p) (Some (|k, x|)) (Some (|k, y|))
= fun (Some (|k', v|)) ->
  compatible_elim (union_pcm p) (Some (|k, x|)) (Some (|k, v|)) (compatible (p k) x v)
    (fun frame -> match frame with
      | Some (|k', frame_x|) -> compatible_intro (p k) x v frame_x
      | None -> (union_pcm p).is_unit (Some (|k, x|)); compatible_refl (p k) x);
  let w = f v in
  let aux (frame: _{composable (union_pcm p) (Some (|k, x|)) frame})
  : Lemma (composable (union_pcm p) (Some (|k, y|)) frame /\
           (op (union_pcm p) (Some (|k, x|)) frame == Some (|k, v|) ==>
            op (union_pcm p) (Some (|k, y|)) frame == Some (|k, w|)))
  = match frame with
    | None -> 
      (union_pcm p).is_unit (Some (|k, x|));
      (union_pcm p).is_unit (Some (|k, y|));
      (p k).is_unit x;
      assert (composable (p k) y (p k).p.one /\
              (op (p k) x (p k).p.one == v ==> op (p k) y (p k).p.one == w));
      (p k).is_unit y
    | Some (|_, frame_x|) -> ()
  in forall_intro aux;
  compatible_elim (p k) y w
    (compatible (union_pcm p) (Some (|k, y|)) (Some (|k, w|)))
    (fun frame -> compatible_intro (union_pcm p) (Some (|k, y|)) (Some (|k, w|))
      (Some (|k, frame|)));
  Some (|k, w|)

/// Example: a model for a tagged union representing colors in RGB or HSV
///   type color =
///     | RGB : r:int -> g:int -> b:int -> color
///     | HSV : h:int -> s:int -> v:int -> color

type rgb_field = | R | G | B
type hsv_field = | H | S | V
type color_tag = | RGB | HSV

(* Carrier of all-or-none PCM for integers *)
let int_pcm_t = option int

(* Type families for fields of RGB and HSV structs *)
let rgb_fields k = match k with
  | R -> int_pcm_t
  | G -> int_pcm_t
  | B -> int_pcm_t
let hsv_fields k = match k with
  | H -> int_pcm_t
  | S -> int_pcm_t
  | V -> int_pcm_t
  
(* Carriers of PCMs for RGB and HSV structs *)
let rgb_t = restricted_t rgb_field rgb_fields
let hsv_t = restricted_t hsv_field hsv_fields

(* Type family for union of RGB and HSV *)
let color_cases t = match t with
  | RGB -> rgb_t
  | HSV -> hsv_t

(* Carrier of PCM for color *)
let color_t = union color_cases

(* All-or-none PCM for integers *)
let int_pcm : pcm int_pcm_t = opt_pcm

(* PCMs for RGB and HSV structs *)
let rgb_pcm : pcm (restricted_t rgb_field rgb_fields) =
  prod_pcm #_ #rgb_fields (fun k -> match k with
    | R -> int_pcm
    | G -> int_pcm
    | B -> int_pcm)
let hsv_pcm : pcm (restricted_t hsv_field hsv_fields) =
  prod_pcm #_ #hsv_fields (fun k -> match k with
    | H -> int_pcm
    | S -> int_pcm
    | V -> int_pcm)

(* PCM for color *)
let color_pcm_cases k : pcm (color_cases k) = match k with
  | RGB -> rgb_pcm
  | HSV -> hsv_pcm
let color_pcm : pcm color_t = union_pcm color_pcm_cases

(* Update RGB *)
let rgb_upd (rgb rgb': rgb_t) (f: frame_preserving_upd rgb_pcm rgb rgb')
: frame_preserving_upd color_pcm (Some (|RGB, rgb|)) (Some (|RGB, rgb'|))
= union_upd color_pcm_cases RGB rgb rgb' f

(* Update HSV *)
let hsv_upd (hsv hsv': hsv_t) (f: frame_preserving_upd hsv_pcm hsv hsv')
: frame_preserving_upd color_pcm (Some (|HSV, hsv|)) (Some (|HSV, hsv'|))
= union_upd color_pcm_cases HSV hsv hsv' f

/// In general, from
///   type s = {x1:t1; ..; xn:tn}
///   (Fields could be annotated with custom PCMs; e.g.
///      xi: ti [@custom_pcm pcm_for_ti])
/// Carrier type is
///   s_pcm_t = t1_pcm_t * .. * tn_pcm_t
/// And the PCM is
///   s_pcm = product PCM of t1_pcm .. tn_pcm
///   where
///     ti_pcm =
///       whatever custom PCM was specified by the user, if it exists,
///       and (opt_pcm #ti_pcm_t) otherwise
/// 
/// Similarly, from
///   type s = | x1:t1 | .. | xn:tn
/// Carrier type is
///   s_pcm_t = t1_pcm_t + .. + tn_pcm_t
/// And the PCM is
///   s_pcm = union PCM of t1_pcm .. tn_pcm
///
/// Any subcomponent of a type built from structs and unions not
/// annotated by a custom PCM can be updated using prod_upd,
/// union_upd, and the following frame-preserving update on the
/// all-or-none PCM:

let opt_pcm_upd (x y: 'a)
: frame_preserving_upd opt_pcm (Some x) (Some y)
= fun (Some _) -> (Some y)
