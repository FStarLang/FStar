module AggregateRefExamples

open Aggregates
open AggregateRef
open FStar.PCM
open FStar.FunctionalExtensionality

open Steel.Effect
module A = Steel.Effect.Atomic

/// Example 1: swapping the coordinates of a 2d point
///
/// Suppose we have the following struct representing 2d points:
///   struct point { int x, y; };
///
/// Carrier of PCM for struct point:

type point_field = | X | Y
let point_fields k = match k with
  | X -> option int
  | Y -> option int
let point = restricted_t point_field point_fields

/// PCM for struct point:

let int_pcm = opt_pcm #int
let point_fields_pcm k : pcm (point_fields k) = match k with
  | X -> int_pcm
  | Y -> int_pcm
let point_pcm = prod_pcm point_fields_pcm

/// (mk_point x y) represents (struct point){.x = x, .y = y}

let mk_point_f (x y: option int) (k: point_field): point_fields k = match k with
  | X -> x
  | Y -> y
let mk_point (x y: option int): point = on_domain point_field (mk_point_f x y)

/// Laws about putting/getting the x and y fields of a (mk_point x y)

let put_x x' x y
: Lemma (feq (put (field point_fields_pcm X) x' (mk_point x y)) (mk_point x' y))
  [SMTPat (put (field point_fields_pcm X) x' (mk_point x y))]
= ()

let get_x x y
: Lemma (get (field point_fields_pcm X) (mk_point x y) == x)
  [SMTPat (get (field point_fields_pcm X) (mk_point x y))]
= ()

let put_y y' x y
: Lemma (feq (put (field point_fields_pcm Y) y' (mk_point x y)) (mk_point x y'))
  [SMTPat (put (field point_fields_pcm Y) y' (mk_point x y))]
= ()

let get_y x y
: Lemma (get (field point_fields_pcm Y) (mk_point x y) == y)
  [SMTPat (get (field point_fields_pcm Y) (mk_point x y))]
= ()

/// Laws relating mk_point to PCM operations

let one_xy : squash (feq (one (prod_pcm point_fields_pcm)) (mk_point None None))
= ()

let merge_xy x y x' y'
: Lemma (feq (op (prod_pcm point_fields_pcm) (mk_point x y) (mk_point x' y'))
             (mk_point (op (point_fields_pcm X) x x') (op (point_fields_pcm Y) y y')))
  [SMTPat (op (prod_pcm point_fields_pcm) (mk_point x y) (mk_point x' y'))]
= ()

/// Taking pointers to the x and y fields of a point

let addr_of_x (p: ref 'a point{p.q == point_pcm}) (x y: Ghost.erased (option int))
: SteelT (q:ref 'a (option int){q == ref_focus p int_pcm (field point_fields_pcm X)})
    (p `pts_to` mk_point x y)
    (fun q ->
       (p `pts_to` mk_point None y) `star`
       (q `pts_to` x))
= let q = addr_of_lens p int_pcm (field point_fields_pcm X) (mk_point x y) in
  A.change_equal_slprop (p `pts_to` _) (p `pts_to` mk_point None y);
  A.change_equal_slprop (q `pts_to` _) (q `pts_to` x);
  A.return q

let addr_of_y (p: ref 'a point{p.q == point_pcm}) (x y: Ghost.erased (option int))
: SteelT (q:ref 'a (option int){q == ref_focus p int_pcm (field point_fields_pcm Y)})
    (p `pts_to` mk_point x y)
    (fun q ->
       (p `pts_to` mk_point x None) `star`
       (q `pts_to` y))
= let q = addr_of_lens p int_pcm (field point_fields_pcm Y) (mk_point x y) in
  A.change_equal_slprop (p `pts_to` _) (p `pts_to` mk_point x None);
  A.change_equal_slprop (q `pts_to` _) (q `pts_to` y);
  A.return q

/// With the above, we can write the following function that swaps the x and y fields of a given point:
/// 
/// void point_swap(struct point *p) {
///   int *q = &p.x;
///   int *r = &p.y;
///   int tmp = *q;
///   *q = *r;
///   *r = tmp;
/// }

let point_swap (p: ref 'a point{p.q == point_pcm}) (x y: Ghost.erased int)
: SteelT unit
    (p `pts_to` mk_point (Some (Ghost.reveal x)) (Some (Ghost.reveal y)))
    (fun _ -> p `pts_to` mk_point (Some (Ghost.reveal y)) (Some (Ghost.reveal x)))
= (* int *q = &p.x; *)
  A.change_equal_slprop (p `pts_to` _) (p `pts_to` _);
  let q = addr_of_x p (Some (Ghost.reveal x)) (Some (Ghost.reveal y)) in
  (* int *r = &p.y; *)
  A.change_equal_slprop (p `pts_to` _) (p `pts_to` _);
  let r = addr_of_y p None (Some (Ghost.reveal y)) in
  (* tmp = *q; *)
  let Some tmp = ref_read q (Some (Ghost.reveal x)) in
  assert (tmp = Ghost.reveal x);
  (* *q = *r; *)
  let Some vy = ref_read r (Some (Ghost.reveal y)) in
  assert (vy = Ghost.reveal y);
  ref_write q _ vy;
  (* *r = tmp; *)
  ref_write r _ tmp;
  (* Gather *)
  A.change_equal_slprop (q `pts_to` _) (q `pts_to` _);
  unfocus q p (field point_fields_pcm X) (Some vy);
  unfocus r p (field point_fields_pcm Y) (Some tmp);
  A.change_equal_slprop
    (p `pts_to` put (field point_fields_pcm X) _ _)
    (p `pts_to` mk_point (Some vy) None);
  A.change_equal_slprop
    (p `pts_to` put (field point_fields_pcm Y) _ _)
    (p `pts_to` mk_point None (Some tmp));
  gather p (mk_point (Some vy) None) (mk_point None (Some tmp));
  gather p (mk_point (Ghost.reveal (Ghost.hide None)) None) _;
  //gather p _ _; // Ask
  A.change_equal_slprop (p `pts_to` _) _

/// Here's a generic swap:
///
/// void generic_swap<A>(A *p, A *q) {
///   A tmp = *p;
///   *p = *q;
///   *q = tmp;
/// }

let generic_swap
  (p:ref 'a (option 'c){p.q == opt_pcm #'c})
  (q:ref 'b (option 'c){q.q == opt_pcm #'c})
  (x y: Ghost.erased 'c)
: SteelT unit
    ((p `pts_to` Some (Ghost.reveal x)) `star`
     (q `pts_to` Some (Ghost.reveal y)))
    (fun _ ->
     (p `pts_to` Some (Ghost.reveal y)) `star`
     (q `pts_to` Some (Ghost.reveal x)))
= (* A tmp = *p; *)
  let Some tmp = ref_read p (Some (Ghost.reveal x)) in
  (* *p = *q; *)
  let Some vy = ref_read q (Some (Ghost.reveal y)) in
  ref_write p _ vy;
  (* *q = tmp *)
  ref_write q _ tmp;
  A.change_equal_slprop (p `pts_to` _) (p `pts_to` _);
  A.change_equal_slprop (q `pts_to` _) (q `pts_to` _)

/// Now, here's point_swap written using generic_swap:
///
/// void point_swap_generically(struct point *p) {
///   int *q = &p.x;
///   int *r = &p.y;
///   generic_swap(q, r);
/// }

let point_swap_generically
  (p: ref 'a point{p.q == point_pcm}) (x y: Ghost.erased int)
: SteelT unit
    (p `pts_to` mk_point (Some (Ghost.reveal x)) (Some (Ghost.reveal y)))
    (fun _ -> p `pts_to` mk_point (Some (Ghost.reveal y)) (Some (Ghost.reveal x)))
= (* int *q = &p.x; *)
  A.change_equal_slprop (p `pts_to` _) (p `pts_to` _);
  let q = addr_of_x p (Some (Ghost.reveal x)) (Some (Ghost.reveal y)) in
  (* int *r = &p.y; *)
  A.change_equal_slprop (p `pts_to` _) (p `pts_to` _);
  let r = addr_of_y p None (Some (Ghost.reveal y)) in
  (* generic_swap(q, r); *)
  A.change_equal_slprop (q `pts_to` _) (q `pts_to` _);
  A.change_equal_slprop (r `pts_to` _) (r `pts_to` _);
  generic_swap q r (Ghost.reveal x) (Ghost.reveal y);
  (* Gather *)
  A.change_equal_slprop (q `pts_to` _) (q `pts_to` _);
  A.change_equal_slprop (r `pts_to` _) (r `pts_to` _);
  unfocus q p (field point_fields_pcm X) (Some (Ghost.reveal y));
  unfocus r p (field point_fields_pcm Y) (Some (Ghost.reveal x));
  A.change_equal_slprop
    (p `pts_to` put (field point_fields_pcm X) _ _)
    (p `pts_to` mk_point (Some (Ghost.reveal y)) None);
  A.change_equal_slprop
    (p `pts_to` put (field point_fields_pcm Y) _ _)
    (p `pts_to` mk_point None (Some (Ghost.reveal x)));
  gather p (mk_point (Some (Ghost.reveal y)) None) (mk_point None (Some (Ghost.reveal x)));
  gather p (mk_point (Ghost.reveal (Ghost.hide None)) None) _;
  A.change_equal_slprop (p `pts_to` _) _

(*
to print proof state, try:

val fake : vprop
let f unit : Steel unit fake (fun _ -> _)
*)

(*
// let gather (r: ref 'a 'c) (x y: Ghost.erased 'c)
// : SteelT (_:unit{composable r.q x y})
//     (to_vprop (r `pts_to` x) `star` to_vprop (r `pts_to` y))
//     (fun _ -> to_vprop (r `pts_to` op r.q x y))

  (*
    (to_vprop (r `pts_to` x))
    (fun _ -> to_vprop (r' `pts_to` put l x (one r'.q)))
    (fun _ -> r == ref_focus r' q l)
    (fun _ _ _ -> True)
    *)

let unfocus #inames (r: ref 'a 'c) (r': ref 'a 'b) (q: refined_one_pcm 'c)
  (l: pcm_lens r'.q q) (x: Ghost.erased 'c)
: A.SteelGhost unit inames
    (to_vprop (r `pts_to` x))
    (fun _ -> to_vprop (r' `pts_to` put l x (one r'.q)))
    (fun _ -> r == ref_focus r' q l)
    (fun _ _ _ -> True)
= A.change_slprop_rel  
    (to_vprop (r `pts_to` x))
    (to_vprop (r' `pts_to` put l x (one r'.q)))
    (fun _ _ -> True)
    (fun m -> r'.pl.get_morphism.f_one ())
*)

(*
let swap (p: ref 'a point{p.q == point_pcm}) (xy: Ghost.erased int)
: SteelT unit
    (to_vprop (p `pts_to` xy))
    (fun _ -> to_vprop (p `pts_to` mk_point (xy Y) (xy X)))
  
let swap (p: ref 'a point{p.q == point_pcm}) (xy: Ghost.erased int)
: SteelT unit
    (to_vprop (p `pts_to` xy))
    (fun _ -> to_vprop (p `pts_to` xy `upd` (X, xy Y) `upd` (Y, xy X)))

let swap (p: ref 'a point{p.q == point_pcm}) (x y: Ghost.erased int)
: SteelT unit
    (to_vprop (p `pts_to` mk_point (Some (Ghost.reveal x)) (Some (Ghost.reveal y))))
    (fun _ -> to_vprop (p `pts_to` mk_point (Some (Ghost.reveal y)) (Some (Ghost.reveal x))))
= let q =
    addr_of_lens p int_pcm (field point_fields_pcm X)
      (mk_point (Some (Ghost.reveal x)) (Some (Ghost.reveal y))) in
  A.slassert (
    to_vprop (p `pts_to` mk_point None (Some (Ghost.reveal y))) `star`
    to_vprop (q `pts_to` Some (Ghost.reveal x)));
  A.sladmit ();
  A.return ()
*)

// let addr_of_lens (r: ref 'a 'b) (q: refined_one_pcm 'c) (l: pcm_lens r.q q) (x: Ghost.erased 'b)
// : SteelT (ref 'a 'c)
//     (to_vprop (r `pts_to` x))
//     (fun s ->
//       to_vprop (r `pts_to` put l (one q) x) `star` 
//       to_vprop (s `pts_to` get l x))
// = peel r q l x;
//   focus r q l (put l (get l x) (one r.q)) (get l x)

(*
let swap (p: ref 'a point) (x y: Ghost.erased (option int))
: Steel unit
    (to_vprop (r `pts_to` mk_point x y))
    (fun _ -> to_vprop (r `pts_to` mk_point y x))
= 
let ref_read (r: ref 'a 'b) (x: Ghost.erased 'b)
: Steel 'b
    (to_vprop (r `pts_to` x)) 
    (fun _ -> to_vprop (r `pts_to` x))
    (requires fun _ -> True)
    (ensures fun _ x' _ -> compatible r.q x x')*)

(** Example: a model for a tagged union representing colors in RGB or HSV
      type color =
        | RGB : r:int -> g:int -> b:int -> color
        | HSV : h:int -> s:int -> v:int -> color *)

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
  
(** Carriers of PCMs for RGB and HSV structs *)
let rgb_t = restricted_t rgb_field rgb_fields
let hsv_t = restricted_t hsv_field hsv_fields

(** Type family for union of RGB and HSV *)
let color_cases t = match t with
  | RGB -> rgb_t
  | HSV -> hsv_t

(** Carrier of PCM for color *)
let color_t = union color_cases

(** All-or-none PCM for integers *)
let int_pcm : pcm int_pcm_t = opt_pcm

(** PCMs for RGB and HSV structs *)
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

(** PCM for color *)
let color_pcm_cases k : pcm (color_cases k) = match k with
  | RGB -> rgb_pcm
  | HSV -> hsv_pcm
let color_pcm : pcm color_t = union_pcm color_pcm_cases
