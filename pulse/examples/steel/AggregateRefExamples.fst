module AggregateRefExamples

open Aggregates
open AggregateRef
open FStar.PCM
open FStar.FunctionalExtensionality

open Steel.Effect
module A = Steel.Effect.Atomic

/// Example 1: swapping the coordinates of a 2d point

open PointStruct
open PCM.POD

/// We can write the following function that swaps the x and y fields of a given point:
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
    (p `pts_to` mk_point (some x) (some y))
    (fun _ -> p `pts_to` mk_point (some y) (some x))
= (* int *q = &p.x; *)
  let q = addr_of_x p (some x) (some y) in
  (* int *r = &p.y; *)
  let r = addr_of_y p none (some y) in
  (* tmp = *q; *)
  let tmp = ref_read q (some x) in
  (* *q = *r; *)
  let vy = ref_read r (some y) in
  ref_write q _ vy;
  (* *r = tmp; *)
  ref_write r _ tmp;
  (* Gather *)
  un_addr_of_x p q (Ghost.hide vy) none;
  un_addr_of_y p r (Ghost.hide vy) (Ghost.hide tmp);
  A.change_equal_slprop (p `pts_to` _) (p `pts_to` _)

/// We can also implement swap generically:
///
/// void generic_swap<A>(A *p, A *q) {
///   A tmp = *p;
///   *p = *q;
///   *q = tmp;
/// }

let generic_swap
  (p:ref 'a (pod 'c){p.q == pod_pcm 'c})
  (q:ref 'b (pod 'c){q.q == pod_pcm 'c})
  (x y: Ghost.erased 'c)
: SteelT unit ((p `pts_to` some x) `star` (q `pts_to` some y))
    (fun _ -> (p `pts_to` some y) `star` (q `pts_to` some x))
= (* A tmp = *p; *)
  let tmp = ref_read p (some x) in
  (* *p = *q; *)
  let vy = ref_read q (some y) in
  ref_write p _ vy;
  (* *q = tmp *)
  ref_write q _ tmp;
  A.change_equal_slprop (p `pts_to` _) (p `pts_to` _);
  A.change_equal_slprop (q `pts_to` _) (q `pts_to` _)

/// Now, point_swap written using generic_swap:
///
/// void point_swap_generically(struct point *p) {
///   int *q = &p.x;
///   int *r = &p.y;
///   generic_swap(q, r);
/// }

let point_swap_generically
  (p: ref 'a point{p.q == point_pcm}) (x y: Ghost.erased int)
: SteelT unit
    (p `pts_to` mk_point (some x) (some y))
    (fun _ -> p `pts_to` mk_point (some y) (some x))
= (* int *q = &p.x; *)
  let q = addr_of_x p (some x) (some y) in
  (* int *r = &p.y; *)
  let r = addr_of_y p none (some y) in
  (* generic_swap(q, r); *)
  generic_swap q r x y;
  (* Gather *)
  un_addr_of_x p q (some y) none;
  un_addr_of_y p r (some y) (some x);
  A.change_equal_slprop (p `pts_to` _) (p `pts_to` _)

(*
/// Example 2: pointers to nested fields
///
/// Here's a struct representing a line segment by its two endpoints:
///   struct line { struct point p1; struct point p2; };
///
/// Carrier of PCM for line:

type line_field = | P1 | P2
let line_fields k = match k with
  | P1 -> point
  | P2 -> point
let line = restricted_t line_field line_fields

/// PCM for line:

let line_fields_pcm k : pcm (line_fields k) = match k with
  | P1 -> point_pcm
  | P2 -> point_pcm
let line_pcm = prod_pcm line_fields_pcm

/// (mk_line p1 p2) represents (struct line){.p1 = p1, .p2 = p2}

let mk_line_f (p1 p2: point) (k: line_field): line_fields k = match k with
  | P1 -> p1
  | P2 -> p2
let mk_line (p1 p2: point): line = on_domain line_field (mk_line_f p1 p2)

/// Laws about putting/getting the x and y fields of a (mk_line x y)

let put_p1 p1' p1 p2
: Lemma (feq (put (field line_fields_pcm P1) p1' (mk_line p1 p2)) (mk_line p1' p2))
  [SMTPat (put (field line_fields_pcm P1) p1' (mk_line p1 p2))]
= ()

let get_p1 p1 p2
: Lemma (get (field line_fields_pcm P1) (mk_line p1 p2) == p1)
  [SMTPat (get (field line_fields_pcm P1) (mk_line p1 p2))]
= ()

let put_p2 p2' p1 p2
: Lemma (feq (put (field line_fields_pcm P2) p2' (mk_line p1 p2)) (mk_line p1 p2'))
  [SMTPat (put (field line_fields_pcm P2) p2' (mk_line p1 p2))]
= ()

let get_p2 p1 p2
: Lemma (get (field line_fields_pcm P2) (mk_line p1 p2) == p2)
  [SMTPat (get (field line_fields_pcm P2) (mk_line p1 p2))]
= ()

/// Laws relating mk_line to PCM operations

let one_line : squash (feq (one line_pcm) (mk_line (one point_pcm) (one point_pcm)))
= ()

let merge_line p1 p2 p1' p2'
: Lemma (feq (op line_pcm (mk_line p1 p2) (mk_line p1' p2'))
             (mk_line (op (line_fields_pcm P1) p1 p1') (op (line_fields_pcm P2) p2 p2')))
  [SMTPat (op line_pcm (mk_line p1 p2) (mk_line p1' p2'))]
= ()

/// Taking pointers to the p1 and p2 fields of a line

let addr_of_p1 (p: ref 'a line{p.q == line_pcm}) (p1 p2: Ghost.erased point)
: SteelT (q:ref 'a point{q == ref_focus p point_pcm (field line_fields_pcm P1)})
    (p `pts_to` mk_line p1 p2)
    (fun q ->
       (p `pts_to` mk_line (one point_pcm) p2) `star`
       (q `pts_to` p1))
= let q = addr_of_lens p (field line_fields_pcm P1) (mk_line p1 p2) in
  A.change_equal_slprop (p `pts_to` _) (p `pts_to` mk_line (one point_pcm) p2);
  A.change_equal_slprop (q `pts_to` _) (q `pts_to` p1);
  A.return q

let un_addr_of_p1
  (p: ref 'a line{p.q == line_pcm})
  (q: ref 'a point{q == ref_focus p point_pcm (field line_fields_pcm P1)})
  (p1 p2: Ghost.erased point)
: SteelT unit
    ((p `pts_to` mk_line (one point_pcm) p2) `star` (q `pts_to` p1))
    (fun q -> p `pts_to` mk_line p1 p2)
= un_addr_of_lens q p (field line_fields_pcm P1) (mk_line (one point_pcm) p2) p1;
  A.change_equal_slprop (p `pts_to` _) (p `pts_to` _)

let addr_of_p2 (p: ref 'a line{p.q == line_pcm}) (p1 p2: Ghost.erased point)
: SteelT (q:ref 'a point{q == ref_focus p point_pcm (field line_fields_pcm P2)})
    (p `pts_to` mk_line p1 p2)
    (fun q ->
       (p `pts_to` mk_line p1 (one point_pcm)) `star`
       (q `pts_to` p2))
= let q = addr_of_lens p (field line_fields_pcm P2) (mk_line p1 p2) in
  A.change_equal_slprop (p `pts_to` _) (p `pts_to` mk_line p1 (one point_pcm));
  A.change_equal_slprop (q `pts_to` _) (q `pts_to` p2);
  A.return q

let un_addr_of_p2
  (p: ref 'a line{p.q == line_pcm})
  (q: ref 'a point{q == ref_focus p point_pcm (field line_fields_pcm P2)})
  (p1 p2: Ghost.erased point)
: SteelT unit
    ((p `pts_to` mk_line p1 (one point_pcm)) `star` (q `pts_to` p2))
    (fun q -> p `pts_to` mk_line p1 p2)
= un_addr_of_lens q p (field line_fields_pcm P2) (mk_line p1 (one point_pcm)) p2;
  A.change_equal_slprop (p `pts_to` _) (p `pts_to` _)

/// Reflect a line segment across the line y=x and reverse its direction
///
/// void reflect_and_reverse(struct line *p) {
///   generic_swap(&p.p1.x, &p.p2.y);
///   generic_swap(&p.p1.y, &p.p2.x);
/// }

#push-options "--z3rlimit 20"
let reflect_and_reverse
  (p: ref 'a line{p.q == line_pcm}) (x1 y1 x2 y2: Ghost.erased int)
: SteelT unit
    (p `pts_to`
      mk_line
        (mk_point (some (Ghost.reveal x1)) (some (Ghost.reveal y1)))
        (mk_point (some (Ghost.reveal x2)) (some (Ghost.reveal y2))))
    (fun _ ->
      p `pts_to`
        mk_line
          (mk_point (some (Ghost.reveal y2)) (some (Ghost.reveal x2)))
          (mk_point (some (Ghost.reveal y1)) (some (Ghost.reveal x1))))
= (* Take all the requisite pointers *)
  A.change_equal_slprop (p `pts_to` _) (p `pts_to` _);
  let pp1 =
    addr_of_p1 p
      (mk_point (some (Ghost.reveal x1)) (some (Ghost.reveal y1)))
      (mk_point (some (Ghost.reveal x2)) (some (Ghost.reveal y2)))
  in
  A.change_equal_slprop (p `pts_to` _) (p `pts_to` _);
  let pp2 =
    addr_of_p2 p
      (one point_pcm)
      (mk_point (some (Ghost.reveal x2)) (some (Ghost.reveal y2)))
  in
  (* &p.p1.x *)
  A.change_equal_slprop (pp1 `pts_to` _) (pp1 `pts_to` _);
  let pp1x = addr_of_x pp1 (some (Ghost.reveal x1)) (some (Ghost.reveal y1)) in
  (* &p.p1.y *)
  A.change_equal_slprop (pp1 `pts_to` _) (pp1 `pts_to` _);
  let pp1y = addr_of_y pp1 none (some (Ghost.reveal y1)) in
  (* &p.p2.x *)
  A.change_equal_slprop (pp2 `pts_to` _) (pp2 `pts_to` _);
  let pp2x = addr_of_x pp2 (some (Ghost.reveal x2)) (some (Ghost.reveal y2)) in
  (* &p.p2.y *)
  A.change_equal_slprop (pp2 `pts_to` _) (pp2 `pts_to` _);
  let pp2y = addr_of_y pp2 none (some (Ghost.reveal y2)) in
  (* generic_swap(&p.p1.x, &p.p2.y); *)
  generic_swap pp1x pp2y x1 y2;
  (* generic_swap(&p.p1.y, &p.p2.x); *)
  generic_swap pp1y pp2x y1 x2;
  (* Gather p1 *)
  A.change_equal_slprop (pp1x `pts_to` _) (pp1x `pts_to` _);
  A.change_equal_slprop (pp1 `pts_to` _) (pp1 `pts_to` _);
  un_addr_of_x pp1 pp1x (some (Ghost.reveal y2)) none;
  A.change_equal_slprop (pp1y `pts_to` _) (pp1y `pts_to` _);
  A.change_equal_slprop (pp1 `pts_to` _) (pp1 `pts_to` _);
  un_addr_of_y pp1 pp1y (some (Ghost.reveal y2)) (some (Ghost.reveal x2));
  (* Gather p2 *)
  A.change_equal_slprop (pp2x `pts_to` _) (pp2x `pts_to` _);
  A.change_equal_slprop (pp2 `pts_to` _) (pp2 `pts_to` _);
  un_addr_of_x pp2 pp2x (some (Ghost.reveal y1)) none;
  A.change_equal_slprop (pp2y `pts_to` _) (pp2y `pts_to` _);
  A.change_equal_slprop (pp2 `pts_to` _) (pp2 `pts_to` _);
  un_addr_of_y pp2 pp2y (some (Ghost.reveal y1)) (some (Ghost.reveal x1));
  (* Gather p *)
  A.change_equal_slprop (pp1 `pts_to` _) (pp1 `pts_to` _);
  A.change_equal_slprop (p `pts_to` _) (p `pts_to` _);
  un_addr_of_p1 p pp1 (mk_point (some (Ghost.reveal y2)) (some (Ghost.reveal x2))) (one point_pcm);
  A.change_equal_slprop (pp2 `pts_to` _) (pp2 `pts_to` _);
  A.change_equal_slprop (p `pts_to` _) (p `pts_to` _);
  un_addr_of_p2 p pp2
    (mk_point (some (Ghost.reveal y2)) (some (Ghost.reveal x2)))
    (mk_point (some (Ghost.reveal y1)) (some (Ghost.reveal x1)));
  A.change_equal_slprop (p `pts_to` _) (p `pts_to` _)
#pop-options

(*
addr_of
  (r `pts_to` xs)
  (r `pts_to` xs \ k `star` s `pts_to` xs k)
  
addr_of
  (r `pts_to` xs `star` s `pts_to` y)
  (r `pts_to` xs [k `mapsto` y])
  *)

(*

  A.change_equal_slprop (pp1x `pts_to` _) (pp1x `pts_to` _);
  A.change_equal_slprop (pp1y `pts_to` _) (pp1y `pts_to` _);
  unfocus pp1x pp1 (field point_fields_pcm X) (some (Ghost.reveal y2));
  unfocus pp1y pp1 (field point_fields_pcm Y) (some (Ghost.reveal x2));
  A.change_equal_slprop
    (pp1 `pts_to` put (field point_fields_pcm X) _ _)
    (pp1 `pts_to` mk_point (some (Ghost.reveal y2)) none);
  A.change_equal_slprop
    (pp1 `pts_to` put (field point_fields_pcm Y) _ _)
    (pp1 `pts_to` mk_point none (some (Ghost.reveal x2)));
  gather pp1 (mk_point (some (Ghost.reveal y2)) none) (mk_point none (some (Ghost.reveal x2)));
  gather pp1 (mk_point (Ghost.reveal (Ghost.hide none)) none) _;
  (* Gather p2 *)
  A.change_equal_slprop (pp2x `pts_to` _) (pp2x `pts_to` _);
  A.change_equal_slprop (pp2y `pts_to` _) (pp2y `pts_to` _);
  unfocus pp2x pp2 (field point_fields_pcm X) (some (Ghost.reveal y1));
  unfocus pp2y pp2 (field point_fields_pcm Y) (some (Ghost.reveal x1));
  A.change_equal_slprop
    (pp2 `pts_to` put (field point_fields_pcm X) _ _)
    (pp2 `pts_to` mk_point (some (Ghost.reveal y1)) none);
  A.change_equal_slprop
    (pp2 `pts_to` put (field point_fields_pcm Y) _ _)
    (pp2 `pts_to` mk_point none (some (Ghost.reveal x1)));
  gather pp2 (mk_point (some (Ghost.reveal y1)) none) (mk_point none (some (Ghost.reveal x1)));
  gather pp2 (mk_point (Ghost.reveal (Ghost.hide none)) none) _;
  (* Gather p *)
  A.change_equal_slprop (pp1 `pts_to` _) (pp1 `pts_to` _);
  A.change_equal_slprop (pp2 `pts_to` _) (pp2 `pts_to` _);
  unfocus pp1 p (field line_fields_pcm P1)
    (mk_point (some (Ghost.reveal y2)) (some (Ghost.reveal x2)));
  unfocus pp2 p (field line_fields_pcm P2)
    (mk_point (some (Ghost.reveal y1)) (some (Ghost.reveal x1)));
  A.change_equal_slprop
    (p `pts_to` put (field line_fields_pcm P1) _ _)
    (p `pts_to`
      mk_line
        (mk_point (some (Ghost.reveal y2)) (some (Ghost.reveal x2)))
        (one point_pcm));
  A.change_equal_slprop
    (p `pts_to` put (field line_fields_pcm P2) _ _)
    (p `pts_to`
      mk_line
        (one point_pcm)
        (mk_point (some (Ghost.reveal y1)) (some (Ghost.reveal x1))));
  gather p
    (mk_line
      (mk_point (some (Ghost.reveal y2)) (some (Ghost.reveal x2)))
      (one point_pcm))
    (mk_line
       (one point_pcm)
       (mk_point (some (Ghost.reveal y1)) (some (Ghost.reveal x1))));
  gather p (mk_line (Ghost.reveal (Ghost.hide (one point_pcm))) (one point_pcm)) _;
  //A.change_equal_slprop (pp2 `pts_to` _) _;
  (* int *r = &p.p1.y; *)
  (* int *s = &p.p2.x; *)
  (* int *t = &p.p2.y; *)
  A.sladmit();
  A.return ()
#pop-options
*)

(*
pts_to r x
(fun r' -> pts_to r' x')
(requires (fun _ -> x is in case A))
(ensures (fun _ r' _ -> x == A x'))
A x' = (|TagA, x'|)

(q:ref .) (t: erased tag)
pts_to q (t, u)
(requires (fun _ -> u is in case (tag_denote t)))

(q:ref .) (t: erased tag)
(r:ref . = the union inside q)
pts_to q (t, one) `star` pts_to r x

(requires (fun _ -> x is in case (tag_denote t)))
*)

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
    (to_vprop (p `pts_to` mk_point (some (Ghost.reveal x)) (some (Ghost.reveal y))))
    (fun _ -> to_vprop (p `pts_to` mk_point (some (Ghost.reveal y)) (some (Ghost.reveal x))))
= let q =
    addr_of_lens p int_pcm (field point_fields_pcm X)
      (mk_point (some (Ghost.reveal x)) (some (Ghost.reveal y))) in
  A.slassert (
    to_vprop (p `pts_to` mk_point none (some (Ghost.reveal y))) `star`
    to_vprop (q `pts_to` some (Ghost.reveal x)));
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

*)
