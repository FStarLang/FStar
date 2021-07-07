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

let one_xy : squash (feq (one point_pcm) (mk_point None None))
= ()

let merge_xy x y x' y'
: Lemma (feq (op point_pcm (mk_point x y) (mk_point x' y'))
             (mk_point (op (point_fields_pcm X) x x') (op (point_fields_pcm Y) y y')))
  [SMTPat (op point_pcm (mk_point x y) (mk_point x' y'))]
= ()

/// Taking pointers to the x and y fields of a point

let addr_of_x (p: ref 'a point{p.q == point_pcm}) (x y: Ghost.erased (option int))
: SteelT (q:ref 'a (option int){q == ref_focus p int_pcm (field point_fields_pcm X)})
    (p `pts_to` mk_point x y)
    (fun q ->
       (p `pts_to` mk_point None y) `star`
       (q `pts_to` x))
= let q = addr_of_lens p (field point_fields_pcm X) (mk_point x y) in
  A.change_equal_slprop (p `pts_to` _) (p `pts_to` mk_point None y);
  A.change_equal_slprop (q `pts_to` _) (q `pts_to` x);
  A.return q

let un_addr_of_x
  (p: ref 'a point{p.q == point_pcm})
  (q: ref 'a (option int){q == ref_focus p int_pcm (field point_fields_pcm X)})
  (x y: Ghost.erased (option int))
: SteelT unit
    ((p `pts_to` mk_point None y) `star` (q `pts_to` x))
    (fun q -> p `pts_to` mk_point x y)
= un_addr_of_lens q p (field point_fields_pcm X) (mk_point None y) x;
  A.change_equal_slprop (p `pts_to` _) (p `pts_to` _)

let addr_of_y (p: ref 'a point{p.q == point_pcm}) (x y: Ghost.erased (option int))
: SteelT (q:ref 'a (option int){q == ref_focus p int_pcm (field point_fields_pcm Y)})
    (p `pts_to` mk_point x y)
    (fun q ->
       (p `pts_to` mk_point x None) `star`
       (q `pts_to` y))
= let q = addr_of_lens p (field point_fields_pcm Y) (mk_point x y) in
  A.change_equal_slprop (p `pts_to` _) (p `pts_to` mk_point x None);
  A.change_equal_slprop (q `pts_to` _) (q `pts_to` y);
  A.return q

let un_addr_of_y
  (p: ref 'a point{p.q == point_pcm})
  (q: ref 'a (option int){q == ref_focus p int_pcm (field point_fields_pcm Y)})
  (x y: Ghost.erased (option int))
: SteelT unit
    ((p `pts_to` mk_point x None) `star` (q `pts_to` y))
    (fun q -> p `pts_to` mk_point x y)
= un_addr_of_lens q p (field point_fields_pcm Y) (mk_point x None) y;
  A.change_equal_slprop (p `pts_to` _) (p `pts_to` _)

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
  (* *q = *r; *)
  let Some vy = ref_read r (Some (Ghost.reveal y)) in
  ref_write q _ vy;
  (* *r = tmp; *)
  ref_write r _ tmp;
  (* Gather *)
  A.change_equal_slprop (p `pts_to` _) (p `pts_to` _);
  A.change_equal_slprop (q `pts_to` _) (q `pts_to` _);
  un_addr_of_x p q (Some vy) None;
  A.change_equal_slprop (p `pts_to` _) (p `pts_to` _);
  A.change_equal_slprop (r `pts_to` _) (r `pts_to` _);
  un_addr_of_y p r (Some vy) (Some tmp);
  A.change_equal_slprop (p `pts_to` _) (p `pts_to` _)

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
  A.change_equal_slprop (p `pts_to` _) (p `pts_to` _);
  A.change_equal_slprop (q `pts_to` _) (q `pts_to` _);
  un_addr_of_x p q (Some (Ghost.reveal y)) None;
  A.change_equal_slprop (p `pts_to` _) (p `pts_to` _);
  A.change_equal_slprop (r `pts_to` _) (r `pts_to` _);
  un_addr_of_y p r (Some (Ghost.reveal y)) (Some (Ghost.reveal x));
  A.change_equal_slprop (p `pts_to` _) (p `pts_to` _)

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
        (mk_point (Some (Ghost.reveal x1)) (Some (Ghost.reveal y1)))
        (mk_point (Some (Ghost.reveal x2)) (Some (Ghost.reveal y2))))
    (fun _ ->
      p `pts_to`
        mk_line
          (mk_point (Some (Ghost.reveal y2)) (Some (Ghost.reveal x2)))
          (mk_point (Some (Ghost.reveal y1)) (Some (Ghost.reveal x1))))
= (* Take all the requisite pointers *)
  A.change_equal_slprop (p `pts_to` _) (p `pts_to` _);
  let pp1 =
    addr_of_p1 p
      (mk_point (Some (Ghost.reveal x1)) (Some (Ghost.reveal y1)))
      (mk_point (Some (Ghost.reveal x2)) (Some (Ghost.reveal y2)))
  in
  A.change_equal_slprop (p `pts_to` _) (p `pts_to` _);
  let pp2 =
    addr_of_p2 p
      (one point_pcm)
      (mk_point (Some (Ghost.reveal x2)) (Some (Ghost.reveal y2)))
  in
  (* &p.p1.x *)
  A.change_equal_slprop (pp1 `pts_to` _) (pp1 `pts_to` _);
  let pp1x = addr_of_x pp1 (Some (Ghost.reveal x1)) (Some (Ghost.reveal y1)) in
  (* &p.p1.y *)
  A.change_equal_slprop (pp1 `pts_to` _) (pp1 `pts_to` _);
  let pp1y = addr_of_y pp1 None (Some (Ghost.reveal y1)) in
  (* &p.p2.x *)
  A.change_equal_slprop (pp2 `pts_to` _) (pp2 `pts_to` _);
  let pp2x = addr_of_x pp2 (Some (Ghost.reveal x2)) (Some (Ghost.reveal y2)) in
  (* &p.p2.y *)
  A.change_equal_slprop (pp2 `pts_to` _) (pp2 `pts_to` _);
  let pp2y = addr_of_y pp2 None (Some (Ghost.reveal y2)) in
  (* generic_swap(&p.p1.x, &p.p2.y); *)
  generic_swap pp1x pp2y x1 y2;
  (* generic_swap(&p.p1.y, &p.p2.x); *)
  generic_swap pp1y pp2x y1 x2;
  (* Gather p1 *)
  A.change_equal_slprop (pp1x `pts_to` _) (pp1x `pts_to` _);
  A.change_equal_slprop (pp1 `pts_to` _) (pp1 `pts_to` _);
  un_addr_of_x pp1 pp1x (Some (Ghost.reveal y2)) None;
  A.change_equal_slprop (pp1y `pts_to` _) (pp1y `pts_to` _);
  A.change_equal_slprop (pp1 `pts_to` _) (pp1 `pts_to` _);
  un_addr_of_y pp1 pp1y (Some (Ghost.reveal y2)) (Some (Ghost.reveal x2));
  (* Gather p2 *)
  A.change_equal_slprop (pp2x `pts_to` _) (pp2x `pts_to` _);
  A.change_equal_slprop (pp2 `pts_to` _) (pp2 `pts_to` _);
  un_addr_of_x pp2 pp2x (Some (Ghost.reveal y1)) None;
  A.change_equal_slprop (pp2y `pts_to` _) (pp2y `pts_to` _);
  A.change_equal_slprop (pp2 `pts_to` _) (pp2 `pts_to` _);
  un_addr_of_y pp2 pp2y (Some (Ghost.reveal y1)) (Some (Ghost.reveal x1));
  (* Gather p *)
  A.change_equal_slprop (pp1 `pts_to` _) (pp1 `pts_to` _);
  A.change_equal_slprop (p `pts_to` _) (p `pts_to` _);
  un_addr_of_p1 p pp1 (mk_point (Some (Ghost.reveal y2)) (Some (Ghost.reveal x2))) (one point_pcm);
  A.change_equal_slprop (pp2 `pts_to` _) (pp2 `pts_to` _);
  A.change_equal_slprop (p `pts_to` _) (p `pts_to` _);
  un_addr_of_p2 p pp2
    (mk_point (Some (Ghost.reveal y2)) (Some (Ghost.reveal x2)))
    (mk_point (Some (Ghost.reveal y1)) (Some (Ghost.reveal x1)));
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
  unfocus pp1x pp1 (field point_fields_pcm X) (Some (Ghost.reveal y2));
  unfocus pp1y pp1 (field point_fields_pcm Y) (Some (Ghost.reveal x2));
  A.change_equal_slprop
    (pp1 `pts_to` put (field point_fields_pcm X) _ _)
    (pp1 `pts_to` mk_point (Some (Ghost.reveal y2)) None);
  A.change_equal_slprop
    (pp1 `pts_to` put (field point_fields_pcm Y) _ _)
    (pp1 `pts_to` mk_point None (Some (Ghost.reveal x2)));
  gather pp1 (mk_point (Some (Ghost.reveal y2)) None) (mk_point None (Some (Ghost.reveal x2)));
  gather pp1 (mk_point (Ghost.reveal (Ghost.hide None)) None) _;
  (* Gather p2 *)
  A.change_equal_slprop (pp2x `pts_to` _) (pp2x `pts_to` _);
  A.change_equal_slprop (pp2y `pts_to` _) (pp2y `pts_to` _);
  unfocus pp2x pp2 (field point_fields_pcm X) (Some (Ghost.reveal y1));
  unfocus pp2y pp2 (field point_fields_pcm Y) (Some (Ghost.reveal x1));
  A.change_equal_slprop
    (pp2 `pts_to` put (field point_fields_pcm X) _ _)
    (pp2 `pts_to` mk_point (Some (Ghost.reveal y1)) None);
  A.change_equal_slprop
    (pp2 `pts_to` put (field point_fields_pcm Y) _ _)
    (pp2 `pts_to` mk_point None (Some (Ghost.reveal x1)));
  gather pp2 (mk_point (Some (Ghost.reveal y1)) None) (mk_point None (Some (Ghost.reveal x1)));
  gather pp2 (mk_point (Ghost.reveal (Ghost.hide None)) None) _;
  (* Gather p *)
  A.change_equal_slprop (pp1 `pts_to` _) (pp1 `pts_to` _);
  A.change_equal_slprop (pp2 `pts_to` _) (pp2 `pts_to` _);
  unfocus pp1 p (field line_fields_pcm P1)
    (mk_point (Some (Ghost.reveal y2)) (Some (Ghost.reveal x2)));
  unfocus pp2 p (field line_fields_pcm P2)
    (mk_point (Some (Ghost.reveal y1)) (Some (Ghost.reveal x1)));
  A.change_equal_slprop
    (p `pts_to` put (field line_fields_pcm P1) _ _)
    (p `pts_to`
      mk_line
        (mk_point (Some (Ghost.reveal y2)) (Some (Ghost.reveal x2)))
        (one point_pcm));
  A.change_equal_slprop
    (p `pts_to` put (field line_fields_pcm P2) _ _)
    (p `pts_to`
      mk_line
        (one point_pcm)
        (mk_point (Some (Ghost.reveal y1)) (Some (Ghost.reveal x1))));
  gather p
    (mk_line
      (mk_point (Some (Ghost.reveal y2)) (Some (Ghost.reveal x2)))
      (one point_pcm))
    (mk_line
       (one point_pcm)
       (mk_point (Some (Ghost.reveal y1)) (Some (Ghost.reveal x1))));
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
