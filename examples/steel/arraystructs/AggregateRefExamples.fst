module AggregateRefExamples

open Steel.C.PCM
open Steel.C.Ref

open Steel.Effect
module A = Steel.Effect.Atomic

/// Example 1: swapping the coordinates of a 2d point

open Steel.C.Opt

open PointStruct

/// We can write the following function that swaps the x and y fields of a given point:
/// 
/// void point_swap(struct point *p) {
///   int *q = &p.x;
///   int *r = &p.y;
///   int tmp = *q;
///   *q = *r;
///   *r = tmp;
/// }

let point_swap (p: ref 'a point_pcm) (x y: Ghost.erased int)
: SteelT unit
    (p `pts_to` mk_point (some x) (some y))
    (fun _ -> p `pts_to` mk_point (some y) (some x))
= (* int *q = &p.x; *)
  let q = addr_of_x p in
  (* int *r = &p.y; *)
  let r = addr_of_y p in
  (* tmp = *q; *)
  let tmp : int = opt_read q in
  (* *q = *r; *)
  let vy : int = opt_read r in
  opt_write q vy;
  (* *r = tmp; *)
  opt_write r tmp;
  (* Gather *)
  unaddr_of_x p q;
  unaddr_of_y p r;
  A.return ()

/// We can also implement swap generically:
///
/// void generic_swap<A>(A *p, A *q) {
///   A tmp = *p;
///   *p = *q;
///   *q = tmp;
/// }

let generic_swap (#x #y: Ghost.erased 'c) (p:ref 'a (opt_pcm #'c)) (q:ref 'b (opt_pcm #'c))
: SteelT unit ((p `pts_to` some x) `star` (q `pts_to` some y))
    (fun _ -> (p `pts_to` some y) `star` (q `pts_to` some x))
= (* A tmp = *p; *)
  let tmp = opt_read p in
  (* *p = *q; *)
  let vy = opt_read q in
  opt_write p vy;
  (* *q = tmp *)
  opt_write q tmp;
  A.return ()

/// Now, point_swap written using generic_swap:
///
/// void point_swap_generically(struct point *p) {
///   int *q = &p.x;
///   int *r = &p.y;
///   generic_swap(q, r);
/// }

let point_swap_generically (#x #y: Ghost.erased int) (p: ref 'a point_pcm)
: SteelT unit
    (p `pts_to` mk_point (some x) (some y))
    (fun _ -> p `pts_to` mk_point (some y) (some x))
= (* int *q = &p.x; *)
  let q = addr_of_x p in
  (* int *r = &p.y; *)
  let r = addr_of_y p in
  (* generic_swap(q, r); *)
  generic_swap q r;
  (* Gather *)
  unaddr_of_x p q;
  unaddr_of_y p r;
  A.return ()

/// Reflect a line segment across the line y=x and reverse its direction
///
/// void reflect_and_reverse(struct line *p) {
///   generic_swap(&p.p1.x, &p.p2.y);
///   generic_swap(&p.p1.y, &p.p2.x);
/// }

open LineStruct

let reflect_and_reverse (p: ref 'a line_pcm) (x1 y1 x2 y2: Ghost.erased int)
: SteelT unit
    (p `pts_to` mk_line (mk_point (some x1) (some y1)) (mk_point (some x2) (some y2)))
    (fun _ -> p `pts_to` mk_line (mk_point (some y2) (some x2)) (mk_point (some y1) (some x1)))
= (* generic_swap(&p.p1.x, &p.p2.y); *)
  let pp1 = addr_of_p1 p in
  let pp1x = addr_of_x pp1 in
  let pp2 = addr_of_p2 p in
  let pp2y = addr_of_y pp2 in
  generic_swap pp1x pp2y;
  (* generic_swap(&p.p1.y, &p.p2.x); *)
  let pp1y = addr_of_y pp1 in
  let pp2x = addr_of_x pp2 in
  generic_swap pp1y pp2x;
  (* Gather p1 *)
  unaddr_of_x pp1 pp1x;
  unaddr_of_y pp1 pp1y;
  (* Gather p2 *)
  unaddr_of_x pp2 pp2x;
  unaddr_of_y pp2 pp2y;
  (* Gather p *)
  unaddr_of_p1 p pp1;
  unaddr_of_p2 p pp2;
  A.return ()

open IntOrBool

/// Swap two ints inside two (union int_or_bool)s using generic_swap
///
/// void int_or_bool_int_swap(union int_or_bool *p, union int_or_bool *q)
/// { generic_swap(&p.i, &q.i); }

let int_or_bool_int_swap
  (p: ref 'a int_or_bool_pcm) (q: ref 'b int_or_bool_pcm)
  (i j: Ghost.erased int)
: SteelT unit
    ((p `pts_to` mk_int (some i)) `star` (q `pts_to` mk_int (some j)))
    (fun _ -> (p `pts_to` mk_int (some j)) `star` (q `pts_to` mk_int (some i)))
= (* &p.i *)
  let pi = addr_of_i p in
  (* &q.i *)
  let qi = addr_of_i q in
  (* generic_swap(&p.i, &q.i); *)
  generic_swap pi qi;
  (* Give permissions back to p and q *)
  unaddr_of_i p pi;
  unaddr_of_i q qi

/// Convert an int_or_bool + runtime tag into an int
///
/// int int_or_bool_to_int(bool is_int, union int_or_bool *p) {
///   if (is_int) return p->i;
///   else return p->b ? 1 : 0;
/// }

(* For some reason the proof needs to be given explicitly *)
let extract_int (u: Ghost.erased int_or_bool) (h: squash (case_of_int_or_bool u == Some I))
: Tot (i:Ghost.erased (option int){u == mk_int i /\ ~ (Ghost.reveal i == one (opt_pcm #int))})
= get_int u
let extract_bool (u: Ghost.erased int_or_bool) (h: squash (case_of_int_or_bool u == Some B))
: Tot (b:Ghost.erased (option bool){u == mk_bool b /\ ~ (Ghost.reveal b == one (opt_pcm #bool))})
= get_bool u

let int_or_bool_to_int'
  (is_int: bool)
  (p: ref 'a int_or_bool_pcm)
  (u: Ghost.erased int_or_bool)
: Steel int
    (p `pts_to` u)
    (fun _ -> p `pts_to` u)
    (requires fun _ ->
      if is_int then case_of_int_or_bool u == Some I 
      else case_of_int_or_bool u == Some B)
    (ensures fun _ _ _ -> True)
= if is_int then begin
    let prf: squash (case_of_int_or_bool u == Some I) = () in
    let i: Ghost.erased int = Ghost.hide (Some?.v (extract_int u prf)) in
    assert (u == mk_int (some i));
    A.change_equal_slprop (p `pts_to` u) (p `pts_to` mk_int (some i));
    let pi = addr_of_i p in
    let i = opt_read pi in
    unaddr_of_i p pi;
    A.return i
  end else begin
    let prf: squash (case_of_int_or_bool u == Some B) = () in
    let b: Ghost.erased bool = Ghost.hide (Some?.v (extract_bool u prf)) in
    assert (u == mk_bool (some b));
    A.change_equal_slprop (p `pts_to` u) (p `pts_to` mk_bool (some b));
    let pb = addr_of_b p in
    let b = opt_read pb in
    unaddr_of_b p pb;
    if b then A.return 1 else A.return 0
  end

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
let color_pcm : pcm color_t 
*)
