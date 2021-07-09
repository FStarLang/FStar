module LineStruct

open FStar.FunctionalExtensionality
module A = Steel.Effect.Atomic

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
let mk_line p1 p2 = on_domain line_field (mk_line_f (Ghost.reveal p1) (Ghost.reveal p2))

let _p1 = field line_fields_pcm P1
let _p2 = field line_fields_pcm P2

/// Laws about putting/getting the x and y fields of a (mk_line x y)

let put_p1 p1' p1 p2
: Lemma (feq (put _p1 (Ghost.reveal p1') (mk_line p1 p2)) (mk_line p1' p2))
  [SMTPat (put _p1 p1' (mk_line p1 p2))]
= ()

let put_p2 p2' p1 p2
: Lemma (feq (put _p2 (Ghost.reveal p2') (mk_line p1 p2)) (mk_line p1 p2'))
  [SMTPat (put _p2 p2' (mk_line p1 p2))]
= ()

/// Laws relating mk_line to PCM operations

let one_line : squash (feq (one line_pcm) (mk_line (one point_pcm) (one point_pcm)))
= ()

let merge_line p1 p2 p1' p2'
: Lemma
    (requires composable line_pcm (mk_line p1 p2) (mk_line p1' p2'))
    (ensures feq (op line_pcm (mk_line p1 p2) (mk_line p1' p2'))
             (mk_line (op (line_fields_pcm P1) (Ghost.reveal p1) (Ghost.reveal p1'))
                      (op (line_fields_pcm P2) (Ghost.reveal p2) (Ghost.reveal p2'))))
  [SMTPat (op line_pcm (mk_line p1 p2) (mk_line p1' p2'))]
= ()

/// Taking pointers to the p1 and p2 fields of a line

let addr_of_p1 #a #p1 #p2 p =
  let q = addr_of_lens p _p1 (mk_line p1 p2) in
  A.change_equal_slprop (p `pts_to` _) (p `pts_to` mk_line (one point_pcm) p2);
  A.change_equal_slprop (q `pts_to` _) (q `pts_to` p1);
  A.return q

let unaddr_of_p1 #a #p1 #p2 p q =
  unaddr_of_lens q p _p1 (mk_line (one point_pcm) p2) p1;
  A.change_equal_slprop (p `pts_to` _) (p `pts_to` _)

let addr_of_p2 #a #p1 #p2 p =
  let q = addr_of_lens p _p2 (mk_line p1 p2) in
  A.change_equal_slprop (p `pts_to` _) (p `pts_to` mk_line p1 (one point_pcm));
  A.change_equal_slprop (q `pts_to` _) (q `pts_to` p2);
  A.return q

let unaddr_of_p2 #a #p1 #p2 p q =
  unaddr_of_lens q p _p2 (mk_line p1 (one point_pcm)) p2;
  A.change_equal_slprop (p `pts_to` _) (p `pts_to` _)
