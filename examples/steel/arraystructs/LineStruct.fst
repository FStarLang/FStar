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
let mk_line p1 p2 =
  Ghost.hide (on_domain line_field (mk_line_f (Ghost.reveal p1) (Ghost.reveal p2)))

let _p1 = struct_field line_fields_pcm P1
let _p2 = struct_field line_fields_pcm P2

/// Taking pointers to the p1 and p2 fields of a line

let line_without_p1 p1 p2
: Lemma (struct_without_field line_fields_pcm P1 (mk_line p1 p2) `feq`
         Ghost.reveal (mk_line (one point_pcm) p2))
  [SMTPat (mk_line p1 p2)]
= ()

let line_with_p1 p1 p2
: Lemma (struct_with_field line_fields_pcm P1 (Ghost.reveal p1) (mk_line (one point_pcm) p2) `feq`
         Ghost.reveal (mk_line p1 p2))
  [SMTPat (mk_line p1 p2)]
= ()

let line_without_p2 p1 p2
: Lemma (struct_without_field line_fields_pcm P2 (mk_line p1 p2) `feq`
         Ghost.reveal (mk_line p1 (one point_pcm)))
  [SMTPat (mk_line p1 p2)]
= ()

let line_with_p2 p1 p2
: Lemma (struct_with_field line_fields_pcm P2 (Ghost.reveal p2) (mk_line p1 (one point_pcm)) `feq`
         Ghost.reveal (mk_line p1 p2))
  [SMTPat (mk_line p1 p2)]
= ()

let addr_of_p1 #a #p1 #p2 p =
  let q = addr_of_struct_field p P1 (mk_line p1 p2) in
  A.change_equal_slprop (p `pts_to` _) (p `pts_to` mk_line (one point_pcm) p2);
  A.change_equal_slprop (q `pts_to` _) (q `pts_to` p1);
  A.return q

let unaddr_of_p1 #a #p1 #p2 p q =
  unaddr_of_struct_field P1 q p (mk_line (one point_pcm) p2) p1;
  A.change_equal_slprop (p `pts_to` _) (p `pts_to` _)

let addr_of_p2 #a #p1 #p2 p =
  let q = addr_of_struct_field p P2 (mk_line p1 p2) in
  A.change_equal_slprop (p `pts_to` _) (p `pts_to` mk_line p1 (one point_pcm));
  A.change_equal_slprop (q `pts_to` _) (q `pts_to` p2);
  A.return q

let unaddr_of_p2 #a #p1 #p2 p q =
  unaddr_of_struct_field P2 q p (mk_line p1 (one point_pcm)) p2;
  A.change_equal_slprop (p `pts_to` _) (p `pts_to` _)
