module LineStruct

open Aggregates
open AggregateRef
open FStar.PCM
open Steel.Effect
open PointStruct

/// Example 2: pointers to nested fields
///
/// Here's a struct representing a line segment by its two endpoints:
///   struct line { struct point p1; struct point p2; };
///
/// Carrier of PCM for line:

val line : Type0

/// PCM for line:

val line_pcm : refined_one_pcm line

/// (mk_line p1 p2) represents (struct line){.p1 = p1, .p2 = p2}

val mk_line (x y: Ghost.erased point): Ghost.erased line

/// Lenses for fields

val _p1 : pcm_lens line_pcm point_pcm
val _p2 : pcm_lens line_pcm point_pcm

/// Taking pointers to the p1 and p2 fields of a line

val addr_of_p1 (#p1 #p2: Ghost.erased point) (p: ref 'a line{p.q == line_pcm})
: SteelT (q:ref 'a point{q == ref_focus p point_pcm _p1})
    (p `pts_to` mk_line p1 p2)
    (fun q ->
       (p `pts_to` mk_line (one point_pcm) p2) `star`
       (q `pts_to` p1))

val un_addr_of_p1 (#p1 #p2: Ghost.erased point)
  (p: ref 'a line{p.q == line_pcm})
  (q: ref 'a point{q == ref_focus p point_pcm _p1})
: SteelT unit
    ((p `pts_to` mk_line (one point_pcm) p2) `star` (q `pts_to` p1))
    (fun q -> p `pts_to` mk_line p1 p2)

val addr_of_p2 (#p1 #p2: Ghost.erased point) (p: ref 'a line{p.q == line_pcm})
: SteelT (q:ref 'a point{q == ref_focus p point_pcm _p2})
    (p `pts_to` mk_line p1 p2)
    (fun q ->
       (p `pts_to` mk_line p1 (one point_pcm)) `star`
       (q `pts_to` p2))

val un_addr_of_p2 (#p1 #p2: Ghost.erased point)
  (p: ref 'a line{p.q == line_pcm})
  (q: ref 'a point{q == ref_focus p point_pcm _p2})
: SteelT unit
    ((p `pts_to` mk_line p1 (one point_pcm)) `star` (q `pts_to` p2))
    (fun q -> p `pts_to` mk_line p1 p2)
