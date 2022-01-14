module Steel.ST.Combinators
include Steel.ST.Util
module Ghost = FStar.Ghost

#set-options "--ide_id_info_off"

(* This module is basically saying that, for any vprop s, there is a
   generic way to derive its "explicit pts_to" version, namely "s
   `vrefine` equals x".  Thus, we offer vprop combinators and
   corresponding rules based on that pattern, all of which we claim
   can eliminate the need for selector predicates in practice.  *)

let equals (#a: Type) (x: a) (y: a) : Tot prop =
  x == y

val vrefine_elim
  (#inames: _)
  (s: vprop)
  (p: t_of s -> Tot prop)
: STGhostT unit inames
    (s `vrefine` p)
    (fun _ -> s)

val vrefine_equals_intro
  (#inames: _)
  (s: vprop)
: STGhostT (Ghost.erased (t_of s)) inames
    s
    (fun res -> s `vrefine` equals (Ghost.reveal res))

val vrefine_vrefine_equals_elim
  (#inames: _)
  (s: vprop)
  (p: t_of s -> Tot prop)
  (x: t_of s)
: STGhost unit
    inames
    (s `vrefine` p `vrefine` equals x)
    (fun _ -> s `vrefine` equals x)
    True
    (fun _ -> p x)

val vrefine_vrefine_equals_intro
  (#inames: _)
  (s: vprop)
  (p: t_of s -> Tot prop)
  (x: t_of s)
: STGhost unit
    inames
    (s `vrefine` equals x)
    (fun _ -> s `vrefine` p `vrefine` equals x)
    (p x)
    (fun _ -> True)

val vrefine_equals_star_intro
  (#inames: _)
  (s1 s2: vprop)
  (x1: t_of s1)
  (x2: t_of s2)
: STGhostT unit
    inames
    ((s1 `vrefine` equals x1) `star` (s2 `vrefine` equals x2))
    (fun _ -> (s1 `star` s2) `vrefine` equals (x1, x2))

val vrefine_equals_star_elim
  (#inames: _)
  (s1 s2: vprop)
  (x: t_of (s1 `star` s2))
: STGhostT unit
    inames
    ((s1 `star` s2) `vrefine` equals x)
    (fun _ -> (s1 `vrefine` equals (fst x)) `star` (s2 `vrefine` equals (snd x)))

val vrewrite_vrefine_equals_intro0
  (#inames: _)
  (#t: Type)
  (s: vprop)
  (f: t_of s -> GTot t)
  (x: t_of s)
: STGhost (Ghost.erased t) inames
    (s `vrefine` equals x)
    (fun res -> s `vrewrite` f `vrefine` equals (Ghost.reveal res))
    True
    (fun res -> Ghost.reveal res == f x)

let vrewrite_vrefine_equals_intro
  (#inames: _)
  (#t: Type)
  (s: vprop)
  (f: t_of s -> GTot t)
  (x: t_of s)
: STGhostT unit inames
    (s `vrefine` equals x)
    (fun res -> s `vrewrite` f `vrefine` equals (f x))
= let res = vrewrite_vrefine_equals_intro0 s f x in
  rewrite
    (s `vrewrite` f `vrefine` equals (Ghost.reveal res))
    (s `vrewrite` f `vrefine` equals (f x))

val vrewrite_vrefine_equals_elim
  (#inames: _)
  (#t: Type)
  (s: vprop)
  (f: t_of s -> GTot t)
  (x: t)
: STGhost (Ghost.erased (t_of s)) inames
    (s `vrewrite` f `vrefine` equals x)
    (fun res -> s `vrefine` equals (Ghost.reveal res))
    True
    (fun res -> f (Ghost.reveal res) == x)

val vdep_intro
  (#inames: _)
  (vtag: vprop)
  (vpl: (t_of vtag -> Tot vprop))
  (tag: t_of vtag)
  (vpl0: vprop)
  (pl: t_of vpl0)
: STGhost (Ghost.erased (normal (t_of (vtag `vdep` vpl)))) inames
    ((vtag `vrefine` equals tag) `star` (vpl0 `vrefine` equals pl))
    (fun res -> (vtag `vdep` vpl) `vrefine` equals (Ghost.reveal res))
    (vpl0 == vpl tag)
    (fun res ->
      vpl0 == vpl tag /\
      dfst (Ghost.reveal res) == tag /\
      dsnd (Ghost.reveal res) == pl
    )

val vdep_elim
  (#inames: _)
  (vtag: vprop)
  (vpl: (t_of vtag -> Tot vprop))
  (x: normal (t_of (vtag `vdep` vpl)))
: STGhostT unit inames
    ((vtag `vdep` vpl) `vrefine` equals x)
    (fun _ -> (vtag `vrefine` equals (dfst x)) `star` (vpl (dfst x) `vrefine` equals (dsnd x)))
