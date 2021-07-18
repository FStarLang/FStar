module Steel.C.PCM
module P = FStar.PCM
open FStar.FunctionalExtensionality
open FStar.IndefiniteDescription

let symrel_codom (#t: Type) (x: t) : Tot Type0 = bool

let symrel (a: Type u#a) = c:(restricted_g_t (a & a) symrel_codom) { (forall x y. c (x, y) == c (y, x)) }

let op_dom (#a: Type) (composable: symrel a) : Type = (xy: (a & a) { composable xy == true })

let op_codom (#a: Type) (composable: symrel a) (x: op_dom composable) : Type = a

noeq
type pcm' (a:Type u#a) = {
  composable: symrel a;
  op: restricted_t (op_dom composable) (op_codom composable);
  one:a
}

let pcm'_eq (#a: Type u#a) (p1 p2: pcm' a) : Lemma
  (requires (
    p1.composable `feq_g` p2.composable /\
    p1.op `feq` p2.op /\
    p1.one == p2.one
  ))
  (ensures (p1 == p2))
= ()

let fstar_pcm'_of_pcm'
  (#a: Type)
  (p: pcm' a)
: Tot (P.pcm' a)
= {
  P.composable = (fun x y -> p.composable (x, y) == true);
  P.op = (fun x y -> p.op (x, y));
  P.one = p.one;
}

let composable_of_fstar_composable
  (#a: Type)
  (p: P.pcm' a)
: Tot (symrel a)
= on_dom_g (a & a) (fun xy -> strong_excluded_middle (p.P.composable (fst xy) (snd xy)) <: bool)

let op_of_fstar_op
  (#a: Type)
  (p: P.pcm' a)
: Tot (restricted_t (op_dom (composable_of_fstar_composable p)) (op_codom (composable_of_fstar_composable p)))
= on_dom (op_dom (composable_of_fstar_composable p)) (fun xy -> p.P.op (fst xy) (snd xy))

let pcm'_of_fstar_pcm'
  (#a: Type)
  (p: P.pcm' a)
: Tot (pcm' a)
= {
  composable = composable_of_fstar_composable p;
  op = op_of_fstar_op p;
  one = p.P.one;
}

let pcm'_of_fstar_pcm'_of_pcm'
  (#a: Type)
  (p: pcm' a)
: Lemma
  (pcm'_of_fstar_pcm' (fstar_pcm'_of_pcm' p) == p)
= pcm'_of_fstar_pcm' (fstar_pcm'_of_pcm' p) `pcm'_eq` p

let lem_commutative_codom
  (#a: Type u#a) (p:pcm' a) (xy: op_dom p.composable)
: Tot Type
= squash (p.op xy == p.op (snd xy, fst xy))

let lem_commutative (#a: Type u#a) (p:pcm' a) = restricted_t (op_dom p.composable) (lem_commutative_codom p)

let lem_assoc_l_dom (#a: Type u#a) (p: pcm' a) =
  (xyz: (a & a & a) {
    let (x, y, z) = xyz in
    p.composable (y, z) == true /\
    p.composable (x, p.op (y, z)) == true
  })

let lem_assoc_l_codom (#a :Type u#a) (p: pcm' a) (xyz: lem_assoc_l_dom p) =
  squash (
    let (x, y, z) = xyz in
    p.composable (x, y) == true /\
    p.composable (p.op (x, y), z) == true /\
    p.op (x, p.op (y, z)) == p.op (p.op (x, y), z)
  )

let lem_assoc_l (#a :Type u#a) (p: pcm' a) =
  restricted_t (lem_assoc_l_dom p) (lem_assoc_l_codom p)

let lem_assoc_r_dom (#a: Type u#a) (p: pcm' a) =
  (xyz: (a & a & a) {
    let (x, y, z) = xyz in
    p.composable (x, y) == true /\
    p.composable (p.op (x, y), z) == true
  })

let lem_assoc_r_codom (#a :Type u#a) (p: pcm' a) (xyz: lem_assoc_r_dom p) =
  squash (
    let (x, y, z) = xyz in
    p.composable (y, z) == true /\
    p.composable (x, p.op (y, z)) == true /\
    p.op (x, p.op (y, z)) == p.op (p.op (x, y), z)
  )

let lem_assoc_r (#a: Type u#a) (p: pcm' a) =
  restricted_t (lem_assoc_r_dom p) (lem_assoc_r_codom p)

let lem_is_unit_codom (#a: Type u#a) (p: pcm' a) (x: a) : Tot Type0 =
  squash (
    p.composable (x, p.one) == true /\
    p.op (x, p.one) == x
  )

let lem_is_unit (#a: Type) (p: pcm' a) =
  restricted_t a (lem_is_unit_codom p)

noeq
type pcm0 (a:Type u#a) : Type u#a = {
  p:pcm' a;
  comm:lem_commutative p;
  assoc: lem_assoc_l p;
  assoc_r: lem_assoc_r p;
  is_unit: lem_is_unit p;
  refine: restricted_g_t a symrel_codom;
}

let pcm_eq (#a: Type u#a) (p1 p2: pcm0 a) : Lemma
  (requires (
    p1.p.composable `feq_g` p2.p.composable /\
    p1.p.op `feq` p2.p.op /\
    p1.p.one == p2.p.one /\
    p1.refine `feq_g` p2.refine
  ))
  (ensures (p1 == p2))
= assert (p1.comm `feq` p2.comm);
  assert (p1.assoc `feq` p2.assoc);
  assert (p1.assoc_r `feq` p2.assoc_r);
  assert (p1.is_unit `feq` p2.is_unit)

let composable (#a: Type u#a) (p:pcm0 a) (x y:a) = p.p.composable (x, y) == true

let one (#a: Type) (p: pcm0 a) = p.p.one

let op (#a: Type u#a) (p:pcm0 a) (x:a) (y:a{composable p x y}) = p.p.op (x, y)

let op_comm
  (#a: Type u#a)
  (p: pcm0 a)
  (x y: a)
: Lemma
  (requires (composable p x y))
  (ensures (composable p y x /\ op p x y == op p y x))
  [SMTPat (composable p x y)]
= p.comm (x, y)

let p_refine (#a: Type) (p: pcm0 a) (x: a) : Tot prop =
  p.refine x == true

let pcm_of_fstar_pcm
  (#a: Type)
  (p: P.pcm a)
: Tot (pcm0 a)
= let pp = pcm'_of_fstar_pcm' p.P.p in
  {
  p = pp;
  comm = on_dom (op_dom pp.composable) (fun xy -> p.P.comm (fst xy) (snd xy) <: lem_commutative_codom pp xy);
  assoc = on_dom (lem_assoc_l_dom pp) (fun xyz -> let (x, y, z) = xyz in p.P.assoc x y z <: lem_assoc_l_codom pp xyz);
  assoc_r = on_dom (lem_assoc_r_dom pp) (fun xyz -> let (x, y, z) = xyz in p.P.assoc_r x y z <: lem_assoc_r_codom pp xyz);
  is_unit = on_dom a (fun x -> p.P.is_unit x <: lem_is_unit_codom pp x);
  refine = on_dom_g _ (fun x -> strong_excluded_middle (p.P.refine x) <: bool);
}

let fstar_pcm_of_pcm
  (#a: Type)
  (p: pcm0 a)
: Tot (P.pcm a)
= let pp = fstar_pcm'_of_pcm' p.p in
  {
  P.p = pp;
  P.comm = (fun x y -> p.comm (x, y));
  P.assoc = (fun x y z -> p.assoc (x, y, z));
  P.assoc_r = (fun x y z -> p.assoc_r (x, y, z));
  P.is_unit = (fun x ->
    let _ : squash (
      p.p.composable (x, p.p.one) == true /\
      p.p.op (x, p.p.one) == x
    ) =
      p.is_unit x
    in
    assert (p.p.composable (x, p.p.one) == true);
    assert (p.p.op (x, p.p.one) == x)
  );
  P.refine = (fun x -> p.refine x == true);
}

let pcm_of_fstar_pcm_of_pcm
  (#a: Type)
  (p: pcm0 a)
: Lemma
  (pcm_of_fstar_pcm (fstar_pcm_of_pcm p) == p)
= pcm_of_fstar_pcm (fstar_pcm_of_pcm p) `pcm_eq` p

let exclusive (#a:Type u#a) (p:pcm0 a) (x:a) =
  forall (frame:a). composable p x frame ==> frame == p.p.one

let compatible (#a: Type u#a) (pcm:pcm0 a) (x y:a) =
  (exists (frame:a).
    composable pcm x frame /\ op pcm frame x == y
  )

let is_unit (#a: Type u#a) (p:pcm0 a)
  (x:a)
:  Lemma (composable p x (one p) /\
         op p x (one p) == x)
= (fstar_pcm_of_pcm p).P.is_unit x

let is_unit_pat (#a: Type u#a) (p:pcm0 a)
  (x:a)
:  Lemma (composable p x (one p) /\
         op p x (one p) == x)
   [SMTPat (composable p x (one p))]
= is_unit p x

let compatible_intro
  (#a: Type u#a)
  (pcm: pcm0 a)
  (x y: a)
  (frame: a)
: Lemma
  (requires (composable pcm x frame /\ op pcm frame x == y))
  (ensures (compatible pcm x y))
= ()

let compatible_elim
  (#a: Type u#a)
  (pcm: pcm0 a)
  (x y: a)
: Ghost a
  (requires (compatible pcm x y))
  (ensures (fun frame ->
    composable pcm x frame /\
    op pcm frame x == y
  ))
= FStar.IndefiniteDescription.indefinite_description_ghost _ (fun frame -> 
    composable pcm x frame /\
    op pcm frame x == y
  )

let compatible_refl
  (#a: Type u#a)
  (pcm: pcm0 a)
  (x: a)
: Lemma
  (compatible pcm x x)
= compatible_intro pcm x x (one pcm)

type frame_preserving_upd (#a:Type u#a) (p:pcm0 a) (x y:a) =
  v:a{
    p_refine p v /\
    compatible p x v
  } ->
  v_new:a{
    p_refine p v_new /\
    compatible p y v_new /\
    (forall (frame:a{composable p x frame}).{:pattern composable p x frame}
       composable p y frame /\
       (op p x frame == v ==> op p y frame == v_new))}

let fstar_fpu_of_fpu
  (#a: Type u#a)
  (p: pcm0 a)
  (x y: Ghost.erased a)
  (f: frame_preserving_upd p x y)
: Tot (FStar.PCM.frame_preserving_upd (fstar_pcm_of_pcm p) x y)
= fun v ->
  let y : a = f v in
  assert (forall frame . P.composable (fstar_pcm_of_pcm p) x frame <==> composable p x frame);
  y

let pcm (a: Type) : Tot Type =
  (p: pcm0 a {
    (forall (x:a) (y:a{composable p x y}).{:pattern (composable p x y)}
      op p x y == one p ==> x == one p /\ y == one p) /\ // necessary to lift frame-preserving updates to unions
    (forall (x:a) . {:pattern (p_refine p x)} p_refine p x ==> exclusive p x) /\ // nice to have, but not used yet
    (~ (p_refine p (one p))) // necessary to maintain (refine ==> exclusive) for uninit
  })
