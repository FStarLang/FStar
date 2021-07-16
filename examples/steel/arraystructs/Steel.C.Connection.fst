module Steel.C.Connection

open FStar.PCM
open Steel.C.PCM
open FStar.FunctionalExtensionality

let morph_compose2 (pa: pcm 'a) (pb: pcm 'b) (morph: 'a -> 'b)
  (x1: 'a) (x2: 'a{composable pa x1 x2})
= squash (
    composable pb (morph x1) (morph x2) /\
    morph (x1 `pa.p.op` x2) == morph x1 `pb.p.op` morph x2)
    
let morph_compose1 (pa: pcm 'a) (pb: pcm 'b) (morph: 'a -> 'b) (x1: 'a) =
  restricted_t (x2:'a{composable pa x1 x2}) (morph_compose2 pa pb morph x1)

noeq
type morphism (#a #b: Type) (pa: pcm a) (pb: pcm b) = {
  morph: (a ^-> b);
  morph_unit: squash (morph pa.p.one == pb.p.one);
  morph_compose: restricted_t a (morph_compose1 pa pb morph);
}

let mkmorphism (#pa: pcm 'a) (#pb: pcm 'b) (morph: 'a -> 'b)
  (morph_unit: squash (morph pa.p.one == pb.p.one))
  (morph_compose: (x1:'a -> x2:'a{composable pa x1 x2} -> morph_compose2 pa pb (on_dom 'a morph) x1 x2))
: pa `morphism` pb = {
  morph = on_dom 'a morph;
  morph_unit = morph_unit;
  morph_compose = on_dom 'a (fun x1 -> on_dom (x2:'a{composable pa x1 x2}) (fun x2 -> morph_compose x1 x2));
}

let morph_compose2_irrelevant (pa: pcm 'a) (pb: pcm 'b) (morph: 'a ^-> 'b)
  (x1: 'a) (x2: 'a{composable pa x1 x2})
  (prf1 prf2: morph_compose2 pa pb morph x1 x2)
: Lemma (prf1 == prf2)
= ()

let morph_compose1_irrelevant (pa: pcm 'a) (pb: pcm 'b) (morph: 'a ^-> 'b) (x1: 'a)
  (prf1 prf2: morph_compose1 pa pb morph x1)
: Lemma (prf1 == prf2)
= assert (prf1 `feq` prf2)

let morph_compose_irrelevant (pa: pcm 'a) (pb: pcm 'b) (morph: 'a ^-> 'b)
  (prf1 prf2: restricted_t 'a (morph_compose1 pa pb morph))
: Lemma (prf1 == prf2)
= let aux (x: 'a): Lemma (prf1 x == prf2 x) [SMTPat (prf1 x)] =
    morph_compose1_irrelevant pa pb morph x (prf1 x) (prf2 x)
  in assert (prf1 `feq` prf2)

let morph_eq (f g: 'p `morphism` 'q)
: Lemma (requires f.morph `feq` g.morph) (ensures f == g)
  [SMTPat (f.morph `feq` g.morph)]
= assert (f.morph == g.morph);
  morph_compose_irrelevant 'p 'q f.morph f.morph_compose g.morph_compose

let morphism_morph_compose
  (#a #b: Type) (#pa: pcm a) (#pb: pcm b) (m: morphism pa pb)
  (x1: a)
  (x2: a)
: Lemma
  (requires (composable pa x1 x2))
  (ensures (composable pb (m.morph x1) (m.morph x2) /\ m.morph (x1 `pa.p.op` x2) == m.morph x1 `pb.p.op` m.morph x2))
  [SMTPat (composable pb (m.morph x1) (m.morph x2))]
= m.morph_compose x1 x2

let morphism_compose (#a #b #c: Type) (#pa: pcm a) (#pb: pcm b) (#pc: pcm c) (fab: morphism pa pb) (fbc: morphism pb pc) : Tot (morphism pa pc) =
  mkmorphism
    (fun x -> fbc.morph (fab.morph x))
    ()
    (fun x1 x2 ->
      fab.morph_compose x1 x2;
      fbc.morph_compose (fab.morph x1) (fab.morph x2))

let compatible_intro
  (#a: Type u#a)
  (pcm: pcm a)
  (x y: a)
  (frame: a)
: Lemma
  (requires (composable pcm x frame /\ op pcm frame x == y))
  (ensures (compatible pcm x y))
= ()

let compatible_elim
  (#a: Type u#a)
  (pcm: pcm a)
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

let compatible_morphism
  (#p: pcm 'a) (#q: pcm 'b)
  (f: p `morphism` q)
  (x y: Ghost.erased 'a)
: Lemma
    (requires compatible p x y)
    (ensures compatible q (f.morph x) (f.morph y))
= let frame_x = compatible_elim p x y in
  f.morph_compose frame_x x;
  compatible_intro q (f.morph x) (f.morph y) (f.morph frame_x)

let injective (#a #b: Type) (f: (a -> Tot b)) : Tot prop =
  (forall x1 x2 . {:pattern f x1; f x2} f x1 == f x2 ==> x1 == x2)

let is_inverse_of (#a #b: Type) (g: (b -> Tot a)) (f: (a -> Tot b)) : Tot prop =
  (forall x . {:pattern (g (f x))} g (f x) == x)

let is_inverse_of_injective (#a #b: Type) (g: (b -> Tot a)) (f: (a -> Tot b))
  x1 x2
: Lemma
  (requires (g `is_inverse_of` f /\ f x1 == f x2))
  (ensures (x1 == x2))
  [SMTPat (g `is_inverse_of` f); SMTPat (f x1); SMTPat (f x2)]
= assert (g (f x1) == g (f x2))

#push-options "--print_universes"

let fpu_lift_dom (#t_large:Type) (#t_small: Type) (#p_large: pcm t_large) (#p_small: pcm t_small)
  (conn_small_to_large: morphism p_small p_large)
= (x:(x:Ghost.erased t_small{~ (Ghost.reveal x == p_small.p.one)}) &
   y:Ghost.erased t_small &
   frame_preserving_upd p_small x y)

let fpu_lift_cod (#t_large:Type) (#t_small: Type) (#p_large: pcm t_large) (#p_small: pcm t_small)
  (conn_small_to_large: morphism p_small p_large)
: fpu_lift_dom conn_small_to_large -> Type
= fun (|x, y, f|) ->
  frame_preserving_upd p_large (conn_small_to_large.morph x) (conn_small_to_large.morph y)
     
let fpu_lift (#t_large:Type) (#t_small: Type) (p_large: pcm t_large) (p_small: pcm t_small)
  (conn_small_to_large: morphism p_small p_large)
: Type
= restricted_t
    (fpu_lift_dom conn_small_to_large)
    (fpu_lift_cod conn_small_to_large)

noeq
type connection (#t_large #t_small: Type) (p_large: pcm t_large) (p_small: pcm t_small) = {
  conn_small_to_large: morphism p_small p_large;
  conn_large_to_small: morphism p_large p_small;
  conn_small_to_large_inv: squash (conn_large_to_small.morph `is_inverse_of` conn_small_to_large.morph);
  conn_lift_frame_preserving_upd: fpu_lift p_large p_small conn_small_to_large;
}

let mkconnection (#t_large #t_small: Type) (#p_large: pcm t_large) (#p_small: pcm t_small)
  (conn_small_to_large: morphism p_small p_large)
  (conn_large_to_small: morphism p_large p_small)
  (conn_small_to_large_inv:
    squash (conn_large_to_small.morph `is_inverse_of` conn_small_to_large.morph))
  (conn_lift_frame_preserving_upd:
    (x:(x:Ghost.erased t_small{~ (Ghost.reveal x == p_small.p.one)}) ->
     y:Ghost.erased t_small ->
     frame_preserving_upd p_small x y ->
     frame_preserving_upd p_large (conn_small_to_large.morph x) (conn_small_to_large.morph y)))
: connection p_large p_small = {
  conn_small_to_large = conn_small_to_large;
  conn_large_to_small = conn_large_to_small;
  conn_small_to_large_inv = conn_small_to_large_inv;
  conn_lift_frame_preserving_upd =
    on_domain
      (fpu_lift_dom conn_small_to_large)
      (fun (z: fpu_lift_dom conn_small_to_large) ->
        let (|x, y, f|) = z in
	conn_lift_frame_preserving_upd x y f <: fpu_lift_cod conn_small_to_large z)
}

let connection_eq (l m: 'p `connection` 'q)
: Lemma
    (requires l.conn_small_to_large.morph `feq` m.conn_small_to_large.morph /\
              l.conn_large_to_small.morph `feq` m.conn_large_to_small.morph /\
              l.conn_lift_frame_preserving_upd `feq` m.conn_lift_frame_preserving_upd)
    (ensures l == m)
= ()

let connection_compose (#a #b #c: Type) (#pa: pcm a) (#pb: pcm b) (#pc: pcm c) (fab: connection pa pb) (fbc: connection pb pc) : Tot (connection pa pc) =
  mkconnection
    (fbc.conn_small_to_large `morphism_compose` fab.conn_small_to_large)
    (fab.conn_large_to_small `morphism_compose` fbc.conn_large_to_small)
    ()
    (fun xc yc f ->
    let xb = Ghost.hide (fbc.conn_small_to_large.morph xc) in
    let yb = Ghost.hide (fbc.conn_small_to_large.morph yc) in
    let xa = Ghost.hide (fab.conn_small_to_large.morph xb) in
    let ya = Ghost.hide (fab.conn_small_to_large.morph yb) in
    fab.conn_lift_frame_preserving_upd (|xb, yb, fbc.conn_lift_frame_preserving_upd (|xc, yc, f|)|))
