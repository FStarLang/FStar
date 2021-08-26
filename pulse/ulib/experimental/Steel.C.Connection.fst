module Steel.C.Connection

open Steel.C.PCM
open FStar.FunctionalExtensionality

let morph_compose2 (pa: pcm 'a) (pb: pcm 'b) (morph: 'a -> 'b)
  (x1: 'a) (x2: 'a{composable pa x1 x2})
= squash (
    composable pb (morph x1) (morph x2) /\
    morph (x1 `op pa` x2) == morph x1 `op pb` morph x2)

let morph_compose1 (pa: pcm 'a) (pb: pcm 'b) (morph: 'a -> 'b) (x1: 'a) =
  restricted_t (x2:'a{composable pa x1 x2}) (morph_compose2 pa pb morph x1)

noeq
type morphism (#a #b: Type) (pa: pcm a) (pb: pcm b) = {
  morph: (a ^-> b);
  morph_unit: squash (morph (one pa) == one pb);
  morph_compose: restricted_t a (morph_compose1 pa pb morph);
}

let mkmorphism (#pa: pcm 'a) (#pb: pcm 'b) (morph: 'a -> 'b)
  (morph_unit: squash (morph (one pa) == one pb))
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
  (ensures (composable pb (m.morph x1) (m.morph x2) /\ m.morph (x1 `op pa` x2) == m.morph x1 `op pb` m.morph x2))
  [SMTPat (composable pb (m.morph x1) (m.morph x2))]
= m.morph_compose x1 x2

let morphism_compose (#a #b #c: Type) (#pa: pcm a) (#pb: pcm b) (#pc: pcm c) (fab: morphism pa pb) (fbc: morphism pb pc) : Tot (morphism pa pc) =
  mkmorphism
    (fun x -> fbc.morph (fab.morph x))
    ()
    (fun x1 x2 ->
      fab.morph_compose x1 x2;
      fbc.morph_compose (fab.morph x1) (fab.morph x2))

let morphism_id
  (#a: Type)
  (p: pcm a)
: Tot (morphism p p)
= mkmorphism
    (fun x -> x)
    ()
    (fun _ _ -> ())

let morphism_compose_id_left
  (#a #b: Type) (#pa: pcm a) (#pb: pcm b)  
  (m: morphism pa pb)
: Lemma
  (morphism_id pa `morphism_compose` m == m)
= morph_eq (morphism_id pa `morphism_compose` m) m

let morphism_compose_id_right
  (#a #b: Type) (#pa: pcm a) (#pb: pcm b)  
  (m: morphism pa pb)
: Lemma
  (m `morphism_compose` morphism_id pb == m)
= morph_eq (m `morphism_compose` morphism_id pb) m

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

let restricted_frame_preserving_upd
  (#a:Type u#a) (p:pcm a) (x y:a)
=
  restricted_t
    (frame_preserving_upd_dom p x)
    (frame_preserving_upd_codom p x y)

let restricted_frame_preserving_upd_intro
  (#a:Type u#a) (#p:pcm a) (#x #y: Ghost.erased a)
  (f: frame_preserving_upd p x y)
: Tot (restricted_frame_preserving_upd p x y)
=
  on_dom
    (frame_preserving_upd_dom p x)
    #(frame_preserving_upd_codom p x y)
    (fun v -> f v)

let restricted_frame_preserving_upd_elim
  (#a:Type u#a) (#p:pcm a) (#x #y: Ghost.erased a)
  (f: restricted_frame_preserving_upd p x y)
: Tot (frame_preserving_upd p x y)
= f

let fpu_lift_dom (#t_small: Type) (p_small: pcm t_small)
= (x:(x:Ghost.erased t_small{~ (Ghost.reveal x == (one p_small))}) &
   y:Ghost.erased t_small &
   restricted_frame_preserving_upd p_small x y)

let fpu_lift_cod (#t_large:Type) (#t_small: Type) (#p_large: pcm t_large) (#p_small: pcm t_small)
  (conn_small_to_large: morphism p_small p_large)
: fpu_lift_dom p_small -> Type
= fun (|x, y, f|) ->
  restricted_frame_preserving_upd p_large (conn_small_to_large.morph x) (conn_small_to_large.morph y)

let fpu_lift (#t_large:Type) (#t_small: Type) (#p_large: pcm t_large) (#p_small: pcm t_small)
  (conn_small_to_large: morphism p_small p_large)
: Type
= restricted_t
    (fpu_lift_dom p_small)
    (fpu_lift_cod conn_small_to_large)

let fpu_lift_elim (#t_large:Type) (#t_small: Type) (#p_large: pcm t_large) (#p_small: pcm t_small)
  (#conn_small_to_large: morphism p_small p_large)
  (lift: fpu_lift conn_small_to_large)
  (x: Ghost.erased t_small { ~ (Ghost.reveal x == one p_small) })
  (y: Ghost.erased t_small)
  (f: frame_preserving_upd p_small x y)
: Tot (frame_preserving_upd p_large (conn_small_to_large.morph x) (conn_small_to_large.morph y))
= lift (| x, y, restricted_frame_preserving_upd_intro f |)

noeq
type connection (#t_large #t_small: Type) (p_large: pcm t_large) (p_small: pcm t_small) = {
  conn_small_to_large: morphism p_small p_large;
  conn_large_to_small: morphism p_large p_small;
  conn_small_to_large_inv: squash (conn_large_to_small.morph `is_inverse_of` conn_small_to_large.morph);
  conn_lift_frame_preserving_upd: fpu_lift conn_small_to_large;
}

let mkconnection0 (#t_large #t_small: Type) (#p_large: pcm t_large) (#p_small: pcm t_small)
  (conn_small_to_large: morphism p_small p_large)
  (conn_large_to_small: morphism p_large p_small)
  (conn_small_to_large_inv:
    squash (conn_large_to_small.morph `is_inverse_of` conn_small_to_large.morph))
  (conn_lift_frame_preserving_upd:
    (x:(x:Ghost.erased t_small{~ (Ghost.reveal x == (one p_small))}) ->
     y:Ghost.erased t_small ->
     restricted_frame_preserving_upd p_small x y ->
     restricted_frame_preserving_upd p_large (conn_small_to_large.morph x) (conn_small_to_large.morph y)))
: connection p_large p_small = {
  conn_small_to_large = conn_small_to_large;
  conn_large_to_small = conn_large_to_small;
  conn_small_to_large_inv = conn_small_to_large_inv;
  conn_lift_frame_preserving_upd =
    on_domain
      (fpu_lift_dom p_small)
      (fun (z: fpu_lift_dom p_small) ->
        let (|x, y, f|) = z in
	conn_lift_frame_preserving_upd x y f <: fpu_lift_cod conn_small_to_large z)
}

let mkconnection (#t_large #t_small: Type) (#p_large: pcm t_large) (#p_small: pcm t_small)
  (conn_small_to_large: morphism p_small p_large)
  (conn_large_to_small: morphism p_large p_small)
  (conn_small_to_large_inv:
    squash (conn_large_to_small.morph `is_inverse_of` conn_small_to_large.morph))
  (conn_lift_frame_preserving_upd:
    (x:(x:Ghost.erased t_small{~ (Ghost.reveal x == (one p_small))}) ->
     y:Ghost.erased t_small ->
     frame_preserving_upd p_small x y ->
     frame_preserving_upd p_large (conn_small_to_large.morph x) (conn_small_to_large.morph y)))
: connection p_large p_small =
  mkconnection0
    conn_small_to_large
    conn_large_to_small
    conn_small_to_large_inv
    (fun x y f ->
      restricted_frame_preserving_upd_intro (conn_lift_frame_preserving_upd x y f))

let connection_eq #a (#p: pcm a) #b (#q: pcm b) (l m: p `connection` q)
: Lemma
    (requires l.conn_small_to_large.morph `feq` m.conn_small_to_large.morph /\
              l.conn_large_to_small.morph `feq` m.conn_large_to_small.morph /\
              l.conn_lift_frame_preserving_upd `feq` m.conn_lift_frame_preserving_upd)
    (ensures l == m)
= ()

let connection_compose (#a #b #c: Type) (#pa: pcm a) (#pb: pcm b) (#pc: pcm c) (fab: connection pa pb) (fbc: connection pb pc) : Tot (connection pa pc) =
  mkconnection0
    (fbc.conn_small_to_large `morphism_compose` fab.conn_small_to_large)
    (fab.conn_large_to_small `morphism_compose` fbc.conn_large_to_small)
    ()
    (fun xc yc f ->
    let xb = Ghost.hide (fbc.conn_small_to_large.morph xc) in
    let yb = Ghost.hide (fbc.conn_small_to_large.morph yc) in
    let fb = fbc.conn_lift_frame_preserving_upd (| xc, yc, f |) in
    fab.conn_lift_frame_preserving_upd (| xb, yb, fb |) )

let connection_id
  (#a: Type)
  (p: pcm a)
: Tot (connection p p)
= mkconnection0
    (morphism_id p)
    (morphism_id p)
    ()
    (fun _ _ f -> f)

let connection_compose_id_left
  (#t_large #t_small: Type) (#p_large: pcm t_large) (#p_small: pcm t_small)
  (c: connection p_large p_small)
: Lemma
  (connection_id p_large `connection_compose` c == c)
= connection_eq (connection_id p_large `connection_compose` c) c

let connection_compose_id_right
  (#t_large #t_small: Type) (#p_large: pcm t_large) (#p_small: pcm t_small)
  (c: connection p_large p_small)
: Lemma
  (c `connection_compose` connection_id p_small == c)
= connection_eq (c `connection_compose` connection_id p_small) c

#push-options "--z3rlimit 32"

let connection_compose_assoc
  (#t1 #t2 #t3 #t4: Type)
  (#p1: pcm t1)
  (#p2: pcm t2)
  (#p3: pcm t3)
  (#p4: pcm t4)
  (c12: connection p1 p2)
  (c23: connection p2 p3)
  (c34: connection p3 p4)
: Lemma
  ((c12 `connection_compose` c23) `connection_compose` c34 == c12 `connection_compose` (c23 `connection_compose` c34))
=
  ((c12 `connection_compose` c23) `connection_compose` c34) `connection_eq` (c12 `connection_compose` (c23 `connection_compose` c34))

#pop-options

let morph_refine (pa: pcm 'a) (pb: pcm 'b) (morph: 'a -> 'b)
  (xa: 'a { p_refine pa xa })
= squash (
    p_refine pb (morph xa)
  )

noeq
type isomorphism (#t1 #t2: Type) (p1: pcm t1) (p2: pcm t2) = {
  iso_1_2: morphism p1 p2;
  iso_2_1: morphism p2 p1;
  iso_1_2_inv_2_1: squash (iso_1_2.morph `is_inverse_of` iso_2_1.morph);
  iso_2_1_inv_1_2: squash (iso_2_1.morph `is_inverse_of` iso_1_2.morph);
  iso_1_2_refine: restricted_t (x1: t1 { p_refine p1 x1 }) (morph_refine p1 p2 iso_1_2.morph);
  iso_2_1_refine: restricted_t (x2: t2 { p_refine p2 x2 }) (morph_refine p2 p1 iso_2_1.morph);
}

let isomorphism_eq
  (#t1 #t2: Type) (#p1: pcm t1) (#p2: pcm t2) (i i': isomorphism p1 p2)
: Lemma
  (requires (
    i.iso_1_2.morph `feq` i'.iso_1_2.morph /\
    i.iso_2_1.morph `feq` i'.iso_2_1.morph
  ))
  (ensures (
    i == i'
  ))
= assert (i.iso_1_2_refine `feq` i'.iso_1_2_refine);
  assert (i.iso_2_1_refine `feq` i'.iso_2_1_refine)

let mkisomorphism
  (#t1 #t2: Type) (#p1: pcm t1) (#p2: pcm t2)
  (iso_1_2: morphism p1 p2)
  (iso_2_1: morphism p2 p1)
  (iso_1_2_inv_2_1: squash (iso_1_2.morph `is_inverse_of` iso_2_1.morph))
  (iso_2_1_inv_1_2: squash (iso_2_1.morph `is_inverse_of` iso_1_2.morph))
  (iso_1_2_refine:
    (x1: t1) ->
    Lemma
    (requires (p_refine p1 x1))
    (ensures (p_refine p2 (iso_1_2.morph x1)))
  )
  (iso_2_1_refine:
    (x2: t2) ->
    Lemma
    (requires (p_refine p2 x2))
    (ensures (p_refine p1 (iso_2_1.morph x2)))
  )
: Tot (isomorphism p1 p2)
= {
  iso_1_2 = iso_1_2;
  iso_2_1 = iso_2_1;
  iso_1_2_inv_2_1 = iso_1_2_inv_2_1;
  iso_2_1_inv_1_2 = iso_2_1_inv_1_2;
  iso_1_2_refine = on_dom (x1: t1 { p_refine p1 x1 }) #(morph_refine p1 p2 iso_1_2.morph) (fun x1 -> iso_1_2_refine x1);
  iso_2_1_refine = on_dom (x2: t2 { p_refine p2 x2 }) #(morph_refine p2 p1 iso_2_1.morph) (fun x2 -> iso_2_1_refine x2);
}

let isomorphism_id
  (#t: Type)
  (p: pcm t)
: Tot (isomorphism p p)
= mkisomorphism
    (morphism_id p)
    (morphism_id p)
    ()
    ()
    (fun _ -> ())
    (fun _ -> ())

let isomorphism_inverse
  (#t1 #t2: Type) (#p1: pcm t1) (#p2: pcm t2)
  (i: isomorphism p1 p2)
: Tot (isomorphism p2 p1)
= {
  iso_1_2 = i.iso_2_1;
  iso_2_1 = i.iso_1_2;
  iso_1_2_inv_2_1 = i.iso_2_1_inv_1_2;
  iso_2_1_inv_1_2 = i.iso_1_2_inv_2_1;
  iso_1_2_refine = i.iso_2_1_refine;
  iso_2_1_refine = i.iso_1_2_refine;
}

let isomorphism_inverse_involutive
  (#t1 #t2: Type) (#p1: pcm t1) (#p2: pcm t2)
  (i: isomorphism p1 p2)
: Lemma
  (isomorphism_inverse (isomorphism_inverse i) == i)
= isomorphism_inverse (isomorphism_inverse i) `isomorphism_eq` i

let connection_of_isomorphism_fpu'
  (#t1 #t2: Type)
  (#p1: pcm t1)
  (#p2: pcm t2)
  (i: isomorphism p1 p2)
  (x: Ghost.erased t2 { ~ (Ghost.reveal x == one p2) })
  (y: Ghost.erased t2)
  (f: restricted_frame_preserving_upd p2 x y)
  (v: frame_preserving_upd_dom p1 (i.iso_2_1.morph x))
: Tot t1
=
  let x1 = Ghost.hide (i.iso_2_1.morph x) in
  compatible_morphism i.iso_1_2 x1 v;
  i.iso_1_2_refine v;
  let v2' = f (i.iso_1_2.morph v) in
  let v' = i.iso_2_1.morph v2' in
  v'

let connection_of_isomorphism_fpu'_correct
  (#t1 #t2: Type)
  (#p1: pcm t1)
  (#p2: pcm t2)
  (i: isomorphism p1 p2)
  (x: Ghost.erased t2 { ~ (Ghost.reveal x == one p2) })
  (y: Ghost.erased t2)
  (f: restricted_frame_preserving_upd p2 x y)
  (v: frame_preserving_upd_dom p1 (i.iso_2_1.morph x))
: Lemma
  (
    let x1 = i.iso_2_1.morph x in
    let y1 = i.iso_2_1.morph y in
    let v_new = connection_of_isomorphism_fpu' i x y f v in
    p_refine p1 v_new /\
    compatible p1 y1 v_new /\
    (forall (frame: _ {composable p1 x1 frame}).{:pattern composable p1 x1 frame}
       composable p1 y1 frame /\
       (op p1 x1 frame == v ==> op p1 y1 frame == v_new))
  )
=
  let x1 = Ghost.hide (i.iso_2_1.morph x) in
  compatible_morphism i.iso_1_2 x1 v;
  i.iso_1_2_refine v;
  let v2' = f (i.iso_1_2.morph v) in
  let v' = i.iso_2_1.morph v2' in
  i.iso_2_1_refine v2' ;
  assert (p_refine p1 v');
  compatible_morphism i.iso_2_1 y v2' ;
  let y1 = Ghost.hide (i.iso_2_1.morph y) in
  assert (compatible p1 y1 v');
  let aux
    (frame: t1 { composable p1 x1 frame })
  : Lemma
    (composable p1 y1 frame /\
    (op p1 x1 frame == v ==> op p1 y1 frame == v'))
    [SMTPat (composable p1 x1 frame)]
  =
    let frame2 = i.iso_1_2.morph frame in
    assert (composable p2 x frame2);
    assert (composable p1 y1 (i.iso_2_1.morph frame2));
    ()
  in
  ()

let connection_of_isomorphism_fpu
  (#t1 #t2: Type)
  (#p1: pcm t1)
  (#p2: pcm t2)
  (i: isomorphism p1 p2)
  (x: Ghost.erased t2 { ~ (Ghost.reveal x == one p2) })
  (y: Ghost.erased t2)
  (f: restricted_frame_preserving_upd p2 x y)
: Tot (restricted_frame_preserving_upd p1 (i.iso_2_1.morph x) (i.iso_2_1.morph y))
=
  Classical.forall_intro (connection_of_isomorphism_fpu'_correct i x y f);
  restricted_frame_preserving_upd_intro #_ #p1 #(i.iso_2_1.morph x) #(i.iso_2_1.morph y) (fun z -> connection_of_isomorphism_fpu' i x y f z)

let connection_of_isomorphism_fpu_inverse'
  (#t1 #t2: Type)
  (#p1: pcm t1)
  (#p2: pcm t2)
  (i: isomorphism p1 p2)
  (x: Ghost.erased t2 { ~ (Ghost.reveal x == one p2) })
  (y: Ghost.erased t2)
  (f: restricted_frame_preserving_upd p2 x y)
  (v: frame_preserving_upd_dom p2 x)
: Lemma
  (connection_of_isomorphism_fpu (isomorphism_inverse i) (i.iso_2_1.morph x) (i.iso_2_1.morph y) (connection_of_isomorphism_fpu i x y f) v == f v)
= compatible_morphism i.iso_2_1 x v;
  i.iso_2_1_refine v

let connection_of_isomorphism_fpu_inverse
  (#t1 #t2: Type)
  (#p1: pcm t1)
  (#p2: pcm t2)
  (i: isomorphism p1 p2)
  (x: Ghost.erased t2 { ~ (Ghost.reveal x == one p2) })
  (y: Ghost.erased t2)
  (f: restricted_frame_preserving_upd p2 x y)
: Lemma
  (connection_of_isomorphism_fpu (isomorphism_inverse i) (i.iso_2_1.morph x) (i.iso_2_1.morph y) (connection_of_isomorphism_fpu i x y f) == f)
= Classical.forall_intro (connection_of_isomorphism_fpu_inverse' i x y f);
  assert (connection_of_isomorphism_fpu (isomorphism_inverse i) (i.iso_2_1.morph x) (i.iso_2_1.morph y) (connection_of_isomorphism_fpu i x y f) `feq` f)

let connection_of_isomorphism
  (#t1 #t2: Type)
  (#p1: pcm t1)
  (#p2: pcm t2)
  (i: isomorphism p1 p2)
: Tot (connection p1 p2)
= mkconnection0
    i.iso_2_1
    i.iso_1_2
    i.iso_1_2_inv_2_1
    (connection_of_isomorphism_fpu i)

let connection_of_isomorphism_inverse_left
  (#t1 #t2: Type)
  (#p1: pcm t1)
  (#p2: pcm t2)
  (i: isomorphism p1 p2)
: Lemma
  (connection_of_isomorphism (isomorphism_inverse i) `connection_compose` connection_of_isomorphism i == connection_id _)
= Classical.forall_intro_3 (connection_of_isomorphism_fpu_inverse i);
  (connection_of_isomorphism (isomorphism_inverse i) `connection_compose` connection_of_isomorphism i) `connection_eq` connection_id _

let connection_of_isomorphism_inverse_right
  (#t1 #t2: Type)
  (#p1: pcm t1)
  (#p2: pcm t2)
  (i: isomorphism p1 p2)
: Lemma
  (connection_of_isomorphism i `connection_compose` connection_of_isomorphism (isomorphism_inverse i) == connection_id _)
= isomorphism_inverse_involutive i;
  connection_of_isomorphism_inverse_left (isomorphism_inverse i)
