module Steel.ST.C.Model.Struct
open Steel.ST.Util

module P = FStar.PCM
open Steel.C.Model.PCM
open Steel.C.Model.Connection
open Steel.ST.C.Model.Ref

(** A PCM for structs *)

/// We can generalize to 'a-ary products (k:'a -> 'b k), given a PCM for each k:

open FStar.FunctionalExtensionality
open FStar.Classical
let ext (f g: restricted_t 'a 'b) (fg:(x:'a -> Lemma (f x == g x))) : Lemma (f == g) =
  extensionality 'a 'b f g;
  forall_intro fg

let prod_comp (p:(k:'a -> pcm ('b k))) (x y: restricted_t 'a 'b): prop =
  forall k. composable (p k) (x k) (y k)

let prod_op (p:(k:'a -> pcm ('b k)))
  (x: restricted_t 'a 'b) (y: restricted_t 'a 'b{prod_comp p x y})
: restricted_t 'a 'b
= on_domain 'a (fun k -> op (p k) (x k) (y k) <: 'b k)

let prod_one (p:(k:'a -> pcm ('b k))): restricted_t 'a 'b =
  on_domain 'a (fun k -> one (p k))

let prod_comm (p:(k:'a -> pcm ('b k)))
  (x: restricted_t 'a 'b) (y: restricted_t 'a 'b{prod_comp p x y})
: Lemma (prod_op p x y == prod_op p y x)
= ext (prod_op p x y) (prod_op p y x) (fun k -> ())

let prod_assoc (p:(k:'a -> pcm ('b k)))
  (x y: restricted_t 'a 'b)
  (z: restricted_t 'a 'b{prod_comp p y z /\ prod_comp p x (prod_op p y z)})
: Lemma (prod_comp p x y /\
         prod_comp p (prod_op p x y) z /\
         prod_op p x (prod_op p y z) == prod_op p (prod_op p x y) z)
= let aux k
  : Lemma (composable (p k) (x k) (y k) /\
           composable (p k) (op (p k) (x k) (y k)) (z k)) 
    [SMTPat (p k)]
  = ()
  in
  ext (prod_op p x (prod_op p y z)) (prod_op p (prod_op p x y) z)
    (fun k -> ())

let prod_assoc_r (p:(k:'a -> pcm ('b k)))
  (x y: restricted_t 'a 'b)
  (z: restricted_t 'a 'b{prod_comp p x y /\ prod_comp p (prod_op p x y) z})
: Lemma (prod_comp p y z /\
         prod_comp p x (prod_op p y z) /\
         prod_op p x (prod_op p y z) == prod_op p (prod_op p x y) z)
= let aux k
  : Lemma (composable (p k) (y k) (z k) /\
           composable (p k) (x k) (op (p k) (y k) (z k)))
    [SMTPat (p k)]
  = ()
  in
  ext (prod_op p x (prod_op p y z)) (prod_op p (prod_op p x y) z)
    (fun k -> ())

let prod_is_unit (p:(k:'a -> pcm ('b k))) (x: restricted_t 'a 'b)
: Lemma (prod_comp p x (prod_one p) /\
         prod_op p x (prod_one p) == x)
= let is_unit k
  : Lemma (composable (p k) (x k) (prod_one p k))
    [SMTPat (p k)]
  = ()
  in ext (prod_op p x (prod_one p)) x (fun k -> ())

let prod_refine (p:(k:'a -> pcm ('b k))) (x: restricted_t 'a 'b): prop =
  (exists (k: 'a). True) /\ (forall k. p_refine (p k) (x k))

let fstar_prod_pcm (p:(k:'a -> pcm ('b k))): P.pcm (restricted_t 'a 'b) = let open P in {
  comm = prod_comm p;
  p = {composable = prod_comp p; op = prod_op p; one = prod_one p};
  assoc = prod_assoc p;
  assoc_r = prod_assoc_r p;
  is_unit = prod_is_unit p;
  refine = prod_refine p
}

let prod_pcm' (p:(k:'a -> pcm ('b k))): pcm0 (restricted_t 'a 'b) = pcm_of_fstar_pcm (fstar_prod_pcm p)

let prod_pcm (p:(k:'a -> pcm ('b k))): pcm (restricted_t 'a 'b) =
  let p' = prod_pcm' p in
  assert (forall x y . (composable p' x y /\ op p' x y == one p') ==> (
    x `feq` one p' /\ y `feq` one p'
  ));
  assert (forall x frame . (prod_refine p x /\ prod_comp p x frame) ==> frame `feq` prod_one p);
  prod_pcm' p

let prod_pcm_ext
  (#a: Type)
  (#b: (a -> Type))
  (p1 p2: ((k: a) -> pcm (b k)))
  (p_eq: (
    (k: a) ->
    Lemma
    (p1 k == p2 k)
  ))
: Lemma
  (prod_pcm p1 == prod_pcm p2)
= Classical.forall_intro p_eq;
  pcm0_ext (prod_pcm p1) (prod_pcm p2)
    (fun x y -> ())
    (fun x y -> assert (op (prod_pcm p1) x y `feq` op (prod_pcm p2) x y))
    (fun _ -> ())
    (assert (one (prod_pcm p1) `feq` one (prod_pcm p2)))

let prod_pcm_composable_intro0
  (p:(k:'a -> pcm ('b k)))
  (x y: restricted_t 'a 'b)
: Lemma
  ((composable (prod_pcm p) x y <==> prod_comp p x y) /\
  (composable (prod_pcm p) x y ==> op (prod_pcm p) x y == prod_op p x y))
  [SMTPat (composable (prod_pcm p) x y)]
= ()

let prod_pcm_composable_intro (p:(k:'a -> pcm ('b k))) (x y: restricted_t 'a 'b)
  (h:(k:'a -> Lemma (composable (p k) (x k) (y k))))
: Lemma (composable (prod_pcm p) x y) = FStar.Classical.forall_intro h

let field_to_struct_f
  (#a: eqtype)
  (#b: a -> Type)
  (p:(k: a -> pcm (b k)))
  (k: a)
  (x: b k)
: Pure (restricted_t a b)
  (requires True)
  (ensures (fun y -> forall k' . y k' == (if k' = k then (x <: b k') else one (p k'))))
= on_dom a (fun k' -> if k' = k then (x <: b k') else one (p k'))

let field_to_struct
  (#a: eqtype)
  (#b: a -> Type)
  (p:(k: a -> pcm (b k)))
  (k: a)
: Tot (morphism (p k) (prod_pcm p))
= mkmorphism
    (field_to_struct_f p k)
    (assert (field_to_struct_f p k (one (p k)) `feq` one (prod_pcm p)))
    (fun x1 x2 ->
      Classical.forall_intro_2 (fun k -> is_unit (p k));
      assert (prod_op p (field_to_struct_f p k x1) (field_to_struct_f p k x2) `feq` field_to_struct_f p k (op (p k) x1 x2));
        ())

let struct_to_field_f
  (#a: Type)
  (#b: a -> Type)
  (p:(k: a -> pcm (b k)))
  (k: a)
  (x: restricted_t a b)
: Tot (b k)
= x k

let struct_to_field
  (#a: Type)
  (#b: a -> Type)
  (p:(k: a -> pcm (b k)))
  (k: a)
: Tot (morphism (prod_pcm p) (p k))
= mkmorphism
    (struct_to_field_f p k) ()
    (fun x1 x2 -> ())

let struct_field_lift_fpu'
  (#a: eqtype)
  (#b: a -> Type)
  (p:(k: a -> pcm (b k)))
  (k: a)
  (x: Ghost.erased (b k) { ~ (Ghost.reveal x == one (p k)) })
  (y: Ghost.erased (b k))
  (f: frame_preserving_upd (p k) x y)
  (v: restricted_t a b {
    p_refine (prod_pcm p) v /\
    compatible (prod_pcm p) ((field_to_struct p k).morph x) v
  })
: Tot (restricted_t a b)
= 
    on_dom a (fun k' ->
      if k' = k
      then f (v k) <: b k'
      else v k'
    )

#push-options "--query_stats --z3rlimit 30"
#restart-solver

let struct_field_lift_fpu_prf
  (#a: eqtype)
  (#b: a -> Type)
  (p:(k: a -> pcm (b k)))
  (k: a)
  (x: Ghost.erased (b k) { ~ (Ghost.reveal x == one (p k)) })
  (y: Ghost.erased (b k))
  (f: frame_preserving_upd (p k) x y)
  (v: restricted_t a b {
    p_refine (prod_pcm p) v /\
    compatible (prod_pcm p) ((field_to_struct p k).morph x) v
  })
: Lemma
  (let v_new = struct_field_lift_fpu' p k x y f v in
    p_refine (prod_pcm p) v_new /\
    compatible (prod_pcm p) ((field_to_struct p k).morph y) v_new /\
    (forall (frame:_{composable (prod_pcm p) ((field_to_struct p k).morph x) frame}).
       composable (prod_pcm p) ((field_to_struct p k).morph y) frame /\
       (op (prod_pcm p) ((field_to_struct p k).morph x) frame == v ==> op (prod_pcm p) ((field_to_struct p k).morph y) frame == v_new))
  )
=
  let y' = (field_to_struct p k).morph y in
  let v_new = struct_field_lift_fpu' p k x y f v in
  Classical.forall_intro_2 (fun k -> is_unit (p k));
  assert (forall (frame: b k) .
    (composable (p k) y frame /\ op (p k) frame y == f (v k)) ==> (
    let frame' : restricted_t a b = on_dom a (fun k' -> if k' = k then (frame <: b k') else v_new k') in
    composable (prod_pcm p) y' frame' /\
    op (prod_pcm p) frame' y' `feq` v_new
  ));
  assert (compatible (prod_pcm p) y' v_new);
  assert (forall (frame:_{composable (prod_pcm p) ((field_to_struct p k).morph x) frame}).
       composable (prod_pcm p) ((field_to_struct p k).morph y) frame /\
       (op (prod_pcm p) ((field_to_struct p k).morph x) frame == v ==> op (prod_pcm p) ((field_to_struct p k).morph y) frame `feq` v_new));
  ()

#pop-options

let struct_field_lift_fpu
  (#a: eqtype)
  (#b: a -> Type)
  (p:(k: a -> pcm (b k)))
  (k: a)
  (x: Ghost.erased (b k) { ~ (Ghost.reveal x == one (p k)) })
  (y: Ghost.erased (b k))
  (f: frame_preserving_upd (p k) x y)
: Tot (frame_preserving_upd (prod_pcm p) ((field_to_struct p k).morph x) ((field_to_struct p k).morph y))
= fun v ->
    struct_field_lift_fpu_prf p k x y f v;
    struct_field_lift_fpu' p k x y f v

let struct_field
  (#a: eqtype)
  (#b: a -> Type u#b)
  (p:(k: a -> pcm (b k)))
  (k: a)
: Tot (connection (prod_pcm p) (p k))
= mkconnection
    (field_to_struct p k)
    (struct_to_field p k)
    ()
    (struct_field_lift_fpu p k)

#push-options "--split_queries"

#restart-solver
let struct_field_ext
  (#a: eqtype)
  (#b: a -> Type u#b)
  (p1 p2:(k: a -> pcm (b k)))
  (p_eq: (
    (k: a) ->
    Lemma
    (p1 k == p2 k)
  ))
  (k: a)
: Lemma
  (prod_pcm p1 == prod_pcm p2 /\
    p1 k == p2 k /\
    struct_field p1 k === struct_field p2 k
  )
= prod_pcm_ext p1 p2 p_eq;
  p_eq k;
  Classical.forall_intro p_eq;
  let l = struct_field p1 k in
  let m : connection (prod_pcm p1) (p1 k) = coerce_eq () (struct_field p2 k) in
  assert (forall x . field_to_struct_f p1 k x `feq` field_to_struct_f p2 k x);
  connection_eq_gen
    l
    m
    ()
    (fun x y f v ->
      struct_field_lift_fpu_prf p1 k x y f v;
      struct_field_lift_fpu_prf p2 k x y f v;
      assert (forall k' . struct_field_lift_fpu' p1 k x y f v k' == struct_field_lift_fpu' p2 k x y f v k');
      assert (struct_field_lift_fpu' p1 k x y f v == struct_field_lift_fpu' p2 k x y f v);
      assert ((l.conn_lift_frame_preserving_upd ({ fpu_lift_dom_x = x; fpu_lift_dom_y = y; fpu_lift_dom_f = f; })).fpu_f v == (m.conn_lift_frame_preserving_upd ({ fpu_lift_dom_x = x; fpu_lift_dom_y = y; fpu_lift_dom_f = f; })).fpu_f v)
    )

#pop-options

let is_substruct
  (#a: eqtype)
  (#b: a -> Type)
  (p:(k: a -> pcm (b k)))
  (#a': eqtype)
  (#b': (a' -> Type))
  (p': (k: a' -> pcm (b' k)))
  (inj: (a' -> a))
  (surj: (a -> option a'))
: Tot prop
= (forall (k: a') . b' k == b (inj k) /\ p' k == p (inj k)) /\
  (forall (k: a') . surj (inj k) == Some k) /\
  (forall (k: a) . (match surj k with None -> True | Some k' -> inj k' == k))

let substruct_to_struct_f
  (#a: eqtype)
  (#b: a -> Type)
  (p:(k: a -> pcm (b k)))
  (#a': eqtype)
  (#b': (a' -> Type))
  (p': (k: a' -> pcm (b' k)))
  (inj: (a' -> a))
  (surj: (a -> option a'))
  (sq: squash (is_substruct p p' inj surj))
  (x: restricted_t a' b')
: Pure (restricted_t a b)
  (requires True)
  (ensures (fun y -> forall k . y k == (match surj k with Some k' -> (x k' <: b k) | _ -> one (p k))))
= on_dom a (fun k -> match surj k with Some k' -> (x k' <: b k) | _ -> one (p k))

let substruct_to_struct
  (#a: eqtype)
  (#b: a -> Type)
  (p:(k: a -> pcm (b k)))
  (#a': eqtype)
  (#b': (a' -> Type))
  (p': (k: a' -> pcm (b' k)))
  (inj: (a' -> a))
  (surj: (a -> option a'))
  (sq: squash (is_substruct p p' inj surj))
: Tot (morphism (prod_pcm p') (prod_pcm p))
= mkmorphism
    (substruct_to_struct_f p p' inj surj sq)
    (assert (substruct_to_struct_f p p' inj surj sq (one (prod_pcm p')) `feq` one (prod_pcm p)))
    (fun x1 x2 ->
      assert (prod_op p (substruct_to_struct_f p p' inj surj sq x1) (substruct_to_struct_f p p' inj surj sq x2) `feq` substruct_to_struct_f p p' inj surj sq (prod_op p' x1 x2))
    )

let struct_to_substruct_f
  (#a: eqtype)
  (#b: a -> Type)
  (p:(k: a -> pcm (b k)))
  (#a': eqtype)
  (#b': (a' -> Type))
  (p': (k: a' -> pcm (b' k)))
  (inj: (a' -> a))
  (surj: (a -> option a'))
  (sq: squash (is_substruct p p' inj surj))
  (x: restricted_t a b)
: Pure (restricted_t a' b')
  (requires True)
  (ensures (fun y -> forall k . y k == x (inj k)))
= on_dom a' (fun k -> x (inj k) <: b' k)

let struct_to_substruct
  (#a: eqtype)
  (#b: a -> Type)
  (p:(k: a -> pcm (b k)))
  (#a': eqtype)
  (#b': (a' -> Type))
  (p': (k: a' -> pcm (b' k)))
  (inj: (a' -> a))
  (surj: (a -> option a'))
  (sq: squash (is_substruct p p' inj surj))
: Tot (morphism (prod_pcm p) (prod_pcm p'))
= mkmorphism
    (struct_to_substruct_f p p' inj surj sq)
    (assert (struct_to_substruct_f p p' inj surj sq (one (prod_pcm p)) `feq` one (prod_pcm p')))
    (fun x1 x2 ->
      assert (prod_op p' (struct_to_substruct_f p p' inj surj sq x1) (struct_to_substruct_f p p' inj surj sq x2) `feq` struct_to_substruct_f p p' inj surj sq (prod_op p x1 x2))
    )

let substruct_lift_fpu'
  (#a: eqtype)
  (#b: a -> Type)
  (p:(k: a -> pcm (b k)))
  (#a': eqtype)
  (#b': (a' -> Type))
  (p': (k: a' -> pcm (b' k)))
  (inj: (a' -> a))
  (surj: (a -> option a'))
  (sq: squash (is_substruct p p' inj surj))
  (x': Ghost.erased (restricted_t a' b') { ~ (Ghost.reveal x' == one (prod_pcm p')) })
  (y': Ghost.erased (restricted_t a' b'))
  (f': frame_preserving_upd (prod_pcm p') x' y')
  (v: restricted_t a b {
    p_refine (prod_pcm p) v /\
    compatible (prod_pcm p) ((substruct_to_struct p p' inj surj sq).morph x') v
  })
: Tot (restricted_t a b)
= 
    on_dom a (fun k ->
      let v' = ((struct_to_substruct p p' inj surj sq).morph v) in
      let x = Ghost.hide ((substruct_to_struct p p' inj surj sq).morph x') in
      assert (forall frame . (composable (prod_pcm p) x frame /\ op (prod_pcm p) x frame == v) ==> (
        let frame' = (struct_to_substruct p p' inj surj sq).morph frame in
        composable (prod_pcm p') x' frame' /\ op (prod_pcm p') x' frame' `feq` v'
      ));
      assert ((~ (exists (k' : a') . True)) ==> Ghost.reveal x' `feq` one (prod_pcm p'));
      match surj k with
      | Some k' -> f' v' k' <: b k
      | _ -> v k
    )

#push-options "--query_stats --z3rlimit 64 --split_queries"

#restart-solver
let substruct_lift_fpu_prf
  (#a: eqtype)
  (#b: a -> Type)
  (p:(k: a -> pcm (b k)))
  (#a': eqtype)
  (#b': (a' -> Type))
  (p': (k: a' -> pcm (b' k)))
  (inj: (a' -> a))
  (surj: (a -> option a'))
  (sq: squash (is_substruct p p' inj surj))
  (x': Ghost.erased (restricted_t a' b') { ~ (Ghost.reveal x' == one (prod_pcm p')) })
  (y': Ghost.erased (restricted_t a' b'))
  (f': frame_preserving_upd (prod_pcm p') x' y')
  (v: restricted_t a b {
    p_refine (prod_pcm p) v /\
    compatible (prod_pcm p) ((substruct_to_struct p p' inj surj sq).morph x') v
  })
: Lemma
  (let v_new = substruct_lift_fpu' p p' inj surj sq x' y' f' v in
    frame_preserving_upd_post (prod_pcm p)
    ((substruct_to_struct p p' inj surj sq).morph x')
    ((substruct_to_struct p p' inj surj sq).morph y')
    v
    (substruct_lift_fpu' p p' inj surj sq x' y' f' v)
  )
=
  let y = (substruct_to_struct p p' inj surj sq).morph y' in
  let v_new = substruct_lift_fpu' p p' inj surj sq x' y' f' v in
  let v' = ((struct_to_substruct p p' inj surj sq).morph v) in
  let x = Ghost.hide ((substruct_to_struct p p' inj surj sq).morph x') in
  assert (forall frame . (composable (prod_pcm p) x frame /\ op (prod_pcm p) x frame == v) ==> (
    let frame' = (struct_to_substruct p p' inj surj sq).morph frame in
    composable (prod_pcm p') x' frame' /\ op (prod_pcm p') x' frame' `feq` v'
  ));
  assert ((~ (exists (k' : a') . True)) ==> Ghost.reveal x' `feq` one (prod_pcm p'));
  assert (compatible (prod_pcm p') y' (f' v'));
  assert (forall (frame': restricted_t a' b') .
    (composable (prod_pcm p') y' frame' /\ op (prod_pcm p') frame' y' == f' v') ==> (
    let frame : restricted_t a b = on_dom a (fun k -> match surj k with None -> v_new k | Some k' -> frame' k' <: b k) in
    composable (prod_pcm p) y frame /\
    op (prod_pcm p) frame y `feq` v_new
  ));
  assert (compatible (prod_pcm p) y v_new);
  assert (p_refine (prod_pcm p) v_new);
  Classical.forall_intro_2 (fun k -> is_unit (p k));
  let prf (frame: restricted_t a b) : Lemma
    (requires (
      composable (prod_pcm p) x frame
    ))
    (ensures (
      composable (prod_pcm p) x frame /\
      composable (prod_pcm p) y frame /\
      (op (prod_pcm p) x frame == v ==> op (prod_pcm p) y frame `feq` v_new)
    ))
  =
    let frame' = struct_to_substruct_f p p' inj surj sq frame in
    assert (composable (prod_pcm p') x' frame');
    assert (composable (prod_pcm p') y' frame');
    assert (op (prod_pcm p) x frame == v ==> op (prod_pcm p') x' frame' `feq` v');
    ()
  in
  Classical.forall_intro (Classical.move_requires prf)

#pop-options

let substruct_lift_fpu
  (#a: eqtype)
  (#b: a -> Type)
  (p:(k: a -> pcm (b k)))
  (#a': eqtype)
  (#b': (a' -> Type))
  (p': (k: a' -> pcm (b' k)))
  (inj: (a' -> a))
  (surj: (a -> option a'))
  (sq: squash (is_substruct p p' inj surj))
  (x': Ghost.erased (restricted_t a' b') { ~ (Ghost.reveal x' == one (prod_pcm p')) })
  (y': Ghost.erased (restricted_t a' b'))
  (f': frame_preserving_upd (prod_pcm p') x' y')
: Tot (frame_preserving_upd (prod_pcm p) ((substruct_to_struct p p' inj surj sq).morph x') ((substruct_to_struct p p' inj surj sq).morph y'))
= fun v ->
    substruct_lift_fpu_prf p p' inj surj sq x' y' f' v;
    substruct_lift_fpu' p p' inj surj sq x' y' f' v

let substruct
  (#a: eqtype)
  (#b: a -> Type)
  (p:(k: a -> pcm (b k)))
  (#a': eqtype)
  (#b': (a' -> Type))
  (p': (k: a' -> pcm (b' k)))
  (inj: (a' -> a))
  (surj: (a -> option a'))
  (sq: squash (is_substruct p p' inj surj))
: Tot (connection (prod_pcm p) (prod_pcm p'))
= mkconnection
    (substruct_to_struct p p' inj surj sq)
    (struct_to_substruct p p' inj surj sq)
    (assert (forall x .
      struct_to_substruct_f p p' inj surj sq (substruct_to_struct_f p p' inj surj sq x) `feq` x
    ))
    (substruct_lift_fpu p p' inj surj sq)

#push-options "--query_stats --z3rlimit 64"

#restart-solver
let substruct_id
  (#a: eqtype)
  (#b: a -> Type)
  (p:(k: a -> pcm (b k)))
  (inj: (a -> a))
  (surj: (a -> option a))
  (sq: squash (
    (forall x . inj x == x) /\
    (forall x . surj x == Some x)
  ))
: Lemma
  (substruct p p inj surj () == connection_id (prod_pcm p))
= let l = substruct p p inj surj () in
  let m = connection_id (prod_pcm p) in
  let _ : squash (l.conn_small_to_large.morph `feq` m.conn_small_to_large.morph) =
    assert (forall x . l.conn_small_to_large.morph x `feq` m.conn_small_to_large.morph x)
  in
  let _ : squash (l.conn_large_to_small.morph `feq` m.conn_large_to_small.morph) = () in
  connection_eq_gen
    l
    m
    ()
    (fun x y f v ->
      assert ((l.conn_lift_frame_preserving_upd ({ fpu_lift_dom_x = x; fpu_lift_dom_y = y; fpu_lift_dom_f = f; })).fpu_f v `feq` (m.conn_lift_frame_preserving_upd ({ fpu_lift_dom_x = x; fpu_lift_dom_y = y; fpu_lift_dom_f = f; })).fpu_f v)
    )

#pop-options

#push-options "--query_stats --z3rlimit 256"

#restart-solver
let substruct_compose
  (#a1: eqtype)
  (#b1: a1 -> Type)
  (p1:(k: a1 -> pcm (b1 k)))
  (#a2: eqtype)
  (#b2: (a2 -> Type))
  (p2: (k: a2 -> pcm (b2 k)))
  (inj21: (a2 -> a1))
  (surj12: (a1 -> option a2))
  (sq12: squash (is_substruct p1 p2 inj21 surj12))
  (#a3: eqtype)
  (#b3: (a3 -> Type))
  (p3: (k: a3 -> pcm (b3 k)))
  (inj32: (a3 -> a2))
  (surj23: (a2 -> option a3))
  (sq23: squash (is_substruct p2 p3 inj32 surj23))
  (inj31: (a3 -> a1))
  (surj13: (a1 -> option a3))
  (sq13: squash (is_substruct p1 p3 inj31 surj13))
: Lemma
  (requires (
    (forall x3 . inj31 x3 == inj21 (inj32 x3)) /\
    (forall x1 . surj13 x1 == (match surj12 x1 with
    | None -> None
    | Some x2 -> surj23 x2
  ))))
  (ensures (
    substruct p1 p3 inj31 surj13 sq13 ==
      substruct p1 p2 inj21 surj12 sq12 `connection_compose`
      substruct p2 p3 inj32 surj23 sq23
  ))
=
  let c12 = substruct p1 p2 inj21 surj12 sq12 in
  let c23 = substruct p2 p3 inj32 surj23 sq23 in
  let l = substruct p1 p3 inj31 surj13 sq13 in
  let m = connection_compose c12 c23 in
  let _ : squash (l.conn_small_to_large.morph `feq` m.conn_small_to_large.morph) =
    assert (forall x . l.conn_small_to_large.morph x `feq` m.conn_small_to_large.morph x)
  in
  let _ : squash (l.conn_large_to_small.morph `feq` m.conn_large_to_small.morph) =
    assert (forall x . l.conn_large_to_small.morph x `feq` m.conn_large_to_small.morph x)
  in
  connection_eq_gen
    l
    m
    ()
    (fun x y f v ->
      assert ((l.conn_lift_frame_preserving_upd ({ fpu_lift_dom_x = x; fpu_lift_dom_y = y; fpu_lift_dom_f = f; })).fpu_f v `feq` (m.conn_lift_frame_preserving_upd ({ fpu_lift_dom_x = x; fpu_lift_dom_y = y; fpu_lift_dom_f = f; })).fpu_f v)
    )

#pop-options

#push-options "--query_stats --z3rlimit 64"

#restart-solver
let substruct_field
  (#a: eqtype)
  (#b: a -> Type)
  (p:(k: a -> pcm (b k)))
  (#a': eqtype)
  (#b': (a' -> Type))
  (p': (k: a' -> pcm (b' k)))
  (inj: (a' -> a))
  (surj: (a -> option a'))
  (sq: squash (is_substruct p p' inj surj))
  (field': a')
: Lemma
  (substruct p p' inj surj sq `connection_compose` struct_field p' field' ==
    struct_field p (inj field')
  )
=
  let l = substruct p p' inj surj sq `connection_compose` struct_field p' field' in
  let m = struct_field p (inj field') in
  let _ : squash (l.conn_small_to_large.morph `feq` m.conn_small_to_large.morph) =
    assert (forall x . l.conn_small_to_large.morph x `feq` m.conn_small_to_large.morph x)
  in
  let _ : squash (l.conn_large_to_small.morph `feq` m.conn_large_to_small.morph) = () in
  connection_eq_gen
    l
    m
    ()
    (fun x y f v ->
      assert ((l.conn_lift_frame_preserving_upd ({ fpu_lift_dom_x = x; fpu_lift_dom_y = y; fpu_lift_dom_f = f; })).fpu_f v `feq` (m.conn_lift_frame_preserving_upd ({ fpu_lift_dom_x = x; fpu_lift_dom_y = y; fpu_lift_dom_f = f; })).fpu_f v)
    )

#pop-options

let substruct_erase_fields
  (#a: eqtype)
  (#b: a -> Type)
  (p:(k: a -> pcm (b k)))
  (#a': eqtype)
  (surj: (a -> option a'))
  (f: restricted_t a b)
: Tot (restricted_t a b)
= on_dom a (fun x -> if Some? (surj x) then one (p x) else f x)

let substruct_erase_fields_op
  (#a: eqtype)
  (#b: a -> Type)
  (p:(k: a -> pcm (b k)))
  (#a': eqtype)
  (#b': (a' -> Type))
  (p': (k: a' -> pcm (b' k)))
  (inj: (a' -> a))
  (surj: (a -> option a'))
  (sq: squash (is_substruct p p' inj surj))
  (f: restricted_t a b)
: Lemma
  (
    let f_sub = substruct_to_struct_f p p' inj surj sq (struct_to_substruct_f p p' inj surj sq f) in
    let f_rem = substruct_erase_fields p surj f in
    composable (prod_pcm p) f_sub f_rem /\
    op (prod_pcm p) f_sub f_rem `feq` f
  )
= Classical.forall_intro_2 (fun k -> is_unit (p k))

let substruct_composable
  (#a: eqtype)
  (#b: a -> Type)
  (p:(k: a -> pcm (b k)))
  (#a': eqtype)
  (#b': (a' -> Type))
  (p': (k: a' -> pcm (b' k)))
  (inj: (a' -> a))
  (surj: (a -> option a'))
  (sq: squash (is_substruct p p' inj surj))
  (f: restricted_t a b)
  (g': restricted_t a' b')
: Lemma
  (requires (
    forall x' . f (inj x') == one (p' x')
  ))
  (ensures (
    let g = substruct_to_struct_f p p' inj surj sq g' in
    composable (prod_pcm p) f g /\
    (forall x . op (prod_pcm p) f g x == (match surj x with None -> f x | Some x' -> g' x' <: b x))
  ))
= Classical.forall_intro_2 (fun k -> is_unit (p k))

let substruct_pts_to_intro
  (#opened: _)
  (#base: Type)
  (#a: eqtype)
  (#b: a -> Type)
  (p:(k: a -> pcm (b k)))
  (#a': eqtype)
  (#b': (a' -> Type))
  (p': (k: a' -> pcm (b' k)))
  (inj: (a' -> a))
  (surj: (a -> option a'))
  (sq: squash (is_substruct p p' inj surj))
  (r: ref base (prod_pcm p))
  (f: restricted_t a b)
: STGhostT unit opened
    (pts_to r f)
    (fun _ ->
      pts_to r (substruct_erase_fields p surj f) `star`
      pts_to (r `ref_focus` substruct p p' inj surj sq) (struct_to_substruct_f p p' inj surj sq f)
    )
= substruct_erase_fields_op p p' inj surj sq f;
  split r _ (substruct_erase_fields p surj f) (substruct_to_struct_f p p' inj surj sq (struct_to_substruct_f p p' inj surj sq f));
  gfocus r (substruct p p' inj surj sq) (substruct_to_struct_f _ _ _ _ _ _) _

let substruct_pts_to_elim
  (#opened: _)
  (#base: Type)
  (#a: eqtype)
  (#b: a -> Type)
  (p:(k: a -> pcm (b k)))
  (#a': eqtype)
  (#b': (a' -> Type))
  (p': (k: a' -> pcm (b' k)))
  (inj: (a' -> a))
  (surj: (a -> option a'))
  (sq: squash (is_substruct p p' inj surj))
  (r: ref base (prod_pcm p))
  (f: restricted_t a b)
  (g': restricted_t a' b')
: STGhost (Ghost.erased (restricted_t a b)) opened
    (pts_to r f `star` pts_to (r `ref_focus` substruct p p' inj surj sq) g')
    (fun res -> pts_to r res)
    (
      forall x' . f (inj x') == one (p' x')
    )
    (fun res ->
      let g = substruct_to_struct_f p p' inj surj sq g' in
      composable (prod_pcm p) f g /\
      Ghost.reveal res == op (prod_pcm p) f g /\
      (forall x . Ghost.reveal res x == (match surj x with None -> f x | Some x' -> g' x' <: b x))
    )
= substruct_composable p p' inj surj sq f g';
  let g = substruct_to_struct_f p p' inj surj sq g' in
  let res = Ghost.hide (op (prod_pcm p) f g) in
  unfocus (r `ref_focus` _) r (substruct p p' inj surj sq) _;
  let _ = gather r f _ in
  rewrite
    (pts_to r _)
    (pts_to r res);
  res

let exclusive_struct_intro
  (#a: Type)
  (#b: a -> Type)
  (p:(k: a -> pcm (b k)))
  (x: restricted_t a b)
: Lemma
  (requires (
    forall k . exclusive (p k) (struct_to_field_f p k x)
  ))
  (ensures (
    exclusive (prod_pcm p) x
  ))
  [SMTPat (exclusive (prod_pcm p) x)]
=
  assert (forall frame . prod_comp p x frame ==> frame `feq` prod_one p)

let exclusive_struct_elim
  (#a: eqtype)
  (#b: a -> Type)
  (p:(k: a -> pcm (b k)))
  (x: restricted_t a b)
  (k: a)
: Lemma
  (requires (exclusive (prod_pcm p) x))
  (ensures (exclusive (p k) (struct_to_field_f p k x)))
=
  let phi
    frame
  : Lemma
    (requires (composable (p k) (struct_to_field_f p k x) frame))
    (ensures (composable (prod_pcm p) x (field_to_struct_f p k frame)))
    [SMTPat (composable (p k) (struct_to_field_f p k x) frame)]
  = let x' = struct_to_field_f p k x in
    let f' = field_to_struct_f p k frame in
    let psi
      k'
    : Lemma
      (composable (p k') (x k') (f' k'))
      [SMTPat (composable (p k') (x k') (f' k'))]
    = if k' = k
      then ()
      else is_unit (p k') (x k')
    in
    ()
  in
  ()

let struct_without_field (#a:eqtype) (#b: a -> Type u#b) (p:(k:a -> pcm (b k))) (k:a)
  (xs: restricted_t a b)
: restricted_t a b
= on_dom a (fun k' -> if k' = k then one (p k) else xs k')

let struct_peel (#a:eqtype) (#b: a -> Type u#b) (p:(k:a -> pcm (b k))) (k:a)
  (xs: restricted_t a b)
: Lemma (
    composable (prod_pcm p) (struct_without_field p k xs) (field_to_struct_f p k (xs k)) /\
    xs == op (prod_pcm p) (struct_without_field p k xs) (field_to_struct_f p k (xs k)))
= Classical.forall_intro_2 (fun k -> is_unit (p k));
  assert (xs `feq` op (prod_pcm p) (struct_without_field p k xs) (field_to_struct_f p k (xs k)))

let g_addr_of_struct_field
  (#opened: _)
  (#base:Type) (#a:eqtype) (#b: a -> Type u#b) (#p:(k:a -> pcm (b k)))
  (r: ref base (prod_pcm p)) (k:a)
  (xs: Ghost.erased (restricted_t a b))
: STGhostT unit opened
    (r `pts_to` xs)
    (fun _ ->
      (r `pts_to` struct_without_field p k xs) `star` 
      (ref_focus r (struct_field p k) `pts_to` Ghost.reveal xs k))
= struct_peel p k xs;
  split r xs (struct_without_field p k xs) (field_to_struct_f p k (Ghost.reveal xs k));
  rewrite (r `pts_to` _) (r `pts_to` _);
  gfocus r (struct_field p k) (field_to_struct_f p k (Ghost.reveal xs k)) (Ghost.reveal xs k)

let addr_of_struct_field
  (#opened: _)
  (#base:Type) (#a:eqtype) (#b: a -> Type u#b) (#p:(k:a -> pcm (b k)))
  (r: ref base (prod_pcm p)) (k:a)
  (xs: Ghost.erased (restricted_t a b))
: STAtomicBase (ref base (p k)) false opened Unobservable
    (r `pts_to` xs)
    (fun s ->
      (r `pts_to` struct_without_field p k xs) `star` 
      (s `pts_to` Ghost.reveal xs k))
    (requires True)
    (ensures fun r' -> r' == ref_focus r (struct_field p k))
= struct_peel p k xs;
  split r xs (struct_without_field p k xs) (field_to_struct_f p k (Ghost.reveal xs k));
  rewrite (r `pts_to` _) (r `pts_to` _);
  let r = focus r (struct_field p k) (field_to_struct_f p k (Ghost.reveal xs k)) (Ghost.reveal xs k) in
  rewrite (r `pts_to` _) (r `pts_to` _);
  return r

(*
let ptr_addr_of_struct_field
  (#base:Type) (#a:eqtype) (#b: a -> Type u#b) (#p:(k:a -> pcm (b k)))
  (r: Ptr.ptr base (prod_pcm p)) (k:a)
  (xs: Ghost.erased (restricted_t a b))
: Steel (ref base (p k))
    (r `pts_to` xs)
    (fun s ->
      (r `pts_to` struct_without_field p k xs) `star` 
      (s `pts_to` Ghost.reveal xs k))
    (requires fun _ -> True)
    (ensures fun _ r' _ -> r' == ref_focus r (struct_field p k))
= struct_peel p k xs;
  split r xs (struct_without_field p k xs) (field_to_struct_f p k (Ghost.reveal xs k));
  let r = focus r (struct_field p k) (field_to_struct_f p k (Ghost.reveal xs k)) (Ghost.reveal xs k) in
  return r
*)

let struct_with_field (#a:eqtype) (#b: a -> Type u#b) (p:(k:a -> pcm (b k))) (k:a)
  (x:b k) (xs: restricted_t a b)
: restricted_t a b
= on_dom a (fun k' -> if k' = k then x else xs k')

let struct_unpeel (#a:eqtype) (#b: a -> Type u#b) (p:(k:a -> pcm (b k))) (k:a)
  (x: b k) (xs: restricted_t a b)
: Lemma
    (requires xs k == one (p k))
    (ensures
      composable (prod_pcm p) xs (field_to_struct_f p k x) /\
      struct_with_field p k x xs == op (prod_pcm p) xs (field_to_struct_f p k x))
= Classical.forall_intro_2 (fun k -> is_unit (p k));
  assert (struct_with_field p k x xs `feq` op (prod_pcm p) xs (field_to_struct_f p k x))

let unaddr_of_struct_field
  (#opened: _)
  (#base:Type) (#a:eqtype) (#b: a -> Type u#b) (#p:(k:a -> pcm (b k))) (k:a)
  (r': ref base (p k)) (r: ref base (prod_pcm p))
  (xs: Ghost.erased (restricted_t a b)) (x: Ghost.erased (b k))
: STGhost unit opened
    ((r `pts_to` xs) `star` (r' `pts_to` x))
    (fun s -> r `pts_to` struct_with_field p k x xs)
    (requires r' == ref_focus r (struct_field p k) /\ Ghost.reveal xs k == one (p k))
    (ensures fun _ -> True)
= unfocus r' r (struct_field p k) x;
  let _ = gather r xs (field_to_struct_f p k x) in
  struct_unpeel p k x xs;
  rewrite (r `pts_to` _) (r `pts_to` _)
