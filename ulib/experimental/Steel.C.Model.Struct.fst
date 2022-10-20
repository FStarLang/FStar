module Steel.C.Model.Struct

module P = FStar.PCM
open Steel.C.Model.PCM
open Steel.C.Model.Connection
open Steel.C.Model.Ref
// module Ptr = Steel.C.Model.Ptr
open Steel.Effect
module A = Steel.Effect.Atomic

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

let addr_of_struct_field
  (#a:eqtype) (#b: a -> Type u#b) (#p:(k:a -> pcm (b k)))
  (r: ref (prod_pcm p)) (k:a)
  (xs: Ghost.erased (restricted_t a b))
: Steel (ref (p k))
    (r `pts_to` xs)
    (fun s ->
      (r `pts_to` struct_without_field p k xs) `star` 
      (s `pts_to` Ghost.reveal xs k))
    (requires fun _ -> True)
    (ensures fun _ r' _ -> r' == ref_focus r (struct_field p k))
= struct_peel p k xs;
  split r xs (struct_without_field p k xs) (field_to_struct_f p k (Ghost.reveal xs k));
  A.change_equal_slprop (r `pts_to` _) (r `pts_to` _);
  let r = focus r (struct_field p k) (field_to_struct_f p k (Ghost.reveal xs k)) (Ghost.reveal xs k) in
  A.change_equal_slprop (r `pts_to` _) (r `pts_to` _);
  A.return r

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
  A.return r
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
  (#a:eqtype) (#b: a -> Type u#b) (#p:(k:a -> pcm (b k))) (k:a)
  (r': ref (p k)) (r: ref (prod_pcm p))
  (xs: Ghost.erased (restricted_t a b)) (x: Ghost.erased (b k))
: Steel unit
    ((r `pts_to` xs) `star` (r' `pts_to` x))
    (fun s -> r `pts_to` struct_with_field p k x xs)
    (requires fun _ -> r' == ref_focus r (struct_field p k) /\ Ghost.reveal xs k == one (p k))
    (ensures fun _ _ _ -> True)
= unfocus r' r (struct_field p k) x;
  gather r xs (field_to_struct_f p k x);
  struct_unpeel p k x xs;
  A.change_equal_slprop (r `pts_to` _) (r `pts_to` _);
  A.return ()

(*
let struct_view_to_view_prop
  (#a:Type) (#b: a -> Type) (#p:(k:a -> pcm (b k)))
  (fa:a -> prop)
  (view_t:(refine a fa -> Type))
  (field_view:(k:refine a fa -> sel_view (p k) (view_t k)))
: restricted_t a b -> Tot prop
= fun (f : restricted_t a b) ->
  forall (k:a).
    (fa k ==> (field_view k).to_view_prop (f k))

let struct_view_to_view
  (#a:Type) (#b: a -> Type) (#p:(k:a -> pcm (b k)))
  (#fa:a -> prop)
  (view_t:(refine a fa -> Type))
  (field_view:(k:refine a fa -> sel_view (p k) (view_t k)))
: refine (restricted_t a b) (struct_view_to_view_prop fa view_t field_view) ->
  Tot (restricted_t (refine a fa) view_t)
= fun (f: refine (restricted_t a b) (struct_view_to_view_prop fa view_t field_view)) ->
  let g = on_dom (refine a fa) (fun (k: refine a fa) -> (field_view k).to_view (f k)) in
  g

let struct_view_to_carrier
  (#a:Type) (#b: a -> Type) (#p:(k:a -> pcm (b k)))
  (#fa:a -> prop)
  (dec_fa: decidable fa)
  (view_t:(refine a fa -> Type))
  (field_view:(k:refine a fa -> sel_view (p k) (view_t k)))
: restricted_t (refine a fa) view_t ->
  Tot (refine (restricted_t a b) (struct_view_to_view_prop fa view_t field_view))
= fun (f: restricted_t (refine a fa) view_t) ->
  let g: restricted_t a b = on_dom a (fun k ->
    if dec_fa k then
      (field_view k).to_carrier (f k) <: b k
    else one (p k))
  in g

// let struct_view_to_carrier_not_one
//   (#a:Type) (#b: a -> Type) (#p:(k:a -> pcm (b k)))
//   (#fa:a -> prop)
//   (dec_fa: decidable fa)
//   (view_t:(refine a fa -> Type))
//   (field_view:(k:refine a fa -> sel_view (p k) (view_t k)))
//   (x:restricted_t (refine a fa) view_t)
// : Lemma
//     (requires exists (k:a). fa k)
//     (ensures struct_view_to_carrier dec_fa view_t field_view x =!= one (prod_pcm p))
// = let k = FStar.IndefiniteDescription.indefinite_description_ghost a fa in
//   (field_view k).to_carrier_not_one (x k)

let struct_view_to_view_frame
  (#a:Type) (#b: a -> Type) (#p:(k:a -> pcm (b k)))
  (#fa:a -> prop)
  (dec_fa: decidable fa)
  (view_t:(refine a fa -> Type))
  (field_view:(k:refine a fa -> sel_view (p k) (view_t k)))
  (x:restricted_t (refine a fa) view_t)
  (frame: restricted_t a b)
: Lemma
    (requires (composable (prod_pcm p) (struct_view_to_carrier dec_fa view_t field_view x) frame))
    (ensures
      struct_view_to_view_prop fa view_t field_view
        (op (prod_pcm p) (struct_view_to_carrier dec_fa view_t field_view x) frame) /\ 
      struct_view_to_view view_t field_view
        (op (prod_pcm p) (struct_view_to_carrier dec_fa view_t field_view x) frame) == x)
= let aux (k:refine a fa)
  : Lemma (
      (field_view k).to_view_prop (op (p k) ((field_view k).to_carrier (x k)) (frame k)) /\
      (field_view k).to_view (op (p k) ((field_view k).to_carrier (x k)) (frame k)) == x k)
  = assert (composable (p k) ((field_view k).to_carrier (x k)) (frame k));
    (field_view k).to_view_frame (x k) (frame k)
  in forall_intro aux;
  assert (
    struct_view_to_view view_t field_view
       (op (prod_pcm p) (struct_view_to_carrier dec_fa view_t field_view x) frame) `feq` x)
*)

let mem (#a:eqtype) (xs:list a) x : prop = List.mem x xs == true

let struct_view_to_view_prop 
  (#a:eqtype) (#b: a -> Type) (#p:(k:a -> pcm (b k)))
  (#view_t:a -> Type)
  (#can_view_units: bool)
  (field_view:(k:a -> sel_view (p k) (view_t k) can_view_units))
  (included: list a)
: restricted_t a b -> prop
= fun f -> forall (k:a). (mem included k ==> (field_view k).to_view_prop (f k))

let struct_view_to_view
  (#a:eqtype) (#b: a -> Type) (#p:(k:a -> pcm (b k)))
  (#view_t:a -> Type)
  (#can_view_units: bool)
  (field_view:(k:a -> sel_view (p k) (view_t k) can_view_units))
  (included: list a)
: refine (restricted_t a b) (struct_view_to_view_prop field_view included) ->
  Tot (restricted_t (refine a (mem included)) view_t)
= fun f -> on_dom (refine a (mem included)) (fun k -> (field_view k).to_view (f k))

let struct_view_to_carrier
  (#a:eqtype) (#b: a -> Type) (#p:(k:a -> pcm (b k)))
  (#view_t:a -> Type)
  (#can_view_units: bool)
  (field_view:(k:a -> sel_view (p k) (view_t k) can_view_units))
  (included: list a)
: restricted_t (refine a (mem included)) view_t ->
  Tot (refine (restricted_t a b) (struct_view_to_view_prop field_view included))
= fun f ->
  let g: restricted_t a b = on_dom a (fun k ->
    if k `List.mem` included then
      (field_view k).to_carrier (f k) <: b k
    else one (p k))
  in g

let struct_view_to_view_frame
  (#a:eqtype) (#b: a -> Type) (#p:(k:a -> pcm (b k)))
  (#view_t:a -> Type)
  (#can_view_units: bool)
  (field_view:(k:a -> sel_view (p k) (view_t k) can_view_units))
  (included: list a)
  (x:restricted_t (refine a (mem included)) view_t)
  (frame: restricted_t a b)
: Lemma
    (requires (composable (prod_pcm p) (struct_view_to_carrier field_view included x) frame))
    (ensures
      struct_view_to_view_prop field_view included
        (op (prod_pcm p) (struct_view_to_carrier field_view included x) frame) /\ 
      struct_view_to_view field_view included
        (op (prod_pcm p) (struct_view_to_carrier field_view included x) frame) == x)
= let aux (k:refine a (mem included))
  : Lemma (
      (field_view k).to_view_prop (op (p k) ((field_view k).to_carrier (x k)) (frame k)) /\
      (field_view k).to_view (op (p k) ((field_view k).to_carrier (x k)) (frame k)) == x k)
  = assert (composable (p k) ((field_view k).to_carrier (x k)) (frame k));
    (field_view k).to_view_frame (x k) (frame k)
  in forall_intro aux;
  assert (
    struct_view_to_view field_view included
       (op (prod_pcm p) (struct_view_to_carrier field_view included x) frame) `feq` x)

let struct_view
  (#a:eqtype) (#b: a -> Type) (#p:(k:a -> pcm (b k)))
  (#view_t:a -> Type)
  (#can_view_units: bool)
  (field_view:(k:a -> sel_view (p k) (view_t k) can_view_units))
  (included: list a)
: sel_view (prod_pcm p)
    (restricted_t (refine a (mem included)) view_t)
    (can_view_units || Nil? included)
= {
  to_view_prop = struct_view_to_view_prop field_view included;
  to_view = struct_view_to_view field_view included;
  to_carrier = struct_view_to_carrier field_view included;
  to_carrier_not_one = begin
    let aux () : Lemma
      (requires ~ (can_view_units || Nil? included))
      (ensures
        ~ (exists x. struct_view_to_carrier field_view included x == one (prod_pcm p)) /\
        ~ (struct_view_to_view_prop field_view included (one (prod_pcm p))))
    = let k :: _ = included in ()
    in move_requires aux () end;
  to_view_frame = struct_view_to_view_frame field_view included;
}
