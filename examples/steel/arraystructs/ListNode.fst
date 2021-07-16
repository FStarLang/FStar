module ListNode

#push-options "--print_universes"

open FStar.FunctionalExtensionality
module A = Steel.Effect.Atomic
open Steel.Effect
open FStar.PCM
open FStar.PCM.POD
open Steel.C.PCM
open Steel.C.Ref
open Steel.C.Connection
open Steel.C.Struct
module U = FStar.Universe

type node_field = | Value | Next

let node_fields (node:Type u#1) k : Type u#1 = match k with
  | Value -> pod int'
  | Next -> pod (option (ref' node node))

#push-options "--__no_positivity"
noeq type node: Type u#1 =
{ un_node: restricted_t node_field (node_fields node) }
#pop-options

let node': Type u#1 = restricted_t node_field (node_fields node)

let node_fields_pcm k: pcm (node_fields node k) = match k with
  | Value -> pod_pcm int'
  | Next -> pod_pcm (option (ref' node node))

let node_pcm': pcm node' = prod_pcm node_fields_pcm

let node_pcm: pcm node = {
  FStar.PCM.p = {
    composable = (fun x y -> composable node_pcm' x.un_node y.un_node);
    op = (fun x y -> Mknode (op node_pcm' x.un_node y.un_node));
    one = Mknode (one node_pcm');
  };
  comm = (fun x y -> node_pcm'.comm x.un_node y.un_node);
  assoc = (fun x y z -> node_pcm'.assoc x.un_node y.un_node z.un_node);
  assoc_r = (fun x y z -> node_pcm'.assoc_r x.un_node y.un_node z.un_node);
  is_unit = (fun x -> node_pcm'.is_unit x.un_node);
  refine = (fun x -> node_pcm'.refine x.un_node);
}

let roll: node_pcm' `morphism` node_pcm =
  mkmorphism
    Mknode
    ()
    (fun _ _ -> ())

let unroll: node_pcm `morphism` node_pcm' =
  mkmorphism
    Mknode?.un_node
    ()
    (fun _ _ -> ())

let mk_un_node: squash (Mknode `is_inverse_of` Mknode?.un_node) = ()
let un_mk_node: squash (Mknode?.un_node `is_inverse_of` Mknode) = ()

let roll_compatible x v
: Lemma
    (requires compatible node_pcm' x v)
    (ensures compatible node_pcm (Mknode x) (Mknode v))
    [SMTPat (compatible node_pcm' x v)]
= compatible_morphism roll x v

let unroll_compatible x v
: Lemma
    (requires compatible node_pcm x v)
    (ensures compatible node_pcm' x.un_node v.un_node)
    [SMTPat (compatible node_pcm x v)]
= compatible_morphism unroll x v

let roll_conn_lift_fpu
  (x: Ghost.erased _ {~ (Ghost.reveal x == one node_pcm) })
  (y: Ghost.erased _)
  (f: frame_preserving_upd node_pcm x y)
: frame_preserving_upd node_pcm' x.un_node y.un_node
= fun v ->
  let w = (f (Mknode v)).un_node in
  assert (node_pcm'.refine w);
  assert (compatible node_pcm' y.un_node w);
  let aux (frame:_{composable node_pcm' x.un_node frame})
  : Lemma (
      composable node_pcm' y.un_node frame /\
      (op node_pcm' x.un_node frame == v ==> op node_pcm' y.un_node frame == w))
  = roll.morph_compose x.un_node frame
  in FStar.Classical.forall_intro aux;
  w

let roll_conn: node_pcm' `connection` node_pcm = {
  conn_small_to_large = unroll;
  conn_large_to_small = roll;
  conn_small_to_large_inv = ();
  conn_lift_frame_preserving_upd = roll_conn_lift_fpu;
}

let unroll_conn_lift_fpu
  (x: Ghost.erased _ {~ (Ghost.reveal x == one node_pcm') })
  (y: Ghost.erased _)
  (f: frame_preserving_upd node_pcm' x y)
: frame_preserving_upd node_pcm (Mknode x) (Mknode y)
= fun v ->
  let w = Mknode (f v.un_node) in
  let aux (frame:_{composable node_pcm (Mknode x) frame})
  : Lemma (
      composable node_pcm (Mknode y) frame /\
      (op node_pcm (Mknode x) frame == v ==> op node_pcm (Mknode y) frame == w))
  = unroll.morph_compose (Mknode x) frame
  in FStar.Classical.forall_intro aux;
  w

let unroll_conn: node_pcm `connection` node_pcm' = {
  conn_small_to_large = roll;
  conn_large_to_small = unroll;
  conn_small_to_large_inv = ();
  conn_lift_frame_preserving_upd = unroll_conn_lift_fpu;
}

let mk_node'_f (value: pod int') (next: pod (option (ref' node node)))
  (k: node_field)
: node_fields node k
= match k with
  | Value -> value
  | Next -> next
  
let mk_node'
  (value: Ghost.erased (pod int'))
  (next: Ghost.erased (pod (option (ref' node node))))
: Ghost.erased node'
= Ghost.hide (on_domain node_field (mk_node'_f (Ghost.reveal value) (Ghost.reveal next)))

let mk_node value next = Ghost.hide (Mknode (mk_node' (Ghost.reveal value) (Ghost.reveal next)))

let _value
: node_pcm `connection` pod_pcm int'
= unroll_conn `connection_compose` struct_field node_fields_pcm Value

let _next
: node_pcm `connection` pod_pcm (option (ref' node node))
= unroll_conn `connection_compose` struct_field node_fields_pcm Next

let one_next : Ghost.erased (pod int') =
  Ghost.hide (one (pod_pcm int'))

let node'_without_value value next
: Lemma (struct_without_field node_fields_pcm Value (mk_node' value next) `feq`
         Ghost.reveal (mk_node' none next))
  [SMTPat (mk_node' value next)]
= ()

let node'_with_value value next
: Lemma (struct_with_field node_fields_pcm Value (Ghost.reveal value) (mk_node' none next) `feq`
         Ghost.reveal (mk_node' value next))
  [SMTPat (mk_node' value next)]
= ()

let node'_without_next value next
: Lemma (struct_without_field node_fields_pcm Next (mk_node' value next) `feq`
         Ghost.reveal (mk_node' value none))
  [SMTPat (mk_node' value next)]
= ()

let node'_with_next value next
: Lemma (struct_with_field node_fields_pcm Next (Ghost.reveal next) (mk_node' value none) `feq`
         Ghost.reveal (mk_node' value next))
  [SMTPat (mk_node' value next)]
= ()

let mk_node_mk_node' value next
: Lemma (
    Ghost.reveal (mk_node value next) ==
    unroll_conn.conn_small_to_large.morph (mk_node' value next))
= ()

let unroll_ref 
  (#value:Ghost.erased (pod int'))
  (#next:Ghost.erased (pod (option (ref' node node))))
  (p: ref 'a node_pcm)
: SteelT (p':ref 'a node_pcm'{p' == ref_focus p unroll_conn})
    (p `pts_to` mk_node value next)
    (fun p' -> p' `pts_to` mk_node' value next)
= let p' = focus p unroll_conn (mk_node value next) (mk_node' value next) in
  A.return p'

let roll_ref 
  (#value:Ghost.erased (pod int'))
  (#next:Ghost.erased (pod (option (ref' node node))))
  (p: ref 'a node_pcm) (p': ref 'a node_pcm')
: Steel unit
    (p' `pts_to` mk_node' value next)
    (fun _ -> p `pts_to` mk_node value next)
    (requires fun _ -> p' == ref_focus p unroll_conn)
    (ensures fun _ _ _ -> True)
= unfocus p' p unroll_conn (mk_node' value next);
  A.change_equal_slprop (p `pts_to` _) (p `pts_to` _)

let addr_of_value
  (#value:Ghost.erased (pod int'))
  (#next:Ghost.erased (pod (option (ref' node node))))
  (p: ref 'a node_pcm)
: SteelT (q:ref 'a (pod_pcm int'){q == ref_focus p _value})
    (p `pts_to` mk_node value next)
    (fun q ->
       (p `pts_to` mk_node none next) `star`
       (q `pts_to` value))
= let p' = unroll_ref p in
  let q = addr_of_struct_field p' Value (mk_node' value next) in
  A.change_equal_slprop (p' `pts_to` _) (p' `pts_to` mk_node' none next);
  A.change_equal_slprop (q `pts_to` _) (q `pts_to` value);
  roll_ref p p';
  A.return q

let unaddr_of_value
  (#value:Ghost.erased (pod int'))
  (#next:Ghost.erased (pod (option (ref' node node))))
  (p: ref 'a node_pcm)
  (q: ref 'a (pod_pcm int'){q == ref_focus p _value})
: SteelT unit
    ((p `pts_to` mk_node none next) `star` (q `pts_to` value))
    (fun _ -> p `pts_to` mk_node value next)
= let p' = unroll_ref p in
  let q = unaddr_of_struct_field Value q p' (mk_node' none next) value in
  A.change_equal_slprop (p' `pts_to` _) (p' `pts_to` mk_node' value next);
  roll_ref p p';
  A.return ()

let addr_of_next
  (#value:Ghost.erased (pod int'))
  (#next:Ghost.erased (pod (option (ref' node node))))
  (p: ref 'a node_pcm)
: SteelT (q:ref 'a (pod_pcm (option (ref' node node))){q == ref_focus p _next})
    (p `pts_to` mk_node value next)
    (fun q ->
       (p `pts_to` mk_node value none) `star`
       (q `pts_to` next))
= let p' = unroll_ref p in
  let q = addr_of_struct_field p' Next (mk_node' value next) in
  A.change_equal_slprop (p' `pts_to` _) (p' `pts_to` mk_node' value none);
  A.change_equal_slprop (q `pts_to` _) (q `pts_to` next);
  roll_ref p p';
  A.return q

let unaddr_of_next
  (#value:Ghost.erased (pod int'))
  (#next:Ghost.erased (pod (option (ref' node node))))
  (p: ref 'a node_pcm)
  (q: ref 'a (pod_pcm (option (ref' node node))){q == ref_focus p _next})
: SteelT unit
    ((p `pts_to` mk_node value none) `star` (q `pts_to` next))
    (fun q -> p `pts_to` mk_node value next)
= let p' = unroll_ref p in
  let q = unaddr_of_struct_field Next q p' (mk_node' value none) next in
  A.change_equal_slprop (p' `pts_to` _) (p' `pts_to` mk_node' value next);
  roll_ref p p';
  A.return ()
