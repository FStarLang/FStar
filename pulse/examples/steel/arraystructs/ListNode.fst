module ListNode

#push-options "--print_universes"

open FStar.FunctionalExtensionality
module A = Steel.Effect.Atomic
open Steel.Effect
open Steel.C.Opt
open Steel.C.PCM
open Steel.C.Ref
open Steel.C.Connection
open Steel.C.Struct
module U = FStar.Universe
module P = FStar.PCM

type node_field = | Value | Next

let node_fields (node:Type u#0) k : Type u#0 = match k with
  | Value -> option int
  | Next -> option (option (ref' node node))

#push-options "--__no_positivity"
noeq type node: Type u#0 =
{ un_node: restricted_t node_field (node_fields node) }
#pop-options

let node': Type u#0 = restricted_t node_field (node_fields node)

let node_fields_pcm k: pcm (node_fields node k) = match k with
  | Value -> opt_pcm #int
  | Next -> opt_pcm #(option (ref' node node))

let node_pcm': pcm node' = prod_pcm node_fields_pcm

let node_composable
  (x y: _)
: Tot prop
= composable node_pcm' x.un_node y.un_node

let node_op
  (x: _) (y: _ { node_composable x y })
: Tot _
= Mknode (op node_pcm' x.un_node y.un_node)

let fstar_node_pcm: FStar.PCM.pcm node = {
  P.p = {
    P.composable = node_composable;
    P.op = node_op;
    P.one = Mknode (one node_pcm');
  };
  P.comm = (fun x y -> op_comm node_pcm' x.un_node y.un_node);
  P.assoc = (fun x y z -> op_assoc_l node_pcm' x.un_node y.un_node z.un_node);
  P.assoc_r = (fun x y z -> op_assoc_r node_pcm' x.un_node y.un_node z.un_node);
  P.is_unit = (fun x -> is_unit node_pcm' x.un_node);
  P.refine = (fun x -> p_refine node_pcm' x.un_node);
}

let node_pcm: pcm node = pcm_of_fstar_pcm fstar_node_pcm

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

let node_iso : isomorphism node_pcm node_pcm' =
  mkisomorphism
    unroll
    roll
    ()
    ()
    (fun _ -> ())
    (fun _ -> ())


let roll_conn: node_pcm' `connection` node_pcm =
  connection_of_isomorphism (isomorphism_inverse node_iso)

let unroll_conn: node_pcm `connection` node_pcm' =
  connection_of_isomorphism node_iso

let mk_node'_f (value: option int) (next: option (option (ref' node node)))
  (k: node_field)
: node_fields node k
= match k with
  | Value -> value
  | Next -> next
  
let mk_node'
  (value: Ghost.erased (option int))
  (next: Ghost.erased (option (option (ref' node node))))
: Ghost.erased node'
= Ghost.hide (on_domain node_field (mk_node'_f (Ghost.reveal value) (Ghost.reveal next)))

let mk_node value next = Ghost.hide (Mknode (mk_node' (Ghost.reveal value) (Ghost.reveal next)))

let mk_node_tot value next = Mknode (on_domain node_field (mk_node'_f value next))

let mk_node_tot_mk_node value next = ()

open Steel.C.PCM
module P = FStar.PCM

let mk_node_refine value next = ()

let _value
: node_pcm `connection` opt_pcm #int
= unroll_conn `connection_compose` struct_field node_fields_pcm Value

let _next
: node_pcm `connection` opt_pcm #(option (ref' node node))
= unroll_conn `connection_compose` struct_field node_fields_pcm Next

let one_next : Ghost.erased (option int) =
  Ghost.hide (one (opt_pcm #int))

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
  (#value:Ghost.erased (option int))
  (#next:Ghost.erased (option (option (ref' node node))))
  (p: ref 'a node_pcm)
: Steel (ref 'a node_pcm')
    (p `pts_to` mk_node value next)
    (fun p' -> p' `pts_to` mk_node' value next)
    (requires (fun _ -> True))
    (ensures (fun _ p' _ ->
      p' == ref_focus p unroll_conn
    ))
= let p' = focus p unroll_conn (mk_node value next) (mk_node' value next) in
  A.return p'

let roll_ref 
  (#value:Ghost.erased (option int))
  (#next:Ghost.erased (option (option (ref' node node))))
  (p: ref 'a node_pcm) (p': ref 'a node_pcm')
: Steel unit
    (p' `pts_to` mk_node' value next)
    (fun _ -> p `pts_to` mk_node value next)
    (requires fun _ -> p' == ref_focus p unroll_conn)
    (ensures fun _ _ _ -> True)
= unfocus p' p unroll_conn (mk_node' value next);
  A.change_equal_slprop (p `pts_to` _) (p `pts_to` _)

let addr_of_value
  (#value:Ghost.erased (option int))
  (#next:Ghost.erased (option (option (ref' node node))))
  (p: ref 'a node_pcm)
: Steel (ref 'a (opt_pcm #int))
    (p `pts_to` mk_node value next)
    (fun q ->
       (p `pts_to` mk_node none next) `star`
       (q `pts_to` value))
    (requires (fun _ -> True))
    (ensures (fun _ q _ ->
      q == ref_focus p _value
    ))
= let p' = unroll_ref p in
  let q = addr_of_struct_field p' Value (mk_node' value next) in
  A.change_equal_slprop (p' `pts_to` _) (p' `pts_to` mk_node' none next);
  A.change_equal_slprop (q `pts_to` _) (q `pts_to` value);
  roll_ref p p';
  A.return q

let unaddr_of_value
  (#value:Ghost.erased (option int))
  (#next:Ghost.erased (option (option (ref' node node))))
  (p: ref 'a node_pcm)
  (q: ref 'a (opt_pcm #int))
: Steel unit
    ((p `pts_to` mk_node none next) `star` (q `pts_to` value))
    (fun _ -> p `pts_to` mk_node value next)
    (requires (fun _ -> q == ref_focus p _value))
    (ensures (fun _ _ _ -> True))
= let p' = unroll_ref p in
  let q = unaddr_of_struct_field #_ #_ #_ #node_fields_pcm Value q p' (mk_node' none next) value in // FIXME: WHY WHY WHY does F* infer the constant function (due to the type of q) instead?
  A.change_equal_slprop (p' `pts_to` _) (p' `pts_to` mk_node' value next);
  roll_ref p p';
  A.return ()

let addr_of_next
  (#value:Ghost.erased (option int))
  (#next:Ghost.erased (option (option (ref' node node))))
  (p: ref 'a node_pcm)
: Steel (ref 'a (opt_pcm #(option (ref' node node))))
    (p `pts_to` mk_node value next)
    (fun q ->
       (p `pts_to` mk_node value none) `star`
       (q `pts_to` next))
    (requires (fun _ -> True))
    (ensures (fun _ q _ -> q == ref_focus p _next))
= let p' = unroll_ref p in
  let q = addr_of_struct_field p' Next (mk_node' value next) in
  A.change_equal_slprop (p' `pts_to` _) (p' `pts_to` mk_node' value none);
  A.change_equal_slprop (q `pts_to` _) (q `pts_to` next);
  roll_ref p p';
  A.return q

let unaddr_of_next
  (#value:Ghost.erased (option int))
  (#next:Ghost.erased (option (option (ref' node node))))
  (p: ref 'a node_pcm)
  (q: ref 'a (opt_pcm #(option (ref' node node))))
: Steel unit
    ((p `pts_to` mk_node value none) `star` (q `pts_to` next))
    (fun q -> p `pts_to` mk_node value next)
    (requires (fun _ -> (q == ref_focus p _next)))
    (ensures (fun _ _ _ -> True))
= let p' = unroll_ref p in
  let q = unaddr_of_struct_field #_ #_ #_ #node_fields_pcm Next q p' (mk_node' value none) next in // same here
  A.change_equal_slprop (p' `pts_to` _) (p' `pts_to` mk_node' value next);
  roll_ref p p';
  A.return ()
