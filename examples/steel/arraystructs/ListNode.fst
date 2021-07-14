module ListNode

#push-options "--print_universes"

open FStar.FunctionalExtensionality
module A = Steel.Effect.Atomic
open Steel.Effect
open FStar.PCM
open FStar.PCM.POD
open Steel.C.PCM

type node_field = | Value | Next

let ref' a b = pb: Ghost.erased (pcm b) & ref a pb

let node_fields node k = match k with
  | Value -> pod (FStar.Universe.raise_t int)
  | Next -> pod (option (ref' (FStar.Universe.raise_t node) node))

#push-options "--__no_positivity"
noeq type node =
{ un_node: restricted_t node_field (node_fields node) }
#pop-options

let node_fields_pcm k: pcm (node_fields node k) = match k with
  | Value -> pod_pcm (FStar.Universe.raise_t int)
  | Next -> pod_pcm (option (ref' (FStar.Universe.raise_t node) node))

let node_pcm' = prod_pcm node_fields_pcm

let node_pcm: pcm node =
  let p: FStar.PCM.pcm node = {
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
  } in
  p

let roll: node_pcm' `morphism` node_pcm = {
  morph = Mknode;
  morph_unit = ();
  morph_compose = (fun _ _ -> ());
}

let unroll: node_pcm `morphism` node_pcm' = {
  morph = Mknode?.un_node;
  morph_unit = ();
  morph_compose = (fun _ _ -> ());
}

let mk_un_node: squash (Mknode `is_inverse_of` Mknode?.un_node) = ()
let un_mk_node: squash (Mknode?.un_node `is_inverse_of` Mknode) = ()

let roll_compatible x v
: Lemma
    (requires compatible node_pcm' x v)
    (ensures compatible node_pcm (Mknode x) (Mknode v))
    [SMTPat (compatible node_pcm' x v)]
= let frame = compatible_elim node_pcm' x v in
  compatible_intro node_pcm (Mknode x) (Mknode v) (Mknode frame)

val compatible_morphism
  (#p: pcm 'a) (#q: pcm 'b)
  (f: p `morphism` q)
  (x y: Ghost.erased 'a)
: Lemma
    (requires compatible p x y)
    (ensures compatible q (f.morph x) (f.morph y))

let compatible_morphism #a #b #p #q f x y =
  let frame_x = compatible_elim p x y in
  let _ = f.morph_compose frame_x x in
  compatible_intro q (f.morph x) (f.morph y) (f.morph frame_x)

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

let mk_node' (value: Ghost.erased _) (next: Ghost.erased _): Ghost.erased _ =
  Ghost.hide (fun k -> match k with
  | Value -> value
  | Next -> next)

let mk_node (value: Ghost.erased _) (next: Ghost.erased _): Ghost.erased _ =
  Ghost.hide (mk_node' (Ghost.reveal value) (Ghost.reveal next))

assume val _value : connection node_pcm (pod_pcm (FStar.Universe.raise_t int))

let one_next : Ghost.erased (pod (Universe.raise_t int)) =
  Ghost.hide (one (pod_pcm (FStar.Universe.raise_t int)))

let addr_of_next
  (#value:Ghost.erased (pod (Universe.raise_t int)))
  (#next:Ghost.erased _)
  (p: ref 'a node_pcm)
: SteelT (q:ref 'a (pod_pcm (FStar.Universe.raise_t int)){q == ref_focus p _value})
    (p `pts_to` mk_node value next)
    (fun q ->
       (p `pts_to` mk_node one_next next) `star`
       (q `pts_to` value))
= A.sladmit(); A.return (admit())

//let node_pcm: pcm (restricted_t 
//node --> prod_pcm node_pcm_fields

// #push-options "--print_universes"
// 
// let x = 3
// 
// #pop-options
// 
// type node = {
// }
// 
// let node_fields k: Type = match k with
//   | I -> pod int
//   | Next -> uninit_t (pod rec_arg)
//   
// let node (rec_arg:Type): Type = restricted_t node_field (node_fields rec_arg)
// 
// /// PCM for node:
// 
// let node_fields_pcm k : pcm (node_fields k) = match k with
//   | P1 -> point_pcm
//   | P2 -> point_pcm
// let node_pcm = prod_pcm node_fields_pcm
// 
// /// (mk_node p1 p2) represents (struct node){.p1 = p1, .p2 = p2}
// 
// let mk_node_f (p1 p2: point) (k: node_field): node_fields k = match k with
//   | P1 -> p1
//   | P2 -> p2
// let mk_node p1 p2 = on_domain node_field (mk_node_f (Ghost.reveal p1) (Ghost.reveal p2))
// 
// let _p1 = struct_field node_fields_pcm P1
// let _p2 = struct_field node_fields_pcm P2
// 
// /// Taking pointers to the p1 and p2 fields of a node
// 
// let node_without_p1 p1 p2
// : Lemma (struct_without_field node_fields_pcm P1 (mk_node p1 p2) `feq`
//          Ghost.reveal (mk_node (one point_pcm) p2))
//   [SMTPat (mk_node p1 p2)]
// = ()
// 
// let node_with_p1 p1 p2
// : Lemma (struct_with_field node_fields_pcm P1 (Ghost.reveal p1) (mk_node (one point_pcm) p2) `feq`
//          Ghost.reveal (mk_node p1 p2))
//   [SMTPat (mk_node p1 p2)]
// = ()
// 
// let node_without_p2 p1 p2
// : Lemma (struct_without_field node_fields_pcm P2 (mk_node p1 p2) `feq`
//          Ghost.reveal (mk_node p1 (one point_pcm)))
//   [SMTPat (mk_node p1 p2)]
// = ()
// 
// let node_with_p2 p1 p2
// : Lemma (struct_with_field node_fields_pcm P2 (Ghost.reveal p2) (mk_node p1 (one point_pcm)) `feq`
//          Ghost.reveal (mk_node p1 p2))
//   [SMTPat (mk_node p1 p2)]
// = ()
// 
// let addr_of_p1 #a #p1 #p2 p =
//   let q = addr_of_struct_field p P1 (mk_node p1 p2) in
//   A.change_equal_slprop (p `pts_to` _) (p `pts_to` mk_node (one point_pcm) p2);
//   A.change_equal_slprop (q `pts_to` _) (q `pts_to` p1);
//   A.return q
// 
// let unaddr_of_p1 #a #p1 #p2 p q =
//   unaddr_of_struct_field P1 q p (mk_node (one point_pcm) p2) p1;
//   A.change_equal_slprop (p `pts_to` _) (p `pts_to` _)
// 
// let addr_of_p2 #a #p1 #p2 p =
//   let q = addr_of_struct_field p P2 (mk_node p1 p2) in
//   A.change_equal_slprop (p `pts_to` _) (p `pts_to` mk_node p1 (one point_pcm));
//   A.change_equal_slprop (q `pts_to` _) (q `pts_to` p2);
//   A.return q
// 
// let unaddr_of_p2 #a #p1 #p2 p q =
//   unaddr_of_struct_field P2 q p (mk_node p1 (one point_pcm)) p2;
//   A.change_equal_slprop (p `pts_to` _) (p `pts_to` _)

#pop-options
