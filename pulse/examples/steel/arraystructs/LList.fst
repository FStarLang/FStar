module LList
open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect

open Steel.C.Ref
open Steel.C.PCM
open Steel.C.Opt
open Steel.C.Connection

open ListNode

let vpure_sel'
  (p: prop)
: Tot (selector' (squash p) (Steel.Memory.pure p))
= fun (m: Steel.Memory.hmem (Steel.Memory.pure p)) -> pure_interp p m

let vpure_sel
  (p: prop)
: Tot (selector (squash p) (Steel.Memory.pure p))
= vpure_sel' p

[@@ __steel_reduce__]
let vpure'
  (p: prop)
: GTot vprop'
= {
  hp = Steel.Memory.pure p;
  t = squash p;
  sel = vpure_sel p;
}

[@@ __steel_reduce__]
let vpure (p: prop) : Tot vprop = VUnit (vpure' p)

let intro_vpure
  (#opened: _)
  (p: prop)
: SteelGhost unit opened
    emp
    (fun _ -> vpure p)
    (fun _ -> p)
    (fun _ _ h' -> p)
=
  change_slprop_rel
    emp
    (vpure p)
    (fun _ _ -> p)
    (fun m -> pure_interp p m)

let elim_vpure
  (#opened: _)
  (p: prop)
: SteelGhost unit opened
    (vpure p)
    (fun _ -> emp)
    (fun _ -> True)
    (fun _ _ _ -> p)
=
  change_slprop_rel
    (vpure p)
    emp
    (fun _ _ -> p)
    (fun m -> pure_interp p m; reveal_emp (); intro_emp m)

let ptr = option (ref' node node)
let cells = list (Ghost.erased int & Ghost.erased ptr)

let pts_to_llist_cons (value: Ghost.erased int) (next: Ghost.erased ptr) (tl: cells)
  (pts_to_llist:(
    Ghost.erased ptr ->
    l:cells{List.length l < List.length ((value, next) :: tl)} ->
    Tot vprop))
  (p: option (ref' node node))
  (prf: squash (Some? p /\ pcm_of_ref' (Some?.v p) == node_pcm))
: vprop
= let r: ref node node_pcm = Some?.v p in
  (r `pts_to` mk_node (some value) (some next)) `star`
  (next `pts_to_llist` tl)

let rec pts_to_llist (p:Ghost.erased ptr) (l:cells)
: Tot vprop (decreases (List.length l))
= match l with
  | [] -> vpure (p == none)
  | (value, next) :: tl ->
    vpure (Some? p /\ pcm_of_ref' (Some?.v p) == node_pcm) `vdep`
    pts_to_llist_cons value next tl pts_to_llist p

let pts_to_llist_nil_eq p
: Lemma ((p `pts_to_llist` []) == vpure (p == none))
  [SMTPat (p `pts_to_llist` [])]
= ()

let pts_to_llist_cons_eq (p: Ghost.erased ptr) value next tl
: Lemma ((p `pts_to_llist` ((value, next) :: tl)) == 
    vpure (Some? p /\ pcm_of_ref' (Some?.v p) == node_pcm) `vdep`
    pts_to_llist_cons value next tl pts_to_llist p)
= assert_norm ((p `pts_to_llist` ((value, next) :: tl)) == 
    vpure (Some? p /\ pcm_of_ref' (Some?.v p) == node_pcm) `vdep`
    pts_to_llist_cons value next tl pts_to_llist p)

let pts_to_llist_cons_eq' (p: Ghost.erased ptr) value next tl prf
: Lemma (pts_to_llist_cons value next tl pts_to_llist p prf ==
    (let r: ref node node_pcm = Some?.v p in
     (r `pts_to` mk_node (some value) (some next)) `star`
     (next `pts_to_llist` tl)))
= assert_norm (pts_to_llist_cons value next tl pts_to_llist p prf ==
    (let r: ref node node_pcm = Some?.v p in
     (r `pts_to` mk_node (some value) (some next)) `star`
     (next `pts_to_llist` tl)))

assume val intro_llist_nil : unit -> SteelT unit emp (fun _ -> none `pts_to_llist` [])

// let intro_llist_nil () =
//   intro_vpure (none #(ref' node node) == none);
//   pts_to_llist_nil_eq none;
//   change_equal_slprop _ (none `pts_to_llist` [])
  
assume val intro_llist_cons
  (#opened:inames) (r: Ghost.erased (ref node node_pcm))
  (value: Ghost.erased int) (next: Ghost.erased ptr)
  (tl: cells)
: SteelGhostT unit opened
    (r `pts_to` (mk_node (some value) (some next)) `star` (next `pts_to_llist` tl))
    (fun _ -> some (Ghost.hide (Ghost.reveal r)) `pts_to_llist` ((value, next)::tl))
  
// let intro_llist_cons r value next tl = 
//   let p: Ghost.erased ptr = some (Ghost.hide (Ghost.reveal r)) in
//   intro_vpure (Some? p /\ pcm_of_ref' (Some?.v p) == node_pcm);
//   intro_vdep (vpure (Some? p /\ pcm_of_ref' (Some?.v p) == node_pcm))
//     (r `pts_to` (mk_node (some value) (some next)) `star`
//      (next `pts_to_llist` tl))
//     (pts_to_llist_cons value next tl pts_to_llist p);
//   pts_to_llist_cons_eq p value next tl;
//   change_equal_slprop _ (some (Ghost.hide (Ghost.reveal r)) `pts_to_llist` ((value, next)::tl))

assume val elim_llist_cons
  (#opened:inames) (p: Ghost.erased ptr)
  (value: Ghost.erased int) (next: Ghost.erased ptr)
  (tl: cells)
: SteelGhost (Ghost.erased (ref node node_pcm)) opened
    (p `pts_to_llist` ((value, next)::tl))
    (fun r ->
      (r `pts_to` mk_node (some value) (some next)) `star`
      (next `pts_to_llist` tl))
    (requires fun _ -> True)
    (ensures fun _ r _ -> p == some (Ghost.hide (Ghost.reveal r)))

// let elim_llist_cons p value next tl =
//   pts_to_llist_cons_eq p value next tl;
//   change_equal_slprop
//     (p `pts_to_llist` _)
//     (vpure (Some? p /\ pcm_of_ref' (Some?.v p) == node_pcm) `vdep`
//      pts_to_llist_cons value next tl pts_to_llist p);
//   let prf: Ghost.erased (t_of (vpure (Some? p /\ pcm_of_ref' (Some?.v p) == node_pcm))) =
//     elim_vdep 
//       (vpure (Some? p /\ pcm_of_ref' (Some?.v p) == node_pcm))
//       (pts_to_llist_cons value next tl pts_to_llist p)
//   in
//   elim_vpure (Some? p /\ pcm_of_ref' (Some?.v p) == node_pcm);
//   pts_to_llist_cons_eq' p value next tl prf;
//   let r: Ghost.erased (ref node node_pcm) = Some?.v p in
//   change_equal_slprop
//     (pts_to_llist_cons value next tl pts_to_llist p prf)
//     ((Ghost.reveal r `pts_to`
//       mk_node (some value) (some next)) `star`
//      (next `pts_to_llist` tl));
//   r

let rec values (l:cells) : GTot (list int) =
  match l with
  | [] -> []
  | (value, _)::tl -> Ghost.reveal value :: values tl
  
val new_llist (init:int)
  : Steel (ptr & cells)
          emp
          (fun (p, l) -> p `pts_to_llist` l)
          (requires fun _ -> True)
          (ensures fun _ (p, l) _ -> values l == [init])

#set-options "--ide_id_info_off"

let new_llist (init:int) =
  let cell: Ghost.erased int & Ghost.erased ptr = (Ghost.hide init, Ghost.hide None) in
  let r = ref_alloc node_pcm (mk_node_tot (Some init) (Some None)) in
  intro_llist_nil ();
  change_equal_slprop
    (r `pts_to` Ghost.hide (mk_node_tot (Some init) (Some None)))
    (Ghost.reveal (Ghost.hide r) `pts_to` mk_node (some init) (some none));
  intro_llist_cons r (Ghost.hide init) (Ghost.hide None) [];
  change_equal_slprop (some _ `pts_to_llist` _) (Some r `pts_to_llist` _);
  return (Some r, [cell])

val push (p:ptr) (l:cells) (value:int)
: Steel (ptr & cells)
    (p `pts_to_llist` l)
    (fun (p', l') -> p' `pts_to_llist` l')
    (requires fun _ -> True)
    (ensures fun _ (_, l') _ -> values l' == value :: values l)

let push p l value =
  let cell: Ghost.erased int & Ghost.erased ptr = (Ghost.hide value, Ghost.hide p) in
  let r = ref_alloc node_pcm (mk_node_tot (Some value) (Some p)) in
  change_equal_slprop
    (r `pts_to` Ghost.hide (mk_node_tot (Some value) (Some p)))
    (Ghost.reveal (Ghost.hide r) `pts_to` mk_node (some value) (some (Ghost.hide p)));
  intro_llist_cons (Ghost.hide r) (Ghost.hide value) (Ghost.hide p) l;
  change_equal_slprop (some _ `pts_to_llist` _) (Some r `pts_to_llist` _);
  return (Some r, cell :: l)

//val ref_alloc
//  (#a:Type0) (p: pcm a) (x: a)
//: Steel (ref a p)
//    emp
//    (fun r -> r `pts_to` x)
//    (requires fun _ -> p_refine p x)
//    (ensures fun _ _ _ -> True)

//elim_vdep
// Mutate the kth element of a list (of fixed k)
// 
// t k = type of functions that mutate kth element of a list
// 
// set_zero : Tot (t 0)
// set_succ : t k -> Tot (t (k + 1))
//
// let rec set k .. : Steel _ = 
// let rec set k .. : Tot (.. -> Steel _) = 

val push (#a:Type) (ptr:t a) (l:list (cell a)) (v:a)
  : Steel (t a & list (cell a))
          (llist ptr l)
          (fun pc -> llist (fst pc) (snd pc))
          (requires fun _ -> True)
          (ensures fun _ pc _ -> datas (snd pc) == v::datas l)

let push #a ptr l v =
  let cell = mk_cell ptr v in
  let p = alloc_pt cell in
  rewrite_slprop (llist ptr l) (llist (next cell) l) (fun _ -> ());
  intro_llist_cons p cell l;
  let pc = p, (cell::l) in
  pc

val pop (#a:Type) (ptr:t a) (l:list (cell a){Cons? l})
  : Steel a
          (llist ptr l)
          (fun _ -> llist (next (L.hd l)) (L.tl l))
          (requires fun _ -> True)
          (ensures fun _ x _ -> x == data (L.hd l))

let pop #a ptr l =
  let hd = L.hd l in
  let tl = L.tl l in
  rewrite_slprop (llist ptr l) (llist ptr (hd::tl)) (fun _ -> ());
  elim_llist_cons ptr hd tl;
  let c = read_pt ptr in
  let n = next hd in
  free_pt ptr;
  rewrite_slprop (llist (next hd) tl) (llist (next (L.hd l)) (L.tl l)) (fun _ -> ());
  return (data c)
