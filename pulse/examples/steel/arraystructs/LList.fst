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
let cells = list (int & ptr)

let pts_to_llist_cons (value: int) (next: ptr) (tl: cells)
  (pts_to_llist:(
    ptr ->
    l:Ghost.erased cells{List.length l < List.length ((value, next) :: tl)} ->
    Tot vprop))
  (p: option (ref' node node))
  (prf: squash (Some? p /\ pcm_of_ref' (Some?.v p) == node_pcm))
: vprop
= let r: ref node node_pcm = Some?.v p in
  (r `pts_to` mk_node (some value) (some next)) `star`
  (next `pts_to_llist` Ghost.hide tl)

let rec pts_to_llist ([@@@smt_fallback] p:ptr) ([@@@smt_fallback] l:Ghost.erased cells)
: Tot vprop (decreases (List.length l))
= match Ghost.reveal l with
  | [] -> vpure (p == None)
  | (value, next) :: tl ->
    vpure (Some? p /\ pcm_of_ref' (Some?.v p) == node_pcm) `vdep`
    pts_to_llist_cons value next tl pts_to_llist p

let pts_to_llist_nil_eq p
: Lemma ((p `pts_to_llist` []) == vpure (p == None))
  [SMTPat (p `pts_to_llist` [])]
= ()

let pts_to_llist_cons_eq (p:ptr) (value:int) (next:ptr) (tl:cells)
: Lemma ((p `pts_to_llist` Ghost.hide ((value, next) :: tl)) == 
    vpure (Some? p /\ pcm_of_ref' (Some?.v p) == node_pcm) `vdep`
    pts_to_llist_cons value next tl pts_to_llist p)
= assert_norm ((p `pts_to_llist` Ghost.hide ((value, next) :: tl)) == 
  (match Ghost.reveal (Ghost.hide ((value, next) :: tl)) with
  | [] -> vpure (p == None)
  | (value, next) :: tl ->
    vpure (Some? p /\ pcm_of_ref' (Some?.v p) == node_pcm) `vdep`
    pts_to_llist_cons value next tl pts_to_llist p)) 
    // TODO Why do I have to keep the match around?

let pts_to_llist_cons_eq' (p: ptr) value (next:ptr) tl prf
: Lemma (pts_to_llist_cons value next tl pts_to_llist p prf ==
    (let r: ref node node_pcm = Some?.v p in
     (r `pts_to` mk_node (some (Ghost.hide value)) (some (Ghost.hide next))) `star`
     (next `pts_to_llist` Ghost.hide tl)))
= assert_norm (pts_to_llist_cons value next tl pts_to_llist p prf ==
    (let r: ref node node_pcm = Some?.v p in
     (r `pts_to` mk_node (some value) (some next)) `star`
     (next `pts_to_llist` Ghost.hide tl)))

val intro_llist_nil : unit -> SteelT unit emp (fun _ -> None `pts_to_llist` [])

let intro_llist_nil () =
  intro_vpure (None #(ref' node node) == None);
  pts_to_llist_nil_eq None;
  change_equal_slprop _ (None `pts_to_llist` [])
  
val intro_llist_cons
  (#opened:inames) (r: ref node node_pcm)
  (value: int) (next: ptr)
  (tl: cells)
: SteelGhostT unit opened
    ((r `pts_to` mk_node (some value) (some next)) `star` (next `pts_to_llist` tl))
    (fun _ -> Some r `pts_to_llist` ((value, next)::tl))
  
let intro_llist_cons r value next tl = 
  let p: ptr = Some r in
  intro_vpure (Some? p /\ pcm_of_ref' (Some?.v p) == node_pcm);
  intro_vdep (vpure (Some? p /\ pcm_of_ref' (Some?.v p) == node_pcm))
    (r `pts_to` (mk_node (some value) (some next)) `star`
     (next `pts_to_llist` tl))
    (pts_to_llist_cons value next tl pts_to_llist p);
  pts_to_llist_cons_eq p value next tl;
  change_equal_slprop _ (Some r `pts_to_llist` ((value, next)::tl))

val elim_llist_cons
  (#opened:inames) (p: ptr)
  (value: int) (next: ptr) (tl: cells)
: SteelGhost (Ghost.erased (ref node node_pcm)) opened
    (p `pts_to_llist` ((value, next)::tl))
    (fun r ->
      (r `pts_to` mk_node (some value) (some next)) `star`
      (next `pts_to_llist` tl))
    (requires fun _ -> True)
    (ensures fun _ r _ -> p == Some (Ghost.reveal r))

let elim_llist_cons p value next tl =
  pts_to_llist_cons_eq p value next tl;
  change_equal_slprop
    (p `pts_to_llist` _)
    (vpure (Some? p /\ pcm_of_ref' (Some?.v p) == node_pcm) `vdep`
     pts_to_llist_cons value next tl pts_to_llist p);
  let prf: Ghost.erased (t_of (vpure (Some? p /\ pcm_of_ref' (Some?.v p) == node_pcm))) =
    elim_vdep 
      (vpure (Some? p /\ pcm_of_ref' (Some?.v p) == node_pcm))
      (pts_to_llist_cons value next tl pts_to_llist p)
  in
  elim_vpure (Some? p /\ pcm_of_ref' (Some?.v p) == node_pcm);
  pts_to_llist_cons_eq' p value next tl prf;
  let r: Ghost.erased (ref node node_pcm) = Some?.v p in
  change_equal_slprop
    (pts_to_llist_cons value next tl pts_to_llist p prf)
    ((Ghost.reveal r `pts_to` mk_node (some value) (some next)) `star`
     (next `pts_to_llist` tl));
  r

let rec values (l:cells) : GTot (list int) =
  match l with
  | [] -> []
  | (value, _) :: tl -> Ghost.reveal value :: values tl

#set-options "--ide_id_info_off"

val push (p:ptr) (l:Ghost.erased cells) (value:int)
: Steel (ptr & Ghost.erased cells)
    (p `pts_to_llist` l)
    (fun (p', l') -> p' `pts_to_llist` l')
    (requires fun _ -> True)
    (ensures fun _ (_, l') _ -> values l' == value :: values l)

let push p l value =
  let cell: int & ptr = (value, p) in
  let r = ref_alloc node_pcm (mk_node_tot (Some value) (Some p)) in
  intro_llist_cons r value p l;
  return (Some r, Ghost.hide (cell :: l))
  
let cells_set_hd x (l: cells) = match l with
  | [] -> []
  | (_, next) :: l' -> (x, next) :: l'

/// Mutate the head of a list

// TODO does this exist already?
assume val exfalso (#opened:inames) (p:vprop) (q:prop)
: SteelGhost unit opened emp (fun _ -> p) (requires fun _ -> False) (ensures fun _ _ _ -> q)

val pts_to_llist_nullptr (#opened:inames) (p:ptr) (l:Ghost.erased cells)
: SteelGhost unit opened
    (p `pts_to_llist` l) 
    (fun _ -> None `pts_to_llist` [])
    (requires fun _ -> p == None)
    (ensures fun _ _ _ -> Ghost.reveal l == [])

let pts_to_llist_nullptr p l =
  match Ghost.reveal l with
  | [] -> change_equal_slprop (p `pts_to_llist` l) (None `pts_to_llist` [])
  | (value, next) :: tl ->
    change_equal_slprop (p `pts_to_llist` l) (None `pts_to_llist` ((value, next) :: tl));
    let r = elim_llist_cons None value next tl in
    assert (None == Some r);
    sladmit() // TODO
    //exfalso (None `pts_to_llist` []) (Ghost.reveal l == [])

[@@erasable]
noeq type pts_to_llist_res = {
  value: int;
  next: ptr;
  tl: cells;
}

val pts_to_llist_some (#opened:inames) (p:ptr) (l:Ghost.erased cells)
: SteelGhost pts_to_llist_res opened
    (p `pts_to_llist` l) 
    (fun res -> p `pts_to_llist` ((res.value, res.next) :: res.tl))
    (requires fun _ -> Some? p)
    (ensures fun _ res _ ->
      Some? p /\ pcm_of_ref' (Some?.v p) == node_pcm /\
      Ghost.reveal l == ((res.value, res.next) :: res.tl))

let pts_to_llist_some p l =
  match Ghost.reveal l with
  | [] ->
    change_equal_slprop (p `pts_to_llist` l) (p `pts_to_llist` []);
    assert (Some? p /\ p == None);
    sladmit() // TODO
  | (value, next) :: tl ->
    change_equal_slprop (p `pts_to_llist` l) (p `pts_to_llist` ((value, next) :: tl));
    {value; next; tl}

val set_hd (p:ptr) (l:cells) (value:int)
: SteelT unit
    (p `pts_to_llist` l)
    (fun _ -> p `pts_to_llist` cells_set_hd value l)

let set_hd p l new_value =
  match p with
  | None -> pts_to_llist_nullptr p l; return ()
  | Some r ->
    let res = pts_to_llist_some p l in
    let value: Ghost.erased int = Ghost.hide res.value in
    let next: Ghost.erased ptr = Ghost.hide res.next in
    let tl: Ghost.erased cells = Ghost.hide res.tl in
    //let value: Ghost.erased int = Ghost.hide (fst value_next_tl) in
    //let next: Ghost.erased ptr = Ghost.hide (fst (snd value_next_tl)) in
    //let tl: Ghost.erased cells = Ghost.hide (snd (snd value_next_tl)) in
    change_equal_slprop (p `pts_to_llist` l)
      (Some r `pts_to_llist`
       Ghost.hide ((Ghost.reveal value, Ghost.reveal next) :: Ghost.reveal tl));
    let r' = elim_llist_cons (Some r) (Ghost.reveal value) (Ghost.reveal next) (Ghost.reveal tl) in
    let r: ref node node_pcm = r in
    //assert (Ghost.reveal r' == r);
    //slassert (Ghost.reveal r' `pts_to` mk_node (some value) (some next));
    change_equal_slprop (Ghost.reveal r' `pts_to` mk_node (some value) (some next))
      (r `pts_to` mk_node (some value) (some next));
    let r_value = addr_of_value r in
    r_value `opt_write` new_value;
    unaddr_of_value r r_value;
    intro_llist_cons r new_value next tl;
    //change_equal_slprop (Ghost.reveal r' `pts_to` mk_node _ _) (r `pts_to` mk_node _ _);
    //sladmit(); return ()
    return ()

// Mutate the kth element of a list (of fixed k)
// 
// t k = type of functions that mutate kth element of a list
// 
// set_zero : Tot (t 0)
// set_succ : t k -> Tot (t (k + 1))
//
// let rec set k .. : Steel _ = 
// let rec set k .. : Tot (.. -> Steel _) = 

(*
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
*)
