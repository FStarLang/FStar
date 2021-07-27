module LList
open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect

module R = Steel.C.Ref
open Steel.C.Ref
open Steel.C.Ptr
open Steel.C.PCM
open Steel.C.Opt
open Steel.C.Connection

/// TODO move and dedup with Steel.C.Ptr.fst

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

val unreachable (#opened:inames) (#p:vprop) (#q:'a -> vprop) (r:'a -> prop)
: SteelGhostF 'a opened p q (requires fun _ -> False) (ensures fun _ x _ -> r x)

let unreachable (#opened:inames) (#p:vprop) (#q:'a -> vprop) (r:'a -> prop)
: SteelGhostF 'a opened p q (requires fun _ -> False) (ensures fun _ x _ -> r x)
= let x: 'a = FStar.IndefiniteDescription.indefinite_description_tot 'a (fun _ -> True) in
  change_slprop_rel p (q x) (fun _ _ -> r x) (fun _ -> ());
  x

// ----------------------------------------

open ListNode

let cell = int & ptr node node
let cells = list cell

let hd_node (l: cells): option node =
  match l with
  | (value, next) :: _ -> Some (mk_node (Some value) (Some next))
  | [] -> None

let pts_to_llist_tl (l:cells)
  (pts_to_llist:(
    p:ptr node node -> 
    l':cells{List.length l' < List.length l} -> 
    Tot vprop))
: Tot vprop
= match l with
  | [] -> emp
  | (value, next) :: tl -> next `pts_to_llist` tl

let pts_to_llist_nullptr_condition (p: ptr node node) (l: cells)
: Tot prop
= p == nullptr <==> l == []

let rec pts_to_llist (p:ptr node node) ([@@@smt_fallback] l:cells)
: Tot vprop (decreases (List.length l))
= vpure (pts_to_llist_nullptr_condition p l) `star`
  pts_to_or_null p node_pcm (hd_node l) `star`
  pts_to_llist_tl l pts_to_llist

let unfold_pts_to_llist (#opened:inames) (p:ptr node node) (l:cells)
: SteelGhost unit opened
    (p `pts_to_llist` l)
    (fun _ -> 
      pts_to_or_null p node_pcm (hd_node l) `star`
      pts_to_llist_tl l pts_to_llist)
    (requires fun _ -> True)
    (ensures fun _ _ _ -> pts_to_llist_nullptr_condition p l)
= change_equal_slprop
    (p `pts_to_llist` l)
    (vpure (pts_to_llist_nullptr_condition p l) `star`
     pts_to_or_null p node_pcm (hd_node l) `star`
     pts_to_llist_tl l pts_to_llist);
  elim_vpure _

let fold_pts_to_llist (#opened:inames) (p:ptr node node) (l:cells)
: SteelGhost unit opened
    (pts_to_or_null p node_pcm (hd_node l) `star`
     pts_to_llist_tl l pts_to_llist)
    (fun _ -> p `pts_to_llist` l)
    (requires fun _ -> pts_to_llist_nullptr_condition p l)
    (ensures fun _ _ _ -> True)
= intro_vpure (pts_to_llist_nullptr_condition p l);
  change_equal_slprop
    (vpure (pts_to_llist_nullptr_condition p l) `star`
     pts_to_or_null p node_pcm (hd_node l) `star`
     pts_to_llist_tl l pts_to_llist)
    (p `pts_to_llist` l)

let intro_pts_to_llist_nil #opened p
: SteelGhost unit opened 
    emp
    (fun _ -> p `pts_to_llist` [])
    (requires fun _ -> p == nullptr)
    (ensures fun _ _ _ -> True)
= intro_vpure (pts_to_llist_nullptr_condition p []);
  intro_pts_to_or_null_nullptr #node node_pcm;
  change_equal_slprop
    (pts_to_or_null (nullptr #node) node_pcm (None))
    (pts_to_or_null p node_pcm (hd_node ([] #cell)))

let elim_pts_to_llist_nil #opened p
: SteelGhost unit opened 
    (p `pts_to_llist` [])
    (fun _ -> emp)
    (requires fun _ -> True)
    (ensures fun _ _ _ -> p == nullptr)
= change_equal_slprop
    (p `pts_to_llist` [])
    (vpure (pts_to_llist_nullptr_condition p []) `star`
     pts_to_or_null p node_pcm None `star` emp);
  elim_vpure (p == nullptr <==> [] #cell == []);
  elim_pts_to_or_null_nullptr p

let intro_pts_to_llist_cons #opened p value_next value next (l: Ghost.erased cells)
: SteelGhost unit opened 
    (pts_to p node_pcm value_next `star` (next `pts_to_llist` l))
    (fun _ -> p `pts_to_llist` ((value, next) :: Ghost.reveal l))
    (requires fun _ -> value_next == mk_node (some value) (some next))
    (ensures fun _ _ _ -> p =!= nullptr)
= change_equal_slprop
    (pts_to p node_pcm value_next)
    (pts_to p node_pcm (mk_node (some value) (some next)));
  pts_to_nonnull p; assert (p =!= nullptr);
  let l': Ghost.erased cells = Ghost.hide ((value, next) :: Ghost.reveal l) in
  intro_vpure (p == nullptr <==> Ghost.reveal l' == []);
  assert (hd_node l' == Some (mk_node (Some value) (Some next)));
  intro_pts_to_or_null p;
  change_equal_slprop (next `pts_to_llist` l) (pts_to_llist_tl l' pts_to_llist);
  change_equal_slprop
    (vpure (pts_to_llist_nullptr_condition p (Ghost.reveal l')) `star`
     pts_to_or_null p node_pcm (hd_node l') `star`
     pts_to_llist_tl l' pts_to_llist)
    (p `pts_to_llist` _)

[@@erasable]
noeq type elim_pts_to_llist_cons_res = {
  value: int;
  next: ptr node node;
  tl: cells;
}

let elim_pts_to_llist_cons #opened p (l: Ghost.erased cells)
: SteelGhost elim_pts_to_llist_cons_res opened 
    (p `pts_to_llist` l)
    (fun res ->
      pts_to p node_pcm (mk_node (some res.value) (some res.next)) `star`
      (res.next `pts_to_llist` res.tl))
    (requires fun _ -> p =!= nullptr)
    (ensures fun _ res _ -> Ghost.reveal l == (res.value, res.next) :: res.tl)
= change_equal_slprop (p `pts_to_llist` l)
    (vpure (pts_to_llist_nullptr_condition p (Ghost.reveal l)) `star`
     pts_to_or_null p node_pcm (hd_node l) `star`
     pts_to_llist_tl l pts_to_llist);
  elim_vpure (pts_to_llist_nullptr_condition p (Ghost.reveal l));
  match Ghost.reveal l with
  | [] -> unreachable (fun res -> Ghost.reveal l == (res.value, res.next) :: res.tl)
  | (value, next) :: tl ->
    assert (hd_node l == Some (mk_node (Some value) (Some next)));
    let w = elim_pts_to_or_null p in
    assert (Ghost.reveal w == mk_node (Some value) (Some next));
    change_equal_slprop (pts_to_llist_tl l pts_to_llist) (next `pts_to_llist` tl);
    {value; next; tl}

let ptr a = ptr a a

let intro_llist_nil ()
: SteelT (ptr node) emp (fun p -> p `pts_to_llist` [])
= let p = nullptr in
  intro_pts_to_llist_nil p;
  sladmit(); // TODO why
  return p

let rec values (l:cells) : GTot (list int) =
  match l with
  | [] -> []
  | (value, _) :: tl -> Ghost.reveal value :: values tl

#set-options "--ide_id_info_off"

val push (p:ptr node) (l:Ghost.erased cells) (value:int)
: Steel (ptr node & Ghost.erased cells)
    (p `pts_to_llist` l)
    (fun (p', l') -> p' `pts_to_llist` l')
    (requires fun _ -> True)
    (ensures fun _ (_, l') _ -> values l' == value :: values l)

let push p l value =
  let cell: int & ptr node = (value, p) in
  let value_next: node = mk_node (Some value) (Some p) in
  let r = ref_alloc node_pcm value_next in
  let q = intro_pts_to r in
  intro_pts_to_llist_cons q value_next value p l;
  return (q, Ghost.hide (cell :: l))
  
let cells_set_hd x (l: cells) = match l with
  | [] -> []
  | (_, next) :: l' -> (x, next) :: l'

val pts_to_llist_nullptr (#opened:inames) (p:ptr node) (l:Ghost.erased cells)
: SteelGhost unit opened
    (p `pts_to_llist` l) 
    (fun _ -> p `pts_to_llist` l)
    (requires fun _ -> p == nullptr)
    (ensures fun _ _ _ -> Ghost.reveal l == [])

let pts_to_llist_nullptr p l =
  unfold_pts_to_llist p l;
  assert (Ghost.reveal l == []);
  fold_pts_to_llist p l

(* Currently z3 is going through the lemma
      refine value /\ refine next ==> refine (mk_node value next)
   plus the fact that for our PCMs, ~ refine one.
   If change refine predicate/drop the side condition ~ refine one, will 
   need to expose the proper lemmas about mk_node in ListNode.fsti
*)
let nontrivial_fact_about_mk_node value next
: Lemma (Ghost.reveal (mk_node (some value) (some next)) =!= one node_pcm)
= ()

val is_empty
  (#l: Ghost.erased cells) (p: ptr node)
: Steel bool
    (p `pts_to_llist` l)
    (fun _ -> p `pts_to_llist` l)
    (requires fun _ -> True)
    (ensures fun _ b _ -> b <==> p == nullptr)
let is_empty #l p =
  unfold_pts_to_llist p l;
  let b = is_null p in
  fold_pts_to_llist p l;
  return b

val set_first (p:ptr node) (l:Ghost.erased cells) (value:int)
: SteelT unit
    (p `pts_to_llist` l)
    (fun _ -> p `pts_to_llist` cells_set_hd value l)

val intro_pts_to_llist_cons' : #opened:inames ->
      p: ptr node ->
      value: int ->
      next: ptr node ->
      l: Ghost.erased cells
    -> Steel.Effect.Atomic.SteelGhostT unit
        opened
        (star (pts_to p node_pcm (mk_node (some (Ghost.hide value)) (some (Ghost.hide next))))
	  (pts_to_llist next l))
        (fun _ ->
            pts_to_llist p
              (Ghost.hide (FStar.Pervasives.Native.Mktuple2 value next :: Ghost.reveal l)))

let intro_pts_to_llist_cons' p value next l = 
  intro_pts_to_llist_cons p
    (mk_node (some (Ghost.hide value)) (some (Ghost.hide next))) 
    value next l

(* TODO move to Steel.C.Ptr? *)
val intro_pts_to'
  (#pb: pcm 'b) (#v: Ghost.erased 'b)
  (r: ref 'a pb) (p: Steel.C.Ptr.ptr 'a 'b)
: Steel unit
    (r `R.pts_to` v)
    (fun _ -> pts_to p pb v)
    (requires fun _ -> p == vptr r)
    (ensures fun _ _ _ -> True)

let intro_pts_to' r p =
  let p' = intro_pts_to r in
  change_equal_slprop (pts_to p' _ _) (pts_to p _ _)

let set_first p l new_value =
  let b = is_empty p in
  if b then begin
    pts_to_llist_nullptr p l;
    return ()
  end else begin
    let res = elim_pts_to_llist_cons p l in
    let r = elim_pts_to p in
    let r_value = addr_of_value r in
    r_value `opt_write` new_value;
    unaddr_of_value r r_value;
    intro_pts_to' r p;
    intro_pts_to_llist_cons' p new_value res.next res.tl;
    return ()
  end
