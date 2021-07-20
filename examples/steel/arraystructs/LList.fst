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

// ----------------------------------------

open ListNode

let cells = list (int & ptr node node)

let rec pts_to_llist (p:ptr node node) ([@@@smt_fallback] l:Ghost.erased cells)
: Tot vprop (decreases (List.length l))
= match Ghost.reveal l with
  | [] -> vpure (p == nullptr)
  | (value, next) :: tl ->
    pts_to p node_pcm (mk_node (some value) (some next)) `star`
    (next `pts_to_llist` Ghost.hide tl)

let pts_to_llist_nil_eq p
: Lemma ((p `pts_to_llist` []) == vpure (p == nullptr))
  [SMTPat (p `pts_to_llist` [])]
= ()

let pts_to_llist_cons_eq (p:ptr node node) (value:int) (next:ptr node node) (tl:cells)
: Lemma ((p `pts_to_llist` Ghost.hide ((value, next) :: tl)) == 
    pts_to p node_pcm (mk_node (some value) (some next)) `star`
    (next `pts_to_llist` Ghost.hide tl))
= ()

val intro_llist_nil : unit -> SteelT unit emp (fun _ -> nullptr `pts_to_llist` [])

let intro_llist_nil () =
  intro_vpure (nullptr #node #node == nullptr);
  pts_to_llist_nil_eq nullptr;
  change_equal_slprop _ (nullptr `pts_to_llist` [])
  
val intro_llist_cons
  (#opened:inames) (p: ptr node node)
  (value: int) (next: ptr node node)
  (tl: cells)
: SteelGhostT unit opened
    ((pts_to p node_pcm (mk_node (some value) (some next))) `star` (next `pts_to_llist` tl))
    (fun _ -> p `pts_to_llist` ((value, next)::tl))
  
let intro_llist_cons p' value next tl = change_equal_slprop _ _

val elim_llist_cons
  (#opened:inames) (p: ptr node node)
  (value: int) (next: ptr node node) (tl: cells)
: SteelGhostT unit opened
    (p `pts_to_llist` ((value, next)::tl))
    (fun _ ->
      (pts_to p node_pcm (mk_node (some value) (some next))) `star`
      (next `pts_to_llist` tl))

let elim_llist_cons p value next tl =
  change_equal_slprop
    (p `pts_to_llist` ((value, next)::tl)) // TODO why can't these be inferred?
    ((pts_to p node_pcm (mk_node (some value) (some next))) `star`
     (next `pts_to_llist` tl))

let rec values (l:cells) : GTot (list int) =
  match l with
  | [] -> []
  | (value, _) :: tl -> Ghost.reveal value :: values tl

#set-options "--ide_id_info_off"

val push (p:ptr node node) (l:Ghost.erased cells) (value:int)
: Steel (ptr node node & Ghost.erased cells)
    (p `pts_to_llist` l)
    (fun (p', l') -> p' `pts_to_llist` l')
    (requires fun _ -> True)
    (ensures fun _ (_, l') _ -> values l' == value :: values l)

let push p l value =
  let cell: int & ptr node node = (value, p) in
  let r = ref_alloc node_pcm (mk_node_tot (Some value) (Some p)) in
  let q = intro_pts_to r in
  intro_llist_cons q value p l;
  return (q, Ghost.hide (cell :: l))
  
let cells_set_hd x (l: cells) = match l with
  | [] -> []
  | (_, next) :: l' -> (x, next) :: l'

val exfalso (#opened:inames) (p:vprop) (q:'a -> vprop) (r:'a -> prop)
: SteelGhostF 'a opened p q (requires fun _ -> False) (ensures fun _ x _ -> r x)

let exfalso (#opened:inames) (p:vprop) (q:'a -> vprop) (r:'a -> prop)
: SteelGhostF 'a opened p q (requires fun _ -> False) (ensures fun _ x _ -> r x)
= let x: 'a = FStar.IndefiniteDescription.indefinite_description_tot 'a (fun _ -> True) in
  change_slprop_rel p (q x) (fun _ _ -> r x) (fun _ -> ());
  x

val pts_to_llist_nullptr (#opened:inames) (p:ptr node node) (l:Ghost.erased cells)
: SteelGhost unit opened
    (p `pts_to_llist` l) 
    (fun _ -> p `pts_to_llist` l)
    (requires fun _ -> p == nullptr)
    (ensures fun _ _ _ -> Ghost.reveal l == [])

let pts_to_llist_nullptr p l =
  match Ghost.reveal l with
  | [] -> change_equal_slprop (p `pts_to_llist` l) (p `pts_to_llist` l) // TODO why can't just put ()
  | (value, next) :: tl ->
    change_equal_slprop (p `pts_to_llist` l) (p `pts_to_llist` ((value, next) :: tl));
    let r = elim_llist_cons p value next tl in
    pts_to_nonnull p;
    assert (p =!= nullptr);
    assert (p == nullptr);
    exfalso _ _ (fun _ -> Ghost.reveal l == [])

[@@erasable]
noeq type pts_to_llist_res = {
  value: int;
  next: ptr node node;
  tl: cells;
}

val pts_to_llist_some (#opened:inames) (p:ptr node node) (l:Ghost.erased cells)
: SteelGhost pts_to_llist_res opened
    (p `pts_to_llist` l) 
    (fun res -> p `pts_to_llist` ((res.value, res.next) :: res.tl))
    (requires fun _ -> p =!= nullptr)
    (ensures fun _ res _ -> Ghost.reveal l == ((res.value, res.next) :: res.tl))

let pts_to_llist_some p l =
  match Ghost.reveal l with
  | [] ->
    change_equal_slprop (p `pts_to_llist` l) (p `pts_to_llist` []);
    assert (p == nullptr);
    assert (p =!= nullptr);
    exfalso _ _ (fun res -> Ghost.reveal l == ((res.value, res.next) :: res.tl))
  | (value, next) :: tl ->
    change_equal_slprop (p `pts_to_llist` l) (p `pts_to_llist` ((value, next) :: tl));
    {value; next; tl}

val set_hd (p:ptr node node) (l:Ghost.erased cells) (value:int)
: SteelT unit
    (p `pts_to_llist` l)
    (fun _ -> p `pts_to_llist` cells_set_hd value l)

// Problem: need (pts_to_or_null p pb v), where v =!= one, before can check whether it's null
// Unclear how to rearrange pts_to_or_null

let set_hd p l new_value =
  //let b = is_null p in
  if true then begin
    //pts_to_llist_nullptr p l;
    sladmit(); return ()
  end else begin
    sladmit(); return ()
    //let res = pts_to_llist_some p l in
    //let value: Ghost.erased int = Ghost.hide res.value in
    //let next: Ghost.erased ptr = Ghost.hide res.next in
    //let tl: Ghost.erased cells = Ghost.hide res.tl in
    //change_equal_slprop (p `pts_to_llist` _) (p `pts_to_llist` _);
    //let r' = elim_llist_cons p (Ghost.reveal value) (Ghost.reveal next) (Ghost.reveal tl) in
    //let r: ref node node_pcm = r in
    //change_equal_slprop
    //  (Ghost.reveal r' `pts_to` mk_node (some value) (some next))
    //  (r `pts_to` mk_node (some value) (some next));
    //let r_value = addr_of_value r in
    //r_value `opt_write` new_value;
    //unaddr_of_value r r_value;
    //intro_llist_cons r p new_value next tl;
    //return ()
  end

// for the presentation, write write code for set_hd
// based on assume val for needed selectors, then solve assumes

let rec cells_set_nth (n:nat) (value:int) (l:cells) : Tot cells (decreases n) =
  if n = 0 then cells_set_hd value l
  else match l with
  | [] -> []
  | hd :: tl -> hd :: cells_set_nth (n - 1) value tl

let rec cells_set_nth_nil n value
: Lemma (ensures cells_set_nth n value [] == []) (decreases n)
= if n = 0 then () else cells_set_nth_nil (n - 1) value

let llist_setter (n:nat) =
  p:ptr node node -> l:Ghost.erased cells -> value:int ->
  SteelT unit
    (p `pts_to_llist` l)
    (fun _ -> p `pts_to_llist` cells_set_nth n value l)

let llist_set_zero: llist_setter 0 = set_hd

(*
let aux n (ih: llist_setter n) (p: ptr) (l: Ghost.erased cells) (new_value: int)
: SteelT unit
    (p `pts_to_llist` l)
    (fun _ -> p `pts_to_llist` cells_set_nth (n + 1) new_value l)
= assume (Some? p);
  // match p with
  // | None ->
  //   pts_to_llist_nullptr p l;
  //   cells_set_nth_nil (n + 1) value;
  //   change_equal_slprop
  //     (None `pts_to_llist` [])
  //     (p `pts_to_llist` cells_set_nth (n + 1) value l);
  //   return ()
  // | Some r ->
  let Some r = p in
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
    change_equal_slprop (Ghost.reveal r' `pts_to` mk_node (some value) (some next))
      (r `pts_to` mk_node (some value) (some next));
    let r_next = addr_of_next r in
    let q: ptr = opt_read r_next in
    assert (q == Ghost.reveal next);
    unaddr_of_next r r_next;
    change_equal_slprop (Ghost.reveal next `pts_to_llist` _) (q `pts_to_llist` _);
    ih q tl new_value;
    change_equal_slprop (q `pts_to_llist` _) (Ghost.reveal next `pts_to_llist` _);
    intro_llist_cons r (Ghost.reveal value) (Ghost.reveal next) _;
//val intro_llist_cons
//  (#opened:inames) (r: ref node node_pcm)
//  (value: int) (next: ptr)
//  (tl: cells)
//: SteelGhostT unit opened
//    ((r `pts_to` mk_node (some value) (some next)) `star` (next `pts_to_llist` tl))
//    (fun _ -> Some r `pts_to_llist` ((value, next)::tl))
    sladmit(); return ()
    // //assert (Ghost.reveal r' == r);
    // //slassert (Ghost.reveal r' `pts_to` mk_node (some value) (some next));
    // let r_value = addr_of_value r in
    // r_value `opt_write` new_value;
    // unaddr_of_value r r_value;
    // intro_llist_cons r new_value next tl;
    // //change_equal_slprop (Ghost.reveal r' `pts_to` mk_node _ _) (r `pts_to` mk_node _ _);
    // //sladmit(); return ()
    // return ()

let llist_set_succ n (ih: llist_setter n): llist_setter (n + 1) =
  let aux (p: ptr) (l: Ghost.erased cells) (value: int)
  : SteelT unit
      (p `pts_to_llist` l)
      (fun _ -> p `pts_to_llist` cells_set_nth (n + 1) value l)
  = assume (Some? p);
    // match p with
    // | None ->
    //   pts_to_llist_nullptr p l;
    //   cells_set_nth_nil (n + 1) value;
    //   change_equal_slprop
    //     (None `pts_to_llist` [])
    //     (p `pts_to_llist` cells_set_nth (n + 1) value l);
    //   return ()
    // | Some r ->
    let Some r = p in
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
      change_equal_slprop (Ghost.reveal r' `pts_to` mk_node (some value) (some next))
        (r `pts_to` mk_node (some value) (some next));
      let r_next = addr_of_next r in
      let q: ptr = opt_read r_next in
      unaddr_of_next r r_next;
      //ih q tl value;
      sladmit(); return ()
      // //assert (Ghost.reveal r' == r);
      // //slassert (Ghost.reveal r' `pts_to` mk_node (some value) (some next));
      // let r_value = addr_of_value r in
      // r_value `opt_write` new_value;
      // unaddr_of_value r r_value;
      // intro_llist_cons r new_value next tl;
      // //change_equal_slprop (Ghost.reveal r' `pts_to` mk_node _ _) (r `pts_to` mk_node _ _);
      // //sladmit(); return ()
      // return ()
  in aux

*)

// TODO look at #2319, construct module of (possibly null) pointers
// (define pts_to_or_null; can compare against null only if points to non-unit)

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
