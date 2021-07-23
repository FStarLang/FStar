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

let hd_node (l: Ghost.erased cells): Ghost.erased (option node) =
  match Ghost.reveal l with
  | (value, next) :: _ -> some (mk_node (some value) (some next))
  | [] -> none

let pts_to_llist_tl (l:Ghost.erased cells)
  (pts_to_llist:(
    p:ptr node node -> 
    l':Ghost.erased cells{List.length l' < List.length l} -> 
    Tot vprop))
: Tot vprop
= match Ghost.reveal l with
  | [] -> emp
  | (value, next) :: tl -> next `pts_to_llist` tl

let rec pts_to_llist (p:ptr node node) ([@@@smt_fallback] l:Ghost.erased cells)
: Tot vprop (decreases (List.length l))
= vpure (p == nullptr <==> Ghost.reveal l == []) `star`
  pts_to_or_null p node_pcm (hd_node l) `star`
  pts_to_llist_tl l pts_to_llist

let unfold_pts_to_llist (#opened:inames) (p:ptr node node) (l:Ghost.erased cells)
: SteelGhost unit opened
    (p `pts_to_llist` l)
    (fun _ -> 
      pts_to_or_null p node_pcm (hd_node l) `star`
      pts_to_llist_tl l pts_to_llist)
    (requires fun _ -> True)
    (ensures fun _ _ _ -> p == nullptr <==> Ghost.reveal l == [])
= change_equal_slprop
    (p `pts_to_llist` l)
    (vpure (p == nullptr <==> Ghost.reveal l == []) `star`
     pts_to_or_null p node_pcm (hd_node l) `star`
     pts_to_llist_tl l pts_to_llist);
  elim_vpure _

let fold_pts_to_llist (#opened:inames) (p:ptr node node) (l:Ghost.erased cells)
: SteelGhost unit opened
    (pts_to_or_null p node_pcm (hd_node l) `star`
     pts_to_llist_tl l pts_to_llist)
    (fun _ -> p `pts_to_llist` l)
    (requires fun _ -> p == nullptr <==> Ghost.reveal l == [])
    (ensures fun _ _ _ -> True)
= intro_vpure (p == nullptr <==> Ghost.reveal l == []);
  change_equal_slprop
    (vpure (p == nullptr <==> Ghost.reveal l == []) `star`
     pts_to_or_null p node_pcm (hd_node l) `star`
     pts_to_llist_tl l pts_to_llist)
    (p `pts_to_llist` l)

let intro_pts_to_llist_nil #opened p
: SteelGhost unit opened 
    emp
    (fun _ -> p `pts_to_llist` Ghost.hide [])
    (requires fun _ -> p == nullptr)
    (ensures fun _ _ _ -> True)
= intro_vpure (p == nullptr <==> Ghost.reveal (Ghost.hide ([] #cell)) == []);
  intro_pts_to_or_null_nullptr node_pcm;
  change_equal_slprop
    (vpure (p == nullptr <==> Ghost.reveal (Ghost.hide ([] #cell)) == []) `star`
     pts_to_or_null (nullptr #node) node_pcm none `star` emp)
    (p `pts_to_llist` Ghost.hide [])

let elim_pts_to_llist_nil #opened p
: SteelGhost unit opened 
    (p `pts_to_llist` Ghost.hide [])
    (fun _ -> emp)
    (requires fun _ -> True)
    (ensures fun _ _ _ -> p == nullptr)
= change_equal_slprop
    (p `pts_to_llist` Ghost.hide [])
    (vpure (p == nullptr <==> Ghost.reveal (Ghost.hide ([] #cell)) == []) `star`
     pts_to_or_null p node_pcm none `star` emp);
  elim_vpure (p == nullptr <==> Ghost.reveal (Ghost.hide ([] #cell)) == []);
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
  assert (hd_node l' == some (mk_node (some value) (some next)));
  intro_pts_to_or_null p;
  change_equal_slprop (next `pts_to_llist` l) (pts_to_llist_tl l' pts_to_llist);
  change_equal_slprop
    (vpure (p == nullptr <==> Ghost.reveal l' == []) `star`
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
    (vpure (p == nullptr <==> Ghost.reveal l == []) `star`
     pts_to_or_null p node_pcm (hd_node l) `star`
     pts_to_llist_tl l pts_to_llist);
  elim_vpure (p == nullptr <==> Ghost.reveal l == []);
  match Ghost.reveal l with
  | [] -> unreachable (fun res -> Ghost.reveal l == (res.value, res.next) :: res.tl)
  | (value, next) :: tl ->
    assert (hd_node l == some (mk_node (some value) (some next)));
    let w = elim_pts_to_or_null p in
    assert (w == mk_node (some value) (some next));
    change_equal_slprop (pts_to_llist_tl l pts_to_llist) (next `pts_to_llist` tl);
    {value; next; tl}

let ptr a = ptr a a

let intro_llist_nil ()
: SteelT (ptr node) emp (fun p -> p `pts_to_llist` [])
= let p = nullptr in
  intro_pts_to_llist_nil p;
  return p

let rec values (l:cells) : GTot (list int) =
  match l with
  | [] -> []
  | (value, _) :: tl -> Ghost.reveal value :: values tl

#set-options "--ide_id_info_off"

val push (p:ptr node) (l:Ghost.erased cells) (value:int)
: Steel (ptr node & _)
    (p `pts_to_llist` l)
    (fun (p', l') -> p' `pts_to_llist` l')
    (requires fun _ -> True)
    (ensures fun _ (_, l') _ -> values l' == value :: values l)

let push p l value =
  let cell: int & ptr node = (value, p) in
  let value_next: node = mk_node_tot (Some value) (Some p) in
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

assume val intro_pts_to_llist_cons' : #opened:inames ->
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

assume val addr_of_value
  (#value:Ghost.erased (option int))
  (#next:Ghost.erased (option (Steel.C.Ptr.ptr node node)))
  (p: Steel.C.Ptr.ptr node node)
: Steel (Steel.C.Ptr.ptr node (option int))
    (pts_to p node_pcm (mk_node value next))
    (fun q ->
       (pts_to p node_pcm (mk_node none next)) `star`
       (pts_to q opt_pcm value))
    (requires (fun _ -> True))
    (ensures (fun _ q _ -> ptr_focused q p _value))

assume val unaddr_of_value
  (#value:Ghost.erased (option int))
  (#next:Ghost.erased (option (Steel.C.Ptr.ptr node node)))
  (p: Steel.C.Ptr.ptr node node)
  (q: Steel.C.Ptr.ptr node (option int))
: Steel unit
    ((pts_to p node_pcm (mk_node none next)) `star`
     (pts_to q opt_pcm value))
    (fun q -> pts_to p node_pcm (mk_node value next))
    (requires (fun _ -> ptr_focused q p _value))
    (ensures (fun _ _ _ -> True))

val set_first (p:ptr node) (l:Ghost.erased cells) (value:int)
: SteelT unit
    (p `pts_to_llist` l)
    (fun _ -> p `pts_to_llist` cells_set_hd value l)

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

let set_first p l new_value =
  let b = is_empty p in
  if b then begin
    pts_to_llist_nullptr p l;
    return ()
  end else begin
    let res = elim_pts_to_llist_cons p l in
    let p_value = addr_of_value p in
    p_value `ptr_opt_write` new_value;
    unaddr_of_value p p_value;
    intro_pts_to_llist_cons' p new_value res.next res.tl;
    return ()
  end

let rec cells_set_nth (n:nat) (value:int) (l:cells) : Tot cells (decreases n) =
  if n = 0 then cells_set_hd value l
  else match l with
  | [] -> []
  | hd :: tl -> hd :: cells_set_nth (n - 1) value tl

let rec cells_set_nth_nil n value
: Lemma (ensures cells_set_nth n value [] == []) (decreases n)
= if n = 0 then () else cells_set_nth_nil (n - 1) value

let llist_setter (n:nat) =
  p:ptr node -> l:Ghost.erased cells -> value:int ->
  SteelT unit
    (p `pts_to_llist` l)
    (fun _ -> p `pts_to_llist` cells_set_nth n value l)

let llist_set_zero: llist_setter 0 = set_hd

// TODO set_hd: can make helper function is_empty to check whether list is empty or not

let aux n value l = cells_set_nth (n + 1) value l

let aux n (ih: llist_setter n) (p: ptr node) (l: Ghost.erased cells) (new_value: int)
: SteelT unit
    (p `pts_to_llist` l)
    (fun _ -> p `pts_to_llist` cells_set_nth (n + 1) new_value l)
= unfold_pts_to_llist p l;
  let b = is_null p in
  fold_pts_to_llist p l;
  assume (b == false);
  //if b then begin
  //  pts_to_llist_nullptr p l;
  //  cells_set_nth_nil (n + 1) new_value;
  //  return ()
  //end else begin
    let res = elim_pts_to_llist_cons p l in
    let r = elim_pts_to p in
    let r_next = addr_of_next r in
    let q = opt_read r_next in
    unaddr_of_next r r_next;
    assert (q == res.next);
    change_equal_slprop (res.next `pts_to_llist` _) (q `pts_to_llist` _);
    ih q res.tl new_value;
    //let p' = intro_pts_to r in
    //change_equal_slprop (pts_to p' node_pcm _) (pts_to p node_pcm _);
    //intro_pts_to_llist_cons p
    //  (mk_node (some (Ghost.hide new_value)) (some (Ghost.hide res.next)))
    //  new_value res.next res.tl;
    sladmit();
    return ()
  //end

  // assume (Some? p);
  // // match p with
  // // | None ->
  // //   pts_to_llist_nullptr p l;
  // //   cells_set_nth_nil (n + 1) value;
  // //   change_equal_slprop
  // //     (None `pts_to_llist` [])
  // //     (p `pts_to_llist` cells_set_nth (n + 1) value l);
  // //   return ()
  // // | Some r ->
  // let Some r = p in
  //   let res = pts_to_llist_some p l in
  //   let value: Ghost.erased int = Ghost.hide res.value in
  //   let next: Ghost.erased ptr = Ghost.hide res.next in
  //   let tl: Ghost.erased cells = Ghost.hide res.tl in
  //   //let value: Ghost.erased int = Ghost.hide (fst value_next_tl) in
  //   //let next: Ghost.erased ptr = Ghost.hide (fst (snd value_next_tl)) in
  //   //let tl: Ghost.erased cells = Ghost.hide (snd (snd value_next_tl)) in
  //   change_equal_slprop (p `pts_to_llist` l)
  //     (Some r `pts_to_llist`
  //      Ghost.hide ((Ghost.reveal value, Ghost.reveal next) :: Ghost.reveal tl));
  //   let r' = elim_llist_cons (Some r) (Ghost.reveal value) (Ghost.reveal next) (Ghost.reveal tl) in
  //   let r: ref node node_pcm = r in
  //   change_equal_slprop (Ghost.reveal r' `pts_to` mk_node (some value) (some next))
  //     (r `pts_to` mk_node (some value) (some next));
  //   let r_next = addr_of_next r in
  //   let q: ptr = opt_read r_next in
  //   assert (q == Ghost.reveal next);
  //   unaddr_of_next r r_next;
  //   change_equal_slprop (Ghost.reveal next `pts_to_llist` _) (q `pts_to_llist` _);
  //   ih q tl new_value;
  //   change_equal_slprop (q `pts_to_llist` _) (Ghost.reveal next `pts_to_llist` _);
  //   intro_llist_cons r (Ghost.reveal value) (Ghost.reveal next) _;
//// val intro_llist_cons
////   (#opened:inames) (r: ref node node_pcm)
////   (value: int) (next: ptr)
////   (tl: cells)
//// : SteelGhostT unit opened
////     ((r `pts_to` mk_node (some value) (some next)) `star` (next `pts_to_llist` tl))
////     (fun _ -> Some r `pts_to_llist` ((value, next)::tl))
  //   sladmit(); return ()
  //   // //assert (Ghost.reveal r' == r);
  //   // //slassert (Ghost.reveal r' `pts_to` mk_node (some value) (some next));
  //   // let r_value = addr_of_value r in
  //   // r_value `opt_write` new_value;
  //   // unaddr_of_value r r_value;
  //   // intro_llist_cons r new_value next tl;
  //   // //change_equal_slprop (Ghost.reveal r' `pts_to` mk_node _ _) (r `pts_to` mk_node _ _);
  //   // //sladmit(); return ()
  //   // return ()
  // let set_hd p l new_value =

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
