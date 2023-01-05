module Selectors.LList3

open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect
open Selectors.ArrayRef

module L = FStar.List.Tot

/// This module provides the same interface as Selectors.LList.
/// The difference is in the implementation, it uses a newer, promising style to handle vprop.
/// Instead of going down all the way to the underlying slprop representation, it uses different
/// combinators to define the core list vprop

/// Abstract type of a list cell containing a value of type [a]
val cell (a:Type0) : Type0
/// The type of a list: A reference to a cell
inline_for_extraction
let t (a:Type0) = ref (cell a)

(* Helpers to manipulate cells while keeping its definition abstract *)

inline_for_extraction
val next (#a:Type0) (c:cell a) : t a
inline_for_extraction
val data (#a:Type0) (c:cell a) : a
inline_for_extraction
val mk_cell (#a:Type0) (n: t a) (d:a)
  : Pure (cell a)
    (requires True)
    (ensures fun c ->
      next c == n /\
      data c == d)


/// The null list pointer
inline_for_extraction
val null_llist (#a:Type) : t a

/// Lifting the null pointer check to empty lists
inline_for_extraction
val is_null (#a:Type) (ptr:t a) : (b:bool{b <==> ptr == null_llist})


/// Separation logic predicate stating that reference [r] points to a valid list in memory
val llist_sl (#a:Type0) (r:t a) : slprop u#1

/// Selector of a list. Returns an F* list of elements of type [a]
val llist_sel (#a:Type0) (r:t a) : selector (list a) (llist_sl r)

/// Combining the two above into a linked list vprop
[@@__steel_reduce__]
let llist' #a r : vprop' =
  {hp = llist_sl r;
   t = list a;
   sel = llist_sel r}
unfold
let llist (#a:Type0) (r:t a) = VUnit (llist' r)

/// A wrapper to access a list selector more easily.
/// Ensuring that the corresponding llist vprop is in the context is done by
/// calling a variant of the framing tactic, as defined in Steel.Effect.Common
[@@ __steel_reduce__]
let v_llist (#a:Type0) (#p:vprop) (r:t a)
  (h:rmem p{FStar.Tactics.with_tactic selector_tactic (can_be_split p (llist r) /\ True)}) : GTot (list a)
  = h (llist r)

(** Stateful lemmas to fold and unfold the llist predicate **)

val intro_llist_nil (#opened: _) (a:Type0)
  : SteelGhost unit opened emp (fun _ -> llist (null_llist #a))
          (requires fun _ -> True)
          (ensures fun _ _ h1 -> v_llist #a null_llist h1 == [])

inline_for_extraction
val is_nil (#a:Type0) (ptr:t a)
  : Steel bool (llist ptr) (fun _ -> llist ptr)
          (requires fun _ -> True)
          (ensures fun h0 res h1 ->
            (res == true <==> ptr == null_llist #a) /\
            v_llist ptr h0 == v_llist ptr h1 /\
            res == Nil? (v_llist ptr h1))

inline_for_extraction
val intro_llist_cons (#a:Type0) (ptr1 ptr2:t a)
  : Steel unit (vptr ptr1 `star` llist ptr2)
                  (fun _ -> llist ptr1)
                  (requires fun h -> next (sel ptr1 h) == ptr2)
                  (ensures fun h0 _ h1 -> v_llist ptr1 h1 == (data (sel ptr1 h0)) :: v_llist ptr2 h0)

inline_for_extraction
val tail (#a:Type0) (ptr:t a)
  : Steel (t a) (llist ptr)
                   (fun n -> vptr ptr `star` llist n)
                   (requires fun _ -> ptr =!= null_llist)
                   (ensures fun h0 n h1 ->
                     Cons? (v_llist ptr h0) /\
                     sel ptr h1 == mk_cell n (L.hd (v_llist ptr h0)) /\
                     v_llist n h1 == L.tl (v_llist ptr h0))
