module SelectorsLList3Example

open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect
open Steel.ArrayRef

module L = FStar.List.Tot
module LL = Selectors.LList3
module U32 = FStar.UInt32

module MB = LowStar.Monotonic.Buffer // for is_null

inline_for_extraction noextract let a = U32.t
let cell = LL.cell a
/// The type of a list: A reference to a cell
let t = LL.t a

let next (c:cell) : t = LL.next c
let data (c:cell) : a = LL.data c
let mk_cell (n: t) (d:a)
  : Pure cell
    (requires True)
    (ensures fun c ->
      next c == n /\
      data c == d)
= LL.mk_cell n d

/// The null list pointer
let null_llist () : t = LL.null_llist

/// Lifting the null pointer check to empty lists
let is_null (ptr:t) : (b:bool{b <==> ptr == null_llist ()})
= LL.is_null ptr

let is_nil (ptr:t)
  : Steel bool (LL.llist ptr) (fun _ -> LL.llist ptr)
          (requires fun _ -> True)
          (ensures fun h0 res h1 ->
            (res == true <==> ptr == null_llist ()) /\
            LL.v_llist ptr h0 == LL.v_llist ptr h1 /\
            res == Nil? (LL.v_llist ptr h1))
= LL.is_nil ptr

let intro_llist_cons (ptr1 ptr2:t)
  : Steel unit (vptr ptr1 `star` LL.llist ptr2)
                  (fun _ -> LL.llist ptr1)
                  (requires fun h -> next (sel ptr1 h) == ptr2)
                  (ensures fun h0 _ h1 -> LL.v_llist ptr1 h1 == (data (sel ptr1 h0)) :: LL.v_llist ptr2 h0)
= LL.intro_llist_cons ptr1 ptr2

let tail (ptr:t)
  : Steel (t) (LL.llist ptr)
                   (fun n -> vptr ptr `star` LL.llist n)
                   (requires fun _ -> ptr =!= null_llist ())
                   (ensures fun h0 n h1 ->
                     Cons? (LL.v_llist ptr h0) /\
                     sel ptr h1 == mk_cell n (L.hd (LL.v_llist ptr h0)) /\
                     LL.v_llist n h1 == L.tl (LL.v_llist ptr h0))
= LL.tail ptr
