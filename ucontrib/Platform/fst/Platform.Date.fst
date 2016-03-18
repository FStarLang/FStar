module Platform.Date

open FStar.Heap
open FStar.HyperHeap

assume new type dateTime : Type0
assume new type timeSpan : Type0

(* This library is used by miTLS; for now we model external calls as
   stateful but with no effect on the heap; we could be more
   precise. *)

effect EXT (a:Type) = ST a
  (requires (fun _ -> True)) 
  (ensures (fun h0 _ h1 -> modifies Set.empty h0 h1))

assume val now: unit -> EXT dateTime
assume val secondsFromDawn: unit -> EXT (n:nat{Bytes.repr_bytes n <= 4})
assume val newTimeSpan: int -> int -> int -> int -> Tot timeSpan
assume val addTimeSpan: dateTime -> timeSpan -> Tot dateTime
assume val greaterDateTime: dateTime -> dateTime -> Tot bool
