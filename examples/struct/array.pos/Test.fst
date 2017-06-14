module Test


module DM = FStar.DependentMap
module S  = FStar.Pointer
module B  = FStar.BufferNG
module HST = FStar.ST

type fields =
| I
| B

let fields_def (x: fields) : Tot Type = match x with
| I -> int
| B -> bool

let struct = DM.t _ fields_def

let obj = S.pointer struct

let callee
   (pfrom pto: obj)
: HST.Stack int
  (requires (fun h -> S.live h pfrom /\ S.live h pto /\ S.disjoint pfrom pto))
  (ensures (fun h z h' ->
    S.live h pfrom /\ S.live h pto /\
    S.live h' pfrom /\ S.live h' pto /\
    S.modifies_1 (S.gfield pto I) h h' /\
    S.gread h (S.gfield pfrom I) == z /\
    S.gread h' (S.gfield pto I) == z + 1))
= S.write (S.field pto I) (S.read (S.field pfrom I) + 1);
  S.read (S.field pfrom I)

let caller
  ()
: HST.Stack int
  (requires (fun _ -> True))
  (ensures (fun _ z _ -> z == 18))
= HST.push_frame();
  let dm = DM.create #fields #fields_def (function | I -> 18 | B -> true) in
  let b = B.buffer_of_array_pointer (S.screate #(S.array 2ul struct) (Seq.create 2 dm)) in
  let pfrom : obj = B.pointer_of_buffer_cell b (UInt32.uint_to_t 0) in
  let pto : obj = B.pointer_of_buffer_cell b (UInt32.uint_to_t 1) in
  let z = callee pfrom pto in
  HST.pop_frame ();
  z
