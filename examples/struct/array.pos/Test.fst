module Test


module DM = FStar.DependentMap
module S  = FStar.Struct
module HST = FStar.HyperStack.ST
module B = FStar.Buffer

type fields =
| I
| B

let fields_def (x: fields) : Tot Type = match x with
| I -> int
| B -> bool

let struct = DM.t _ fields_def

let obj = S.struct_ptr struct

let callee
   (pfrom pto: obj)
: HST.Stack int
  (requires (fun h -> S.live h pfrom /\ S.live h pto /\ S.disjoint pfrom pto))
  (ensures (fun h z h' ->
    S.live h pfrom /\ S.live h pto /\
    S.live h' pfrom /\ S.live h' pto /\
    S.modifies_1 (S.gfield pto I) h h' /\
    S.as_value h (S.gfield pfrom I) == z /\
    S.as_value h' (S.gfield pto I) == z + 1))
= S.write (S.field pto I) (S.read (S.field pfrom I) + 1);
  S.read (S.field pfrom I)

let caller
  ()
: HST.Stack int
  (requires (fun _ -> True))
  (ensures (fun _ z _ -> z == 18))
= HST.push_frame();
  let dm = DM.create #fields #fields_def (function | I -> 18 | B -> true) in
  let b = B.create dm (UInt32.uint_to_t 2) in
  let pfrom : obj = S.from_buffer_index b (UInt32.uint_to_t 0) in
  let pto : obj = S.from_buffer_index b (UInt32.uint_to_t 1) in
  let z = callee pfrom pto in
  HST.pop_frame ();
  z
