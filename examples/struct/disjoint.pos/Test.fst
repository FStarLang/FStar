module Test


module DM = FStar.DependentMap
module S  = FStar.Struct
module HST = FStar.HyperStack.ST

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

type more_fields =
| Less
| ThisMore

let more_fields_def (x: more_fields) : Tot Type = match x with
| Less -> struct
| ThisMore -> unit

type more_struct = DM.t _ more_fields_def

let more_obj = S.struct_ptr more_struct

let caller
  ()
: HST.Stack int
  (requires (fun _ -> True))
  (ensures (fun _ z _ -> z == 18))
= HST.push_frame();
  let ofrom : obj = S.screate (DM.create #fields #fields_def (function | I -> 18 | B -> true)) in
  let moto : more_obj = S.screate (DM.create #more_fields #more_fields_def (function | Less -> DM.create #fields #fields_def (function  | I -> 1729 | B -> false ) | ThisMore -> ())) in
  let pfrom : obj = ofrom in
  let pto : obj = S.field moto Less in
  let z = callee pfrom pto in
  HST.pop_frame ();
  z
