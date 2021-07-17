module MachineIntegerConstants

(*
  Check that all machine integer constants from modules [U]Int(8-64)
  extract to Stdint in OCaml.
  The only exception is UInt8, that should extract to OCaml's native
  int type.
*)

// Signed

let e_int8 x = match x with
  | 22y -> FStar.Int8.(42y +^ x)
  | _ -> 0y

let e_int16 x = match x with
  | 22s -> FStar.Int16.(42s +^ x)
  | _ -> 0s

let e_int32 x = match x with
  | 22l -> FStar.Int32.(42l +^ x)
  | _ -> 0l

let e_int64 x = match x with
  | 22L -> FStar.Int64.(42L +^ x)
  | _ -> 0L

// Unsigned

let e_uint8 x = match x with
  | 22uy -> FStar.UInt8.(42uy +^ x)
  | _ -> 0uy

let e_uint16 x = match x with
  | 22us -> FStar.UInt16.(42us +^ x)
  | _ -> 0us

let e_uint32 x = match x with
  | 22ul -> FStar.UInt32.(42ul +^ x)
  | _ -> 0ul

let e_uint64 x = match x with
  | 22UL -> FStar.UInt64.(42UL +^ x)
  | _ -> 0UL
