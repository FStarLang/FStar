module Test

module DM = FStar.DependentMap
module S  = FStar.Seq
module B = FStar.BufferNG
module HST = FStar.HyperStack.ST

type point_fd =
| X
| Y

let point_struct_ty = function
| X -> UInt16.t
| Y -> UInt16.t

(* FIXME: Leaving point_struct_ty as an anonymous function makes us unable to prove
   anything about point_struct
*)
let point_struct = DM.t point_fd point_struct_ty

type cpoint_fd =
| Point
| Gray

let cpoint_struct_ty = function
| Point -> point_struct
| Gray -> UInt16.t

let cpoint_struct = DM.t cpoint_fd cpoint_struct_ty

let mk_point (x : UInt16.t) (y : UInt16.t) : point_struct =
  DM.create #_ #point_struct_ty (function X -> x | Y -> y)
  (* DM.create (function X -> x | Y -> y) *)

let mk_cpoint (p : point_struct) (g : UInt16.t) : cpoint_struct =
  DM.create #_ #cpoint_struct_ty (function Point -> p | Gray -> g)

let point = Pointer.pointer point_struct
let cpoint = Pointer.pointer cpoint_struct

let parse_uint16_le_spec (s : S.seq UInt8.t { S.length s = 2 }) : Tot UInt16.t
=
  let x_lo = S.index s 0 in
  let x_hi = S.index s 1 in
  let x_lo_16 = FStar.Int.Cast.uint8_to_uint16 x_lo in
  let x_hi_16 = FStar.Int.Cast.uint8_to_uint16 x_hi in
  FStar.UInt16.(x_lo_16 |^ (x_hi_16 <<^ 8ul))

let parse_uint16_le
  (b : B.buffer UInt8.t { B.length b = 2ul }) : HST.Stack UInt16.t
  (requires (fun h -> B.live h b))
  (ensures (fun h x h' ->
    h == h' /\
    parse_uint16_le_spec (B.as_seq h' b) = x
  ))
=
  let x_lo = B.read b 0ul in
  let x_hi = B.read b 1ul in
  let x_lo_16 = FStar.Int.Cast.uint8_to_uint16 x_lo in
  let x_hi_16 = FStar.Int.Cast.uint8_to_uint16 x_hi in
  FStar.UInt16.(x_lo_16 |^ (x_hi_16 <<^ 8ul))

let parse_point_spec
  (s : S.seq UInt8.t { S.length s = 4 }) : Tot point_struct =
  let x = parse_uint16_le_spec (Seq.slice s 0 2) in
  let y = parse_uint16_le_spec (Seq.slice s 2 4) in
  mk_point x y

let parse_point
  (b : B.buffer UInt8.t { B.length b = 4ul })
  (p : point) : HST.Stack unit
  (requires (fun h ->
    B.live h b /\ Pointer.live h p /\
    B.disjoint_buffer_vs_pointer b p
  ))
  (ensures (fun h0 _ h1 ->
    Pointer.live h1 p /\
    Pointer.modifies_1 p h0 h1 /\
    (Pointer.gread h1 p) == (parse_point_spec (B.as_seq h0 b))
  ))
  =
  let h0 = HST.get () in
  let x = parse_uint16_le (B.sub b 0ul 2ul) in
  let y = parse_uint16_le (B.sub b 2ul 2ul) in
  Pointer.write (Pointer.field p X) x;
  Pointer.write (Pointer.field p Y) y;
  let h1 = HST.get () in
  assert (DM.equal (Pointer.gread h1 p) (parse_point_spec (B.as_seq h0 b)))


let parse_spec (s : S.seq UInt8.t { S.length s = 6 }) : Tot cpoint_struct =
  let p = parse_point_spec (Seq.slice s 0 4) in
  let gray = parse_uint16_le_spec (Seq.slice s 4 6) in
  mk_cpoint p gray

#set-options "--z3rlimit 16"

let parse_impl (b : B.buffer UInt8.t { B.length b = 6ul }) (p : cpoint) : HST.Stack unit
  (requires (fun h ->
    B.live h b /\ Pointer.live h p /\
    B.disjoint_buffer_vs_pointer b p
  ))
  (ensures (fun h0 _ h1 ->
    Pointer.live h1 p /\
    Pointer.modifies_1 p h0 h1 /\
    (Pointer.gread h1 p) == (parse_spec (B.as_seq h0 b))
  ))
=
  let h0 = HST.get () in
  let gray = parse_uint16_le (B.sub b 4ul 2ul) in
  let _ = parse_point (B.sub b 0ul 4ul) (Pointer.field p Point) in
  let _ = Pointer.write (Pointer.field p Gray) gray in
  let h2 = HST.get () in
  assert (DM.equal (Pointer.gread h2 p) (parse_spec (B.as_seq h0 b)))
