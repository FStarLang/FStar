module Test

module S  = FStar.Seq
module B = FStar.BufferNG
module HST = FStar.HyperStack.ST
module VA = ValueArray

let parse
  (data_len : UInt32.t)
  (data : B.buffer UInt8.t{ B.length data = data_len })
  (indices_len : UInt32.t)
  (indices : B.buffer UInt32.t{ B.length indices = indices_len }) :
  HST.Stack (option (VA.t UInt32.t indices_len))
  (requires (fun h ->
    B.live h data /\ B.live h indices /\
    B.disjoint_buffer_vs_buffer data indices
  ))
  (ensures (fun h0 _ h1 ->
    B.live h1 data /\ B.live h1 indices
    (* /\ modifies 1 *)
    (* /\ spec *)
  ))
=
  (* Returns [Some i] where [i] is the number of indices written, or [None] in
     case of error (incorrect packet sizes in [data] that would lead to an
     overflow, or too many packets for the given number of indices).
  *)
  let rec loop
    (data_i : UInt32.t{ UInt32.v data_i < UInt32.v (B.length data) })
    (idx : UInt32.t{ UInt32.v idx < UInt32.v (B.length indices) }) :
    HST.Stack (option UInt32.t)
    (requires (fun h -> B.live h data /\ B.live h indices /\ B.disjoint_buffer_vs_buffer data indices))
    (ensures (fun h0 _ h1 -> B.live h1 data /\ B.live h1 indices /\ B.disjoint_buffer_vs_buffer data indices
                          (* /\ modifies_1 /\ ...*)))
  =
    let _ = B.write indices idx data_i in
    let packet_len : UInt8.t = B.read data data_i in
    let packet_len_i32 = FStar.Int.Cast.uint8_to_uint32 packet_len in
    let remaining = FStar.UInt32.(data_len -^ data_i -^ 1ul) in
    if FStar.UInt32.(remaining <^ packet_len_i32) then None
    else if FStar.UInt32.(remaining = packet_len_i32) then Some idx
    else if FStar.UInt32.(idx +^ 1ul <^ indices_len) then
      loop FStar.UInt32.(data_i +^ packet_len_i32 +^ 1ul) FStar.UInt32.(idx +^ 1ul)
    else None
  in
  if data_len = 0ul || indices_len = 0ul then None
  else
    match loop 0ul 0ul with
    | None -> None
    | Some _ -> Some (VA.of_buffer indices_len indices)
