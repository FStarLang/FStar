module Parsing3

open FStar.Mul
open FStar.Ghost
open FStar.HyperStack
open FStar.HST
open FStar.UInt32
open FStar.Int.Cast
open FStar.Buffer
open Low.Bytes

#set-options "--lax"

val read_length: b:bytes -> n:UInt32.t{v n = 1 \/ v n = 2 \/ v n = 3} -> STL UInt32.t
  (requires (fun h -> Buffer.live h b /\ v n <= Buffer.length b))
  (ensures  (fun h0 z h1 -> h1 == h0 ))
let read_length b n =
  if n = 1ul then (
    let b0 = index b 0ul in
    uint8_to_uint32 b0
  ) else if n = 2ul then (
    let b1 = index b 0ul in
    let b0 = index b 1ul in
    let b0 = uint8_to_uint32 b0 in
    let b1 = uint8_to_uint32 b1 in
    b0 |^ (b1 <<^ 8ul)
  ) else (
    let b2 = index b 0ul in
    let b1 = index b 1ul in
    let b0 = index b 2ul in
    let b0 = uint8_to_uint32 b0 in
    let b1 = uint8_to_uint32 b1 in
    let b2 = uint8_to_uint32 b2 in
    b0 |^ (b1 <<^ 8ul) |^ (b2 <<^ 16ul)
  )

(* Shallow ch_extension validation *)
val validate_ch_extensions: b:bytes -> ext_len:UInt32.t -> Stl bool
let rec validate_ch_extensions b ext_len =
  if UInt32.eq ext_len 0ul then true
  else if UInt32.lt ext_len 4ul (* Extension type (2 bytes) + var length (2 bytes) *)
  then false
  else begin
    let len_bytes = sub_8 b 2ul 2ul in
    let l = read_length len_bytes 2ul in
    if UInt32.lt ext_len l then false
    else validate_ch_extensions (offset_8 b (4ul +^ l)) (ext_len -^ (4ul +^ l))
 end     

val validate_key_share: b:bytes -> ks_len:UInt32.t -> Stl bool
let rec validate_key_share b ks_len =
  if UInt32.eq ks_len 0ul then true
  else if UInt32.lt ks_len 4ul (* ks_group_name (2 bytes) + var length public key (2 bytes) *)
    then false
  else begin
    let len_bytes = sub_8 b 2ul 2ul in
    let l = 4ul +^ (read_length len_bytes 2ul) in
    if UInt32.lt ks_len l then false
    else validate_key_share (offset_8 b l) (ks_len -^ l)
  end

val validate_buf_var: b:bytes -> var_len:UInt32.t -> bv_len:UInt32.t -> Stl bool
let rec validate_buf_var b var_len bv_len =
  if UInt32.eq bv_len 0ul then true
  else if UInt32.lt bv_len var_len then false
  else begin
    let len_bytes = sub_8 b 0ul var_len in
    let l = var_len +^ (read_length len_bytes var_len) in
    if UInt32.lt bv_len l then false
    else validate_buf_var (offset_8 b l) var_len (bv_len -^ l)
  end

val validate_ch_extensions_deep: b:bytes -> ext_len:UInt32.t -> Stl bool
let rec validate_ch_extensions_deep b ext_len =
  if UInt32.eq ext_len 0ul then true
  else if UInt32.lt ext_len 4ul (* Extension type (2 bytes) + var length (2 bytes) *)
  then false
  else begin
    let len_bytes = sub_8 b 2ul 2ul in
    let ext_ty_bytes = bytes_to_u16s (sub_8 b 0ul 2ul) in (* Cast to short* *)
    let data_bytes = offset_8 b 4ul in
    let l = read_length len_bytes 2ul in
    if UInt32.lt ext_len l then false
    else begin
      (* Dummy values for extension types *)
      let ext_ty = read_16 ext_ty_bytes 0ul in
      if UInt16.eq ext_ty 0us then
	(* CE_extended_ms*) validate_ch_extensions_deep (offset_8 b 4ul) (ext_len -^ 4ul)
      else if UInt16.eq ext_ty 1us then begin
	(* CE_secure_renegotiation *)
	let l = 4ul +^ (read_length data_bytes 1ul) in
	if UInt32.lt ext_len l then false
	else validate_ch_extensions_deep b (ext_len -^ l) end
      else if UInt16.eq ext_ty 2us then begin
        (* CE_supported_groups *)
	let l = 4ul +^ (read_length data_bytes 2ul) in
	if UInt32.lt ext_len l then false
	else validate_ch_extensions_deep b (ext_len -^ l) end
      else if UInt16.eq ext_ty 3us then begin
	(* CE_supported_point_formats *)
	let l = 4ul +^ (read_length data_bytes 1ul) in
	if UInt32.lt ext_len l then false
	else validate_ch_extensions_deep b (ext_len -^ l) end
      else if UInt16.eq ext_ty 4us then begin
        (* CE_signature_algorithms *)
	let l = 4ul +^ (read_length data_bytes 2ul) in
	if UInt32.lt ext_len l then false
	else validate_ch_extensions_deep b (ext_len -^ l) end
      else if UInt16.eq ext_ty 5us then
	(* CE_earlyData *) validate_ch_extensions_deep (offset_8 b 4ul) (ext_len -^ 4ul)
      else if UInt16.eq ext_ty 6us then begin
	(* CE_keyShare *)
	if UInt32.lt ext_len 6ul then false
	else begin
	  let ks_len = read_length data_bytes 2ul in
	  if UInt32.lt ext_len (4ul +^ ks_len) then false
	  else if validate_key_share (offset_8 data_bytes 2ul) ks_len then 
	    validate_ch_extensions_deep (offset_8 b (6ul +^ ks_len)) (ext_len -^ 6ul -^ ks_len)
	  else false
	end
      end
      else if UInt16.eq ext_ty 7us || UInt16.eq ext_ty 8us then begin
	(* CE_preSharedKey or CE_server_names, same format *)
	if UInt32.lt ext_len 6ul then false
	else begin
	  let bv_len = read_length data_bytes 2ul in
	  if UInt32.lt ext_len (4ul +^ bv_len) then false
	  else if validate_buf_var (offset_8 data_bytes 2ul) 2ul bv_len then 
	    validate_ch_extensions_deep (offset_8 b (6ul +^ bv_len)) (ext_len -^ 6ul -^ bv_len)
	  else false	 
	end
      end
      else false
    end
  end

val validate_ch: b:bytes -> len_ch:UInt32.t -> Stl bool
let validate_ch b len_ch =
  if UInt32.lt len_ch 34ul then false
  else begin
    (* Jumping over pv and client random that have fixed size *)
    let sid_bytes = offset_8 b 34ul in
    let l = 2ul +^ 32ul +^ 1ul +^ (read_length sid_bytes 1ul) in
    if UInt32.lt len_ch l then false
    else begin
      let cs_bytes = offset_8 b l in
      let l = l +^ 2ul +^ (read_length cs_bytes 2ul) in
      if UInt32.lt len_ch l then false
      else begin
	let comp_bytes = offset_8 b l in
	let l = l +^ 1ul +^ (read_length comp_bytes 1ul) in
	if UInt32.lt len_ch l then false
	else begin
	  let ext_bytes = offset_8 b l in
	  let ext_len = (read_length ext_bytes 1ul) in
	  let l = l +^ 3ul +^ ext_len in
	  if not(UInt32.eq len_ch l) then false
	  else 
	    validate_ch_extensions (offset_8 ext_bytes 3ul) ext_len
        end
      end
    end
  end
