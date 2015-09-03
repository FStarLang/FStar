(*--build-config
    options:--z3timeout 10 --prims ../../lib/prims.fst --verify_module Bloom --admit_fsi FStar.Seq --max_fuel 4 --initial_fuel 0 --max_ifuel 2 --initial_ifuel 1;
    variables:LIB=../../lib
              CONTRIB=../../contrib;
    other-files:
            $LIB/ext.fst $LIB/classical.fst
            $LIB/set.fsi $LIB/set.fst
            $LIB/heap.fst $LIB/st.fst $LIB/all.fst
            $LIB/string.fst $LIB/list.fst
	    $LIB/bytes.fst
            $LIB/seq.fsi $LIB/seqproperties.fst
            $LIB/io.fsti
            $CONTRIB/Platform/fst/Bytes.fst
            $CONTRIB/CoreCrypto/fst/CoreCrypto.fst
	    bloom-format.fst
  --*)

module Bloom

open FStar.All
open FStar.String
open FStar.IO
open FStar.Heap
open FStar.Seq
open FStar.SeqProperties

open Format

logic type Pos (i: int) = (i > 0)
type ln_t = ln:uint16{Pos ln}
type hash = h:seq byte{Seq.length h >= 2}
type text = seq byte
type hash_fn = text -> hash
type bloom (ln:ln_t) = bl:seq bool{Seq.length bl = ln}

(* TODO: put this as an anonymous function in le *)
val le_loop: ln:ln_t -> i:uint16 -> bl1: bloom ln -> bl2: bloom ln -> Tot bool
let rec le_loop ln i bl1 bl2 =
  if i >= 0 then
  begin
    let b1 = Seq.index bl1 i in
    let b2 = Seq.index bl2 i in
    if ((not b1) || b2) then le_loop ln (i-1) bl1 bl2
    else false
  end
  else true

val le: ln:ln_t -> bl1:bloom ln -> bl2:bloom ln -> Tot bool
let le ln bl1 bl2 = le_loop ln ln bl1 bl2

val set: ln:ln_t -> bl:bloom ln -> i:uint16 -> Tot (bl':bloom ln)
let set ln bl i =
  let i' = op_Modulus i ln in
  Seq.upd bl i' true

val is_set: ln:ln_t -> bl:bloom ln -> i:uint16 -> Tot (b:bool)
let is_set ln bl i =
  let i' = op_Modulus i ln in
  Seq.index bl i'

val check: ln:ln_t -> h:hash_fn -> n:uint16 -> x:text -> bl:bloom ln -> Tot (b:bool)
let rec check ln h n x bl =
  if n > 0 then
  begin
    let pt = Seq.append (uint16_to_bytes n) x in
    let hs = h pt in
    let b = is_set ln bl (bytes_to_uint16 (append (index hs 0) (index hs 1))) in
    if b then check ln h (n-1) x bl
    else false
  end
  else true

val add: ln:ln_t -> h:hash_fn -> n:uint16 -> x:text -> bl:bloom ln -> Tot (bl':bloom ln{le bl bl' && check ln h n x bl'})
let rec add ln h n x bl =
  if n > 0 then
    let pt = Seq.append (uint16_to_bytes n) x in
    let (hs, _) = split_eq (h pt) 2 in
    let bl' = set ln bl (bytes_to_uint16 hs) in
    add ln h (n-1) x bl'
  else bl
