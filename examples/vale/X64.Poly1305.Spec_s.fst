module X64.Poly1305.Spec_s

open FStar.Mul
open FStar.UInt
open FStar.Map

(* syntax for map accesses, m.[key] and m.[key] <- value *)
type map (key:eqtype) (value:Type) = Map.t key value
let op_String_Access     = sel
let op_String_Assignment = upd

let nat128_max = 0x100000000000000000000000000000000
let _ = assert_norm (pow2 128 = nat128_max) 
type nat128 = x:int{0 <= x && x < nat128_max}

let modp'(x:int):int =
  x % (nat128_max * 4 - 5)

let and128 (x:nat128) (y:nat128) :nat128 =
  logand #128 x y

let rec poly1305_hash_blocks (h:int) (pad:int) (r:int) (inp:int->nat128) (i:int) (k:int{k >= i && (k-i)%16 = 0}) : Tot int (decreases (k - i)) =
  if i = k then h
  else
    let kk = k - 16 in
    let hh = poly1305_hash_blocks h pad r inp i kk in
    modp' ((hh + pad + inp kk) * r)

let poly1305_hash (key_r:nat128) (key_s:nat128) (inp:int->nat128) (start:int) (len:nat) :int =
  let r = logand #128 key_r 0x0ffffffc0ffffffc0ffffffc0fffffff in
  let nBlocks = len / 16 in
  let nExtra = len % 16 in
  let padBlocks = nat128_max in
  let hBlocks = poly1305_hash_blocks 0 padBlocks r inp start (start + 16 * nBlocks) in
  if nExtra = 0 then
    (hBlocks + key_s) % nat128_max
  else
    let k = start + 16 * nBlocks in
    let padLast = pow2(nExtra * 8) in
    let hLast = modp' ((hBlocks + padLast + ((inp k) % padLast)) * r) in
    (hLast + key_s) % nat128_max
