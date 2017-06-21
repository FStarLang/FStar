module Crypto.Symmetric.AES

// FIPS197 ?
// TODO factor it out in terms of https://en.wikipedia.org/wiki/AES_instruction_set
// see also https://software.intel.com/sites/default/files/article/165683/aes-wp-2012-09-22-v01.pdf

// TODO this is AES256; 
// we also need AES128 (nk=4ul, nr=10) and maybe AES192 (nk=6ul,nr=12).

open FStar.Mul
open FStar.Ghost
open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.UInt8
open FStar.Int.Cast
open FStar.Buffer

(* Module abbreviations *)
module HH = FStar.HyperHeap
module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST

module U8  = FStar.UInt8
module U32 = FStar.UInt32
module H8  = FStar.UInt8
module H32  = FStar.UInt32


type bytes = FStar.Buffer.buffer byte
type lbytes l = b:bytes {length b = l} 
let v (x:UInt32.t) : nat  = UInt32.v x

(* Parameters for AES-256 *)
inline_for_extraction let nb =  4ul 
inline_for_extraction let nk =  8ul // 4, 6, or 8
inline_for_extraction let nr = 14ul // 10, 12, or 14

let blocklen = U32.(4ul *^ nb)
let keylen   = U32.(4ul *^ nk)
let xkeylen  = U32.(4ul *^ nb *^ (nr +^ 1ul)) // 176, 208, or 240

type block = lbytes (v blocklen)
type skey  = lbytes (v keylen)
type xkey  = lbytes (v xkeylen)

type rnd = r:UInt32.t{v r <= v nr}
type idx_16 = ctr:UInt32.t{v ctr <= 16}

val xtime: b:byte -> Tot byte
let xtime b =
  (b <<^ 1ul) ^^ (((b >>^ 7ul) &^ 1uy) *%^ 0x1buy)

val multiply: a:byte -> b:byte -> Tot byte
let multiply a b =
  ((a *%^ (b &^ 1uy))
  ^^ (xtime a *%^ ((b >>^ 1ul) &^ 1uy))
  ^^ (xtime (xtime a) *%^ ((b >>^ 2ul) &^ 1uy))
  ^^ (xtime (xtime (xtime a)) *%^ ((b >>^ 3ul) &^ 1uy))
  ^^ (xtime (xtime (xtime (xtime a))) *%^ ((b >>^ 4ul) &^ 1uy))
  ^^ (xtime (xtime (xtime (xtime (xtime a)))) *%^ ((b >>^ 5ul) &^ 1uy))
  ^^ (xtime (xtime (xtime (xtime (xtime (xtime a))))) *%^ ((b >>^ 6ul) &^ 1uy))
  ^^ (xtime (xtime (xtime (xtime (xtime (xtime (xtime a)))))) *%^ ((b >>^ 7ul) &^ 1uy)))

#set-options "--lax"
// tables for S-box and inv-S-box, derived from GF256 specification.

type sbox  = lbytes 256

(* val mk_sbox: unit -> StackInline sbox *)
(*   (requires (fun _ -> True)) *)
(*   (ensures  (fun h0 s h1 -> live h1 s /\ modifies_0 h0 h1 /\ ~(contains h0 s))) *)
(* let mk_sbox () = *)
(*   createL [ *)
(*     0x52uy, 0x09uy, 0x6auy, 0xd5uy, *)
(*     0x30uy, 0x36uy, 0xa5uy, 0x38uy,  *)
(*     0xbfuy, 0x40uy, 0xa3uy, 0x9euy, *)
(*     0x81uy, 0xf3uy, 0xd7uy, 0xfbuy,  *)
(*     0x7cuy, 0xe3uy, 0x39uy, 0x82uy,  *)
(*     0x9buy, 0x2fuy, 0xffuy, 0x87uy,  *)
(*     0x34uy, 0x8euy, 0x43uy, 0x44uy,  *)
(*     0xc4uy, 0xdeuy, 0xe9uy, 0xcbuy,  *)
(*     0x54uy, 0x7buy, 0x94uy, 0x32uy,  *)
(*     0xa6uy, 0xc2uy, 0x23uy, 0x3duy,  *)
(*     0xeeuy, 0x4cuy, 0x95uy, 0x0buy,  *)
(*     0x42uy, 0xfauy, 0xc3uy, 0x4euy,  *)
(*     0x08uy, 0x2euy, 0xa1uy, 0x66uy,  *)
(*     0x28uy, 0xd9uy, 0x24uy, 0xb2uy,  *)
(*     0x76uy, 0x5buy, 0xa2uy, 0x49uy,  *)
(*     0x6duy, 0x8buy, 0xd1uy, 0x25uy,  *)
(*     0x72uy, 0xf8uy, 0xf6uy, 0x64uy,  *)
(*     0x86uy, 0x68uy, 0x98uy, 0x16uy,  *)
(*     0xd4uy, 0xa4uy, 0x5cuy, 0xccuy,  *)
(*     0x5duy, 0x65uy, 0xb6uy, 0x92uy,  *)
(*     0x6cuy, 0x70uy, 0x48uy, 0x50uy,  *)
(*     0xfduy, 0xeduy, 0xb9uy, 0xdauy,  *)
(*     0x5euy, 0x15uy, 0x46uy, 0x57uy,  *)
(*     0xa7uy, 0x8duy, 0x9duy, 0x84uy,  *)
(*     0x90uy, 0xd8uy, 0xabuy, 0x00uy,  *)
(*     0x8cuy, 0xbcuy, 0xd3uy, 0x0auy,  *)
(*     0xf7uy, 0xe4uy, 0x58uy, 0x05uy,  *)
(*     0xb8uy, 0xb3uy, 0x45uy, 0x06uy,  *)
(*     0xd0uy, 0x2cuy, 0x1euy, 0x8fuy,  *)
(*     0xcauy, 0x3fuy, 0x0fuy, 0x02uy,  *)
(*     0xc1uy, 0xafuy, 0xbduy, 0x03uy,  *)
(*     0x01uy, 0x13uy, 0x8auy, 0x6buy,  *)
(*     0x3auy, 0x91uy, 0x11uy, 0x41uy,  *)
(*     0x4fuy, 0x67uy, 0xdcuy, 0xeauy,  *)
(*     0x97uy, 0xf2uy, 0xcfuy, 0xceuy,  *)
(*     0xf0uy, 0xb4uy, 0xe6uy, 0x73uy,  *)
(*     0x96uy, 0xacuy, 0x74uy, 0x22uy,  *)
(*     0xe7uy, 0xaduy, 0x35uy, 0x85uy,  *)
(*     0xe2uy, 0xf9uy, 0x37uy, 0xe8uy,  *)
(*     0x1cuy, 0x75uy, 0xdfuy, 0x6euy,  *)
(*     0x47uy, 0xf1uy, 0x1auy, 0x71uy,  *)
(*     0x1duy, 0x29uy, 0xc5uy, 0x89uy,  *)
(*     0x6fuy, 0xb7uy, 0x62uy, 0x0euy,  *)
(*     0xaauy, 0x18uy, 0xbeuy, 0x1buy,  *)
(*     0xfcuy, 0x56uy, 0x3euy, 0x4buy,  *)
(*     0xc6uy, 0xd2uy, 0x79uy, 0x20uy,  *)
(*     0x9auy, 0xdbuy, 0xc0uy, 0xfeuy,  *)
(*     0x78uy, 0xcduy, 0x5auy, 0xf4uy,  *)
(*     0x1fuy, 0xdduy, 0xa8uy, 0x33uy,  *)
(*     0x88uy, 0x07uy, 0xc7uy, 0x31uy,  *)
(*     0xb1uy, 0x12uy, 0x10uy, 0x59uy,  *)
(*     0x27uy, 0x80uy, 0xecuy, 0x5fuy,  *)
(*     0x60uy, 0x51uy, 0x7fuy, 0xa9uy,  *)
(*     0x19uy, 0xb5uy, 0x4auy, 0x0duy,  *)
(*     0x2duy, 0xe5uy, 0x7auy, 0x9fuy,  *)
(*     0x93uy, 0xc9uy, 0x9cuy, 0xefuy,  *)
(*     0xa0uy, 0xe0uy, 0x3buy, 0x4duy,  *)
(*     0xaeuy, 0x2auy, 0xf5uy, 0xb0uy, *)
(*     0xc8uy, 0xebuy, 0xbbuy, 0x3cuy, *)
(*     0x83uy, 0x53uy, 0x99uy, 0x61uy, *)
(*     0x17uy, 0x2buy, 0x04uy, 0x7euy, *)
(*     0xbauy, 0x77uy, 0xd6uy, 0x26uy, *)
(*     0xe1uy, 0x69uy, 0x14uy, 0x63uy, *)
(*     0x55uy, 0x21uy, 0x0cuy, 0x7duy *)
(*   ] *)


(* val mk_inv_sbox: unit -> StackInline sbox *)
(*   (requires (fun _ -> True)) *)
(*   (ensures  (fun h0 s h1 -> live h1 s /\ modifies_0 h0 h1 /\ ~(contains h0 s))) *)
(* let mk_inv_sbox () = *)
(*   0x52uy; 0x09uy; 0x6auy; 0xd5uy; *)
(*   0x30uy; 0x36uy; 0xa5uy; 0x38uy; *)
(*   0xbfuy; 0x40uy; 0xa3uy; 0x9euy; *)
(*   0x81uy; 0xf3uy; 0xd7uy; 0xfbuy; *)
(*   0x7cuy; 0xe3uy; 0x39uy; 0x82uy; *)
(*   0x9buy; 0x2fuy; 0xffuy; 0x87uy; *)
(*   0x34uy; 0x8euy; 0x43uy; 0x44uy; *)
(*   0xc4uy; 0xdeuy; 0xe9uy; 0xcbuy; *)
(*   0x54uy; 0x7buy; 0x94uy; 0x32uy; *)
(*   0xa6uy; 0xc2uy; 0x23uy; 0x3duy; *)
(*   0xeeuy; 0x4cuy; 0x95uy; 0x0buy; *)
(*   0x42uy; 0xfauy; 0xc3uy; 0x4euy; *)
(*   0x08uy; 0x2euy; 0xa1uy; 0x66uy; *)
(*   0x28uy; 0xd9uy; 0x24uy; 0xb2uy; *)
(*   0x76uy; 0x5buy; 0xa2uy; 0x49uy; *)
(*   0x6duy; 0x8buy; 0xd1uy; 0x25uy; *)
(*   0x72uy; 0xf8uy; 0xf6uy; 0x64uy; *)
(*   0x86uy; 0x68uy; 0x98uy; 0x16uy; *)
(*   0xd4uy; 0xa4uy; 0x5cuy; 0xccuy; *)
(*   0x5duy; 0x65uy; 0xb6uy; 0x92uy; *)
(*   0x6cuy; 0x70uy; 0x48uy; 0x50uy; *)
(*   0xfduy; 0xeduy; 0xb9uy; 0xdauy; *)
(*   0x5euy; 0x15uy; 0x46uy; 0x57uy; *)
(*   0xa7uy; 0x8duy; 0x9duy; 0x84uy; *)
(*   0x90uy; 0xd8uy; 0xabuy; 0x00uy; *)
(*   0x8cuy; 0xbcuy; 0xd3uy; 0x0auy; *)
(*   0xf7uy; 0xe4uy; 0x58uy; 0x05uy; *)
(*   0xb8uy; 0xb3uy; 0x45uy; 0x06uy; *)
(*   0xd0uy; 0x2cuy; 0x1euy; 0x8fuy; *)
(*   0xcauy; 0x3fuy; 0x0fuy; 0x02uy; *)
(*   0xc1uy; 0xafuy; 0xbduy; 0x03uy; *)
(*   0x01uy; 0x13uy; 0x8auy; 0x6buy; *)
(*   0x3auy; 0x91uy; 0x11uy; 0x41uy; *)
(*   0x4fuy; 0x67uy; 0xdcuy; 0xeauy; *)
(*   0x97uy; 0xf2uy; 0xcfuy; 0xceuy; *)
(*   0xf0uy; 0xb4uy; 0xe6uy; 0x73uy; *)
(*   0x96uy; 0xacuy; 0x74uy; 0x22uy; *)
(*   0xe7uy; 0xaduy; 0x35uy; 0x85uy; *)
(*   0xe2uy; 0xf9uy; 0x37uy; 0xe8uy; *)
(*   0x1cuy; 0x75uy; 0xdfuy; 0x6euy; *)
(*   0x47uy; 0xf1uy; 0x1auy; 0x71uy; *)
(*   0x1duy; 0x29uy; 0xc5uy; 0x89uy; *)
(*   0x6fuy; 0xb7uy; 0x62uy; 0x0euy; *)
(*   0xaauy; 0x18uy; 0xbeuy; 0x1buy; *)
(*   0xfcuy; 0x56uy; 0x3euy; 0x4buy; *)
(*   0xc6uy; 0xd2uy; 0x79uy; 0x20uy; *)
(*   0x9auy; 0xdbuy; 0xc0uy; 0xfeuy; *)
(*   0x78uy; 0xcduy; 0x5auy; 0xf4uy; *)
(*   0x1fuy; 0xdduy; 0xa8uy; 0x33uy; *)
(*   0x88uy; 0x07uy; 0xc7uy; 0x31uy; *)
(*   0xb1uy; 0x12uy; 0x10uy; 0x59uy; *)
(*   0x27uy; 0x80uy; 0xecuy; 0x5fuy; *)
(*   0x60uy; 0x51uy; 0x7fuy; 0xa9uy; *)
(*   0x19uy; 0xb5uy; 0x4auy; 0x0duy; *)
(*   0x2duy; 0xe5uy; 0x7auy; 0x9fuy; *)
(*   0x93uy; 0xc9uy; 0x9cuy; 0xefuy; *)
(*   0xa0uy; 0xe0uy; 0x3buy; 0x4duy; *)
(*   0xaeuy; 0x2auy; 0xf5uy; 0xb0uy; *)
(*   0xc8uy; 0xebuy; 0xbbuy; 0x3cuy; *)
(*   0x83uy; 0x53uy; 0x99uy; 0x61uy; *)
(*   0x17uy; 0x2buy; 0x04uy; 0x7euy; *)
(*   0xbauy; 0x77uy; 0xd6uy; 0x26uy; *)
(*   0xe1uy; 0x69uy; 0x14uy; 0x63uy; *)
(*   0x55uy; 0x21uy; 0x0cuy; 0x7duy *)


val mk_sbox: sb:sbox -> Stack unit
  (requires (fun h -> live h sb))
  (ensures  (fun h0 _ h1 -> live h1 sb /\ modifies_1 sb h0 h1))
let mk_sbox sbox =
  sbox.(0ul) <-   0x63uy; sbox.(1ul) <-   0x7cuy; sbox.(2ul) <-   0x77uy; sbox.(3ul) <-   0x7buy;
  sbox.(4ul) <-   0xf2uy; sbox.(5ul) <-   0x6buy; sbox.(6ul) <-   0x6fuy; sbox.(7ul) <-   0xc5uy;
  sbox.(8ul) <-   0x30uy; sbox.(9ul) <-   0x01uy; sbox.(10ul) <-  0x67uy; sbox.(11ul) <-  0x2buy;
  sbox.(12ul) <-  0xfeuy; sbox.(13ul) <-  0xd7uy; sbox.(14ul) <-  0xabuy; sbox.(15ul) <-  0x76uy;
  sbox.(16ul) <-  0xcauy; sbox.(17ul) <-  0x82uy; sbox.(18ul) <-  0xc9uy; sbox.(19ul) <-  0x7duy;
  sbox.(20ul) <-  0xfauy; sbox.(21ul) <-  0x59uy; sbox.(22ul) <-  0x47uy; sbox.(23ul) <-  0xf0uy;
  sbox.(24ul) <-  0xaduy; sbox.(25ul) <-  0xd4uy; sbox.(26ul) <-  0xa2uy; sbox.(27ul) <-  0xafuy;
  sbox.(28ul) <-  0x9cuy; sbox.(29ul) <-  0xa4uy; sbox.(30ul) <-  0x72uy; sbox.(31ul) <-  0xc0uy;
  sbox.(32ul) <-  0xb7uy; sbox.(33ul) <-  0xfduy; sbox.(34ul) <-  0x93uy; sbox.(35ul) <-  0x26uy;
  sbox.(36ul) <-  0x36uy; sbox.(37ul) <-  0x3fuy; sbox.(38ul) <-  0xf7uy; sbox.(39ul) <-  0xccuy;
  sbox.(40ul) <-  0x34uy; sbox.(41ul) <-  0xa5uy; sbox.(42ul) <-  0xe5uy; sbox.(43ul) <-  0xf1uy;
  sbox.(44ul) <-  0x71uy; sbox.(45ul) <-  0xd8uy; sbox.(46ul) <-  0x31uy; sbox.(47ul) <-  0x15uy;
  sbox.(48ul) <-  0x04uy; sbox.(49ul) <-  0xc7uy; sbox.(50ul) <-  0x23uy; sbox.(51ul) <-  0xc3uy;
  sbox.(52ul) <-  0x18uy; sbox.(53ul) <-  0x96uy; sbox.(54ul) <-  0x05uy; sbox.(55ul) <-  0x9auy;
  sbox.(56ul) <-  0x07uy; sbox.(57ul) <-  0x12uy; sbox.(58ul) <-  0x80uy; sbox.(59ul) <-  0xe2uy;
  sbox.(60ul) <-  0xebuy; sbox.(61ul) <-  0x27uy; sbox.(62ul) <-  0xb2uy; sbox.(63ul) <-  0x75uy;
  sbox.(64ul) <-  0x09uy; sbox.(65ul) <-  0x83uy; sbox.(66ul) <-  0x2cuy; sbox.(67ul) <-  0x1auy;
  sbox.(68ul) <-  0x1buy; sbox.(69ul) <-  0x6euy; sbox.(70ul) <-  0x5auy; sbox.(71ul) <-  0xa0uy;
  sbox.(72ul) <-  0x52uy; sbox.(73ul) <-  0x3buy; sbox.(74ul) <-  0xd6uy; sbox.(75ul) <-  0xb3uy;
  sbox.(76ul) <-  0x29uy; sbox.(77ul) <-  0xe3uy; sbox.(78ul) <-  0x2fuy; sbox.(79ul) <-  0x84uy;
  sbox.(80ul) <-  0x53uy; sbox.(81ul) <-  0xd1uy; sbox.(82ul) <-  0x00uy; sbox.(83ul) <-  0xeduy;
  sbox.(84ul) <-  0x20uy; sbox.(85ul) <-  0xfcuy; sbox.(86ul) <-  0xb1uy; sbox.(87ul) <-  0x5buy;
  sbox.(88ul) <-  0x6auy; sbox.(89ul) <-  0xcbuy; sbox.(90ul) <-  0xbeuy; sbox.(91ul) <-  0x39uy;
  sbox.(92ul) <-  0x4auy; sbox.(93ul) <-  0x4cuy; sbox.(94ul) <-  0x58uy; sbox.(95ul) <-  0xcfuy;
  sbox.(96ul) <-  0xd0uy; sbox.(97ul) <-  0xefuy; sbox.(98ul) <-  0xaauy; sbox.(99ul) <-  0xfbuy;
  sbox.(100ul) <- 0x43uy; sbox.(101ul) <- 0x4duy; sbox.(102ul) <- 0x33uy; sbox.(103ul) <- 0x85uy;
  sbox.(104ul) <- 0x45uy; sbox.(105ul) <- 0xf9uy; sbox.(106ul) <- 0x02uy; sbox.(107ul) <- 0x7fuy;
  sbox.(108ul) <- 0x50uy; sbox.(109ul) <- 0x3cuy; sbox.(110ul) <- 0x9fuy; sbox.(111ul) <- 0xa8uy;
  sbox.(112ul) <- 0x51uy; sbox.(113ul) <- 0xa3uy; sbox.(114ul) <- 0x40uy; sbox.(115ul) <- 0x8fuy;
  sbox.(116ul) <- 0x92uy; sbox.(117ul) <- 0x9duy; sbox.(118ul) <- 0x38uy; sbox.(119ul) <- 0xf5uy;
  sbox.(120ul) <- 0xbcuy; sbox.(121ul) <- 0xb6uy; sbox.(122ul) <- 0xdauy; sbox.(123ul) <- 0x21uy;
  sbox.(124ul) <- 0x10uy; sbox.(125ul) <- 0xffuy; sbox.(126ul) <- 0xf3uy; sbox.(127ul) <- 0xd2uy;
  sbox.(128ul) <- 0xcduy; sbox.(129ul) <- 0x0cuy; sbox.(130ul) <- 0x13uy; sbox.(131ul) <- 0xecuy;
  sbox.(132ul) <- 0x5fuy; sbox.(133ul) <- 0x97uy; sbox.(134ul) <- 0x44uy; sbox.(135ul) <- 0x17uy;
  sbox.(136ul) <- 0xc4uy; sbox.(137ul) <- 0xa7uy; sbox.(138ul) <- 0x7euy; sbox.(139ul) <- 0x3duy;
  sbox.(140ul) <- 0x64uy; sbox.(141ul) <- 0x5duy; sbox.(142ul) <- 0x19uy; sbox.(143ul) <- 0x73uy;
  sbox.(144ul) <- 0x60uy; sbox.(145ul) <- 0x81uy; sbox.(146ul) <- 0x4fuy; sbox.(147ul) <- 0xdcuy;
  sbox.(148ul) <- 0x22uy; sbox.(149ul) <- 0x2auy; sbox.(150ul) <- 0x90uy; sbox.(151ul) <- 0x88uy;
  sbox.(152ul) <- 0x46uy; sbox.(153ul) <- 0xeeuy; sbox.(154ul) <- 0xb8uy; sbox.(155ul) <- 0x14uy;
  sbox.(156ul) <- 0xdeuy; sbox.(157ul) <- 0x5euy; sbox.(158ul) <- 0x0buy; sbox.(159ul) <- 0xdbuy;
  sbox.(160ul) <- 0xe0uy; sbox.(161ul) <- 0x32uy; sbox.(162ul) <- 0x3auy; sbox.(163ul) <- 0x0auy;
  sbox.(164ul) <- 0x49uy; sbox.(165ul) <- 0x06uy; sbox.(166ul) <- 0x24uy; sbox.(167ul) <- 0x5cuy;
  sbox.(168ul) <- 0xc2uy; sbox.(169ul) <- 0xd3uy; sbox.(170ul) <- 0xacuy; sbox.(171ul) <- 0x62uy;
  sbox.(172ul) <- 0x91uy; sbox.(173ul) <- 0x95uy; sbox.(174ul) <- 0xe4uy; sbox.(175ul) <- 0x79uy;
  sbox.(176ul) <- 0xe7uy; sbox.(177ul) <- 0xc8uy; sbox.(178ul) <- 0x37uy; sbox.(179ul) <- 0x6duy;
  sbox.(180ul) <- 0x8duy; sbox.(181ul) <- 0xd5uy; sbox.(182ul) <- 0x4euy; sbox.(183ul) <- 0xa9uy;
  sbox.(184ul) <- 0x6cuy; sbox.(185ul) <- 0x56uy; sbox.(186ul) <- 0xf4uy; sbox.(187ul) <- 0xeauy;
  sbox.(188ul) <- 0x65uy; sbox.(189ul) <- 0x7auy; sbox.(190ul) <- 0xaeuy; sbox.(191ul) <- 0x08uy;
  sbox.(192ul) <- 0xbauy; sbox.(193ul) <- 0x78uy; sbox.(194ul) <- 0x25uy; sbox.(195ul) <- 0x2euy;
  sbox.(196ul) <- 0x1cuy; sbox.(197ul) <- 0xa6uy; sbox.(198ul) <- 0xb4uy; sbox.(199ul) <- 0xc6uy;
  sbox.(200ul) <- 0xe8uy; sbox.(201ul) <- 0xdduy; sbox.(202ul) <- 0x74uy; sbox.(203ul) <- 0x1fuy;
  sbox.(204ul) <- 0x4buy; sbox.(205ul) <- 0xbduy; sbox.(206ul) <- 0x8buy; sbox.(207ul) <- 0x8auy;
  sbox.(208ul) <- 0x70uy; sbox.(209ul) <- 0x3euy; sbox.(210ul) <- 0xb5uy; sbox.(211ul) <- 0x66uy;
  sbox.(212ul) <- 0x48uy; sbox.(213ul) <- 0x03uy; sbox.(214ul) <- 0xf6uy; sbox.(215ul) <- 0x0euy;
  sbox.(216ul) <- 0x61uy; sbox.(217ul) <- 0x35uy; sbox.(218ul) <- 0x57uy; sbox.(219ul) <- 0xb9uy;
  sbox.(220ul) <- 0x86uy; sbox.(221ul) <- 0xc1uy; sbox.(222ul) <- 0x1duy; sbox.(223ul) <- 0x9euy;
  sbox.(224ul) <- 0xe1uy; sbox.(225ul) <- 0xf8uy; sbox.(226ul) <- 0x98uy; sbox.(227ul) <- 0x11uy;
  sbox.(228ul) <- 0x69uy; sbox.(229ul) <- 0xd9uy; sbox.(230ul) <- 0x8euy; sbox.(231ul) <- 0x94uy;
  sbox.(232ul) <- 0x9buy; sbox.(233ul) <- 0x1euy; sbox.(234ul) <- 0x87uy; sbox.(235ul) <- 0xe9uy;
  sbox.(236ul) <- 0xceuy; sbox.(237ul) <- 0x55uy; sbox.(238ul) <- 0x28uy; sbox.(239ul) <- 0xdfuy;
  sbox.(240ul) <- 0x8cuy; sbox.(241ul) <- 0xa1uy; sbox.(242ul) <- 0x89uy; sbox.(243ul) <- 0x0duy;
  sbox.(244ul) <- 0xbfuy; sbox.(245ul) <- 0xe6uy; sbox.(246ul) <- 0x42uy; sbox.(247ul) <- 0x68uy;
  sbox.(248ul) <- 0x41uy; sbox.(249ul) <- 0x99uy; sbox.(250ul) <- 0x2duy; sbox.(251ul) <- 0x0fuy;
  sbox.(252ul) <- 0xb0uy; sbox.(253ul) <- 0x54uy; sbox.(254ul) <- 0xbbuy; sbox.(255ul) <- 0x16uy

val mk_inv_sbox: sb:sbox -> Stack unit
  (requires (fun h -> live h sb))
  (ensures  (fun h0 _ h1 -> live h1 sb /\ modifies_1 sb h0 h1))
let mk_inv_sbox sbox =
  sbox.(0ul) <-   0x52uy; sbox.(1ul) <-   0x09uy; sbox.(2ul) <-   0x6auy; sbox.(3ul) <-   0xd5uy;
  sbox.(4ul) <-   0x30uy; sbox.(5ul) <-   0x36uy; sbox.(6ul) <-   0xa5uy; sbox.(7ul) <-   0x38uy;
  sbox.(8ul) <-   0xbfuy; sbox.(9ul) <-   0x40uy; sbox.(10ul) <-  0xa3uy; sbox.(11ul) <-  0x9euy;
  sbox.(12ul) <-  0x81uy; sbox.(13ul) <-  0xf3uy; sbox.(14ul) <-  0xd7uy; sbox.(15ul) <-  0xfbuy;
  sbox.(16ul) <-  0x7cuy; sbox.(17ul) <-  0xe3uy; sbox.(18ul) <-  0x39uy; sbox.(19ul) <-  0x82uy;
  sbox.(20ul) <-  0x9buy; sbox.(21ul) <-  0x2fuy; sbox.(22ul) <-  0xffuy; sbox.(23ul) <-  0x87uy;
  sbox.(24ul) <-  0x34uy; sbox.(25ul) <-  0x8euy; sbox.(26ul) <-  0x43uy; sbox.(27ul) <-  0x44uy;
  sbox.(28ul) <-  0xc4uy; sbox.(29ul) <-  0xdeuy; sbox.(30ul) <-  0xe9uy; sbox.(31ul) <-  0xcbuy;
  sbox.(32ul) <-  0x54uy; sbox.(33ul) <-  0x7buy; sbox.(34ul) <-  0x94uy; sbox.(35ul) <-  0x32uy;
  sbox.(36ul) <-  0xa6uy; sbox.(37ul) <-  0xc2uy; sbox.(38ul) <-  0x23uy; sbox.(39ul) <-  0x3duy;
  sbox.(40ul) <-  0xeeuy; sbox.(41ul) <-  0x4cuy; sbox.(42ul) <-  0x95uy; sbox.(43ul) <-  0x0buy;
  sbox.(44ul) <-  0x42uy; sbox.(45ul) <-  0xfauy; sbox.(46ul) <-  0xc3uy; sbox.(47ul) <-  0x4euy;
  sbox.(48ul) <-  0x08uy; sbox.(49ul) <-  0x2euy; sbox.(50ul) <-  0xa1uy; sbox.(51ul) <-  0x66uy;
  sbox.(52ul) <-  0x28uy; sbox.(53ul) <-  0xd9uy; sbox.(54ul) <-  0x24uy; sbox.(55ul) <-  0xb2uy;
  sbox.(56ul) <-  0x76uy; sbox.(57ul) <-  0x5buy; sbox.(58ul) <-  0xa2uy; sbox.(59ul) <-  0x49uy;
  sbox.(60ul) <-  0x6duy; sbox.(61ul) <-  0x8buy; sbox.(62ul) <-  0xd1uy; sbox.(63ul) <-  0x25uy;
  sbox.(64ul) <-  0x72uy; sbox.(65ul) <-  0xf8uy; sbox.(66ul) <-  0xf6uy; sbox.(67ul) <-  0x64uy;
  sbox.(68ul) <-  0x86uy; sbox.(69ul) <-  0x68uy; sbox.(70ul) <-  0x98uy; sbox.(71ul) <-  0x16uy;
  sbox.(72ul) <-  0xd4uy; sbox.(73ul) <-  0xa4uy; sbox.(74ul) <-  0x5cuy; sbox.(75ul) <-  0xccuy;
  sbox.(76ul) <-  0x5duy; sbox.(77ul) <-  0x65uy; sbox.(78ul) <-  0xb6uy; sbox.(79ul) <-  0x92uy;
  sbox.(80ul) <-  0x6cuy; sbox.(81ul) <-  0x70uy; sbox.(82ul) <-  0x48uy; sbox.(83ul) <-  0x50uy;
  sbox.(84ul) <-  0xfduy; sbox.(85ul) <-  0xeduy; sbox.(86ul) <-  0xb9uy; sbox.(87ul) <-  0xdauy;
  sbox.(88ul) <-  0x5euy; sbox.(89ul) <-  0x15uy; sbox.(90ul) <-  0x46uy; sbox.(91ul) <-  0x57uy;
  sbox.(92ul) <-  0xa7uy; sbox.(93ul) <-  0x8duy; sbox.(94ul) <-  0x9duy; sbox.(95ul) <-  0x84uy;
  sbox.(96ul) <-  0x90uy; sbox.(97ul) <-  0xd8uy; sbox.(98ul) <-  0xabuy; sbox.(99ul) <-  0x00uy;
  sbox.(100ul) <- 0x8cuy; sbox.(101ul) <- 0xbcuy; sbox.(102ul) <- 0xd3uy; sbox.(103ul) <- 0x0auy;
  sbox.(104ul) <- 0xf7uy; sbox.(105ul) <- 0xe4uy; sbox.(106ul) <- 0x58uy; sbox.(107ul) <- 0x05uy;
  sbox.(108ul) <- 0xb8uy; sbox.(109ul) <- 0xb3uy; sbox.(110ul) <- 0x45uy; sbox.(111ul) <- 0x06uy;
  sbox.(112ul) <- 0xd0uy; sbox.(113ul) <- 0x2cuy; sbox.(114ul) <- 0x1euy; sbox.(115ul) <- 0x8fuy;
  sbox.(116ul) <- 0xcauy; sbox.(117ul) <- 0x3fuy; sbox.(118ul) <- 0x0fuy; sbox.(119ul) <- 0x02uy;
  sbox.(120ul) <- 0xc1uy; sbox.(121ul) <- 0xafuy; sbox.(122ul) <- 0xbduy; sbox.(123ul) <- 0x03uy;
  sbox.(124ul) <- 0x01uy; sbox.(125ul) <- 0x13uy; sbox.(126ul) <- 0x8auy; sbox.(127ul) <- 0x6buy;
  sbox.(128ul) <- 0x3auy; sbox.(129ul) <- 0x91uy; sbox.(130ul) <- 0x11uy; sbox.(131ul) <- 0x41uy;
  sbox.(132ul) <- 0x4fuy; sbox.(133ul) <- 0x67uy; sbox.(134ul) <- 0xdcuy; sbox.(135ul) <- 0xeauy;
  sbox.(136ul) <- 0x97uy; sbox.(137ul) <- 0xf2uy; sbox.(138ul) <- 0xcfuy; sbox.(139ul) <- 0xceuy;
  sbox.(140ul) <- 0xf0uy; sbox.(141ul) <- 0xb4uy; sbox.(142ul) <- 0xe6uy; sbox.(143ul) <- 0x73uy;
  sbox.(144ul) <- 0x96uy; sbox.(145ul) <- 0xacuy; sbox.(146ul) <- 0x74uy; sbox.(147ul) <- 0x22uy;
  sbox.(148ul) <- 0xe7uy; sbox.(149ul) <- 0xaduy; sbox.(150ul) <- 0x35uy; sbox.(151ul) <- 0x85uy;
  sbox.(152ul) <- 0xe2uy; sbox.(153ul) <- 0xf9uy; sbox.(154ul) <- 0x37uy; sbox.(155ul) <- 0xe8uy;
  sbox.(156ul) <- 0x1cuy; sbox.(157ul) <- 0x75uy; sbox.(158ul) <- 0xdfuy; sbox.(159ul) <- 0x6euy;
  sbox.(160ul) <- 0x47uy; sbox.(161ul) <- 0xf1uy; sbox.(162ul) <- 0x1auy; sbox.(163ul) <- 0x71uy;
  sbox.(164ul) <- 0x1duy; sbox.(165ul) <- 0x29uy; sbox.(166ul) <- 0xc5uy; sbox.(167ul) <- 0x89uy;
  sbox.(168ul) <- 0x6fuy; sbox.(169ul) <- 0xb7uy; sbox.(170ul) <- 0x62uy; sbox.(171ul) <- 0x0euy;
  sbox.(172ul) <- 0xaauy; sbox.(173ul) <- 0x18uy; sbox.(174ul) <- 0xbeuy; sbox.(175ul) <- 0x1buy;
  sbox.(176ul) <- 0xfcuy; sbox.(177ul) <- 0x56uy; sbox.(178ul) <- 0x3euy; sbox.(179ul) <- 0x4buy;
  sbox.(180ul) <- 0xc6uy; sbox.(181ul) <- 0xd2uy; sbox.(182ul) <- 0x79uy; sbox.(183ul) <- 0x20uy;
  sbox.(184ul) <- 0x9auy; sbox.(185ul) <- 0xdbuy; sbox.(186ul) <- 0xc0uy; sbox.(187ul) <- 0xfeuy;
  sbox.(188ul) <- 0x78uy; sbox.(189ul) <- 0xcduy; sbox.(190ul) <- 0x5auy; sbox.(191ul) <- 0xf4uy;
  sbox.(192ul) <- 0x1fuy; sbox.(193ul) <- 0xdduy; sbox.(194ul) <- 0xa8uy; sbox.(195ul) <- 0x33uy;
  sbox.(196ul) <- 0x88uy; sbox.(197ul) <- 0x07uy; sbox.(198ul) <- 0xc7uy; sbox.(199ul) <- 0x31uy;
  sbox.(200ul) <- 0xb1uy; sbox.(201ul) <- 0x12uy; sbox.(202ul) <- 0x10uy; sbox.(203ul) <- 0x59uy;
  sbox.(204ul) <- 0x27uy; sbox.(205ul) <- 0x80uy; sbox.(206ul) <- 0xecuy; sbox.(207ul) <- 0x5fuy;
  sbox.(208ul) <- 0x60uy; sbox.(209ul) <- 0x51uy; sbox.(210ul) <- 0x7fuy; sbox.(211ul) <- 0xa9uy;
  sbox.(212ul) <- 0x19uy; sbox.(213ul) <- 0xb5uy; sbox.(214ul) <- 0x4auy; sbox.(215ul) <- 0x0duy;
  sbox.(216ul) <- 0x2duy; sbox.(217ul) <- 0xe5uy; sbox.(218ul) <- 0x7auy; sbox.(219ul) <- 0x9fuy;
  sbox.(220ul) <- 0x93uy; sbox.(221ul) <- 0xc9uy; sbox.(222ul) <- 0x9cuy; sbox.(223ul) <- 0xefuy;
  sbox.(224ul) <- 0xa0uy; sbox.(225ul) <- 0xe0uy; sbox.(226ul) <- 0x3buy; sbox.(227ul) <- 0x4duy;
  sbox.(228ul) <- 0xaeuy; sbox.(229ul) <- 0x2auy; sbox.(230ul) <- 0xf5uy; sbox.(231ul) <- 0xb0uy;
  sbox.(232ul) <- 0xc8uy; sbox.(233ul) <- 0xebuy; sbox.(234ul) <- 0xbbuy; sbox.(235ul) <- 0x3cuy;
  sbox.(236ul) <- 0x83uy; sbox.(237ul) <- 0x53uy; sbox.(238ul) <- 0x99uy; sbox.(239ul) <- 0x61uy;
  sbox.(240ul) <- 0x17uy; sbox.(241ul) <- 0x2buy; sbox.(242ul) <- 0x04uy; sbox.(243ul) <- 0x7euy;
  sbox.(244ul) <- 0xbauy; sbox.(245ul) <- 0x77uy; sbox.(246ul) <- 0xd6uy; sbox.(247ul) <- 0x26uy;
  sbox.(248ul) <- 0xe1uy; sbox.(249ul) <- 0x69uy; sbox.(250ul) <- 0x14uy; sbox.(251ul) <- 0x63uy;
  sbox.(252ul) <- 0x55uy; sbox.(253ul) <- 0x21uy; sbox.(254ul) <- 0x0cuy; sbox.(255ul) <- 0x7duy
#reset-options

let rec access_aux: sb:sbox -> byte -> ctr:UInt32.t{v ctr <= 256} -> byte -> Stack byte
  (requires (fun h -> live h sb))
  (ensures  (fun h0 _ h1 -> h1 == h0))
  = fun sbox i ctr tmp ->
  if ctr = 256ul then tmp
  else let mask = eq_mask i (uint32_to_uint8 ctr) in
       let tmp = tmp |^ (mask &^ sbox.(ctr)) in
       access_aux sbox i (U32.(ctr +^ 1ul)) tmp

val access: sb:sbox -> idx:byte -> Stack byte
  (requires (fun h -> live h sb))
  (ensures  (fun h0 _ h1 -> h1 == h0))
let access sbox i =
  if Flag.aes_ct then access_aux sbox i 0ul 0uy
  else sbox.(Int.Cast.uint8_to_uint32 i)


// ENCRYPTION 

val subBytes_aux_sbox: state:block -> sb:sbox{disjoint state sb} -> ctr:idx_16 -> Stack unit
  (requires (fun h -> live h state /\ live h sb))
  (ensures  (fun h0 _ h1 -> live h1 state /\ modifies_1 state h0 h1))
let rec subBytes_aux_sbox state sbox ctr =
  if ctr <> 16ul then 
  begin
    let si = state.(ctr) in
    let si' = access sbox si in
    state.(ctr) <- si';
    subBytes_aux_sbox state sbox (U32.(ctr +^ 1ul))
  end

val subBytes_sbox: state:block -> sbox:sbox{disjoint state sbox} -> Stack unit
  (requires (fun h -> live h state /\ live h sbox))
  (ensures  (fun h0 _ h1 -> modifies_1 state h0 h1 /\ live h1 state))
let subBytes_sbox state sbox =
  subBytes_aux_sbox state sbox 0ul

val shiftRows: state:block -> Stack unit
  (requires (fun h -> live h state))
  (ensures  (fun h0 _ h1 -> live h1 state /\ modifies_1 state h0 h1))
let shiftRows state =
  let open FStar.UInt32 in
  let i = 1ul in
  let tmp = state.(i) in
  state.(i)       <- state.(i+^ 4ul);
  state.(i+^ 4ul) <- state.(i+^ 8ul);
  state.(i+^ 8ul) <- state.(i+^12ul);
  state.(i+^12ul) <- tmp;

  let i = 2ul in
  let tmp = state.(i) in
  state.(i)       <- state.(i+^8ul);
  state.(i+^ 8ul) <- tmp;
  let tmp = state.(i+^4ul) in
  state.(i+^ 4ul) <- state.(i+^12ul);
  state.(i+^12ul) <- tmp;

  let i = 3ul in
  let tmp = state.(i) in
  state.(i)       <- state.(i+^12ul);
  state.(i+^12ul) <- state.(i+^ 8ul);
  state.(i+^ 8ul) <- state.(i+^ 4ul);
  state.(i+^ 4ul) <- tmp

val mixColumns_: state:block -> c:UInt32.t{v c < 4} -> Stack unit
  (requires (fun h -> live h state))
  (ensures  (fun h0 _ h1 -> live h1 state /\ modifies_1 state h0 h1))
let mixColumns_ state c =
  let s = Buffer.sub state (H32.(4ul*^c)) 4ul in 
  let s0 = s.(0ul) in
  let s1 = s.(1ul) in
  let s2 = s.(2ul) in
  let s3 = s.(3ul) in
  s.(0ul) <- H8.(multiply 0x2uy s0 ^^ multiply 0x3uy s1 ^^ s2 ^^ s3);
  s.(1ul) <- H8.(multiply 0x2uy s1 ^^ multiply 0x3uy s2 ^^ s3 ^^ s0);
  s.(2ul) <- H8.(multiply 0x2uy s2 ^^ multiply 0x3uy s3 ^^ s0 ^^ s1);
  s.(3ul) <- H8.(multiply 0x2uy s3 ^^ multiply 0x3uy s0 ^^ s1 ^^ s2)

#reset-options "--initial_fuel 0 --max_fuel 0"

val mixColumns: state:block -> Stack unit
  (requires (fun h -> live h state))
  (ensures  (fun h0 _ h1 -> live h1 state /\ modifies_1 state h0 h1))
let mixColumns state =
  mixColumns_ state 0ul;
  mixColumns_ state 1ul;
  mixColumns_ state 2ul;
  mixColumns_ state 3ul

#reset-options "--z3rlimit 10 --initial_fuel 0 --max_fuel 0"

val addRoundKey_: state:block -> w:xkey{disjoint state w} -> rnd -> c:UInt32.t{v c < 4} -> Stack unit
  (requires (fun h -> live h state /\ live h w))
  (ensures  (fun h0 _ h1 -> live h1 state /\ modifies_1 state h0 h1))
let addRoundKey_ state w round c =
  let open FStar.UInt32 in
  let target = Buffer.sub state (4ul*^c) 4ul in 
  let subkey = Buffer.sub w (blocklen*^round +^ 4ul*^c) 4ul in
  let open FStar.UInt8 in 
  target.(0ul) <- target.(0ul) ^^ subkey.(0ul);
  target.(1ul) <- target.(1ul) ^^ subkey.(1ul);
  target.(2ul) <- target.(2ul) ^^ subkey.(2ul);
  target.(3ul) <- target.(3ul) ^^ subkey.(3ul)

val addRoundKey: state:block -> w:xkey{disjoint state w} -> round:rnd  -> Stack unit
  (requires (fun h -> live h state /\ live h w))
  (ensures  (fun h0 _ h1 -> live h1 state /\ modifies_1 state h0 h1))
let addRoundKey state w round =
  addRoundKey_ state w round 0ul;
  addRoundKey_ state w round 1ul;
  addRoundKey_ state w round 2ul;
  addRoundKey_ state w round 3ul

val cipher_loop: state:block -> w:xkey{disjoint state w} -> sb:sbox{disjoint sb state} -> round:rnd -> Stack unit
  (requires (fun h -> live h state /\ live h w /\ live h sb))
  (ensures  (fun h0 _ h1 -> live h1 state /\ modifies_1 state h0 h1))
let rec cipher_loop state w sbox round =
  let open FStar.UInt32 in
  if round <> nr then 
  begin
    subBytes_sbox state sbox;   
    shiftRows     state;
    mixColumns    state;
    addRoundKey   state w round;
    cipher_loop   state w sbox (round+^1ul)
  end

#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

val cipher: out:block -> input:block -> w:xkey -> sb:sbox -> Stack unit
  (requires (fun h -> live h out /\ live h input /\ live h w /\ live h sb /\ 
                   disjoint out input /\ disjoint out w /\ disjoint out sb))
  (ensures  (fun h0 _ h1 -> live h1 out /\ modifies_1 out h0 h1))
let cipher out input w sbox =
  push_frame();
  let state = create 0uy blocklen in // could we use output instead? alignment? 
  blit input 0ul state 0ul blocklen;
  addRoundKey    state w 0ul;
  cipher_loop    state w sbox 1ul;
  subBytes_sbox  state sbox;
  shiftRows      state;
  addRoundKey    state w nr;
  blit state 0ul out 0ul blocklen;
  pop_frame()


// KEY EXPANSION

val rotWord: word:lbytes 4 -> Stack unit
  (requires (fun h -> live h word))
  (ensures  (fun h0 _ h1 -> live h1 word /\ modifies_1 word h0 h1))
let rotWord word =
  let w0 = word.(0ul) in
  let w1 = word.(1ul) in
  let w2 = word.(2ul) in
  let w3 = word.(3ul) in
  word.(0ul) <- w1;
  word.(1ul) <- w2;
  word.(2ul) <- w3;
  word.(3ul) <- w0

val subWord: word:lbytes 4 -> sbox:sbox -> Stack unit
  (requires (fun h -> live h word /\ live h sbox /\ disjoint word sbox))
  (ensures  (fun h0 _ h1 -> live h1 word /\ modifies_1 word h0 h1))
let subWord word sbox =
  word.(0ul) <- access sbox word.(0ul);
  word.(1ul) <- access sbox word.(1ul);
  word.(2ul) <- access sbox word.(2ul);
  word.(3ul) <- access sbox word.(3ul)

#reset-options "--z3rlimit 40 --initial_fuel 0 --max_fuel 0"

val rcon: i:UInt32.t{v i >= 1} -> byte -> Tot byte (decreases (v i))
let rec rcon i tmp =
  if i = 1ul then tmp
  else begin
    let tmp = multiply 0x2uy tmp in
    rcon (U32.(i-^1ul)) tmp
  end

#reset-options "--z3rlimit 20 --initial_fuel 0 --max_fuel 0"

val keyExpansion_aux_0:w:xkey -> temp:lbytes 4 -> sbox:sbox -> i:UInt32.t{v i < (v xkeylen / 4) /\ v i >= v nk} -> Stack unit
  (requires (fun h -> live h w /\ live h temp /\ live h sbox /\ 
                   disjoint w temp /\ disjoint w sbox /\ disjoint temp sbox))
  (ensures  (fun h0 _ h1 -> live h1 temp /\ modifies_1 temp h0 h1))
let keyExpansion_aux_0 w temp sbox j =
  let open FStar.UInt32 in
  let h0 = ST.get() in
  blit w (4ul *^ j -^ 4ul) temp 0ul 4ul;
  if j %^ nk = 0ul then (
    rotWord temp;
    subWord temp sbox;
    let t0 = temp.(0ul) in
    let rc = rcon (j/^nk) 1uy in
    let z = H8.(t0 ^^ rc) in
    temp.(0ul) <- z ) 
  else if j %^ nk = 4ul then 
    subWord temp sbox
  

#reset-options "--z3rlimit 50 --initial_fuel 0 --max_fuel 0"

val keyExpansion_aux_1: w:xkey -> temp:lbytes 4 -> sbox:sbox -> i:UInt32.t{v i < (v xkeylen / 4) /\ v i >= v nk} -> Stack unit
  (requires (fun h -> live h w /\ live h temp /\ live h sbox
    /\ disjoint w temp /\ disjoint w sbox /\ disjoint temp sbox))
  (ensures  (fun h0 _ h1 -> live h1 w /\ modifies_1 w h0 h1))
let keyExpansion_aux_1 w temp sbox j =
  let open FStar.UInt32 in
  let i = 4ul *^ j in
  let w0 = w.(i +^ 0ul -^ keylen) in
  let w1 = w.(i +^ 1ul -^ keylen) in
  let w2 = w.(i +^ 2ul -^ keylen) in
  let w3 = w.(i +^ 3ul -^ keylen) in
  let t0 = temp.(0ul) in
  let t1 = temp.(1ul) in
  let t2 = temp.(2ul) in
  let t3 = temp.(3ul) in
  w.(i+^0ul) <- H8.(t0 ^^ w0);
  w.(i+^1ul) <- H8.(t1 ^^ w1);
  w.(i+^2ul) <- H8.(t2 ^^ w2);
  w.(i+^3ul) <- H8.(t3 ^^ w3)

val keyExpansion_aux: w:xkey -> temp:lbytes 4 -> sbox:sbox -> i:UInt32.t{v i <= (v xkeylen / 4) /\ v i >= v nk} -> Stack unit
  (requires (fun h -> live h w /\ live h temp /\ live h sbox
    /\ disjoint w temp /\ disjoint w sbox /\ disjoint temp sbox))
  (ensures  (fun h0 _ h1 -> live h1 temp /\ live h1 w /\ modifies_2 temp w h0 h1))
let rec keyExpansion_aux w temp sbox j =
  let open FStar.UInt32 in
  let h0 = ST.get() in
  if j <^ (xkeylen /^ 4ul) then
  begin
    keyExpansion_aux_0 w temp sbox j;
    keyExpansion_aux_1 w temp sbox j;
    keyExpansion_aux w temp sbox (j +^ 1ul)
  end

val keyExpansion: key:skey -> w:xkey -> sb:sbox -> Stack unit
  (requires (fun h -> live h key /\ live h w /\ live h sb /\ disjoint key w /\ disjoint w sb))
  (ensures  (fun h0 _ h1 -> live h1 w /\ modifies_1 w h0 h1))
let keyExpansion key w sbox =
  let open FStar.UInt32 in
  push_frame();
  let temp = create 0uy 4ul in
  blit key 0ul w 0ul keylen;
  keyExpansion_aux w temp sbox nk;
  pop_frame()


// DECRYPTION

val invSubBytes_aux_sbox: state:block -> sbox:sbox -> ctr:idx_16 -> Stack unit
  (requires (fun h -> live h state /\ live h sbox /\ disjoint state sbox))
  (ensures  (fun h0 _ h1 -> live h1 state /\ modifies_1 state h0 h1))
let rec invSubBytes_aux_sbox state sbox ctr =
  if ctr = 16ul then ()
  else begin
    let si = state.(ctr) in
    let si' = access sbox si in
    state.(ctr) <- si';
    invSubBytes_aux_sbox state sbox (U32.(ctr+^1ul))
  end

val invSubBytes_sbox: state:block -> sbox:sbox -> Stack unit
  (requires (fun h -> live h state /\ live h sbox /\ disjoint state sbox))
  (ensures  (fun h0 _ h1 -> live h1 state /\ modifies_1 state h0 h1))
let invSubBytes_sbox state sbox =
  invSubBytes_aux_sbox state sbox 0ul

val invShiftRows: state:block -> Stack unit
  (requires (fun h -> live h state))
  (ensures  (fun h0 _ h1 -> live h1 state /\ modifies_1 state h0 h1))
let invShiftRows state =
  let open FStar.UInt32 in
  let i = 3ul in
  let tmp = state.(i) in
  state.(i)       <- state.(i+^4ul);
  state.(i+^4ul)  <- state.(i+^8ul);
  state.(i+^8ul)  <- state.(i+^12ul);
  state.(i+^12ul) <- tmp;

  let i = 2ul in
  let tmp = state.(i) in
  state.(i)       <- state.(i+^8ul);
  state.(i+^8ul)  <- tmp;
  let tmp = state.(i+^4ul) in
  state.(i+^4ul)  <- state.(i+^12ul);
  state.(i+^12ul) <- tmp;

  let i = 1ul in
  let tmp = state.(i) in
  state.(i)       <- state.(i+^12ul);
  state.(i+^12ul) <- state.(i+^8ul);
  state.(i+^8ul)  <- state.(i+^4ul);
  state.(i+^4ul)  <- tmp

val invMixColumns_: state:block -> c:UInt32.t{v c < 4} -> Stack unit
  (requires (fun h -> live h state))
  (ensures  (fun h0 _ h1 -> live h1 state /\ modifies_1 state h0 h1 ))
let invMixColumns_ state c =
  let s = Buffer.sub state (H32.(4ul*^c)) 4ul in 
  let s0 = s.(0ul) in
  let s1 = s.(1ul) in
  let s2 = s.(2ul) in
  let s3 = s.(3ul) in
  let mix x0 x1 x2 x3 = H8.(multiply 0xeuy x0 ^^ multiply 0xbuy x1 ^^ multiply 0xduy x2 ^^ multiply 0x9uy x3) in
  s.(0ul) <- mix s0 s1 s2 s3;
  s.(1ul) <- mix s1 s2 s3 s0;
  s.(2ul) <- mix s2 s3 s0 s1;
  s.(3ul) <- mix s3 s0 s1 s2

#reset-options "--initial_fuel 0 --max_fuel 0"

val invMixColumns: state:block -> Stack unit
  (requires (fun h -> live h state))
  (ensures  (fun h0 _ h1 -> live h1 state /\ modifies_1 state h0 h1 ))
let invMixColumns state =
  invMixColumns_ state 0ul;
  invMixColumns_ state 1ul;
  invMixColumns_ state 2ul;
  invMixColumns_ state 3ul

val inv_cipher_loop: state:block -> w:xkey -> sb:sbox -> round:UInt32.t{v round <= v nr - 1} -> Stack unit
  (requires (fun h -> live h state /\ live h w /\ live h sb /\ disjoint state w /\ disjoint state sb /\ disjoint sb w))
  (ensures  (fun h0 _ h1 -> live h1 state /\ modifies_1 state h0 h1 ))
let rec inv_cipher_loop state w sbox round =
  let open FStar.UInt32 in
  if round <> 0ul then
  begin
    invShiftRows state;
    invSubBytes_sbox state sbox;
    addRoundKey state w round;
    invMixColumns state;
    inv_cipher_loop state w sbox (round -^ 1ul)
  end

val inv_cipher: out:block -> input:block -> w:xkey -> sb:sbox -> Stack unit
  (requires (fun h -> live h out /\ live h input /\ live h w /\ live h sb /\ 
                   disjoint out input /\ disjoint out w /\ disjoint out sb /\ disjoint sb w))
  (ensures  (fun h0 _ h1 -> live h1 out /\ modifies_1 out h0 h1))
let inv_cipher out input w sbox =
  push_frame();
  let state = create 0uy blocklen in
  blit input 0ul   state 0ul blocklen;
  addRoundKey      state w nr;
  inv_cipher_loop  state w sbox (U32.(nr -^ 1ul));
  invShiftRows     state;
  invSubBytes_sbox state sbox;
  addRoundKey      state w 0ul;
  blit state 0ul out 0ul blocklen;
  pop_frame()
