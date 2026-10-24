module CNoUnfold

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module I = CNoUnfoldIface

noeq type pair (a:Type) = { fst: a; snd: a }

[@@FStar.Attributes.custard_no_unfold]
type byte_pair = pair U8.t

type flag_pair = pair bool

[@@FStar.Attributes.custard_no_unfold]
type word = U32.t

[@@FStar.Attributes.custard_no_unfold]
type callback = word -> word

[@@FStar.Attributes.custard_no_unfold]
type named_pair (a:Type) = pair a

[@@FStar.Attributes.custard_no_unfold]
type unused_word = FStar.UInt64.t

type cli_word = U16.t

let swap (p:byte_pair) : byte_pair = { fst = p.snd; snd = p.fst }
let swapf (p:flag_pair) : flag_pair = { fst = p.snd; snd = p.fst }
let increment (x:word) : word = U32.add_mod x 1ul
let apply (f:callback) (x:word) : word = f x
let swap_named (p:named_pair U32.t) : named_pair U32.t =
  { fst = p.snd; snd = p.fst }
let cli_identity (x:cli_word) : cli_word = x

let main () : U32.t =
  let p = swap { fst = 1uy; snd = 2uy } in
  let q = swapf { fst = true; snd = false } in
  let r = swap_named { fst = 3ul; snd = 4ul } in
  if p.fst = 2uy && p.snd = 1uy &&
     not q.fst && q.snd &&
     r.fst = 4ul && r.snd = 3ul &&
     apply increment 41ul = 42ul &&
     cli_identity 7us = 7us &&
     I.identity 9ul = 9ul
  then 0ul else 1ul
