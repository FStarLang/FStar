(* See FStar.StringBuffer.fsi *)
type t = Buffer.t
let create (i:FStarC_BigInt.t) = Buffer.create (FStarC_BigInt.to_int i)
let add s t = Buffer.add_string t s; t
let contents = Buffer.contents
let clear t = Buffer.clear t; t
let output_channel = Buffer.output_buffer
