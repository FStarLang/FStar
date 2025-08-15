(* See FStar.StringBuffer.fsi *)
type t = Buffer.t
let create (i:Z.t) = Buffer.create (Z.to_int i)
let add s t = Buffer.add_string t s; t
let contents = Buffer.contents
let clear t = Buffer.clear t; t
let output_channel = Buffer.output_buffer
