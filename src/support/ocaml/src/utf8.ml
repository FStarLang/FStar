(* -------------------------------------------------------------------- *)
module Impl = BatUTF8

(* -------------------------------------------------------------------- *)
type ustring = Impl.t

exception InvalidEncoding

(* -------------------------------------------------------------------- *)
let of_utf8 (b : string) : ustring =
  (try Impl.validate b with Impl.Malformed_code -> raise InvalidEncoding);
  (b : ustring)

(* -------------------------------------------------------------------- *)
let to_utf8 (b : string) : ustring =
  (b : string)
