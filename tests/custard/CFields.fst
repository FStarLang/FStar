module CFields
module U32 = FStar.UInt32
module I32 = FStar.Int32
open FStar.All

(* Section 116.  Appending an underscore is an escape only if it lands where
   nothing else does.  [switch] is a C keyword and [switch_] is not, and both
   came out as [switch_] -- two members of one struct with one name.  The
   escape now strips the trailing underscores before the keyword test, which
   shifts the whole family by one. *)
type pair = { switch:U32.t; switch_:U32.t }

let select (p:pair) : U32.t = U32.add_mod p.switch p.switch_

let main () : ML I32.t =
  if U32.eq (select ({ switch = 3ul; switch_ = 4ul })) 7ul then 0l else 1l
