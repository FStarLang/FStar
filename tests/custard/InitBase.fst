module InitBase
module U32 = FStar.UInt32

(* Section 116.  A global whose value another unit's global is computed from:
   the linked initializers have to run in dependency order, which is the order
   --custard_link was written in. *)
type point = { x:U32.t; y:U32.t }

let origin : point = { x = 3ul; y = 4ul }

let sum (_:unit) : U32.t = U32.add_mod origin.x origin.y
