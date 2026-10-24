module GlobalRenameSpecCollision
module U32 = FStar.UInt32

[@@FStar.Attributes.rename_let "one_instance"]
let rec countdown (#a:Type) (x:a) (n:U32.t) : Tot a (decreases (U32.v n)) =
  if U32.gt n 0ul then countdown x (U32.sub n 1ul) else x

let main () =
  if countdown true 1ul then countdown 0ul 1ul else 1ul
