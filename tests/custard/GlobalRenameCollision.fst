module GlobalRenameCollision

[@@FStar.Attributes.rename_let "same_name"]
private let first (x:FStar.UInt32.t) = FStar.UInt32.add_mod x 1ul

[@@FStar.Attributes.rename_let "same_name"]
private let second (x:FStar.UInt32.t) = FStar.UInt32.add_mod x 2ul

let main () = FStar.UInt32.add_mod (first 1ul) (second 2ul)
