module GlobalRenameImported

[@@FStar.Attributes.rename_let "InterfaceStep"]
let step (x:FStar.UInt32.t) = FStar.UInt32.add_mod x 2ul

let main () = step (GlobalRenameIface.step 0ul)
