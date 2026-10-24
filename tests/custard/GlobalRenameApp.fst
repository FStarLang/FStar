module GlobalRenameApp

let main () : FStar.All.ML FStar.Int32.t =
  if FStar.UInt32.eq (GlobalRenameIface.step 41ul) 42ul then 0l else 1l
