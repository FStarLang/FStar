module GlobalRenameOCaml

[@@FStar.Attributes.rename_let "COnlyName"]
let increment (x:int) : int = x + 1

let main () : FStar.All.ML unit =
  FStar.IO.print_string
    (if increment 41 = 42 && FStar.UInt32.eq (GlobalRenameIface.step 41ul) 42ul
     then "ok\n" else "bad\n")
