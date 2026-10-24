module GlobalRenameInvalid

[@@FStar.Attributes.rename_let "not-a-name"]
let main () = 0ul
