module GlobalRenameTag

type tag = | Tag | Other

[@@FStar.Attributes.rename_let "GLOBALRENAMETAG_TAG"]
let helper (x:tag) : FStar.UInt32.t = match x with | Tag -> 0ul | Other -> 1ul

let main () = helper Tag
