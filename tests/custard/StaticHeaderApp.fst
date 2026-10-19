module StaticHeaderApp

let main () : FStar.All.ML FStar.UInt32.t =
  let p = { StaticHeader.left = 1ul; StaticHeader.right = 2ul } in
  if StaticHeader.api 1ul = 12ul && StaticHeader.plain 2ul = 3ul &&
     StaticHeader.equal p p && StaticHeader.countdown 3ul = 0ul
  then 0ul else 1ul
