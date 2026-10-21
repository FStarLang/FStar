module StaticHeaderApp

let main () : FStar.All.ML FStar.UInt32.t =
  let p = { StaticHeader.left = 1ul; StaticHeader.right = 2ul } in
  if StaticHeader.api 1ul = 12ul && StaticHeader.plain 2ul = 3ul &&
     StaticHeader.equal p p && StaticHeader.countdown 3ul = 0ul &&
     StaticHeader.helper 41ul = 42ul && StaticHeader.helper' 40ul = 42ul &&
     StaticHeader.helper_ 39ul = 42ul && StaticHeader.collision 0ul = 25ul &&
     StaticHeader.internal_limit = 19ul
  then 0ul else 1ul
