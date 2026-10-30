module StaticHeaderReuseApp

let main () : FStar.All.ML FStar.UInt32.t =
  if StaticHeaderReuse.api 40ul = 42ul &&
     StaticHeaderReuse.helper 40ul = 42ul &&
     StaticHeader_hidden.api 40ul = 42ul &&
     StaticHeader_hidden.collision 40ul = 42ul &&
     StaticHeader.hidden_collision 41ul = 42ul &&
     StaticHeader.helper 41ul = 42ul &&
     StaticHeader.plain 2ul = 3ul && StaticHeader.api 1ul = 12ul
  then 0ul else 1ul
