module Bug807c

noeq
type t = { f : (#x:int) -> unit }

let test (c:t) = c.f #2
