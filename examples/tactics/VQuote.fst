module VQuote

let var = 2
type myrec = { a:int ; b:bool }

let _ = assert (`%var     == "VQuote.var")
let _ = assert (`%Some?.v == "FStar.Pervasives.Native.__proj__Some__item__v")
let _ = assert (`%Some?   == "FStar.Pervasives.Native.uu___is_Some")
let _ = assert (`%Some    == "FStar.Pervasives.Native.Some")
let _ = assert (`%int     == "Prims.int")
let _ = assert (`%(Mkmyrec?.a) == "VQuote.__proj__Mkmyrec__item__a")
let _ = assert (`%(Mkmyrec?.b) == "VQuote.__proj__Mkmyrec__item__b")
