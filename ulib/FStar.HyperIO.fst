module FStar.HyperIO

open FStar.HyperStack.ST

assume val print_string: Prims.string -> Stack unit (fun _ -> true) (fun h0 _ h1 -> h0 == h1)
