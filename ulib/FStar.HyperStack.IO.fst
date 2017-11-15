module FStar.HyperStack.IO

open FStar.HyperStack.All

assume val print_string: Prims.string ->
  All unit
    (requires (fun _ -> true))
    (ensures (fun h0 _ h1 -> h0 == h1))
