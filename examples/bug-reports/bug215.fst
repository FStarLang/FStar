module Bug215

open Comp


assume val bug: unit -> STATE2.ST2 (unit * unit)
                                   (requires (fun h -> True))
                                   (ensures (fun h1 r h2 -> True))
