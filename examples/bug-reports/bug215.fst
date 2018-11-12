module Bug215

open FStar.Relational.Comp

assume val bug: unit -> ST2 (unit * unit)
                                   (requires (fun h -> True))
                                   (ensures (fun h1 r h2 -> True))
