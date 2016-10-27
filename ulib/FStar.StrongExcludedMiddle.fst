module FStar.StrongExcludedMiddle

(* WARNING: this breaks parametricity; use with care *)
assume val strong_excluded_middle : p:prop -> GTot (b:bool{b = true <==> p})

let squash_in_prop (p:Type) : prop = squash p
