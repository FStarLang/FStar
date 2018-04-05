module FStar.StrongExcludedMiddle

(* WARNING: this breaks parametricity; use with care *)
assume val strong_excluded_middle : p:prop -> GTot (b:bool{b = true <==> p})
