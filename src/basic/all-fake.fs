module FStar.All
type ML<'a> = 'a
let exit i = exit (Prims.to_int i)
