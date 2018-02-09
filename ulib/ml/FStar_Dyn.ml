type dyn = Obj.t
let mkdyn (x:'a) : dyn = Obj.repr x
let undyn (x:dyn) : 'a = Obj.obj x
