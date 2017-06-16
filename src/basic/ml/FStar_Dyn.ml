type dyn = | Dyn of Obj.t

let mkdyn (x:'a) : dyn =
    Dyn (Obj.repr x)

let undyn (d:dyn) : 'a =
    match d with
    | Dyn d -> Obj.obj d
