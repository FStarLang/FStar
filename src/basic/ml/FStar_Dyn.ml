type dyn = | Dyn of Obj.t
[@printer fun fmt _ -> Format.pp_print_string fmt "<dyn>"]
[@@deriving show]

let mkdyn (x:'a) : dyn =
    Dyn (Obj.repr x)

let undyn (d:dyn) : 'a =
    match d with
    | Dyn d -> Obj.obj d
