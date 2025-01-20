type dyn = Obj.t
[@printer fun fmt _ -> Format.pp_print_string fmt "<dyn>"]
[@@deriving show]

let dyn_to_yojson _ = `Null
let dyn_of_yojson _ = failwith "cannot readback"

let mkdyn (x:'a) : dyn =
    Obj.repr x

let undyn (d:dyn) : 'a =
    Obj.obj d
