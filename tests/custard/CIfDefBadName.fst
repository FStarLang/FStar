module CIfDefBadName

[@@CIfDef; custard_extern "9not_an_identifier"]
assume val flag : bool

let main () : FStar.Int32.t = 0l
