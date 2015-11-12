open Ffibridge
open FFI
open AST

let mill ps p x = 
let e1 = mk_const (C_eprins ps) in
let e2 = mk_mkwire (mk_const (C_eprins (singleton p))) (mk_box (mk_const (C_eprins (singleton p))) (mk_const (C_opaque ((), Obj.magic x, T_cons ("Prims.int", []))))) in
let dv = Interpreteriface.run p "mill" T_unknown [e1; e2] in
Obj.magic (project_value_content dv)

