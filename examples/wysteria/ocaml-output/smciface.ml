open Ffibridge
open FFI
open AST


let psi_mono ps p x = 
let e1 = mk_const (C_eprins ps) in
let e2 = mk_mkwire (mk_const (C_eprins (singleton p))) (mk_box (mk_const (C_eprins (singleton p))) (mk_const (C_opaque ((), Obj.magic x, T_cons ("Prims.list", [ (T_cons ("Prims.int", []));]))))) in
let dv = Interpreteriface.run p "psi_mono" T_unknown [e1; e2] true in
Obj.magic (Interpreteriface.project_value_content dv)


let psi_opt ps p x = 
let e1 = mk_const (C_eprins ps) in
let e2 = mk_mkwire (mk_const (C_eprins (singleton p))) (mk_box (mk_const (C_eprins (singleton p))) (mk_const (C_opaque ((), Obj.magic x, T_cons ("Prims.list", [ (T_cons ("Prims.int", []));]))))) in
let dv = Interpreteriface.run p "psi_opt" T_unknown [e1; e2] true in
Obj.magic (Interpreteriface.project_value_content dv)


let psi ps p x = 
let e1 = mk_const (C_eprins ps) in
let e2 = mk_mkwire (mk_const (C_eprins (singleton p))) (mk_box (mk_const (C_eprins (singleton p))) (mk_const (C_opaque ((), Obj.magic x, T_cons ("Prims.list", [ (T_cons ("Prims.int", []));]))))) in
let dv = Interpreteriface.run p "psi" T_unknown [e1; e2] true in
Obj.magic (Interpreteriface.project_value_content dv)



