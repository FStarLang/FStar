open Ffibridge
open FFI
open AST


let deal ps p shares rands deal_to = 
  let e1 = mk_const (C_eprins ps) in
  let e2 = mk_const (C_opaque ((), Obj.magic shares, T_cons ("Prims.list", [ T_sh;]))) in
  let e3 = mk_mkwire (mk_const (C_eprins (singleton p))) (mk_box (mk_const (C_eprins (singleton p))) (mk_const (C_opaque ((), Obj.magic rands, T_cons ("Prims.int", []))))) in
  let e4 = mk_const (C_prin deal_to) in
  let dv = Interpreteriface.run p "deal" T_unknown [e1; e2; e3; e4] false in
  Obj.magic (Interpreteriface.project_value_content dv)
