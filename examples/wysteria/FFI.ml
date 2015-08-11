open AST

open OrdSet

let exec_ffi (s:string) (l:dvalue list) = D_v ((OrdSet.empty (), Can_b), (V_const C_unit))
