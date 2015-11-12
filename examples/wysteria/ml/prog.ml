open AST

open FFI

let const_meta = AST.Meta ([], AST.Can_b, [], AST.Can_w)

let program = [
("alice_s", (T_eprins), (mk_ffi 1 "FFI.singleton" (FFI.singleton) [  (mk_var "alice" (T_prin)); ] (fun x -> D_v (const_meta, V_eprins x))));
("bob_s", (T_eprins), (mk_ffi 1 "FFI.singleton" (FFI.singleton) [  (mk_var "bob" (T_prin)); ] (fun x -> D_v (const_meta, V_eprins x))));
("ab", (T_cons ("Prins.eprins", [])), (mk_ffi 2 "FFI.union" (FFI.union) [  (mk_var "alice_s" (T_eprins)); (mk_var "bob_s" (T_eprins)); ] (fun x -> D_v (const_meta, V_eprins x))));
("mill", (T_unknown), (mk_abs (mk_varname "ps" (T_eprins)) (mk_abs (mk_varname "w" (T_wire (T_cons ("Prims.int", [])))) (mk_let (mk_varname "g" (T_unknown)) (mk_abs (mk_varname "_15_12" (T_unit)) (mk_let (mk_varname "x" (T_cons ("Prims.int", []))) (mk_projwire (mk_var "alice" (T_prin)) (mk_var "w" (T_wire (T_cons ("Prims.int", []))))) (mk_let (mk_varname "y" (T_cons ("Prims.int", []))) (mk_projwire (mk_var "bob" (T_prin)) (mk_var "w" (T_wire (T_cons ("Prims.int", []))))) (mk_ffi 2 "Prims.(>)" (Prims.(>)) [  (mk_var "x" (T_cons ("Prims.int", []))); (mk_var "y" (T_cons ("Prims.int", []))); ] (fun x -> D_v (const_meta, V_bool x)))))) (mk_assec (mk_var "ab" (T_cons ("Prins.eprins", []))) (mk_var "g" (T_unknown)))))));
]

