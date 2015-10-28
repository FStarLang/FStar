open AST

open FFI

let const_meta = AST.Meta ([], AST.Can_b, [], AST.Can_w)

let program = mk_let "alice_s" (mk_ffi 1 "FFI.singleton" (FFI.singleton) [  (mk_var "alice"); ] (fun x -> D_v (const_meta, V_eprins x))) (mk_let "bob_s" (mk_ffi 1 "FFI.singleton" (FFI.singleton) [  (mk_var "bob"); ] (fun x -> D_v (const_meta, V_eprins x))) (mk_let "ab" (mk_ffi 2 "FFI.union" (FFI.union) [  (mk_var "alice_s"); (mk_var "bob_s"); ] (fun x -> D_v (const_meta, V_eprins x))) (mk_let "read_fn" (mk_abs "x" (mk_ffi 1 "FFI.read_int" FFI.read_int [ E_const (C_unit ()) ] (fun x -> mk_v_opaque x slice_id compose_ids slice_id_sps))) (mk_let "mill1" (mk_abs "_15_13" (mk_let "x" (mk_aspar (mk_var "alice_s") (mk_var "read_fn")) (mk_let "y" (mk_aspar (mk_var "bob_s") (mk_var "read_fn")) (mk_let "g" (mk_abs "_15_17" (mk_ffi 2 "Prims.(>)" (Prims.(>)) [  (mk_unbox (mk_var "x")); (mk_unbox (mk_var "y")); ] (fun x -> D_v (const_meta, V_bool x)))) (mk_assec (mk_var "ab") (mk_var "g")))))) (mk_let "x" (mk_app (mk_var "mill1") (E_const (C_unit ()))) (mk_ffi 1 "FFI.print_bool" (FFI.print_bool) [  (mk_var "x"); ] (fun x -> D_v (const_meta, V_unit))))))))

