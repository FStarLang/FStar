(*--build-config
   options:--admit_fsi FStar.OrdSet --admit_fsi FStar.OrdMap --admit_fsi Prins;
   other-files:ordset.fsi ordmap.fsi FStar.Ghost.fst prins.fsi ast.fst
--*)

module Ffibridge

open AST

val exec_ffi: nat -> 'a -> list dvalue -> 'b -> Tot dvalue

type compose_fn_wrapper =
  | Mk_c_w: ('a -> 'a -> Tot 'a) -> compose_fn_wrapper

val compose_v_opaques: #m1:v_meta -> #m2:v_meta
                       -> v1:value m1{is_V_opaque v1} -> v2:value m2{is_V_opaque v2}
		       -> Tot (dv:dvalue{D_v.meta dv = compose_opaque_meta m1 m2 /\
		                        is_V_opaque (D_v.v dv) /\
					Mk_c_w (V_opaque.compose_fn (D_v.v dv)) =
					Mk_c_w (V_opaque.compose_fn v1)})

(**********)

val nat_of_c_opaque: const -> Tot nat

val nat_of_v_opaque: #meta:v_meta -> value meta -> Tot nat

val int_list_of_v_opaque: #meta:v_meta -> value meta -> Tot (list nat)
