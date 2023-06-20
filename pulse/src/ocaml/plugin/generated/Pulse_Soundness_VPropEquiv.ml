open Prims
let (vprop_equiv_refl_type : FStar_Reflection_Types.term) =
  let var = Prims.int_zero in
  let v = Pulse_Reflection_Util.mk_name var in
  let v_typ = Pulse_Elaborate_Pure.elab_term Pulse_Syntax_Base.tm_vprop in
  Pulse_Reflection_Util.mk_arrow (v_typ, FStar_Reflection_Data.Q_Explicit)
    (FStar_Reflection_Typing.close_term
       (Pulse_Reflection_Util.stt_vprop_equiv v v) var)
let (vprop_equiv_sym_type : FStar_Reflection_Types.term) =
  let var0 = Prims.int_zero in
  let v0 = Pulse_Reflection_Util.mk_name var0 in
  let var1 = Prims.int_one in
  let v1 = Pulse_Reflection_Util.mk_name var1 in
  let v_typ = Pulse_Elaborate_Pure.elab_term Pulse_Syntax_Base.tm_vprop in
  Pulse_Reflection_Util.mk_arrow (v_typ, FStar_Reflection_Data.Q_Implicit)
    (FStar_Reflection_Typing.close_term
       (Pulse_Reflection_Util.mk_arrow
          (v_typ, FStar_Reflection_Data.Q_Implicit)
          (FStar_Reflection_Typing.close_term
             (Pulse_Reflection_Util.mk_arrow
                ((Pulse_Reflection_Util.stt_vprop_equiv v0 v1),
                  FStar_Reflection_Data.Q_Explicit)
                (Pulse_Reflection_Util.stt_vprop_equiv v0 v1)) var1)) var0)
let (vprop_tm : FStar_Reflection_Types.term) =
  FStar_Reflection_Builtins.pack_ln
    (FStar_Reflection_Data.Tv_FVar
       (FStar_Reflection_Builtins.pack_fv Pulse_Reflection_Util.vprop_lid))
let (vprop_equiv_ext_type : FStar_Reflection_Types.term) =
  let v_typ =
    FStar_Reflection_Builtins.pack_ln
      (FStar_Reflection_Data.Tv_FVar
         (FStar_Reflection_Builtins.pack_fv Pulse_Reflection_Util.vprop_lid)) in
  let mk_bv index =
    FStar_Reflection_Builtins.pack_ln
      (FStar_Reflection_Data.Tv_BVar
         (FStar_Reflection_Builtins.pack_bv
            {
              FStar_Reflection_Data.bv_ppname =
                FStar_Reflection_Typing.pp_name_default;
              FStar_Reflection_Data.bv_index = index
            })) in
  Pulse_Reflection_Util.mk_arrow (vprop_tm, FStar_Reflection_Data.Q_Explicit)
    (Pulse_Reflection_Util.mk_arrow
       (vprop_tm, FStar_Reflection_Data.Q_Explicit)
       (Pulse_Reflection_Util.mk_arrow
          ((Pulse_Reflection_Util.vprop_eq_tm (mk_bv Prims.int_one)
              (mk_bv Prims.int_zero)), FStar_Reflection_Data.Q_Explicit)
          (Pulse_Reflection_Util.stt_vprop_equiv (mk_bv (Prims.of_int (2)))
             (mk_bv Prims.int_one))))