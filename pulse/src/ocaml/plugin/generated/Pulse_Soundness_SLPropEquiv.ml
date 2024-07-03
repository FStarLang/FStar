open Prims
let (slprop_equiv_refl_type : FStar_Reflection_Types.term) =
  let var = Prims.int_zero in
  let v = Pulse_Reflection_Util.mk_name var in
  Pulse_Reflection_Util.mk_arrow
    (Pulse_Syntax_Pure.tm_slprop, FStar_Reflection_V2_Data.Q_Explicit)
    (FStar_Reflection_Typing.close_term
       (Pulse_Reflection_Util.stt_slprop_equiv v v) var)
let (slprop_equiv_sym_type : FStar_Reflection_Types.term) =
  let var0 = Prims.int_zero in
  let v0 = Pulse_Reflection_Util.mk_name var0 in
  let var1 = Prims.int_one in
  let v1 = Pulse_Reflection_Util.mk_name var1 in
  Pulse_Reflection_Util.mk_arrow
    (Pulse_Syntax_Pure.tm_slprop, FStar_Reflection_V2_Data.Q_Implicit)
    (FStar_Reflection_Typing.close_term
       (Pulse_Reflection_Util.mk_arrow
          (Pulse_Syntax_Pure.tm_slprop, FStar_Reflection_V2_Data.Q_Implicit)
          (FStar_Reflection_Typing.close_term
             (Pulse_Reflection_Util.mk_arrow
                ((Pulse_Reflection_Util.stt_slprop_equiv v0 v1),
                  FStar_Reflection_V2_Data.Q_Explicit)
                (Pulse_Reflection_Util.stt_slprop_equiv v0 v1)) var1)) var0)
let (slprop_tm : FStar_Reflection_Types.term) =
  FStar_Reflection_V2_Builtins.pack_ln
    (FStar_Reflection_V2_Data.Tv_FVar
       (FStar_Reflection_V2_Builtins.pack_fv Pulse_Reflection_Util.slprop_lid))
let (slprop_equiv_ext_type : FStar_Reflection_Types.term) =
  let v_typ =
    FStar_Reflection_V2_Builtins.pack_ln
      (FStar_Reflection_V2_Data.Tv_FVar
         (FStar_Reflection_V2_Builtins.pack_fv
            Pulse_Reflection_Util.slprop_lid)) in
  let mk_bv index =
    FStar_Reflection_V2_Builtins.pack_ln
      (FStar_Reflection_V2_Data.Tv_BVar
         (FStar_Reflection_V2_Builtins.pack_bv
            {
              FStar_Reflection_V2_Data.index = index;
              FStar_Reflection_V2_Data.sort1 =
                (FStar_Sealed.seal Pulse_Reflection_Util.tun);
              FStar_Reflection_V2_Data.ppname1 =
                FStar_Reflection_Typing.pp_name_default
            })) in
  Pulse_Reflection_Util.mk_arrow
    (slprop_tm, FStar_Reflection_V2_Data.Q_Explicit)
    (Pulse_Reflection_Util.mk_arrow
       (slprop_tm, FStar_Reflection_V2_Data.Q_Explicit)
       (Pulse_Reflection_Util.mk_arrow
          ((Pulse_Reflection_Util.slprop_eq_tm (mk_bv Prims.int_one)
              (mk_bv Prims.int_zero)), FStar_Reflection_V2_Data.Q_Explicit)
          (Pulse_Reflection_Util.stt_slprop_equiv (mk_bv (Prims.of_int (2)))
             (mk_bv Prims.int_one))))