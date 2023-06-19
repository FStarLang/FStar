open Prims
let (app0 : FStar_Reflection_Types.term -> FStar_Reflection_Types.term) =
  fun t ->
    FStar_Reflection_V2_Derived.mk_app t
      [((Pulse_Reflection_Util.bound_var Prims.int_zero),
         FStar_Reflection_V2_Data.Q_Explicit)]
let (abs_and_app0 :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun ty ->
    fun b ->
      FStar_Reflection_V2_Derived.mk_app
        (Pulse_Reflection_Util.mk_abs ty FStar_Reflection_V2_Data.Q_Explicit
           b)
        [((Pulse_Reflection_Util.bound_var Prims.int_zero),
           FStar_Reflection_V2_Data.Q_Explicit)]
let (vprop_arrow : Pulse_Syntax_Base.term -> Pulse_Syntax_Base.term) =
  fun t ->
    Pulse_Syntax_Pure.tm_arrow (Pulse_Syntax_Base.null_binder t)
      FStar_Pervasives_Native.None
      (Pulse_Syntax_Base.C_Tot Pulse_Syntax_Base.Tm_VProp)