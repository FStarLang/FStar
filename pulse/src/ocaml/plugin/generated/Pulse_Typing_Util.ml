open Prims
let (check_equiv_now :
  FStar_Reflection_Types.env ->
    FStar_Tactics_NamedView.term ->
      FStar_Tactics_NamedView.term ->
        (((unit, unit, unit) FStar_Tactics_Types.equiv_token
           FStar_Pervasives_Native.option * FStar_Tactics_Types.issues),
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun tcenv ->
    fun t0 ->
      fun t1 ->
        FStar_Tactics_V2_Derived.with_policy FStar_Tactics_Types.SMTSync
          (fun uu___ -> FStar_Tactics_V2_Builtins.check_equiv tcenv t0 t1)
let (universe_of_now :
  FStar_Reflection_Types.env ->
    FStar_Tactics_NamedView.term ->
      ((FStar_Tactics_NamedView.universe FStar_Pervasives_Native.option *
         FStar_Tactics_Types.issues),
        unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun e ->
      FStar_Tactics_V2_Derived.with_policy FStar_Tactics_Types.SMTSync
        (fun uu___ -> FStar_Tactics_V2_Builtins.universe_of g e)