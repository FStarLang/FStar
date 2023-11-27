open Prims
let (app_typing :
  FStar_Reflection_Types.env ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.term ->
          FStar_Reflection_Types.term ->
            (unit, unit, unit) FStar_Reflection_Typing.tot_typing ->
              (unit, unit, unit) FStar_Reflection_Typing.tot_typing ->
                (unit, unit, unit) FStar_Reflection_Typing.tot_typing)
  =
  fun g ->
    fun ty1 ->
      fun ty2 -> fun f -> fun tm -> fun df -> fun dt -> Prims.magic ()