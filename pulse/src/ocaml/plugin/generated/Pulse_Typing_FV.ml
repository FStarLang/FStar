open Prims
let (contains : Pulse_Typing_Env.env -> Pulse_Syntax_Base.var -> Prims.bool)
  =
  fun g ->
    fun x ->
      FStar_Pervasives_Native.uu___is_Some (Pulse_Typing_Env.lookup g x)
let set_minus : 'a . 'a FStar_Set.set -> 'a -> 'a FStar_Set.set =
  fun s ->
    fun x ->
      FStar_Set.intersect s (FStar_Set.complement (FStar_Set.singleton x))
let (contains_r :
  FStar_Reflection_Types.env -> Pulse_Syntax_Base.var -> Prims.bool) =
  fun g ->
    fun x ->
      FStar_Pervasives_Native.uu___is_Some
        (FStar_Reflection_Typing.lookup_bvar g x)
type ('a, 'du) src_typing_freevars_t = unit