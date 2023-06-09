open Prims
type eqn =
  (Pulse_Syntax_Base.term * Pulse_Syntax_Base.term * Pulse_Syntax_Base.term)
type binding = (Pulse_Syntax_Base.term, eqn) FStar_Pervasives.either
type env_bindings = (Pulse_Syntax_Base.var * binding) Prims.list
type context = (Prims.string Prims.list, unit) FStar_Sealed_Inhabited.sealed
type env =
  {
  f: FStar_Reflection_Typing.fstar_top_env ;
  g: env_bindings ;
  ctxt: context }
let (__proj__Mkenv__item__f : env -> FStar_Reflection_Typing.fstar_top_env) =
  fun projectee -> match projectee with | { f; g; ctxt;_} -> f
let (__proj__Mkenv__item__g : env -> env_bindings) =
  fun projectee -> match projectee with | { f; g; ctxt;_} -> g
let (__proj__Mkenv__item__ctxt : env -> context) =
  fun projectee -> match projectee with | { f; g; ctxt;_} -> ctxt