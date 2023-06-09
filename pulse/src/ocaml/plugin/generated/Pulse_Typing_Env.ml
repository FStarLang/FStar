open Prims
type bmap = (Pulse_Syntax_Base.var, Pulse_Syntax_Base.typ) FStar_Map.t
let (remove_binding :
  (Pulse_Syntax_Base.var * Pulse_Syntax_Base.typ) -> bmap -> bmap) =
  fun uu___ ->
    fun m ->
      match uu___ with
      | (x, uu___1) ->
          FStar_Map.restrict (FStar_Set.complement (FStar_Set.singleton x))
            (FStar_Map.upd m x Pulse_Syntax_Base.Tm_Unknown)
type ('bs, 'm) related = unit
type env =
  {
  f: FStar_Reflection_Typing.fstar_top_env ;
  bs: (Pulse_Syntax_Base.var * Pulse_Syntax_Base.typ) Prims.list ;
  m: bmap ;
  ctxt: Pulse_RuntimeUtils.context }
let (__proj__Mkenv__item__f : env -> FStar_Reflection_Typing.fstar_top_env) =
  fun projectee -> match projectee with | { f; bs; m; ctxt;_} -> f
let (__proj__Mkenv__item__bs :
  env -> (Pulse_Syntax_Base.var * Pulse_Syntax_Base.typ) Prims.list) =
  fun projectee -> match projectee with | { f; bs; m; ctxt;_} -> bs
let (__proj__Mkenv__item__m : env -> bmap) =
  fun projectee -> match projectee with | { f; bs; m; ctxt;_} -> m
let (__proj__Mkenv__item__ctxt : env -> Pulse_RuntimeUtils.context) =
  fun projectee -> match projectee with | { f; bs; m; ctxt;_} -> ctxt
let (fstar_env : env -> FStar_Reflection_Typing.fstar_top_env) = fun g -> g.f
type binding = (Pulse_Syntax_Base.var * Pulse_Syntax_Base.typ)
type env_bindings = binding Prims.list
let (bindings : env -> env_bindings) = fun g -> g.bs
let (as_map :
  env -> (Pulse_Syntax_Base.var, Pulse_Syntax_Base.typ) FStar_Map.t) =
  fun g -> g.m
type ('bs, 'm) is_related_to = unit
let (dom : env -> Pulse_Syntax_Base.var FStar_Set.set) =
  fun g -> FStar_Map.domain (as_map g)
let (empty_bmap : bmap) =
  FStar_Map.const_on (FStar_Set.empty ()) Pulse_Syntax_Base.Tm_Unknown
let (mk_env : FStar_Reflection_Typing.fstar_top_env -> env) =
  fun f -> { f; bs = []; m = empty_bmap; ctxt = (FStar_Sealed.seal []) }
let (push_binding :
  env -> Pulse_Syntax_Base.var -> Pulse_Syntax_Base.typ -> env) =
  fun g ->
    fun x ->
      fun t ->
        {
          f = (g.f);
          bs = ((x, t) :: (g.bs));
          m = (FStar_Map.upd g.m x t);
          ctxt = (g.ctxt)
        }
let (lookup :
  env ->
    Pulse_Syntax_Base.var ->
      Pulse_Syntax_Base.typ FStar_Pervasives_Native.option)
  =
  fun g ->
    fun x ->
      let m = as_map g in
      if FStar_Map.contains m x
      then FStar_Pervasives_Native.Some (FStar_Map.sel m x)
      else FStar_Pervasives_Native.None
let rec (max :
  (Pulse_Syntax_Base.var * Pulse_Syntax_Base.typ) Prims.list ->
    Pulse_Syntax_Base.var -> Pulse_Syntax_Base.var)
  =
  fun bs ->
    fun current ->
      match bs with
      | [] -> current
      | (x, t)::rest ->
          let current1 = if x < current then current else x in
          max rest current1
let (fresh : env -> Pulse_Syntax_Base.var) =
  fun g ->
    match g.bs with
    | [] -> Prims.int_one
    | (x, uu___)::bs_rest -> let max1 = max bs_rest x in max1 + Prims.int_one
let (contains : env -> Pulse_Syntax_Base.var -> Prims.bool) =
  fun g -> fun x -> FStar_Map.contains (as_map g) x
type ('g1, 'g2) disjoint = unit
type ('g1, 'g2, 'g3) extends_with = unit
type ('g1, 'g2) env_extends = unit
let (join : env -> env -> env) =
  fun g1 ->
    fun g2 ->
      {
        f = (g1.f);
        bs = (FStar_List_Tot_Base.op_At g1.bs g2.bs);
        m = (FStar_Map.concat g1.m g2.m);
        ctxt = (FStar_Sealed.seal [])
      }
let (push_context : env -> Prims.string -> env) =
  fun g ->
    fun ctx ->
      {
        f = (g.f);
        bs = (g.bs);
        m = (g.m);
        ctxt = (Pulse_RuntimeUtils.extend_context ctx g.ctxt)
      }
let (get_context : env -> Pulse_RuntimeUtils.context) = fun g -> g.ctxt