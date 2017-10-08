open Prims
type step =
  | Beta
  | Iota
  | Zeta
  | Exclude of step
  | WHNF
  | Primops
  | Eager_unfolding
  | Inlining
  | NoDeltaSteps
  | UnfoldUntil of FStar_Syntax_Syntax.delta_depth
  | UnfoldOnly of FStar_Ident.lid Prims.list
  | UnfoldTac
  | PureSubtermsWithinComputations
  | Simplify
  | EraseUniverses
  | AllowUnboundUniverses
  | Reify
  | CompressUvars
  | NoFullNorm
  | CheckNoUvars
  | Unmeta[@@deriving show]
let uu___is_Beta: step -> Prims.bool =
  fun projectee  -> match projectee with | Beta  -> true | uu____19 -> false
let uu___is_Iota: step -> Prims.bool =
  fun projectee  -> match projectee with | Iota  -> true | uu____24 -> false
let uu___is_Zeta: step -> Prims.bool =
  fun projectee  -> match projectee with | Zeta  -> true | uu____29 -> false
let uu___is_Exclude: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Exclude _0 -> true | uu____35 -> false
let __proj__Exclude__item___0: step -> step =
  fun projectee  -> match projectee with | Exclude _0 -> _0
let uu___is_WHNF: step -> Prims.bool =
  fun projectee  -> match projectee with | WHNF  -> true | uu____48 -> false
let uu___is_Primops: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____53 -> false
let uu___is_Eager_unfolding: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Eager_unfolding  -> true | uu____58 -> false
let uu___is_Inlining: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____63 -> false
let uu___is_NoDeltaSteps: step -> Prims.bool =
  fun projectee  ->
    match projectee with | NoDeltaSteps  -> true | uu____68 -> false
let uu___is_UnfoldUntil: step -> Prims.bool =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____74 -> false
let __proj__UnfoldUntil__item___0: step -> FStar_Syntax_Syntax.delta_depth =
  fun projectee  -> match projectee with | UnfoldUntil _0 -> _0
let uu___is_UnfoldOnly: step -> Prims.bool =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____90 -> false
let __proj__UnfoldOnly__item___0: step -> FStar_Ident.lid Prims.list =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0
let uu___is_UnfoldTac: step -> Prims.bool =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____109 -> false
let uu___is_PureSubtermsWithinComputations: step -> Prims.bool =
  fun projectee  ->
    match projectee with
    | PureSubtermsWithinComputations  -> true
    | uu____114 -> false
let uu___is_Simplify: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Simplify  -> true | uu____119 -> false
let uu___is_EraseUniverses: step -> Prims.bool =
  fun projectee  ->
    match projectee with | EraseUniverses  -> true | uu____124 -> false
let uu___is_AllowUnboundUniverses: step -> Prims.bool =
  fun projectee  ->
    match projectee with
    | AllowUnboundUniverses  -> true
    | uu____129 -> false
let uu___is_Reify: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____134 -> false
let uu___is_CompressUvars: step -> Prims.bool =
  fun projectee  ->
    match projectee with | CompressUvars  -> true | uu____139 -> false
let uu___is_NoFullNorm: step -> Prims.bool =
  fun projectee  ->
    match projectee with | NoFullNorm  -> true | uu____144 -> false
let uu___is_CheckNoUvars: step -> Prims.bool =
  fun projectee  ->
    match projectee with | CheckNoUvars  -> true | uu____149 -> false
let uu___is_Unmeta: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Unmeta  -> true | uu____154 -> false
type steps = step Prims.list[@@deriving show]
type closure =
  | Clos of
  ((FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
     FStar_Pervasives_Native.tuple2 Prims.list,FStar_Syntax_Syntax.term,
  ((FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
     FStar_Pervasives_Native.tuple2 Prims.list,FStar_Syntax_Syntax.term)
    FStar_Pervasives_Native.tuple2 FStar_Syntax_Syntax.memo,Prims.bool)
  FStar_Pervasives_Native.tuple4
  | Univ of FStar_Syntax_Syntax.universe
  | Dummy[@@deriving show]
let uu___is_Clos: closure -> Prims.bool =
  fun projectee  ->
    match projectee with | Clos _0 -> true | uu____236 -> false
let __proj__Clos__item___0:
  closure ->
    ((FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
       FStar_Pervasives_Native.tuple2 Prims.list,FStar_Syntax_Syntax.term,
      ((FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
         FStar_Pervasives_Native.tuple2 Prims.list,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2 FStar_Syntax_Syntax.memo,Prims.bool)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | Clos _0 -> _0
let uu___is_Univ: closure -> Prims.bool =
  fun projectee  ->
    match projectee with | Univ _0 -> true | uu____340 -> false
let __proj__Univ__item___0: closure -> FStar_Syntax_Syntax.universe =
  fun projectee  -> match projectee with | Univ _0 -> _0
let uu___is_Dummy: closure -> Prims.bool =
  fun projectee  ->
    match projectee with | Dummy  -> true | uu____353 -> false
type env =
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2 Prims.list[@@deriving show]
type branches =
  (FStar_Syntax_Syntax.pat,FStar_Syntax_Syntax.term
                             FStar_Pervasives_Native.option,FStar_Syntax_Syntax.term)
    FStar_Pervasives_Native.tuple3 Prims.list[@@deriving show]
type psc =
  {
  psc_range: FStar_Range.range;
  psc_subst: FStar_Syntax_Syntax.subst_t;}[@@deriving show]
let __proj__Mkpsc__item__psc_range: psc -> FStar_Range.range =
  fun projectee  ->
    match projectee with
    | { psc_range = __fname__psc_range; psc_subst = __fname__psc_subst;_} ->
        __fname__psc_range
let __proj__Mkpsc__item__psc_subst: psc -> FStar_Syntax_Syntax.subst_t =
  fun projectee  ->
    match projectee with
    | { psc_range = __fname__psc_range; psc_subst = __fname__psc_subst;_} ->
        __fname__psc_subst
let null_psc: psc = { psc_range = FStar_Range.dummyRange; psc_subst = [] }
let psc_range: psc -> FStar_Range.range = fun psc  -> psc.psc_range
let psc_subst: psc -> FStar_Syntax_Syntax.subst_t = fun psc  -> psc.psc_subst
type primitive_step =
  {
  name: FStar_Ident.lid;
  arity: Prims.int;
  strong_reduction_ok: Prims.bool;
  requires_binder_substitution: Prims.bool;
  interpretation:
    psc ->
      FStar_Syntax_Syntax.args ->
        FStar_Syntax_Syntax.term FStar_Pervasives_Native.option;}[@@deriving
                                                                   show]
let __proj__Mkprimitive_step__item__name: primitive_step -> FStar_Ident.lid =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        strong_reduction_ok = __fname__strong_reduction_ok;
        requires_binder_substitution = __fname__requires_binder_substitution;
        interpretation = __fname__interpretation;_} -> __fname__name
let __proj__Mkprimitive_step__item__arity: primitive_step -> Prims.int =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        strong_reduction_ok = __fname__strong_reduction_ok;
        requires_binder_substitution = __fname__requires_binder_substitution;
        interpretation = __fname__interpretation;_} -> __fname__arity
let __proj__Mkprimitive_step__item__strong_reduction_ok:
  primitive_step -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        strong_reduction_ok = __fname__strong_reduction_ok;
        requires_binder_substitution = __fname__requires_binder_substitution;
        interpretation = __fname__interpretation;_} ->
        __fname__strong_reduction_ok
let __proj__Mkprimitive_step__item__requires_binder_substitution:
  primitive_step -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        strong_reduction_ok = __fname__strong_reduction_ok;
        requires_binder_substitution = __fname__requires_binder_substitution;
        interpretation = __fname__interpretation;_} ->
        __fname__requires_binder_substitution
let __proj__Mkprimitive_step__item__interpretation:
  primitive_step ->
    psc ->
      FStar_Syntax_Syntax.args ->
        FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        strong_reduction_ok = __fname__strong_reduction_ok;
        requires_binder_substitution = __fname__requires_binder_substitution;
        interpretation = __fname__interpretation;_} ->
        __fname__interpretation
type stack_elt =
  | Arg of (closure,FStar_Syntax_Syntax.aqual,FStar_Range.range)
  FStar_Pervasives_Native.tuple3
  | UnivArgs of (FStar_Syntax_Syntax.universe Prims.list,FStar_Range.range)
  FStar_Pervasives_Native.tuple2
  | MemoLazy of (env,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
  FStar_Syntax_Syntax.memo
  | Match of (env,branches,FStar_Range.range) FStar_Pervasives_Native.tuple3
  | Abs of
  (env,FStar_Syntax_Syntax.binders,env,FStar_Syntax_Syntax.residual_comp
                                         FStar_Pervasives_Native.option,
  FStar_Range.range) FStar_Pervasives_Native.tuple5
  | App of
  (env,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Range.range)
  FStar_Pervasives_Native.tuple4
  | Meta of (FStar_Syntax_Syntax.metadata,FStar_Range.range)
  FStar_Pervasives_Native.tuple2
  | Let of
  (env,FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.letbinding,FStar_Range.range)
  FStar_Pervasives_Native.tuple4
  | Steps of
  (steps,primitive_step Prims.list,FStar_TypeChecker_Env.delta_level
                                     Prims.list)
  FStar_Pervasives_Native.tuple3
  | Debug of (FStar_Syntax_Syntax.term,FStar_Util.time)
  FStar_Pervasives_Native.tuple2[@@deriving show]
let uu___is_Arg: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Arg _0 -> true | uu____653 -> false
let __proj__Arg__item___0:
  stack_elt ->
    (closure,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Arg _0 -> _0
let uu___is_UnivArgs: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____691 -> false
let __proj__UnivArgs__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.universe Prims.list,FStar_Range.range)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | UnivArgs _0 -> _0
let uu___is_MemoLazy: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____729 -> false
let __proj__MemoLazy__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
      FStar_Syntax_Syntax.memo
  = fun projectee  -> match projectee with | MemoLazy _0 -> _0
let uu___is_Match: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____788 -> false
let __proj__Match__item___0:
  stack_elt ->
    (env,branches,FStar_Range.range) FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Match _0 -> _0
let uu___is_Abs: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____832 -> false
let __proj__Abs__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,env,FStar_Syntax_Syntax.residual_comp
                                           FStar_Pervasives_Native.option,
      FStar_Range.range) FStar_Pervasives_Native.tuple5
  = fun projectee  -> match projectee with | Abs _0 -> _0
let uu___is_App: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____890 -> false
let __proj__App__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | App _0 -> _0
let uu___is_Meta: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____932 -> false
let __proj__Meta__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.metadata,FStar_Range.range)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Meta _0 -> _0
let uu___is_Let: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____966 -> false
let __proj__Let__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.letbinding,FStar_Range.range)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | Let _0 -> _0
let uu___is_Steps: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Steps _0 -> true | uu____1014 -> false
let __proj__Steps__item___0:
  stack_elt ->
    (steps,primitive_step Prims.list,FStar_TypeChecker_Env.delta_level
                                       Prims.list)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Steps _0 -> _0
let uu___is_Debug: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____1062 -> false
let __proj__Debug__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.term,FStar_Util.time) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Debug _0 -> _0
type stack = stack_elt Prims.list[@@deriving show]
type cfg =
  {
  steps: steps;
  tcenv: FStar_TypeChecker_Env.env;
  delta_level: FStar_TypeChecker_Env.delta_level Prims.list;
  primitive_steps: primitive_step Prims.list;}[@@deriving show]
let __proj__Mkcfg__item__steps: cfg -> steps =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps;_} -> __fname__steps
let __proj__Mkcfg__item__tcenv: cfg -> FStar_TypeChecker_Env.env =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps;_} -> __fname__tcenv
let __proj__Mkcfg__item__delta_level:
  cfg -> FStar_TypeChecker_Env.delta_level Prims.list =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps;_} -> __fname__delta_level
let __proj__Mkcfg__item__primitive_steps: cfg -> primitive_step Prims.list =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps;_} ->
        __fname__primitive_steps
let dummy:
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2
  = (FStar_Pervasives_Native.None, Dummy)
let closure_to_string: closure -> Prims.string =
  fun uu___172_1172  ->
    match uu___172_1172 with
    | Clos (uu____1173,t,uu____1175,uu____1176) ->
        FStar_Syntax_Print.term_to_string t
    | Univ uu____1221 -> "Univ"
    | Dummy  -> "dummy"
let mk:
  'Auu____1228 .
    'Auu____1228 ->
      FStar_Range.range -> 'Auu____1228 FStar_Syntax_Syntax.syntax
  =
  fun t  -> fun r  -> FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None r
let set_memo:
  'Auu____1385 'Auu____1386 .
    ('Auu____1386 FStar_Pervasives_Native.option,'Auu____1385) FStar_ST.mref
      -> 'Auu____1386 -> Prims.unit
  =
  fun r  ->
    fun t  ->
      let uu____1681 = FStar_ST.op_Bang r in
      match uu____1681 with
      | FStar_Pervasives_Native.Some uu____1782 ->
          failwith "Unexpected set_memo: thunk already evaluated"
      | FStar_Pervasives_Native.None  ->
          FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some t)
let env_to_string: closure Prims.list -> Prims.string =
  fun env  ->
    let uu____1889 = FStar_List.map closure_to_string env in
    FStar_All.pipe_right uu____1889 (FStar_String.concat "; ")
let stack_elt_to_string: stack_elt -> Prims.string =
  fun uu___173_1897  ->
    match uu___173_1897 with
    | Arg (c,uu____1899,uu____1900) ->
        let uu____1901 = closure_to_string c in
        FStar_Util.format1 "Closure %s" uu____1901
    | MemoLazy uu____1902 -> "MemoLazy"
    | Abs (uu____1909,bs,uu____1911,uu____1912,uu____1913) ->
        let uu____1918 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs) in
        FStar_Util.format1 "Abs %s" uu____1918
    | UnivArgs uu____1923 -> "UnivArgs"
    | Match uu____1930 -> "Match"
    | App (uu____1937,t,uu____1939,uu____1940) ->
        let uu____1941 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "App %s" uu____1941
    | Meta (m,uu____1943) -> "Meta"
    | Let uu____1944 -> "Let"
    | Steps (uu____1953,uu____1954,uu____1955) -> "Steps"
    | Debug (t,uu____1965) ->
        let uu____1966 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "Debug %s" uu____1966
let stack_to_string: stack_elt Prims.list -> Prims.string =
  fun s  ->
    let uu____1975 = FStar_List.map stack_elt_to_string s in
    FStar_All.pipe_right uu____1975 (FStar_String.concat "; ")
let log: cfg -> (Prims.unit -> Prims.unit) -> Prims.unit =
  fun cfg  ->
    fun f  ->
      let uu____1993 =
        FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other "Norm") in
      if uu____1993 then f () else ()
let is_empty: 'Auu____1999 . 'Auu____1999 Prims.list -> Prims.bool =
  fun uu___174_2005  ->
    match uu___174_2005 with | [] -> true | uu____2008 -> false
let lookup_bvar:
  'Auu____2019 'Auu____2020 .
    ('Auu____2020,'Auu____2019) FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Syntax_Syntax.bv -> 'Auu____2019
  =
  fun env  ->
    fun x  ->
      try
        let uu____2044 = FStar_List.nth env x.FStar_Syntax_Syntax.index in
        FStar_Pervasives_Native.snd uu____2044
      with
      | uu____2057 ->
          let uu____2058 =
            let uu____2059 = FStar_Syntax_Print.db_to_string x in
            FStar_Util.format1 "Failed to find %s\n" uu____2059 in
          failwith uu____2058
let downgrade_ghost_effect_name:
  FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option =
  fun l  ->
    if FStar_Ident.lid_equals l FStar_Parser_Const.effect_Ghost_lid
    then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Pure_lid
    else
      if FStar_Ident.lid_equals l FStar_Parser_Const.effect_GTot_lid
      then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Tot_lid
      else
        if FStar_Ident.lid_equals l FStar_Parser_Const.effect_GHOST_lid
        then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_PURE_lid
        else FStar_Pervasives_Native.None
let norm_universe:
  cfg -> env -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun cfg  ->
    fun env  ->
      fun u  ->
        let norm_univs us =
          let us1 = FStar_Util.sort_with FStar_Syntax_Util.compare_univs us in
          let uu____2100 =
            FStar_List.fold_left
              (fun uu____2126  ->
                 fun u1  ->
                   match uu____2126 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____2151 = FStar_Syntax_Util.univ_kernel u1 in
                       (match uu____2151 with
                        | (k_u,n1) ->
                            let uu____2166 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u in
                            if uu____2166
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1 in
          match uu____2100 with
          | (uu____2184,u1,out) -> FStar_List.rev (u1 :: out) in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1 in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____2209 =
                   let uu____2210 = FStar_List.nth env x in
                   FStar_Pervasives_Native.snd uu____2210 in
                 match uu____2209 with
                 | Univ u3 -> aux u3
                 | Dummy  -> [u2]
                 | uu____2228 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____2237 ->
                   let uu____2238 =
                     FStar_All.pipe_right cfg.steps
                       (FStar_List.contains AllowUnboundUniverses) in
                   if uu____2238
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_unif uu____2244 when
              FStar_All.pipe_right cfg.steps
                (FStar_List.contains CheckNoUvars)
              -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____2253 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____2262 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____2269 = FStar_List.collect aux us in
                FStar_All.pipe_right uu____2269 norm_univs in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest in
                   let uu____2286 = FStar_Syntax_Util.univ_kernel u_k in
                   (match uu____2286 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____2294 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____2302 =
                                    FStar_Syntax_Util.univ_kernel u3 in
                                  match uu____2302 with
                                  | (uu____2307,m) -> n1 <= m)) in
                        if uu____2294 then rest1 else us1
                    | uu____2312 -> us1)
               | uu____2317 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____2321 = aux u3 in
              FStar_List.map (fun _0_42  -> FStar_Syntax_Syntax.U_succ _0_42)
                uu____2321 in
        let uu____2324 =
          FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses) in
        if uu____2324
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____2326 = aux u in
           match uu____2326 with
           | [] -> FStar_Syntax_Syntax.U_zero
           | (FStar_Syntax_Syntax.U_zero )::[] -> FStar_Syntax_Syntax.U_zero
           | (FStar_Syntax_Syntax.U_zero )::u1::[] -> u1
           | (FStar_Syntax_Syntax.U_zero )::us ->
               FStar_Syntax_Syntax.U_max us
           | u1::[] -> u1
           | us -> FStar_Syntax_Syntax.U_max us)
let rec closure_as_term:
  cfg -> env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun cfg  ->
    fun env  ->
      fun t  ->
        log cfg
          (fun uu____2430  ->
             let uu____2431 = FStar_Syntax_Print.tag_of_term t in
             let uu____2432 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.print2 ">>> %s Closure_as_term %s\n" uu____2431
               uu____2432);
        (match env with
         | [] when
             FStar_All.pipe_left Prims.op_Negation
               (FStar_List.contains CompressUvars cfg.steps)
             -> t
         | uu____2439 ->
             let t1 = FStar_Syntax_Subst.compress t in
             (match t1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_delayed uu____2441 ->
                  failwith "Impossible"
              | FStar_Syntax_Syntax.Tm_unknown  -> t1
              | FStar_Syntax_Syntax.Tm_constant uu____2466 -> t1
              | FStar_Syntax_Syntax.Tm_name uu____2467 -> t1
              | FStar_Syntax_Syntax.Tm_fvar uu____2468 -> t1
              | FStar_Syntax_Syntax.Tm_uvar uu____2469 ->
                  let uu____2486 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains CheckNoUvars) in
                  if uu____2486
                  then
                    let uu____2487 =
                      let uu____2488 =
                        FStar_Range.string_of_range
                          t1.FStar_Syntax_Syntax.pos in
                      let uu____2489 = FStar_Syntax_Print.term_to_string t1 in
                      FStar_Util.format2
                        "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                        uu____2488 uu____2489 in
                    failwith uu____2487
                  else t1
              | FStar_Syntax_Syntax.Tm_type u ->
                  let uu____2492 =
                    let uu____2493 = norm_universe cfg env u in
                    FStar_Syntax_Syntax.Tm_type uu____2493 in
                  mk uu____2492 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                  let uu____2500 = FStar_List.map (norm_universe cfg env) us in
                  FStar_Syntax_Syntax.mk_Tm_uinst t' uu____2500
              | FStar_Syntax_Syntax.Tm_bvar x ->
                  let uu____2502 = lookup_bvar env x in
                  (match uu____2502 with
                   | Univ uu____2505 ->
                       failwith
                         "Impossible: term variable is bound to a universe"
                   | Dummy  -> t1
                   | Clos (env1,t0,r,uu____2509) ->
                       closure_as_term cfg env1 t0)
              | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                  let head2 = closure_as_term_delayed cfg env head1 in
                  let args1 = closures_as_args_delayed cfg env args in
                  mk (FStar_Syntax_Syntax.Tm_app (head2, args1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
                  let uu____2621 = closures_as_binders_delayed cfg env bs in
                  (match uu____2621 with
                   | (bs1,env1) ->
                       let body1 = closure_as_term_delayed cfg env1 body in
                       let uu____2649 =
                         let uu____2650 =
                           let uu____2667 = close_lcomp_opt cfg env1 lopt in
                           (bs1, body1, uu____2667) in
                         FStar_Syntax_Syntax.Tm_abs uu____2650 in
                       mk uu____2649 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                  let uu____2698 = closures_as_binders_delayed cfg env bs in
                  (match uu____2698 with
                   | (bs1,env1) ->
                       let c1 = close_comp cfg env1 c in
                       mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                  let uu____2740 =
                    let uu____2751 =
                      let uu____2758 = FStar_Syntax_Syntax.mk_binder x in
                      [uu____2758] in
                    closures_as_binders_delayed cfg env uu____2751 in
                  (match uu____2740 with
                   | (x1,env1) ->
                       let phi1 = closure_as_term_delayed cfg env1 phi in
                       let uu____2776 =
                         let uu____2777 =
                           let uu____2784 =
                             let uu____2785 = FStar_List.hd x1 in
                             FStar_All.pipe_right uu____2785
                               FStar_Pervasives_Native.fst in
                           (uu____2784, phi1) in
                         FStar_Syntax_Syntax.Tm_refine uu____2777 in
                       mk uu____2776 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_ascribed (t11,(annot,tacopt),lopt) ->
                  let annot1 =
                    match annot with
                    | FStar_Util.Inl t2 ->
                        let uu____2876 = closure_as_term_delayed cfg env t2 in
                        FStar_Util.Inl uu____2876
                    | FStar_Util.Inr c ->
                        let uu____2890 = close_comp cfg env c in
                        FStar_Util.Inr uu____2890 in
                  let tacopt1 =
                    FStar_Util.map_opt tacopt
                      (closure_as_term_delayed cfg env) in
                  let uu____2906 =
                    let uu____2907 =
                      let uu____2934 = closure_as_term_delayed cfg env t11 in
                      (uu____2934, (annot1, tacopt1), lopt) in
                    FStar_Syntax_Syntax.Tm_ascribed uu____2907 in
                  mk uu____2906 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_pattern args) ->
                  let uu____2985 =
                    let uu____2986 =
                      let uu____2993 = closure_as_term_delayed cfg env t' in
                      let uu____2996 =
                        let uu____2997 =
                          FStar_All.pipe_right args
                            (FStar_List.map
                               (closures_as_args_delayed cfg env)) in
                        FStar_Syntax_Syntax.Meta_pattern uu____2997 in
                      (uu____2993, uu____2996) in
                    FStar_Syntax_Syntax.Tm_meta uu____2986 in
                  mk uu____2985 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic (m,tbody)) ->
                  let uu____3057 =
                    let uu____3058 =
                      let uu____3065 = closure_as_term_delayed cfg env t' in
                      let uu____3068 =
                        let uu____3069 =
                          let uu____3076 =
                            closure_as_term_delayed cfg env tbody in
                          (m, uu____3076) in
                        FStar_Syntax_Syntax.Meta_monadic uu____3069 in
                      (uu____3065, uu____3068) in
                    FStar_Syntax_Syntax.Tm_meta uu____3058 in
                  mk uu____3057 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody)) ->
                  let uu____3095 =
                    let uu____3096 =
                      let uu____3103 = closure_as_term_delayed cfg env t' in
                      let uu____3106 =
                        let uu____3107 =
                          let uu____3116 =
                            closure_as_term_delayed cfg env tbody in
                          (m1, m2, uu____3116) in
                        FStar_Syntax_Syntax.Meta_monadic_lift uu____3107 in
                      (uu____3103, uu____3106) in
                    FStar_Syntax_Syntax.Tm_meta uu____3096 in
                  mk uu____3095 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta (t',m) ->
                  let uu____3129 =
                    let uu____3130 =
                      let uu____3137 = closure_as_term_delayed cfg env t' in
                      (uu____3137, m) in
                    FStar_Syntax_Syntax.Tm_meta uu____3130 in
                  mk uu____3129 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                  let env0 = env in
                  let env1 =
                    FStar_List.fold_left
                      (fun env1  ->
                         fun uu____3177  ->
                           (FStar_Pervasives_Native.None, Dummy) :: env1) env
                      lb.FStar_Syntax_Syntax.lbunivs in
                  let typ =
                    closure_as_term_delayed cfg env1
                      lb.FStar_Syntax_Syntax.lbtyp in
                  let def =
                    closure_as_term cfg env1 lb.FStar_Syntax_Syntax.lbdef in
                  let uu____3198 =
                    let uu____3209 = FStar_Syntax_Syntax.is_top_level [lb] in
                    if uu____3209
                    then ((lb.FStar_Syntax_Syntax.lbname), body)
                    else
                      (let x = FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                       let uu____3228 =
                         closure_as_term cfg
                           ((FStar_Pervasives_Native.None, Dummy) :: env0)
                           body in
                       ((FStar_Util.Inl
                           (let uu___193_3242 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___193_3242.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___193_3242.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = typ
                            })), uu____3228)) in
                  (match uu____3198 with
                   | (nm,body1) ->
                       let lb1 =
                         let uu___194_3258 = lb in
                         {
                           FStar_Syntax_Syntax.lbname = nm;
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___194_3258.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = typ;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___194_3258.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef = def
                         } in
                       mk
                         (FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_let ((uu____3269,lbs),body) ->
                  let norm_one_lb env1 lb =
                    let env_univs =
                      FStar_List.fold_right
                        (fun uu____3328  ->
                           fun env2  -> (FStar_Pervasives_Native.None, Dummy)
                             :: env2) lb.FStar_Syntax_Syntax.lbunivs env1 in
                    let env2 =
                      let uu____3355 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____3355
                      then env_univs
                      else
                        FStar_List.fold_right
                          (fun uu____3375  ->
                             fun env2  ->
                               (FStar_Pervasives_Native.None, Dummy) :: env2)
                          lbs env_univs in
                    let ty =
                      closure_as_term cfg env_univs
                        lb.FStar_Syntax_Syntax.lbtyp in
                    let nm =
                      let uu____3399 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____3399
                      then lb.FStar_Syntax_Syntax.lbname
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                         FStar_All.pipe_right
                           (let uu___195_3411 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___195_3411.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___195_3411.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = ty
                            }) (fun _0_43  -> FStar_Util.Inl _0_43)) in
                    let uu___196_3412 = lb in
                    let uu____3413 =
                      closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef in
                    {
                      FStar_Syntax_Syntax.lbname = nm;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___196_3412.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = ty;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___196_3412.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = uu____3413
                    } in
                  let lbs1 =
                    FStar_All.pipe_right lbs
                      (FStar_List.map (norm_one_lb env)) in
                  let body1 =
                    let body_env =
                      FStar_List.fold_right
                        (fun uu____3443  ->
                           fun env1  -> (FStar_Pervasives_Native.None, Dummy)
                             :: env1) lbs1 env in
                    closure_as_term cfg body_env body in
                  mk (FStar_Syntax_Syntax.Tm_let ((true, lbs1), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
                  let head2 = closure_as_term cfg env head1 in
                  let norm_one_branch env1 uu____3534 =
                    match uu____3534 with
                    | (pat,w_opt,tm) ->
                        let rec norm_pat env2 p =
                          match p.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_constant uu____3589 ->
                              (p, env2)
                          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                              let uu____3610 =
                                FStar_All.pipe_right pats
                                  (FStar_List.fold_left
                                     (fun uu____3670  ->
                                        fun uu____3671  ->
                                          match (uu____3670, uu____3671) with
                                          | ((pats1,env3),(p1,b)) ->
                                              let uu____3762 =
                                                norm_pat env3 p1 in
                                              (match uu____3762 with
                                               | (p2,env4) ->
                                                   (((p2, b) :: pats1), env4)))
                                     ([], env2)) in
                              (match uu____3610 with
                               | (pats1,env3) ->
                                   ((let uu___197_3844 = p in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats1)));
                                       FStar_Syntax_Syntax.p =
                                         (uu___197_3844.FStar_Syntax_Syntax.p)
                                     }), env3))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x1 =
                                let uu___198_3863 = x in
                                let uu____3864 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___198_3863.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___198_3863.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3864
                                } in
                              ((let uu___199_3878 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___199_3878.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x1 =
                                let uu___200_3889 = x in
                                let uu____3890 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___200_3889.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___200_3889.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3890
                                } in
                              ((let uu___201_3904 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___201_3904.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                              let x1 =
                                let uu___202_3920 = x in
                                let uu____3921 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___202_3920.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___202_3920.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3921
                                } in
                              let t3 = closure_as_term cfg env2 t2 in
                              ((let uu___203_3928 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term
                                       (x1, t3));
                                  FStar_Syntax_Syntax.p =
                                    (uu___203_3928.FStar_Syntax_Syntax.p)
                                }), env2) in
                        let uu____3931 = norm_pat env1 pat in
                        (match uu____3931 with
                         | (pat1,env2) ->
                             let w_opt1 =
                               match w_opt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____3960 =
                                     closure_as_term cfg env2 w in
                                   FStar_Pervasives_Native.Some uu____3960 in
                             let tm1 = closure_as_term cfg env2 tm in
                             (pat1, w_opt1, tm1)) in
                  let uu____3966 =
                    let uu____3967 =
                      let uu____3990 =
                        FStar_All.pipe_right branches
                          (FStar_List.map (norm_one_branch env)) in
                      (head2, uu____3990) in
                    FStar_Syntax_Syntax.Tm_match uu____3967 in
                  mk uu____3966 t1.FStar_Syntax_Syntax.pos))
and closure_as_term_delayed:
  cfg ->
    env ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun cfg  ->
    fun env  ->
      fun t  ->
        match env with
        | [] when
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains CompressUvars cfg.steps)
            -> t
        | uu____4076 -> closure_as_term cfg env t
and closures_as_args_delayed:
  cfg ->
    env ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
          FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun cfg  ->
    fun env  ->
      fun args  ->
        match env with
        | [] when
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains CompressUvars cfg.steps)
            -> args
        | uu____4102 ->
            FStar_List.map
              (fun uu____4119  ->
                 match uu____4119 with
                 | (x,imp) ->
                     let uu____4138 = closure_as_term_delayed cfg env x in
                     (uu____4138, imp)) args
and closures_as_binders_delayed:
  cfg ->
    env ->
      (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
           FStar_Pervasives_Native.tuple2 Prims.list,env)
          FStar_Pervasives_Native.tuple2
  =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____4152 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____4201  ->
                  fun uu____4202  ->
                    match (uu____4201, uu____4202) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___204_4272 = b in
                          let uu____4273 =
                            closure_as_term_delayed cfg env1
                              b.FStar_Syntax_Syntax.sort in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___204_4272.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___204_4272.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____4273
                          } in
                        let env2 = dummy :: env1 in
                        (env2, ((b1, imp) :: out))) (env, [])) in
        match uu____4152 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)
and close_comp:
  cfg ->
    env ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax
  =
  fun cfg  ->
    fun env  ->
      fun c  ->
        match env with
        | [] when
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains CompressUvars cfg.steps)
            -> c
        | uu____4366 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____4379 = closure_as_term_delayed cfg env t in
                 let uu____4380 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_Total' uu____4379 uu____4380
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____4393 = closure_as_term_delayed cfg env t in
                 let uu____4394 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_GTotal' uu____4393 uu____4394
             | FStar_Syntax_Syntax.Comp c1 ->
                 let rt =
                   closure_as_term_delayed cfg env
                     c1.FStar_Syntax_Syntax.result_typ in
                 let args =
                   closures_as_args_delayed cfg env
                     c1.FStar_Syntax_Syntax.effect_args in
                 let flags =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map
                        (fun uu___175_4420  ->
                           match uu___175_4420 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____4424 =
                                 closure_as_term_delayed cfg env t in
                               FStar_Syntax_Syntax.DECREASES uu____4424
                           | f -> f)) in
                 let uu____4428 =
                   let uu___205_4429 = c1 in
                   let uu____4430 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____4430;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___205_4429.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags
                   } in
                 FStar_Syntax_Syntax.mk_Comp uu____4428)
and filter_out_lcomp_cflags:
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list
  =
  fun flags  ->
    FStar_All.pipe_right flags
      (FStar_List.filter
         (fun uu___176_4440  ->
            match uu___176_4440 with
            | FStar_Syntax_Syntax.DECREASES uu____4441 -> false
            | uu____4444 -> true))
and close_lcomp_opt:
  cfg ->
    env ->
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option
  =
  fun cfg  ->
    fun env  ->
      fun lopt  ->
        match lopt with
        | FStar_Pervasives_Native.Some rc ->
            let flags =
              FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
                (FStar_List.filter
                   (fun uu___177_4462  ->
                      match uu___177_4462 with
                      | FStar_Syntax_Syntax.DECREASES uu____4463 -> false
                      | uu____4466 -> true)) in
            let rc1 =
              let uu___206_4468 = rc in
              let uu____4469 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (closure_as_term cfg env) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___206_4468.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____4469;
                FStar_Syntax_Syntax.residual_flags = flags
              } in
            FStar_Pervasives_Native.Some rc1
        | uu____4476 -> lopt
let built_in_primitive_steps: primitive_step Prims.list =
  let const_as_tm c p = mk (FStar_Syntax_Syntax.Tm_constant c) p in
  let int_as_const p i =
    let uu____4497 =
      let uu____4498 =
        let uu____4509 = FStar_Util.string_of_int i in
        (uu____4509, FStar_Pervasives_Native.None) in
      FStar_Const.Const_int uu____4498 in
    const_as_tm uu____4497 p in
  let bool_as_const p b = const_as_tm (FStar_Const.Const_bool b) p in
  let string_as_const p b = const_as_tm (FStar_Const.Const_string (b, p)) p in
  let arg_as_int uu____4543 =
    match uu____4543 with
    | (a,uu____4551) ->
        let uu____4554 =
          let uu____4555 = FStar_Syntax_Subst.compress a in
          uu____4555.FStar_Syntax_Syntax.n in
        (match uu____4554 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
             (i,FStar_Pervasives_Native.None )) ->
             let uu____4571 = FStar_Util.int_of_string i in
             FStar_Pervasives_Native.Some uu____4571
         | uu____4572 -> FStar_Pervasives_Native.None) in
  let arg_as_bounded_int uu____4586 =
    match uu____4586 with
    | (a,uu____4598) ->
        let uu____4605 =
          let uu____4606 = FStar_Syntax_Subst.compress a in
          uu____4606.FStar_Syntax_Syntax.n in
        (match uu____4605 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.pos = uu____4616;
                FStar_Syntax_Syntax.vars = uu____4617;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,FStar_Pervasives_Native.None
                                                               ));
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____4619;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____4620;_},uu____4621)::[])
             when
             FStar_Util.ends_with
               (FStar_Ident.text_of_lid
                  (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
               "int_to_t"
             ->
             let uu____4660 =
               let uu____4665 = FStar_Util.int_of_string i in
               (fv1, uu____4665) in
             FStar_Pervasives_Native.Some uu____4660
         | uu____4670 -> FStar_Pervasives_Native.None) in
  let arg_as_bool uu____4684 =
    match uu____4684 with
    | (a,uu____4692) ->
        let uu____4695 =
          let uu____4696 = FStar_Syntax_Subst.compress a in
          uu____4696.FStar_Syntax_Syntax.n in
        (match uu____4695 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) ->
             FStar_Pervasives_Native.Some b
         | uu____4702 -> FStar_Pervasives_Native.None) in
  let arg_as_char uu____4712 =
    match uu____4712 with
    | (a,uu____4720) ->
        let uu____4723 =
          let uu____4724 = FStar_Syntax_Subst.compress a in
          uu____4724.FStar_Syntax_Syntax.n in
        (match uu____4723 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c) ->
             FStar_Pervasives_Native.Some c
         | uu____4730 -> FStar_Pervasives_Native.None) in
  let arg_as_string uu____4740 =
    match uu____4740 with
    | (a,uu____4748) ->
        let uu____4751 =
          let uu____4752 = FStar_Syntax_Subst.compress a in
          uu____4752.FStar_Syntax_Syntax.n in
        (match uu____4751 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (s,uu____4758)) -> FStar_Pervasives_Native.Some s
         | uu____4759 -> FStar_Pervasives_Native.None) in
  let arg_as_list f uu____4785 =
    match uu____4785 with
    | (a,uu____4799) ->
        let rec sequence l =
          match l with
          | [] -> FStar_Pervasives_Native.Some []
          | (FStar_Pervasives_Native.None )::uu____4828 ->
              FStar_Pervasives_Native.None
          | (FStar_Pervasives_Native.Some x)::xs ->
              let uu____4845 = sequence xs in
              (match uu____4845 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some xs' ->
                   FStar_Pervasives_Native.Some (x :: xs')) in
        let uu____4865 = FStar_Syntax_Util.list_elements a in
        (match uu____4865 with
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some elts ->
             let uu____4883 =
               FStar_List.map
                 (fun x  ->
                    let uu____4893 = FStar_Syntax_Syntax.as_arg x in
                    f uu____4893) elts in
             sequence uu____4883) in
  let lift_unary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____4931 = f a in FStar_Pervasives_Native.Some uu____4931
    | uu____4932 -> FStar_Pervasives_Native.None in
  let lift_binary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____4982 = f a0 a1 in FStar_Pervasives_Native.Some uu____4982
    | uu____4983 -> FStar_Pervasives_Native.None in
  let unary_op as_a f res args =
    let uu____5032 = FStar_List.map as_a args in
    lift_unary (f res.psc_range) uu____5032 in
  let binary_op as_a f res args =
    let uu____5088 = FStar_List.map as_a args in
    lift_binary (f res.psc_range) uu____5088 in
  let as_primitive_step uu____5112 =
    match uu____5112 with
    | (l,arity,f) ->
        {
          name = l;
          arity;
          strong_reduction_ok = true;
          requires_binder_substitution = false;
          interpretation = f
        } in
  let unary_int_op f =
    unary_op arg_as_int
      (fun r  -> fun x  -> let uu____5160 = f x in int_as_const r uu____5160) in
  let binary_int_op f =
    binary_op arg_as_int
      (fun r  ->
         fun x  ->
           fun y  -> let uu____5188 = f x y in int_as_const r uu____5188) in
  let unary_bool_op f =
    unary_op arg_as_bool
      (fun r  -> fun x  -> let uu____5209 = f x in bool_as_const r uu____5209) in
  let binary_bool_op f =
    binary_op arg_as_bool
      (fun r  ->
         fun x  ->
           fun y  -> let uu____5237 = f x y in bool_as_const r uu____5237) in
  let binary_string_op f =
    binary_op arg_as_string
      (fun r  ->
         fun x  ->
           fun y  -> let uu____5265 = f x y in string_as_const r uu____5265) in
  let list_of_string' rng s =
    let name l =
      let uu____5279 =
        let uu____5280 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            FStar_Pervasives_Native.None in
        FStar_Syntax_Syntax.Tm_fvar uu____5280 in
      mk uu____5279 rng in
    let char_t = name FStar_Parser_Const.char_lid in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng in
    let uu____5290 =
      let uu____5293 = FStar_String.list_of_string s in
      FStar_List.map charterm uu____5293 in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____5290 in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l in FStar_Syntax_Util.exp_string s in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2 in int_as_const rng r in
  let string_concat' psc args =
    match args with
    | a1::a2::[] ->
        let uu____5368 = arg_as_string a1 in
        (match uu____5368 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____5374 = arg_as_list arg_as_string a2 in
             (match uu____5374 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2 in
                  let uu____5387 = string_as_const psc.psc_range r in
                  FStar_Pervasives_Native.Some uu____5387
              | uu____5388 -> FStar_Pervasives_Native.None)
         | uu____5393 -> FStar_Pervasives_Native.None)
    | uu____5396 -> FStar_Pervasives_Native.None in
  let string_of_int1 rng i =
    let uu____5410 = FStar_Util.string_of_int i in
    string_as_const rng uu____5410 in
  let string_of_bool1 rng b =
    string_as_const rng (if b then "true" else "false") in
  let string_of_int2 rng i =
    let uu____5426 = FStar_Util.string_of_int i in
    string_as_const rng uu____5426 in
  let string_of_bool2 rng b =
    string_as_const rng (if b then "true" else "false") in
  let term_of_range r =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range r))
      FStar_Pervasives_Native.None r in
  let range_of1 uu____5456 args =
    match args with
    | uu____5468::(t,uu____5470)::[] ->
        let uu____5499 = term_of_range t.FStar_Syntax_Syntax.pos in
        FStar_Pervasives_Native.Some uu____5499
    | uu____5504 -> FStar_Pervasives_Native.None in
  let set_range_of1 uu____5526 args =
    match args with
    | uu____5536::(t,uu____5538)::(r,uu____5540)::[] ->
        let r1 = FStar_Syntax_Embeddings.unembed_range r in
        FStar_Pervasives_Native.Some
          (let uu___207_5565 = t in
           {
             FStar_Syntax_Syntax.n = (uu___207_5565.FStar_Syntax_Syntax.n);
             FStar_Syntax_Syntax.pos = r1;
             FStar_Syntax_Syntax.vars =
               (uu___207_5565.FStar_Syntax_Syntax.vars)
           })
    | uu____5566 -> FStar_Pervasives_Native.None in
  let mk_range1 uu____5586 args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____5645 =
          let uu____5666 = arg_as_string fn in
          let uu____5669 = arg_as_int from_line in
          let uu____5672 = arg_as_int from_col in
          let uu____5675 = arg_as_int to_line in
          let uu____5678 = arg_as_int to_col in
          (uu____5666, uu____5669, uu____5672, uu____5675, uu____5678) in
        (match uu____5645 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____5709 = FStar_Range.mk_pos from_l from_c in
               let uu____5710 = FStar_Range.mk_pos to_l to_c in
               FStar_Range.mk_range fn1 uu____5709 uu____5710 in
             let uu____5711 = term_of_range r in
             FStar_Pervasives_Native.Some uu____5711
         | uu____5716 -> FStar_Pervasives_Native.None)
    | uu____5737 -> FStar_Pervasives_Native.None in
  let decidable_eq neg psc args =
    let r = psc.psc_range in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r in
    match args with
    | (_typ,uu____5768)::(a1,uu____5770)::(a2,uu____5772)::[] ->
        let uu____5809 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____5809 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____5822 -> FStar_Pervasives_Native.None)
    | uu____5823 -> failwith "Unexpected number of arguments" in
  let basic_ops =
    let uu____5841 =
      let uu____5856 =
        let uu____5871 =
          let uu____5886 =
            let uu____5901 =
              let uu____5916 =
                let uu____5931 =
                  let uu____5946 =
                    let uu____5961 =
                      let uu____5976 =
                        let uu____5991 =
                          let uu____6006 =
                            let uu____6021 =
                              let uu____6036 =
                                let uu____6051 =
                                  let uu____6066 =
                                    let uu____6081 =
                                      let uu____6096 =
                                        let uu____6111 =
                                          let uu____6126 =
                                            let uu____6141 =
                                              let uu____6154 =
                                                FStar_Parser_Const.p2l
                                                  ["FStar";
                                                  "String";
                                                  "list_of_string"] in
                                              (uu____6154,
                                                (Prims.parse_int "1"),
                                                (unary_op arg_as_string
                                                   list_of_string')) in
                                            let uu____6161 =
                                              let uu____6176 =
                                                let uu____6189 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "string_of_list"] in
                                                (uu____6189,
                                                  (Prims.parse_int "1"),
                                                  (unary_op
                                                     (arg_as_list arg_as_char)
                                                     string_of_list')) in
                                              let uu____6198 =
                                                let uu____6213 =
                                                  let uu____6232 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "concat"] in
                                                  (uu____6232,
                                                    (Prims.parse_int "2"),
                                                    string_concat') in
                                                let uu____6245 =
                                                  let uu____6266 =
                                                    let uu____6287 =
                                                      FStar_Parser_Const.p2l
                                                        ["Prims"; "range_of"] in
                                                    (uu____6287,
                                                      (Prims.parse_int "2"),
                                                      range_of1) in
                                                  let uu____6302 =
                                                    let uu____6325 =
                                                      let uu____6344 =
                                                        FStar_Parser_Const.p2l
                                                          ["Prims";
                                                          "set_range_of"] in
                                                      (uu____6344,
                                                        (Prims.parse_int "3"),
                                                        set_range_of1) in
                                                    let uu____6357 =
                                                      let uu____6378 =
                                                        let uu____6397 =
                                                          FStar_Parser_Const.p2l
                                                            ["Prims";
                                                            "mk_range"] in
                                                        (uu____6397,
                                                          (Prims.parse_int
                                                             "5"), mk_range1) in
                                                      [uu____6378] in
                                                    uu____6325 :: uu____6357 in
                                                  uu____6266 :: uu____6302 in
                                                uu____6213 :: uu____6245 in
                                              uu____6176 :: uu____6198 in
                                            uu____6141 :: uu____6161 in
                                          (FStar_Parser_Const.op_notEq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq true)) ::
                                            uu____6126 in
                                        (FStar_Parser_Const.op_Eq,
                                          (Prims.parse_int "3"),
                                          (decidable_eq false)) :: uu____6111 in
                                      (FStar_Parser_Const.string_compare,
                                        (Prims.parse_int "2"),
                                        (binary_op arg_as_string
                                           string_compare'))
                                        :: uu____6096 in
                                    (FStar_Parser_Const.string_of_bool_lid,
                                      (Prims.parse_int "1"),
                                      (unary_op arg_as_bool string_of_bool2))
                                      :: uu____6081 in
                                  (FStar_Parser_Const.string_of_int_lid,
                                    (Prims.parse_int "1"),
                                    (unary_op arg_as_int string_of_int2)) ::
                                    uu____6066 in
                                (FStar_Parser_Const.strcat_lid',
                                  (Prims.parse_int "2"),
                                  (binary_string_op
                                     (fun x  -> fun y  -> Prims.strcat x y)))
                                  :: uu____6051 in
                              (FStar_Parser_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____6036 in
                            (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____6021 in
                          (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____6006 in
                        (FStar_Parser_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____5991 in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op (fun x  -> fun y  -> x mod y))) ::
                        uu____5976 in
                    (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op arg_as_int
                         (fun r  ->
                            fun x  -> fun y  -> bool_as_const r (x >= y))))
                      :: uu____5961 in
                  (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op arg_as_int
                       (fun r  -> fun x  -> fun y  -> bool_as_const r (x > y))))
                    :: uu____5946 in
                (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op arg_as_int
                     (fun r  -> fun x  -> fun y  -> bool_as_const r (x <= y))))
                  :: uu____5931 in
              (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                (binary_op arg_as_int
                   (fun r  -> fun x  -> fun y  -> bool_as_const r (x < y))))
                :: uu____5916 in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op (fun x  -> fun y  -> x / y))) :: uu____5901 in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op (fun x  -> fun y  -> x * y))) :: uu____5886 in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> x - y))) :: uu____5871 in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> x + y))) :: uu____5856 in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> - x))) :: uu____5841 in
  let bounded_arith_ops =
    let bounded_int_types =
      ["Int8";
      "UInt8";
      "Int16";
      "UInt16";
      "Int32";
      "UInt32";
      "Int64";
      "UInt64";
      "UInt128"] in
    let int_as_bounded r int_to_t1 n1 =
      let c = int_as_const r n1 in
      let int_to_t2 = FStar_Syntax_Syntax.fv_to_tm int_to_t1 in
      let uu____7002 =
        let uu____7003 =
          let uu____7004 = FStar_Syntax_Syntax.as_arg c in [uu____7004] in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____7003 in
      uu____7002 FStar_Pervasives_Native.None r in
    FStar_All.pipe_right bounded_int_types
      (FStar_List.collect
         (fun m  ->
            let uu____7039 =
              let uu____7052 = FStar_Parser_Const.p2l ["FStar"; m; "add"] in
              (uu____7052, (Prims.parse_int "2"),
                (binary_op arg_as_bounded_int
                   (fun r  ->
                      fun uu____7071  ->
                        fun uu____7072  ->
                          match (uu____7071, uu____7072) with
                          | ((int_to_t1,x),(uu____7091,y)) ->
                              int_as_bounded r int_to_t1 (x + y)))) in
            let uu____7101 =
              let uu____7116 =
                let uu____7129 = FStar_Parser_Const.p2l ["FStar"; m; "sub"] in
                (uu____7129, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____7148  ->
                          fun uu____7149  ->
                            match (uu____7148, uu____7149) with
                            | ((int_to_t1,x),(uu____7168,y)) ->
                                int_as_bounded r int_to_t1 (x - y)))) in
              let uu____7178 =
                let uu____7193 =
                  let uu____7206 = FStar_Parser_Const.p2l ["FStar"; m; "mul"] in
                  (uu____7206, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____7225  ->
                            fun uu____7226  ->
                              match (uu____7225, uu____7226) with
                              | ((int_to_t1,x),(uu____7245,y)) ->
                                  int_as_bounded r int_to_t1 (x * y)))) in
                [uu____7193] in
              uu____7116 :: uu____7178 in
            uu____7039 :: uu____7101)) in
  FStar_List.map as_primitive_step
    (FStar_List.append basic_ops bounded_arith_ops)
let equality_ops: primitive_step Prims.list =
  let interp_prop psc args =
    let r = psc.psc_range in
    match args with
    | (_typ,uu____7344)::(a1,uu____7346)::(a2,uu____7348)::[] ->
        let uu____7385 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____7385 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___208_7391 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___208_7391.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___208_7391.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___209_7395 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___209_7395.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___209_7395.FStar_Syntax_Syntax.vars)
                })
         | uu____7396 -> FStar_Pervasives_Native.None)
    | (_typ,uu____7398)::uu____7399::(a1,uu____7401)::(a2,uu____7403)::[] ->
        let uu____7452 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____7452 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___208_7458 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___208_7458.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___208_7458.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___209_7462 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___209_7462.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___209_7462.FStar_Syntax_Syntax.vars)
                })
         | uu____7463 -> FStar_Pervasives_Native.None)
    | uu____7464 -> failwith "Unexpected number of arguments" in
  let propositional_equality =
    {
      name = FStar_Parser_Const.eq2_lid;
      arity = (Prims.parse_int "3");
      strong_reduction_ok = true;
      requires_binder_substitution = false;
      interpretation = interp_prop
    } in
  let hetero_propositional_equality =
    {
      name = FStar_Parser_Const.eq3_lid;
      arity = (Prims.parse_int "4");
      strong_reduction_ok = true;
      requires_binder_substitution = false;
      interpretation = interp_prop
    } in
  [propositional_equality; hetero_propositional_equality]
let mk_psc_subst:
  cfg ->
    (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____7517  ->
           fun subst1  ->
             match uu____7517 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,memo,uu____7543)) ->
                      ((let uu____7591 =
                          FStar_Syntax_Print.binder_to_string b in
                        FStar_Util.print1
                          "++++++++++++Name in environment is %s" uu____7591);
                       (let uu____7592 = b in
                        match uu____7592 with
                        | (bv,uu____7596) ->
                            let uu____7597 =
                              let uu____7598 =
                                FStar_Syntax_Util.is_constructed_typ
                                  bv.FStar_Syntax_Syntax.sort
                                  FStar_Parser_Const.fstar_reflection_types_binder_lid in
                              Prims.op_Negation uu____7598 in
                            if uu____7597
                            then subst1
                            else
                              (let term1 = closure_as_term cfg env1 term in
                               let x =
                                 let uu____7604 =
                                   FStar_Syntax_Util.un_alien term1 in
                                 FStar_All.pipe_right uu____7604
                                   FStar_Dyn.undyn in
                               let b1 =
                                 let uu____7606 =
                                   let uu___210_7607 = bv in
                                   let uu____7608 =
                                     FStar_Syntax_Subst.subst subst1
                                       (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___210_7607.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___210_7607.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = uu____7608
                                   } in
                                 FStar_Syntax_Syntax.freshen_bv uu____7606 in
                               let b_for_x =
                                 let uu____7612 =
                                   let uu____7619 =
                                     FStar_Syntax_Syntax.bv_to_name b1 in
                                   ((FStar_Pervasives_Native.fst x),
                                     uu____7619) in
                                 FStar_Syntax_Syntax.NT uu____7612 in
                               let subst2 =
                                 FStar_List.filter
                                   (fun uu___178_7628  ->
                                      match uu___178_7628 with
                                      | FStar_Syntax_Syntax.NT
                                          (uu____7629,{
                                                        FStar_Syntax_Syntax.n
                                                          =
                                                          FStar_Syntax_Syntax.Tm_name
                                                          b';
                                                        FStar_Syntax_Syntax.pos
                                                          = uu____7631;
                                                        FStar_Syntax_Syntax.vars
                                                          = uu____7632;_})
                                          ->
                                          Prims.op_Negation
                                            (FStar_Ident.ident_equals
                                               b1.FStar_Syntax_Syntax.ppname
                                               b'.FStar_Syntax_Syntax.ppname)
                                      | uu____7637 -> true) subst1 in
                               b_for_x :: subst2)))
                  | uu____7638 -> subst1)) env []
let reduce_primops:
  'Auu____7655 .
    cfg ->
      (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____7655 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack1  ->
        fun tm  ->
          let uu____7688 =
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains Primops cfg.steps) in
          if uu____7688
          then tm
          else
            (let uu____7690 = FStar_Syntax_Util.head_and_args tm in
             match uu____7690 with
             | (head1,args) ->
                 let uu____7727 =
                   let uu____7728 = FStar_Syntax_Util.un_uinst head1 in
                   uu____7728.FStar_Syntax_Syntax.n in
                 (match uu____7727 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____7732 =
                        FStar_List.tryFind
                          (fun ps  ->
                             FStar_Syntax_Syntax.fv_eq_lid fv ps.name)
                          cfg.primitive_steps in
                      (match uu____7732 with
                       | FStar_Pervasives_Native.None  -> tm
                       | FStar_Pervasives_Native.Some prim_step ->
                           if (FStar_List.length args) < prim_step.arity
                           then tm
                           else
                             (let psc =
                                let uu____7746 =
                                  if prim_step.requires_binder_substitution
                                  then mk_psc_subst cfg env
                                  else [] in
                                {
                                  psc_range = (head1.FStar_Syntax_Syntax.pos);
                                  psc_subst = uu____7746
                                } in
                              let uu____7748 =
                                prim_step.interpretation psc args in
                              match uu____7748 with
                              | FStar_Pervasives_Native.None  -> tm
                              | FStar_Pervasives_Native.Some reduced ->
                                  reduced))
                  | uu____7752 -> tm))
let reduce_equality:
  'Auu____7761 .
    cfg ->
      (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____7761 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___211_7791 = cfg in
         {
           steps = [Primops];
           tcenv = (uu___211_7791.tcenv);
           delta_level = (uu___211_7791.delta_level);
           primitive_steps = equality_ops
         }) tm
let maybe_simplify:
  'Auu____7802 .
    cfg ->
      (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____7802 ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
            FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack1  ->
        fun tm  ->
          let steps = cfg.steps in
          let w t =
            let uu___212_7850 = t in
            {
              FStar_Syntax_Syntax.n = (uu___212_7850.FStar_Syntax_Syntax.n);
              FStar_Syntax_Syntax.pos = (tm.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___212_7850.FStar_Syntax_Syntax.vars)
            } in
          let simp_t t =
            match t.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_fvar fv when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
                -> FStar_Pervasives_Native.Some true
            | FStar_Syntax_Syntax.Tm_fvar fv when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
                -> FStar_Pervasives_Native.Some false
            | uu____7867 -> FStar_Pervasives_Native.None in
          let simplify1 arg =
            ((simp_t (FStar_Pervasives_Native.fst arg)), arg) in
          let tm1 = reduce_primops cfg env stack1 tm in
          let uu____7907 =
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains Simplify steps) in
          if uu____7907
          then tm1
          else
            (match tm1.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____7910;
                         FStar_Syntax_Syntax.vars = uu____7911;_},uu____7912);
                    FStar_Syntax_Syntax.pos = uu____7913;
                    FStar_Syntax_Syntax.vars = uu____7914;_},args)
                 ->
                 let uu____7940 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid in
                 if uu____7940
                 then
                   let uu____7941 =
                     FStar_All.pipe_right args (FStar_List.map simplify1) in
                   (match uu____7941 with
                    | (FStar_Pervasives_Native.Some (true ),uu____7996)::
                        (uu____7997,(arg,uu____7999))::[] -> arg
                    | (uu____8064,(arg,uu____8066))::(FStar_Pervasives_Native.Some
                                                      (true ),uu____8067)::[]
                        -> arg
                    | (FStar_Pervasives_Native.Some (false ),uu____8132)::uu____8133::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____8196::(FStar_Pervasives_Native.Some (false
                                   ),uu____8197)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____8260 -> tm1)
                 else
                   (let uu____8276 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid in
                    if uu____8276
                    then
                      let uu____8277 =
                        FStar_All.pipe_right args (FStar_List.map simplify1) in
                      match uu____8277 with
                      | (FStar_Pervasives_Native.Some (true ),uu____8332)::uu____8333::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____8396::(FStar_Pervasives_Native.Some (true
                                     ),uu____8397)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____8460)::
                          (uu____8461,(arg,uu____8463))::[] -> arg
                      | (uu____8528,(arg,uu____8530))::(FStar_Pervasives_Native.Some
                                                        (false ),uu____8531)::[]
                          -> arg
                      | uu____8596 -> tm1
                    else
                      (let uu____8612 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid in
                       if uu____8612
                       then
                         let uu____8613 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1) in
                         match uu____8613 with
                         | uu____8668::(FStar_Pervasives_Native.Some (true
                                        ),uu____8669)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false ),uu____8732)::uu____8733::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____8796)::
                             (uu____8797,(arg,uu____8799))::[] -> arg
                         | (uu____8864,(p,uu____8866))::(uu____8867,(q,uu____8869))::[]
                             ->
                             let uu____8934 = FStar_Syntax_Util.term_eq p q in
                             (if uu____8934
                              then w FStar_Syntax_Util.t_true
                              else tm1)
                         | uu____8936 -> tm1
                       else
                         (let uu____8952 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.not_lid in
                          if uu____8952
                          then
                            let uu____8953 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1) in
                            match uu____8953 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____9008)::[] ->
                                w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____9047)::[] ->
                                w FStar_Syntax_Util.t_true
                            | uu____9086 -> tm1
                          else
                            (let uu____9102 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.forall_lid in
                             if uu____9102
                             then
                               match args with
                               | (t,uu____9104)::[] ->
                                   let uu____9121 =
                                     let uu____9122 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____9122.FStar_Syntax_Syntax.n in
                                   (match uu____9121 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____9125::[],body,uu____9127) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____9154 -> tm1)
                                    | uu____9157 -> tm1)
                               | (uu____9158,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____9159))::
                                   (t,uu____9161)::[] ->
                                   let uu____9200 =
                                     let uu____9201 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____9201.FStar_Syntax_Syntax.n in
                                   (match uu____9200 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____9204::[],body,uu____9206) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____9233 -> tm1)
                                    | uu____9236 -> tm1)
                               | uu____9237 -> tm1
                             else
                               (let uu____9247 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.exists_lid in
                                if uu____9247
                                then
                                  match args with
                                  | (t,uu____9249)::[] ->
                                      let uu____9266 =
                                        let uu____9267 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____9267.FStar_Syntax_Syntax.n in
                                      (match uu____9266 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____9270::[],body,uu____9272)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____9299 -> tm1)
                                       | uu____9302 -> tm1)
                                  | (uu____9303,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____9304))::(t,uu____9306)::[] ->
                                      let uu____9345 =
                                        let uu____9346 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____9346.FStar_Syntax_Syntax.n in
                                      (match uu____9345 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____9349::[],body,uu____9351)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____9378 -> tm1)
                                       | uu____9381 -> tm1)
                                  | uu____9382 -> tm1
                                else reduce_equality cfg env stack1 tm1)))))
             | FStar_Syntax_Syntax.Tm_app
                 ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                    FStar_Syntax_Syntax.pos = uu____9393;
                    FStar_Syntax_Syntax.vars = uu____9394;_},args)
                 ->
                 let uu____9416 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid in
                 if uu____9416
                 then
                   let uu____9417 =
                     FStar_All.pipe_right args (FStar_List.map simplify1) in
                   (match uu____9417 with
                    | (FStar_Pervasives_Native.Some (true ),uu____9472)::
                        (uu____9473,(arg,uu____9475))::[] -> arg
                    | (uu____9540,(arg,uu____9542))::(FStar_Pervasives_Native.Some
                                                      (true ),uu____9543)::[]
                        -> arg
                    | (FStar_Pervasives_Native.Some (false ),uu____9608)::uu____9609::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____9672::(FStar_Pervasives_Native.Some (false
                                   ),uu____9673)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____9736 -> tm1)
                 else
                   (let uu____9752 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid in
                    if uu____9752
                    then
                      let uu____9753 =
                        FStar_All.pipe_right args (FStar_List.map simplify1) in
                      match uu____9753 with
                      | (FStar_Pervasives_Native.Some (true ),uu____9808)::uu____9809::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____9872::(FStar_Pervasives_Native.Some (true
                                     ),uu____9873)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____9936)::
                          (uu____9937,(arg,uu____9939))::[] -> arg
                      | (uu____10004,(arg,uu____10006))::(FStar_Pervasives_Native.Some
                                                          (false
                                                          ),uu____10007)::[]
                          -> arg
                      | uu____10072 -> tm1
                    else
                      (let uu____10088 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid in
                       if uu____10088
                       then
                         let uu____10089 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1) in
                         match uu____10089 with
                         | uu____10144::(FStar_Pervasives_Native.Some (true
                                         ),uu____10145)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____10208)::uu____10209::[] ->
                             w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____10272)::
                             (uu____10273,(arg,uu____10275))::[] -> arg
                         | (uu____10340,(p,uu____10342))::(uu____10343,
                                                           (q,uu____10345))::[]
                             ->
                             let uu____10410 = FStar_Syntax_Util.term_eq p q in
                             (if uu____10410
                              then w FStar_Syntax_Util.t_true
                              else tm1)
                         | uu____10412 -> tm1
                       else
                         (let uu____10428 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.not_lid in
                          if uu____10428
                          then
                            let uu____10429 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1) in
                            match uu____10429 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____10484)::[] ->
                                w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____10523)::[] ->
                                w FStar_Syntax_Util.t_true
                            | uu____10562 -> tm1
                          else
                            (let uu____10578 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.forall_lid in
                             if uu____10578
                             then
                               match args with
                               | (t,uu____10580)::[] ->
                                   let uu____10597 =
                                     let uu____10598 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____10598.FStar_Syntax_Syntax.n in
                                   (match uu____10597 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____10601::[],body,uu____10603) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____10630 -> tm1)
                                    | uu____10633 -> tm1)
                               | (uu____10634,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____10635))::
                                   (t,uu____10637)::[] ->
                                   let uu____10676 =
                                     let uu____10677 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____10677.FStar_Syntax_Syntax.n in
                                   (match uu____10676 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____10680::[],body,uu____10682) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____10709 -> tm1)
                                    | uu____10712 -> tm1)
                               | uu____10713 -> tm1
                             else
                               (let uu____10723 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.exists_lid in
                                if uu____10723
                                then
                                  match args with
                                  | (t,uu____10725)::[] ->
                                      let uu____10742 =
                                        let uu____10743 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____10743.FStar_Syntax_Syntax.n in
                                      (match uu____10742 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____10746::[],body,uu____10748)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____10775 -> tm1)
                                       | uu____10778 -> tm1)
                                  | (uu____10779,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____10780))::(t,uu____10782)::[] ->
                                      let uu____10821 =
                                        let uu____10822 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____10822.FStar_Syntax_Syntax.n in
                                      (match uu____10821 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____10825::[],body,uu____10827)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____10854 -> tm1)
                                       | uu____10857 -> tm1)
                                  | uu____10858 -> tm1
                                else reduce_equality cfg env stack1 tm1)))))
             | uu____10868 -> tm1)
let is_norm_request:
  'Auu____10875 .
    FStar_Syntax_Syntax.term -> 'Auu____10875 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____10888 =
        let uu____10895 =
          let uu____10896 = FStar_Syntax_Util.un_uinst hd1 in
          uu____10896.FStar_Syntax_Syntax.n in
        (uu____10895, args) in
      match uu____10888 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10902::uu____10903::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10907::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____10912::uu____10913::[])
          -> FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____10916 -> false
let tr_norm_step: FStar_Syntax_Embeddings.norm_step -> step Prims.list =
  fun uu___179_10928  ->
    match uu___179_10928 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.WHNF  -> [WHNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____10934 =
          let uu____10937 =
            let uu____10938 = FStar_List.map FStar_Ident.lid_of_str names1 in
            UnfoldOnly uu____10938 in
          [uu____10937] in
        (UnfoldUntil FStar_Syntax_Syntax.Delta_constant) :: uu____10934
let tr_norm_steps:
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list =
  fun s  -> FStar_List.concatMap tr_norm_step s
let get_norm_request:
  'Auu____10957 .
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      (FStar_Syntax_Syntax.term,'Auu____10957) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (step Prims.list,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2
  =
  fun full_norm  ->
    fun args  ->
      let parse_steps s =
        let uu____10995 =
          FStar_Syntax_Embeddings.unembed_list
            FStar_Syntax_Embeddings.unembed_norm_step s in
        FStar_All.pipe_left tr_norm_steps uu____10995 in
      match args with
      | uu____11008::(tm,uu____11010)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (tm,uu____11033)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (steps,uu____11048)::uu____11049::(tm,uu____11051)::[] ->
          let add_exclude s z =
            if Prims.op_Negation (FStar_List.contains z s)
            then (Exclude z) :: s
            else s in
          let s =
            let uu____11091 =
              let uu____11094 = full_norm steps in parse_steps uu____11094 in
            Beta :: uu____11091 in
          let s1 = add_exclude s Zeta in
          let s2 = add_exclude s1 Iota in (s2, tm)
      | uu____11103 -> failwith "Impossible"
let is_reify_head: stack_elt Prims.list -> Prims.bool =
  fun uu___180_11121  ->
    match uu___180_11121 with
    | (App
        (uu____11124,{
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____11125;
                       FStar_Syntax_Syntax.vars = uu____11126;_},uu____11127,uu____11128))::uu____11129
        -> true
    | uu____11136 -> false
let firstn:
  'Auu____11145 .
    Prims.int ->
      'Auu____11145 Prims.list ->
        ('Auu____11145 Prims.list,'Auu____11145 Prims.list)
          FStar_Pervasives_Native.tuple2
  =
  fun k  ->
    fun l  ->
      if (FStar_List.length l) < k then (l, []) else FStar_Util.first_N k l
let rec norm:
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack1  ->
        fun t  ->
          let t1 = FStar_Syntax_Subst.compress t in
          log cfg
            (fun uu____11272  ->
               let uu____11273 = FStar_Syntax_Print.tag_of_term t1 in
               let uu____11274 = FStar_Syntax_Print.term_to_string t1 in
               let uu____11275 =
                 FStar_Util.string_of_int (FStar_List.length env) in
               let uu____11282 =
                 let uu____11283 =
                   let uu____11286 = firstn (Prims.parse_int "4") stack1 in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____11286 in
                 stack_to_string uu____11283 in
               FStar_Util.print4
                 ">>> %s\nNorm %s with with %s env elements top of the stack %s \n"
                 uu____11273 uu____11274 uu____11275 uu____11282);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_delayed uu____11309 ->
               failwith "Impossible: got a delayed substitution"
           | FStar_Syntax_Syntax.Tm_uvar uu____11334 when
               FStar_All.pipe_right cfg.steps
                 (FStar_List.contains CheckNoUvars)
               ->
               let uu____11351 =
                 let uu____11352 =
                   FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                 let uu____11353 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format2
                   "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                   uu____11352 uu____11353 in
               failwith uu____11351
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_uvar uu____11354 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_constant uu____11371 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_name uu____11372 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11373;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____11374;_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11377;
                 FStar_Syntax_Syntax.fv_delta = uu____11378;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11379;
                 FStar_Syntax_Syntax.fv_delta = uu____11380;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____11381);_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((FStar_Syntax_Util.is_fstar_tactics_embed hd1) ||
                  ((FStar_Syntax_Util.is_fstar_tactics_quote hd1) &&
                     (FStar_List.contains NoDeltaSteps cfg.steps)))
                 || (FStar_Syntax_Util.is_fstar_tactics_by_tactic hd1)
               ->
               let args1 = closures_as_args_delayed cfg env args in
               let hd2 = closure_as_term cfg env hd1 in
               let t2 =
                 let uu___213_11423 = t1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd2, args1));
                   FStar_Syntax_Syntax.pos =
                     (uu___213_11423.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___213_11423.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack1 t2
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((let uu____11456 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains NoFullNorm) in
                 Prims.op_Negation uu____11456) && (is_norm_request hd1 args))
                 &&
                 (Prims.op_Negation
                    (FStar_Ident.lid_equals
                       (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                       FStar_Parser_Const.prims_lid))
               ->
               let cfg' =
                 let uu___214_11464 = cfg in
                 let uu____11465 =
                   FStar_List.filter
                     (fun uu___181_11468  ->
                        match uu___181_11468 with
                        | UnfoldOnly uu____11469 -> false
                        | NoDeltaSteps  -> false
                        | uu____11472 -> true) cfg.steps in
                 {
                   steps = uu____11465;
                   tcenv = (uu___214_11464.tcenv);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___214_11464.primitive_steps)
                 } in
               let uu____11473 = get_norm_request (norm cfg' env []) args in
               (match uu____11473 with
                | (s,tm) ->
                    let delta_level =
                      let uu____11489 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___182_11494  ->
                                match uu___182_11494 with
                                | UnfoldUntil uu____11495 -> true
                                | UnfoldOnly uu____11496 -> true
                                | uu____11499 -> false)) in
                      if uu____11489
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.Delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta] in
                    let cfg'1 =
                      let uu___215_11504 = cfg in
                      {
                        steps = s;
                        tcenv = (uu___215_11504.tcenv);
                        delta_level;
                        primitive_steps = (uu___215_11504.primitive_steps)
                      } in
                    let stack' =
                      let tail1 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack1 in
                      let uu____11515 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug cfg.tcenv)
                          (FStar_Options.Other "print_normalized_terms") in
                      if uu____11515
                      then
                        let uu____11518 =
                          let uu____11519 =
                            let uu____11524 = FStar_Util.now () in
                            (t1, uu____11524) in
                          Debug uu____11519 in
                        uu____11518 :: tail1
                      else tail1 in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.pos = uu____11526;
                  FStar_Syntax_Syntax.vars = uu____11527;_},a1::a2::rest)
               ->
               let uu____11575 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____11575 with
                | (hd1,uu____11591) ->
                    let t' =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_app (hd1, [a1]))
                        FStar_Pervasives_Native.None
                        t1.FStar_Syntax_Syntax.pos in
                    let t2 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_app (t', (a2 :: rest)))
                        FStar_Pervasives_Native.None
                        t1.FStar_Syntax_Syntax.pos in
                    norm cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect uu____11656);
                  FStar_Syntax_Syntax.pos = uu____11657;
                  FStar_Syntax_Syntax.vars = uu____11658;_},a::[])
               when
               (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify))
                 && (is_reify_head stack1)
               ->
               let uu____11690 = FStar_List.tl stack1 in
               norm cfg env uu____11690 (FStar_Pervasives_Native.fst a)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.pos = uu____11693;
                  FStar_Syntax_Syntax.vars = uu____11694;_},a::[])
               when
               FStar_All.pipe_right cfg.steps (FStar_List.contains Reify) ->
               let uu____11726 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____11726 with
                | (reify_head,uu____11742) ->
                    let a1 =
                      let uu____11764 =
                        FStar_All.pipe_left FStar_Syntax_Util.unascribe
                          (FStar_Pervasives_Native.fst a) in
                      FStar_Syntax_Subst.compress uu____11764 in
                    (match a1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_app
                         ({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_constant
                              (FStar_Const.Const_reflect uu____11767);
                            FStar_Syntax_Syntax.pos = uu____11768;
                            FStar_Syntax_Syntax.vars = uu____11769;_},a2::[])
                         ->
                         norm cfg env stack1 (FStar_Pervasives_Native.fst a2)
                     | uu____11803 ->
                         let stack2 =
                           (App
                              (env, reify_head, FStar_Pervasives_Native.None,
                                (t1.FStar_Syntax_Syntax.pos)))
                           :: stack1 in
                         norm cfg env stack2 a1))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u in
               let uu____11813 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack1 uu____11813
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____11820 =
                 FStar_All.pipe_right cfg.steps
                   (FStar_List.contains EraseUniverses) in
               if uu____11820
               then norm cfg env stack1 t'
               else
                 (let us1 =
                    let uu____11823 =
                      let uu____11830 =
                        FStar_List.map (norm_universe cfg env) us in
                      (uu____11830, (t1.FStar_Syntax_Syntax.pos)) in
                    UnivArgs uu____11823 in
                  let stack2 = us1 :: stack1 in norm cfg env stack2 t')
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let t0 = t1 in
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
                      (fun uu___183_11844  ->
                         match uu___183_11844 with
                         | FStar_TypeChecker_Env.UnfoldTac  -> false
                         | FStar_TypeChecker_Env.NoDelta  -> false
                         | FStar_TypeChecker_Env.Inlining  -> true
                         | FStar_TypeChecker_Env.Eager_unfolding_only  ->
                             true
                         | FStar_TypeChecker_Env.Unfold l ->
                             FStar_TypeChecker_Common.delta_depth_greater_than
                               f.FStar_Syntax_Syntax.fv_delta l)) in
               let should_delta1 =
                 let uu____11847 =
                   (FStar_List.mem FStar_TypeChecker_Env.UnfoldTac
                      cfg.delta_level)
                     &&
                     (((((((((FStar_Syntax_Syntax.fv_eq_lid f
                                FStar_Parser_Const.and_lid)
                               ||
                               (FStar_Syntax_Syntax.fv_eq_lid f
                                  FStar_Parser_Const.or_lid))
                              ||
                              (FStar_Syntax_Syntax.fv_eq_lid f
                                 FStar_Parser_Const.imp_lid))
                             ||
                             (FStar_Syntax_Syntax.fv_eq_lid f
                                FStar_Parser_Const.forall_lid))
                            ||
                            (FStar_Syntax_Syntax.fv_eq_lid f
                               FStar_Parser_Const.squash_lid))
                           ||
                           (FStar_Syntax_Syntax.fv_eq_lid f
                              FStar_Parser_Const.exists_lid))
                          ||
                          (FStar_Syntax_Syntax.fv_eq_lid f
                             FStar_Parser_Const.eq2_lid))
                         ||
                         (FStar_Syntax_Syntax.fv_eq_lid f
                            FStar_Parser_Const.true_lid))
                        ||
                        (FStar_Syntax_Syntax.fv_eq_lid f
                           FStar_Parser_Const.false_lid)) in
                 if uu____11847
                 then false
                 else
                   (let uu____11849 =
                      FStar_All.pipe_right cfg.steps
                        (FStar_List.tryFind
                           (fun uu___184_11856  ->
                              match uu___184_11856 with
                              | UnfoldOnly uu____11857 -> true
                              | uu____11860 -> false)) in
                    match uu____11849 with
                    | FStar_Pervasives_Native.Some (UnfoldOnly lids) ->
                        should_delta &&
                          (FStar_Util.for_some
                             (FStar_Syntax_Syntax.fv_eq_lid f) lids)
                    | uu____11864 -> should_delta) in
               (log cfg
                  (fun uu____11872  ->
                     let uu____11873 = FStar_Syntax_Print.term_to_string t1 in
                     let uu____11874 =
                       FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                     let uu____11875 =
                       FStar_Util.string_of_bool should_delta1 in
                     FStar_Util.print3 ">>> For %s (%s), should_delta = %s\n"
                       uu____11873 uu____11874 uu____11875);
                if Prims.op_Negation should_delta1
                then rebuild cfg env stack1 t1
                else
                  (let r_env =
                     let uu____11878 = FStar_Syntax_Syntax.range_of_fv f in
                     FStar_TypeChecker_Env.set_range cfg.tcenv uu____11878 in
                   let uu____11879 =
                     FStar_TypeChecker_Env.lookup_definition cfg.delta_level
                       r_env
                       (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   match uu____11879 with
                   | FStar_Pervasives_Native.None  ->
                       (log cfg
                          (fun uu____11892  ->
                             FStar_Util.print "Tm_fvar case 2\n" []);
                        rebuild cfg env stack1 t1)
                   | FStar_Pervasives_Native.Some (us,t2) ->
                       (log cfg
                          (fun uu____11903  ->
                             let uu____11904 =
                               FStar_Syntax_Print.term_to_string t0 in
                             let uu____11905 =
                               FStar_Syntax_Print.term_to_string t2 in
                             FStar_Util.print2 ">>> Unfolded %s to %s\n"
                               uu____11904 uu____11905);
                        (let t3 =
                           let uu____11907 =
                             FStar_All.pipe_right cfg.steps
                               (FStar_List.contains
                                  (UnfoldUntil
                                     FStar_Syntax_Syntax.Delta_constant)) in
                           if uu____11907
                           then t2
                           else
                             FStar_Syntax_Subst.set_use_range
                               (FStar_Ident.range_of_lid
                                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                               t2 in
                         let n1 = FStar_List.length us in
                         if n1 > (Prims.parse_int "0")
                         then
                           match stack1 with
                           | (UnivArgs (us',uu____11917))::stack2 ->
                               let env1 =
                                 FStar_All.pipe_right us'
                                   (FStar_List.fold_left
                                      (fun env1  ->
                                         fun u  ->
                                           (FStar_Pervasives_Native.None,
                                             (Univ u))
                                           :: env1) env) in
                               norm cfg env1 stack2 t3
                           | uu____11972 when
                               FStar_All.pipe_right cfg.steps
                                 (FStar_List.contains EraseUniverses)
                               -> norm cfg env stack1 t3
                           | uu____11973 ->
                               let uu____11974 =
                                 let uu____11975 =
                                   FStar_Syntax_Print.lid_to_string
                                     (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                 FStar_Util.format1
                                   "Impossible: missing universe instantiation on %s"
                                   uu____11975 in
                               failwith uu____11974
                         else norm cfg env stack1 t3))))
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____11978 = lookup_bvar env x in
               (match uu____11978 with
                | Univ uu____11981 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (Prims.op_Negation
                           (FStar_List.contains (Exclude Zeta) cfg.steps))
                    then
                      let uu____12030 = FStar_ST.op_Bang r in
                      (match uu____12030 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____12167  ->
                                 let uu____12168 =
                                   FStar_Syntax_Print.term_to_string t1 in
                                 let uu____12169 =
                                   FStar_Syntax_Print.term_to_string t' in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____12168
                                   uu____12169);
                            (let uu____12170 =
                               let uu____12171 =
                                 FStar_Syntax_Subst.compress t' in
                               uu____12171.FStar_Syntax_Syntax.n in
                             match uu____12170 with
                             | FStar_Syntax_Syntax.Tm_abs uu____12174 ->
                                 norm cfg env2 stack1 t'
                             | uu____12191 -> rebuild cfg env2 stack1 t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack1) t0)
                    else norm cfg env1 stack1 t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack1 with
                | (UnivArgs uu____12249)::uu____12250 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____12259)::uu____12260 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____12270,uu____12271))::stack_rest ->
                    (match c with
                     | Univ uu____12275 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____12284 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (log cfg
                                 (fun uu____12305  ->
                                    let uu____12306 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____12306);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (log cfg
                                 (fun uu____12346  ->
                                    let uu____12347 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____12347);
                               (let body1 =
                                  mk
                                    (FStar_Syntax_Syntax.Tm_abs
                                       (tl1, body, lopt))
                                    t1.FStar_Syntax_Syntax.pos in
                                norm cfg
                                  (((FStar_Pervasives_Native.Some b), c) ::
                                  env) stack_rest body1))))
                | (Steps (s,ps,dl))::stack2 ->
                    norm
                      (let uu___216_12397 = cfg in
                       {
                         steps = s;
                         tcenv = (uu___216_12397.tcenv);
                         delta_level = dl;
                         primitive_steps = ps
                       }) env stack2 t1
                | (MemoLazy r)::stack2 ->
                    (set_memo r (env, t1);
                     log cfg
                       (fun uu____12482  ->
                          let uu____12483 =
                            FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 "\tSet memo %s\n" uu____12483);
                     norm cfg env stack2 t1)
                | (Debug uu____12484)::uu____12485 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____12492 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12492
                    else
                      (let uu____12494 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12494 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12536  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12564 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12564
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12574 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12574)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___217_12579 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___217_12579.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___217_12579.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12580 -> lopt in
                           (log cfg
                              (fun uu____12586  ->
                                 let uu____12587 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12587);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___218_12600 = cfg in
                               let uu____12601 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___218_12600.steps);
                                 tcenv = (uu___218_12600.tcenv);
                                 delta_level = (uu___218_12600.delta_level);
                                 primitive_steps = uu____12601
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Meta uu____12616)::uu____12617 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____12624 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12624
                    else
                      (let uu____12626 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12626 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12668  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12696 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12696
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12706 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12706)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___217_12711 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___217_12711.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___217_12711.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12712 -> lopt in
                           (log cfg
                              (fun uu____12718  ->
                                 let uu____12719 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12719);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___218_12732 = cfg in
                               let uu____12733 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___218_12732.steps);
                                 tcenv = (uu___218_12732.tcenv);
                                 delta_level = (uu___218_12732.delta_level);
                                 primitive_steps = uu____12733
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Let uu____12748)::uu____12749 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____12760 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12760
                    else
                      (let uu____12762 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12762 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12804  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12832 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12832
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12842 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12842)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___217_12847 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___217_12847.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___217_12847.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12848 -> lopt in
                           (log cfg
                              (fun uu____12854  ->
                                 let uu____12855 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12855);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___218_12868 = cfg in
                               let uu____12869 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___218_12868.steps);
                                 tcenv = (uu___218_12868.tcenv);
                                 delta_level = (uu___218_12868.delta_level);
                                 primitive_steps = uu____12869
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (App uu____12884)::uu____12885 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____12896 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12896
                    else
                      (let uu____12898 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12898 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12940  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12968 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12968
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12978 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12978)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___217_12983 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___217_12983.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___217_12983.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12984 -> lopt in
                           (log cfg
                              (fun uu____12990  ->
                                 let uu____12991 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12991);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___218_13004 = cfg in
                               let uu____13005 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___218_13004.steps);
                                 tcenv = (uu___218_13004.tcenv);
                                 delta_level = (uu___218_13004.delta_level);
                                 primitive_steps = uu____13005
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Abs uu____13020)::uu____13021 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____13036 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____13036
                    else
                      (let uu____13038 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____13038 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13080  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____13108 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____13108
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____13118 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____13118)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___217_13123 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___217_13123.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___217_13123.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13124 -> lopt in
                           (log cfg
                              (fun uu____13130  ->
                                 let uu____13131 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13131);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___218_13144 = cfg in
                               let uu____13145 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___218_13144.steps);
                                 tcenv = (uu___218_13144.tcenv);
                                 delta_level = (uu___218_13144.delta_level);
                                 primitive_steps = uu____13145
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | [] ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____13160 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____13160
                    else
                      (let uu____13162 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____13162 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13204  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____13232 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____13232
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____13242 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____13242)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___217_13247 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___217_13247.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___217_13247.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13248 -> lopt in
                           (log cfg
                              (fun uu____13254  ->
                                 let uu____13255 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13255);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___218_13268 = cfg in
                               let uu____13269 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___218_13268.steps);
                                 tcenv = (uu___218_13268.tcenv);
                                 delta_level = (uu___218_13268.delta_level);
                                 primitive_steps = uu____13269
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1))))
           | FStar_Syntax_Syntax.Tm_app (head1,args) ->
               let stack2 =
                 FStar_All.pipe_right stack1
                   (FStar_List.fold_right
                      (fun uu____13322  ->
                         fun stack2  ->
                           match uu____13322 with
                           | (a,aq) ->
                               let uu____13334 =
                                 let uu____13335 =
                                   let uu____13342 =
                                     let uu____13343 =
                                       let uu____13374 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None in
                                       (env, a, uu____13374, false) in
                                     Clos uu____13343 in
                                   (uu____13342, aq,
                                     (t1.FStar_Syntax_Syntax.pos)) in
                                 Arg uu____13335 in
                               uu____13334 :: stack2) args) in
               (log cfg
                  (fun uu____13450  ->
                     let uu____13451 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args) in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____13451);
                norm cfg env stack2 head1)
           | FStar_Syntax_Syntax.Tm_refine (x,f) ->
               if FStar_List.contains WHNF cfg.steps
               then
                 (match (env, stack1) with
                  | ([],[]) ->
                      let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                      let t2 =
                        mk
                          (FStar_Syntax_Syntax.Tm_refine
                             ((let uu___219_13487 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___219_13487.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___219_13487.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2
                  | uu____13488 ->
                      let uu____13493 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____13493)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                  let uu____13496 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f in
                  match uu____13496 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1 in
                      let t2 =
                        let uu____13527 =
                          let uu____13528 =
                            let uu____13535 =
                              FStar_Syntax_Subst.close closing f2 in
                            ((let uu___220_13537 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___220_13537.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___220_13537.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____13535) in
                          FStar_Syntax_Syntax.Tm_refine uu____13528 in
                        mk uu____13527 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if FStar_List.contains WHNF cfg.steps
               then
                 let uu____13556 = closure_as_term cfg env t1 in
                 rebuild cfg env stack1 uu____13556
               else
                 (let uu____13558 = FStar_Syntax_Subst.open_comp bs c in
                  match uu____13558 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____13566 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____13590  -> dummy :: env1) env) in
                        norm_comp cfg uu____13566 c1 in
                      let t2 =
                        let uu____13612 = norm_binders cfg env bs1 in
                        FStar_Syntax_Util.arrow uu____13612 c2 in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack1 with
                | (Match uu____13671)::uu____13672 -> norm cfg env stack1 t11
                | (Arg uu____13681)::uu____13682 -> norm cfg env stack1 t11
                | (App
                    (uu____13691,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____13692;
                                   FStar_Syntax_Syntax.vars = uu____13693;_},uu____13694,uu____13695))::uu____13696
                    -> norm cfg env stack1 t11
                | (MemoLazy uu____13703)::uu____13704 ->
                    norm cfg env stack1 t11
                | uu____13713 ->
                    let t12 = norm cfg env [] t11 in
                    (log cfg
                       (fun uu____13717  ->
                          FStar_Util.print_string
                            "+++ Normalizing ascription \n");
                     (let tc1 =
                        match tc with
                        | FStar_Util.Inl t2 ->
                            let uu____13734 = norm cfg env [] t2 in
                            FStar_Util.Inl uu____13734
                        | FStar_Util.Inr c ->
                            let uu____13742 = norm_comp cfg env c in
                            FStar_Util.Inr uu____13742 in
                      let tacopt1 =
                        FStar_Util.map_opt tacopt (norm cfg env []) in
                      let uu____13748 =
                        let uu____13749 =
                          let uu____13750 =
                            let uu____13777 = FStar_Syntax_Util.unascribe t12 in
                            (uu____13777, (tc1, tacopt1), l) in
                          FStar_Syntax_Syntax.Tm_ascribed uu____13750 in
                        mk uu____13749 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 uu____13748)))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack2 =
                 (Match (env, branches, (t1.FStar_Syntax_Syntax.pos))) ::
                 stack1 in
               norm cfg env stack2 head1
           | FStar_Syntax_Syntax.Tm_let
               ((uu____13853,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____13854;
                               FStar_Syntax_Syntax.lbunivs = uu____13855;
                               FStar_Syntax_Syntax.lbtyp = uu____13856;
                               FStar_Syntax_Syntax.lbeff = uu____13857;
                               FStar_Syntax_Syntax.lbdef = uu____13858;_}::uu____13859),uu____13860)
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff in
               let uu____13896 =
                 (let uu____13899 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoDeltaSteps) in
                  Prims.op_Negation uu____13899) &&
                   ((FStar_Syntax_Util.is_pure_effect n1) ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (let uu____13901 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations) in
                          Prims.op_Negation uu____13901))) in
               if uu____13896
               then
                 let binder =
                   let uu____13903 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                   FStar_Syntax_Syntax.mk_binder uu____13903 in
                 let env1 =
                   let uu____13913 =
                     let uu____13920 =
                       let uu____13921 =
                         let uu____13952 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____13952,
                           false) in
                       Clos uu____13921 in
                     ((FStar_Pervasives_Native.Some binder), uu____13920) in
                   uu____13913 :: env in
                 norm cfg env1 stack1 body
               else
                 (let uu____14036 =
                    let uu____14041 =
                      let uu____14042 =
                        let uu____14043 =
                          FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname
                            FStar_Util.left in
                        FStar_All.pipe_right uu____14043
                          FStar_Syntax_Syntax.mk_binder in
                      [uu____14042] in
                    FStar_Syntax_Subst.open_term uu____14041 body in
                  match uu____14036 with
                  | (bs,body1) ->
                      let ty = norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                      let lbname =
                        let x =
                          let uu____14057 = FStar_List.hd bs in
                          FStar_Pervasives_Native.fst uu____14057 in
                        FStar_Util.Inl
                          (let uu___221_14067 = x in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___221_14067.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___221_14067.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = ty
                           }) in
                      let lb1 =
                        let uu___222_14069 = lb in
                        let uu____14070 =
                          norm cfg env [] lb.FStar_Syntax_Syntax.lbdef in
                        {
                          FStar_Syntax_Syntax.lbname = lbname;
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___222_14069.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = ty;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___222_14069.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____14070
                        } in
                      let env' =
                        FStar_All.pipe_right bs
                          (FStar_List.fold_left
                             (fun env1  -> fun uu____14105  -> dummy :: env1)
                             env) in
                      norm cfg env'
                        ((Let (env, bs, lb1, (t1.FStar_Syntax_Syntax.pos)))
                        :: stack1) body1)
           | FStar_Syntax_Syntax.Tm_let ((true ,lbs),body) when
               (FStar_List.contains CompressUvars cfg.steps) ||
                 ((FStar_List.contains (Exclude Zeta) cfg.steps) &&
                    (FStar_List.contains PureSubtermsWithinComputations
                       cfg.steps))
               ->
               let uu____14140 = FStar_Syntax_Subst.open_let_rec lbs body in
               (match uu____14140 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                           let lbname =
                             let uu____14176 =
                               let uu___223_14177 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___223_14177.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___223_14177.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               } in
                             FStar_Util.Inl uu____14176 in
                           let uu____14178 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef in
                           match uu____14178 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs in
                               let env1 =
                                 let uu____14204 =
                                   FStar_List.map (fun uu____14220  -> dummy)
                                     lbs1 in
                                 let uu____14221 =
                                   let uu____14230 =
                                     FStar_List.map
                                       (fun uu____14250  -> dummy) xs1 in
                                   FStar_List.append uu____14230 env in
                                 FStar_List.append uu____14204 uu____14221 in
                               let def_body1 = norm cfg env1 [] def_body in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____14274 =
                                       let uu___224_14275 = rc in
                                       let uu____14276 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 []) in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___224_14275.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____14276;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___224_14275.FStar_Syntax_Syntax.residual_flags)
                                       } in
                                     FStar_Pervasives_Native.Some uu____14274
                                 | uu____14283 -> lopt in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1 in
                               let uu___225_14287 = lb in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___225_14287.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___225_14287.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def
                               }) lbs1 in
                    let env' =
                      let uu____14297 =
                        FStar_List.map (fun uu____14313  -> dummy) lbs2 in
                      FStar_List.append uu____14297 env in
                    let body2 = norm cfg env' [] body1 in
                    let uu____14321 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2 in
                    (match uu____14321 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___226_14337 = t1 in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___226_14337.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___226_14337.FStar_Syntax_Syntax.vars)
                           } in
                         rebuild cfg env stack1 t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let uu____14364 = closure_as_term cfg env t1 in
               rebuild cfg env stack1 uu____14364
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____14383 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____14459  ->
                        match uu____14459 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___227_14580 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___227_14580.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___227_14580.FStar_Syntax_Syntax.sort)
                              } in
                            let f_i = FStar_Syntax_Syntax.bv_to_tm bv in
                            let fix_f_i =
                              mk (FStar_Syntax_Syntax.Tm_let (lbs, f_i))
                                t1.FStar_Syntax_Syntax.pos in
                            let memo =
                              FStar_Util.mk_ref FStar_Pervasives_Native.None in
                            let rec_env1 =
                              (FStar_Pervasives_Native.None,
                                (Clos (env, fix_f_i, memo, true)))
                              :: rec_env in
                            (rec_env1, (memo :: memos),
                              (i + (Prims.parse_int "1"))))
                   (FStar_Pervasives_Native.snd lbs)
                   (env, [], (Prims.parse_int "0")) in
               (match uu____14383 with
                | (rec_env,memos,uu____14777) ->
                    let uu____14830 =
                      FStar_List.map2
                        (fun lb  ->
                           fun memo  ->
                             FStar_ST.op_Colon_Equals memo
                               (FStar_Pervasives_Native.Some
                                  (rec_env, (lb.FStar_Syntax_Syntax.lbdef))))
                        (FStar_Pervasives_Native.snd lbs) memos in
                    let body_env =
                      FStar_List.fold_right
                        (fun lb  ->
                           fun env1  ->
                             let uu____15361 =
                               let uu____15368 =
                                 let uu____15369 =
                                   let uu____15400 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____15400, false) in
                                 Clos uu____15369 in
                               (FStar_Pervasives_Native.None, uu____15368) in
                             uu____15361 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env in
                    norm cfg body_env stack1 body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (match m with
                | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                    let should_reify =
                      match stack1 with
                      | (App
                          (uu____15506,{
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_constant
                                           (FStar_Const.Const_reify );
                                         FStar_Syntax_Syntax.pos =
                                           uu____15507;
                                         FStar_Syntax_Syntax.vars =
                                           uu____15508;_},uu____15509,uu____15510))::uu____15511
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____15518 -> false in
                    if Prims.op_Negation should_reify
                    then
                      let t3 = norm cfg env [] t2 in
                      let stack2 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack1 in
                      let cfg1 =
                        let uu____15528 =
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains
                               PureSubtermsWithinComputations) in
                        if uu____15528
                        then
                          let uu___228_15529 = cfg in
                          {
                            steps =
                              [PureSubtermsWithinComputations;
                              Primops;
                              AllowUnboundUniverses;
                              EraseUniverses;
                              Exclude Zeta;
                              NoDeltaSteps];
                            tcenv = (uu___228_15529.tcenv);
                            delta_level =
                              [FStar_TypeChecker_Env.Inlining;
                              FStar_TypeChecker_Env.Eager_unfolding_only];
                            primitive_steps =
                              (uu___228_15529.primitive_steps)
                          }
                        else
                          (let uu___229_15531 = cfg in
                           {
                             steps =
                               (FStar_List.append [Exclude Zeta] cfg.steps);
                             tcenv = (uu___229_15531.tcenv);
                             delta_level = (uu___229_15531.delta_level);
                             primitive_steps =
                               (uu___229_15531.primitive_steps)
                           }) in
                      norm cfg1 env
                        ((Meta
                            ((FStar_Syntax_Syntax.Meta_monadic (m1, t3)),
                              (t3.FStar_Syntax_Syntax.pos))) :: stack2) head1
                    else
                      (let uu____15533 =
                         let uu____15534 = FStar_Syntax_Subst.compress head1 in
                         uu____15534.FStar_Syntax_Syntax.n in
                       match uu____15533 with
                       | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____15552 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____15552 with
                            | (uu____15553,bind_repr) ->
                                (match lb.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr uu____15559 ->
                                     failwith
                                       "Cannot reify a top-level let binding"
                                 | FStar_Util.Inl x ->
                                     let is_return e =
                                       let uu____15567 =
                                         let uu____15568 =
                                           FStar_Syntax_Subst.compress e in
                                         uu____15568.FStar_Syntax_Syntax.n in
                                       match uu____15567 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e1,FStar_Syntax_Syntax.Meta_monadic
                                            (uu____15574,uu____15575))
                                           ->
                                           let uu____15584 =
                                             let uu____15585 =
                                               FStar_Syntax_Subst.compress e1 in
                                             uu____15585.FStar_Syntax_Syntax.n in
                                           (match uu____15584 with
                                            | FStar_Syntax_Syntax.Tm_meta
                                                (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                                 (uu____15591,msrc,uu____15593))
                                                when
                                                FStar_Syntax_Util.is_pure_effect
                                                  msrc
                                                ->
                                                let uu____15602 =
                                                  FStar_Syntax_Subst.compress
                                                    e2 in
                                                FStar_Pervasives_Native.Some
                                                  uu____15602
                                            | uu____15603 ->
                                                FStar_Pervasives_Native.None)
                                       | uu____15604 ->
                                           FStar_Pervasives_Native.None in
                                     let uu____15605 =
                                       is_return lb.FStar_Syntax_Syntax.lbdef in
                                     (match uu____15605 with
                                      | FStar_Pervasives_Native.Some e ->
                                          let lb1 =
                                            let uu___230_15610 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (uu___230_15610.FStar_Syntax_Syntax.lbname);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___230_15610.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___230_15610.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                FStar_Parser_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.lbdef = e
                                            } in
                                          let uu____15611 =
                                            FStar_List.tl stack1 in
                                          let uu____15612 =
                                            let uu____15613 =
                                              let uu____15616 =
                                                let uu____15617 =
                                                  let uu____15630 =
                                                    FStar_Syntax_Util.mk_reify
                                                      body in
                                                  ((false, [lb1]),
                                                    uu____15630) in
                                                FStar_Syntax_Syntax.Tm_let
                                                  uu____15617 in
                                              FStar_Syntax_Syntax.mk
                                                uu____15616 in
                                            uu____15613
                                              FStar_Pervasives_Native.None
                                              head1.FStar_Syntax_Syntax.pos in
                                          norm cfg env uu____15611
                                            uu____15612
                                      | FStar_Pervasives_Native.None  ->
                                          let uu____15646 =
                                            let uu____15647 = is_return body in
                                            match uu____15647 with
                                            | FStar_Pervasives_Native.Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_bvar
                                                    y;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____15651;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____15652;_}
                                                ->
                                                FStar_Syntax_Syntax.bv_eq x y
                                            | uu____15657 -> false in
                                          if uu____15646
                                          then
                                            norm cfg env stack1
                                              lb.FStar_Syntax_Syntax.lbdef
                                          else
                                            (let head2 =
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Util.mk_reify
                                                 lb.FStar_Syntax_Syntax.lbdef in
                                             let body1 =
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Util.mk_reify
                                                 body in
                                             let body_rc =
                                               {
                                                 FStar_Syntax_Syntax.residual_effect
                                                   = m1;
                                                 FStar_Syntax_Syntax.residual_typ
                                                   =
                                                   (FStar_Pervasives_Native.Some
                                                      t2);
                                                 FStar_Syntax_Syntax.residual_flags
                                                   = []
                                               } in
                                             let body2 =
                                               let uu____15681 =
                                                 let uu____15684 =
                                                   let uu____15685 =
                                                     let uu____15702 =
                                                       let uu____15705 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x in
                                                       [uu____15705] in
                                                     (uu____15702, body1,
                                                       (FStar_Pervasives_Native.Some
                                                          body_rc)) in
                                                   FStar_Syntax_Syntax.Tm_abs
                                                     uu____15685 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____15684 in
                                               uu____15681
                                                 FStar_Pervasives_Native.None
                                                 body1.FStar_Syntax_Syntax.pos in
                                             let close1 =
                                               closure_as_term cfg env in
                                             let bind_inst =
                                               let uu____15721 =
                                                 let uu____15722 =
                                                   FStar_Syntax_Subst.compress
                                                     bind_repr in
                                                 uu____15722.FStar_Syntax_Syntax.n in
                                               match uu____15721 with
                                               | FStar_Syntax_Syntax.Tm_uinst
                                                   (bind1,uu____15728::uu____15729::[])
                                                   ->
                                                   let uu____15736 =
                                                     let uu____15739 =
                                                       let uu____15740 =
                                                         let uu____15747 =
                                                           let uu____15750 =
                                                             let uu____15751
                                                               =
                                                               close1
                                                                 lb.FStar_Syntax_Syntax.lbtyp in
                                                             (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                               cfg.tcenv
                                                               uu____15751 in
                                                           let uu____15752 =
                                                             let uu____15755
                                                               =
                                                               let uu____15756
                                                                 = close1 t2 in
                                                               (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                 cfg.tcenv
                                                                 uu____15756 in
                                                             [uu____15755] in
                                                           uu____15750 ::
                                                             uu____15752 in
                                                         (bind1, uu____15747) in
                                                       FStar_Syntax_Syntax.Tm_uinst
                                                         uu____15740 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____15739 in
                                                   uu____15736
                                                     FStar_Pervasives_Native.None
                                                     t2.FStar_Syntax_Syntax.pos
                                               | uu____15764 ->
                                                   failwith
                                                     "NIY : Reification of indexed effects" in
                                             let reified =
                                               let uu____15770 =
                                                 let uu____15773 =
                                                   let uu____15774 =
                                                     let uu____15789 =
                                                       let uu____15792 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           lb.FStar_Syntax_Syntax.lbtyp in
                                                       let uu____15793 =
                                                         let uu____15796 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             t2 in
                                                         let uu____15797 =
                                                           let uu____15800 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               FStar_Syntax_Syntax.tun in
                                                           let uu____15801 =
                                                             let uu____15804
                                                               =
                                                               FStar_Syntax_Syntax.as_arg
                                                                 head2 in
                                                             let uu____15805
                                                               =
                                                               let uu____15808
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   FStar_Syntax_Syntax.tun in
                                                               let uu____15809
                                                                 =
                                                                 let uu____15812
                                                                   =
                                                                   FStar_Syntax_Syntax.as_arg
                                                                    body2 in
                                                                 [uu____15812] in
                                                               uu____15808 ::
                                                                 uu____15809 in
                                                             uu____15804 ::
                                                               uu____15805 in
                                                           uu____15800 ::
                                                             uu____15801 in
                                                         uu____15796 ::
                                                           uu____15797 in
                                                       uu____15792 ::
                                                         uu____15793 in
                                                     (bind_inst, uu____15789) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____15774 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____15773 in
                                               uu____15770
                                                 FStar_Pervasives_Native.None
                                                 t2.FStar_Syntax_Syntax.pos in
                                             let uu____15820 =
                                               FStar_List.tl stack1 in
                                             norm cfg env uu____15820 reified))))
                       | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____15844 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____15844 with
                            | (uu____15845,bind_repr) ->
                                let maybe_unfold_action head2 =
                                  let maybe_extract_fv t3 =
                                    let t4 =
                                      let uu____15874 =
                                        let uu____15875 =
                                          FStar_Syntax_Subst.compress t3 in
                                        uu____15875.FStar_Syntax_Syntax.n in
                                      match uu____15874 with
                                      | FStar_Syntax_Syntax.Tm_uinst
                                          (t4,uu____15881) -> t4
                                      | uu____15886 -> head2 in
                                    let uu____15887 =
                                      let uu____15888 =
                                        FStar_Syntax_Subst.compress t4 in
                                      uu____15888.FStar_Syntax_Syntax.n in
                                    match uu____15887 with
                                    | FStar_Syntax_Syntax.Tm_fvar x ->
                                        FStar_Pervasives_Native.Some x
                                    | uu____15894 ->
                                        FStar_Pervasives_Native.None in
                                  let uu____15895 = maybe_extract_fv head2 in
                                  match uu____15895 with
                                  | FStar_Pervasives_Native.Some x when
                                      let uu____15905 =
                                        FStar_Syntax_Syntax.lid_of_fv x in
                                      FStar_TypeChecker_Env.is_action
                                        cfg.tcenv uu____15905
                                      ->
                                      let head3 = norm cfg env [] head2 in
                                      let action_unfolded =
                                        let uu____15910 =
                                          maybe_extract_fv head3 in
                                        match uu____15910 with
                                        | FStar_Pervasives_Native.Some
                                            uu____15915 ->
                                            FStar_Pervasives_Native.Some true
                                        | uu____15916 ->
                                            FStar_Pervasives_Native.Some
                                              false in
                                      (head3, action_unfolded)
                                  | uu____15921 ->
                                      (head2, FStar_Pervasives_Native.None) in
                                ((let is_arg_impure uu____15936 =
                                    match uu____15936 with
                                    | (e,q) ->
                                        let uu____15943 =
                                          let uu____15944 =
                                            FStar_Syntax_Subst.compress e in
                                          uu____15944.FStar_Syntax_Syntax.n in
                                        (match uu____15943 with
                                         | FStar_Syntax_Syntax.Tm_meta
                                             (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                              (m11,m2,t'))
                                             ->
                                             Prims.op_Negation
                                               (FStar_Syntax_Util.is_pure_effect
                                                  m11)
                                         | uu____15959 -> false) in
                                  let uu____15960 =
                                    let uu____15961 =
                                      let uu____15968 =
                                        FStar_Syntax_Syntax.as_arg head_app in
                                      uu____15968 :: args in
                                    FStar_Util.for_some is_arg_impure
                                      uu____15961 in
                                  if uu____15960
                                  then
                                    let uu____15973 =
                                      let uu____15974 =
                                        FStar_Syntax_Print.term_to_string
                                          head1 in
                                      FStar_Util.format1
                                        "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                        uu____15974 in
                                    failwith uu____15973
                                  else ());
                                 (let uu____15976 =
                                    maybe_unfold_action head_app in
                                  match uu____15976 with
                                  | (head_app1,found_action) ->
                                      let mk1 tm =
                                        FStar_Syntax_Syntax.mk tm
                                          FStar_Pervasives_Native.None
                                          t2.FStar_Syntax_Syntax.pos in
                                      let body =
                                        mk1
                                          (FStar_Syntax_Syntax.Tm_app
                                             (head_app1, args)) in
                                      let body1 =
                                        match found_action with
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Syntax_Util.mk_reify body
                                        | FStar_Pervasives_Native.Some (false
                                            ) ->
                                            mk1
                                              (FStar_Syntax_Syntax.Tm_meta
                                                 (body,
                                                   (FStar_Syntax_Syntax.Meta_monadic
                                                      (m1, t2))))
                                        | FStar_Pervasives_Native.Some (true
                                            ) -> body in
                                      let uu____16015 = FStar_List.tl stack1 in
                                      norm cfg env uu____16015 body1)))
                       | FStar_Syntax_Syntax.Tm_meta
                           (e,FStar_Syntax_Syntax.Meta_monadic_lift
                            (msrc,mtgt,t'))
                           ->
                           let lifted =
                             let uu____16029 = closure_as_term cfg env t' in
                             reify_lift cfg.tcenv e msrc mtgt uu____16029 in
                           let uu____16030 = FStar_List.tl stack1 in
                           norm cfg env uu____16030 lifted
                       | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                           let branches1 =
                             FStar_All.pipe_right branches
                               (FStar_List.map
                                  (fun uu____16151  ->
                                     match uu____16151 with
                                     | (pat,wopt,tm) ->
                                         let uu____16199 =
                                           FStar_Syntax_Util.mk_reify tm in
                                         (pat, wopt, uu____16199))) in
                           let tm =
                             mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                               t2.FStar_Syntax_Syntax.pos in
                           let uu____16231 = FStar_List.tl stack1 in
                           norm cfg env uu____16231 tm
                       | uu____16232 -> norm cfg env stack1 head1)
                | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                    let should_reify =
                      match stack1 with
                      | (App
                          (uu____16241,{
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_constant
                                           (FStar_Const.Const_reify );
                                         FStar_Syntax_Syntax.pos =
                                           uu____16242;
                                         FStar_Syntax_Syntax.vars =
                                           uu____16243;_},uu____16244,uu____16245))::uu____16246
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____16253 -> false in
                    if should_reify
                    then
                      let uu____16254 = FStar_List.tl stack1 in
                      let uu____16255 =
                        let uu____16256 = closure_as_term cfg env t2 in
                        reify_lift cfg.tcenv head1 m1 m' uu____16256 in
                      norm cfg env uu____16254 uu____16255
                    else
                      (let t3 = norm cfg env [] t2 in
                       let uu____16259 =
                         ((FStar_Syntax_Util.is_pure_effect m1) ||
                            (FStar_Syntax_Util.is_ghost_effect m1))
                           &&
                           (FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations)) in
                       if uu____16259
                       then
                         let stack2 =
                           (Steps
                              ((cfg.steps), (cfg.primitive_steps),
                                (cfg.delta_level)))
                           :: stack1 in
                         let cfg1 =
                           let uu___231_16268 = cfg in
                           {
                             steps =
                               [PureSubtermsWithinComputations;
                               Primops;
                               AllowUnboundUniverses;
                               EraseUniverses;
                               Exclude Zeta];
                             tcenv = (uu___231_16268.tcenv);
                             delta_level =
                               [FStar_TypeChecker_Env.Inlining;
                               FStar_TypeChecker_Env.Eager_unfolding_only];
                             primitive_steps =
                               (uu___231_16268.primitive_steps)
                           } in
                         norm cfg1 env
                           ((Meta
                               ((FStar_Syntax_Syntax.Meta_monadic_lift
                                   (m1, m', t3)),
                                 (head1.FStar_Syntax_Syntax.pos))) :: stack2)
                           head1
                       else
                         norm cfg env
                           ((Meta
                               ((FStar_Syntax_Syntax.Meta_monadic_lift
                                   (m1, m', t3)),
                                 (head1.FStar_Syntax_Syntax.pos))) :: stack1)
                           head1)
                | uu____16270 ->
                    if FStar_List.contains Unmeta cfg.steps
                    then norm cfg env stack1 head1
                    else
                      (match stack1 with
                       | uu____16272::uu____16273 ->
                           (match m with
                            | FStar_Syntax_Syntax.Meta_labeled
                                (l,r,uu____16278) ->
                                norm cfg env ((Meta (m, r)) :: stack1) head1
                            | FStar_Syntax_Syntax.Meta_alien (b,s) ->
                                norm cfg env
                                  ((Meta (m, (t1.FStar_Syntax_Syntax.pos)))
                                  :: stack1) head1
                            | FStar_Syntax_Syntax.Meta_pattern args ->
                                let args1 = norm_pattern_args cfg env args in
                                norm cfg env
                                  ((Meta
                                      ((FStar_Syntax_Syntax.Meta_pattern
                                          args1),
                                        (t1.FStar_Syntax_Syntax.pos))) ::
                                  stack1) head1
                            | uu____16303 -> norm cfg env stack1 head1)
                       | [] ->
                           let head2 = norm cfg env [] head1 in
                           let m1 =
                             match m with
                             | FStar_Syntax_Syntax.Meta_pattern args ->
                                 let uu____16317 =
                                   norm_pattern_args cfg env args in
                                 FStar_Syntax_Syntax.Meta_pattern uu____16317
                             | uu____16328 -> m in
                           let t2 =
                             mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                               t1.FStar_Syntax_Syntax.pos in
                           rebuild cfg env stack1 t2)))
and reify_lift:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.monad_name ->
        FStar_Syntax_Syntax.monad_name ->
          FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun e  ->
      fun msrc  ->
        fun mtgt  ->
          fun t  ->
            if FStar_Syntax_Util.is_pure_effect msrc
            then
              let ed = FStar_TypeChecker_Env.get_effect_decl env mtgt in
              let uu____16340 = ed.FStar_Syntax_Syntax.return_repr in
              match uu____16340 with
              | (uu____16341,return_repr) ->
                  let return_inst =
                    let uu____16350 =
                      let uu____16351 =
                        FStar_Syntax_Subst.compress return_repr in
                      uu____16351.FStar_Syntax_Syntax.n in
                    match uu____16350 with
                    | FStar_Syntax_Syntax.Tm_uinst
                        (return_tm,uu____16357::[]) ->
                        let uu____16364 =
                          let uu____16367 =
                            let uu____16368 =
                              let uu____16375 =
                                let uu____16378 =
                                  env.FStar_TypeChecker_Env.universe_of env t in
                                [uu____16378] in
                              (return_tm, uu____16375) in
                            FStar_Syntax_Syntax.Tm_uinst uu____16368 in
                          FStar_Syntax_Syntax.mk uu____16367 in
                        uu____16364 FStar_Pervasives_Native.None
                          e.FStar_Syntax_Syntax.pos
                    | uu____16386 ->
                        failwith "NIY : Reification of indexed effects" in
                  let uu____16389 =
                    let uu____16392 =
                      let uu____16393 =
                        let uu____16408 =
                          let uu____16411 = FStar_Syntax_Syntax.as_arg t in
                          let uu____16412 =
                            let uu____16415 = FStar_Syntax_Syntax.as_arg e in
                            [uu____16415] in
                          uu____16411 :: uu____16412 in
                        (return_inst, uu____16408) in
                      FStar_Syntax_Syntax.Tm_app uu____16393 in
                    FStar_Syntax_Syntax.mk uu____16392 in
                  uu____16389 FStar_Pervasives_Native.None
                    e.FStar_Syntax_Syntax.pos
            else
              (let uu____16424 =
                 FStar_TypeChecker_Env.monad_leq env msrc mtgt in
               match uu____16424 with
               | FStar_Pervasives_Native.None  ->
                   let uu____16427 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt) in
                   failwith uu____16427
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____16428;
                     FStar_TypeChecker_Env.mtarget = uu____16429;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____16430;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.None ;_};_}
                   ->
                   failwith
                     "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____16441;
                     FStar_TypeChecker_Env.mtarget = uu____16442;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____16443;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.Some lift;_};_}
                   ->
                   let uu____16461 = FStar_Syntax_Util.mk_reify e in
                   lift t FStar_Syntax_Syntax.tun uu____16461)
and norm_pattern_args:
  cfg ->
    env ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list Prims.list ->
        (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
          FStar_Pervasives_Native.tuple2 Prims.list Prims.list
  =
  fun cfg  ->
    fun env  ->
      fun args  ->
        FStar_All.pipe_right args
          (FStar_List.map
             (FStar_List.map
                (fun uu____16517  ->
                   match uu____16517 with
                   | (a,imp) ->
                       let uu____16528 = norm cfg env [] a in
                       (uu____16528, imp))))
and norm_comp:
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        let comp1 = ghost_to_pure_aux cfg env comp in
        match comp1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___232_16545 = comp1 in
            let uu____16548 =
              let uu____16549 =
                let uu____16558 = norm cfg env [] t in
                let uu____16559 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____16558, uu____16559) in
              FStar_Syntax_Syntax.Total uu____16549 in
            {
              FStar_Syntax_Syntax.n = uu____16548;
              FStar_Syntax_Syntax.pos =
                (uu___232_16545.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___232_16545.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___233_16574 = comp1 in
            let uu____16577 =
              let uu____16578 =
                let uu____16587 = norm cfg env [] t in
                let uu____16588 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____16587, uu____16588) in
              FStar_Syntax_Syntax.GTotal uu____16578 in
            {
              FStar_Syntax_Syntax.n = uu____16577;
              FStar_Syntax_Syntax.pos =
                (uu___233_16574.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___233_16574.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____16640  ->
                      match uu____16640 with
                      | (a,i) ->
                          let uu____16651 = norm cfg env [] a in
                          (uu____16651, i))) in
            let flags =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___185_16662  ->
                      match uu___185_16662 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____16666 = norm cfg env [] t in
                          FStar_Syntax_Syntax.DECREASES uu____16666
                      | f -> f)) in
            let uu___234_16670 = comp1 in
            let uu____16673 =
              let uu____16674 =
                let uu___235_16675 = ct in
                let uu____16676 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs in
                let uu____16677 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ in
                let uu____16680 =
                  norm_args ct.FStar_Syntax_Syntax.effect_args in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____16676;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___235_16675.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____16677;
                  FStar_Syntax_Syntax.effect_args = uu____16680;
                  FStar_Syntax_Syntax.flags = flags
                } in
              FStar_Syntax_Syntax.Comp uu____16674 in
            {
              FStar_Syntax_Syntax.n = uu____16673;
              FStar_Syntax_Syntax.pos =
                (uu___234_16670.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___234_16670.FStar_Syntax_Syntax.vars)
            }
and ghost_to_pure_aux:
  cfg ->
    env ->
      FStar_Syntax_Syntax.comp ->
        FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax
  =
  fun cfg  ->
    fun env  ->
      fun c  ->
        let norm1 t =
          norm
            (let uu___236_16698 = cfg in
             {
               steps =
                 [Eager_unfolding;
                 UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
                 AllowUnboundUniverses];
               tcenv = (uu___236_16698.tcenv);
               delta_level = (uu___236_16698.delta_level);
               primitive_steps = (uu___236_16698.primitive_steps)
             }) env [] t in
        let non_info t =
          let uu____16703 = norm1 t in
          FStar_Syntax_Util.non_informative uu____16703 in
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____16706 -> c
        | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
            let uu___237_16725 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
              FStar_Syntax_Syntax.pos =
                (uu___237_16725.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___237_16725.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let l =
              FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                ct.FStar_Syntax_Syntax.effect_name in
            let uu____16732 =
              (FStar_Syntax_Util.is_ghost_effect l) &&
                (non_info ct.FStar_Syntax_Syntax.result_typ) in
            if uu____16732
            then
              let ct1 =
                match downgrade_ghost_effect_name
                        ct.FStar_Syntax_Syntax.effect_name
                with
                | FStar_Pervasives_Native.Some pure_eff ->
                    let flags =
                      if
                        FStar_Ident.lid_equals pure_eff
                          FStar_Parser_Const.effect_Tot_lid
                      then FStar_Syntax_Syntax.TOTAL ::
                        (ct.FStar_Syntax_Syntax.flags)
                      else ct.FStar_Syntax_Syntax.flags in
                    let uu___238_16743 = ct in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___238_16743.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name = pure_eff;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___238_16743.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___238_16743.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags = flags
                    }
                | FStar_Pervasives_Native.None  ->
                    let ct1 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c in
                    let uu___239_16745 = ct1 in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___239_16745.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name =
                        FStar_Parser_Const.effect_PURE_lid;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___239_16745.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___239_16745.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___239_16745.FStar_Syntax_Syntax.flags)
                    } in
              let uu___240_16746 = c in
              {
                FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
                FStar_Syntax_Syntax.pos =
                  (uu___240_16746.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars =
                  (uu___240_16746.FStar_Syntax_Syntax.vars)
              }
            else c
        | uu____16748 -> c
and norm_binder:
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder =
  fun cfg  ->
    fun env  ->
      fun uu____16751  ->
        match uu____16751 with
        | (x,imp) ->
            let uu____16754 =
              let uu___241_16755 = x in
              let uu____16756 = norm cfg env [] x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___241_16755.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___241_16755.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____16756
              } in
            (uu____16754, imp)
and norm_binders:
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____16762 =
          FStar_List.fold_left
            (fun uu____16780  ->
               fun b  ->
                 match uu____16780 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs in
        match uu____16762 with | (nbs,uu____16820) -> FStar_List.rev nbs
and norm_lcomp_opt:
  cfg ->
    env ->
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option
  =
  fun cfg  ->
    fun env  ->
      fun lopt  ->
        match lopt with
        | FStar_Pervasives_Native.Some rc ->
            let flags =
              filter_out_lcomp_cflags rc.FStar_Syntax_Syntax.residual_flags in
            let uu____16836 =
              let uu___242_16837 = rc in
              let uu____16838 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env []) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___242_16837.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____16838;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___242_16837.FStar_Syntax_Syntax.residual_flags)
              } in
            FStar_Pervasives_Native.Some uu____16836
        | uu____16845 -> lopt
and rebuild:
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack1  ->
        fun t  ->
          log cfg
            (fun uu____16858  ->
               let uu____16859 = FStar_Syntax_Print.tag_of_term t in
               let uu____16860 = FStar_Syntax_Print.term_to_string t in
               let uu____16861 =
                 FStar_Util.string_of_int (FStar_List.length env) in
               let uu____16868 =
                 let uu____16869 =
                   let uu____16872 = firstn (Prims.parse_int "4") stack1 in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____16872 in
                 stack_to_string uu____16869 in
               FStar_Util.print4
                 ">>> %s\\Rebuild %s with %s env elements and top of the stack %s \n"
                 uu____16859 uu____16860 uu____16861 uu____16868);
          (match stack1 with
           | [] -> t
           | (Debug (tm,time_then))::stack2 ->
               ((let uu____16901 =
                   FStar_All.pipe_left
                     (FStar_TypeChecker_Env.debug cfg.tcenv)
                     (FStar_Options.Other "print_normalized_terms") in
                 if uu____16901
                 then
                   let time_now = FStar_Util.now () in
                   let uu____16903 =
                     let uu____16904 =
                       let uu____16905 =
                         FStar_Util.time_diff time_then time_now in
                       FStar_Pervasives_Native.snd uu____16905 in
                     FStar_Util.string_of_int uu____16904 in
                   let uu____16910 = FStar_Syntax_Print.term_to_string tm in
                   let uu____16911 = FStar_Syntax_Print.term_to_string t in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____16903 uu____16910 uu____16911
                 else ());
                rebuild cfg env stack2 t)
           | (Steps (s,ps,dl))::stack2 ->
               rebuild
                 (let uu___243_16929 = cfg in
                  {
                    steps = s;
                    tcenv = (uu___243_16929.tcenv);
                    delta_level = dl;
                    primitive_steps = ps
                  }) env stack2 t
           | (Meta (m,r))::stack2 ->
               let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m)) r in
               rebuild cfg env stack2 t1
           | (MemoLazy r)::stack2 ->
               (set_memo r (env, t);
                log cfg
                  (fun uu____17022  ->
                     let uu____17023 = FStar_Syntax_Print.term_to_string t in
                     FStar_Util.print1 "\tSet memo %s\n" uu____17023);
                rebuild cfg env stack2 t)
           | (Let (env',bs,lb,r))::stack2 ->
               let body = FStar_Syntax_Subst.close bs t in
               let t1 =
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_let ((false, [lb]), body))
                   FStar_Pervasives_Native.None r in
               rebuild cfg env' stack2 t1
           | (Abs (env',bs,env'',lopt,r))::stack2 ->
               let bs1 = norm_binders cfg env' bs in
               let lopt1 = norm_lcomp_opt cfg env'' lopt in
               let uu____17059 =
                 let uu___244_17060 = FStar_Syntax_Util.abs bs1 t lopt1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___244_17060.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___244_17060.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack2 uu____17059
           | (Arg (Univ uu____17061,uu____17062,uu____17063))::uu____17064 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____17067,uu____17068))::uu____17069 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack2 ->
               let t1 = FStar_Syntax_Syntax.mk_Tm_uinst t us in
               rebuild cfg env stack2 t1
           | (Arg (Clos (env_arg,tm,m,uu____17085),aq,r))::stack2 ->
               (log cfg
                  (fun uu____17138  ->
                     let uu____17139 = FStar_Syntax_Print.term_to_string tm in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____17139);
                if FStar_List.contains (Exclude Iota) cfg.steps
                then
                  (if FStar_List.contains WHNF cfg.steps
                   then
                     let arg = closure_as_term cfg env_arg tm in
                     let t1 =
                       FStar_Syntax_Syntax.extend_app t (arg, aq)
                         FStar_Pervasives_Native.None r in
                     rebuild cfg env_arg stack2 t1
                   else
                     (let stack3 = (App (env, t, aq, r)) :: stack2 in
                      norm cfg env_arg stack3 tm))
                else
                  (let uu____17149 = FStar_ST.op_Bang m in
                   match uu____17149 with
                   | FStar_Pervasives_Native.None  ->
                       if FStar_List.contains WHNF cfg.steps
                       then
                         let arg = closure_as_term cfg env_arg tm in
                         let t1 =
                           FStar_Syntax_Syntax.extend_app t (arg, aq)
                             FStar_Pervasives_Native.None r in
                         rebuild cfg env_arg stack2 t1
                       else
                         (let stack3 = (MemoLazy m) :: (App (env, t, aq, r))
                            :: stack2 in
                          norm cfg env_arg stack3 tm)
                   | FStar_Pervasives_Native.Some (uu____17293,a) ->
                       let t1 =
                         FStar_Syntax_Syntax.extend_app t (a, aq)
                           FStar_Pervasives_Native.None r in
                       rebuild cfg env_arg stack2 t1))
           | (App (env1,head1,aq,r))::stack2 ->
               let t1 =
                 FStar_Syntax_Syntax.extend_app head1 (t, aq)
                   FStar_Pervasives_Native.None r in
               let uu____17336 = maybe_simplify cfg env1 stack2 t1 in
               rebuild cfg env1 stack2 uu____17336
           | (Match (env1,branches,r))::stack2 ->
               (log cfg
                  (fun uu____17348  ->
                     let uu____17349 = FStar_Syntax_Print.term_to_string t in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____17349);
                (let scrutinee = t in
                 let norm_and_rebuild_match uu____17354 =
                   log cfg
                     (fun uu____17359  ->
                        let uu____17360 =
                          FStar_Syntax_Print.term_to_string scrutinee in
                        let uu____17361 =
                          let uu____17362 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____17379  ->
                                    match uu____17379 with
                                    | (p,uu____17389,uu____17390) ->
                                        FStar_Syntax_Print.pat_to_string p)) in
                          FStar_All.pipe_right uu____17362
                            (FStar_String.concat "\n\t") in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____17360 uu____17361);
                   (let whnf1 = FStar_List.contains WHNF cfg.steps in
                    let cfg_exclude_iota_zeta =
                      let new_delta =
                        FStar_All.pipe_right cfg.delta_level
                          (FStar_List.filter
                             (fun uu___186_17407  ->
                                match uu___186_17407 with
                                | FStar_TypeChecker_Env.Inlining  -> true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____17408 -> false)) in
                      let steps' =
                        let uu____17412 =
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains
                               PureSubtermsWithinComputations) in
                        if uu____17412
                        then [Exclude Zeta]
                        else [Exclude Iota; Exclude Zeta] in
                      let uu___245_17416 = cfg in
                      {
                        steps = (FStar_List.append steps' cfg.steps);
                        tcenv = (uu___245_17416.tcenv);
                        delta_level = new_delta;
                        primitive_steps = (uu___245_17416.primitive_steps)
                      } in
                    let norm_or_whnf env2 t1 =
                      if whnf1
                      then closure_as_term cfg_exclude_iota_zeta env2 t1
                      else norm cfg_exclude_iota_zeta env2 [] t1 in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____17448 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____17469 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____17529  ->
                                    fun uu____17530  ->
                                      match (uu____17529, uu____17530) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____17621 = norm_pat env3 p1 in
                                          (match uu____17621 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2)) in
                          (match uu____17469 with
                           | (pats1,env3) ->
                               ((let uu___246_17703 = p in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___246_17703.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___247_17722 = x in
                            let uu____17723 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___247_17722.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___247_17722.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17723
                            } in
                          ((let uu___248_17737 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___248_17737.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___249_17748 = x in
                            let uu____17749 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___249_17748.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___249_17748.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17749
                            } in
                          ((let uu___250_17763 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___250_17763.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                          let x1 =
                            let uu___251_17779 = x in
                            let uu____17780 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___251_17779.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___251_17779.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17780
                            } in
                          let t2 = norm_or_whnf env2 t1 in
                          ((let uu___252_17787 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                              FStar_Syntax_Syntax.p =
                                (uu___252_17787.FStar_Syntax_Syntax.p)
                            }), env2) in
                    let branches1 =
                      match env1 with
                      | [] when whnf1 -> branches
                      | uu____17797 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____17811 =
                                    FStar_Syntax_Subst.open_branch branch1 in
                                  match uu____17811 with
                                  | (p,wopt,e) ->
                                      let uu____17831 = norm_pat env1 p in
                                      (match uu____17831 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____17856 =
                                                   norm_or_whnf env2 w in
                                                 FStar_Pervasives_Native.Some
                                                   uu____17856 in
                                           let e1 = norm_or_whnf env2 e in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1)))) in
                    let uu____17862 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                        r in
                    rebuild cfg env1 stack2 uu____17862) in
                 let rec is_cons head1 =
                   match head1.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____17872) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____17877 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____17878;
                         FStar_Syntax_Syntax.fv_delta = uu____17879;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____17880;
                         FStar_Syntax_Syntax.fv_delta = uu____17881;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____17882);_}
                       -> true
                   | uu____17889 -> false in
                 let guard_when_clause wopt b rest =
                   match wopt with
                   | FStar_Pervasives_Native.None  -> b
                   | FStar_Pervasives_Native.Some w ->
                       let then_branch = b in
                       let else_branch =
                         mk (FStar_Syntax_Syntax.Tm_match (scrutinee, rest))
                           r in
                       FStar_Syntax_Util.if_then_else w then_branch
                         else_branch in
                 let rec matches_pat scrutinee_orig p =
                   let scrutinee1 = FStar_Syntax_Util.unmeta scrutinee_orig in
                   let uu____18034 =
                     FStar_Syntax_Util.head_and_args scrutinee1 in
                   match uu____18034 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____18121 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee1.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when 
                                 s = s' -> FStar_Util.Inl []
                             | uu____18160 ->
                                 let uu____18161 =
                                   let uu____18162 = is_cons head1 in
                                   Prims.op_Negation uu____18162 in
                                 FStar_Util.Inr uu____18161)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____18187 =
                              let uu____18188 =
                                FStar_Syntax_Util.un_uinst head1 in
                              uu____18188.FStar_Syntax_Syntax.n in
                            (match uu____18187 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____18206 ->
                                 let uu____18207 =
                                   let uu____18208 = is_cons head1 in
                                   Prims.op_Negation uu____18208 in
                                 FStar_Util.Inr uu____18207))
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t1,uu____18277)::rest_a,(p1,uu____18280)::rest_p) ->
                       let uu____18324 = matches_pat t1 p1 in
                       (match uu____18324 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____18373 -> FStar_Util.Inr false in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____18479 = matches_pat scrutinee1 p1 in
                       (match uu____18479 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (log cfg
                               (fun uu____18519  ->
                                  let uu____18520 =
                                    FStar_Syntax_Print.pat_to_string p1 in
                                  let uu____18521 =
                                    let uu____18522 =
                                      FStar_List.map
                                        (fun uu____18532  ->
                                           match uu____18532 with
                                           | (uu____18537,t1) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t1) s in
                                    FStar_All.pipe_right uu____18522
                                      (FStar_String.concat "; ") in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____18520 uu____18521);
                             (let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____18568  ->
                                       match uu____18568 with
                                       | (bv,t1) ->
                                           let uu____18591 =
                                             let uu____18598 =
                                               let uu____18601 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv in
                                               FStar_Pervasives_Native.Some
                                                 uu____18601 in
                                             let uu____18602 =
                                               let uu____18603 =
                                                 let uu____18634 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t1)) in
                                                 ([], t1, uu____18634, false) in
                                               Clos uu____18603 in
                                             (uu____18598, uu____18602) in
                                           uu____18591 :: env2) env1 s in
                              let uu____18743 = guard_when_clause wopt b rest in
                              norm cfg env2 stack2 uu____18743))) in
                 let uu____18744 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains (Exclude Iota)) in
                 if uu____18744
                 then norm_and_rebuild_match ()
                 else matches scrutinee branches)))
let config: step Prims.list -> FStar_TypeChecker_Env.env -> cfg =
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___187_18767  ->
                match uu___187_18767 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                | uu____18771 -> [])) in
      let d1 =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____18777 -> d in
      {
        steps = s;
        tcenv = e;
        delta_level = d1;
        primitive_steps = built_in_primitive_steps
      }
let normalize_with_primitive_steps:
  primitive_step Prims.list ->
    step Prims.list ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun ps  ->
    fun s  ->
      fun e  ->
        fun t  ->
          let c = config s e in
          let c1 =
            let uu___253_18806 = config s e in
            {
              steps = (uu___253_18806.steps);
              tcenv = (uu___253_18806.tcenv);
              delta_level = (uu___253_18806.delta_level);
              primitive_steps = (FStar_List.append c.primitive_steps ps)
            } in
          norm c1 [] [] t
let normalize:
  steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  = fun s  -> fun e  -> fun t  -> normalize_with_primitive_steps [] s e t
let normalize_comp:
  steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun s  ->
    fun e  ->
      fun t  -> let uu____18837 = config s e in norm_comp uu____18837 [] t
let normalize_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let uu____18852 = config [] env in norm_universe uu____18852 [] u
let ghost_to_pure:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun env  ->
    fun c  ->
      let uu____18867 = config [] env in ghost_to_pure_aux uu____18867 [] c
let ghost_to_pure_lcomp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp
  =
  fun env  ->
    fun lc  ->
      let cfg =
        config
          [Eager_unfolding;
          UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
          EraseUniverses;
          AllowUnboundUniverses] env in
      let non_info t =
        let uu____18887 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____18887 in
      let uu____18894 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ) in
      if uu____18894
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | FStar_Pervasives_Native.Some pure_eff ->
            let uu___254_18896 = lc in
            {
              FStar_Syntax_Syntax.eff_name = pure_eff;
              FStar_Syntax_Syntax.res_typ =
                (uu___254_18896.FStar_Syntax_Syntax.res_typ);
              FStar_Syntax_Syntax.cflags =
                (uu___254_18896.FStar_Syntax_Syntax.cflags);
              FStar_Syntax_Syntax.comp =
                ((fun uu____18899  ->
                    let uu____18900 = lc.FStar_Syntax_Syntax.comp () in
                    ghost_to_pure env uu____18900))
            }
        | FStar_Pervasives_Native.None  -> lc
      else lc
let term_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string =
  fun env  ->
    fun t  ->
      let t1 =
        try normalize [AllowUnboundUniverses] env t
        with
        | e ->
            ((let uu____18919 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning "Normalization failed with error %s"
                uu____18919);
             t) in
      FStar_Syntax_Print.term_to_string t1
let comp_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____18932 = config [AllowUnboundUniverses] env in
          norm_comp uu____18932 [] c
        with
        | e ->
            ((let uu____18945 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning "Normalization failed with error %s"
                uu____18945);
             c) in
      FStar_Syntax_Print.comp_to_string c1
let normalize_refinement:
  steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
  =
  fun steps  ->
    fun env  ->
      fun t0  ->
        let t = normalize (FStar_List.append steps [Beta]) env t0 in
        let rec aux t1 =
          let t2 = FStar_Syntax_Subst.compress t1 in
          match t2.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
              let t01 = aux x.FStar_Syntax_Syntax.sort in
              (match t01.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_refine (y,phi1) ->
                   let uu____18985 =
                     let uu____18986 =
                       let uu____18993 = FStar_Syntax_Util.mk_conj phi1 phi in
                       (y, uu____18993) in
                     FStar_Syntax_Syntax.Tm_refine uu____18986 in
                   mk uu____18985 t01.FStar_Syntax_Syntax.pos
               | uu____18998 -> t2)
          | uu____18999 -> t2 in
        aux t
let unfold_whnf:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      normalize [WHNF; UnfoldUntil FStar_Syntax_Syntax.Delta_constant; Beta]
        env t
let reduce_or_remove_uvar_solutions:
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun remove  ->
    fun env  ->
      fun t  ->
        normalize
          (FStar_List.append (if remove then [CheckNoUvars] else [])
             [Beta;
             NoDeltaSteps;
             CompressUvars;
             Exclude Zeta;
             Exclude Iota;
             NoFullNorm]) env t
let reduce_uvar_solutions:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  = fun env  -> fun t  -> reduce_or_remove_uvar_solutions false env t
let remove_uvar_solutions:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  = fun env  -> fun t  -> reduce_or_remove_uvar_solutions true env t
let eta_expand_with_type:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun e  ->
      fun t_e  ->
        let uu____19051 = FStar_Syntax_Util.arrow_formals_comp t_e in
        match uu____19051 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____19080 ->
                 let uu____19087 = FStar_Syntax_Util.abs_formals e in
                 (match uu____19087 with
                  | (actuals,uu____19097,uu____19098) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____19112 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders in
                         match uu____19112 with
                         | (binders,args) ->
                             let uu____19129 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos in
                             FStar_Syntax_Util.abs binders uu____19129
                               (FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.residual_comp_of_comp c)))))
let eta_expand:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_name x ->
          eta_expand_with_type env t x.FStar_Syntax_Syntax.sort
      | uu____19139 ->
          let uu____19140 = FStar_Syntax_Util.head_and_args t in
          (match uu____19140 with
           | (head1,args) ->
               let uu____19177 =
                 let uu____19178 = FStar_Syntax_Subst.compress head1 in
                 uu____19178.FStar_Syntax_Syntax.n in
               (match uu____19177 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____19181,thead) ->
                    let uu____19207 = FStar_Syntax_Util.arrow_formals thead in
                    (match uu____19207 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____19249 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___259_19257 = env in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___259_19257.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___259_19257.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___259_19257.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___259_19257.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___259_19257.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___259_19257.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___259_19257.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___259_19257.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___259_19257.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___259_19257.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___259_19257.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___259_19257.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___259_19257.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___259_19257.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___259_19257.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___259_19257.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___259_19257.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___259_19257.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___259_19257.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___259_19257.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___259_19257.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___259_19257.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___259_19257.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___259_19257.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___259_19257.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___259_19257.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___259_19257.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___259_19257.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___259_19257.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___259_19257.FStar_TypeChecker_Env.dsenv)
                                 }) t in
                            match uu____19249 with
                            | (uu____19258,ty,uu____19260) ->
                                eta_expand_with_type env t ty))
                | uu____19261 ->
                    let uu____19262 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___260_19270 = env in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___260_19270.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___260_19270.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___260_19270.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___260_19270.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___260_19270.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___260_19270.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___260_19270.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___260_19270.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___260_19270.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___260_19270.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___260_19270.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___260_19270.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___260_19270.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___260_19270.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___260_19270.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___260_19270.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___260_19270.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___260_19270.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___260_19270.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___260_19270.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___260_19270.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___260_19270.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___260_19270.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___260_19270.FStar_TypeChecker_Env.qname_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___260_19270.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth =
                             (uu___260_19270.FStar_TypeChecker_Env.synth);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___260_19270.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___260_19270.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___260_19270.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___260_19270.FStar_TypeChecker_Env.dsenv)
                         }) t in
                    (match uu____19262 with
                     | (uu____19271,ty,uu____19273) ->
                         eta_expand_with_type env t ty)))
let elim_uvars_aux_tc:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.binders ->
        (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.comp) FStar_Util.either
          ->
          (FStar_Syntax_Syntax.univ_names,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
                                            FStar_Pervasives_Native.tuple2
                                            Prims.list,(FStar_Syntax_Syntax.term,
                                                         FStar_Syntax_Syntax.comp'
                                                           FStar_Syntax_Syntax.syntax)
                                                         FStar_Util.either)
            FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun univ_names  ->
      fun binders  ->
        fun tc  ->
          let t =
            match (binders, tc) with
            | ([],FStar_Util.Inl t) -> t
            | ([],FStar_Util.Inr c) ->
                failwith "Impossible: empty bindes with a comp"
            | (uu____19351,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____19357,FStar_Util.Inl t) ->
                let uu____19363 =
                  let uu____19366 =
                    let uu____19367 =
                      let uu____19380 = FStar_Syntax_Syntax.mk_Total t in
                      (binders, uu____19380) in
                    FStar_Syntax_Syntax.Tm_arrow uu____19367 in
                  FStar_Syntax_Syntax.mk uu____19366 in
                uu____19363 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos in
          let uu____19384 = FStar_Syntax_Subst.open_univ_vars univ_names t in
          match uu____19384 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1 in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2 in
              let uu____19411 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t3))
                | uu____19466 ->
                    let uu____19467 =
                      let uu____19476 =
                        let uu____19477 = FStar_Syntax_Subst.compress t3 in
                        uu____19477.FStar_Syntax_Syntax.n in
                      (uu____19476, tc) in
                    (match uu____19467 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____19502) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____19539) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____19578,FStar_Util.Inl uu____19579) ->
                         ([], (FStar_Util.Inl t3))
                     | uu____19602 -> failwith "Impossible") in
              (match uu____19411 with
               | (binders1,tc1) -> (univ_names1, binders1, tc1))
let elim_uvars_aux_t:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.univ_names,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
                                            FStar_Pervasives_Native.tuple2
                                            Prims.list,FStar_Syntax_Syntax.term)
            FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun univ_names  ->
      fun binders  ->
        fun t  ->
          let uu____19711 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t) in
          match uu____19711 with
          | (univ_names1,binders1,tc) ->
              let uu____19769 = FStar_Util.left tc in
              (univ_names1, binders1, uu____19769)
let elim_uvars_aux_c:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.comp ->
          (FStar_Syntax_Syntax.univ_names,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
                                            FStar_Pervasives_Native.tuple2
                                            Prims.list,FStar_Syntax_Syntax.comp'
                                                         FStar_Syntax_Syntax.syntax)
            FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun univ_names  ->
      fun binders  ->
        fun c  ->
          let uu____19808 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c) in
          match uu____19808 with
          | (univ_names1,binders1,tc) ->
              let uu____19868 = FStar_Util.right tc in
              (univ_names1, binders1, uu____19868)
let rec elim_uvars:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____19903 = elim_uvars_aux_t env univ_names binders typ in
          (match uu____19903 with
           | (univ_names1,binders1,typ1) ->
               let uu___261_19931 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___261_19931.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___261_19931.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___261_19931.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___261_19931.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___262_19952 = s in
          let uu____19953 =
            let uu____19954 =
              let uu____19963 = FStar_List.map (elim_uvars env) sigs in
              (uu____19963, lids) in
            FStar_Syntax_Syntax.Sig_bundle uu____19954 in
          {
            FStar_Syntax_Syntax.sigel = uu____19953;
            FStar_Syntax_Syntax.sigrng =
              (uu___262_19952.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___262_19952.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___262_19952.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___262_19952.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____19980 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____19980 with
           | (univ_names1,uu____19998,typ1) ->
               let uu___263_20012 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___263_20012.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___263_20012.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___263_20012.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___263_20012.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____20018 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____20018 with
           | (univ_names1,uu____20036,typ1) ->
               let uu___264_20050 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___264_20050.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___264_20050.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___264_20050.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___264_20050.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____20084 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs in
                    match uu____20084 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____20107 =
                            let uu____20108 =
                              FStar_Syntax_Subst.subst opening t in
                            remove_uvar_solutions env uu____20108 in
                          FStar_Syntax_Subst.close_univ_vars lbunivs
                            uu____20107 in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef in
                        let uu___265_20111 = lb in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___265_20111.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___265_20111.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef
                        })) in
          let uu___266_20112 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___266_20112.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___266_20112.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___266_20112.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___266_20112.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___267_20124 = s in
          let uu____20125 =
            let uu____20126 = remove_uvar_solutions env t in
            FStar_Syntax_Syntax.Sig_main uu____20126 in
          {
            FStar_Syntax_Syntax.sigel = uu____20125;
            FStar_Syntax_Syntax.sigrng =
              (uu___267_20124.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___267_20124.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___267_20124.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___267_20124.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____20130 = elim_uvars_aux_t env us [] t in
          (match uu____20130 with
           | (us1,uu____20148,t1) ->
               let uu___268_20162 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___268_20162.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___268_20162.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___268_20162.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___268_20162.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____20163 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____20165 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature in
          (match uu____20165 with
           | (univs1,binders,signature) ->
               let uu____20193 =
                 let uu____20202 = FStar_Syntax_Subst.univ_var_opening univs1 in
                 match uu____20202 with
                 | (univs_opening,univs2) ->
                     let uu____20229 =
                       FStar_Syntax_Subst.univ_var_closing univs2 in
                     (univs_opening, uu____20229) in
               (match uu____20193 with
                | (univs_opening,univs_closing) ->
                    let uu____20246 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders in
                      let uu____20252 =
                        FStar_Syntax_Subst.opening_of_binders binders1 in
                      let uu____20253 =
                        FStar_Syntax_Subst.closing_of_binders binders1 in
                      (uu____20252, uu____20253) in
                    (match uu____20246 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1 in
                         let n_binders = FStar_List.length binders in
                         let elim_tscheme uu____20275 =
                           match uu____20275 with
                           | (us,t) ->
                               let n_us = FStar_List.length us in
                               let uu____20293 =
                                 FStar_Syntax_Subst.open_univ_vars us t in
                               (match uu____20293 with
                                | (us1,t1) ->
                                    let uu____20304 =
                                      let uu____20309 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      let uu____20316 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      (uu____20309, uu____20316) in
                                    (match uu____20304 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____20329 =
                                           let uu____20334 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           let uu____20343 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           (uu____20334, uu____20343) in
                                         (match uu____20329 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____20359 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1 in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____20359 in
                                              let uu____20360 =
                                                elim_uvars_aux_t env [] [] t2 in
                                              (match uu____20360 with
                                               | (uu____20381,uu____20382,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____20397 =
                                                       let uu____20398 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3 in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____20398 in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____20397 in
                                                   (us1, t4))))) in
                         let elim_term t =
                           let uu____20403 =
                             elim_uvars_aux_t env univs1 binders t in
                           match uu____20403 with
                           | (uu____20416,uu____20417,t1) -> t1 in
                         let elim_action a =
                           let action_typ_templ =
                             let body =
                               FStar_Syntax_Syntax.mk
                                 (FStar_Syntax_Syntax.Tm_ascribed
                                    ((a.FStar_Syntax_Syntax.action_defn),
                                      ((FStar_Util.Inl
                                          (a.FStar_Syntax_Syntax.action_typ)),
                                        FStar_Pervasives_Native.None),
                                      FStar_Pervasives_Native.None))
                                 FStar_Pervasives_Native.None
                                 (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                             match a.FStar_Syntax_Syntax.action_params with
                             | [] -> body
                             | uu____20477 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                           let destruct_action_body body =
                             let uu____20494 =
                               let uu____20495 =
                                 FStar_Syntax_Subst.compress body in
                               uu____20495.FStar_Syntax_Syntax.n in
                             match uu____20494 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____20554 -> failwith "Impossible" in
                           let destruct_action_typ_templ t =
                             let uu____20583 =
                               let uu____20584 =
                                 FStar_Syntax_Subst.compress t in
                               uu____20584.FStar_Syntax_Syntax.n in
                             match uu____20583 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____20605) ->
                                 let uu____20626 = destruct_action_body body in
                                 (match uu____20626 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____20671 ->
                                 let uu____20672 = destruct_action_body t in
                                 (match uu____20672 with
                                  | (defn,typ) -> ([], defn, typ)) in
                           let uu____20721 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ) in
                           match uu____20721 with
                           | (action_univs,t) ->
                               let uu____20730 = destruct_action_typ_templ t in
                               (match uu____20730 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___269_20771 = a in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___269_20771.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___269_20771.FStar_Syntax_Syntax.action_unqualified_name);
                                        FStar_Syntax_Syntax.action_univs =
                                          action_univs;
                                        FStar_Syntax_Syntax.action_params =
                                          action_params;
                                        FStar_Syntax_Syntax.action_defn =
                                          action_defn;
                                        FStar_Syntax_Syntax.action_typ =
                                          action_typ
                                      } in
                                    a') in
                         let ed1 =
                           let uu___270_20773 = ed in
                           let uu____20774 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp in
                           let uu____20775 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____20776 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else in
                           let uu____20777 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp in
                           let uu____20778 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger in
                           let uu____20779 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp in
                           let uu____20780 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p in
                           let uu____20781 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p in
                           let uu____20782 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp in
                           let uu____20783 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial in
                           let uu____20784 =
                             elim_term ed.FStar_Syntax_Syntax.repr in
                           let uu____20785 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr in
                           let uu____20786 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr in
                           let uu____20787 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___270_20773.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___270_20773.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____20774;
                             FStar_Syntax_Syntax.bind_wp = uu____20775;
                             FStar_Syntax_Syntax.if_then_else = uu____20776;
                             FStar_Syntax_Syntax.ite_wp = uu____20777;
                             FStar_Syntax_Syntax.stronger = uu____20778;
                             FStar_Syntax_Syntax.close_wp = uu____20779;
                             FStar_Syntax_Syntax.assert_p = uu____20780;
                             FStar_Syntax_Syntax.assume_p = uu____20781;
                             FStar_Syntax_Syntax.null_wp = uu____20782;
                             FStar_Syntax_Syntax.trivial = uu____20783;
                             FStar_Syntax_Syntax.repr = uu____20784;
                             FStar_Syntax_Syntax.return_repr = uu____20785;
                             FStar_Syntax_Syntax.bind_repr = uu____20786;
                             FStar_Syntax_Syntax.actions = uu____20787
                           } in
                         let uu___271_20790 = s in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___271_20790.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___271_20790.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___271_20790.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___271_20790.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___188_20807 =
            match uu___188_20807 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____20834 = elim_uvars_aux_t env us [] t in
                (match uu____20834 with
                 | (us1,uu____20858,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1)) in
          let sub_eff1 =
            let uu___272_20877 = sub_eff in
            let uu____20878 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp in
            let uu____20881 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift in
            {
              FStar_Syntax_Syntax.source =
                (uu___272_20877.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___272_20877.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____20878;
              FStar_Syntax_Syntax.lift = uu____20881
            } in
          let uu___273_20884 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___273_20884.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___273_20884.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___273_20884.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___273_20884.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags) ->
          let uu____20894 = elim_uvars_aux_c env univ_names binders comp in
          (match uu____20894 with
           | (univ_names1,binders1,comp1) ->
               let uu___274_20928 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___274_20928.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___274_20928.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___274_20928.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___274_20928.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____20939 -> s