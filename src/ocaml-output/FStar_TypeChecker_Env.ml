open Prims
type binding =
  | Binding_var of FStar_Syntax_Syntax.bv 
  | Binding_lid of (FStar_Ident.lident * FStar_Syntax_Syntax.tscheme) 
  | Binding_sig of (FStar_Ident.lident Prims.list *
  FStar_Syntax_Syntax.sigelt) 
  | Binding_univ of FStar_Syntax_Syntax.univ_name 
  | Binding_sig_inst of (FStar_Ident.lident Prims.list *
  FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universes) 
let uu___is_Binding_var : binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_var _0 -> true | uu____35 -> false
  
let __proj__Binding_var__item___0 : binding -> FStar_Syntax_Syntax.bv =
  fun projectee  -> match projectee with | Binding_var _0 -> _0 
let uu___is_Binding_lid : binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_lid _0 -> true | uu____51 -> false
  
let __proj__Binding_lid__item___0 :
  binding -> (FStar_Ident.lident * FStar_Syntax_Syntax.tscheme) =
  fun projectee  -> match projectee with | Binding_lid _0 -> _0 
let uu___is_Binding_sig : binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_sig _0 -> true | uu____74 -> false
  
let __proj__Binding_sig__item___0 :
  binding -> (FStar_Ident.lident Prims.list * FStar_Syntax_Syntax.sigelt) =
  fun projectee  -> match projectee with | Binding_sig _0 -> _0 
let uu___is_Binding_univ : binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_univ _0 -> true | uu____97 -> false
  
let __proj__Binding_univ__item___0 : binding -> FStar_Syntax_Syntax.univ_name
  = fun projectee  -> match projectee with | Binding_univ _0 -> _0 
let uu___is_Binding_sig_inst : binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_sig_inst _0 -> true | uu____115 -> false
  
let __proj__Binding_sig_inst__item___0 :
  binding ->
    (FStar_Ident.lident Prims.list * FStar_Syntax_Syntax.sigelt *
      FStar_Syntax_Syntax.universes)
  = fun projectee  -> match projectee with | Binding_sig_inst _0 -> _0 
type delta_level =
  | NoDelta 
  | Inlining 
  | Eager_unfolding_only 
  | Unfold of FStar_Syntax_Syntax.delta_depth 
  | UnfoldTac 
let uu___is_NoDelta : delta_level -> Prims.bool =
  fun projectee  ->
    match projectee with | NoDelta  -> true | uu____144 -> false
  
let uu___is_Inlining : delta_level -> Prims.bool =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____149 -> false
  
let uu___is_Eager_unfolding_only : delta_level -> Prims.bool =
  fun projectee  ->
    match projectee with | Eager_unfolding_only  -> true | uu____154 -> false
  
let uu___is_Unfold : delta_level -> Prims.bool =
  fun projectee  ->
    match projectee with | Unfold _0 -> true | uu____160 -> false
  
let __proj__Unfold__item___0 : delta_level -> FStar_Syntax_Syntax.delta_depth
  = fun projectee  -> match projectee with | Unfold _0 -> _0 
let uu___is_UnfoldTac : delta_level -> Prims.bool =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____173 -> false
  
type mlift =
  {
  mlift_wp:
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
    ;
  mlift_term:
    (FStar_Syntax_Syntax.typ ->
       FStar_Syntax_Syntax.typ ->
         FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
      option
    }
let __proj__Mkmlift__item__mlift_wp :
  mlift ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
  =
  fun projectee  ->
    match projectee with
    | { mlift_wp = __fname__mlift_wp; mlift_term = __fname__mlift_term;_} ->
        __fname__mlift_wp
  
let __proj__Mkmlift__item__mlift_term :
  mlift ->
    (FStar_Syntax_Syntax.typ ->
       FStar_Syntax_Syntax.typ ->
         FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
      option
  =
  fun projectee  ->
    match projectee with
    | { mlift_wp = __fname__mlift_wp; mlift_term = __fname__mlift_term;_} ->
        __fname__mlift_term
  
type edge =
  {
  msource: FStar_Ident.lident ;
  mtarget: FStar_Ident.lident ;
  mlift: mlift }
let __proj__Mkedge__item__msource : edge -> FStar_Ident.lident =
  fun projectee  ->
    match projectee with
    | { msource = __fname__msource; mtarget = __fname__mtarget;
        mlift = __fname__mlift;_} -> __fname__msource
  
let __proj__Mkedge__item__mtarget : edge -> FStar_Ident.lident =
  fun projectee  ->
    match projectee with
    | { msource = __fname__msource; mtarget = __fname__mtarget;
        mlift = __fname__mlift;_} -> __fname__mtarget
  
let __proj__Mkedge__item__mlift : edge -> mlift =
  fun projectee  ->
    match projectee with
    | { msource = __fname__msource; mtarget = __fname__mtarget;
        mlift = __fname__mlift;_} -> __fname__mlift
  
type effects =
  {
  decls:
    (FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.qualifier Prims.list)
      Prims.list
    ;
  order: edge Prims.list ;
  joins:
    (FStar_Ident.lident * FStar_Ident.lident * FStar_Ident.lident * mlift *
      mlift) Prims.list
    }
let __proj__Mkeffects__item__decls :
  effects ->
    (FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.qualifier Prims.list)
      Prims.list
  =
  fun projectee  ->
    match projectee with
    | { decls = __fname__decls; order = __fname__order;
        joins = __fname__joins;_} -> __fname__decls
  
let __proj__Mkeffects__item__order : effects -> edge Prims.list =
  fun projectee  ->
    match projectee with
    | { decls = __fname__decls; order = __fname__order;
        joins = __fname__joins;_} -> __fname__order
  
let __proj__Mkeffects__item__joins :
  effects ->
    (FStar_Ident.lident * FStar_Ident.lident * FStar_Ident.lident * mlift *
      mlift) Prims.list
  =
  fun projectee  ->
    match projectee with
    | { decls = __fname__decls; order = __fname__order;
        joins = __fname__joins;_} -> __fname__joins
  
type name_prefix = Prims.string Prims.list
type flat_proof_namespace = (name_prefix * Prims.bool) Prims.list
type proof_namespace = flat_proof_namespace Prims.list
type cached_elt =
  (((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ),(FStar_Syntax_Syntax.sigelt
                                                                *
                                                                FStar_Syntax_Syntax.universes
                                                                option))
    FStar_Util.either * FStar_Range.range)
type goal = FStar_Syntax_Syntax.term
type env =
  {
  solver: solver_t ;
  range: FStar_Range.range ;
  curmodule: FStar_Ident.lident ;
  gamma: binding Prims.list ;
  gamma_cache: cached_elt FStar_Util.smap ;
  modules: FStar_Syntax_Syntax.modul Prims.list ;
  expected_typ: FStar_Syntax_Syntax.typ option ;
  sigtab: FStar_Syntax_Syntax.sigelt FStar_Util.smap ;
  is_pattern: Prims.bool ;
  instantiate_imp: Prims.bool ;
  effects: effects ;
  generalize: Prims.bool ;
  letrecs: (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ) Prims.list ;
  top_level: Prims.bool ;
  check_uvars: Prims.bool ;
  use_eq: Prims.bool ;
  is_iface: Prims.bool ;
  admit: Prims.bool ;
  lax: Prims.bool ;
  lax_universes: Prims.bool ;
  type_of:
    env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * guard_t)
    ;
  universe_of:
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe ;
  use_bv_sorts: Prims.bool ;
  qname_and_index: (FStar_Ident.lident * Prims.int) option ;
  proof_ns: proof_namespace ;
  synth:
    env ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
    ;
  is_native_tactic: FStar_Ident.lid -> Prims.bool }
and solver_t =
  {
  init: env -> Prims.unit ;
  push: Prims.string -> Prims.unit ;
  pop: Prims.string -> Prims.unit ;
  mark: Prims.string -> Prims.unit ;
  reset_mark: Prims.string -> Prims.unit ;
  commit_mark: Prims.string -> Prims.unit ;
  encode_modul: env -> FStar_Syntax_Syntax.modul -> Prims.unit ;
  encode_sig: env -> FStar_Syntax_Syntax.sigelt -> Prims.unit ;
  preprocess:
    env -> goal -> (env * goal * FStar_Options.optionstate) Prims.list ;
  solve:
    (Prims.unit -> Prims.string) option ->
      env -> FStar_Syntax_Syntax.typ -> Prims.unit
    ;
  is_trivial: env -> FStar_Syntax_Syntax.typ -> Prims.bool ;
  finish: Prims.unit -> Prims.unit ;
  refresh: Prims.unit -> Prims.unit }
and guard_t =
  {
  guard_f: FStar_TypeChecker_Common.guard_formula ;
  deferred: FStar_TypeChecker_Common.deferred ;
  univ_ineqs:
    (FStar_Syntax_Syntax.universe Prims.list *
      FStar_TypeChecker_Common.univ_ineq Prims.list)
    ;
  implicits:
    (Prims.string * env * FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.term
      * FStar_Syntax_Syntax.typ * FStar_Range.range) Prims.list
    }
let __proj__Mkenv__item__solver : env -> solver_t =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;_} -> __fname__solver
  
let __proj__Mkenv__item__range : env -> FStar_Range.range =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;_} -> __fname__range
  
let __proj__Mkenv__item__curmodule : env -> FStar_Ident.lident =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;_} -> __fname__curmodule
  
let __proj__Mkenv__item__gamma : env -> binding Prims.list =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;_} -> __fname__gamma
  
let __proj__Mkenv__item__gamma_cache : env -> cached_elt FStar_Util.smap =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;_} ->
        __fname__gamma_cache
  
let __proj__Mkenv__item__modules :
  env -> FStar_Syntax_Syntax.modul Prims.list =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;_} -> __fname__modules
  
let __proj__Mkenv__item__expected_typ : env -> FStar_Syntax_Syntax.typ option
  =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;_} ->
        __fname__expected_typ
  
let __proj__Mkenv__item__sigtab :
  env -> FStar_Syntax_Syntax.sigelt FStar_Util.smap =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;_} -> __fname__sigtab
  
let __proj__Mkenv__item__is_pattern : env -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;_} ->
        __fname__is_pattern
  
let __proj__Mkenv__item__instantiate_imp : env -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;_} ->
        __fname__instantiate_imp
  
let __proj__Mkenv__item__effects : env -> effects =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;_} -> __fname__effects
  
let __proj__Mkenv__item__generalize : env -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;_} ->
        __fname__generalize
  
let __proj__Mkenv__item__letrecs :
  env -> (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ) Prims.list =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;_} -> __fname__letrecs
  
let __proj__Mkenv__item__top_level : env -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;_} -> __fname__top_level
  
let __proj__Mkenv__item__check_uvars : env -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;_} ->
        __fname__check_uvars
  
let __proj__Mkenv__item__use_eq : env -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;_} -> __fname__use_eq
  
let __proj__Mkenv__item__is_iface : env -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;_} -> __fname__is_iface
  
let __proj__Mkenv__item__admit : env -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;_} -> __fname__admit
  
let __proj__Mkenv__item__lax : env -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;_} -> __fname__lax
  
let __proj__Mkenv__item__lax_universes : env -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;_} ->
        __fname__lax_universes
  
let __proj__Mkenv__item__type_of :
  env ->
    env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * guard_t)
  =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;_} -> __fname__type_of
  
let __proj__Mkenv__item__universe_of :
  env -> env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;_} ->
        __fname__universe_of
  
let __proj__Mkenv__item__use_bv_sorts : env -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;_} ->
        __fname__use_bv_sorts
  
let __proj__Mkenv__item__qname_and_index :
  env -> (FStar_Ident.lident * Prims.int) option =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;_} ->
        __fname__qname_and_index
  
let __proj__Mkenv__item__proof_ns : env -> proof_namespace =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;_} -> __fname__proof_ns
  
let __proj__Mkenv__item__synth :
  env ->
    env ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;_} -> __fname__synth
  
let __proj__Mkenv__item__is_native_tactic :
  env -> FStar_Ident.lid -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;_} ->
        __fname__is_native_tactic
  
let __proj__Mksolver_t__item__init : solver_t -> env -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        mark = __fname__mark; reset_mark = __fname__reset_mark;
        commit_mark = __fname__commit_mark;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; is_trivial = __fname__is_trivial;
        finish = __fname__finish; refresh = __fname__refresh;_} ->
        __fname__init
  
let __proj__Mksolver_t__item__push : solver_t -> Prims.string -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        mark = __fname__mark; reset_mark = __fname__reset_mark;
        commit_mark = __fname__commit_mark;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; is_trivial = __fname__is_trivial;
        finish = __fname__finish; refresh = __fname__refresh;_} ->
        __fname__push
  
let __proj__Mksolver_t__item__pop : solver_t -> Prims.string -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        mark = __fname__mark; reset_mark = __fname__reset_mark;
        commit_mark = __fname__commit_mark;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; is_trivial = __fname__is_trivial;
        finish = __fname__finish; refresh = __fname__refresh;_} ->
        __fname__pop
  
let __proj__Mksolver_t__item__mark : solver_t -> Prims.string -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        mark = __fname__mark; reset_mark = __fname__reset_mark;
        commit_mark = __fname__commit_mark;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; is_trivial = __fname__is_trivial;
        finish = __fname__finish; refresh = __fname__refresh;_} ->
        __fname__mark
  
let __proj__Mksolver_t__item__reset_mark :
  solver_t -> Prims.string -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        mark = __fname__mark; reset_mark = __fname__reset_mark;
        commit_mark = __fname__commit_mark;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; is_trivial = __fname__is_trivial;
        finish = __fname__finish; refresh = __fname__refresh;_} ->
        __fname__reset_mark
  
let __proj__Mksolver_t__item__commit_mark :
  solver_t -> Prims.string -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        mark = __fname__mark; reset_mark = __fname__reset_mark;
        commit_mark = __fname__commit_mark;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; is_trivial = __fname__is_trivial;
        finish = __fname__finish; refresh = __fname__refresh;_} ->
        __fname__commit_mark
  
let __proj__Mksolver_t__item__encode_modul :
  solver_t -> env -> FStar_Syntax_Syntax.modul -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        mark = __fname__mark; reset_mark = __fname__reset_mark;
        commit_mark = __fname__commit_mark;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; is_trivial = __fname__is_trivial;
        finish = __fname__finish; refresh = __fname__refresh;_} ->
        __fname__encode_modul
  
let __proj__Mksolver_t__item__encode_sig :
  solver_t -> env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        mark = __fname__mark; reset_mark = __fname__reset_mark;
        commit_mark = __fname__commit_mark;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; is_trivial = __fname__is_trivial;
        finish = __fname__finish; refresh = __fname__refresh;_} ->
        __fname__encode_sig
  
let __proj__Mksolver_t__item__preprocess :
  solver_t ->
    env -> goal -> (env * goal * FStar_Options.optionstate) Prims.list
  =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        mark = __fname__mark; reset_mark = __fname__reset_mark;
        commit_mark = __fname__commit_mark;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; is_trivial = __fname__is_trivial;
        finish = __fname__finish; refresh = __fname__refresh;_} ->
        __fname__preprocess
  
let __proj__Mksolver_t__item__solve :
  solver_t ->
    (Prims.unit -> Prims.string) option ->
      env -> FStar_Syntax_Syntax.typ -> Prims.unit
  =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        mark = __fname__mark; reset_mark = __fname__reset_mark;
        commit_mark = __fname__commit_mark;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; is_trivial = __fname__is_trivial;
        finish = __fname__finish; refresh = __fname__refresh;_} ->
        __fname__solve
  
let __proj__Mksolver_t__item__is_trivial :
  solver_t -> env -> FStar_Syntax_Syntax.typ -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        mark = __fname__mark; reset_mark = __fname__reset_mark;
        commit_mark = __fname__commit_mark;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; is_trivial = __fname__is_trivial;
        finish = __fname__finish; refresh = __fname__refresh;_} ->
        __fname__is_trivial
  
let __proj__Mksolver_t__item__finish : solver_t -> Prims.unit -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        mark = __fname__mark; reset_mark = __fname__reset_mark;
        commit_mark = __fname__commit_mark;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; is_trivial = __fname__is_trivial;
        finish = __fname__finish; refresh = __fname__refresh;_} ->
        __fname__finish
  
let __proj__Mksolver_t__item__refresh : solver_t -> Prims.unit -> Prims.unit
  =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        mark = __fname__mark; reset_mark = __fname__reset_mark;
        commit_mark = __fname__commit_mark;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; is_trivial = __fname__is_trivial;
        finish = __fname__finish; refresh = __fname__refresh;_} ->
        __fname__refresh
  
let __proj__Mkguard_t__item__guard_f :
  guard_t -> FStar_TypeChecker_Common.guard_formula =
  fun projectee  ->
    match projectee with
    | { guard_f = __fname__guard_f; deferred = __fname__deferred;
        univ_ineqs = __fname__univ_ineqs; implicits = __fname__implicits;_}
        -> __fname__guard_f
  
let __proj__Mkguard_t__item__deferred :
  guard_t -> FStar_TypeChecker_Common.deferred =
  fun projectee  ->
    match projectee with
    | { guard_f = __fname__guard_f; deferred = __fname__deferred;
        univ_ineqs = __fname__univ_ineqs; implicits = __fname__implicits;_}
        -> __fname__deferred
  
let __proj__Mkguard_t__item__univ_ineqs :
  guard_t ->
    (FStar_Syntax_Syntax.universe Prims.list *
      FStar_TypeChecker_Common.univ_ineq Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { guard_f = __fname__guard_f; deferred = __fname__deferred;
        univ_ineqs = __fname__univ_ineqs; implicits = __fname__implicits;_}
        -> __fname__univ_ineqs
  
let __proj__Mkguard_t__item__implicits :
  guard_t ->
    (Prims.string * env * FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.term
      * FStar_Syntax_Syntax.typ * FStar_Range.range) Prims.list
  =
  fun projectee  ->
    match projectee with
    | { guard_f = __fname__guard_f; deferred = __fname__deferred;
        univ_ineqs = __fname__univ_ineqs; implicits = __fname__implicits;_}
        -> __fname__implicits
  
type implicits =
  (Prims.string * env * FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.term *
    FStar_Syntax_Syntax.typ * FStar_Range.range) Prims.list
type env_t = env
type sigtable = FStar_Syntax_Syntax.sigelt FStar_Util.smap
let should_verify : env -> Prims.bool =
  fun env  ->
    ((Prims.op_Negation env.lax) && (Prims.op_Negation env.admit)) &&
      (FStar_Options.should_verify (env.curmodule).FStar_Ident.str)
  
let visible_at : delta_level -> FStar_Syntax_Syntax.qualifier -> Prims.bool =
  fun d  ->
    fun q  ->
      match (d, q) with
      | (NoDelta ,uu____3489) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____3490,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) ->
          true
      | (Unfold uu____3491,FStar_Syntax_Syntax.Visible_default ) -> true
      | (Inlining ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____3492 -> false
  
let default_table_size : Prims.int = (Prims.parse_int "200") 
let new_sigtab uu____3504 = FStar_Util.smap_create default_table_size 
let new_gamma_cache uu____3514 =
  FStar_Util.smap_create (Prims.parse_int "100") 
let initial_env :
  (env ->
     FStar_Syntax_Syntax.term ->
       (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * guard_t))
    ->
    (env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe) ->
      solver_t -> FStar_Ident.lident -> env
  =
  fun type_of  ->
    fun universe_of  ->
      fun solver  ->
        fun module_lid  ->
          let uu____3557 = new_gamma_cache ()  in
          let uu____3559 = new_sigtab ()  in
          let uu____3561 =
            let uu____3562 = FStar_Options.using_facts_from ()  in
            match uu____3562 with
            | Some ns ->
                let uu____3568 =
                  let uu____3573 =
                    FStar_List.map
                      (fun s  -> ((FStar_Ident.path_of_text s), true)) ns
                     in
                  FStar_List.append uu____3573 [([], false)]  in
                [uu____3568]
            | None  -> [[]]  in
          {
            solver;
            range = FStar_Range.dummyRange;
            curmodule = module_lid;
            gamma = [];
            gamma_cache = uu____3557;
            modules = [];
            expected_typ = None;
            sigtab = uu____3559;
            is_pattern = false;
            instantiate_imp = true;
            effects = { decls = []; order = []; joins = [] };
            generalize = true;
            letrecs = [];
            top_level = false;
            check_uvars = false;
            use_eq = false;
            is_iface = false;
            admit = false;
            lax = false;
            lax_universes = false;
            type_of;
            universe_of;
            use_bv_sorts = false;
            qname_and_index = None;
            proof_ns = uu____3561;
            synth =
              (fun e  ->
                 fun g  -> fun tau  -> failwith "no synthesizer available");
            is_native_tactic = (fun uu____3625  -> false)
          }
  
let sigtab : env -> FStar_Syntax_Syntax.sigelt FStar_Util.smap =
  fun env  -> env.sigtab 
let gamma_cache : env -> cached_elt FStar_Util.smap =
  fun env  -> env.gamma_cache 
let query_indices :
  (FStar_Ident.lident * Prims.int) Prims.list Prims.list FStar_ST.ref =
  FStar_Util.mk_ref [[]] 
let push_query_indices : Prims.unit -> Prims.unit =
  fun uu____3658  ->
    let uu____3659 = FStar_ST.read query_indices  in
    match uu____3659 with
    | [] -> failwith "Empty query indices!"
    | uu____3673 ->
        let uu____3678 =
          let uu____3683 =
            let uu____3687 = FStar_ST.read query_indices  in
            FStar_List.hd uu____3687  in
          let uu____3701 = FStar_ST.read query_indices  in uu____3683 ::
            uu____3701
           in
        FStar_ST.write query_indices uu____3678
  
let pop_query_indices : Prims.unit -> Prims.unit =
  fun uu____3724  ->
    let uu____3725 = FStar_ST.read query_indices  in
    match uu____3725 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.write query_indices tl1
  
let add_query_index : (FStar_Ident.lident * Prims.int) -> Prims.unit =
  fun uu____3762  ->
    match uu____3762 with
    | (l,n1) ->
        let uu____3767 = FStar_ST.read query_indices  in
        (match uu____3767 with
         | hd1::tl1 -> FStar_ST.write query_indices (((l, n1) :: hd1) :: tl1)
         | uu____3801 -> failwith "Empty query indices")
  
let peek_query_indices :
  Prims.unit -> (FStar_Ident.lident * Prims.int) Prims.list =
  fun uu____3812  ->
    let uu____3813 = FStar_ST.read query_indices  in FStar_List.hd uu____3813
  
let commit_query_index_mark : Prims.unit -> Prims.unit =
  fun uu____3830  ->
    let uu____3831 = FStar_ST.read query_indices  in
    match uu____3831 with
    | hd1::uu____3843::tl1 -> FStar_ST.write query_indices (hd1 :: tl1)
    | uu____3870 -> failwith "Unmarked query index stack"
  
let stack : env Prims.list FStar_ST.ref = FStar_Util.mk_ref [] 
let push_stack : env -> env =
  fun env  ->
    (let uu____3885 =
       let uu____3887 = FStar_ST.read stack  in env :: uu____3887  in
     FStar_ST.write stack uu____3885);
    (let uu___114_3895 = env  in
     let uu____3896 = FStar_Util.smap_copy (gamma_cache env)  in
     let uu____3898 = FStar_Util.smap_copy (sigtab env)  in
     {
       solver = (uu___114_3895.solver);
       range = (uu___114_3895.range);
       curmodule = (uu___114_3895.curmodule);
       gamma = (uu___114_3895.gamma);
       gamma_cache = uu____3896;
       modules = (uu___114_3895.modules);
       expected_typ = (uu___114_3895.expected_typ);
       sigtab = uu____3898;
       is_pattern = (uu___114_3895.is_pattern);
       instantiate_imp = (uu___114_3895.instantiate_imp);
       effects = (uu___114_3895.effects);
       generalize = (uu___114_3895.generalize);
       letrecs = (uu___114_3895.letrecs);
       top_level = (uu___114_3895.top_level);
       check_uvars = (uu___114_3895.check_uvars);
       use_eq = (uu___114_3895.use_eq);
       is_iface = (uu___114_3895.is_iface);
       admit = (uu___114_3895.admit);
       lax = (uu___114_3895.lax);
       lax_universes = (uu___114_3895.lax_universes);
       type_of = (uu___114_3895.type_of);
       universe_of = (uu___114_3895.universe_of);
       use_bv_sorts = (uu___114_3895.use_bv_sorts);
       qname_and_index = (uu___114_3895.qname_and_index);
       proof_ns = (uu___114_3895.proof_ns);
       synth = (uu___114_3895.synth);
       is_native_tactic = (uu___114_3895.is_native_tactic)
     })
  
let pop_stack : Prims.unit -> env =
  fun uu____3903  ->
    let uu____3904 = FStar_ST.read stack  in
    match uu____3904 with
    | env::tl1 -> (FStar_ST.write stack tl1; env)
    | uu____3916 -> failwith "Impossible: Too many pops"
  
let cleanup_interactive : env -> Prims.unit = fun env  -> (env.solver).pop "" 
let push : env -> Prims.string -> env =
  fun env  ->
    fun msg  -> push_query_indices (); (env.solver).push msg; push_stack env
  
let pop : env -> Prims.string -> env =
  fun env  ->
    fun msg  -> (env.solver).pop msg; pop_query_indices (); pop_stack ()
  
let mark : env -> env =
  fun env  ->
    (env.solver).mark "USER MARK"; push_query_indices (); push_stack env
  
let commit_mark : env -> env =
  fun env  ->
    commit_query_index_mark ();
    (env.solver).commit_mark "USER MARK";
    (let uu____3955 = pop_stack ()  in ());
    env
  
let reset_mark : env -> env =
  fun env  ->
    (env.solver).reset_mark "USER MARK"; pop_query_indices (); pop_stack ()
  
let incr_query_index : env -> env =
  fun env  ->
    let qix = peek_query_indices ()  in
    match env.qname_and_index with
    | None  -> env
    | Some (l,n1) ->
        let uu____3976 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____3988  ->
                  match uu____3988 with
                  | (m,uu____3992) -> FStar_Ident.lid_equals l m))
           in
        (match uu____3976 with
         | None  ->
             let next = n1 + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              (let uu___115_3997 = env  in
               {
                 solver = (uu___115_3997.solver);
                 range = (uu___115_3997.range);
                 curmodule = (uu___115_3997.curmodule);
                 gamma = (uu___115_3997.gamma);
                 gamma_cache = (uu___115_3997.gamma_cache);
                 modules = (uu___115_3997.modules);
                 expected_typ = (uu___115_3997.expected_typ);
                 sigtab = (uu___115_3997.sigtab);
                 is_pattern = (uu___115_3997.is_pattern);
                 instantiate_imp = (uu___115_3997.instantiate_imp);
                 effects = (uu___115_3997.effects);
                 generalize = (uu___115_3997.generalize);
                 letrecs = (uu___115_3997.letrecs);
                 top_level = (uu___115_3997.top_level);
                 check_uvars = (uu___115_3997.check_uvars);
                 use_eq = (uu___115_3997.use_eq);
                 is_iface = (uu___115_3997.is_iface);
                 admit = (uu___115_3997.admit);
                 lax = (uu___115_3997.lax);
                 lax_universes = (uu___115_3997.lax_universes);
                 type_of = (uu___115_3997.type_of);
                 universe_of = (uu___115_3997.universe_of);
                 use_bv_sorts = (uu___115_3997.use_bv_sorts);
                 qname_and_index = (Some (l, next));
                 proof_ns = (uu___115_3997.proof_ns);
                 synth = (uu___115_3997.synth);
                 is_native_tactic = (uu___115_3997.is_native_tactic)
               }))
         | Some (uu____4000,m) ->
             let next = m + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              (let uu___116_4006 = env  in
               {
                 solver = (uu___116_4006.solver);
                 range = (uu___116_4006.range);
                 curmodule = (uu___116_4006.curmodule);
                 gamma = (uu___116_4006.gamma);
                 gamma_cache = (uu___116_4006.gamma_cache);
                 modules = (uu___116_4006.modules);
                 expected_typ = (uu___116_4006.expected_typ);
                 sigtab = (uu___116_4006.sigtab);
                 is_pattern = (uu___116_4006.is_pattern);
                 instantiate_imp = (uu___116_4006.instantiate_imp);
                 effects = (uu___116_4006.effects);
                 generalize = (uu___116_4006.generalize);
                 letrecs = (uu___116_4006.letrecs);
                 top_level = (uu___116_4006.top_level);
                 check_uvars = (uu___116_4006.check_uvars);
                 use_eq = (uu___116_4006.use_eq);
                 is_iface = (uu___116_4006.is_iface);
                 admit = (uu___116_4006.admit);
                 lax = (uu___116_4006.lax);
                 lax_universes = (uu___116_4006.lax_universes);
                 type_of = (uu___116_4006.type_of);
                 universe_of = (uu___116_4006.universe_of);
                 use_bv_sorts = (uu___116_4006.use_bv_sorts);
                 qname_and_index = (Some (l, next));
                 proof_ns = (uu___116_4006.proof_ns);
                 synth = (uu___116_4006.synth);
                 is_native_tactic = (uu___116_4006.is_native_tactic)
               })))
  
let debug : env -> FStar_Options.debug_level_t -> Prims.bool =
  fun env  ->
    fun l  -> FStar_Options.debug_at_level (env.curmodule).FStar_Ident.str l
  
let set_range : env -> FStar_Range.range -> env =
  fun e  ->
    fun r  ->
      if r = FStar_Range.dummyRange
      then e
      else
        (let uu___117_4026 = e  in
         {
           solver = (uu___117_4026.solver);
           range = r;
           curmodule = (uu___117_4026.curmodule);
           gamma = (uu___117_4026.gamma);
           gamma_cache = (uu___117_4026.gamma_cache);
           modules = (uu___117_4026.modules);
           expected_typ = (uu___117_4026.expected_typ);
           sigtab = (uu___117_4026.sigtab);
           is_pattern = (uu___117_4026.is_pattern);
           instantiate_imp = (uu___117_4026.instantiate_imp);
           effects = (uu___117_4026.effects);
           generalize = (uu___117_4026.generalize);
           letrecs = (uu___117_4026.letrecs);
           top_level = (uu___117_4026.top_level);
           check_uvars = (uu___117_4026.check_uvars);
           use_eq = (uu___117_4026.use_eq);
           is_iface = (uu___117_4026.is_iface);
           admit = (uu___117_4026.admit);
           lax = (uu___117_4026.lax);
           lax_universes = (uu___117_4026.lax_universes);
           type_of = (uu___117_4026.type_of);
           universe_of = (uu___117_4026.universe_of);
           use_bv_sorts = (uu___117_4026.use_bv_sorts);
           qname_and_index = (uu___117_4026.qname_and_index);
           proof_ns = (uu___117_4026.proof_ns);
           synth = (uu___117_4026.synth);
           is_native_tactic = (uu___117_4026.is_native_tactic)
         })
  
let get_range : env -> FStar_Range.range = fun e  -> e.range 
let modules : env -> FStar_Syntax_Syntax.modul Prims.list =
  fun env  -> env.modules 
let current_module : env -> FStar_Ident.lident = fun env  -> env.curmodule 
let set_current_module : env -> FStar_Ident.lident -> env =
  fun env  ->
    fun lid  ->
      let uu___118_4048 = env  in
      {
        solver = (uu___118_4048.solver);
        range = (uu___118_4048.range);
        curmodule = lid;
        gamma = (uu___118_4048.gamma);
        gamma_cache = (uu___118_4048.gamma_cache);
        modules = (uu___118_4048.modules);
        expected_typ = (uu___118_4048.expected_typ);
        sigtab = (uu___118_4048.sigtab);
        is_pattern = (uu___118_4048.is_pattern);
        instantiate_imp = (uu___118_4048.instantiate_imp);
        effects = (uu___118_4048.effects);
        generalize = (uu___118_4048.generalize);
        letrecs = (uu___118_4048.letrecs);
        top_level = (uu___118_4048.top_level);
        check_uvars = (uu___118_4048.check_uvars);
        use_eq = (uu___118_4048.use_eq);
        is_iface = (uu___118_4048.is_iface);
        admit = (uu___118_4048.admit);
        lax = (uu___118_4048.lax);
        lax_universes = (uu___118_4048.lax_universes);
        type_of = (uu___118_4048.type_of);
        universe_of = (uu___118_4048.universe_of);
        use_bv_sorts = (uu___118_4048.use_bv_sorts);
        qname_and_index = (uu___118_4048.qname_and_index);
        proof_ns = (uu___118_4048.proof_ns);
        synth = (uu___118_4048.synth);
        is_native_tactic = (uu___118_4048.is_native_tactic)
      }
  
let has_interface : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      FStar_All.pipe_right env.modules
        (FStar_Util.for_some
           (fun m  ->
              m.FStar_Syntax_Syntax.is_interface &&
                (FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name l)))
  
let find_in_sigtab :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.sigelt option =
  fun env  ->
    fun lid  ->
      FStar_Util.smap_try_find (sigtab env) (FStar_Ident.text_of_lid lid)
  
let name_not_found : FStar_Ident.lid -> Prims.string =
  fun l  -> FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str 
let variable_not_found : FStar_Syntax_Syntax.bv -> Prims.string =
  fun v1  ->
    let uu____4076 = FStar_Syntax_Print.bv_to_string v1  in
    FStar_Util.format1 "Variable \"%s\" not found" uu____4076
  
let new_u_univ : Prims.unit -> FStar_Syntax_Syntax.universe =
  fun uu____4080  ->
    let uu____4081 = FStar_Syntax_Unionfind.univ_fresh ()  in
    FStar_Syntax_Syntax.U_unif uu____4081
  
let inst_tscheme_with :
  FStar_Syntax_Syntax.tscheme ->
    FStar_Syntax_Syntax.universes ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term)
  =
  fun ts  ->
    fun us  ->
      match (ts, us) with
      | (([],t),[]) -> ([], t)
      | ((formals,t),uu____4105) ->
          let n1 = (FStar_List.length formals) - (Prims.parse_int "1")  in
          let vs =
            FStar_All.pipe_right us
              (FStar_List.mapi
                 (fun i  -> fun u  -> FStar_Syntax_Syntax.UN ((n1 - i), u)))
             in
          let uu____4124 = FStar_Syntax_Subst.subst vs t  in (us, uu____4124)
  
let inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term)
  =
  fun uu___102_4130  ->
    match uu___102_4130 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____4144  -> new_u_univ ()))
           in
        inst_tscheme_with (us, t) us'
  
let inst_tscheme_with_range :
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term)
  =
  fun r  ->
    fun t  ->
      let uu____4156 = inst_tscheme t  in
      match uu____4156 with
      | (us,t1) ->
          let uu____4163 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____4163)
  
let inst_effect_fun_with :
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____4179  ->
          match uu____4179 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us  in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____4197 =
                         let uu____4198 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1)
                            in
                         let uu____4203 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts)
                            in
                         let uu____4208 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname
                            in
                         let uu____4209 = FStar_Syntax_Print.term_to_string t
                            in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____4198 uu____4203 uu____4208 uu____4209
                          in
                       failwith uu____4197)
                    else ();
                    (let uu____4211 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts
                        in
                     snd uu____4211))
               | uu____4215 ->
                   let uu____4216 =
                     let uu____4217 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname
                        in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____4217
                      in
                   failwith uu____4216)
  
type tri =
  | Yes 
  | No 
  | Maybe 
let uu___is_Yes : tri -> Prims.bool =
  fun projectee  -> match projectee with | Yes  -> true | uu____4222 -> false 
let uu___is_No : tri -> Prims.bool =
  fun projectee  -> match projectee with | No  -> true | uu____4227 -> false 
let uu___is_Maybe : tri -> Prims.bool =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____4232 -> false
  
let in_cur_mod : env -> FStar_Ident.lident -> tri =
  fun env  ->
    fun l  ->
      let cur = current_module env  in
      if l.FStar_Ident.nsstr = cur.FStar_Ident.str
      then Yes
      else
        if FStar_Util.starts_with l.FStar_Ident.nsstr cur.FStar_Ident.str
        then
          (let lns = FStar_List.append l.FStar_Ident.ns [l.FStar_Ident.ident]
              in
           let cur1 =
             FStar_List.append cur.FStar_Ident.ns [cur.FStar_Ident.ident]  in
           let rec aux c l1 =
             match (c, l1) with
             | ([],uu____4260) -> Maybe
             | (uu____4264,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____4276 -> No  in
           aux cur1 lns)
        else No
  
let lookup_qname :
  env ->
    FStar_Ident.lident ->
      (((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ),(FStar_Syntax_Syntax.sigelt
                                                                    *
                                                                    FStar_Syntax_Syntax.universes
                                                                    option))
        FStar_Util.either * FStar_Range.range) option
  =
  fun env  ->
    fun lid  ->
      let cur_mod = in_cur_mod env lid  in
      let cache t =
        FStar_Util.smap_add (gamma_cache env) lid.FStar_Ident.str t; Some t
         in
      let found =
        if cur_mod <> No
        then
          let uu____4338 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str
             in
          match uu____4338 with
          | None  ->
              FStar_Util.find_map env.gamma
                (fun uu___103_4359  ->
                   match uu___103_4359 with
                   | Binding_lid (l,t) ->
                       if FStar_Ident.lid_equals lid l
                       then
                         let uu____4382 =
                           let uu____4392 =
                             let uu____4400 = inst_tscheme t  in
                             FStar_Util.Inl uu____4400  in
                           (uu____4392, (FStar_Ident.range_of_lid l))  in
                         Some uu____4382
                       else None
                   | Binding_sig
                       (uu____4434,{
                                     FStar_Syntax_Syntax.sigel =
                                       FStar_Syntax_Syntax.Sig_bundle
                                       (ses,uu____4436);
                                     FStar_Syntax_Syntax.sigrng = uu____4437;
                                     FStar_Syntax_Syntax.sigquals =
                                       uu____4438;
                                     FStar_Syntax_Syntax.sigmeta = uu____4439;
                                     FStar_Syntax_Syntax.sigattrs =
                                       uu____4440;_})
                       ->
                       FStar_Util.find_map ses
                         (fun se  ->
                            let uu____4450 =
                              FStar_All.pipe_right
                                (FStar_Syntax_Util.lids_of_sigelt se)
                                (FStar_Util.for_some
                                   (FStar_Ident.lid_equals lid))
                               in
                            if uu____4450
                            then
                              cache
                                ((FStar_Util.Inr (se, None)),
                                  (FStar_Syntax_Util.range_of_sigelt se))
                            else None)
                   | Binding_sig (lids,s) ->
                       let maybe_cache t =
                         match s.FStar_Syntax_Syntax.sigel with
                         | FStar_Syntax_Syntax.Sig_declare_typ uu____4477 ->
                             Some t
                         | uu____4481 -> cache t  in
                       let uu____4482 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids
                          in
                       (match uu____4482 with
                        | None  -> None
                        | Some l ->
                            maybe_cache
                              ((FStar_Util.Inr (s, None)),
                                (FStar_Ident.range_of_lid l)))
                   | Binding_sig_inst (lids,s,us) ->
                       let uu____4522 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids
                          in
                       (match uu____4522 with
                        | None  -> None
                        | Some l ->
                            Some
                              ((FStar_Util.Inr (s, (Some us))),
                                (FStar_Ident.range_of_lid l)))
                   | uu____4566 -> None)
          | se -> se
        else None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____4608 =
           (cur_mod <> Yes) || (has_interface env env.curmodule)  in
         if uu____4608
         then
           let uu____4619 = find_in_sigtab env lid  in
           match uu____4619 with
           | Some se ->
               Some
                 ((FStar_Util.Inr (se, None)),
                   (FStar_Syntax_Util.range_of_sigelt se))
           | None  -> None
         else None)
  
let rec add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____4685) ->
          add_sigelts env ses
      | uu____4690 ->
          let lids = FStar_Syntax_Util.lids_of_sigelt se  in
          (FStar_List.iter
             (fun l  -> FStar_Util.smap_add (sigtab env) l.FStar_Ident.str se)
             lids;
           (match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_new_effect ne ->
                FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions
                  (FStar_List.iter
                     (fun a  ->
                        let se_let =
                          FStar_Syntax_Util.action_as_lb
                            ne.FStar_Syntax_Syntax.mname a
                           in
                        FStar_Util.smap_add (sigtab env)
                          (a.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                          se_let))
            | uu____4699 -> ()))

and add_sigelts : env -> FStar_Syntax_Syntax.sigelt Prims.list -> Prims.unit
  =
  fun env  ->
    fun ses  -> FStar_All.pipe_right ses (FStar_List.iter (add_sigelt env))

let try_lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv ->
      ((FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax * FStar_Range.range) option
  =
  fun env  ->
    fun bv  ->
      FStar_Util.find_map env.gamma
        (fun uu___104_4719  ->
           match uu___104_4719 with
           | Binding_var id when FStar_Syntax_Syntax.bv_eq id bv ->
               Some
                 ((id.FStar_Syntax_Syntax.sort),
                   ((id.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____4732 -> None)
  
let lookup_type_of_let :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) *
        FStar_Range.range) option
  =
  fun se  ->
    fun lid  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_let ((uu____4755,lb::[]),uu____4757) ->
          let uu____4764 =
            let uu____4769 =
              inst_tscheme
                ((lb.FStar_Syntax_Syntax.lbunivs),
                  (lb.FStar_Syntax_Syntax.lbtyp))
               in
            let uu____4775 =
              FStar_Syntax_Syntax.range_of_lbname
                lb.FStar_Syntax_Syntax.lbname
               in
            (uu____4769, uu____4775)  in
          Some uu____4764
      | FStar_Syntax_Syntax.Sig_let ((uu____4782,lbs),uu____4784) ->
          FStar_Util.find_map lbs
            (fun lb  ->
               match lb.FStar_Syntax_Syntax.lbname with
               | FStar_Util.Inl uu____4802 -> failwith "impossible"
               | FStar_Util.Inr fv ->
                   let uu____4809 = FStar_Syntax_Syntax.fv_eq_lid fv lid  in
                   if uu____4809
                   then
                     let uu____4815 =
                       let uu____4820 =
                         inst_tscheme
                           ((lb.FStar_Syntax_Syntax.lbunivs),
                             (lb.FStar_Syntax_Syntax.lbtyp))
                          in
                       let uu____4826 = FStar_Syntax_Syntax.range_of_fv fv
                          in
                       (uu____4820, uu____4826)  in
                     Some uu____4815
                   else None)
      | uu____4838 -> None
  
let effect_signature :
  FStar_Syntax_Syntax.sigelt ->
    ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) *
      FStar_Range.range) option
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne ->
        let uu____4858 =
          let uu____4863 =
            let uu____4866 =
              let uu____4867 =
                let uu____4870 =
                  FStar_Syntax_Syntax.mk_Total
                    ne.FStar_Syntax_Syntax.signature
                   in
                FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                  uu____4870
                 in
              ((ne.FStar_Syntax_Syntax.univs), uu____4867)  in
            inst_tscheme uu____4866  in
          (uu____4863, (se.FStar_Syntax_Syntax.sigrng))  in
        Some uu____4858
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,us,binders,uu____4884,uu____4885) ->
        let uu____4888 =
          let uu____4893 =
            let uu____4896 =
              let uu____4897 =
                let uu____4900 =
                  FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff  in
                FStar_Syntax_Util.arrow binders uu____4900  in
              (us, uu____4897)  in
            inst_tscheme uu____4896  in
          (uu____4893, (se.FStar_Syntax_Syntax.sigrng))  in
        Some uu____4888
    | uu____4911 -> None
  
let try_lookup_lid_aux :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes *
        (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax) * FStar_Range.range) option
  =
  fun env  ->
    fun lid  ->
      let mapper uu____4948 =
        match uu____4948 with
        | (lr,rng) ->
            (match lr with
             | FStar_Util.Inl t -> Some (t, rng)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_datacon
                      (uu____4998,uvs,t,uu____5001,uu____5002,uu____5003);
                    FStar_Syntax_Syntax.sigrng = uu____5004;
                    FStar_Syntax_Syntax.sigquals = uu____5005;
                    FStar_Syntax_Syntax.sigmeta = uu____5006;
                    FStar_Syntax_Syntax.sigattrs = uu____5007;_},None
                  )
                 ->
                 let uu____5018 =
                   let uu____5023 = inst_tscheme (uvs, t)  in
                   (uu____5023, rng)  in
                 Some uu____5018
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                    FStar_Syntax_Syntax.sigrng = uu____5035;
                    FStar_Syntax_Syntax.sigquals = qs;
                    FStar_Syntax_Syntax.sigmeta = uu____5037;
                    FStar_Syntax_Syntax.sigattrs = uu____5038;_},None
                  )
                 ->
                 let uu____5047 =
                   let uu____5048 = in_cur_mod env l  in uu____5048 = Yes  in
                 if uu____5047
                 then
                   let uu____5054 =
                     (FStar_All.pipe_right qs
                        (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                       || env.is_iface
                      in
                   (if uu____5054
                    then
                      let uu____5061 =
                        let uu____5066 = inst_tscheme (uvs, t)  in
                        (uu____5066, rng)  in
                      Some uu____5061
                    else None)
                 else
                   (let uu____5081 =
                      let uu____5086 = inst_tscheme (uvs, t)  in
                      (uu____5086, rng)  in
                    Some uu____5081)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____5099,uu____5100);
                    FStar_Syntax_Syntax.sigrng = uu____5101;
                    FStar_Syntax_Syntax.sigquals = uu____5102;
                    FStar_Syntax_Syntax.sigmeta = uu____5103;
                    FStar_Syntax_Syntax.sigattrs = uu____5104;_},None
                  )
                 ->
                 (match tps with
                  | [] ->
                      let uu____5124 =
                        let uu____5129 = inst_tscheme (uvs, k)  in
                        (uu____5129, rng)  in
                      Some uu____5124
                  | uu____5138 ->
                      let uu____5139 =
                        let uu____5144 =
                          let uu____5147 =
                            let uu____5148 =
                              let uu____5151 = FStar_Syntax_Syntax.mk_Total k
                                 in
                              FStar_Syntax_Util.flat_arrow tps uu____5151  in
                            (uvs, uu____5148)  in
                          inst_tscheme uu____5147  in
                        (uu____5144, rng)  in
                      Some uu____5139)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____5166,uu____5167);
                    FStar_Syntax_Syntax.sigrng = uu____5168;
                    FStar_Syntax_Syntax.sigquals = uu____5169;
                    FStar_Syntax_Syntax.sigmeta = uu____5170;
                    FStar_Syntax_Syntax.sigattrs = uu____5171;_},Some
                  us)
                 ->
                 (match tps with
                  | [] ->
                      let uu____5192 =
                        let uu____5197 = inst_tscheme_with (uvs, k) us  in
                        (uu____5197, rng)  in
                      Some uu____5192
                  | uu____5206 ->
                      let uu____5207 =
                        let uu____5212 =
                          let uu____5215 =
                            let uu____5216 =
                              let uu____5219 = FStar_Syntax_Syntax.mk_Total k
                                 in
                              FStar_Syntax_Util.flat_arrow tps uu____5219  in
                            (uvs, uu____5216)  in
                          inst_tscheme_with uu____5215 us  in
                        (uu____5212, rng)  in
                      Some uu____5207)
             | FStar_Util.Inr se ->
                 let uu____5239 =
                   match se with
                   | ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let uu____5250;
                        FStar_Syntax_Syntax.sigrng = uu____5251;
                        FStar_Syntax_Syntax.sigquals = uu____5252;
                        FStar_Syntax_Syntax.sigmeta = uu____5253;
                        FStar_Syntax_Syntax.sigattrs = uu____5254;_},None
                      ) -> lookup_type_of_let (fst se) lid
                   | uu____5262 -> effect_signature (fst se)  in
                 FStar_All.pipe_right uu____5239
                   (FStar_Util.map_option
                      (fun uu____5285  ->
                         match uu____5285 with | (us_t,rng1) -> (us_t, rng1))))
         in
      let uu____5302 =
        let uu____5308 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____5308 mapper  in
      match uu____5302 with
      | Some ((us,t),r) ->
          Some
            ((us,
               (let uu___119_5360 = t  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___119_5360.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___119_5360.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid);
                  FStar_Syntax_Syntax.vars =
                    (uu___119_5360.FStar_Syntax_Syntax.vars)
                })), r)
      | None  -> None
  
let lid_exists : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____5383 = lookup_qname env l  in
      match uu____5383 with | None  -> false | Some uu____5403 -> true
  
let lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv -> (FStar_Syntax_Syntax.typ * FStar_Range.range)
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____5433 = try_lookup_bv env bv  in
      match uu____5433 with
      | None  ->
          let uu____5441 =
            let uu____5442 =
              let uu____5445 = variable_not_found bv  in (uu____5445, bvr)
               in
            FStar_Errors.Error uu____5442  in
          raise uu____5441
      | Some (t,r) ->
          let uu____5452 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____5453 = FStar_Range.set_use_range r bvr  in
          (uu____5452, uu____5453)
  
let try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range) option
  =
  fun env  ->
    fun l  ->
      let uu____5467 = try_lookup_lid_aux env l  in
      match uu____5467 with
      | None  -> None
      | Some ((us,t),r) ->
          let use_range = FStar_Ident.range_of_lid l  in
          let r1 = FStar_Range.set_use_range r use_range  in
          let uu____5509 =
            let uu____5514 =
              let uu____5517 = FStar_Syntax_Subst.set_use_range use_range t
                 in
              (us, uu____5517)  in
            (uu____5514, r1)  in
          Some uu____5509
  
let lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range)
  =
  fun env  ->
    fun l  ->
      let uu____5536 = try_lookup_lid env l  in
      match uu____5536 with
      | None  ->
          let uu____5550 =
            let uu____5551 =
              let uu____5554 = name_not_found l  in
              (uu____5554, (FStar_Ident.range_of_lid l))  in
            FStar_Errors.Error uu____5551  in
          raise uu____5550
      | Some v1 -> v1
  
let lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___105_5577  ->
              match uu___105_5577 with
              | Binding_univ y -> x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____5579 -> false) env.gamma) FStar_Option.isSome
  
let try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier
        Prims.list) option
  =
  fun env  ->
    fun lid  ->
      let uu____5592 = lookup_qname env lid  in
      match uu____5592 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____5607,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____5610;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____5612;
              FStar_Syntax_Syntax.sigattrs = uu____5613;_},None
            ),uu____5614)
          ->
          let uu____5639 =
            let uu____5645 =
              let uu____5648 =
                FStar_Syntax_Subst.set_use_range
                  (FStar_Ident.range_of_lid lid) t
                 in
              (uvs, uu____5648)  in
            (uu____5645, q)  in
          Some uu____5639
      | uu____5657 -> None
  
let lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun lid  ->
      let uu____5681 = lookup_qname env lid  in
      match uu____5681 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____5694,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____5697;
              FStar_Syntax_Syntax.sigquals = uu____5698;
              FStar_Syntax_Syntax.sigmeta = uu____5699;
              FStar_Syntax_Syntax.sigattrs = uu____5700;_},None
            ),uu____5701)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____5726 ->
          let uu____5737 =
            let uu____5738 =
              let uu____5741 = name_not_found lid  in
              (uu____5741, (FStar_Ident.range_of_lid lid))  in
            FStar_Errors.Error uu____5738  in
          raise uu____5737
  
let lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun lid  ->
      let uu____5754 = lookup_qname env lid  in
      match uu____5754 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____5767,uvs,t,uu____5770,uu____5771,uu____5772);
              FStar_Syntax_Syntax.sigrng = uu____5773;
              FStar_Syntax_Syntax.sigquals = uu____5774;
              FStar_Syntax_Syntax.sigmeta = uu____5775;
              FStar_Syntax_Syntax.sigattrs = uu____5776;_},None
            ),uu____5777)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____5804 ->
          let uu____5815 =
            let uu____5816 =
              let uu____5819 = name_not_found lid  in
              (uu____5819, (FStar_Ident.range_of_lid lid))  in
            FStar_Errors.Error uu____5816  in
          raise uu____5815
  
let datacons_of_typ :
  env -> FStar_Ident.lident -> (Prims.bool * FStar_Ident.lident Prims.list) =
  fun env  ->
    fun lid  ->
      let uu____5833 = lookup_qname env lid  in
      match uu____5833 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____5847,uu____5848,uu____5849,uu____5850,uu____5851,dcs);
              FStar_Syntax_Syntax.sigrng = uu____5853;
              FStar_Syntax_Syntax.sigquals = uu____5854;
              FStar_Syntax_Syntax.sigmeta = uu____5855;
              FStar_Syntax_Syntax.sigattrs = uu____5856;_},uu____5857),uu____5858)
          -> (true, dcs)
      | uu____5889 -> (false, [])
  
let typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      let uu____5909 = lookup_qname env lid  in
      match uu____5909 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____5920,uu____5921,uu____5922,l,uu____5924,uu____5925);
              FStar_Syntax_Syntax.sigrng = uu____5926;
              FStar_Syntax_Syntax.sigquals = uu____5927;
              FStar_Syntax_Syntax.sigmeta = uu____5928;
              FStar_Syntax_Syntax.sigattrs = uu____5929;_},uu____5930),uu____5931)
          -> l
      | uu____5959 ->
          let uu____5970 =
            let uu____5971 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____5971  in
          failwith uu____5970
  
let lookup_definition :
  delta_level Prims.list ->
    env ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term) option
  =
  fun delta_levels  ->
    fun env  ->
      fun lid  ->
        let visible quals =
          FStar_All.pipe_right delta_levels
            (FStar_Util.for_some
               (fun dl  ->
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some (visible_at dl))))
           in
        let uu____5998 = lookup_qname env lid  in
        match uu____5998 with
        | Some (FStar_Util.Inr (se,None ),uu____6013) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_let ((uu____6039,lbs),uu____6041) when
                 visible se.FStar_Syntax_Syntax.sigquals ->
                 FStar_Util.find_map lbs
                   (fun lb  ->
                      let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                         in
                      let uu____6056 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                         in
                      if uu____6056
                      then
                        Some
                          ((lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbdef))
                      else None)
             | uu____6077 -> None)
        | uu____6080 -> None
  
let try_lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.typ option =
  fun env  ->
    fun ftv  ->
      let uu____6103 = lookup_qname env ftv  in
      match uu____6103 with
      | Some (FStar_Util.Inr (se,None ),uu____6116) ->
          let uu____6139 = effect_signature se  in
          (match uu____6139 with
           | None  -> None
           | Some ((uu____6150,t),r) ->
               let uu____6159 =
                 FStar_Syntax_Subst.set_use_range
                   (FStar_Ident.range_of_lid ftv) t
                  in
               Some uu____6159)
      | uu____6160 -> None
  
let lookup_effect_lid : env -> FStar_Ident.lident -> FStar_Syntax_Syntax.typ
  =
  fun env  ->
    fun ftv  ->
      let uu____6179 = try_lookup_effect_lid env ftv  in
      match uu____6179 with
      | None  ->
          let uu____6181 =
            let uu____6182 =
              let uu____6185 = name_not_found ftv  in
              (uu____6185, (FStar_Ident.range_of_lid ftv))  in
            FStar_Errors.Error uu____6182  in
          raise uu____6181
      | Some k -> k
  
let lookup_effect_abbrev :
  env ->
    FStar_Syntax_Syntax.universes ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) option
  =
  fun env  ->
    fun univ_insts  ->
      fun lid0  ->
        let uu____6202 = lookup_qname env lid0  in
        match uu____6202 with
        | Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____6220);
                FStar_Syntax_Syntax.sigrng = uu____6221;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____6223;
                FStar_Syntax_Syntax.sigattrs = uu____6224;_},None
              ),uu____6225)
            ->
            let lid1 =
              let uu____6253 =
                FStar_Range.set_use_range (FStar_Ident.range_of_lid lid)
                  (FStar_Ident.range_of_lid lid0)
                 in
              FStar_Ident.set_lid_range lid uu____6253  in
            let uu____6254 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___106_6256  ->
                      match uu___106_6256 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____6257 -> false))
               in
            if uu____6254
            then None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____6274 =
                      let uu____6275 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____6276 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format2
                        "Unexpected instantiation of effect %s with %s universes"
                        uu____6275 uu____6276
                       in
                    failwith uu____6274)
                  in
               match (binders, univs1) with
               | ([],uu____6284) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____6293,uu____6294::uu____6295::uu____6296) ->
                   let uu____6299 =
                     let uu____6300 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____6301 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____6300 uu____6301
                      in
                   failwith uu____6299
               | uu____6309 ->
                   let uu____6312 =
                     let uu____6315 =
                       let uu____6316 = FStar_Syntax_Util.arrow binders c  in
                       (univs1, uu____6316)  in
                     inst_tscheme_with uu____6315 insts  in
                   (match uu____6312 with
                    | (uu____6324,t) ->
                        let t1 =
                          FStar_Syntax_Subst.set_use_range
                            (FStar_Ident.range_of_lid lid1) t
                           in
                        let uu____6327 =
                          let uu____6328 = FStar_Syntax_Subst.compress t1  in
                          uu____6328.FStar_Syntax_Syntax.n  in
                        (match uu____6327 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             Some (binders1, c1)
                         | uu____6358 -> failwith "Impossible")))
        | uu____6362 -> None
  
let norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident =
  let cache = FStar_Util.smap_create (Prims.parse_int "20")  in
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____6390 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____6390 with
        | None  -> None
        | Some (uu____6397,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____6402 = find1 l2  in
            (match uu____6402 with | None  -> Some l2 | Some l' -> Some l')
         in
      let res =
        let uu____6407 = FStar_Util.smap_try_find cache l.FStar_Ident.str  in
        match uu____6407 with
        | Some l1 -> l1
        | None  ->
            let uu____6410 = find1 l  in
            (match uu____6410 with
             | None  -> l
             | Some m -> (FStar_Util.smap_add cache l.FStar_Ident.str m; m))
         in
      FStar_Ident.set_lid_range res (FStar_Ident.range_of_lid l)
  
let lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l  in
      let uu____6424 = lookup_qname env l1  in
      match uu____6424 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____6436;
              FStar_Syntax_Syntax.sigrng = uu____6437;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____6439;
              FStar_Syntax_Syntax.sigattrs = uu____6440;_},uu____6441),uu____6442)
          -> q
      | uu____6468 -> []
  
let lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail uu____6494 =
          let uu____6495 =
            let uu____6496 = FStar_Util.string_of_int i  in
            let uu____6497 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____6496 uu____6497
             in
          failwith uu____6495  in
        let uu____6498 = lookup_datacon env lid  in
        match uu____6498 with
        | (uu____6501,t) ->
            let uu____6503 =
              let uu____6504 = FStar_Syntax_Subst.compress t  in
              uu____6504.FStar_Syntax_Syntax.n  in
            (match uu____6503 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____6508) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let uu____6531 =
                      FStar_Syntax_Util.mk_field_projector_name lid (fst b) i
                       in
                    FStar_All.pipe_right uu____6531 FStar_Pervasives.fst)
             | uu____6536 -> fail ())
  
let is_projector : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____6545 = lookup_qname env l  in
      match uu____6545 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____6556,uu____6557,uu____6558);
              FStar_Syntax_Syntax.sigrng = uu____6559;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____6561;
              FStar_Syntax_Syntax.sigattrs = uu____6562;_},uu____6563),uu____6564)
          ->
          FStar_Util.for_some
            (fun uu___107_6590  ->
               match uu___107_6590 with
               | FStar_Syntax_Syntax.Projector uu____6591 -> true
               | uu____6594 -> false) quals
      | uu____6595 -> false
  
let is_datacon : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____6614 = lookup_qname env lid  in
      match uu____6614 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____6625,uu____6626,uu____6627,uu____6628,uu____6629,uu____6630);
              FStar_Syntax_Syntax.sigrng = uu____6631;
              FStar_Syntax_Syntax.sigquals = uu____6632;
              FStar_Syntax_Syntax.sigmeta = uu____6633;
              FStar_Syntax_Syntax.sigattrs = uu____6634;_},uu____6635),uu____6636)
          -> true
      | uu____6664 -> false
  
let is_record : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____6683 = lookup_qname env lid  in
      match uu____6683 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____6694,uu____6695,uu____6696,uu____6697,uu____6698,uu____6699);
              FStar_Syntax_Syntax.sigrng = uu____6700;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____6702;
              FStar_Syntax_Syntax.sigattrs = uu____6703;_},uu____6704),uu____6705)
          ->
          FStar_Util.for_some
            (fun uu___108_6735  ->
               match uu___108_6735 with
               | FStar_Syntax_Syntax.RecordType uu____6736 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____6741 -> true
               | uu____6746 -> false) quals
      | uu____6747 -> false
  
let is_action : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____6766 = lookup_qname env lid  in
      match uu____6766 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                (uu____6777,uu____6778);
              FStar_Syntax_Syntax.sigrng = uu____6779;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____6781;
              FStar_Syntax_Syntax.sigattrs = uu____6782;_},uu____6783),uu____6784)
          ->
          FStar_Util.for_some
            (fun uu___109_6812  ->
               match uu___109_6812 with
               | FStar_Syntax_Syntax.Action uu____6813 -> true
               | uu____6814 -> false) quals
      | uu____6815 -> false
  
let is_interpreted : env -> FStar_Syntax_Syntax.term -> Prims.bool =
  let interpreted_symbols =
    [FStar_Syntax_Const.op_Eq;
    FStar_Syntax_Const.op_notEq;
    FStar_Syntax_Const.op_LT;
    FStar_Syntax_Const.op_LTE;
    FStar_Syntax_Const.op_GT;
    FStar_Syntax_Const.op_GTE;
    FStar_Syntax_Const.op_Subtraction;
    FStar_Syntax_Const.op_Minus;
    FStar_Syntax_Const.op_Addition;
    FStar_Syntax_Const.op_Multiply;
    FStar_Syntax_Const.op_Division;
    FStar_Syntax_Const.op_Modulus;
    FStar_Syntax_Const.op_And;
    FStar_Syntax_Const.op_Or;
    FStar_Syntax_Const.op_Negation]  in
  fun env  ->
    fun head1  ->
      let uu____6836 =
        let uu____6837 = FStar_Syntax_Util.un_uinst head1  in
        uu____6837.FStar_Syntax_Syntax.n  in
      match uu____6836 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          fv.FStar_Syntax_Syntax.fv_delta =
            FStar_Syntax_Syntax.Delta_equational
      | uu____6841 -> false
  
let is_type_constructor : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let mapper x =
        match fst x with
        | FStar_Util.Inl uu____6881 -> Some false
        | FStar_Util.Inr (se,uu____6890) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____6899 ->
                 Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____6903 -> Some true
             | uu____6912 -> Some false)
         in
      let uu____6913 =
        let uu____6915 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____6915 mapper  in
      match uu____6913 with | Some b -> b | None  -> false
  
let num_inductive_ty_params : env -> FStar_Ident.lident -> Prims.int =
  fun env  ->
    fun lid  ->
      let uu____6944 = lookup_qname env lid  in
      match uu____6944 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____6955,uu____6956,tps,uu____6958,uu____6959,uu____6960);
              FStar_Syntax_Syntax.sigrng = uu____6961;
              FStar_Syntax_Syntax.sigquals = uu____6962;
              FStar_Syntax_Syntax.sigmeta = uu____6963;
              FStar_Syntax_Syntax.sigattrs = uu____6964;_},uu____6965),uu____6966)
          -> FStar_List.length tps
      | uu____7000 ->
          let uu____7011 =
            let uu____7012 =
              let uu____7015 = name_not_found lid  in
              (uu____7015, (FStar_Ident.range_of_lid lid))  in
            FStar_Errors.Error uu____7012  in
          raise uu____7011
  
let effect_decl_opt :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.qualifier
        Prims.list) option
  =
  fun env  ->
    fun l  ->
      FStar_All.pipe_right (env.effects).decls
        (FStar_Util.find_opt
           (fun uu____7039  ->
              match uu____7039 with
              | (d,uu____7044) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl =
  fun env  ->
    fun l  ->
      let uu____7055 = effect_decl_opt env l  in
      match uu____7055 with
      | None  ->
          let uu____7063 =
            let uu____7064 =
              let uu____7067 = name_not_found l  in
              (uu____7067, (FStar_Ident.range_of_lid l))  in
            FStar_Errors.Error uu____7064  in
          raise uu____7063
      | Some md -> fst md
  
let identity_mlift : mlift =
  {
    mlift_wp = (fun t  -> fun wp  -> wp);
    mlift_term = (Some (fun t  -> fun wp  -> fun e  -> e))
  } 
let join :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> (FStar_Ident.lident * mlift * mlift)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        if FStar_Ident.lid_equals l1 l2
        then (l1, identity_mlift, identity_mlift)
        else
          if
            ((FStar_Ident.lid_equals l1 FStar_Syntax_Const.effect_GTot_lid)
               &&
               (FStar_Ident.lid_equals l2 FStar_Syntax_Const.effect_Tot_lid))
              ||
              ((FStar_Ident.lid_equals l2 FStar_Syntax_Const.effect_GTot_lid)
                 &&
                 (FStar_Ident.lid_equals l1 FStar_Syntax_Const.effect_Tot_lid))
          then
            (FStar_Syntax_Const.effect_GTot_lid, identity_mlift,
              identity_mlift)
          else
            (let uu____7113 =
               FStar_All.pipe_right (env.effects).joins
                 (FStar_Util.find_opt
                    (fun uu____7137  ->
                       match uu____7137 with
                       | (m1,m2,uu____7145,uu____7146,uu____7147) ->
                           (FStar_Ident.lid_equals l1 m1) &&
                             (FStar_Ident.lid_equals l2 m2)))
                in
             match uu____7113 with
             | None  ->
                 let uu____7156 =
                   let uu____7157 =
                     let uu____7160 =
                       let uu____7161 = FStar_Syntax_Print.lid_to_string l1
                          in
                       let uu____7162 = FStar_Syntax_Print.lid_to_string l2
                          in
                       FStar_Util.format2
                         "Effects %s and %s cannot be composed" uu____7161
                         uu____7162
                        in
                     (uu____7160, (env.range))  in
                   FStar_Errors.Error uu____7157  in
                 raise uu____7156
             | Some (uu____7166,uu____7167,m3,j1,j2) -> (m3, j1, j2))
  
let monad_leq :
  env -> FStar_Ident.lident -> FStar_Ident.lident -> edge option =
  fun env  ->
    fun l1  ->
      fun l2  ->
        if
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Syntax_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Syntax_Const.effect_GTot_lid))
        then Some { msource = l1; mtarget = l2; mlift = identity_mlift }
        else
          FStar_All.pipe_right (env.effects).order
            (FStar_Util.find_opt
               (fun e  ->
                  (FStar_Ident.lid_equals l1 e.msource) &&
                    (FStar_Ident.lid_equals l2 e.mtarget)))
  
let wp_sig_aux decls m =
  let uu____7220 =
    FStar_All.pipe_right decls
      (FStar_Util.find_opt
         (fun uu____7232  ->
            match uu____7232 with
            | (d,uu____7236) ->
                FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
     in
  match uu____7220 with
  | None  ->
      let uu____7243 =
        FStar_Util.format1 "Impossible: declaration for monad %s not found"
          m.FStar_Ident.str
         in
      failwith uu____7243
  | Some (md,_q) ->
      let uu____7252 =
        inst_tscheme
          ((md.FStar_Syntax_Syntax.univs),
            (md.FStar_Syntax_Syntax.signature))
         in
      (match uu____7252 with
       | (uu____7259,s) ->
           let s1 = FStar_Syntax_Subst.compress s  in
           (match ((md.FStar_Syntax_Syntax.binders),
                    (s1.FStar_Syntax_Syntax.n))
            with
            | ([],FStar_Syntax_Syntax.Tm_arrow
               ((a,uu____7267)::(wp,uu____7269)::[],c)) when
                FStar_Syntax_Syntax.is_teff (FStar_Syntax_Util.comp_result c)
                -> (a, (wp.FStar_Syntax_Syntax.sort))
            | uu____7291 -> failwith "Impossible"))
  
let wp_signature :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.bv *
        (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax)
  = fun env  -> fun m  -> wp_sig_aux (env.effects).decls m 
let null_wp_for_eff :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.comp
  =
  fun env  ->
    fun eff_name  ->
      fun res_u  ->
        fun res_t  ->
          if
            FStar_Ident.lid_equals eff_name FStar_Syntax_Const.effect_Tot_lid
          then FStar_Syntax_Syntax.mk_Total' res_t (Some res_u)
          else
            if
              FStar_Ident.lid_equals eff_name
                FStar_Syntax_Const.effect_GTot_lid
            then FStar_Syntax_Syntax.mk_GTotal' res_t (Some res_u)
            else
              (let eff_name1 = norm_eff_name env eff_name  in
               let ed = get_effect_decl env eff_name1  in
               let null_wp =
                 inst_effect_fun_with [res_u] env ed
                   ed.FStar_Syntax_Syntax.null_wp
                  in
               let null_wp_res =
                 let uu____7333 = get_range env  in
                 let uu____7334 =
                   let uu____7337 =
                     let uu____7338 =
                       let uu____7348 =
                         let uu____7350 = FStar_Syntax_Syntax.as_arg res_t
                            in
                         [uu____7350]  in
                       (null_wp, uu____7348)  in
                     FStar_Syntax_Syntax.Tm_app uu____7338  in
                   FStar_Syntax_Syntax.mk uu____7337  in
                 uu____7334 None uu____7333  in
               let uu____7360 =
                 let uu____7361 =
                   let uu____7367 = FStar_Syntax_Syntax.as_arg null_wp_res
                      in
                   [uu____7367]  in
                 {
                   FStar_Syntax_Syntax.comp_univs = [res_u];
                   FStar_Syntax_Syntax.effect_name = eff_name1;
                   FStar_Syntax_Syntax.result_typ = res_t;
                   FStar_Syntax_Syntax.effect_args = uu____7361;
                   FStar_Syntax_Syntax.flags = []
                 }  in
               FStar_Syntax_Syntax.mk_Comp uu____7360)
  
let build_lattice : env -> FStar_Syntax_Syntax.sigelt -> env =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___120_7378 = env.effects  in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___120_7378.order);
              joins = (uu___120_7378.joins)
            }  in
          let uu___121_7383 = env  in
          {
            solver = (uu___121_7383.solver);
            range = (uu___121_7383.range);
            curmodule = (uu___121_7383.curmodule);
            gamma = (uu___121_7383.gamma);
            gamma_cache = (uu___121_7383.gamma_cache);
            modules = (uu___121_7383.modules);
            expected_typ = (uu___121_7383.expected_typ);
            sigtab = (uu___121_7383.sigtab);
            is_pattern = (uu___121_7383.is_pattern);
            instantiate_imp = (uu___121_7383.instantiate_imp);
            effects;
            generalize = (uu___121_7383.generalize);
            letrecs = (uu___121_7383.letrecs);
            top_level = (uu___121_7383.top_level);
            check_uvars = (uu___121_7383.check_uvars);
            use_eq = (uu___121_7383.use_eq);
            is_iface = (uu___121_7383.is_iface);
            admit = (uu___121_7383.admit);
            lax = (uu___121_7383.lax);
            lax_universes = (uu___121_7383.lax_universes);
            type_of = (uu___121_7383.type_of);
            universe_of = (uu___121_7383.universe_of);
            use_bv_sorts = (uu___121_7383.use_bv_sorts);
            qname_and_index = (uu___121_7383.qname_and_index);
            proof_ns = (uu___121_7383.proof_ns);
            synth = (uu___121_7383.synth);
            is_native_tactic = (uu___121_7383.is_native_tactic)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp r wp1 =
                let uu____7400 = (e1.mlift).mlift_wp r wp1  in
                (e2.mlift).mlift_wp r uu____7400  in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (Some l1,Some l2) ->
                    Some
                      ((fun t  ->
                          fun wp  ->
                            fun e  ->
                              let uu____7479 = (e1.mlift).mlift_wp t wp  in
                              let uu____7480 = l1 t wp e  in
                              l2 t uu____7479 uu____7480))
                | uu____7481 -> None  in
              { mlift_wp; mlift_term }  in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            }  in
          let mk_mlift_wp lift_t r wp1 =
            let uu____7516 = inst_tscheme lift_t  in
            match uu____7516 with
            | (uu____7521,lift_t1) ->
                let uu____7523 =
                  let uu____7526 =
                    let uu____7527 =
                      let uu____7537 =
                        let uu____7539 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____7540 =
                          let uu____7542 = FStar_Syntax_Syntax.as_arg wp1  in
                          [uu____7542]  in
                        uu____7539 :: uu____7540  in
                      (lift_t1, uu____7537)  in
                    FStar_Syntax_Syntax.Tm_app uu____7527  in
                  FStar_Syntax_Syntax.mk uu____7526  in
                uu____7523 None wp1.FStar_Syntax_Syntax.pos
             in
          let sub_mlift_wp =
            match sub1.FStar_Syntax_Syntax.lift_wp with
            | Some sub_lift_wp -> mk_mlift_wp sub_lift_wp
            | None  ->
                failwith "sub effect should've been elaborated at this stage"
             in
          let mk_mlift_term lift_t r wp1 e =
            let uu____7587 = inst_tscheme lift_t  in
            match uu____7587 with
            | (uu____7592,lift_t1) ->
                let uu____7594 =
                  let uu____7597 =
                    let uu____7598 =
                      let uu____7608 =
                        let uu____7610 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____7611 =
                          let uu____7613 = FStar_Syntax_Syntax.as_arg wp1  in
                          let uu____7614 =
                            let uu____7616 = FStar_Syntax_Syntax.as_arg e  in
                            [uu____7616]  in
                          uu____7613 :: uu____7614  in
                        uu____7610 :: uu____7611  in
                      (lift_t1, uu____7608)  in
                    FStar_Syntax_Syntax.Tm_app uu____7598  in
                  FStar_Syntax_Syntax.mk uu____7597  in
                uu____7594 None e.FStar_Syntax_Syntax.pos
             in
          let sub_mlift_term =
            FStar_Util.map_opt sub1.FStar_Syntax_Syntax.lift mk_mlift_term
             in
          let edge =
            {
              msource = (sub1.FStar_Syntax_Syntax.source);
              mtarget = (sub1.FStar_Syntax_Syntax.target);
              mlift =
                { mlift_wp = sub_mlift_wp; mlift_term = sub_mlift_term }
            }  in
          let id_edge l =
            {
              msource = (sub1.FStar_Syntax_Syntax.source);
              mtarget = (sub1.FStar_Syntax_Syntax.target);
              mlift = identity_mlift
            }  in
          let print_mlift l =
            let bogus_term s =
              let uu____7657 =
                let uu____7658 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange  in
                FStar_Syntax_Syntax.lid_as_fv uu____7658
                  FStar_Syntax_Syntax.Delta_constant None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____7657  in
            let arg = bogus_term "ARG"  in
            let wp = bogus_term "WP"  in
            let e = bogus_term "COMP"  in
            let uu____7662 =
              let uu____7663 = l.mlift_wp arg wp  in
              FStar_Syntax_Print.term_to_string uu____7663  in
            let uu____7664 =
              let uu____7665 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____7680 = l1 arg wp e  in
                     FStar_Syntax_Print.term_to_string uu____7680)
                 in
              FStar_Util.dflt "none" uu____7665  in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____7662
              uu____7664
             in
          let order = edge :: ((env.effects).order)  in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____7693  ->
                    match uu____7693 with
                    | (e,uu____7698) -> e.FStar_Syntax_Syntax.mname))
             in
          let find_edge order1 uu____7711 =
            match uu____7711 with
            | (i,j) ->
                if FStar_Ident.lid_equals i j
                then
                  FStar_All.pipe_right (id_edge i) (fun _0_39  -> Some _0_39)
                else
                  FStar_All.pipe_right order1
                    (FStar_Util.find_opt
                       (fun e  ->
                          (FStar_Ident.lid_equals e.msource i) &&
                            (FStar_Ident.lid_equals e.mtarget j)))
             in
          let order1 =
            let fold_fun order1 k =
              let uu____7736 =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i  ->
                        if FStar_Ident.lid_equals i k
                        then []
                        else
                          FStar_All.pipe_right ms
                            (FStar_List.collect
                               (fun j  ->
                                  if FStar_Ident.lid_equals j k
                                  then []
                                  else
                                    (let uu____7748 =
                                       let uu____7753 =
                                         find_edge order1 (i, k)  in
                                       let uu____7755 =
                                         find_edge order1 (k, j)  in
                                       (uu____7753, uu____7755)  in
                                     match uu____7748 with
                                     | (Some e1,Some e2) ->
                                         let uu____7764 = compose_edges e1 e2
                                            in
                                         [uu____7764]
                                     | uu____7765 -> [])))))
                 in
              FStar_List.append order1 uu____7736  in
            FStar_All.pipe_right ms (FStar_List.fold_left fold_fun order)  in
          let order2 =
            FStar_Util.remove_dups
              (fun e1  ->
                 fun e2  ->
                   (FStar_Ident.lid_equals e1.msource e2.msource) &&
                     (FStar_Ident.lid_equals e1.mtarget e2.mtarget)) order1
             in
          (FStar_All.pipe_right order2
             (FStar_List.iter
                (fun edge1  ->
                   let uu____7780 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Syntax_Const.effect_DIV_lid)
                       &&
                       (let uu____7781 =
                          lookup_effect_quals env edge1.mtarget  in
                        FStar_All.pipe_right uu____7781
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect))
                      in
                   if uu____7780
                   then
                     let uu____7784 =
                       let uu____7785 =
                         let uu____7788 =
                           FStar_Util.format1
                             "Divergent computations cannot be included in an effect %s marked 'total'"
                             (edge1.mtarget).FStar_Ident.str
                            in
                         let uu____7789 = get_range env  in
                         (uu____7788, uu____7789)  in
                       FStar_Errors.Error uu____7785  in
                     raise uu____7784
                   else ()));
           (let joins =
              FStar_All.pipe_right ms
                (FStar_List.collect
                   (fun i  ->
                      FStar_All.pipe_right ms
                        (FStar_List.collect
                           (fun j  ->
                              let join_opt =
                                if FStar_Ident.lid_equals i j
                                then Some (i, (id_edge i), (id_edge i))
                                else
                                  FStar_All.pipe_right ms
                                    (FStar_List.fold_left
                                       (fun bopt  ->
                                          fun k  ->
                                            let uu____7852 =
                                              let uu____7857 =
                                                find_edge order2 (i, k)  in
                                              let uu____7859 =
                                                find_edge order2 (j, k)  in
                                              (uu____7857, uu____7859)  in
                                            match uu____7852 with
                                            | (Some ik,Some jk) ->
                                                (match bopt with
                                                 | None  -> Some (k, ik, jk)
                                                 | Some
                                                     (ub,uu____7882,uu____7883)
                                                     ->
                                                     let uu____7887 =
                                                       let uu____7890 =
                                                         let uu____7891 =
                                                           find_edge order2
                                                             (k, ub)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____7891
                                                          in
                                                       let uu____7893 =
                                                         let uu____7894 =
                                                           find_edge order2
                                                             (ub, k)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____7894
                                                          in
                                                       (uu____7890,
                                                         uu____7893)
                                                        in
                                                     (match uu____7887 with
                                                      | (true ,true ) ->
                                                          if
                                                            FStar_Ident.lid_equals
                                                              k ub
                                                          then
                                                            (FStar_Util.print_warning
                                                               "Looking multiple times at the same upper bound candidate";
                                                             bopt)
                                                          else
                                                            failwith
                                                              "Found a cycle in the lattice"
                                                      | (false ,false ) ->
                                                          bopt
                                                      | (true ,false ) ->
                                                          Some (k, ik, jk)
                                                      | (false ,true ) ->
                                                          bopt))
                                            | uu____7913 -> bopt) None)
                                 in
                              match join_opt with
                              | None  -> []
                              | Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))]))))
               in
            let effects =
              let uu___122_7952 = env.effects  in
              { decls = (uu___122_7952.decls); order = order2; joins }  in
            let uu___123_7953 = env  in
            {
              solver = (uu___123_7953.solver);
              range = (uu___123_7953.range);
              curmodule = (uu___123_7953.curmodule);
              gamma = (uu___123_7953.gamma);
              gamma_cache = (uu___123_7953.gamma_cache);
              modules = (uu___123_7953.modules);
              expected_typ = (uu___123_7953.expected_typ);
              sigtab = (uu___123_7953.sigtab);
              is_pattern = (uu___123_7953.is_pattern);
              instantiate_imp = (uu___123_7953.instantiate_imp);
              effects;
              generalize = (uu___123_7953.generalize);
              letrecs = (uu___123_7953.letrecs);
              top_level = (uu___123_7953.top_level);
              check_uvars = (uu___123_7953.check_uvars);
              use_eq = (uu___123_7953.use_eq);
              is_iface = (uu___123_7953.is_iface);
              admit = (uu___123_7953.admit);
              lax = (uu___123_7953.lax);
              lax_universes = (uu___123_7953.lax_universes);
              type_of = (uu___123_7953.type_of);
              universe_of = (uu___123_7953.universe_of);
              use_bv_sorts = (uu___123_7953.use_bv_sorts);
              qname_and_index = (uu___123_7953.qname_and_index);
              proof_ns = (uu___123_7953.proof_ns);
              synth = (uu___123_7953.synth);
              is_native_tactic = (uu___123_7953.is_native_tactic)
            }))
      | uu____7954 -> env
  
let comp_to_comp_typ :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ =
  fun env  ->
    fun c  ->
      let c1 =
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,None ) ->
            let u = env.universe_of env t  in
            FStar_Syntax_Syntax.mk_Total' t (Some u)
        | FStar_Syntax_Syntax.GTotal (t,None ) ->
            let u = env.universe_of env t  in
            FStar_Syntax_Syntax.mk_GTotal' t (Some u)
        | uu____7978 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____7988 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____7988 with
      | None  -> c
      | Some (binders,cdef) ->
          let uu____7998 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____7998 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____8020 =
                     let uu____8021 =
                       let uu____8024 =
                         let uu____8025 =
                           FStar_Util.string_of_int
                             (FStar_List.length binders1)
                            in
                         let uu____8034 =
                           FStar_Util.string_of_int
                             ((FStar_List.length
                                 c.FStar_Syntax_Syntax.effect_args)
                                + (Prims.parse_int "1"))
                            in
                         let uu____8045 =
                           let uu____8046 = FStar_Syntax_Syntax.mk_Comp c  in
                           FStar_Syntax_Print.comp_to_string uu____8046  in
                         FStar_Util.format3
                           "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                           uu____8025 uu____8034 uu____8045
                          in
                       (uu____8024, (comp.FStar_Syntax_Syntax.pos))  in
                     FStar_Errors.Error uu____8021  in
                   raise uu____8020)
                else ();
                (let inst1 =
                   let uu____8050 =
                     let uu____8056 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____8056 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____8063  ->
                        fun uu____8064  ->
                          match (uu____8063, uu____8064) with
                          | ((x,uu____8078),(t,uu____8080)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____8050
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let c2 =
                   let uu____8095 =
                     let uu___124_8096 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___124_8096.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___124_8096.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___124_8096.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___124_8096.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____8095
                     FStar_Syntax_Syntax.mk_Comp
                    in
                 unfold_effect_abbrev env c2)))
  
let effect_repr_aux only_reifiable env c u_c =
  let uu____8131 =
    let uu____8136 = norm_eff_name env (FStar_Syntax_Util.comp_effect_name c)
       in
    effect_decl_opt env uu____8136  in
  match uu____8131 with
  | None  -> None
  | Some (ed,qualifiers) ->
      let uu____8152 =
        only_reifiable &&
          (let uu____8153 =
             FStar_All.pipe_right qualifiers
               (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
              in
           Prims.op_Negation uu____8153)
         in
      if uu____8152
      then None
      else
        (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_unknown  -> None
         | uu____8166 ->
             let c1 = unfold_effect_abbrev env c  in
             let uu____8168 =
               let uu____8177 =
                 FStar_List.hd c1.FStar_Syntax_Syntax.effect_args  in
               ((c1.FStar_Syntax_Syntax.result_typ), uu____8177)  in
             (match uu____8168 with
              | (res_typ,wp) ->
                  let repr =
                    inst_effect_fun_with [u_c] env ed
                      ([], (ed.FStar_Syntax_Syntax.repr))
                     in
                  let uu____8211 =
                    let uu____8214 = get_range env  in
                    let uu____8215 =
                      let uu____8218 =
                        let uu____8219 =
                          let uu____8229 =
                            let uu____8231 =
                              FStar_Syntax_Syntax.as_arg res_typ  in
                            [uu____8231; wp]  in
                          (repr, uu____8229)  in
                        FStar_Syntax_Syntax.Tm_app uu____8219  in
                      FStar_Syntax_Syntax.mk uu____8218  in
                    uu____8215 None uu____8214  in
                  Some uu____8211))
  
let effect_repr :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe ->
        (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
          FStar_Syntax_Syntax.syntax option
  = fun env  -> fun c  -> fun u_c  -> effect_repr_aux false env c u_c 
let reify_comp :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun c  ->
      fun u_c  ->
        let no_reify l =
          let uu____8281 =
            let uu____8282 =
              let uu____8285 =
                let uu____8286 = FStar_Ident.string_of_lid l  in
                FStar_Util.format1 "Effect %s cannot be reified" uu____8286
                 in
              let uu____8287 = get_range env  in (uu____8285, uu____8287)  in
            FStar_Errors.Error uu____8282  in
          raise uu____8281  in
        let uu____8288 = effect_repr_aux true env c u_c  in
        match uu____8288 with
        | None  -> no_reify (FStar_Syntax_Util.comp_effect_name c)
        | Some tm -> tm
  
let is_reifiable_effect : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun effect_lid  ->
      let quals = lookup_effect_quals env effect_lid  in
      FStar_List.contains FStar_Syntax_Syntax.Reifiable quals
  
let is_reifiable : env -> FStar_Syntax_Syntax.residual_comp -> Prims.bool =
  fun env  ->
    fun c  -> is_reifiable_effect env c.FStar_Syntax_Syntax.residual_effect
  
let is_reifiable_comp : env -> FStar_Syntax_Syntax.comp -> Prims.bool =
  fun env  ->
    fun c  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Comp ct ->
          is_reifiable_effect env ct.FStar_Syntax_Syntax.effect_name
      | uu____8326 -> false
  
let is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____8335 =
        let uu____8336 = FStar_Syntax_Subst.compress t  in
        uu____8336.FStar_Syntax_Syntax.n  in
      match uu____8335 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____8339,c) ->
          is_reifiable_comp env c
      | uu____8351 -> false
  
let push_in_gamma : env -> binding -> env =
  fun env  ->
    fun s  ->
      let rec push1 x rest =
        match rest with
        | (Binding_sig uu____8371)::uu____8372 -> x :: rest
        | (Binding_sig_inst uu____8377)::uu____8378 -> x :: rest
        | [] -> [x]
        | local::rest1 ->
            let uu____8387 = push1 x rest1  in local :: uu____8387
         in
      let uu___125_8389 = env  in
      let uu____8390 = push1 s env.gamma  in
      {
        solver = (uu___125_8389.solver);
        range = (uu___125_8389.range);
        curmodule = (uu___125_8389.curmodule);
        gamma = uu____8390;
        gamma_cache = (uu___125_8389.gamma_cache);
        modules = (uu___125_8389.modules);
        expected_typ = (uu___125_8389.expected_typ);
        sigtab = (uu___125_8389.sigtab);
        is_pattern = (uu___125_8389.is_pattern);
        instantiate_imp = (uu___125_8389.instantiate_imp);
        effects = (uu___125_8389.effects);
        generalize = (uu___125_8389.generalize);
        letrecs = (uu___125_8389.letrecs);
        top_level = (uu___125_8389.top_level);
        check_uvars = (uu___125_8389.check_uvars);
        use_eq = (uu___125_8389.use_eq);
        is_iface = (uu___125_8389.is_iface);
        admit = (uu___125_8389.admit);
        lax = (uu___125_8389.lax);
        lax_universes = (uu___125_8389.lax_universes);
        type_of = (uu___125_8389.type_of);
        universe_of = (uu___125_8389.universe_of);
        use_bv_sorts = (uu___125_8389.use_bv_sorts);
        qname_and_index = (uu___125_8389.qname_and_index);
        proof_ns = (uu___125_8389.proof_ns);
        synth = (uu___125_8389.synth);
        is_native_tactic = (uu___125_8389.is_native_tactic)
      }
  
let push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env =
  fun env  ->
    fun s  ->
      let env1 =
        push_in_gamma env
          (Binding_sig ((FStar_Syntax_Util.lids_of_sigelt s), s))
         in
      build_lattice env1 s
  
let push_sigelt_inst :
  env -> FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.universes -> env =
  fun env  ->
    fun s  ->
      fun us  ->
        let env1 =
          push_in_gamma env
            (Binding_sig_inst ((FStar_Syntax_Util.lids_of_sigelt s), s, us))
           in
        build_lattice env1 s
  
let push_local_binding : env -> binding -> env =
  fun env  ->
    fun b  ->
      let uu___126_8424 = env  in
      {
        solver = (uu___126_8424.solver);
        range = (uu___126_8424.range);
        curmodule = (uu___126_8424.curmodule);
        gamma = (b :: (env.gamma));
        gamma_cache = (uu___126_8424.gamma_cache);
        modules = (uu___126_8424.modules);
        expected_typ = (uu___126_8424.expected_typ);
        sigtab = (uu___126_8424.sigtab);
        is_pattern = (uu___126_8424.is_pattern);
        instantiate_imp = (uu___126_8424.instantiate_imp);
        effects = (uu___126_8424.effects);
        generalize = (uu___126_8424.generalize);
        letrecs = (uu___126_8424.letrecs);
        top_level = (uu___126_8424.top_level);
        check_uvars = (uu___126_8424.check_uvars);
        use_eq = (uu___126_8424.use_eq);
        is_iface = (uu___126_8424.is_iface);
        admit = (uu___126_8424.admit);
        lax = (uu___126_8424.lax);
        lax_universes = (uu___126_8424.lax_universes);
        type_of = (uu___126_8424.type_of);
        universe_of = (uu___126_8424.universe_of);
        use_bv_sorts = (uu___126_8424.use_bv_sorts);
        qname_and_index = (uu___126_8424.qname_and_index);
        proof_ns = (uu___126_8424.proof_ns);
        synth = (uu___126_8424.synth);
        is_native_tactic = (uu___126_8424.is_native_tactic)
      }
  
let push_bv : env -> FStar_Syntax_Syntax.bv -> env =
  fun env  -> fun x  -> push_local_binding env (Binding_var x) 
let pop_bv : env -> (FStar_Syntax_Syntax.bv * env) option =
  fun env  ->
    match env.gamma with
    | (Binding_var x)::rest ->
        Some
          (x,
            (let uu___127_8448 = env  in
             {
               solver = (uu___127_8448.solver);
               range = (uu___127_8448.range);
               curmodule = (uu___127_8448.curmodule);
               gamma = rest;
               gamma_cache = (uu___127_8448.gamma_cache);
               modules = (uu___127_8448.modules);
               expected_typ = (uu___127_8448.expected_typ);
               sigtab = (uu___127_8448.sigtab);
               is_pattern = (uu___127_8448.is_pattern);
               instantiate_imp = (uu___127_8448.instantiate_imp);
               effects = (uu___127_8448.effects);
               generalize = (uu___127_8448.generalize);
               letrecs = (uu___127_8448.letrecs);
               top_level = (uu___127_8448.top_level);
               check_uvars = (uu___127_8448.check_uvars);
               use_eq = (uu___127_8448.use_eq);
               is_iface = (uu___127_8448.is_iface);
               admit = (uu___127_8448.admit);
               lax = (uu___127_8448.lax);
               lax_universes = (uu___127_8448.lax_universes);
               type_of = (uu___127_8448.type_of);
               universe_of = (uu___127_8448.universe_of);
               use_bv_sorts = (uu___127_8448.use_bv_sorts);
               qname_and_index = (uu___127_8448.qname_and_index);
               proof_ns = (uu___127_8448.proof_ns);
               synth = (uu___127_8448.synth);
               is_native_tactic = (uu___127_8448.is_native_tactic)
             }))
    | uu____8449 -> None
  
let push_binders : env -> FStar_Syntax_Syntax.binders -> env =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____8464  ->
             match uu____8464 with | (x,uu____8468) -> push_bv env1 x) env bs
  
let binding_of_lb :
  FStar_Syntax_Syntax.lbname ->
    (FStar_Syntax_Syntax.univ_name Prims.list *
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax) -> binding
  =
  fun x  ->
    fun t  ->
      match x with
      | FStar_Util.Inl x1 ->
          let x2 =
            let uu___128_8490 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___128_8490.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___128_8490.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = (snd t)
            }  in
          Binding_var x2
      | FStar_Util.Inr fv ->
          Binding_lid
            (((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v), t)
  
let push_let_binding :
  env -> FStar_Syntax_Syntax.lbname -> FStar_Syntax_Syntax.tscheme -> env =
  fun env  ->
    fun lb  -> fun ts  -> push_local_binding env (binding_of_lb lb ts)
  
let push_module : env -> FStar_Syntax_Syntax.modul -> env =
  fun env  ->
    fun m  ->
      add_sigelts env m.FStar_Syntax_Syntax.exports;
      (let uu___129_8525 = env  in
       {
         solver = (uu___129_8525.solver);
         range = (uu___129_8525.range);
         curmodule = (uu___129_8525.curmodule);
         gamma = [];
         gamma_cache = (uu___129_8525.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = None;
         sigtab = (uu___129_8525.sigtab);
         is_pattern = (uu___129_8525.is_pattern);
         instantiate_imp = (uu___129_8525.instantiate_imp);
         effects = (uu___129_8525.effects);
         generalize = (uu___129_8525.generalize);
         letrecs = (uu___129_8525.letrecs);
         top_level = (uu___129_8525.top_level);
         check_uvars = (uu___129_8525.check_uvars);
         use_eq = (uu___129_8525.use_eq);
         is_iface = (uu___129_8525.is_iface);
         admit = (uu___129_8525.admit);
         lax = (uu___129_8525.lax);
         lax_universes = (uu___129_8525.lax_universes);
         type_of = (uu___129_8525.type_of);
         universe_of = (uu___129_8525.universe_of);
         use_bv_sorts = (uu___129_8525.use_bv_sorts);
         qname_and_index = (uu___129_8525.qname_and_index);
         proof_ns = (uu___129_8525.proof_ns);
         synth = (uu___129_8525.synth);
         is_native_tactic = (uu___129_8525.is_native_tactic)
       })
  
let push_univ_vars : env_t -> FStar_Syntax_Syntax.univ_names -> env =
  fun env  ->
    fun xs  ->
      FStar_List.fold_left
        (fun env1  -> fun x  -> push_local_binding env1 (Binding_univ x)) env
        xs
  
let open_universes_in :
  env ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.term Prims.list ->
        (env * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term
          Prims.list)
  =
  fun env  ->
    fun uvs  ->
      fun terms  ->
        let uu____8554 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____8554 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars  in
            let uu____8570 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____8570)
  
let set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env =
  fun env  ->
    fun t  ->
      let uu___130_8582 = env  in
      {
        solver = (uu___130_8582.solver);
        range = (uu___130_8582.range);
        curmodule = (uu___130_8582.curmodule);
        gamma = (uu___130_8582.gamma);
        gamma_cache = (uu___130_8582.gamma_cache);
        modules = (uu___130_8582.modules);
        expected_typ = (Some t);
        sigtab = (uu___130_8582.sigtab);
        is_pattern = (uu___130_8582.is_pattern);
        instantiate_imp = (uu___130_8582.instantiate_imp);
        effects = (uu___130_8582.effects);
        generalize = (uu___130_8582.generalize);
        letrecs = (uu___130_8582.letrecs);
        top_level = (uu___130_8582.top_level);
        check_uvars = (uu___130_8582.check_uvars);
        use_eq = false;
        is_iface = (uu___130_8582.is_iface);
        admit = (uu___130_8582.admit);
        lax = (uu___130_8582.lax);
        lax_universes = (uu___130_8582.lax_universes);
        type_of = (uu___130_8582.type_of);
        universe_of = (uu___130_8582.universe_of);
        use_bv_sorts = (uu___130_8582.use_bv_sorts);
        qname_and_index = (uu___130_8582.qname_and_index);
        proof_ns = (uu___130_8582.proof_ns);
        synth = (uu___130_8582.synth);
        is_native_tactic = (uu___130_8582.is_native_tactic)
      }
  
let expected_typ : env -> FStar_Syntax_Syntax.typ option =
  fun env  -> match env.expected_typ with | None  -> None | Some t -> Some t 
let clear_expected_typ : env -> (env * FStar_Syntax_Syntax.typ option) =
  fun env_  ->
    let uu____8600 = expected_typ env_  in
    ((let uu___131_8603 = env_  in
      {
        solver = (uu___131_8603.solver);
        range = (uu___131_8603.range);
        curmodule = (uu___131_8603.curmodule);
        gamma = (uu___131_8603.gamma);
        gamma_cache = (uu___131_8603.gamma_cache);
        modules = (uu___131_8603.modules);
        expected_typ = None;
        sigtab = (uu___131_8603.sigtab);
        is_pattern = (uu___131_8603.is_pattern);
        instantiate_imp = (uu___131_8603.instantiate_imp);
        effects = (uu___131_8603.effects);
        generalize = (uu___131_8603.generalize);
        letrecs = (uu___131_8603.letrecs);
        top_level = (uu___131_8603.top_level);
        check_uvars = (uu___131_8603.check_uvars);
        use_eq = false;
        is_iface = (uu___131_8603.is_iface);
        admit = (uu___131_8603.admit);
        lax = (uu___131_8603.lax);
        lax_universes = (uu___131_8603.lax_universes);
        type_of = (uu___131_8603.type_of);
        universe_of = (uu___131_8603.universe_of);
        use_bv_sorts = (uu___131_8603.use_bv_sorts);
        qname_and_index = (uu___131_8603.qname_and_index);
        proof_ns = (uu___131_8603.proof_ns);
        synth = (uu___131_8603.synth);
        is_native_tactic = (uu___131_8603.is_native_tactic)
      }), uu____8600)
  
let finish_module : env -> FStar_Syntax_Syntax.modul -> env =
  let empty_lid = FStar_Ident.lid_of_ids [FStar_Ident.id_of_text ""]  in
  fun env  ->
    fun m  ->
      let sigs =
        if
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Syntax_Const.prims_lid
        then
          let uu____8616 =
            FStar_All.pipe_right env.gamma
              (FStar_List.collect
                 (fun uu___110_8620  ->
                    match uu___110_8620 with
                    | Binding_sig (uu____8622,se) -> [se]
                    | uu____8626 -> []))
             in
          FStar_All.pipe_right uu____8616 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___132_8631 = env  in
       {
         solver = (uu___132_8631.solver);
         range = (uu___132_8631.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_cache = (uu___132_8631.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___132_8631.expected_typ);
         sigtab = (uu___132_8631.sigtab);
         is_pattern = (uu___132_8631.is_pattern);
         instantiate_imp = (uu___132_8631.instantiate_imp);
         effects = (uu___132_8631.effects);
         generalize = (uu___132_8631.generalize);
         letrecs = (uu___132_8631.letrecs);
         top_level = (uu___132_8631.top_level);
         check_uvars = (uu___132_8631.check_uvars);
         use_eq = (uu___132_8631.use_eq);
         is_iface = (uu___132_8631.is_iface);
         admit = (uu___132_8631.admit);
         lax = (uu___132_8631.lax);
         lax_universes = (uu___132_8631.lax_universes);
         type_of = (uu___132_8631.type_of);
         universe_of = (uu___132_8631.universe_of);
         use_bv_sorts = (uu___132_8631.use_bv_sorts);
         qname_and_index = (uu___132_8631.qname_and_index);
         proof_ns = (uu___132_8631.proof_ns);
         synth = (uu___132_8631.synth);
         is_native_tactic = (uu___132_8631.is_native_tactic)
       })
  
let uvars_in_env :
  env -> (FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.typ) FStar_Util.set
  =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_univ uu____8682)::tl1 -> aux out tl1
      | (Binding_lid (uu____8685,(uu____8686,t)))::tl1 ->
          let uu____8695 =
            let uu____8699 = FStar_Syntax_Free.uvars t  in ext out uu____8699
             in
          aux uu____8695 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____8703;
            FStar_Syntax_Syntax.index = uu____8704;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____8710 =
            let uu____8714 = FStar_Syntax_Free.uvars t  in ext out uu____8714
             in
          aux uu____8710 tl1
      | (Binding_sig uu____8718)::uu____8719 -> out
      | (Binding_sig_inst uu____8724)::uu____8725 -> out  in
    aux no_uvs env.gamma
  
let univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____8763)::tl1 -> aux out tl1
      | (Binding_univ uu____8770)::tl1 -> aux out tl1
      | (Binding_lid (uu____8773,(uu____8774,t)))::tl1 ->
          let uu____8783 =
            let uu____8785 = FStar_Syntax_Free.univs t  in ext out uu____8785
             in
          aux uu____8783 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____8787;
            FStar_Syntax_Syntax.index = uu____8788;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____8794 =
            let uu____8796 = FStar_Syntax_Free.univs t  in ext out uu____8796
             in
          aux uu____8794 tl1
      | (Binding_sig uu____8798)::uu____8799 -> out  in
    aux no_univs env.gamma
  
let univnames : env -> FStar_Syntax_Syntax.univ_name FStar_Util.set =
  fun env  ->
    let no_univ_names = FStar_Syntax_Syntax.no_universe_names  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____8837)::tl1 -> aux out tl1
      | (Binding_univ uname)::tl1 ->
          let uu____8847 = FStar_Util.set_add uname out  in
          aux uu____8847 tl1
      | (Binding_lid (uu____8849,(uu____8850,t)))::tl1 ->
          let uu____8859 =
            let uu____8861 = FStar_Syntax_Free.univnames t  in
            ext out uu____8861  in
          aux uu____8859 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____8863;
            FStar_Syntax_Syntax.index = uu____8864;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____8870 =
            let uu____8872 = FStar_Syntax_Free.univnames t  in
            ext out uu____8872  in
          aux uu____8870 tl1
      | (Binding_sig uu____8874)::uu____8875 -> out  in
    aux no_univ_names env.gamma
  
let bound_vars_of_bindings :
  binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___111_8892  ->
            match uu___111_8892 with
            | Binding_var x -> [x]
            | Binding_lid uu____8895 -> []
            | Binding_sig uu____8898 -> []
            | Binding_univ uu____8902 -> []
            | Binding_sig_inst uu____8903 -> []))
  
let binders_of_bindings :
  binding Prims.list -> FStar_Syntax_Syntax.binder Prims.list =
  fun bs  ->
    let uu____8914 =
      let uu____8916 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____8916
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____8914 FStar_List.rev
  
let bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list =
  fun env  -> bound_vars_of_bindings env.gamma 
let all_binders : env -> FStar_Syntax_Syntax.binders =
  fun env  -> binders_of_bindings env.gamma 
let print_gamma : env -> Prims.unit =
  fun env  ->
    let uu____8935 =
      let uu____8936 =
        FStar_All.pipe_right env.gamma
          (FStar_List.map
             (fun uu___112_8940  ->
                match uu___112_8940 with
                | Binding_var x ->
                    let uu____8942 = FStar_Syntax_Print.bv_to_string x  in
                    Prims.strcat "Binding_var " uu____8942
                | Binding_univ u ->
                    Prims.strcat "Binding_univ " u.FStar_Ident.idText
                | Binding_lid (l,uu____8945) ->
                    let uu____8946 = FStar_Ident.string_of_lid l  in
                    Prims.strcat "Binding_lid " uu____8946
                | Binding_sig (ls,uu____8948) ->
                    let uu____8951 =
                      let uu____8952 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid)
                         in
                      FStar_All.pipe_right uu____8952
                        (FStar_String.concat ", ")
                       in
                    Prims.strcat "Binding_sig " uu____8951
                | Binding_sig_inst (ls,uu____8958,uu____8959) ->
                    let uu____8962 =
                      let uu____8963 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid)
                         in
                      FStar_All.pipe_right uu____8963
                        (FStar_String.concat ", ")
                       in
                    Prims.strcat "Binding_sig_inst " uu____8962))
         in
      FStar_All.pipe_right uu____8936 (FStar_String.concat "::\n")  in
    FStar_All.pipe_right uu____8935 (FStar_Util.print1 "%s\n")
  
let eq_gamma : env -> env -> Prims.bool =
  fun env  ->
    fun env'  ->
      let uu____8977 = FStar_Util.physical_equality env.gamma env'.gamma  in
      if uu____8977
      then true
      else
        (let g = all_binders env  in
         let g' = all_binders env'  in
         ((FStar_List.length g) = (FStar_List.length g')) &&
           (FStar_List.forall2
              (fun uu____8998  ->
                 fun uu____8999  ->
                   match (uu____8998, uu____8999) with
                   | ((b1,uu____9009),(b2,uu____9011)) ->
                       FStar_Syntax_Syntax.bv_eq b1 b2) g g'))
  
let fold_env env f a =
  FStar_List.fold_right (fun e  -> fun a1  -> f a1 e) env.gamma a 
let lidents : env -> FStar_Ident.lident Prims.list =
  fun env  ->
    let keys =
      FStar_List.fold_left
        (fun keys  ->
           fun uu___113_9059  ->
             match uu___113_9059 with
             | Binding_sig (lids,uu____9063) -> FStar_List.append lids keys
             | uu____9066 -> keys) [] env.gamma
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____9068  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
  
let should_enc_path : env -> Prims.string Prims.list -> Prims.bool =
  fun env  ->
    fun path  ->
      let rec list_prefix xs ys =
        match (xs, ys) with
        | ([],uu____9095) -> true
        | (x::xs1,y::ys1) -> (x = y) && (list_prefix xs1 ys1)
        | (uu____9107,uu____9108) -> false  in
      let rec should_enc_path' pns path1 =
        match pns with
        | [] -> true
        | (p,b)::pns1 ->
            let uu____9132 = list_prefix p path1  in
            if uu____9132 then b else should_enc_path' pns1 path1
         in
      should_enc_path' (FStar_List.flatten env.proof_ns) path
  
let should_enc_lid : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____9144 = FStar_Ident.path_of_lid lid  in
      should_enc_path env uu____9144
  
let cons_proof_ns : Prims.bool -> env -> name_prefix -> env =
  fun b  ->
    fun e  ->
      fun path  ->
        match e.proof_ns with
        | [] -> failwith "empty proof_ns stack!"
        | pns::rest ->
            let pns' = (path, b) :: pns  in
            let uu___133_9167 = e  in
            {
              solver = (uu___133_9167.solver);
              range = (uu___133_9167.range);
              curmodule = (uu___133_9167.curmodule);
              gamma = (uu___133_9167.gamma);
              gamma_cache = (uu___133_9167.gamma_cache);
              modules = (uu___133_9167.modules);
              expected_typ = (uu___133_9167.expected_typ);
              sigtab = (uu___133_9167.sigtab);
              is_pattern = (uu___133_9167.is_pattern);
              instantiate_imp = (uu___133_9167.instantiate_imp);
              effects = (uu___133_9167.effects);
              generalize = (uu___133_9167.generalize);
              letrecs = (uu___133_9167.letrecs);
              top_level = (uu___133_9167.top_level);
              check_uvars = (uu___133_9167.check_uvars);
              use_eq = (uu___133_9167.use_eq);
              is_iface = (uu___133_9167.is_iface);
              admit = (uu___133_9167.admit);
              lax = (uu___133_9167.lax);
              lax_universes = (uu___133_9167.lax_universes);
              type_of = (uu___133_9167.type_of);
              universe_of = (uu___133_9167.universe_of);
              use_bv_sorts = (uu___133_9167.use_bv_sorts);
              qname_and_index = (uu___133_9167.qname_and_index);
              proof_ns = (pns' :: rest);
              synth = (uu___133_9167.synth);
              is_native_tactic = (uu___133_9167.is_native_tactic)
            }
  
let add_proof_ns : env -> name_prefix -> env =
  fun e  -> fun path  -> cons_proof_ns true e path 
let rem_proof_ns : env -> name_prefix -> env =
  fun e  -> fun path  -> cons_proof_ns false e path 
let push_proof_ns : env -> env =
  fun e  ->
    let uu___134_9191 = e  in
    {
      solver = (uu___134_9191.solver);
      range = (uu___134_9191.range);
      curmodule = (uu___134_9191.curmodule);
      gamma = (uu___134_9191.gamma);
      gamma_cache = (uu___134_9191.gamma_cache);
      modules = (uu___134_9191.modules);
      expected_typ = (uu___134_9191.expected_typ);
      sigtab = (uu___134_9191.sigtab);
      is_pattern = (uu___134_9191.is_pattern);
      instantiate_imp = (uu___134_9191.instantiate_imp);
      effects = (uu___134_9191.effects);
      generalize = (uu___134_9191.generalize);
      letrecs = (uu___134_9191.letrecs);
      top_level = (uu___134_9191.top_level);
      check_uvars = (uu___134_9191.check_uvars);
      use_eq = (uu___134_9191.use_eq);
      is_iface = (uu___134_9191.is_iface);
      admit = (uu___134_9191.admit);
      lax = (uu___134_9191.lax);
      lax_universes = (uu___134_9191.lax_universes);
      type_of = (uu___134_9191.type_of);
      universe_of = (uu___134_9191.universe_of);
      use_bv_sorts = (uu___134_9191.use_bv_sorts);
      qname_and_index = (uu___134_9191.qname_and_index);
      proof_ns = ([] :: (e.proof_ns));
      synth = (uu___134_9191.synth);
      is_native_tactic = (uu___134_9191.is_native_tactic)
    }
  
let pop_proof_ns : env -> env =
  fun e  ->
    match e.proof_ns with
    | [] -> failwith "empty proof_ns stack!"
    | uu____9201::rest ->
        let uu___135_9204 = e  in
        {
          solver = (uu___135_9204.solver);
          range = (uu___135_9204.range);
          curmodule = (uu___135_9204.curmodule);
          gamma = (uu___135_9204.gamma);
          gamma_cache = (uu___135_9204.gamma_cache);
          modules = (uu___135_9204.modules);
          expected_typ = (uu___135_9204.expected_typ);
          sigtab = (uu___135_9204.sigtab);
          is_pattern = (uu___135_9204.is_pattern);
          instantiate_imp = (uu___135_9204.instantiate_imp);
          effects = (uu___135_9204.effects);
          generalize = (uu___135_9204.generalize);
          letrecs = (uu___135_9204.letrecs);
          top_level = (uu___135_9204.top_level);
          check_uvars = (uu___135_9204.check_uvars);
          use_eq = (uu___135_9204.use_eq);
          is_iface = (uu___135_9204.is_iface);
          admit = (uu___135_9204.admit);
          lax = (uu___135_9204.lax);
          lax_universes = (uu___135_9204.lax_universes);
          type_of = (uu___135_9204.type_of);
          universe_of = (uu___135_9204.universe_of);
          use_bv_sorts = (uu___135_9204.use_bv_sorts);
          qname_and_index = (uu___135_9204.qname_and_index);
          proof_ns = rest;
          synth = (uu___135_9204.synth);
          is_native_tactic = (uu___135_9204.is_native_tactic)
        }
  
let get_proof_ns : env -> proof_namespace = fun e  -> e.proof_ns 
let set_proof_ns : proof_namespace -> env -> env =
  fun ns  ->
    fun e  ->
      let uu___136_9217 = e  in
      {
        solver = (uu___136_9217.solver);
        range = (uu___136_9217.range);
        curmodule = (uu___136_9217.curmodule);
        gamma = (uu___136_9217.gamma);
        gamma_cache = (uu___136_9217.gamma_cache);
        modules = (uu___136_9217.modules);
        expected_typ = (uu___136_9217.expected_typ);
        sigtab = (uu___136_9217.sigtab);
        is_pattern = (uu___136_9217.is_pattern);
        instantiate_imp = (uu___136_9217.instantiate_imp);
        effects = (uu___136_9217.effects);
        generalize = (uu___136_9217.generalize);
        letrecs = (uu___136_9217.letrecs);
        top_level = (uu___136_9217.top_level);
        check_uvars = (uu___136_9217.check_uvars);
        use_eq = (uu___136_9217.use_eq);
        is_iface = (uu___136_9217.is_iface);
        admit = (uu___136_9217.admit);
        lax = (uu___136_9217.lax);
        lax_universes = (uu___136_9217.lax_universes);
        type_of = (uu___136_9217.type_of);
        universe_of = (uu___136_9217.universe_of);
        use_bv_sorts = (uu___136_9217.use_bv_sorts);
        qname_and_index = (uu___136_9217.qname_and_index);
        proof_ns = ns;
        synth = (uu___136_9217.synth);
        is_native_tactic = (uu___136_9217.is_native_tactic)
      }
  
let string_of_proof_ns : env -> Prims.string =
  fun env  ->
    let string_of_proof_ns' pns =
      let uu____9236 =
        FStar_List.map
          (fun fpns  ->
             let uu____9247 =
               let uu____9248 =
                 let uu____9249 =
                   FStar_List.map
                     (fun uu____9254  ->
                        match uu____9254 with
                        | (p,b) ->
                            Prims.strcat (if b then "+" else "-")
                              (FStar_String.concat "." p)) fpns
                    in
                 FStar_String.concat "," uu____9249  in
               Prims.strcat uu____9248 "]"  in
             Prims.strcat "[" uu____9247) pns
         in
      FStar_String.concat ";" uu____9236  in
    string_of_proof_ns' env.proof_ns
  
let dummy_solver : solver_t =
  {
    init = (fun uu____9263  -> ());
    push = (fun uu____9264  -> ());
    pop = (fun uu____9265  -> ());
    mark = (fun uu____9266  -> ());
    reset_mark = (fun uu____9267  -> ());
    commit_mark = (fun uu____9268  -> ());
    encode_modul = (fun uu____9269  -> fun uu____9270  -> ());
    encode_sig = (fun uu____9271  -> fun uu____9272  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____9275 =
             let uu____9279 = FStar_Options.peek ()  in (e, g, uu____9279)
              in
           [uu____9275]);
    solve = (fun uu____9286  -> fun uu____9287  -> fun uu____9288  -> ());
    is_trivial = (fun uu____9292  -> fun uu____9293  -> false);
    finish = (fun uu____9294  -> ());
    refresh = (fun uu____9295  -> ())
  } 