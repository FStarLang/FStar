open Prims
type binding =
  | Binding_var of FStar_Syntax_Syntax.bv
  | Binding_lid of (FStar_Ident.lident* FStar_Syntax_Syntax.tscheme)
  | Binding_sig of (FStar_Ident.lident Prims.list*
  FStar_Syntax_Syntax.sigelt)
  | Binding_univ of FStar_Syntax_Syntax.univ_name
  | Binding_sig_inst of (FStar_Ident.lident Prims.list*
  FStar_Syntax_Syntax.sigelt* FStar_Syntax_Syntax.universes)
let uu___is_Binding_var: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_var _0 -> true | uu____34 -> false
let __proj__Binding_var__item___0: binding -> FStar_Syntax_Syntax.bv =
  fun projectee  -> match projectee with | Binding_var _0 -> _0
let uu___is_Binding_lid: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_lid _0 -> true | uu____48 -> false
let __proj__Binding_lid__item___0:
  binding -> (FStar_Ident.lident* FStar_Syntax_Syntax.tscheme) =
  fun projectee  -> match projectee with | Binding_lid _0 -> _0
let uu___is_Binding_sig: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_sig _0 -> true | uu____69 -> false
let __proj__Binding_sig__item___0:
  binding -> (FStar_Ident.lident Prims.list* FStar_Syntax_Syntax.sigelt) =
  fun projectee  -> match projectee with | Binding_sig _0 -> _0
let uu___is_Binding_univ: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_univ _0 -> true | uu____90 -> false
let __proj__Binding_univ__item___0: binding -> FStar_Syntax_Syntax.univ_name
  = fun projectee  -> match projectee with | Binding_univ _0 -> _0
let uu___is_Binding_sig_inst: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_sig_inst _0 -> true | uu____106 -> false
let __proj__Binding_sig_inst__item___0:
  binding ->
    (FStar_Ident.lident Prims.list* FStar_Syntax_Syntax.sigelt*
      FStar_Syntax_Syntax.universes)
  = fun projectee  -> match projectee with | Binding_sig_inst _0 -> _0
type delta_level =
  | NoDelta
  | Inlining
  | Eager_unfolding_only
  | Unfold of FStar_Syntax_Syntax.delta_depth
  | UnfoldTac
let uu___is_NoDelta: delta_level -> Prims.bool =
  fun projectee  ->
    match projectee with | NoDelta  -> true | uu____133 -> false
let uu___is_Inlining: delta_level -> Prims.bool =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____137 -> false
let uu___is_Eager_unfolding_only: delta_level -> Prims.bool =
  fun projectee  ->
    match projectee with | Eager_unfolding_only  -> true | uu____141 -> false
let uu___is_Unfold: delta_level -> Prims.bool =
  fun projectee  ->
    match projectee with | Unfold _0 -> true | uu____146 -> false
let __proj__Unfold__item___0: delta_level -> FStar_Syntax_Syntax.delta_depth
  = fun projectee  -> match projectee with | Unfold _0 -> _0
let uu___is_UnfoldTac: delta_level -> Prims.bool =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____157 -> false
type mlift =
  {
  mlift_wp:
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ;
  mlift_term:
    (FStar_Syntax_Syntax.typ ->
       FStar_Syntax_Syntax.typ ->
         FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
      option;}
let __proj__Mkmlift__item__mlift_wp:
  mlift ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
  =
  fun projectee  ->
    match projectee with
    | { mlift_wp = __fname__mlift_wp; mlift_term = __fname__mlift_term;_} ->
        __fname__mlift_wp
let __proj__Mkmlift__item__mlift_term:
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
  msource: FStar_Ident.lident;
  mtarget: FStar_Ident.lident;
  mlift: mlift;}
let __proj__Mkedge__item__msource: edge -> FStar_Ident.lident =
  fun projectee  ->
    match projectee with
    | { msource = __fname__msource; mtarget = __fname__mtarget;
        mlift = __fname__mlift;_} -> __fname__msource
let __proj__Mkedge__item__mtarget: edge -> FStar_Ident.lident =
  fun projectee  ->
    match projectee with
    | { msource = __fname__msource; mtarget = __fname__mtarget;
        mlift = __fname__mlift;_} -> __fname__mtarget
let __proj__Mkedge__item__mlift: edge -> mlift =
  fun projectee  ->
    match projectee with
    | { msource = __fname__msource; mtarget = __fname__mtarget;
        mlift = __fname__mlift;_} -> __fname__mlift
type effects =
  {
  decls:
    (FStar_Syntax_Syntax.eff_decl* FStar_Syntax_Syntax.qualifier Prims.list)
      Prims.list;
  order: edge Prims.list;
  joins:
    (FStar_Ident.lident* FStar_Ident.lident* FStar_Ident.lident* mlift*
      mlift) Prims.list;}
let __proj__Mkeffects__item__decls:
  effects ->
    (FStar_Syntax_Syntax.eff_decl* FStar_Syntax_Syntax.qualifier Prims.list)
      Prims.list
  =
  fun projectee  ->
    match projectee with
    | { decls = __fname__decls; order = __fname__order;
        joins = __fname__joins;_} -> __fname__decls
let __proj__Mkeffects__item__order: effects -> edge Prims.list =
  fun projectee  ->
    match projectee with
    | { decls = __fname__decls; order = __fname__order;
        joins = __fname__joins;_} -> __fname__order
let __proj__Mkeffects__item__joins:
  effects ->
    (FStar_Ident.lident* FStar_Ident.lident* FStar_Ident.lident* mlift*
      mlift) Prims.list
  =
  fun projectee  ->
    match projectee with
    | { decls = __fname__decls; order = __fname__order;
        joins = __fname__joins;_} -> __fname__joins
type name_prefix = Prims.string Prims.list
type flat_proof_namespace = (name_prefix* Prims.bool) Prims.list
type proof_namespace = flat_proof_namespace Prims.list
type cached_elt =
  (((FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.typ),(FStar_Syntax_Syntax.sigelt*
                                                               FStar_Syntax_Syntax.universes
                                                               option))
    FStar_Util.either* FStar_Range.range)
type goal = FStar_Syntax_Syntax.term
type env =
  {
  solver: solver_t;
  range: FStar_Range.range;
  curmodule: FStar_Ident.lident;
  gamma: binding Prims.list;
  gamma_cache: cached_elt FStar_Util.smap;
  modules: FStar_Syntax_Syntax.modul Prims.list;
  expected_typ: FStar_Syntax_Syntax.typ option;
  sigtab: FStar_Syntax_Syntax.sigelt FStar_Util.smap;
  is_pattern: Prims.bool;
  instantiate_imp: Prims.bool;
  effects: effects;
  generalize: Prims.bool;
  letrecs: (FStar_Syntax_Syntax.lbname* FStar_Syntax_Syntax.typ) Prims.list;
  top_level: Prims.bool;
  check_uvars: Prims.bool;
  use_eq: Prims.bool;
  is_iface: Prims.bool;
  admit: Prims.bool;
  lax: Prims.bool;
  lax_universes: Prims.bool;
  type_of:
    env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.typ* guard_t);
  universe_of:
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe;
  use_bv_sorts: Prims.bool;
  qname_and_index: (FStar_Ident.lident* Prims.int) option;
  proof_ns: proof_namespace;
  synth:
    env ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term;}
and solver_t =
  {
  init: env -> Prims.unit;
  push: Prims.string -> Prims.unit;
  pop: Prims.string -> Prims.unit;
  mark: Prims.string -> Prims.unit;
  reset_mark: Prims.string -> Prims.unit;
  commit_mark: Prims.string -> Prims.unit;
  encode_modul: env -> FStar_Syntax_Syntax.modul -> Prims.unit;
  encode_sig: env -> FStar_Syntax_Syntax.sigelt -> Prims.unit;
  preprocess:
    env -> goal -> (env* goal* FStar_Options.optionstate) Prims.list;
  solve:
    (Prims.unit -> Prims.string) option ->
      env -> FStar_Syntax_Syntax.typ -> Prims.unit;
  is_trivial: env -> FStar_Syntax_Syntax.typ -> Prims.bool;
  finish: Prims.unit -> Prims.unit;
  refresh: Prims.unit -> Prims.unit;}
and guard_t =
  {
  guard_f: FStar_TypeChecker_Common.guard_formula;
  deferred: FStar_TypeChecker_Common.deferred;
  univ_ineqs:
    (FStar_Syntax_Syntax.universe Prims.list*
      FStar_TypeChecker_Common.univ_ineq Prims.list);
  implicits:
    (Prims.string* env* FStar_Syntax_Syntax.uvar* FStar_Syntax_Syntax.term*
      FStar_Syntax_Syntax.typ* FStar_Range.range) Prims.list;}
let __proj__Mkenv__item__solver: env -> solver_t =
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
        proof_ns = __fname__proof_ns; synth = __fname__synth;_} ->
        __fname__solver
let __proj__Mkenv__item__range: env -> FStar_Range.range =
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
        proof_ns = __fname__proof_ns; synth = __fname__synth;_} ->
        __fname__range
let __proj__Mkenv__item__curmodule: env -> FStar_Ident.lident =
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
        proof_ns = __fname__proof_ns; synth = __fname__synth;_} ->
        __fname__curmodule
let __proj__Mkenv__item__gamma: env -> binding Prims.list =
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
        proof_ns = __fname__proof_ns; synth = __fname__synth;_} ->
        __fname__gamma
let __proj__Mkenv__item__gamma_cache: env -> cached_elt FStar_Util.smap =
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
        proof_ns = __fname__proof_ns; synth = __fname__synth;_} ->
        __fname__gamma_cache
let __proj__Mkenv__item__modules: env -> FStar_Syntax_Syntax.modul Prims.list
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
        proof_ns = __fname__proof_ns; synth = __fname__synth;_} ->
        __fname__modules
let __proj__Mkenv__item__expected_typ: env -> FStar_Syntax_Syntax.typ option
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
        proof_ns = __fname__proof_ns; synth = __fname__synth;_} ->
        __fname__expected_typ
let __proj__Mkenv__item__sigtab:
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
        proof_ns = __fname__proof_ns; synth = __fname__synth;_} ->
        __fname__sigtab
let __proj__Mkenv__item__is_pattern: env -> Prims.bool =
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
        proof_ns = __fname__proof_ns; synth = __fname__synth;_} ->
        __fname__is_pattern
let __proj__Mkenv__item__instantiate_imp: env -> Prims.bool =
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
        proof_ns = __fname__proof_ns; synth = __fname__synth;_} ->
        __fname__instantiate_imp
let __proj__Mkenv__item__effects: env -> effects =
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
        proof_ns = __fname__proof_ns; synth = __fname__synth;_} ->
        __fname__effects
let __proj__Mkenv__item__generalize: env -> Prims.bool =
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
        proof_ns = __fname__proof_ns; synth = __fname__synth;_} ->
        __fname__generalize
let __proj__Mkenv__item__letrecs:
  env -> (FStar_Syntax_Syntax.lbname* FStar_Syntax_Syntax.typ) Prims.list =
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
        proof_ns = __fname__proof_ns; synth = __fname__synth;_} ->
        __fname__letrecs
let __proj__Mkenv__item__top_level: env -> Prims.bool =
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
        proof_ns = __fname__proof_ns; synth = __fname__synth;_} ->
        __fname__top_level
let __proj__Mkenv__item__check_uvars: env -> Prims.bool =
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
        proof_ns = __fname__proof_ns; synth = __fname__synth;_} ->
        __fname__check_uvars
let __proj__Mkenv__item__use_eq: env -> Prims.bool =
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
        proof_ns = __fname__proof_ns; synth = __fname__synth;_} ->
        __fname__use_eq
let __proj__Mkenv__item__is_iface: env -> Prims.bool =
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
        proof_ns = __fname__proof_ns; synth = __fname__synth;_} ->
        __fname__is_iface
let __proj__Mkenv__item__admit: env -> Prims.bool =
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
        proof_ns = __fname__proof_ns; synth = __fname__synth;_} ->
        __fname__admit
let __proj__Mkenv__item__lax: env -> Prims.bool =
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
        proof_ns = __fname__proof_ns; synth = __fname__synth;_} ->
        __fname__lax
let __proj__Mkenv__item__lax_universes: env -> Prims.bool =
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
        proof_ns = __fname__proof_ns; synth = __fname__synth;_} ->
        __fname__lax_universes
let __proj__Mkenv__item__type_of:
  env ->
    env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.typ* guard_t)
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
        proof_ns = __fname__proof_ns; synth = __fname__synth;_} ->
        __fname__type_of
let __proj__Mkenv__item__universe_of:
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
        proof_ns = __fname__proof_ns; synth = __fname__synth;_} ->
        __fname__universe_of
let __proj__Mkenv__item__use_bv_sorts: env -> Prims.bool =
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
        proof_ns = __fname__proof_ns; synth = __fname__synth;_} ->
        __fname__use_bv_sorts
let __proj__Mkenv__item__qname_and_index:
  env -> (FStar_Ident.lident* Prims.int) option =
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
        proof_ns = __fname__proof_ns; synth = __fname__synth;_} ->
        __fname__qname_and_index
let __proj__Mkenv__item__proof_ns: env -> proof_namespace =
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
        proof_ns = __fname__proof_ns; synth = __fname__synth;_} ->
        __fname__proof_ns
let __proj__Mkenv__item__synth:
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
        proof_ns = __fname__proof_ns; synth = __fname__synth;_} ->
        __fname__synth
let __proj__Mksolver_t__item__init: solver_t -> env -> Prims.unit =
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
let __proj__Mksolver_t__item__push: solver_t -> Prims.string -> Prims.unit =
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
let __proj__Mksolver_t__item__pop: solver_t -> Prims.string -> Prims.unit =
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
let __proj__Mksolver_t__item__mark: solver_t -> Prims.string -> Prims.unit =
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
let __proj__Mksolver_t__item__reset_mark:
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
let __proj__Mksolver_t__item__commit_mark:
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
let __proj__Mksolver_t__item__encode_modul:
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
let __proj__Mksolver_t__item__encode_sig:
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
let __proj__Mksolver_t__item__preprocess:
  solver_t ->
    env -> goal -> (env* goal* FStar_Options.optionstate) Prims.list
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
let __proj__Mksolver_t__item__solve:
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
let __proj__Mksolver_t__item__is_trivial:
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
let __proj__Mksolver_t__item__finish: solver_t -> Prims.unit -> Prims.unit =
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
let __proj__Mksolver_t__item__refresh: solver_t -> Prims.unit -> Prims.unit =
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
let __proj__Mkguard_t__item__guard_f:
  guard_t -> FStar_TypeChecker_Common.guard_formula =
  fun projectee  ->
    match projectee with
    | { guard_f = __fname__guard_f; deferred = __fname__deferred;
        univ_ineqs = __fname__univ_ineqs; implicits = __fname__implicits;_}
        -> __fname__guard_f
let __proj__Mkguard_t__item__deferred:
  guard_t -> FStar_TypeChecker_Common.deferred =
  fun projectee  ->
    match projectee with
    | { guard_f = __fname__guard_f; deferred = __fname__deferred;
        univ_ineqs = __fname__univ_ineqs; implicits = __fname__implicits;_}
        -> __fname__deferred
let __proj__Mkguard_t__item__univ_ineqs:
  guard_t ->
    (FStar_Syntax_Syntax.universe Prims.list*
      FStar_TypeChecker_Common.univ_ineq Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { guard_f = __fname__guard_f; deferred = __fname__deferred;
        univ_ineqs = __fname__univ_ineqs; implicits = __fname__implicits;_}
        -> __fname__univ_ineqs
let __proj__Mkguard_t__item__implicits:
  guard_t ->
    (Prims.string* env* FStar_Syntax_Syntax.uvar* FStar_Syntax_Syntax.term*
      FStar_Syntax_Syntax.typ* FStar_Range.range) Prims.list
  =
  fun projectee  ->
    match projectee with
    | { guard_f = __fname__guard_f; deferred = __fname__deferred;
        univ_ineqs = __fname__univ_ineqs; implicits = __fname__implicits;_}
        -> __fname__implicits
type implicits =
  (Prims.string* env* FStar_Syntax_Syntax.uvar* FStar_Syntax_Syntax.term*
    FStar_Syntax_Syntax.typ* FStar_Range.range) Prims.list
type env_t = env
type sigtable = FStar_Syntax_Syntax.sigelt FStar_Util.smap
let should_verify: env -> Prims.bool =
  fun env  ->
    ((Prims.op_Negation env.lax) && (Prims.op_Negation env.admit)) &&
      (FStar_Options.should_verify (env.curmodule).FStar_Ident.str)
let visible_at: delta_level -> FStar_Syntax_Syntax.qualifier -> Prims.bool =
  fun d  ->
    fun q  ->
      match (d, q) with
      | (NoDelta ,uu____3239) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____3240,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) ->
          true
      | (Unfold uu____3241,FStar_Syntax_Syntax.Visible_default ) -> true
      | (Inlining ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____3242 -> false
let default_table_size: Prims.int = Prims.parse_int "200"
let new_sigtab uu____3252 = FStar_Util.smap_create default_table_size
let new_gamma_cache uu____3260 =
  FStar_Util.smap_create (Prims.parse_int "100")
let initial_env:
  (env ->
     FStar_Syntax_Syntax.term ->
       (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.typ* guard_t))
    ->
    (env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe) ->
      solver_t -> FStar_Ident.lident -> env
  =
  fun type_of  ->
    fun universe_of  ->
      fun solver  ->
        fun module_lid  ->
          let uu____3299 = new_gamma_cache () in
          let uu____3301 = new_sigtab () in
          let uu____3303 =
            let uu____3304 = FStar_Options.using_facts_from () in
            match uu____3304 with
            | Some ns ->
                let uu____3310 =
                  let uu____3315 =
                    FStar_List.map
                      (fun s  -> ((FStar_Ident.path_of_text s), true)) ns in
                  FStar_List.append uu____3315 [([], false)] in
                [uu____3310]
            | None  -> [[]] in
          {
            solver;
            range = FStar_Range.dummyRange;
            curmodule = module_lid;
            gamma = [];
            gamma_cache = uu____3299;
            modules = [];
            expected_typ = None;
            sigtab = uu____3301;
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
            proof_ns = uu____3303;
            synth =
              (fun e  ->
                 fun g  -> fun tau  -> failwith "no synthesizer available")
          }
let sigtab: env -> FStar_Syntax_Syntax.sigelt FStar_Util.smap =
  fun env  -> env.sigtab
let gamma_cache: env -> cached_elt FStar_Util.smap =
  fun env  -> env.gamma_cache
let query_indices:
  (FStar_Ident.lident* Prims.int) Prims.list Prims.list FStar_ST.ref =
  FStar_Util.mk_ref [[]]
let push_query_indices: Prims.unit -> Prims.unit =
  fun uu____3396  ->
    let uu____3397 = FStar_ST.read query_indices in
    match uu____3397 with
    | [] -> failwith "Empty query indices!"
    | uu____3411 ->
        let uu____3416 =
          let uu____3421 =
            let uu____3425 = FStar_ST.read query_indices in
            FStar_List.hd uu____3425 in
          let uu____3439 = FStar_ST.read query_indices in uu____3421 ::
            uu____3439 in
        FStar_ST.write query_indices uu____3416
let pop_query_indices: Prims.unit -> Prims.unit =
  fun uu____3461  ->
    let uu____3462 = FStar_ST.read query_indices in
    match uu____3462 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.write query_indices tl1
let add_query_index: (FStar_Ident.lident* Prims.int) -> Prims.unit =
  fun uu____3498  ->
    match uu____3498 with
    | (l,n1) ->
        let uu____3503 = FStar_ST.read query_indices in
        (match uu____3503 with
         | hd1::tl1 -> FStar_ST.write query_indices (((l, n1) :: hd1) :: tl1)
         | uu____3537 -> failwith "Empty query indices")
let peek_query_indices:
  Prims.unit -> (FStar_Ident.lident* Prims.int) Prims.list =
  fun uu____3547  ->
    let uu____3548 = FStar_ST.read query_indices in FStar_List.hd uu____3548
let commit_query_index_mark: Prims.unit -> Prims.unit =
  fun uu____3564  ->
    let uu____3565 = FStar_ST.read query_indices in
    match uu____3565 with
    | hd1::uu____3577::tl1 -> FStar_ST.write query_indices (hd1 :: tl1)
    | uu____3604 -> failwith "Unmarked query index stack"
let stack: env Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let push_stack: env -> env =
  fun env  ->
    (let uu____3618 =
       let uu____3620 = FStar_ST.read stack in env :: uu____3620 in
     FStar_ST.write stack uu____3618);
    (let uu___112_3628 = env in
     let uu____3629 = FStar_Util.smap_copy (gamma_cache env) in
     let uu____3631 = FStar_Util.smap_copy (sigtab env) in
     {
       solver = (uu___112_3628.solver);
       range = (uu___112_3628.range);
       curmodule = (uu___112_3628.curmodule);
       gamma = (uu___112_3628.gamma);
       gamma_cache = uu____3629;
       modules = (uu___112_3628.modules);
       expected_typ = (uu___112_3628.expected_typ);
       sigtab = uu____3631;
       is_pattern = (uu___112_3628.is_pattern);
       instantiate_imp = (uu___112_3628.instantiate_imp);
       effects = (uu___112_3628.effects);
       generalize = (uu___112_3628.generalize);
       letrecs = (uu___112_3628.letrecs);
       top_level = (uu___112_3628.top_level);
       check_uvars = (uu___112_3628.check_uvars);
       use_eq = (uu___112_3628.use_eq);
       is_iface = (uu___112_3628.is_iface);
       admit = (uu___112_3628.admit);
       lax = (uu___112_3628.lax);
       lax_universes = (uu___112_3628.lax_universes);
       type_of = (uu___112_3628.type_of);
       universe_of = (uu___112_3628.universe_of);
       use_bv_sorts = (uu___112_3628.use_bv_sorts);
       qname_and_index = (uu___112_3628.qname_and_index);
       proof_ns = (uu___112_3628.proof_ns);
       synth = (uu___112_3628.synth)
     })
let pop_stack: Prims.unit -> env =
  fun uu____3635  ->
    let uu____3636 = FStar_ST.read stack in
    match uu____3636 with
    | env::tl1 -> (FStar_ST.write stack tl1; env)
    | uu____3648 -> failwith "Impossible: Too many pops"
let cleanup_interactive: env -> Prims.unit = fun env  -> (env.solver).pop ""
let push: env -> Prims.string -> env =
  fun env  ->
    fun msg  -> push_query_indices (); (env.solver).push msg; push_stack env
let pop: env -> Prims.string -> env =
  fun env  ->
    fun msg  -> (env.solver).pop msg; pop_query_indices (); pop_stack ()
let mark: env -> env =
  fun env  ->
    (env.solver).mark "USER MARK"; push_query_indices (); push_stack env
let commit_mark: env -> env =
  fun env  ->
    commit_query_index_mark ();
    (env.solver).commit_mark "USER MARK";
    (let uu____3680 = pop_stack () in ());
    env
let reset_mark: env -> env =
  fun env  ->
    (env.solver).reset_mark "USER MARK"; pop_query_indices (); pop_stack ()
let incr_query_index: env -> env =
  fun env  ->
    let qix = peek_query_indices () in
    match env.qname_and_index with
    | None  -> env
    | Some (l,n1) ->
        let uu____3699 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____3711  ->
                  match uu____3711 with
                  | (m,uu____3715) -> FStar_Ident.lid_equals l m)) in
        (match uu____3699 with
         | None  ->
             let next = n1 + (Prims.parse_int "1") in
             (add_query_index (l, next);
              (let uu___113_3720 = env in
               {
                 solver = (uu___113_3720.solver);
                 range = (uu___113_3720.range);
                 curmodule = (uu___113_3720.curmodule);
                 gamma = (uu___113_3720.gamma);
                 gamma_cache = (uu___113_3720.gamma_cache);
                 modules = (uu___113_3720.modules);
                 expected_typ = (uu___113_3720.expected_typ);
                 sigtab = (uu___113_3720.sigtab);
                 is_pattern = (uu___113_3720.is_pattern);
                 instantiate_imp = (uu___113_3720.instantiate_imp);
                 effects = (uu___113_3720.effects);
                 generalize = (uu___113_3720.generalize);
                 letrecs = (uu___113_3720.letrecs);
                 top_level = (uu___113_3720.top_level);
                 check_uvars = (uu___113_3720.check_uvars);
                 use_eq = (uu___113_3720.use_eq);
                 is_iface = (uu___113_3720.is_iface);
                 admit = (uu___113_3720.admit);
                 lax = (uu___113_3720.lax);
                 lax_universes = (uu___113_3720.lax_universes);
                 type_of = (uu___113_3720.type_of);
                 universe_of = (uu___113_3720.universe_of);
                 use_bv_sorts = (uu___113_3720.use_bv_sorts);
                 qname_and_index = (Some (l, next));
                 proof_ns = (uu___113_3720.proof_ns);
                 synth = (uu___113_3720.synth)
               }))
         | Some (uu____3723,m) ->
             let next = m + (Prims.parse_int "1") in
             (add_query_index (l, next);
              (let uu___114_3729 = env in
               {
                 solver = (uu___114_3729.solver);
                 range = (uu___114_3729.range);
                 curmodule = (uu___114_3729.curmodule);
                 gamma = (uu___114_3729.gamma);
                 gamma_cache = (uu___114_3729.gamma_cache);
                 modules = (uu___114_3729.modules);
                 expected_typ = (uu___114_3729.expected_typ);
                 sigtab = (uu___114_3729.sigtab);
                 is_pattern = (uu___114_3729.is_pattern);
                 instantiate_imp = (uu___114_3729.instantiate_imp);
                 effects = (uu___114_3729.effects);
                 generalize = (uu___114_3729.generalize);
                 letrecs = (uu___114_3729.letrecs);
                 top_level = (uu___114_3729.top_level);
                 check_uvars = (uu___114_3729.check_uvars);
                 use_eq = (uu___114_3729.use_eq);
                 is_iface = (uu___114_3729.is_iface);
                 admit = (uu___114_3729.admit);
                 lax = (uu___114_3729.lax);
                 lax_universes = (uu___114_3729.lax_universes);
                 type_of = (uu___114_3729.type_of);
                 universe_of = (uu___114_3729.universe_of);
                 use_bv_sorts = (uu___114_3729.use_bv_sorts);
                 qname_and_index = (Some (l, next));
                 proof_ns = (uu___114_3729.proof_ns);
                 synth = (uu___114_3729.synth)
               })))
let debug: env -> FStar_Options.debug_level_t -> Prims.bool =
  fun env  ->
    fun l  -> FStar_Options.debug_at_level (env.curmodule).FStar_Ident.str l
let set_range: env -> FStar_Range.range -> env =
  fun e  ->
    fun r  ->
      if r = FStar_Range.dummyRange
      then e
      else
        (let uu___115_3745 = e in
         {
           solver = (uu___115_3745.solver);
           range = r;
           curmodule = (uu___115_3745.curmodule);
           gamma = (uu___115_3745.gamma);
           gamma_cache = (uu___115_3745.gamma_cache);
           modules = (uu___115_3745.modules);
           expected_typ = (uu___115_3745.expected_typ);
           sigtab = (uu___115_3745.sigtab);
           is_pattern = (uu___115_3745.is_pattern);
           instantiate_imp = (uu___115_3745.instantiate_imp);
           effects = (uu___115_3745.effects);
           generalize = (uu___115_3745.generalize);
           letrecs = (uu___115_3745.letrecs);
           top_level = (uu___115_3745.top_level);
           check_uvars = (uu___115_3745.check_uvars);
           use_eq = (uu___115_3745.use_eq);
           is_iface = (uu___115_3745.is_iface);
           admit = (uu___115_3745.admit);
           lax = (uu___115_3745.lax);
           lax_universes = (uu___115_3745.lax_universes);
           type_of = (uu___115_3745.type_of);
           universe_of = (uu___115_3745.universe_of);
           use_bv_sorts = (uu___115_3745.use_bv_sorts);
           qname_and_index = (uu___115_3745.qname_and_index);
           proof_ns = (uu___115_3745.proof_ns);
           synth = (uu___115_3745.synth)
         })
let get_range: env -> FStar_Range.range = fun e  -> e.range
let modules: env -> FStar_Syntax_Syntax.modul Prims.list =
  fun env  -> env.modules
let current_module: env -> FStar_Ident.lident = fun env  -> env.curmodule
let set_current_module: env -> FStar_Ident.lident -> env =
  fun env  ->
    fun lid  ->
      let uu___116_3762 = env in
      {
        solver = (uu___116_3762.solver);
        range = (uu___116_3762.range);
        curmodule = lid;
        gamma = (uu___116_3762.gamma);
        gamma_cache = (uu___116_3762.gamma_cache);
        modules = (uu___116_3762.modules);
        expected_typ = (uu___116_3762.expected_typ);
        sigtab = (uu___116_3762.sigtab);
        is_pattern = (uu___116_3762.is_pattern);
        instantiate_imp = (uu___116_3762.instantiate_imp);
        effects = (uu___116_3762.effects);
        generalize = (uu___116_3762.generalize);
        letrecs = (uu___116_3762.letrecs);
        top_level = (uu___116_3762.top_level);
        check_uvars = (uu___116_3762.check_uvars);
        use_eq = (uu___116_3762.use_eq);
        is_iface = (uu___116_3762.is_iface);
        admit = (uu___116_3762.admit);
        lax = (uu___116_3762.lax);
        lax_universes = (uu___116_3762.lax_universes);
        type_of = (uu___116_3762.type_of);
        universe_of = (uu___116_3762.universe_of);
        use_bv_sorts = (uu___116_3762.use_bv_sorts);
        qname_and_index = (uu___116_3762.qname_and_index);
        proof_ns = (uu___116_3762.proof_ns);
        synth = (uu___116_3762.synth)
      }
let has_interface: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      FStar_All.pipe_right env.modules
        (FStar_Util.for_some
           (fun m  ->
              m.FStar_Syntax_Syntax.is_interface &&
                (FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name l)))
let find_in_sigtab:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.sigelt option =
  fun env  ->
    fun lid  ->
      FStar_Util.smap_try_find (sigtab env) (FStar_Ident.text_of_lid lid)
let name_not_found: FStar_Ident.lid -> Prims.string =
  fun l  -> FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str
let variable_not_found: FStar_Syntax_Syntax.bv -> Prims.string =
  fun v1  ->
    let uu____3784 = FStar_Syntax_Print.bv_to_string v1 in
    FStar_Util.format1 "Variable \"%s\" not found" uu____3784
let new_u_univ: Prims.unit -> FStar_Syntax_Syntax.universe =
  fun uu____3787  ->
    let uu____3788 = FStar_Syntax_Unionfind.univ_fresh () in
    FStar_Syntax_Syntax.U_unif uu____3788
let inst_tscheme_with:
  FStar_Syntax_Syntax.tscheme ->
    FStar_Syntax_Syntax.universes ->
      (FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.term)
  =
  fun ts  ->
    fun us  ->
      match (ts, us) with
      | (([],t),[]) -> ([], t)
      | ((formals,t),uu____3810) ->
          let n1 = (FStar_List.length formals) - (Prims.parse_int "1") in
          let vs =
            FStar_All.pipe_right us
              (FStar_List.mapi
                 (fun i  -> fun u  -> FStar_Syntax_Syntax.UN ((n1 - i), u))) in
          let uu____3829 = FStar_Syntax_Subst.subst vs t in (us, uu____3829)
let inst_tscheme:
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.term)
  =
  fun uu___100_3834  ->
    match uu___100_3834 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____3848  -> new_u_univ ())) in
        inst_tscheme_with (us, t) us'
let inst_tscheme_with_range:
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.term)
  =
  fun r  ->
    fun t  ->
      let uu____3858 = inst_tscheme t in
      match uu____3858 with
      | (us,t1) ->
          let uu____3865 = FStar_Syntax_Subst.set_use_range r t1 in
          (us, uu____3865)
let inst_effect_fun_with:
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____3877  ->
          match uu____3877 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____3895 =
                         let uu____3896 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1) in
                         let uu____3901 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts) in
                         let uu____3906 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname in
                         let uu____3907 = FStar_Syntax_Print.term_to_string t in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____3896 uu____3901 uu____3906 uu____3907 in
                       failwith uu____3895)
                    else ();
                    (let uu____3909 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts in
                     snd uu____3909))
               | uu____3913 ->
                   let uu____3914 =
                     let uu____3915 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____3915 in
                   failwith uu____3914)
type tri =
  | Yes
  | No
  | Maybe
let uu___is_Yes: tri -> Prims.bool =
  fun projectee  -> match projectee with | Yes  -> true | uu____3919 -> false
let uu___is_No: tri -> Prims.bool =
  fun projectee  -> match projectee with | No  -> true | uu____3923 -> false
let uu___is_Maybe: tri -> Prims.bool =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____3927 -> false
let in_cur_mod: env -> FStar_Ident.lident -> tri =
  fun env  ->
    fun l  ->
      let cur = current_module env in
      if l.FStar_Ident.nsstr = cur.FStar_Ident.str
      then Yes
      else
        if FStar_Util.starts_with l.FStar_Ident.nsstr cur.FStar_Ident.str
        then
          (let lns = FStar_List.append l.FStar_Ident.ns [l.FStar_Ident.ident] in
           let cur1 =
             FStar_List.append cur.FStar_Ident.ns [cur.FStar_Ident.ident] in
           let rec aux c l1 =
             match (c, l1) with
             | ([],uu____3953) -> Maybe
             | (uu____3957,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____3969 -> No in
           aux cur1 lns)
        else No
let lookup_qname:
  env ->
    FStar_Ident.lident ->
      (((FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.typ),(FStar_Syntax_Syntax.sigelt*
                                                                   FStar_Syntax_Syntax.universes
                                                                   option))
        FStar_Util.either* FStar_Range.range) option
  =
  fun env  ->
    fun lid  ->
      let cur_mod = in_cur_mod env lid in
      let cache t =
        FStar_Util.smap_add (gamma_cache env) lid.FStar_Ident.str t; Some t in
      let found =
        if cur_mod <> No
        then
          let uu____4029 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str in
          match uu____4029 with
          | None  ->
              FStar_Util.find_map env.gamma
                (fun uu___101_4050  ->
                   match uu___101_4050 with
                   | Binding_lid (l,t) ->
                       if FStar_Ident.lid_equals lid l
                       then
                         let uu____4073 =
                           let uu____4083 =
                             let uu____4091 = inst_tscheme t in
                             FStar_Util.Inl uu____4091 in
                           (uu____4083, (FStar_Ident.range_of_lid l)) in
                         Some uu____4073
                       else None
                   | Binding_sig
                       (uu____4125,{
                                     FStar_Syntax_Syntax.sigel =
                                       FStar_Syntax_Syntax.Sig_bundle
                                       (ses,uu____4127);
                                     FStar_Syntax_Syntax.sigrng = uu____4128;
                                     FStar_Syntax_Syntax.sigquals =
                                       uu____4129;
                                     FStar_Syntax_Syntax.sigmeta = uu____4130;_})
                       ->
                       FStar_Util.find_map ses
                         (fun se  ->
                            let uu____4139 =
                              FStar_All.pipe_right
                                (FStar_Syntax_Util.lids_of_sigelt se)
                                (FStar_Util.for_some
                                   (FStar_Ident.lid_equals lid)) in
                            if uu____4139
                            then
                              cache
                                ((FStar_Util.Inr (se, None)),
                                  (FStar_Syntax_Util.range_of_sigelt se))
                            else None)
                   | Binding_sig (lids,s) ->
                       let maybe_cache t =
                         match s.FStar_Syntax_Syntax.sigel with
                         | FStar_Syntax_Syntax.Sig_declare_typ uu____4166 ->
                             Some t
                         | uu____4170 -> cache t in
                       let uu____4171 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids in
                       (match uu____4171 with
                        | None  -> None
                        | Some l ->
                            maybe_cache
                              ((FStar_Util.Inr (s, None)),
                                (FStar_Ident.range_of_lid l)))
                   | Binding_sig_inst (lids,s,us) ->
                       let uu____4211 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids in
                       (match uu____4211 with
                        | None  -> None
                        | Some l ->
                            Some
                              ((FStar_Util.Inr (s, (Some us))),
                                (FStar_Ident.range_of_lid l)))
                   | uu____4255 -> None)
          | se -> se
        else None in
      if FStar_Util.is_some found
      then found
      else
        (let uu____4297 =
           (cur_mod <> Yes) || (has_interface env env.curmodule) in
         if uu____4297
         then
           let uu____4308 = find_in_sigtab env lid in
           match uu____4308 with
           | Some se ->
               Some
                 ((FStar_Util.Inr (se, None)),
                   (FStar_Syntax_Util.range_of_sigelt se))
           | None  -> None
         else None)
let rec add_sigelt: env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____4374) ->
          add_sigelts env ses
      | uu____4379 ->
          let lids = FStar_Syntax_Util.lids_of_sigelt se in
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
                            ne.FStar_Syntax_Syntax.mname a in
                        FStar_Util.smap_add (sigtab env)
                          (a.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                          se_let))
            | uu____4388 -> ()))
and add_sigelts: env -> FStar_Syntax_Syntax.sigelt Prims.list -> Prims.unit =
  fun env  ->
    fun ses  -> FStar_All.pipe_right ses (FStar_List.iter (add_sigelt env))
let try_lookup_bv:
  env ->
    FStar_Syntax_Syntax.bv ->
      ((FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax* FStar_Range.range) option
  =
  fun env  ->
    fun bv  ->
      FStar_Util.find_map env.gamma
        (fun uu___102_4406  ->
           match uu___102_4406 with
           | Binding_var id when FStar_Syntax_Syntax.bv_eq id bv ->
               Some
                 ((id.FStar_Syntax_Syntax.sort),
                   ((id.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____4419 -> None)
let lookup_type_of_let:
  FStar_Syntax_Syntax.sigelt ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.term)*
        FStar_Range.range) option
  =
  fun se  ->
    fun lid  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_let
          ((uu____4440,lb::[]),uu____4442,uu____4443) ->
          let uu____4452 =
            let uu____4457 =
              inst_tscheme
                ((lb.FStar_Syntax_Syntax.lbunivs),
                  (lb.FStar_Syntax_Syntax.lbtyp)) in
            let uu____4463 =
              FStar_Syntax_Syntax.range_of_lbname
                lb.FStar_Syntax_Syntax.lbname in
            (uu____4457, uu____4463) in
          Some uu____4452
      | FStar_Syntax_Syntax.Sig_let ((uu____4470,lbs),uu____4472,uu____4473)
          ->
          FStar_Util.find_map lbs
            (fun lb  ->
               match lb.FStar_Syntax_Syntax.lbname with
               | FStar_Util.Inl uu____4493 -> failwith "impossible"
               | FStar_Util.Inr fv ->
                   let uu____4500 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                   if uu____4500
                   then
                     let uu____4506 =
                       let uu____4511 =
                         inst_tscheme
                           ((lb.FStar_Syntax_Syntax.lbunivs),
                             (lb.FStar_Syntax_Syntax.lbtyp)) in
                       let uu____4517 = FStar_Syntax_Syntax.range_of_fv fv in
                       (uu____4511, uu____4517) in
                     Some uu____4506
                   else None)
      | uu____4529 -> None
let effect_signature:
  FStar_Syntax_Syntax.sigelt ->
    ((FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.term)*
      FStar_Range.range) option
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne ->
        let uu____4548 =
          let uu____4553 =
            let uu____4556 =
              let uu____4557 =
                let uu____4560 =
                  FStar_Syntax_Syntax.mk_Total
                    ne.FStar_Syntax_Syntax.signature in
                FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                  uu____4560 in
              ((ne.FStar_Syntax_Syntax.univs), uu____4557) in
            inst_tscheme uu____4556 in
          (uu____4553, (se.FStar_Syntax_Syntax.sigrng)) in
        Some uu____4548
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,us,binders,uu____4574,uu____4575) ->
        let uu____4578 =
          let uu____4583 =
            let uu____4586 =
              let uu____4587 =
                let uu____4590 =
                  FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff in
                FStar_Syntax_Util.arrow binders uu____4590 in
              (us, uu____4587) in
            inst_tscheme uu____4586 in
          (uu____4583, (se.FStar_Syntax_Syntax.sigrng)) in
        Some uu____4578
    | uu____4601 -> None
let try_lookup_lid_aux:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes*
        (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax)* FStar_Range.range) option
  =
  fun env  ->
    fun lid  ->
      let mapper uu____4636 =
        match uu____4636 with
        | (lr,rng) ->
            (match lr with
             | FStar_Util.Inl t -> Some (t, rng)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_datacon
                      (uu____4686,uvs,t,uu____4689,uu____4690,uu____4691);
                    FStar_Syntax_Syntax.sigrng = uu____4692;
                    FStar_Syntax_Syntax.sigquals = uu____4693;
                    FStar_Syntax_Syntax.sigmeta = uu____4694;_},None
                  )
                 ->
                 let uu____4704 =
                   let uu____4709 = inst_tscheme (uvs, t) in
                   (uu____4709, rng) in
                 Some uu____4704
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                    FStar_Syntax_Syntax.sigrng = uu____4721;
                    FStar_Syntax_Syntax.sigquals = qs;
                    FStar_Syntax_Syntax.sigmeta = uu____4723;_},None
                  )
                 ->
                 let uu____4731 =
                   let uu____4732 = in_cur_mod env l in uu____4732 = Yes in
                 if uu____4731
                 then
                   let uu____4738 =
                     (FStar_All.pipe_right qs
                        (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                       || env.is_iface in
                   (if uu____4738
                    then
                      let uu____4745 =
                        let uu____4750 = inst_tscheme (uvs, t) in
                        (uu____4750, rng) in
                      Some uu____4745
                    else None)
                 else
                   (let uu____4765 =
                      let uu____4770 = inst_tscheme (uvs, t) in
                      (uu____4770, rng) in
                    Some uu____4765)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____4783,uu____4784);
                    FStar_Syntax_Syntax.sigrng = uu____4785;
                    FStar_Syntax_Syntax.sigquals = uu____4786;
                    FStar_Syntax_Syntax.sigmeta = uu____4787;_},None
                  )
                 ->
                 (match tps with
                  | [] ->
                      let uu____4806 =
                        let uu____4811 = inst_tscheme (uvs, k) in
                        (uu____4811, rng) in
                      Some uu____4806
                  | uu____4820 ->
                      let uu____4821 =
                        let uu____4826 =
                          let uu____4829 =
                            let uu____4830 =
                              let uu____4833 = FStar_Syntax_Syntax.mk_Total k in
                              FStar_Syntax_Util.flat_arrow tps uu____4833 in
                            (uvs, uu____4830) in
                          inst_tscheme uu____4829 in
                        (uu____4826, rng) in
                      Some uu____4821)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____4848,uu____4849);
                    FStar_Syntax_Syntax.sigrng = uu____4850;
                    FStar_Syntax_Syntax.sigquals = uu____4851;
                    FStar_Syntax_Syntax.sigmeta = uu____4852;_},Some
                  us)
                 ->
                 (match tps with
                  | [] ->
                      let uu____4872 =
                        let uu____4877 = inst_tscheme_with (uvs, k) us in
                        (uu____4877, rng) in
                      Some uu____4872
                  | uu____4886 ->
                      let uu____4887 =
                        let uu____4892 =
                          let uu____4895 =
                            let uu____4896 =
                              let uu____4899 = FStar_Syntax_Syntax.mk_Total k in
                              FStar_Syntax_Util.flat_arrow tps uu____4899 in
                            (uvs, uu____4896) in
                          inst_tscheme_with uu____4895 us in
                        (uu____4892, rng) in
                      Some uu____4887)
             | FStar_Util.Inr se ->
                 let uu____4919 =
                   match se with
                   | ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let uu____4930;
                        FStar_Syntax_Syntax.sigrng = uu____4931;
                        FStar_Syntax_Syntax.sigquals = uu____4932;
                        FStar_Syntax_Syntax.sigmeta = uu____4933;_},None
                      ) -> lookup_type_of_let (fst se) lid
                   | uu____4942 -> effect_signature (fst se) in
                 FStar_All.pipe_right uu____4919
                   (FStar_Util.map_option
                      (fun uu____4965  ->
                         match uu____4965 with | (us_t,rng1) -> (us_t, rng1)))) in
      let uu____4982 =
        let uu____4988 = lookup_qname env lid in
        FStar_Util.bind_opt uu____4988 mapper in
      match uu____4982 with
      | Some ((us,t),r) ->
          Some
            ((us,
               (let uu___117_5040 = t in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___117_5040.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___117_5040.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid);
                  FStar_Syntax_Syntax.vars =
                    (uu___117_5040.FStar_Syntax_Syntax.vars)
                })), r)
      | None  -> None
let lid_exists: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____5061 = lookup_qname env l in
      match uu____5061 with | None  -> false | Some uu____5081 -> true
let lookup_bv:
  env ->
    FStar_Syntax_Syntax.bv -> (FStar_Syntax_Syntax.typ* FStar_Range.range)
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv in
      let uu____5109 = try_lookup_bv env bv in
      match uu____5109 with
      | None  ->
          let uu____5117 =
            let uu____5118 =
              let uu____5121 = variable_not_found bv in (uu____5121, bvr) in
            FStar_Errors.Error uu____5118 in
          raise uu____5117
      | Some (t,r) ->
          let uu____5128 = FStar_Syntax_Subst.set_use_range bvr t in
          let uu____5129 = FStar_Range.set_use_range r bvr in
          (uu____5128, uu____5129)
let try_lookup_lid:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.typ)*
        FStar_Range.range) option
  =
  fun env  ->
    fun l  ->
      let uu____5141 = try_lookup_lid_aux env l in
      match uu____5141 with
      | None  -> None
      | Some ((us,t),r) ->
          let use_range = FStar_Ident.range_of_lid l in
          let r1 = FStar_Range.set_use_range r use_range in
          let uu____5183 =
            let uu____5188 =
              let uu____5191 = FStar_Syntax_Subst.set_use_range use_range t in
              (us, uu____5191) in
            (uu____5188, r1) in
          Some uu____5183
let lookup_lid:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.typ)*
        FStar_Range.range)
  =
  fun env  ->
    fun l  ->
      let uu____5208 = try_lookup_lid env l in
      match uu____5208 with
      | None  ->
          let uu____5222 =
            let uu____5223 =
              let uu____5226 = name_not_found l in
              (uu____5226, (FStar_Ident.range_of_lid l)) in
            FStar_Errors.Error uu____5223 in
          raise uu____5222
      | Some v1 -> v1
let lookup_univ: env -> FStar_Syntax_Syntax.univ_name -> Prims.bool =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___103_5247  ->
              match uu___103_5247 with
              | Binding_univ y -> x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____5249 -> false) env.gamma) FStar_Option.isSome
let try_lookup_val_decl:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme* FStar_Syntax_Syntax.qualifier Prims.list)
        option
  =
  fun env  ->
    fun lid  ->
      let uu____5260 = lookup_qname env lid in
      match uu____5260 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____5275,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____5278;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____5280;_},None
            ),uu____5281)
          ->
          let uu____5305 =
            let uu____5311 =
              let uu____5314 =
                FStar_Syntax_Subst.set_use_range
                  (FStar_Ident.range_of_lid lid) t in
              (uvs, uu____5314) in
            (uu____5311, q) in
          Some uu____5305
      | uu____5323 -> None
let lookup_val_decl:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun lid  ->
      let uu____5345 = lookup_qname env lid in
      match uu____5345 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____5358,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____5361;
              FStar_Syntax_Syntax.sigquals = uu____5362;
              FStar_Syntax_Syntax.sigmeta = uu____5363;_},None
            ),uu____5364)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____5388 ->
          let uu____5399 =
            let uu____5400 =
              let uu____5403 = name_not_found lid in
              (uu____5403, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____5400 in
          raise uu____5399
let lookup_datacon:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun lid  ->
      let uu____5414 = lookup_qname env lid in
      match uu____5414 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____5427,uvs,t,uu____5430,uu____5431,uu____5432);
              FStar_Syntax_Syntax.sigrng = uu____5433;
              FStar_Syntax_Syntax.sigquals = uu____5434;
              FStar_Syntax_Syntax.sigmeta = uu____5435;_},None
            ),uu____5436)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____5462 ->
          let uu____5473 =
            let uu____5474 =
              let uu____5477 = name_not_found lid in
              (uu____5477, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____5474 in
          raise uu____5473
let datacons_of_typ:
  env -> FStar_Ident.lident -> (Prims.bool* FStar_Ident.lident Prims.list) =
  fun env  ->
    fun lid  ->
      let uu____5489 = lookup_qname env lid in
      match uu____5489 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____5503,uu____5504,uu____5505,uu____5506,uu____5507,dcs);
              FStar_Syntax_Syntax.sigrng = uu____5509;
              FStar_Syntax_Syntax.sigquals = uu____5510;
              FStar_Syntax_Syntax.sigmeta = uu____5511;_},uu____5512),uu____5513)
          -> (true, dcs)
      | uu____5543 -> (false, [])
let typ_of_datacon: env -> FStar_Ident.lident -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      let uu____5561 = lookup_qname env lid in
      match uu____5561 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____5572,uu____5573,uu____5574,l,uu____5576,uu____5577);
              FStar_Syntax_Syntax.sigrng = uu____5578;
              FStar_Syntax_Syntax.sigquals = uu____5579;
              FStar_Syntax_Syntax.sigmeta = uu____5580;_},uu____5581),uu____5582)
          -> l
      | uu____5609 ->
          let uu____5620 =
            let uu____5621 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format1 "Not a datacon: %s" uu____5621 in
          failwith uu____5620
let lookup_definition:
  delta_level Prims.list ->
    env ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.univ_names* FStar_Syntax_Syntax.term) option
  =
  fun delta_levels  ->
    fun env  ->
      fun lid  ->
        let visible quals =
          FStar_All.pipe_right delta_levels
            (FStar_Util.for_some
               (fun dl  ->
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some (visible_at dl)))) in
        let uu____5645 = lookup_qname env lid in
        match uu____5645 with
        | Some (FStar_Util.Inr (se,None ),uu____5660) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_let
                 ((uu____5686,lbs),uu____5688,uu____5689) when
                 visible se.FStar_Syntax_Syntax.sigquals ->
                 FStar_Util.find_map lbs
                   (fun lb  ->
                      let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                      let uu____5706 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                      if uu____5706
                      then
                        Some
                          ((lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbdef))
                      else None)
             | uu____5727 -> None)
        | uu____5730 -> None
let try_lookup_effect_lid:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.typ option =
  fun env  ->
    fun ftv  ->
      let uu____5751 = lookup_qname env ftv in
      match uu____5751 with
      | Some (FStar_Util.Inr (se,None ),uu____5764) ->
          let uu____5787 = effect_signature se in
          (match uu____5787 with
           | None  -> None
           | Some ((uu____5798,t),r) ->
               let uu____5807 =
                 FStar_Syntax_Subst.set_use_range
                   (FStar_Ident.range_of_lid ftv) t in
               Some uu____5807)
      | uu____5808 -> None
let lookup_effect_lid: env -> FStar_Ident.lident -> FStar_Syntax_Syntax.typ =
  fun env  ->
    fun ftv  ->
      let uu____5825 = try_lookup_effect_lid env ftv in
      match uu____5825 with
      | None  ->
          let uu____5827 =
            let uu____5828 =
              let uu____5831 = name_not_found ftv in
              (uu____5831, (FStar_Ident.range_of_lid ftv)) in
            FStar_Errors.Error uu____5828 in
          raise uu____5827
      | Some k -> k
let lookup_effect_abbrev:
  env ->
    FStar_Syntax_Syntax.universes ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.binders* FStar_Syntax_Syntax.comp) option
  =
  fun env  ->
    fun univ_insts  ->
      fun lid0  ->
        let uu____5845 = lookup_qname env lid0 in
        match uu____5845 with
        | Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____5863);
                FStar_Syntax_Syntax.sigrng = uu____5864;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____5866;_},None
              ),uu____5867)
            ->
            let lid1 =
              let uu____5894 =
                FStar_Range.set_use_range (FStar_Ident.range_of_lid lid)
                  (FStar_Ident.range_of_lid lid0) in
              FStar_Ident.set_lid_range lid uu____5894 in
            let uu____5895 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___104_5897  ->
                      match uu___104_5897 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____5898 -> false)) in
            if uu____5895
            then None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____5915 =
                      let uu____5916 = FStar_Syntax_Print.lid_to_string lid1 in
                      let uu____5917 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int in
                      FStar_Util.format2
                        "Unexpected instantiation of effect %s with %s universes"
                        uu____5916 uu____5917 in
                    failwith uu____5915) in
               match (binders, univs1) with
               | ([],uu____5925) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____5934,uu____5935::uu____5936::uu____5937) ->
                   let uu____5940 =
                     let uu____5941 = FStar_Syntax_Print.lid_to_string lid1 in
                     let uu____5942 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1) in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____5941 uu____5942 in
                   failwith uu____5940
               | uu____5950 ->
                   let uu____5953 =
                     let uu____5956 =
                       let uu____5957 = FStar_Syntax_Util.arrow binders c in
                       (univs1, uu____5957) in
                     inst_tscheme_with uu____5956 insts in
                   (match uu____5953 with
                    | (uu____5965,t) ->
                        let t1 =
                          FStar_Syntax_Subst.set_use_range
                            (FStar_Ident.range_of_lid lid1) t in
                        let uu____5968 =
                          let uu____5969 = FStar_Syntax_Subst.compress t1 in
                          uu____5969.FStar_Syntax_Syntax.n in
                        (match uu____5968 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             Some (binders1, c1)
                         | uu____5999 -> failwith "Impossible")))
        | uu____6003 -> None
let norm_eff_name: env -> FStar_Ident.lident -> FStar_Ident.lident =
  let cache = FStar_Util.smap_create (Prims.parse_int "20") in
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____6029 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1 in
        match uu____6029 with
        | None  -> None
        | Some (uu____6036,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c in
            let uu____6041 = find1 l2 in
            (match uu____6041 with | None  -> Some l2 | Some l' -> Some l') in
      let res =
        let uu____6046 = FStar_Util.smap_try_find cache l.FStar_Ident.str in
        match uu____6046 with
        | Some l1 -> l1
        | None  ->
            let uu____6049 = find1 l in
            (match uu____6049 with
             | None  -> l
             | Some m -> (FStar_Util.smap_add cache l.FStar_Ident.str m; m)) in
      FStar_Ident.set_lid_range res (FStar_Ident.range_of_lid l)
let lookup_effect_quals:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l in
      let uu____6061 = lookup_qname env l1 in
      match uu____6061 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____6073;
              FStar_Syntax_Syntax.sigrng = uu____6074;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____6076;_},uu____6077),uu____6078)
          -> q
      | uu____6103 -> []
let lookup_projector:
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail uu____6126 =
          let uu____6127 =
            let uu____6128 = FStar_Util.string_of_int i in
            let uu____6129 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____6128 uu____6129 in
          failwith uu____6127 in
        let uu____6130 = lookup_datacon env lid in
        match uu____6130 with
        | (uu____6133,t) ->
            let uu____6135 =
              let uu____6136 = FStar_Syntax_Subst.compress t in
              uu____6136.FStar_Syntax_Syntax.n in
            (match uu____6135 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____6140) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail ()
                 else
                   (let b = FStar_List.nth binders i in
                    let uu____6163 =
                      FStar_Syntax_Util.mk_field_projector_name lid (fst b) i in
                    FStar_All.pipe_right uu____6163 FStar_Pervasives.fst)
             | uu____6168 -> fail ())
let is_projector: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____6175 = lookup_qname env l in
      match uu____6175 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____6186,uu____6187,uu____6188);
              FStar_Syntax_Syntax.sigrng = uu____6189;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____6191;_},uu____6192),uu____6193)
          ->
          FStar_Util.for_some
            (fun uu___105_6218  ->
               match uu___105_6218 with
               | FStar_Syntax_Syntax.Projector uu____6219 -> true
               | uu____6222 -> false) quals
      | uu____6223 -> false
let is_datacon: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____6240 = lookup_qname env lid in
      match uu____6240 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____6251,uu____6252,uu____6253,uu____6254,uu____6255,uu____6256);
              FStar_Syntax_Syntax.sigrng = uu____6257;
              FStar_Syntax_Syntax.sigquals = uu____6258;
              FStar_Syntax_Syntax.sigmeta = uu____6259;_},uu____6260),uu____6261)
          -> true
      | uu____6288 -> false
let is_record: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____6305 = lookup_qname env lid in
      match uu____6305 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____6316,uu____6317,uu____6318,uu____6319,uu____6320,uu____6321);
              FStar_Syntax_Syntax.sigrng = uu____6322;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____6324;_},uu____6325),uu____6326)
          ->
          FStar_Util.for_some
            (fun uu___106_6355  ->
               match uu___106_6355 with
               | FStar_Syntax_Syntax.RecordType uu____6356 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____6361 -> true
               | uu____6366 -> false) quals
      | uu____6367 -> false
let is_action: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____6384 = lookup_qname env lid in
      match uu____6384 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                (uu____6395,uu____6396,uu____6397);
              FStar_Syntax_Syntax.sigrng = uu____6398;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____6400;_},uu____6401),uu____6402)
          ->
          FStar_Util.for_some
            (fun uu___107_6431  ->
               match uu___107_6431 with
               | FStar_Syntax_Syntax.Action uu____6432 -> true
               | uu____6433 -> false) quals
      | uu____6434 -> false
let is_interpreted: env -> FStar_Syntax_Syntax.term -> Prims.bool =
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
    FStar_Syntax_Const.op_Negation] in
  fun env  ->
    fun head1  ->
      let uu____6453 =
        let uu____6454 = FStar_Syntax_Util.un_uinst head1 in
        uu____6454.FStar_Syntax_Syntax.n in
      match uu____6453 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          fv.FStar_Syntax_Syntax.fv_delta =
            FStar_Syntax_Syntax.Delta_equational
      | uu____6458 -> false
let is_type_constructor: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let mapper x =
        match fst x with
        | FStar_Util.Inl uu____6496 -> Some false
        | FStar_Util.Inr (se,uu____6505) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____6514 ->
                 Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____6518 -> Some true
             | uu____6527 -> Some false) in
      let uu____6528 =
        let uu____6530 = lookup_qname env lid in
        FStar_Util.bind_opt uu____6530 mapper in
      match uu____6528 with | Some b -> b | None  -> false
let num_inductive_ty_params: env -> FStar_Ident.lident -> Prims.int =
  fun env  ->
    fun lid  ->
      let uu____6557 = lookup_qname env lid in
      match uu____6557 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____6568,uu____6569,tps,uu____6571,uu____6572,uu____6573);
              FStar_Syntax_Syntax.sigrng = uu____6574;
              FStar_Syntax_Syntax.sigquals = uu____6575;
              FStar_Syntax_Syntax.sigmeta = uu____6576;_},uu____6577),uu____6578)
          -> FStar_List.length tps
      | uu____6611 ->
          let uu____6622 =
            let uu____6623 =
              let uu____6626 = name_not_found lid in
              (uu____6626, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____6623 in
          raise uu____6622
let effect_decl_opt:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.eff_decl* FStar_Syntax_Syntax.qualifier
        Prims.list) option
  =
  fun env  ->
    fun l  ->
      FStar_All.pipe_right (env.effects).decls
        (FStar_Util.find_opt
           (fun uu____6648  ->
              match uu____6648 with
              | (d,uu____6653) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
let get_effect_decl:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl =
  fun env  ->
    fun l  ->
      let uu____6662 = effect_decl_opt env l in
      match uu____6662 with
      | None  ->
          let uu____6670 =
            let uu____6671 =
              let uu____6674 = name_not_found l in
              (uu____6674, (FStar_Ident.range_of_lid l)) in
            FStar_Errors.Error uu____6671 in
          raise uu____6670
      | Some md -> fst md
let identity_mlift: mlift =
  {
    mlift_wp = (fun t  -> fun wp  -> wp);
    mlift_term = (Some (fun t  -> fun wp  -> fun e  -> e))
  }
let join:
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> (FStar_Ident.lident* mlift* mlift)
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
            (let uu____6717 =
               FStar_All.pipe_right (env.effects).joins
                 (FStar_Util.find_opt
                    (fun uu____6741  ->
                       match uu____6741 with
                       | (m1,m2,uu____6749,uu____6750,uu____6751) ->
                           (FStar_Ident.lid_equals l1 m1) &&
                             (FStar_Ident.lid_equals l2 m2))) in
             match uu____6717 with
             | None  ->
                 let uu____6760 =
                   let uu____6761 =
                     let uu____6764 =
                       let uu____6765 = FStar_Syntax_Print.lid_to_string l1 in
                       let uu____6766 = FStar_Syntax_Print.lid_to_string l2 in
                       FStar_Util.format2
                         "Effects %s and %s cannot be composed" uu____6765
                         uu____6766 in
                     (uu____6764, (env.range)) in
                   FStar_Errors.Error uu____6761 in
                 raise uu____6760
             | Some (uu____6770,uu____6771,m3,j1,j2) -> (m3, j1, j2))
let monad_leq: env -> FStar_Ident.lident -> FStar_Ident.lident -> edge option
  =
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
  let uu____6818 =
    FStar_All.pipe_right decls
      (FStar_Util.find_opt
         (fun uu____6830  ->
            match uu____6830 with
            | (d,uu____6834) ->
                FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m)) in
  match uu____6818 with
  | None  ->
      let uu____6841 =
        FStar_Util.format1 "Impossible: declaration for monad %s not found"
          m.FStar_Ident.str in
      failwith uu____6841
  | Some (md,_q) ->
      let uu____6850 =
        inst_tscheme
          ((md.FStar_Syntax_Syntax.univs),
            (md.FStar_Syntax_Syntax.signature)) in
      (match uu____6850 with
       | (uu____6857,s) ->
           let s1 = FStar_Syntax_Subst.compress s in
           (match ((md.FStar_Syntax_Syntax.binders),
                    (s1.FStar_Syntax_Syntax.n))
            with
            | ([],FStar_Syntax_Syntax.Tm_arrow
               ((a,uu____6865)::(wp,uu____6867)::[],c)) when
                FStar_Syntax_Syntax.is_teff (FStar_Syntax_Util.comp_result c)
                -> (a, (wp.FStar_Syntax_Syntax.sort))
            | uu____6889 -> failwith "Impossible"))
let wp_signature:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.bv*
        (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax)
  = fun env  -> fun m  -> wp_sig_aux (env.effects).decls m
let null_wp_for_eff:
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
              (let eff_name1 = norm_eff_name env eff_name in
               let ed = get_effect_decl env eff_name1 in
               let null_wp =
                 inst_effect_fun_with [res_u] env ed
                   ed.FStar_Syntax_Syntax.null_wp in
               let null_wp_res =
                 let uu____6925 = get_range env in
                 let uu____6926 =
                   let uu____6929 =
                     let uu____6930 =
                       let uu____6940 =
                         let uu____6942 = FStar_Syntax_Syntax.as_arg res_t in
                         [uu____6942] in
                       (null_wp, uu____6940) in
                     FStar_Syntax_Syntax.Tm_app uu____6930 in
                   FStar_Syntax_Syntax.mk uu____6929 in
                 uu____6926 None uu____6925 in
               let uu____6952 =
                 let uu____6953 =
                   let uu____6959 = FStar_Syntax_Syntax.as_arg null_wp_res in
                   [uu____6959] in
                 {
                   FStar_Syntax_Syntax.comp_univs = [res_u];
                   FStar_Syntax_Syntax.effect_name = eff_name1;
                   FStar_Syntax_Syntax.result_typ = res_t;
                   FStar_Syntax_Syntax.effect_args = uu____6953;
                   FStar_Syntax_Syntax.flags = []
                 } in
               FStar_Syntax_Syntax.mk_Comp uu____6952)
let build_lattice: env -> FStar_Syntax_Syntax.sigelt -> env =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___118_6968 = env.effects in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___118_6968.order);
              joins = (uu___118_6968.joins)
            } in
          let uu___119_6973 = env in
          {
            solver = (uu___119_6973.solver);
            range = (uu___119_6973.range);
            curmodule = (uu___119_6973.curmodule);
            gamma = (uu___119_6973.gamma);
            gamma_cache = (uu___119_6973.gamma_cache);
            modules = (uu___119_6973.modules);
            expected_typ = (uu___119_6973.expected_typ);
            sigtab = (uu___119_6973.sigtab);
            is_pattern = (uu___119_6973.is_pattern);
            instantiate_imp = (uu___119_6973.instantiate_imp);
            effects;
            generalize = (uu___119_6973.generalize);
            letrecs = (uu___119_6973.letrecs);
            top_level = (uu___119_6973.top_level);
            check_uvars = (uu___119_6973.check_uvars);
            use_eq = (uu___119_6973.use_eq);
            is_iface = (uu___119_6973.is_iface);
            admit = (uu___119_6973.admit);
            lax = (uu___119_6973.lax);
            lax_universes = (uu___119_6973.lax_universes);
            type_of = (uu___119_6973.type_of);
            universe_of = (uu___119_6973.universe_of);
            use_bv_sorts = (uu___119_6973.use_bv_sorts);
            qname_and_index = (uu___119_6973.qname_and_index);
            proof_ns = (uu___119_6973.proof_ns);
            synth = (uu___119_6973.synth)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp r wp1 =
                let uu____6990 = (e1.mlift).mlift_wp r wp1 in
                (e2.mlift).mlift_wp r uu____6990 in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (Some l1,Some l2) ->
                    Some
                      ((fun t  ->
                          fun wp  ->
                            fun e  ->
                              let uu____7069 = (e1.mlift).mlift_wp t wp in
                              let uu____7070 = l1 t wp e in
                              l2 t uu____7069 uu____7070))
                | uu____7071 -> None in
              { mlift_wp; mlift_term } in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            } in
          let mk_mlift_wp lift_t r wp1 =
            let uu____7106 = inst_tscheme lift_t in
            match uu____7106 with
            | (uu____7111,lift_t1) ->
                let uu____7113 =
                  let uu____7116 =
                    let uu____7117 =
                      let uu____7127 =
                        let uu____7129 = FStar_Syntax_Syntax.as_arg r in
                        let uu____7130 =
                          let uu____7132 = FStar_Syntax_Syntax.as_arg wp1 in
                          [uu____7132] in
                        uu____7129 :: uu____7130 in
                      (lift_t1, uu____7127) in
                    FStar_Syntax_Syntax.Tm_app uu____7117 in
                  FStar_Syntax_Syntax.mk uu____7116 in
                uu____7113 None wp1.FStar_Syntax_Syntax.pos in
          let sub_mlift_wp =
            match sub1.FStar_Syntax_Syntax.lift_wp with
            | Some sub_lift_wp -> mk_mlift_wp sub_lift_wp
            | None  ->
                failwith "sub effect should've been elaborated at this stage" in
          let mk_mlift_term lift_t r wp1 e =
            let uu____7177 = inst_tscheme lift_t in
            match uu____7177 with
            | (uu____7182,lift_t1) ->
                let uu____7184 =
                  let uu____7187 =
                    let uu____7188 =
                      let uu____7198 =
                        let uu____7200 = FStar_Syntax_Syntax.as_arg r in
                        let uu____7201 =
                          let uu____7203 = FStar_Syntax_Syntax.as_arg wp1 in
                          let uu____7204 =
                            let uu____7206 = FStar_Syntax_Syntax.as_arg e in
                            [uu____7206] in
                          uu____7203 :: uu____7204 in
                        uu____7200 :: uu____7201 in
                      (lift_t1, uu____7198) in
                    FStar_Syntax_Syntax.Tm_app uu____7188 in
                  FStar_Syntax_Syntax.mk uu____7187 in
                uu____7184 None e.FStar_Syntax_Syntax.pos in
          let sub_mlift_term =
            FStar_Util.map_opt sub1.FStar_Syntax_Syntax.lift mk_mlift_term in
          let edge =
            {
              msource = (sub1.FStar_Syntax_Syntax.source);
              mtarget = (sub1.FStar_Syntax_Syntax.target);
              mlift =
                { mlift_wp = sub_mlift_wp; mlift_term = sub_mlift_term }
            } in
          let id_edge l =
            {
              msource = (sub1.FStar_Syntax_Syntax.source);
              mtarget = (sub1.FStar_Syntax_Syntax.target);
              mlift = identity_mlift
            } in
          let print_mlift l =
            let bogus_term s =
              let uu____7247 =
                let uu____7248 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange in
                FStar_Syntax_Syntax.lid_as_fv uu____7248
                  FStar_Syntax_Syntax.Delta_constant None in
              FStar_Syntax_Syntax.fv_to_tm uu____7247 in
            let arg = bogus_term "ARG" in
            let wp = bogus_term "WP" in
            let e = bogus_term "COMP" in
            let uu____7252 =
              let uu____7253 = l.mlift_wp arg wp in
              FStar_Syntax_Print.term_to_string uu____7253 in
            let uu____7254 =
              let uu____7255 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____7270 = l1 arg wp e in
                     FStar_Syntax_Print.term_to_string uu____7270) in
              FStar_Util.dflt "none" uu____7255 in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____7252
              uu____7254 in
          let order = edge :: ((env.effects).order) in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____7283  ->
                    match uu____7283 with
                    | (e,uu____7288) -> e.FStar_Syntax_Syntax.mname)) in
          let find_edge order1 uu____7301 =
            match uu____7301 with
            | (i,j) ->
                if FStar_Ident.lid_equals i j
                then
                  FStar_All.pipe_right (id_edge i) (fun _0_39  -> Some _0_39)
                else
                  FStar_All.pipe_right order1
                    (FStar_Util.find_opt
                       (fun e  ->
                          (FStar_Ident.lid_equals e.msource i) &&
                            (FStar_Ident.lid_equals e.mtarget j))) in
          let order1 =
            let fold_fun order1 k =
              let uu____7326 =
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
                                    (let uu____7338 =
                                       let uu____7343 =
                                         find_edge order1 (i, k) in
                                       let uu____7345 =
                                         find_edge order1 (k, j) in
                                       (uu____7343, uu____7345) in
                                     match uu____7338 with
                                     | (Some e1,Some e2) ->
                                         let uu____7354 = compose_edges e1 e2 in
                                         [uu____7354]
                                     | uu____7355 -> []))))) in
              FStar_List.append order1 uu____7326 in
            FStar_All.pipe_right ms (FStar_List.fold_left fold_fun order) in
          let order2 =
            FStar_Util.remove_dups
              (fun e1  ->
                 fun e2  ->
                   (FStar_Ident.lid_equals e1.msource e2.msource) &&
                     (FStar_Ident.lid_equals e1.mtarget e2.mtarget)) order1 in
          (FStar_All.pipe_right order2
             (FStar_List.iter
                (fun edge1  ->
                   let uu____7370 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Syntax_Const.effect_DIV_lid)
                       &&
                       (let uu____7371 =
                          lookup_effect_quals env edge1.mtarget in
                        FStar_All.pipe_right uu____7371
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect)) in
                   if uu____7370
                   then
                     let uu____7374 =
                       let uu____7375 =
                         let uu____7378 =
                           FStar_Util.format1
                             "Divergent computations cannot be included in an effect %s marked 'total'"
                             (edge1.mtarget).FStar_Ident.str in
                         let uu____7379 = get_range env in
                         (uu____7378, uu____7379) in
                       FStar_Errors.Error uu____7375 in
                     raise uu____7374
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
                                            let uu____7442 =
                                              let uu____7447 =
                                                find_edge order2 (i, k) in
                                              let uu____7449 =
                                                find_edge order2 (j, k) in
                                              (uu____7447, uu____7449) in
                                            match uu____7442 with
                                            | (Some ik,Some jk) ->
                                                (match bopt with
                                                 | None  -> Some (k, ik, jk)
                                                 | Some
                                                     (ub,uu____7472,uu____7473)
                                                     ->
                                                     let uu____7477 =
                                                       let uu____7480 =
                                                         let uu____7481 =
                                                           find_edge order2
                                                             (k, ub) in
                                                         FStar_Util.is_some
                                                           uu____7481 in
                                                       let uu____7483 =
                                                         let uu____7484 =
                                                           find_edge order2
                                                             (ub, k) in
                                                         FStar_Util.is_some
                                                           uu____7484 in
                                                       (uu____7480,
                                                         uu____7483) in
                                                     (match uu____7477 with
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
                                            | uu____7503 -> bopt) None) in
                              match join_opt with
                              | None  -> []
                              | Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))])))) in
            let effects =
              let uu___120_7542 = env.effects in
              { decls = (uu___120_7542.decls); order = order2; joins } in
            let uu___121_7543 = env in
            {
              solver = (uu___121_7543.solver);
              range = (uu___121_7543.range);
              curmodule = (uu___121_7543.curmodule);
              gamma = (uu___121_7543.gamma);
              gamma_cache = (uu___121_7543.gamma_cache);
              modules = (uu___121_7543.modules);
              expected_typ = (uu___121_7543.expected_typ);
              sigtab = (uu___121_7543.sigtab);
              is_pattern = (uu___121_7543.is_pattern);
              instantiate_imp = (uu___121_7543.instantiate_imp);
              effects;
              generalize = (uu___121_7543.generalize);
              letrecs = (uu___121_7543.letrecs);
              top_level = (uu___121_7543.top_level);
              check_uvars = (uu___121_7543.check_uvars);
              use_eq = (uu___121_7543.use_eq);
              is_iface = (uu___121_7543.is_iface);
              admit = (uu___121_7543.admit);
              lax = (uu___121_7543.lax);
              lax_universes = (uu___121_7543.lax_universes);
              type_of = (uu___121_7543.type_of);
              universe_of = (uu___121_7543.universe_of);
              use_bv_sorts = (uu___121_7543.use_bv_sorts);
              qname_and_index = (uu___121_7543.qname_and_index);
              proof_ns = (uu___121_7543.proof_ns);
              synth = (uu___121_7543.synth)
            }))
      | uu____7544 -> env
let comp_to_comp_typ:
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ =
  fun env  ->
    fun c  ->
      let c1 =
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,None ) ->
            let u = env.universe_of env t in
            FStar_Syntax_Syntax.mk_Total' t (Some u)
        | FStar_Syntax_Syntax.GTotal (t,None ) ->
            let u = env.universe_of env t in
            FStar_Syntax_Syntax.mk_GTotal' t (Some u)
        | uu____7566 -> c in
      FStar_Syntax_Util.comp_to_comp_typ c1
let rec unfold_effect_abbrev:
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp in
      let uu____7574 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name in
      match uu____7574 with
      | None  -> c
      | Some (binders,cdef) ->
          let uu____7584 = FStar_Syntax_Subst.open_comp binders cdef in
          (match uu____7584 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____7606 =
                     let uu____7607 =
                       let uu____7610 =
                         let uu____7611 =
                           FStar_Util.string_of_int
                             (FStar_List.length binders1) in
                         let uu____7620 =
                           FStar_Util.string_of_int
                             ((FStar_List.length
                                 c.FStar_Syntax_Syntax.effect_args)
                                + (Prims.parse_int "1")) in
                         let uu____7631 =
                           let uu____7632 = FStar_Syntax_Syntax.mk_Comp c in
                           FStar_Syntax_Print.comp_to_string uu____7632 in
                         FStar_Util.format3
                           "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                           uu____7611 uu____7620 uu____7631 in
                       (uu____7610, (comp.FStar_Syntax_Syntax.pos)) in
                     FStar_Errors.Error uu____7607 in
                   raise uu____7606)
                else ();
                (let inst1 =
                   let uu____7636 =
                     let uu____7642 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ in
                     uu____7642 :: (c.FStar_Syntax_Syntax.effect_args) in
                   FStar_List.map2
                     (fun uu____7649  ->
                        fun uu____7650  ->
                          match (uu____7649, uu____7650) with
                          | ((x,uu____7664),(t,uu____7666)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____7636 in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1 in
                 let c2 =
                   let uu____7681 =
                     let uu___122_7682 = comp_to_comp_typ env c1 in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___122_7682.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___122_7682.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___122_7682.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___122_7682.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     } in
                   FStar_All.pipe_right uu____7681
                     FStar_Syntax_Syntax.mk_Comp in
                 unfold_effect_abbrev env c2)))
let effect_repr_aux only_reifiable env c u_c =
  let uu____7712 =
    let uu____7717 = norm_eff_name env (FStar_Syntax_Util.comp_effect_name c) in
    effect_decl_opt env uu____7717 in
  match uu____7712 with
  | None  -> None
  | Some (ed,qualifiers) ->
      let uu____7733 =
        only_reifiable &&
          (let uu____7734 =
             FStar_All.pipe_right qualifiers
               (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
           Prims.op_Negation uu____7734) in
      if uu____7733
      then None
      else
        (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_unknown  -> None
         | uu____7747 ->
             let c1 = unfold_effect_abbrev env c in
             let uu____7749 =
               let uu____7758 =
                 FStar_List.hd c1.FStar_Syntax_Syntax.effect_args in
               ((c1.FStar_Syntax_Syntax.result_typ), uu____7758) in
             (match uu____7749 with
              | (res_typ,wp) ->
                  let repr =
                    inst_effect_fun_with [u_c] env ed
                      ([], (ed.FStar_Syntax_Syntax.repr)) in
                  let uu____7792 =
                    let uu____7795 = get_range env in
                    let uu____7796 =
                      let uu____7799 =
                        let uu____7800 =
                          let uu____7810 =
                            let uu____7812 =
                              FStar_Syntax_Syntax.as_arg res_typ in
                            [uu____7812; wp] in
                          (repr, uu____7810) in
                        FStar_Syntax_Syntax.Tm_app uu____7800 in
                      FStar_Syntax_Syntax.mk uu____7799 in
                    uu____7796 None uu____7795 in
                  Some uu____7792))
let effect_repr:
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe ->
        (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
          FStar_Syntax_Syntax.syntax option
  = fun env  -> fun c  -> fun u_c  -> effect_repr_aux false env c u_c
let reify_comp:
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun c  ->
      fun u_c  ->
        let no_reify l =
          let uu____7856 =
            let uu____7857 =
              let uu____7860 =
                let uu____7861 = FStar_Ident.string_of_lid l in
                FStar_Util.format1 "Effect %s cannot be reified" uu____7861 in
              let uu____7862 = get_range env in (uu____7860, uu____7862) in
            FStar_Errors.Error uu____7857 in
          raise uu____7856 in
        let uu____7863 = effect_repr_aux true env c u_c in
        match uu____7863 with
        | None  -> no_reify (FStar_Syntax_Util.comp_effect_name c)
        | Some tm -> tm
let is_reifiable_effect: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun effect_lid  ->
      let quals = lookup_effect_quals env effect_lid in
      FStar_List.contains FStar_Syntax_Syntax.Reifiable quals
let is_reifiable:
  env ->
    (FStar_Syntax_Syntax.lcomp,FStar_Syntax_Syntax.residual_comp)
      FStar_Util.either -> Prims.bool
  =
  fun env  ->
    fun c  ->
      let effect_lid =
        match c with
        | FStar_Util.Inl lc -> lc.FStar_Syntax_Syntax.eff_name
        | FStar_Util.Inr (eff_name,uu____7895) -> eff_name in
      is_reifiable_effect env effect_lid
let is_reifiable_comp: env -> FStar_Syntax_Syntax.comp -> Prims.bool =
  fun env  ->
    fun c  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Comp ct ->
          is_reifiable_effect env ct.FStar_Syntax_Syntax.effect_name
      | uu____7908 -> false
let is_reifiable_function: env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____7915 =
        let uu____7916 = FStar_Syntax_Subst.compress t in
        uu____7916.FStar_Syntax_Syntax.n in
      match uu____7915 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____7919,c) ->
          is_reifiable_comp env c
      | uu____7931 -> false
let push_in_gamma: env -> binding -> env =
  fun env  ->
    fun s  ->
      let rec push1 x rest =
        match rest with
        | (Binding_sig uu____7949)::uu____7950 -> x :: rest
        | (Binding_sig_inst uu____7955)::uu____7956 -> x :: rest
        | [] -> [x]
        | local::rest1 ->
            let uu____7965 = push1 x rest1 in local :: uu____7965 in
      let uu___123_7967 = env in
      let uu____7968 = push1 s env.gamma in
      {
        solver = (uu___123_7967.solver);
        range = (uu___123_7967.range);
        curmodule = (uu___123_7967.curmodule);
        gamma = uu____7968;
        gamma_cache = (uu___123_7967.gamma_cache);
        modules = (uu___123_7967.modules);
        expected_typ = (uu___123_7967.expected_typ);
        sigtab = (uu___123_7967.sigtab);
        is_pattern = (uu___123_7967.is_pattern);
        instantiate_imp = (uu___123_7967.instantiate_imp);
        effects = (uu___123_7967.effects);
        generalize = (uu___123_7967.generalize);
        letrecs = (uu___123_7967.letrecs);
        top_level = (uu___123_7967.top_level);
        check_uvars = (uu___123_7967.check_uvars);
        use_eq = (uu___123_7967.use_eq);
        is_iface = (uu___123_7967.is_iface);
        admit = (uu___123_7967.admit);
        lax = (uu___123_7967.lax);
        lax_universes = (uu___123_7967.lax_universes);
        type_of = (uu___123_7967.type_of);
        universe_of = (uu___123_7967.universe_of);
        use_bv_sorts = (uu___123_7967.use_bv_sorts);
        qname_and_index = (uu___123_7967.qname_and_index);
        proof_ns = (uu___123_7967.proof_ns);
        synth = (uu___123_7967.synth)
      }
let push_sigelt: env -> FStar_Syntax_Syntax.sigelt -> env =
  fun env  ->
    fun s  ->
      let env1 =
        push_in_gamma env
          (Binding_sig ((FStar_Syntax_Util.lids_of_sigelt s), s)) in
      build_lattice env1 s
let push_sigelt_inst:
  env -> FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.universes -> env =
  fun env  ->
    fun s  ->
      fun us  ->
        let env1 =
          push_in_gamma env
            (Binding_sig_inst ((FStar_Syntax_Util.lids_of_sigelt s), s, us)) in
        build_lattice env1 s
let push_local_binding: env -> binding -> env =
  fun env  ->
    fun b  ->
      let uu___124_7995 = env in
      {
        solver = (uu___124_7995.solver);
        range = (uu___124_7995.range);
        curmodule = (uu___124_7995.curmodule);
        gamma = (b :: (env.gamma));
        gamma_cache = (uu___124_7995.gamma_cache);
        modules = (uu___124_7995.modules);
        expected_typ = (uu___124_7995.expected_typ);
        sigtab = (uu___124_7995.sigtab);
        is_pattern = (uu___124_7995.is_pattern);
        instantiate_imp = (uu___124_7995.instantiate_imp);
        effects = (uu___124_7995.effects);
        generalize = (uu___124_7995.generalize);
        letrecs = (uu___124_7995.letrecs);
        top_level = (uu___124_7995.top_level);
        check_uvars = (uu___124_7995.check_uvars);
        use_eq = (uu___124_7995.use_eq);
        is_iface = (uu___124_7995.is_iface);
        admit = (uu___124_7995.admit);
        lax = (uu___124_7995.lax);
        lax_universes = (uu___124_7995.lax_universes);
        type_of = (uu___124_7995.type_of);
        universe_of = (uu___124_7995.universe_of);
        use_bv_sorts = (uu___124_7995.use_bv_sorts);
        qname_and_index = (uu___124_7995.qname_and_index);
        proof_ns = (uu___124_7995.proof_ns);
        synth = (uu___124_7995.synth)
      }
let push_bv: env -> FStar_Syntax_Syntax.bv -> env =
  fun env  -> fun x  -> push_local_binding env (Binding_var x)
let pop_bv: env -> (FStar_Syntax_Syntax.bv* env) option =
  fun env  ->
    match env.gamma with
    | (Binding_var x)::rest ->
        Some
          (x,
            (let uu___125_8016 = env in
             {
               solver = (uu___125_8016.solver);
               range = (uu___125_8016.range);
               curmodule = (uu___125_8016.curmodule);
               gamma = rest;
               gamma_cache = (uu___125_8016.gamma_cache);
               modules = (uu___125_8016.modules);
               expected_typ = (uu___125_8016.expected_typ);
               sigtab = (uu___125_8016.sigtab);
               is_pattern = (uu___125_8016.is_pattern);
               instantiate_imp = (uu___125_8016.instantiate_imp);
               effects = (uu___125_8016.effects);
               generalize = (uu___125_8016.generalize);
               letrecs = (uu___125_8016.letrecs);
               top_level = (uu___125_8016.top_level);
               check_uvars = (uu___125_8016.check_uvars);
               use_eq = (uu___125_8016.use_eq);
               is_iface = (uu___125_8016.is_iface);
               admit = (uu___125_8016.admit);
               lax = (uu___125_8016.lax);
               lax_universes = (uu___125_8016.lax_universes);
               type_of = (uu___125_8016.type_of);
               universe_of = (uu___125_8016.universe_of);
               use_bv_sorts = (uu___125_8016.use_bv_sorts);
               qname_and_index = (uu___125_8016.qname_and_index);
               proof_ns = (uu___125_8016.proof_ns);
               synth = (uu___125_8016.synth)
             }))
    | uu____8017 -> None
let push_binders: env -> FStar_Syntax_Syntax.binders -> env =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____8030  ->
             match uu____8030 with | (x,uu____8034) -> push_bv env1 x) env bs
let binding_of_lb:
  FStar_Syntax_Syntax.lbname ->
    (FStar_Syntax_Syntax.univ_name Prims.list*
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax) -> binding
  =
  fun x  ->
    fun t  ->
      match x with
      | FStar_Util.Inl x1 ->
          let x2 =
            let uu___126_8054 = x1 in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___126_8054.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___126_8054.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = (snd t)
            } in
          Binding_var x2
      | FStar_Util.Inr fv ->
          Binding_lid
            (((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v), t)
let push_let_binding:
  env -> FStar_Syntax_Syntax.lbname -> FStar_Syntax_Syntax.tscheme -> env =
  fun env  ->
    fun lb  -> fun ts  -> push_local_binding env (binding_of_lb lb ts)
let push_module: env -> FStar_Syntax_Syntax.modul -> env =
  fun env  ->
    fun m  ->
      add_sigelts env m.FStar_Syntax_Syntax.exports;
      (let uu___127_8084 = env in
       {
         solver = (uu___127_8084.solver);
         range = (uu___127_8084.range);
         curmodule = (uu___127_8084.curmodule);
         gamma = [];
         gamma_cache = (uu___127_8084.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = None;
         sigtab = (uu___127_8084.sigtab);
         is_pattern = (uu___127_8084.is_pattern);
         instantiate_imp = (uu___127_8084.instantiate_imp);
         effects = (uu___127_8084.effects);
         generalize = (uu___127_8084.generalize);
         letrecs = (uu___127_8084.letrecs);
         top_level = (uu___127_8084.top_level);
         check_uvars = (uu___127_8084.check_uvars);
         use_eq = (uu___127_8084.use_eq);
         is_iface = (uu___127_8084.is_iface);
         admit = (uu___127_8084.admit);
         lax = (uu___127_8084.lax);
         lax_universes = (uu___127_8084.lax_universes);
         type_of = (uu___127_8084.type_of);
         universe_of = (uu___127_8084.universe_of);
         use_bv_sorts = (uu___127_8084.use_bv_sorts);
         qname_and_index = (uu___127_8084.qname_and_index);
         proof_ns = (uu___127_8084.proof_ns);
         synth = (uu___127_8084.synth)
       })
let push_univ_vars: env_t -> FStar_Syntax_Syntax.univ_names -> env =
  fun env  ->
    fun xs  ->
      FStar_List.fold_left
        (fun env1  -> fun x  -> push_local_binding env1 (Binding_univ x)) env
        xs
let open_universes_in:
  env ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.term Prims.list ->
        (env* FStar_Syntax_Syntax.univ_names* FStar_Syntax_Syntax.term
          Prims.list)
  =
  fun env  ->
    fun uvs  ->
      fun terms  ->
        let uu____8108 = FStar_Syntax_Subst.univ_var_opening uvs in
        match uu____8108 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars in
            let uu____8124 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms in
            (env', univ_vars, uu____8124)
let set_expected_typ: env -> FStar_Syntax_Syntax.typ -> env =
  fun env  ->
    fun t  ->
      let uu___128_8134 = env in
      {
        solver = (uu___128_8134.solver);
        range = (uu___128_8134.range);
        curmodule = (uu___128_8134.curmodule);
        gamma = (uu___128_8134.gamma);
        gamma_cache = (uu___128_8134.gamma_cache);
        modules = (uu___128_8134.modules);
        expected_typ = (Some t);
        sigtab = (uu___128_8134.sigtab);
        is_pattern = (uu___128_8134.is_pattern);
        instantiate_imp = (uu___128_8134.instantiate_imp);
        effects = (uu___128_8134.effects);
        generalize = (uu___128_8134.generalize);
        letrecs = (uu___128_8134.letrecs);
        top_level = (uu___128_8134.top_level);
        check_uvars = (uu___128_8134.check_uvars);
        use_eq = false;
        is_iface = (uu___128_8134.is_iface);
        admit = (uu___128_8134.admit);
        lax = (uu___128_8134.lax);
        lax_universes = (uu___128_8134.lax_universes);
        type_of = (uu___128_8134.type_of);
        universe_of = (uu___128_8134.universe_of);
        use_bv_sorts = (uu___128_8134.use_bv_sorts);
        qname_and_index = (uu___128_8134.qname_and_index);
        proof_ns = (uu___128_8134.proof_ns);
        synth = (uu___128_8134.synth)
      }
let expected_typ: env -> FStar_Syntax_Syntax.typ option =
  fun env  -> match env.expected_typ with | None  -> None | Some t -> Some t
let clear_expected_typ: env -> (env* FStar_Syntax_Syntax.typ option) =
  fun env_  ->
    let uu____8150 = expected_typ env_ in
    ((let uu___129_8153 = env_ in
      {
        solver = (uu___129_8153.solver);
        range = (uu___129_8153.range);
        curmodule = (uu___129_8153.curmodule);
        gamma = (uu___129_8153.gamma);
        gamma_cache = (uu___129_8153.gamma_cache);
        modules = (uu___129_8153.modules);
        expected_typ = None;
        sigtab = (uu___129_8153.sigtab);
        is_pattern = (uu___129_8153.is_pattern);
        instantiate_imp = (uu___129_8153.instantiate_imp);
        effects = (uu___129_8153.effects);
        generalize = (uu___129_8153.generalize);
        letrecs = (uu___129_8153.letrecs);
        top_level = (uu___129_8153.top_level);
        check_uvars = (uu___129_8153.check_uvars);
        use_eq = false;
        is_iface = (uu___129_8153.is_iface);
        admit = (uu___129_8153.admit);
        lax = (uu___129_8153.lax);
        lax_universes = (uu___129_8153.lax_universes);
        type_of = (uu___129_8153.type_of);
        universe_of = (uu___129_8153.universe_of);
        use_bv_sorts = (uu___129_8153.use_bv_sorts);
        qname_and_index = (uu___129_8153.qname_and_index);
        proof_ns = (uu___129_8153.proof_ns);
        synth = (uu___129_8153.synth)
      }), uu____8150)
let finish_module: env -> FStar_Syntax_Syntax.modul -> env =
  let empty_lid = FStar_Ident.lid_of_ids [FStar_Ident.id_of_text ""] in
  fun env  ->
    fun m  ->
      let sigs =
        if
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Syntax_Const.prims_lid
        then
          let uu____8164 =
            FStar_All.pipe_right env.gamma
              (FStar_List.collect
                 (fun uu___108_8168  ->
                    match uu___108_8168 with
                    | Binding_sig (uu____8170,se) -> [se]
                    | uu____8174 -> [])) in
          FStar_All.pipe_right uu____8164 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports in
      add_sigelts env sigs;
      (let uu___130_8179 = env in
       {
         solver = (uu___130_8179.solver);
         range = (uu___130_8179.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_cache = (uu___130_8179.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___130_8179.expected_typ);
         sigtab = (uu___130_8179.sigtab);
         is_pattern = (uu___130_8179.is_pattern);
         instantiate_imp = (uu___130_8179.instantiate_imp);
         effects = (uu___130_8179.effects);
         generalize = (uu___130_8179.generalize);
         letrecs = (uu___130_8179.letrecs);
         top_level = (uu___130_8179.top_level);
         check_uvars = (uu___130_8179.check_uvars);
         use_eq = (uu___130_8179.use_eq);
         is_iface = (uu___130_8179.is_iface);
         admit = (uu___130_8179.admit);
         lax = (uu___130_8179.lax);
         lax_universes = (uu___130_8179.lax_universes);
         type_of = (uu___130_8179.type_of);
         universe_of = (uu___130_8179.universe_of);
         use_bv_sorts = (uu___130_8179.use_bv_sorts);
         qname_and_index = (uu___130_8179.qname_and_index);
         proof_ns = (uu___130_8179.proof_ns);
         synth = (uu___130_8179.synth)
       })
let uvars_in_env:
  env -> (FStar_Syntax_Syntax.uvar* FStar_Syntax_Syntax.typ) FStar_Util.set =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_univ uu____8229)::tl1 -> aux out tl1
      | (Binding_lid (uu____8232,(uu____8233,t)))::tl1 ->
          let uu____8242 =
            let uu____8246 = FStar_Syntax_Free.uvars t in ext out uu____8246 in
          aux uu____8242 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____8250;
            FStar_Syntax_Syntax.index = uu____8251;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____8257 =
            let uu____8261 = FStar_Syntax_Free.uvars t in ext out uu____8261 in
          aux uu____8257 tl1
      | (Binding_sig uu____8265)::uu____8266 -> out
      | (Binding_sig_inst uu____8271)::uu____8272 -> out in
    aux no_uvs env.gamma
let univ_vars: env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____8309)::tl1 -> aux out tl1
      | (Binding_univ uu____8316)::tl1 -> aux out tl1
      | (Binding_lid (uu____8319,(uu____8320,t)))::tl1 ->
          let uu____8329 =
            let uu____8331 = FStar_Syntax_Free.univs t in ext out uu____8331 in
          aux uu____8329 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____8333;
            FStar_Syntax_Syntax.index = uu____8334;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____8340 =
            let uu____8342 = FStar_Syntax_Free.univs t in ext out uu____8342 in
          aux uu____8340 tl1
      | (Binding_sig uu____8344)::uu____8345 -> out in
    aux no_univs env.gamma
let univnames: env -> FStar_Syntax_Syntax.univ_name FStar_Util.set =
  fun env  ->
    let no_univ_names = FStar_Syntax_Syntax.no_universe_names in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____8382)::tl1 -> aux out tl1
      | (Binding_univ uname)::tl1 ->
          let uu____8392 = FStar_Util.set_add uname out in aux uu____8392 tl1
      | (Binding_lid (uu____8394,(uu____8395,t)))::tl1 ->
          let uu____8404 =
            let uu____8406 = FStar_Syntax_Free.univnames t in
            ext out uu____8406 in
          aux uu____8404 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____8408;
            FStar_Syntax_Syntax.index = uu____8409;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____8415 =
            let uu____8417 = FStar_Syntax_Free.univnames t in
            ext out uu____8417 in
          aux uu____8415 tl1
      | (Binding_sig uu____8419)::uu____8420 -> out in
    aux no_univ_names env.gamma
let bound_vars_of_bindings:
  binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___109_8436  ->
            match uu___109_8436 with
            | Binding_var x -> [x]
            | Binding_lid uu____8439 -> []
            | Binding_sig uu____8442 -> []
            | Binding_univ uu____8446 -> []
            | Binding_sig_inst uu____8447 -> []))
let binders_of_bindings:
  binding Prims.list -> FStar_Syntax_Syntax.binder Prims.list =
  fun bs  ->
    let uu____8457 =
      let uu____8459 = bound_vars_of_bindings bs in
      FStar_All.pipe_right uu____8459
        (FStar_List.map FStar_Syntax_Syntax.mk_binder) in
    FStar_All.pipe_right uu____8457 FStar_List.rev
let bound_vars: env -> FStar_Syntax_Syntax.bv Prims.list =
  fun env  -> bound_vars_of_bindings env.gamma
let all_binders: env -> FStar_Syntax_Syntax.binders =
  fun env  -> binders_of_bindings env.gamma
let print_gamma: env -> Prims.unit =
  fun env  ->
    let uu____8475 =
      let uu____8476 =
        FStar_All.pipe_right env.gamma
          (FStar_List.map
             (fun uu___110_8480  ->
                match uu___110_8480 with
                | Binding_var x ->
                    let uu____8482 = FStar_Syntax_Print.bv_to_string x in
                    Prims.strcat "Binding_var " uu____8482
                | Binding_univ u ->
                    Prims.strcat "Binding_univ " u.FStar_Ident.idText
                | Binding_lid (l,uu____8485) ->
                    let uu____8486 = FStar_Ident.string_of_lid l in
                    Prims.strcat "Binding_lid " uu____8486
                | Binding_sig (ls,uu____8488) ->
                    let uu____8491 =
                      let uu____8492 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____8492
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig " uu____8491
                | Binding_sig_inst (ls,uu____8498,uu____8499) ->
                    let uu____8502 =
                      let uu____8503 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____8503
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig_inst " uu____8502)) in
      FStar_All.pipe_right uu____8476 (FStar_String.concat "::\n") in
    FStar_All.pipe_right uu____8475 (FStar_Util.print1 "%s\n")
let eq_gamma: env -> env -> Prims.bool =
  fun env  ->
    fun env'  ->
      let uu____8515 = FStar_Util.physical_equality env.gamma env'.gamma in
      if uu____8515
      then true
      else
        (let g = all_binders env in
         let g' = all_binders env' in
         ((FStar_List.length g) = (FStar_List.length g')) &&
           (FStar_List.forall2
              (fun uu____8536  ->
                 fun uu____8537  ->
                   match (uu____8536, uu____8537) with
                   | ((b1,uu____8547),(b2,uu____8549)) ->
                       FStar_Syntax_Syntax.bv_eq b1 b2) g g'))
let fold_env env f a =
  FStar_List.fold_right (fun e  -> fun a1  -> f a1 e) env.gamma a
let lidents: env -> FStar_Ident.lident Prims.list =
  fun env  ->
    let keys =
      FStar_List.fold_left
        (fun keys  ->
           fun uu___111_8592  ->
             match uu___111_8592 with
             | Binding_sig (lids,uu____8596) -> FStar_List.append lids keys
             | uu____8599 -> keys) [] env.gamma in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____8601  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
let should_enc_path: env -> Prims.string Prims.list -> Prims.bool =
  fun env  ->
    fun path  ->
      let rec list_prefix xs ys =
        match (xs, ys) with
        | ([],uu____8626) -> true
        | (x::xs1,y::ys1) -> (x = y) && (list_prefix xs1 ys1)
        | (uu____8638,uu____8639) -> false in
      let rec should_enc_path' pns path1 =
        match pns with
        | [] -> true
        | (p,b)::pns1 ->
            let uu____8663 = list_prefix p path1 in
            if uu____8663 then b else should_enc_path' pns1 path1 in
      should_enc_path' (FStar_List.flatten env.proof_ns) path
let should_enc_lid: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____8673 = FStar_Ident.path_of_lid lid in
      should_enc_path env uu____8673
let cons_proof_ns: Prims.bool -> env -> name_prefix -> env =
  fun b  ->
    fun e  ->
      fun path  ->
        match e.proof_ns with
        | [] -> failwith "empty proof_ns stack!"
        | pns::rest ->
            let pns' = (path, b) :: pns in
            let uu___131_8693 = e in
            {
              solver = (uu___131_8693.solver);
              range = (uu___131_8693.range);
              curmodule = (uu___131_8693.curmodule);
              gamma = (uu___131_8693.gamma);
              gamma_cache = (uu___131_8693.gamma_cache);
              modules = (uu___131_8693.modules);
              expected_typ = (uu___131_8693.expected_typ);
              sigtab = (uu___131_8693.sigtab);
              is_pattern = (uu___131_8693.is_pattern);
              instantiate_imp = (uu___131_8693.instantiate_imp);
              effects = (uu___131_8693.effects);
              generalize = (uu___131_8693.generalize);
              letrecs = (uu___131_8693.letrecs);
              top_level = (uu___131_8693.top_level);
              check_uvars = (uu___131_8693.check_uvars);
              use_eq = (uu___131_8693.use_eq);
              is_iface = (uu___131_8693.is_iface);
              admit = (uu___131_8693.admit);
              lax = (uu___131_8693.lax);
              lax_universes = (uu___131_8693.lax_universes);
              type_of = (uu___131_8693.type_of);
              universe_of = (uu___131_8693.universe_of);
              use_bv_sorts = (uu___131_8693.use_bv_sorts);
              qname_and_index = (uu___131_8693.qname_and_index);
              proof_ns = (pns' :: rest);
              synth = (uu___131_8693.synth)
            }
let add_proof_ns: env -> name_prefix -> env =
  fun e  -> fun path  -> cons_proof_ns true e path
let rem_proof_ns: env -> name_prefix -> env =
  fun e  -> fun path  -> cons_proof_ns false e path
let push_proof_ns: env -> env =
  fun e  ->
    let uu___132_8712 = e in
    {
      solver = (uu___132_8712.solver);
      range = (uu___132_8712.range);
      curmodule = (uu___132_8712.curmodule);
      gamma = (uu___132_8712.gamma);
      gamma_cache = (uu___132_8712.gamma_cache);
      modules = (uu___132_8712.modules);
      expected_typ = (uu___132_8712.expected_typ);
      sigtab = (uu___132_8712.sigtab);
      is_pattern = (uu___132_8712.is_pattern);
      instantiate_imp = (uu___132_8712.instantiate_imp);
      effects = (uu___132_8712.effects);
      generalize = (uu___132_8712.generalize);
      letrecs = (uu___132_8712.letrecs);
      top_level = (uu___132_8712.top_level);
      check_uvars = (uu___132_8712.check_uvars);
      use_eq = (uu___132_8712.use_eq);
      is_iface = (uu___132_8712.is_iface);
      admit = (uu___132_8712.admit);
      lax = (uu___132_8712.lax);
      lax_universes = (uu___132_8712.lax_universes);
      type_of = (uu___132_8712.type_of);
      universe_of = (uu___132_8712.universe_of);
      use_bv_sorts = (uu___132_8712.use_bv_sorts);
      qname_and_index = (uu___132_8712.qname_and_index);
      proof_ns = ([] :: (e.proof_ns));
      synth = (uu___132_8712.synth)
    }
let pop_proof_ns: env -> env =
  fun e  ->
    match e.proof_ns with
    | [] -> failwith "empty proof_ns stack!"
    | uu____8721::rest ->
        let uu___133_8724 = e in
        {
          solver = (uu___133_8724.solver);
          range = (uu___133_8724.range);
          curmodule = (uu___133_8724.curmodule);
          gamma = (uu___133_8724.gamma);
          gamma_cache = (uu___133_8724.gamma_cache);
          modules = (uu___133_8724.modules);
          expected_typ = (uu___133_8724.expected_typ);
          sigtab = (uu___133_8724.sigtab);
          is_pattern = (uu___133_8724.is_pattern);
          instantiate_imp = (uu___133_8724.instantiate_imp);
          effects = (uu___133_8724.effects);
          generalize = (uu___133_8724.generalize);
          letrecs = (uu___133_8724.letrecs);
          top_level = (uu___133_8724.top_level);
          check_uvars = (uu___133_8724.check_uvars);
          use_eq = (uu___133_8724.use_eq);
          is_iface = (uu___133_8724.is_iface);
          admit = (uu___133_8724.admit);
          lax = (uu___133_8724.lax);
          lax_universes = (uu___133_8724.lax_universes);
          type_of = (uu___133_8724.type_of);
          universe_of = (uu___133_8724.universe_of);
          use_bv_sorts = (uu___133_8724.use_bv_sorts);
          qname_and_index = (uu___133_8724.qname_and_index);
          proof_ns = rest;
          synth = (uu___133_8724.synth)
        }
let get_proof_ns: env -> proof_namespace = fun e  -> e.proof_ns
let set_proof_ns: proof_namespace -> env -> env =
  fun ns  ->
    fun e  ->
      let uu___134_8734 = e in
      {
        solver = (uu___134_8734.solver);
        range = (uu___134_8734.range);
        curmodule = (uu___134_8734.curmodule);
        gamma = (uu___134_8734.gamma);
        gamma_cache = (uu___134_8734.gamma_cache);
        modules = (uu___134_8734.modules);
        expected_typ = (uu___134_8734.expected_typ);
        sigtab = (uu___134_8734.sigtab);
        is_pattern = (uu___134_8734.is_pattern);
        instantiate_imp = (uu___134_8734.instantiate_imp);
        effects = (uu___134_8734.effects);
        generalize = (uu___134_8734.generalize);
        letrecs = (uu___134_8734.letrecs);
        top_level = (uu___134_8734.top_level);
        check_uvars = (uu___134_8734.check_uvars);
        use_eq = (uu___134_8734.use_eq);
        is_iface = (uu___134_8734.is_iface);
        admit = (uu___134_8734.admit);
        lax = (uu___134_8734.lax);
        lax_universes = (uu___134_8734.lax_universes);
        type_of = (uu___134_8734.type_of);
        universe_of = (uu___134_8734.universe_of);
        use_bv_sorts = (uu___134_8734.use_bv_sorts);
        qname_and_index = (uu___134_8734.qname_and_index);
        proof_ns = ns;
        synth = (uu___134_8734.synth)
      }
let string_of_proof_ns: env -> Prims.string =
  fun env  ->
    let string_of_proof_ns' pns =
      let uu____8752 =
        FStar_List.map
          (fun fpns  ->
             let uu____8763 =
               let uu____8764 =
                 let uu____8765 =
                   FStar_List.map
                     (fun uu____8770  ->
                        match uu____8770 with
                        | (p,b) ->
                            Prims.strcat (if b then "+" else "-")
                              (FStar_String.concat "." p)) fpns in
                 FStar_String.concat "," uu____8765 in
               Prims.strcat uu____8764 "]" in
             Prims.strcat "[" uu____8763) pns in
      FStar_String.concat ";" uu____8752 in
    string_of_proof_ns' env.proof_ns
let dummy_solver: solver_t =
  {
    init = (fun uu____8779  -> ());
    push = (fun uu____8780  -> ());
    pop = (fun uu____8781  -> ());
    mark = (fun uu____8782  -> ());
    reset_mark = (fun uu____8783  -> ());
    commit_mark = (fun uu____8784  -> ());
    encode_modul = (fun uu____8785  -> fun uu____8786  -> ());
    encode_sig = (fun uu____8787  -> fun uu____8788  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____8791 =
             let uu____8795 = FStar_Options.peek () in (e, g, uu____8795) in
           [uu____8791]);
    solve = (fun uu____8802  -> fun uu____8803  -> fun uu____8804  -> ());
    is_trivial = (fun uu____8808  -> fun uu____8809  -> false);
    finish = (fun uu____8810  -> ());
    refresh = (fun uu____8811  -> ())
  }