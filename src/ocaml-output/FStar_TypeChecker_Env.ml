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
  preprocess: env -> goal -> (env* goal) Prims.list;
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
  solver_t -> env -> goal -> (env* goal) Prims.list =
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
      | (NoDelta ,uu____3223) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____3224,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) ->
          true
      | (Unfold uu____3225,FStar_Syntax_Syntax.Visible_default ) -> true
      | (Inlining ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____3226 -> false
let default_table_size: Prims.int = Prims.parse_int "200"
let new_sigtab uu____3236 = FStar_Util.smap_create default_table_size
let new_gamma_cache uu____3244 =
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
          let uu____3283 = new_gamma_cache () in
          let uu____3285 = new_sigtab () in
          let uu____3287 =
            let uu____3288 = FStar_Options.using_facts_from () in
            match uu____3288 with
            | Some ns ->
                let uu____3294 =
                  let uu____3299 =
                    FStar_List.map
                      (fun s  -> ((FStar_Ident.path_of_text s), true)) ns in
                  FStar_List.append uu____3299 [([], false)] in
                [uu____3294]
            | None  -> [[]] in
          {
            solver;
            range = FStar_Range.dummyRange;
            curmodule = module_lid;
            gamma = [];
            gamma_cache = uu____3283;
            modules = [];
            expected_typ = None;
            sigtab = uu____3285;
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
            proof_ns = uu____3287;
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
  fun uu____3380  ->
    let uu____3381 = FStar_ST.read query_indices in
    match uu____3381 with
    | [] -> failwith "Empty query indices!"
    | uu____3395 ->
        let uu____3400 =
          let uu____3405 =
            let uu____3409 = FStar_ST.read query_indices in
            FStar_List.hd uu____3409 in
          let uu____3423 = FStar_ST.read query_indices in uu____3405 ::
            uu____3423 in
        FStar_ST.write query_indices uu____3400
let pop_query_indices: Prims.unit -> Prims.unit =
  fun uu____3445  ->
    let uu____3446 = FStar_ST.read query_indices in
    match uu____3446 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.write query_indices tl1
let add_query_index: (FStar_Ident.lident* Prims.int) -> Prims.unit =
  fun uu____3482  ->
    match uu____3482 with
    | (l,n1) ->
        let uu____3487 = FStar_ST.read query_indices in
        (match uu____3487 with
         | hd1::tl1 -> FStar_ST.write query_indices (((l, n1) :: hd1) :: tl1)
         | uu____3521 -> failwith "Empty query indices")
let peek_query_indices:
  Prims.unit -> (FStar_Ident.lident* Prims.int) Prims.list =
  fun uu____3531  ->
    let uu____3532 = FStar_ST.read query_indices in FStar_List.hd uu____3532
let commit_query_index_mark: Prims.unit -> Prims.unit =
  fun uu____3548  ->
    let uu____3549 = FStar_ST.read query_indices in
    match uu____3549 with
    | hd1::uu____3561::tl1 -> FStar_ST.write query_indices (hd1 :: tl1)
    | uu____3588 -> failwith "Unmarked query index stack"
let stack: env Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let push_stack: env -> env =
  fun env  ->
    (let uu____3602 =
       let uu____3604 = FStar_ST.read stack in env :: uu____3604 in
     FStar_ST.write stack uu____3602);
    (let uu___112_3612 = env in
     let uu____3613 = FStar_Util.smap_copy (gamma_cache env) in
     let uu____3615 = FStar_Util.smap_copy (sigtab env) in
     {
       solver = (uu___112_3612.solver);
       range = (uu___112_3612.range);
       curmodule = (uu___112_3612.curmodule);
       gamma = (uu___112_3612.gamma);
       gamma_cache = uu____3613;
       modules = (uu___112_3612.modules);
       expected_typ = (uu___112_3612.expected_typ);
       sigtab = uu____3615;
       is_pattern = (uu___112_3612.is_pattern);
       instantiate_imp = (uu___112_3612.instantiate_imp);
       effects = (uu___112_3612.effects);
       generalize = (uu___112_3612.generalize);
       letrecs = (uu___112_3612.letrecs);
       top_level = (uu___112_3612.top_level);
       check_uvars = (uu___112_3612.check_uvars);
       use_eq = (uu___112_3612.use_eq);
       is_iface = (uu___112_3612.is_iface);
       admit = (uu___112_3612.admit);
       lax = (uu___112_3612.lax);
       lax_universes = (uu___112_3612.lax_universes);
       type_of = (uu___112_3612.type_of);
       universe_of = (uu___112_3612.universe_of);
       use_bv_sorts = (uu___112_3612.use_bv_sorts);
       qname_and_index = (uu___112_3612.qname_and_index);
       proof_ns = (uu___112_3612.proof_ns);
       synth = (uu___112_3612.synth)
     })
let pop_stack: Prims.unit -> env =
  fun uu____3619  ->
    let uu____3620 = FStar_ST.read stack in
    match uu____3620 with
    | env::tl1 -> (FStar_ST.write stack tl1; env)
    | uu____3632 -> failwith "Impossible: Too many pops"
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
    (let uu____3664 = pop_stack () in ());
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
        let uu____3683 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____3695  ->
                  match uu____3695 with
                  | (m,uu____3699) -> FStar_Ident.lid_equals l m)) in
        (match uu____3683 with
         | None  ->
             let next = n1 + (Prims.parse_int "1") in
             (add_query_index (l, next);
              (let uu___113_3704 = env in
               {
                 solver = (uu___113_3704.solver);
                 range = (uu___113_3704.range);
                 curmodule = (uu___113_3704.curmodule);
                 gamma = (uu___113_3704.gamma);
                 gamma_cache = (uu___113_3704.gamma_cache);
                 modules = (uu___113_3704.modules);
                 expected_typ = (uu___113_3704.expected_typ);
                 sigtab = (uu___113_3704.sigtab);
                 is_pattern = (uu___113_3704.is_pattern);
                 instantiate_imp = (uu___113_3704.instantiate_imp);
                 effects = (uu___113_3704.effects);
                 generalize = (uu___113_3704.generalize);
                 letrecs = (uu___113_3704.letrecs);
                 top_level = (uu___113_3704.top_level);
                 check_uvars = (uu___113_3704.check_uvars);
                 use_eq = (uu___113_3704.use_eq);
                 is_iface = (uu___113_3704.is_iface);
                 admit = (uu___113_3704.admit);
                 lax = (uu___113_3704.lax);
                 lax_universes = (uu___113_3704.lax_universes);
                 type_of = (uu___113_3704.type_of);
                 universe_of = (uu___113_3704.universe_of);
                 use_bv_sorts = (uu___113_3704.use_bv_sorts);
                 qname_and_index = (Some (l, next));
                 proof_ns = (uu___113_3704.proof_ns);
                 synth = (uu___113_3704.synth)
               }))
         | Some (uu____3707,m) ->
             let next = m + (Prims.parse_int "1") in
             (add_query_index (l, next);
              (let uu___114_3713 = env in
               {
                 solver = (uu___114_3713.solver);
                 range = (uu___114_3713.range);
                 curmodule = (uu___114_3713.curmodule);
                 gamma = (uu___114_3713.gamma);
                 gamma_cache = (uu___114_3713.gamma_cache);
                 modules = (uu___114_3713.modules);
                 expected_typ = (uu___114_3713.expected_typ);
                 sigtab = (uu___114_3713.sigtab);
                 is_pattern = (uu___114_3713.is_pattern);
                 instantiate_imp = (uu___114_3713.instantiate_imp);
                 effects = (uu___114_3713.effects);
                 generalize = (uu___114_3713.generalize);
                 letrecs = (uu___114_3713.letrecs);
                 top_level = (uu___114_3713.top_level);
                 check_uvars = (uu___114_3713.check_uvars);
                 use_eq = (uu___114_3713.use_eq);
                 is_iface = (uu___114_3713.is_iface);
                 admit = (uu___114_3713.admit);
                 lax = (uu___114_3713.lax);
                 lax_universes = (uu___114_3713.lax_universes);
                 type_of = (uu___114_3713.type_of);
                 universe_of = (uu___114_3713.universe_of);
                 use_bv_sorts = (uu___114_3713.use_bv_sorts);
                 qname_and_index = (Some (l, next));
                 proof_ns = (uu___114_3713.proof_ns);
                 synth = (uu___114_3713.synth)
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
        (let uu___115_3729 = e in
         {
           solver = (uu___115_3729.solver);
           range = r;
           curmodule = (uu___115_3729.curmodule);
           gamma = (uu___115_3729.gamma);
           gamma_cache = (uu___115_3729.gamma_cache);
           modules = (uu___115_3729.modules);
           expected_typ = (uu___115_3729.expected_typ);
           sigtab = (uu___115_3729.sigtab);
           is_pattern = (uu___115_3729.is_pattern);
           instantiate_imp = (uu___115_3729.instantiate_imp);
           effects = (uu___115_3729.effects);
           generalize = (uu___115_3729.generalize);
           letrecs = (uu___115_3729.letrecs);
           top_level = (uu___115_3729.top_level);
           check_uvars = (uu___115_3729.check_uvars);
           use_eq = (uu___115_3729.use_eq);
           is_iface = (uu___115_3729.is_iface);
           admit = (uu___115_3729.admit);
           lax = (uu___115_3729.lax);
           lax_universes = (uu___115_3729.lax_universes);
           type_of = (uu___115_3729.type_of);
           universe_of = (uu___115_3729.universe_of);
           use_bv_sorts = (uu___115_3729.use_bv_sorts);
           qname_and_index = (uu___115_3729.qname_and_index);
           proof_ns = (uu___115_3729.proof_ns);
           synth = (uu___115_3729.synth)
         })
let get_range: env -> FStar_Range.range = fun e  -> e.range
let modules: env -> FStar_Syntax_Syntax.modul Prims.list =
  fun env  -> env.modules
let current_module: env -> FStar_Ident.lident = fun env  -> env.curmodule
let set_current_module: env -> FStar_Ident.lident -> env =
  fun env  ->
    fun lid  ->
      let uu___116_3746 = env in
      {
        solver = (uu___116_3746.solver);
        range = (uu___116_3746.range);
        curmodule = lid;
        gamma = (uu___116_3746.gamma);
        gamma_cache = (uu___116_3746.gamma_cache);
        modules = (uu___116_3746.modules);
        expected_typ = (uu___116_3746.expected_typ);
        sigtab = (uu___116_3746.sigtab);
        is_pattern = (uu___116_3746.is_pattern);
        instantiate_imp = (uu___116_3746.instantiate_imp);
        effects = (uu___116_3746.effects);
        generalize = (uu___116_3746.generalize);
        letrecs = (uu___116_3746.letrecs);
        top_level = (uu___116_3746.top_level);
        check_uvars = (uu___116_3746.check_uvars);
        use_eq = (uu___116_3746.use_eq);
        is_iface = (uu___116_3746.is_iface);
        admit = (uu___116_3746.admit);
        lax = (uu___116_3746.lax);
        lax_universes = (uu___116_3746.lax_universes);
        type_of = (uu___116_3746.type_of);
        universe_of = (uu___116_3746.universe_of);
        use_bv_sorts = (uu___116_3746.use_bv_sorts);
        qname_and_index = (uu___116_3746.qname_and_index);
        proof_ns = (uu___116_3746.proof_ns);
        synth = (uu___116_3746.synth)
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
    let uu____3768 = FStar_Syntax_Print.bv_to_string v1 in
    FStar_Util.format1 "Variable \"%s\" not found" uu____3768
let new_u_univ: Prims.unit -> FStar_Syntax_Syntax.universe =
  fun uu____3771  ->
    let uu____3772 = FStar_Syntax_Unionfind.univ_fresh () in
    FStar_Syntax_Syntax.U_unif uu____3772
let inst_tscheme_with:
  FStar_Syntax_Syntax.tscheme ->
    FStar_Syntax_Syntax.universes ->
      (FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.term)
  =
  fun ts  ->
    fun us  ->
      match (ts, us) with
      | (([],t),[]) -> ([], t)
      | ((formals,t),uu____3794) ->
          let n1 = (FStar_List.length formals) - (Prims.parse_int "1") in
          let vs =
            FStar_All.pipe_right us
              (FStar_List.mapi
                 (fun i  -> fun u  -> FStar_Syntax_Syntax.UN ((n1 - i), u))) in
          let uu____3813 = FStar_Syntax_Subst.subst vs t in (us, uu____3813)
let inst_tscheme:
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.term)
  =
  fun uu___100_3818  ->
    match uu___100_3818 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____3832  -> new_u_univ ())) in
        inst_tscheme_with (us, t) us'
let inst_tscheme_with_range:
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.term)
  =
  fun r  ->
    fun t  ->
      let uu____3842 = inst_tscheme t in
      match uu____3842 with
      | (us,t1) ->
          let uu____3849 = FStar_Syntax_Subst.set_use_range r t1 in
          (us, uu____3849)
let inst_effect_fun_with:
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____3861  ->
          match uu____3861 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____3879 =
                         let uu____3880 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1) in
                         let uu____3885 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts) in
                         let uu____3890 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname in
                         let uu____3891 = FStar_Syntax_Print.term_to_string t in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____3880 uu____3885 uu____3890 uu____3891 in
                       failwith uu____3879)
                    else ();
                    (let uu____3893 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts in
                     snd uu____3893))
               | uu____3897 ->
                   let uu____3898 =
                     let uu____3899 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____3899 in
                   failwith uu____3898)
type tri =
  | Yes
  | No
  | Maybe
let uu___is_Yes: tri -> Prims.bool =
  fun projectee  -> match projectee with | Yes  -> true | uu____3903 -> false
let uu___is_No: tri -> Prims.bool =
  fun projectee  -> match projectee with | No  -> true | uu____3907 -> false
let uu___is_Maybe: tri -> Prims.bool =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____3911 -> false
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
             | ([],uu____3937) -> Maybe
             | (uu____3941,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____3953 -> No in
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
          let uu____4013 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str in
          match uu____4013 with
          | None  ->
              FStar_Util.find_map env.gamma
                (fun uu___101_4034  ->
                   match uu___101_4034 with
                   | Binding_lid (l,t) ->
                       if FStar_Ident.lid_equals lid l
                       then
                         let uu____4057 =
                           let uu____4067 =
                             let uu____4075 = inst_tscheme t in
                             FStar_Util.Inl uu____4075 in
                           (uu____4067, (FStar_Ident.range_of_lid l)) in
                         Some uu____4057
                       else None
                   | Binding_sig
                       (uu____4109,{
                                     FStar_Syntax_Syntax.sigel =
                                       FStar_Syntax_Syntax.Sig_bundle
                                       (ses,uu____4111);
                                     FStar_Syntax_Syntax.sigrng = uu____4112;
                                     FStar_Syntax_Syntax.sigquals =
                                       uu____4113;
                                     FStar_Syntax_Syntax.sigmeta = uu____4114;_})
                       ->
                       FStar_Util.find_map ses
                         (fun se  ->
                            let uu____4123 =
                              FStar_All.pipe_right
                                (FStar_Syntax_Util.lids_of_sigelt se)
                                (FStar_Util.for_some
                                   (FStar_Ident.lid_equals lid)) in
                            if uu____4123
                            then
                              cache
                                ((FStar_Util.Inr (se, None)),
                                  (FStar_Syntax_Util.range_of_sigelt se))
                            else None)
                   | Binding_sig (lids,s) ->
                       let maybe_cache t =
                         match s.FStar_Syntax_Syntax.sigel with
                         | FStar_Syntax_Syntax.Sig_declare_typ uu____4150 ->
                             Some t
                         | uu____4154 -> cache t in
                       let uu____4155 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids in
                       (match uu____4155 with
                        | None  -> None
                        | Some l ->
                            maybe_cache
                              ((FStar_Util.Inr (s, None)),
                                (FStar_Ident.range_of_lid l)))
                   | Binding_sig_inst (lids,s,us) ->
                       let uu____4195 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids in
                       (match uu____4195 with
                        | None  -> None
                        | Some l ->
                            Some
                              ((FStar_Util.Inr (s, (Some us))),
                                (FStar_Ident.range_of_lid l)))
                   | uu____4239 -> None)
          | se -> se
        else None in
      if FStar_Util.is_some found
      then found
      else
        (let uu____4281 =
           (cur_mod <> Yes) || (has_interface env env.curmodule) in
         if uu____4281
         then
           let uu____4292 = find_in_sigtab env lid in
           match uu____4292 with
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
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____4358) ->
          add_sigelts env ses
      | uu____4363 ->
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
            | uu____4372 -> ()))
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
        (fun uu___102_4390  ->
           match uu___102_4390 with
           | Binding_var id when FStar_Syntax_Syntax.bv_eq id bv ->
               Some
                 ((id.FStar_Syntax_Syntax.sort),
                   ((id.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____4403 -> None)
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
          ((uu____4424,lb::[]),uu____4426,uu____4427) ->
          let uu____4436 =
            let uu____4441 =
              inst_tscheme
                ((lb.FStar_Syntax_Syntax.lbunivs),
                  (lb.FStar_Syntax_Syntax.lbtyp)) in
            let uu____4447 =
              FStar_Syntax_Syntax.range_of_lbname
                lb.FStar_Syntax_Syntax.lbname in
            (uu____4441, uu____4447) in
          Some uu____4436
      | FStar_Syntax_Syntax.Sig_let ((uu____4454,lbs),uu____4456,uu____4457)
          ->
          FStar_Util.find_map lbs
            (fun lb  ->
               match lb.FStar_Syntax_Syntax.lbname with
               | FStar_Util.Inl uu____4477 -> failwith "impossible"
               | FStar_Util.Inr fv ->
                   let uu____4484 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                   if uu____4484
                   then
                     let uu____4490 =
                       let uu____4495 =
                         inst_tscheme
                           ((lb.FStar_Syntax_Syntax.lbunivs),
                             (lb.FStar_Syntax_Syntax.lbtyp)) in
                       let uu____4501 = FStar_Syntax_Syntax.range_of_fv fv in
                       (uu____4495, uu____4501) in
                     Some uu____4490
                   else None)
      | uu____4513 -> None
let effect_signature:
  FStar_Syntax_Syntax.sigelt ->
    ((FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.term)*
      FStar_Range.range) option
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne ->
        let uu____4532 =
          let uu____4537 =
            let uu____4540 =
              let uu____4541 =
                let uu____4544 =
                  FStar_Syntax_Syntax.mk_Total
                    ne.FStar_Syntax_Syntax.signature in
                FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                  uu____4544 in
              ((ne.FStar_Syntax_Syntax.univs), uu____4541) in
            inst_tscheme uu____4540 in
          (uu____4537, (se.FStar_Syntax_Syntax.sigrng)) in
        Some uu____4532
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,us,binders,uu____4558,uu____4559) ->
        let uu____4562 =
          let uu____4567 =
            let uu____4570 =
              let uu____4571 =
                let uu____4574 =
                  FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff in
                FStar_Syntax_Util.arrow binders uu____4574 in
              (us, uu____4571) in
            inst_tscheme uu____4570 in
          (uu____4567, (se.FStar_Syntax_Syntax.sigrng)) in
        Some uu____4562
    | uu____4585 -> None
let try_lookup_lid_aux:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes*
        (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax)* FStar_Range.range) option
  =
  fun env  ->
    fun lid  ->
      let mapper uu____4620 =
        match uu____4620 with
        | (lr,rng) ->
            (match lr with
             | FStar_Util.Inl t -> Some (t, rng)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_datacon
                      (uu____4670,uvs,t,uu____4673,uu____4674,uu____4675);
                    FStar_Syntax_Syntax.sigrng = uu____4676;
                    FStar_Syntax_Syntax.sigquals = uu____4677;
                    FStar_Syntax_Syntax.sigmeta = uu____4678;_},None
                  )
                 ->
                 let uu____4688 =
                   let uu____4693 = inst_tscheme (uvs, t) in
                   (uu____4693, rng) in
                 Some uu____4688
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                    FStar_Syntax_Syntax.sigrng = uu____4705;
                    FStar_Syntax_Syntax.sigquals = qs;
                    FStar_Syntax_Syntax.sigmeta = uu____4707;_},None
                  )
                 ->
                 let uu____4715 =
                   let uu____4716 = in_cur_mod env l in uu____4716 = Yes in
                 if uu____4715
                 then
                   let uu____4722 =
                     (FStar_All.pipe_right qs
                        (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                       || env.is_iface in
                   (if uu____4722
                    then
                      let uu____4729 =
                        let uu____4734 = inst_tscheme (uvs, t) in
                        (uu____4734, rng) in
                      Some uu____4729
                    else None)
                 else
                   (let uu____4749 =
                      let uu____4754 = inst_tscheme (uvs, t) in
                      (uu____4754, rng) in
                    Some uu____4749)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____4767,uu____4768);
                    FStar_Syntax_Syntax.sigrng = uu____4769;
                    FStar_Syntax_Syntax.sigquals = uu____4770;
                    FStar_Syntax_Syntax.sigmeta = uu____4771;_},None
                  )
                 ->
                 (match tps with
                  | [] ->
                      let uu____4790 =
                        let uu____4795 = inst_tscheme (uvs, k) in
                        (uu____4795, rng) in
                      Some uu____4790
                  | uu____4804 ->
                      let uu____4805 =
                        let uu____4810 =
                          let uu____4813 =
                            let uu____4814 =
                              let uu____4817 = FStar_Syntax_Syntax.mk_Total k in
                              FStar_Syntax_Util.flat_arrow tps uu____4817 in
                            (uvs, uu____4814) in
                          inst_tscheme uu____4813 in
                        (uu____4810, rng) in
                      Some uu____4805)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____4832,uu____4833);
                    FStar_Syntax_Syntax.sigrng = uu____4834;
                    FStar_Syntax_Syntax.sigquals = uu____4835;
                    FStar_Syntax_Syntax.sigmeta = uu____4836;_},Some
                  us)
                 ->
                 (match tps with
                  | [] ->
                      let uu____4856 =
                        let uu____4861 = inst_tscheme_with (uvs, k) us in
                        (uu____4861, rng) in
                      Some uu____4856
                  | uu____4870 ->
                      let uu____4871 =
                        let uu____4876 =
                          let uu____4879 =
                            let uu____4880 =
                              let uu____4883 = FStar_Syntax_Syntax.mk_Total k in
                              FStar_Syntax_Util.flat_arrow tps uu____4883 in
                            (uvs, uu____4880) in
                          inst_tscheme_with uu____4879 us in
                        (uu____4876, rng) in
                      Some uu____4871)
             | FStar_Util.Inr se ->
                 let uu____4903 =
                   match se with
                   | ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let uu____4914;
                        FStar_Syntax_Syntax.sigrng = uu____4915;
                        FStar_Syntax_Syntax.sigquals = uu____4916;
                        FStar_Syntax_Syntax.sigmeta = uu____4917;_},None
                      ) -> lookup_type_of_let (fst se) lid
                   | uu____4926 -> effect_signature (fst se) in
                 FStar_All.pipe_right uu____4903
                   (FStar_Util.map_option
                      (fun uu____4949  ->
                         match uu____4949 with | (us_t,rng1) -> (us_t, rng1)))) in
      let uu____4966 =
        let uu____4972 = lookup_qname env lid in
        FStar_Util.bind_opt uu____4972 mapper in
      match uu____4966 with
      | Some ((us,t),r) ->
          Some
            ((us,
               (let uu___117_5024 = t in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___117_5024.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___117_5024.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid);
                  FStar_Syntax_Syntax.vars =
                    (uu___117_5024.FStar_Syntax_Syntax.vars)
                })), r)
      | None  -> None
let lid_exists: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____5045 = lookup_qname env l in
      match uu____5045 with | None  -> false | Some uu____5065 -> true
let lookup_bv:
  env ->
    FStar_Syntax_Syntax.bv -> (FStar_Syntax_Syntax.typ* FStar_Range.range)
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv in
      let uu____5093 = try_lookup_bv env bv in
      match uu____5093 with
      | None  ->
          let uu____5101 =
            let uu____5102 =
              let uu____5105 = variable_not_found bv in (uu____5105, bvr) in
            FStar_Errors.Error uu____5102 in
          raise uu____5101
      | Some (t,r) ->
          let uu____5112 = FStar_Syntax_Subst.set_use_range bvr t in
          let uu____5113 = FStar_Range.set_use_range r bvr in
          (uu____5112, uu____5113)
let try_lookup_lid:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.typ)*
        FStar_Range.range) option
  =
  fun env  ->
    fun l  ->
      let uu____5125 = try_lookup_lid_aux env l in
      match uu____5125 with
      | None  -> None
      | Some ((us,t),r) ->
          let use_range = FStar_Ident.range_of_lid l in
          let r1 = FStar_Range.set_use_range r use_range in
          let uu____5167 =
            let uu____5172 =
              let uu____5175 = FStar_Syntax_Subst.set_use_range use_range t in
              (us, uu____5175) in
            (uu____5172, r1) in
          Some uu____5167
let lookup_lid:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.typ)*
        FStar_Range.range)
  =
  fun env  ->
    fun l  ->
      let uu____5192 = try_lookup_lid env l in
      match uu____5192 with
      | None  ->
          let uu____5206 =
            let uu____5207 =
              let uu____5210 = name_not_found l in
              (uu____5210, (FStar_Ident.range_of_lid l)) in
            FStar_Errors.Error uu____5207 in
          raise uu____5206
      | Some v1 -> v1
let lookup_univ: env -> FStar_Syntax_Syntax.univ_name -> Prims.bool =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___103_5231  ->
              match uu___103_5231 with
              | Binding_univ y -> x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____5233 -> false) env.gamma) FStar_Option.isSome
let try_lookup_val_decl:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme* FStar_Syntax_Syntax.qualifier Prims.list)
        option
  =
  fun env  ->
    fun lid  ->
      let uu____5244 = lookup_qname env lid in
      match uu____5244 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____5259,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____5262;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____5264;_},None
            ),uu____5265)
          ->
          let uu____5289 =
            let uu____5295 =
              let uu____5298 =
                FStar_Syntax_Subst.set_use_range
                  (FStar_Ident.range_of_lid lid) t in
              (uvs, uu____5298) in
            (uu____5295, q) in
          Some uu____5289
      | uu____5307 -> None
let lookup_val_decl:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun lid  ->
      let uu____5329 = lookup_qname env lid in
      match uu____5329 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____5342,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____5345;
              FStar_Syntax_Syntax.sigquals = uu____5346;
              FStar_Syntax_Syntax.sigmeta = uu____5347;_},None
            ),uu____5348)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____5372 ->
          let uu____5383 =
            let uu____5384 =
              let uu____5387 = name_not_found lid in
              (uu____5387, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____5384 in
          raise uu____5383
let lookup_datacon:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun lid  ->
      let uu____5398 = lookup_qname env lid in
      match uu____5398 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____5411,uvs,t,uu____5414,uu____5415,uu____5416);
              FStar_Syntax_Syntax.sigrng = uu____5417;
              FStar_Syntax_Syntax.sigquals = uu____5418;
              FStar_Syntax_Syntax.sigmeta = uu____5419;_},None
            ),uu____5420)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____5446 ->
          let uu____5457 =
            let uu____5458 =
              let uu____5461 = name_not_found lid in
              (uu____5461, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____5458 in
          raise uu____5457
let datacons_of_typ:
  env -> FStar_Ident.lident -> (Prims.bool* FStar_Ident.lident Prims.list) =
  fun env  ->
    fun lid  ->
      let uu____5473 = lookup_qname env lid in
      match uu____5473 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____5487,uu____5488,uu____5489,uu____5490,uu____5491,dcs);
              FStar_Syntax_Syntax.sigrng = uu____5493;
              FStar_Syntax_Syntax.sigquals = uu____5494;
              FStar_Syntax_Syntax.sigmeta = uu____5495;_},uu____5496),uu____5497)
          -> (true, dcs)
      | uu____5527 -> (false, [])
let typ_of_datacon: env -> FStar_Ident.lident -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      let uu____5545 = lookup_qname env lid in
      match uu____5545 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____5556,uu____5557,uu____5558,l,uu____5560,uu____5561);
              FStar_Syntax_Syntax.sigrng = uu____5562;
              FStar_Syntax_Syntax.sigquals = uu____5563;
              FStar_Syntax_Syntax.sigmeta = uu____5564;_},uu____5565),uu____5566)
          -> l
      | uu____5593 ->
          let uu____5604 =
            let uu____5605 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format1 "Not a datacon: %s" uu____5605 in
          failwith uu____5604
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
        let uu____5629 = lookup_qname env lid in
        match uu____5629 with
        | Some (FStar_Util.Inr (se,None ),uu____5644) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_let
                 ((uu____5670,lbs),uu____5672,uu____5673) when
                 visible se.FStar_Syntax_Syntax.sigquals ->
                 FStar_Util.find_map lbs
                   (fun lb  ->
                      let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                      let uu____5690 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                      if uu____5690
                      then
                        Some
                          ((lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbdef))
                      else None)
             | uu____5711 -> None)
        | uu____5714 -> None
let try_lookup_effect_lid:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.typ option =
  fun env  ->
    fun ftv  ->
      let uu____5735 = lookup_qname env ftv in
      match uu____5735 with
      | Some (FStar_Util.Inr (se,None ),uu____5748) ->
          let uu____5771 = effect_signature se in
          (match uu____5771 with
           | None  -> None
           | Some ((uu____5782,t),r) ->
               let uu____5791 =
                 FStar_Syntax_Subst.set_use_range
                   (FStar_Ident.range_of_lid ftv) t in
               Some uu____5791)
      | uu____5792 -> None
let lookup_effect_lid: env -> FStar_Ident.lident -> FStar_Syntax_Syntax.typ =
  fun env  ->
    fun ftv  ->
      let uu____5809 = try_lookup_effect_lid env ftv in
      match uu____5809 with
      | None  ->
          let uu____5811 =
            let uu____5812 =
              let uu____5815 = name_not_found ftv in
              (uu____5815, (FStar_Ident.range_of_lid ftv)) in
            FStar_Errors.Error uu____5812 in
          raise uu____5811
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
        let uu____5829 = lookup_qname env lid0 in
        match uu____5829 with
        | Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____5847);
                FStar_Syntax_Syntax.sigrng = uu____5848;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____5850;_},None
              ),uu____5851)
            ->
            let lid1 =
              let uu____5878 =
                FStar_Range.set_use_range (FStar_Ident.range_of_lid lid)
                  (FStar_Ident.range_of_lid lid0) in
              FStar_Ident.set_lid_range lid uu____5878 in
            let uu____5879 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___104_5881  ->
                      match uu___104_5881 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____5882 -> false)) in
            if uu____5879
            then None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____5899 =
                      let uu____5900 = FStar_Syntax_Print.lid_to_string lid1 in
                      let uu____5901 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int in
                      FStar_Util.format2
                        "Unexpected instantiation of effect %s with %s universes"
                        uu____5900 uu____5901 in
                    failwith uu____5899) in
               match (binders, univs1) with
               | ([],uu____5909) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____5918,uu____5919::uu____5920::uu____5921) ->
                   let uu____5924 =
                     let uu____5925 = FStar_Syntax_Print.lid_to_string lid1 in
                     let uu____5926 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1) in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____5925 uu____5926 in
                   failwith uu____5924
               | uu____5934 ->
                   let uu____5937 =
                     let uu____5940 =
                       let uu____5941 = FStar_Syntax_Util.arrow binders c in
                       (univs1, uu____5941) in
                     inst_tscheme_with uu____5940 insts in
                   (match uu____5937 with
                    | (uu____5949,t) ->
                        let t1 =
                          FStar_Syntax_Subst.set_use_range
                            (FStar_Ident.range_of_lid lid1) t in
                        let uu____5952 =
                          let uu____5953 = FStar_Syntax_Subst.compress t1 in
                          uu____5953.FStar_Syntax_Syntax.n in
                        (match uu____5952 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             Some (binders1, c1)
                         | uu____5983 -> failwith "Impossible")))
        | uu____5987 -> None
let norm_eff_name: env -> FStar_Ident.lident -> FStar_Ident.lident =
  let cache = FStar_Util.smap_create (Prims.parse_int "20") in
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____6013 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1 in
        match uu____6013 with
        | None  -> None
        | Some (uu____6020,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c in
            let uu____6025 = find1 l2 in
            (match uu____6025 with | None  -> Some l2 | Some l' -> Some l') in
      let res =
        let uu____6030 = FStar_Util.smap_try_find cache l.FStar_Ident.str in
        match uu____6030 with
        | Some l1 -> l1
        | None  ->
            let uu____6033 = find1 l in
            (match uu____6033 with
             | None  -> l
             | Some m -> (FStar_Util.smap_add cache l.FStar_Ident.str m; m)) in
      FStar_Ident.set_lid_range res (FStar_Ident.range_of_lid l)
let lookup_effect_quals:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l in
      let uu____6045 = lookup_qname env l1 in
      match uu____6045 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____6057;
              FStar_Syntax_Syntax.sigrng = uu____6058;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____6060;_},uu____6061),uu____6062)
          -> q
      | uu____6087 -> []
let lookup_projector:
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail uu____6110 =
          let uu____6111 =
            let uu____6112 = FStar_Util.string_of_int i in
            let uu____6113 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____6112 uu____6113 in
          failwith uu____6111 in
        let uu____6114 = lookup_datacon env lid in
        match uu____6114 with
        | (uu____6117,t) ->
            let uu____6119 =
              let uu____6120 = FStar_Syntax_Subst.compress t in
              uu____6120.FStar_Syntax_Syntax.n in
            (match uu____6119 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____6124) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail ()
                 else
                   (let b = FStar_List.nth binders i in
                    let uu____6147 =
                      FStar_Syntax_Util.mk_field_projector_name lid (fst b) i in
                    FStar_All.pipe_right uu____6147 FStar_Pervasives.fst)
             | uu____6152 -> fail ())
let is_projector: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____6159 = lookup_qname env l in
      match uu____6159 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____6170,uu____6171,uu____6172);
              FStar_Syntax_Syntax.sigrng = uu____6173;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____6175;_},uu____6176),uu____6177)
          ->
          FStar_Util.for_some
            (fun uu___105_6202  ->
               match uu___105_6202 with
               | FStar_Syntax_Syntax.Projector uu____6203 -> true
               | uu____6206 -> false) quals
      | uu____6207 -> false
let is_datacon: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____6224 = lookup_qname env lid in
      match uu____6224 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____6235,uu____6236,uu____6237,uu____6238,uu____6239,uu____6240);
              FStar_Syntax_Syntax.sigrng = uu____6241;
              FStar_Syntax_Syntax.sigquals = uu____6242;
              FStar_Syntax_Syntax.sigmeta = uu____6243;_},uu____6244),uu____6245)
          -> true
      | uu____6272 -> false
let is_record: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____6289 = lookup_qname env lid in
      match uu____6289 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____6300,uu____6301,uu____6302,uu____6303,uu____6304,uu____6305);
              FStar_Syntax_Syntax.sigrng = uu____6306;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____6308;_},uu____6309),uu____6310)
          ->
          FStar_Util.for_some
            (fun uu___106_6339  ->
               match uu___106_6339 with
               | FStar_Syntax_Syntax.RecordType uu____6340 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____6345 -> true
               | uu____6350 -> false) quals
      | uu____6351 -> false
let is_action: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____6368 = lookup_qname env lid in
      match uu____6368 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                (uu____6379,uu____6380,uu____6381);
              FStar_Syntax_Syntax.sigrng = uu____6382;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____6384;_},uu____6385),uu____6386)
          ->
          FStar_Util.for_some
            (fun uu___107_6415  ->
               match uu___107_6415 with
               | FStar_Syntax_Syntax.Action uu____6416 -> true
               | uu____6417 -> false) quals
      | uu____6418 -> false
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
      let uu____6437 =
        let uu____6438 = FStar_Syntax_Util.un_uinst head1 in
        uu____6438.FStar_Syntax_Syntax.n in
      match uu____6437 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          fv.FStar_Syntax_Syntax.fv_delta =
            FStar_Syntax_Syntax.Delta_equational
      | uu____6442 -> false
let is_type_constructor: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let mapper x =
        match fst x with
        | FStar_Util.Inl uu____6480 -> Some false
        | FStar_Util.Inr (se,uu____6489) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____6498 ->
                 Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____6502 -> Some true
             | uu____6511 -> Some false) in
      let uu____6512 =
        let uu____6514 = lookup_qname env lid in
        FStar_Util.bind_opt uu____6514 mapper in
      match uu____6512 with | Some b -> b | None  -> false
let num_inductive_ty_params: env -> FStar_Ident.lident -> Prims.int =
  fun env  ->
    fun lid  ->
      let uu____6541 = lookup_qname env lid in
      match uu____6541 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____6552,uu____6553,tps,uu____6555,uu____6556,uu____6557);
              FStar_Syntax_Syntax.sigrng = uu____6558;
              FStar_Syntax_Syntax.sigquals = uu____6559;
              FStar_Syntax_Syntax.sigmeta = uu____6560;_},uu____6561),uu____6562)
          -> FStar_List.length tps
      | uu____6595 ->
          let uu____6606 =
            let uu____6607 =
              let uu____6610 = name_not_found lid in
              (uu____6610, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____6607 in
          raise uu____6606
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
           (fun uu____6632  ->
              match uu____6632 with
              | (d,uu____6637) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
let get_effect_decl:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl =
  fun env  ->
    fun l  ->
      let uu____6646 = effect_decl_opt env l in
      match uu____6646 with
      | None  ->
          let uu____6654 =
            let uu____6655 =
              let uu____6658 = name_not_found l in
              (uu____6658, (FStar_Ident.range_of_lid l)) in
            FStar_Errors.Error uu____6655 in
          raise uu____6654
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
            (let uu____6701 =
               FStar_All.pipe_right (env.effects).joins
                 (FStar_Util.find_opt
                    (fun uu____6725  ->
                       match uu____6725 with
                       | (m1,m2,uu____6733,uu____6734,uu____6735) ->
                           (FStar_Ident.lid_equals l1 m1) &&
                             (FStar_Ident.lid_equals l2 m2))) in
             match uu____6701 with
             | None  ->
                 let uu____6744 =
                   let uu____6745 =
                     let uu____6748 =
                       let uu____6749 = FStar_Syntax_Print.lid_to_string l1 in
                       let uu____6750 = FStar_Syntax_Print.lid_to_string l2 in
                       FStar_Util.format2
                         "Effects %s and %s cannot be composed" uu____6749
                         uu____6750 in
                     (uu____6748, (env.range)) in
                   FStar_Errors.Error uu____6745 in
                 raise uu____6744
             | Some (uu____6754,uu____6755,m3,j1,j2) -> (m3, j1, j2))
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
  let uu____6802 =
    FStar_All.pipe_right decls
      (FStar_Util.find_opt
         (fun uu____6814  ->
            match uu____6814 with
            | (d,uu____6818) ->
                FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m)) in
  match uu____6802 with
  | None  ->
      let uu____6825 =
        FStar_Util.format1 "Impossible: declaration for monad %s not found"
          m.FStar_Ident.str in
      failwith uu____6825
  | Some (md,_q) ->
      let uu____6834 =
        inst_tscheme
          ((md.FStar_Syntax_Syntax.univs),
            (md.FStar_Syntax_Syntax.signature)) in
      (match uu____6834 with
       | (uu____6841,s) ->
           let s1 = FStar_Syntax_Subst.compress s in
           (match ((md.FStar_Syntax_Syntax.binders),
                    (s1.FStar_Syntax_Syntax.n))
            with
            | ([],FStar_Syntax_Syntax.Tm_arrow
               ((a,uu____6849)::(wp,uu____6851)::[],c)) when
                FStar_Syntax_Syntax.is_teff (FStar_Syntax_Util.comp_result c)
                -> (a, (wp.FStar_Syntax_Syntax.sort))
            | uu____6873 -> failwith "Impossible"))
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
                 let uu____6909 = get_range env in
                 let uu____6910 =
                   let uu____6913 =
                     let uu____6914 =
                       let uu____6924 =
                         let uu____6926 = FStar_Syntax_Syntax.as_arg res_t in
                         [uu____6926] in
                       (null_wp, uu____6924) in
                     FStar_Syntax_Syntax.Tm_app uu____6914 in
                   FStar_Syntax_Syntax.mk uu____6913 in
                 uu____6910 None uu____6909 in
               let uu____6936 =
                 let uu____6937 =
                   let uu____6943 = FStar_Syntax_Syntax.as_arg null_wp_res in
                   [uu____6943] in
                 {
                   FStar_Syntax_Syntax.comp_univs = [res_u];
                   FStar_Syntax_Syntax.effect_name = eff_name1;
                   FStar_Syntax_Syntax.result_typ = res_t;
                   FStar_Syntax_Syntax.effect_args = uu____6937;
                   FStar_Syntax_Syntax.flags = []
                 } in
               FStar_Syntax_Syntax.mk_Comp uu____6936)
let build_lattice: env -> FStar_Syntax_Syntax.sigelt -> env =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___118_6952 = env.effects in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___118_6952.order);
              joins = (uu___118_6952.joins)
            } in
          let uu___119_6957 = env in
          {
            solver = (uu___119_6957.solver);
            range = (uu___119_6957.range);
            curmodule = (uu___119_6957.curmodule);
            gamma = (uu___119_6957.gamma);
            gamma_cache = (uu___119_6957.gamma_cache);
            modules = (uu___119_6957.modules);
            expected_typ = (uu___119_6957.expected_typ);
            sigtab = (uu___119_6957.sigtab);
            is_pattern = (uu___119_6957.is_pattern);
            instantiate_imp = (uu___119_6957.instantiate_imp);
            effects;
            generalize = (uu___119_6957.generalize);
            letrecs = (uu___119_6957.letrecs);
            top_level = (uu___119_6957.top_level);
            check_uvars = (uu___119_6957.check_uvars);
            use_eq = (uu___119_6957.use_eq);
            is_iface = (uu___119_6957.is_iface);
            admit = (uu___119_6957.admit);
            lax = (uu___119_6957.lax);
            lax_universes = (uu___119_6957.lax_universes);
            type_of = (uu___119_6957.type_of);
            universe_of = (uu___119_6957.universe_of);
            use_bv_sorts = (uu___119_6957.use_bv_sorts);
            qname_and_index = (uu___119_6957.qname_and_index);
            proof_ns = (uu___119_6957.proof_ns);
            synth = (uu___119_6957.synth)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp r wp1 =
                let uu____6974 = (e1.mlift).mlift_wp r wp1 in
                (e2.mlift).mlift_wp r uu____6974 in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (Some l1,Some l2) ->
                    Some
                      ((fun t  ->
                          fun wp  ->
                            fun e  ->
                              let uu____7053 = (e1.mlift).mlift_wp t wp in
                              let uu____7054 = l1 t wp e in
                              l2 t uu____7053 uu____7054))
                | uu____7055 -> None in
              { mlift_wp; mlift_term } in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            } in
          let mk_mlift_wp lift_t r wp1 =
            let uu____7090 = inst_tscheme lift_t in
            match uu____7090 with
            | (uu____7095,lift_t1) ->
                let uu____7097 =
                  let uu____7100 =
                    let uu____7101 =
                      let uu____7111 =
                        let uu____7113 = FStar_Syntax_Syntax.as_arg r in
                        let uu____7114 =
                          let uu____7116 = FStar_Syntax_Syntax.as_arg wp1 in
                          [uu____7116] in
                        uu____7113 :: uu____7114 in
                      (lift_t1, uu____7111) in
                    FStar_Syntax_Syntax.Tm_app uu____7101 in
                  FStar_Syntax_Syntax.mk uu____7100 in
                uu____7097 None wp1.FStar_Syntax_Syntax.pos in
          let sub_mlift_wp =
            match sub1.FStar_Syntax_Syntax.lift_wp with
            | Some sub_lift_wp -> mk_mlift_wp sub_lift_wp
            | None  ->
                failwith "sub effect should've been elaborated at this stage" in
          let mk_mlift_term lift_t r wp1 e =
            let uu____7161 = inst_tscheme lift_t in
            match uu____7161 with
            | (uu____7166,lift_t1) ->
                let uu____7168 =
                  let uu____7171 =
                    let uu____7172 =
                      let uu____7182 =
                        let uu____7184 = FStar_Syntax_Syntax.as_arg r in
                        let uu____7185 =
                          let uu____7187 = FStar_Syntax_Syntax.as_arg wp1 in
                          let uu____7188 =
                            let uu____7190 = FStar_Syntax_Syntax.as_arg e in
                            [uu____7190] in
                          uu____7187 :: uu____7188 in
                        uu____7184 :: uu____7185 in
                      (lift_t1, uu____7182) in
                    FStar_Syntax_Syntax.Tm_app uu____7172 in
                  FStar_Syntax_Syntax.mk uu____7171 in
                uu____7168 None e.FStar_Syntax_Syntax.pos in
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
              let uu____7231 =
                let uu____7232 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange in
                FStar_Syntax_Syntax.lid_as_fv uu____7232
                  FStar_Syntax_Syntax.Delta_constant None in
              FStar_Syntax_Syntax.fv_to_tm uu____7231 in
            let arg = bogus_term "ARG" in
            let wp = bogus_term "WP" in
            let e = bogus_term "COMP" in
            let uu____7236 =
              let uu____7237 = l.mlift_wp arg wp in
              FStar_Syntax_Print.term_to_string uu____7237 in
            let uu____7238 =
              let uu____7239 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____7254 = l1 arg wp e in
                     FStar_Syntax_Print.term_to_string uu____7254) in
              FStar_Util.dflt "none" uu____7239 in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____7236
              uu____7238 in
          let order = edge :: ((env.effects).order) in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____7267  ->
                    match uu____7267 with
                    | (e,uu____7272) -> e.FStar_Syntax_Syntax.mname)) in
          let find_edge order1 uu____7285 =
            match uu____7285 with
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
              let uu____7310 =
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
                                    (let uu____7322 =
                                       let uu____7327 =
                                         find_edge order1 (i, k) in
                                       let uu____7329 =
                                         find_edge order1 (k, j) in
                                       (uu____7327, uu____7329) in
                                     match uu____7322 with
                                     | (Some e1,Some e2) ->
                                         let uu____7338 = compose_edges e1 e2 in
                                         [uu____7338]
                                     | uu____7339 -> []))))) in
              FStar_List.append order1 uu____7310 in
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
                   let uu____7354 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Syntax_Const.effect_DIV_lid)
                       &&
                       (let uu____7355 =
                          lookup_effect_quals env edge1.mtarget in
                        FStar_All.pipe_right uu____7355
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect)) in
                   if uu____7354
                   then
                     let uu____7358 =
                       let uu____7359 =
                         let uu____7362 =
                           FStar_Util.format1
                             "Divergent computations cannot be included in an effect %s marked 'total'"
                             (edge1.mtarget).FStar_Ident.str in
                         let uu____7363 = get_range env in
                         (uu____7362, uu____7363) in
                       FStar_Errors.Error uu____7359 in
                     raise uu____7358
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
                                            let uu____7426 =
                                              let uu____7431 =
                                                find_edge order2 (i, k) in
                                              let uu____7433 =
                                                find_edge order2 (j, k) in
                                              (uu____7431, uu____7433) in
                                            match uu____7426 with
                                            | (Some ik,Some jk) ->
                                                (match bopt with
                                                 | None  -> Some (k, ik, jk)
                                                 | Some
                                                     (ub,uu____7456,uu____7457)
                                                     ->
                                                     let uu____7461 =
                                                       let uu____7464 =
                                                         let uu____7465 =
                                                           find_edge order2
                                                             (k, ub) in
                                                         FStar_Util.is_some
                                                           uu____7465 in
                                                       let uu____7467 =
                                                         let uu____7468 =
                                                           find_edge order2
                                                             (ub, k) in
                                                         FStar_Util.is_some
                                                           uu____7468 in
                                                       (uu____7464,
                                                         uu____7467) in
                                                     (match uu____7461 with
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
                                            | uu____7487 -> bopt) None) in
                              match join_opt with
                              | None  -> []
                              | Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))])))) in
            let effects =
              let uu___120_7526 = env.effects in
              { decls = (uu___120_7526.decls); order = order2; joins } in
            let uu___121_7527 = env in
            {
              solver = (uu___121_7527.solver);
              range = (uu___121_7527.range);
              curmodule = (uu___121_7527.curmodule);
              gamma = (uu___121_7527.gamma);
              gamma_cache = (uu___121_7527.gamma_cache);
              modules = (uu___121_7527.modules);
              expected_typ = (uu___121_7527.expected_typ);
              sigtab = (uu___121_7527.sigtab);
              is_pattern = (uu___121_7527.is_pattern);
              instantiate_imp = (uu___121_7527.instantiate_imp);
              effects;
              generalize = (uu___121_7527.generalize);
              letrecs = (uu___121_7527.letrecs);
              top_level = (uu___121_7527.top_level);
              check_uvars = (uu___121_7527.check_uvars);
              use_eq = (uu___121_7527.use_eq);
              is_iface = (uu___121_7527.is_iface);
              admit = (uu___121_7527.admit);
              lax = (uu___121_7527.lax);
              lax_universes = (uu___121_7527.lax_universes);
              type_of = (uu___121_7527.type_of);
              universe_of = (uu___121_7527.universe_of);
              use_bv_sorts = (uu___121_7527.use_bv_sorts);
              qname_and_index = (uu___121_7527.qname_and_index);
              proof_ns = (uu___121_7527.proof_ns);
              synth = (uu___121_7527.synth)
            }))
      | uu____7528 -> env
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
        | uu____7550 -> c in
      FStar_Syntax_Util.comp_to_comp_typ c1
let rec unfold_effect_abbrev:
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp in
      let uu____7558 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name in
      match uu____7558 with
      | None  -> c
      | Some (binders,cdef) ->
          let uu____7568 = FStar_Syntax_Subst.open_comp binders cdef in
          (match uu____7568 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____7590 =
                     let uu____7591 =
                       let uu____7594 =
                         let uu____7595 =
                           FStar_Util.string_of_int
                             (FStar_List.length binders1) in
                         let uu____7604 =
                           FStar_Util.string_of_int
                             ((FStar_List.length
                                 c.FStar_Syntax_Syntax.effect_args)
                                + (Prims.parse_int "1")) in
                         let uu____7615 =
                           let uu____7616 = FStar_Syntax_Syntax.mk_Comp c in
                           FStar_Syntax_Print.comp_to_string uu____7616 in
                         FStar_Util.format3
                           "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                           uu____7595 uu____7604 uu____7615 in
                       (uu____7594, (comp.FStar_Syntax_Syntax.pos)) in
                     FStar_Errors.Error uu____7591 in
                   raise uu____7590)
                else ();
                (let inst1 =
                   let uu____7620 =
                     let uu____7626 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ in
                     uu____7626 :: (c.FStar_Syntax_Syntax.effect_args) in
                   FStar_List.map2
                     (fun uu____7633  ->
                        fun uu____7634  ->
                          match (uu____7633, uu____7634) with
                          | ((x,uu____7648),(t,uu____7650)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____7620 in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1 in
                 let c2 =
                   let uu____7665 =
                     let uu___122_7666 = comp_to_comp_typ env c1 in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___122_7666.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___122_7666.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___122_7666.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___122_7666.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     } in
                   FStar_All.pipe_right uu____7665
                     FStar_Syntax_Syntax.mk_Comp in
                 unfold_effect_abbrev env c2)))
let effect_repr_aux only_reifiable env c u_c =
  let uu____7696 =
    let uu____7701 = norm_eff_name env (FStar_Syntax_Util.comp_effect_name c) in
    effect_decl_opt env uu____7701 in
  match uu____7696 with
  | None  -> None
  | Some (ed,qualifiers) ->
      let uu____7717 =
        only_reifiable &&
          (let uu____7718 =
             FStar_All.pipe_right qualifiers
               (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
           Prims.op_Negation uu____7718) in
      if uu____7717
      then None
      else
        (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_unknown  -> None
         | uu____7731 ->
             let c1 = unfold_effect_abbrev env c in
             let uu____7733 =
               let uu____7742 =
                 FStar_List.hd c1.FStar_Syntax_Syntax.effect_args in
               ((c1.FStar_Syntax_Syntax.result_typ), uu____7742) in
             (match uu____7733 with
              | (res_typ,wp) ->
                  let repr =
                    inst_effect_fun_with [u_c] env ed
                      ([], (ed.FStar_Syntax_Syntax.repr)) in
                  let uu____7776 =
                    let uu____7779 = get_range env in
                    let uu____7780 =
                      let uu____7783 =
                        let uu____7784 =
                          let uu____7794 =
                            let uu____7796 =
                              FStar_Syntax_Syntax.as_arg res_typ in
                            [uu____7796; wp] in
                          (repr, uu____7794) in
                        FStar_Syntax_Syntax.Tm_app uu____7784 in
                      FStar_Syntax_Syntax.mk uu____7783 in
                    uu____7780 None uu____7779 in
                  Some uu____7776))
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
          let uu____7840 =
            let uu____7841 =
              let uu____7844 =
                let uu____7845 = FStar_Ident.string_of_lid l in
                FStar_Util.format1 "Effect %s cannot be reified" uu____7845 in
              let uu____7846 = get_range env in (uu____7844, uu____7846) in
            FStar_Errors.Error uu____7841 in
          raise uu____7840 in
        let uu____7847 = effect_repr_aux true env c u_c in
        match uu____7847 with
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
        | FStar_Util.Inr (eff_name,uu____7879) -> eff_name in
      is_reifiable_effect env effect_lid
let is_reifiable_comp: env -> FStar_Syntax_Syntax.comp -> Prims.bool =
  fun env  ->
    fun c  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Comp ct ->
          is_reifiable_effect env ct.FStar_Syntax_Syntax.effect_name
      | uu____7892 -> false
let is_reifiable_function: env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____7899 =
        let uu____7900 = FStar_Syntax_Subst.compress t in
        uu____7900.FStar_Syntax_Syntax.n in
      match uu____7899 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____7903,c) ->
          is_reifiable_comp env c
      | uu____7915 -> false
let push_in_gamma: env -> binding -> env =
  fun env  ->
    fun s  ->
      let rec push1 x rest =
        match rest with
        | (Binding_sig uu____7933)::uu____7934 -> x :: rest
        | (Binding_sig_inst uu____7939)::uu____7940 -> x :: rest
        | [] -> [x]
        | local::rest1 ->
            let uu____7949 = push1 x rest1 in local :: uu____7949 in
      let uu___123_7951 = env in
      let uu____7952 = push1 s env.gamma in
      {
        solver = (uu___123_7951.solver);
        range = (uu___123_7951.range);
        curmodule = (uu___123_7951.curmodule);
        gamma = uu____7952;
        gamma_cache = (uu___123_7951.gamma_cache);
        modules = (uu___123_7951.modules);
        expected_typ = (uu___123_7951.expected_typ);
        sigtab = (uu___123_7951.sigtab);
        is_pattern = (uu___123_7951.is_pattern);
        instantiate_imp = (uu___123_7951.instantiate_imp);
        effects = (uu___123_7951.effects);
        generalize = (uu___123_7951.generalize);
        letrecs = (uu___123_7951.letrecs);
        top_level = (uu___123_7951.top_level);
        check_uvars = (uu___123_7951.check_uvars);
        use_eq = (uu___123_7951.use_eq);
        is_iface = (uu___123_7951.is_iface);
        admit = (uu___123_7951.admit);
        lax = (uu___123_7951.lax);
        lax_universes = (uu___123_7951.lax_universes);
        type_of = (uu___123_7951.type_of);
        universe_of = (uu___123_7951.universe_of);
        use_bv_sorts = (uu___123_7951.use_bv_sorts);
        qname_and_index = (uu___123_7951.qname_and_index);
        proof_ns = (uu___123_7951.proof_ns);
        synth = (uu___123_7951.synth)
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
      let uu___124_7979 = env in
      {
        solver = (uu___124_7979.solver);
        range = (uu___124_7979.range);
        curmodule = (uu___124_7979.curmodule);
        gamma = (b :: (env.gamma));
        gamma_cache = (uu___124_7979.gamma_cache);
        modules = (uu___124_7979.modules);
        expected_typ = (uu___124_7979.expected_typ);
        sigtab = (uu___124_7979.sigtab);
        is_pattern = (uu___124_7979.is_pattern);
        instantiate_imp = (uu___124_7979.instantiate_imp);
        effects = (uu___124_7979.effects);
        generalize = (uu___124_7979.generalize);
        letrecs = (uu___124_7979.letrecs);
        top_level = (uu___124_7979.top_level);
        check_uvars = (uu___124_7979.check_uvars);
        use_eq = (uu___124_7979.use_eq);
        is_iface = (uu___124_7979.is_iface);
        admit = (uu___124_7979.admit);
        lax = (uu___124_7979.lax);
        lax_universes = (uu___124_7979.lax_universes);
        type_of = (uu___124_7979.type_of);
        universe_of = (uu___124_7979.universe_of);
        use_bv_sorts = (uu___124_7979.use_bv_sorts);
        qname_and_index = (uu___124_7979.qname_and_index);
        proof_ns = (uu___124_7979.proof_ns);
        synth = (uu___124_7979.synth)
      }
let push_bv: env -> FStar_Syntax_Syntax.bv -> env =
  fun env  -> fun x  -> push_local_binding env (Binding_var x)
let pop_bv: env -> (FStar_Syntax_Syntax.bv* env) option =
  fun env  ->
    match env.gamma with
    | (Binding_var x)::rest ->
        Some
          (x,
            (let uu___125_8000 = env in
             {
               solver = (uu___125_8000.solver);
               range = (uu___125_8000.range);
               curmodule = (uu___125_8000.curmodule);
               gamma = rest;
               gamma_cache = (uu___125_8000.gamma_cache);
               modules = (uu___125_8000.modules);
               expected_typ = (uu___125_8000.expected_typ);
               sigtab = (uu___125_8000.sigtab);
               is_pattern = (uu___125_8000.is_pattern);
               instantiate_imp = (uu___125_8000.instantiate_imp);
               effects = (uu___125_8000.effects);
               generalize = (uu___125_8000.generalize);
               letrecs = (uu___125_8000.letrecs);
               top_level = (uu___125_8000.top_level);
               check_uvars = (uu___125_8000.check_uvars);
               use_eq = (uu___125_8000.use_eq);
               is_iface = (uu___125_8000.is_iface);
               admit = (uu___125_8000.admit);
               lax = (uu___125_8000.lax);
               lax_universes = (uu___125_8000.lax_universes);
               type_of = (uu___125_8000.type_of);
               universe_of = (uu___125_8000.universe_of);
               use_bv_sorts = (uu___125_8000.use_bv_sorts);
               qname_and_index = (uu___125_8000.qname_and_index);
               proof_ns = (uu___125_8000.proof_ns);
               synth = (uu___125_8000.synth)
             }))
    | uu____8001 -> None
let push_binders: env -> FStar_Syntax_Syntax.binders -> env =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____8014  ->
             match uu____8014 with | (x,uu____8018) -> push_bv env1 x) env bs
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
            let uu___126_8038 = x1 in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___126_8038.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___126_8038.FStar_Syntax_Syntax.index);
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
      (let uu___127_8068 = env in
       {
         solver = (uu___127_8068.solver);
         range = (uu___127_8068.range);
         curmodule = (uu___127_8068.curmodule);
         gamma = [];
         gamma_cache = (uu___127_8068.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = None;
         sigtab = (uu___127_8068.sigtab);
         is_pattern = (uu___127_8068.is_pattern);
         instantiate_imp = (uu___127_8068.instantiate_imp);
         effects = (uu___127_8068.effects);
         generalize = (uu___127_8068.generalize);
         letrecs = (uu___127_8068.letrecs);
         top_level = (uu___127_8068.top_level);
         check_uvars = (uu___127_8068.check_uvars);
         use_eq = (uu___127_8068.use_eq);
         is_iface = (uu___127_8068.is_iface);
         admit = (uu___127_8068.admit);
         lax = (uu___127_8068.lax);
         lax_universes = (uu___127_8068.lax_universes);
         type_of = (uu___127_8068.type_of);
         universe_of = (uu___127_8068.universe_of);
         use_bv_sorts = (uu___127_8068.use_bv_sorts);
         qname_and_index = (uu___127_8068.qname_and_index);
         proof_ns = (uu___127_8068.proof_ns);
         synth = (uu___127_8068.synth)
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
        let uu____8092 = FStar_Syntax_Subst.univ_var_opening uvs in
        match uu____8092 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars in
            let uu____8108 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms in
            (env', univ_vars, uu____8108)
let set_expected_typ: env -> FStar_Syntax_Syntax.typ -> env =
  fun env  ->
    fun t  ->
      let uu___128_8118 = env in
      {
        solver = (uu___128_8118.solver);
        range = (uu___128_8118.range);
        curmodule = (uu___128_8118.curmodule);
        gamma = (uu___128_8118.gamma);
        gamma_cache = (uu___128_8118.gamma_cache);
        modules = (uu___128_8118.modules);
        expected_typ = (Some t);
        sigtab = (uu___128_8118.sigtab);
        is_pattern = (uu___128_8118.is_pattern);
        instantiate_imp = (uu___128_8118.instantiate_imp);
        effects = (uu___128_8118.effects);
        generalize = (uu___128_8118.generalize);
        letrecs = (uu___128_8118.letrecs);
        top_level = (uu___128_8118.top_level);
        check_uvars = (uu___128_8118.check_uvars);
        use_eq = false;
        is_iface = (uu___128_8118.is_iface);
        admit = (uu___128_8118.admit);
        lax = (uu___128_8118.lax);
        lax_universes = (uu___128_8118.lax_universes);
        type_of = (uu___128_8118.type_of);
        universe_of = (uu___128_8118.universe_of);
        use_bv_sorts = (uu___128_8118.use_bv_sorts);
        qname_and_index = (uu___128_8118.qname_and_index);
        proof_ns = (uu___128_8118.proof_ns);
        synth = (uu___128_8118.synth)
      }
let expected_typ: env -> FStar_Syntax_Syntax.typ option =
  fun env  -> match env.expected_typ with | None  -> None | Some t -> Some t
let clear_expected_typ: env -> (env* FStar_Syntax_Syntax.typ option) =
  fun env_  ->
    let uu____8134 = expected_typ env_ in
    ((let uu___129_8137 = env_ in
      {
        solver = (uu___129_8137.solver);
        range = (uu___129_8137.range);
        curmodule = (uu___129_8137.curmodule);
        gamma = (uu___129_8137.gamma);
        gamma_cache = (uu___129_8137.gamma_cache);
        modules = (uu___129_8137.modules);
        expected_typ = None;
        sigtab = (uu___129_8137.sigtab);
        is_pattern = (uu___129_8137.is_pattern);
        instantiate_imp = (uu___129_8137.instantiate_imp);
        effects = (uu___129_8137.effects);
        generalize = (uu___129_8137.generalize);
        letrecs = (uu___129_8137.letrecs);
        top_level = (uu___129_8137.top_level);
        check_uvars = (uu___129_8137.check_uvars);
        use_eq = false;
        is_iface = (uu___129_8137.is_iface);
        admit = (uu___129_8137.admit);
        lax = (uu___129_8137.lax);
        lax_universes = (uu___129_8137.lax_universes);
        type_of = (uu___129_8137.type_of);
        universe_of = (uu___129_8137.universe_of);
        use_bv_sorts = (uu___129_8137.use_bv_sorts);
        qname_and_index = (uu___129_8137.qname_and_index);
        proof_ns = (uu___129_8137.proof_ns);
        synth = (uu___129_8137.synth)
      }), uu____8134)
let finish_module: env -> FStar_Syntax_Syntax.modul -> env =
  let empty_lid = FStar_Ident.lid_of_ids [FStar_Ident.id_of_text ""] in
  fun env  ->
    fun m  ->
      let sigs =
        if
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Syntax_Const.prims_lid
        then
          let uu____8148 =
            FStar_All.pipe_right env.gamma
              (FStar_List.collect
                 (fun uu___108_8152  ->
                    match uu___108_8152 with
                    | Binding_sig (uu____8154,se) -> [se]
                    | uu____8158 -> [])) in
          FStar_All.pipe_right uu____8148 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports in
      add_sigelts env sigs;
      (let uu___130_8163 = env in
       {
         solver = (uu___130_8163.solver);
         range = (uu___130_8163.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_cache = (uu___130_8163.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___130_8163.expected_typ);
         sigtab = (uu___130_8163.sigtab);
         is_pattern = (uu___130_8163.is_pattern);
         instantiate_imp = (uu___130_8163.instantiate_imp);
         effects = (uu___130_8163.effects);
         generalize = (uu___130_8163.generalize);
         letrecs = (uu___130_8163.letrecs);
         top_level = (uu___130_8163.top_level);
         check_uvars = (uu___130_8163.check_uvars);
         use_eq = (uu___130_8163.use_eq);
         is_iface = (uu___130_8163.is_iface);
         admit = (uu___130_8163.admit);
         lax = (uu___130_8163.lax);
         lax_universes = (uu___130_8163.lax_universes);
         type_of = (uu___130_8163.type_of);
         universe_of = (uu___130_8163.universe_of);
         use_bv_sorts = (uu___130_8163.use_bv_sorts);
         qname_and_index = (uu___130_8163.qname_and_index);
         proof_ns = (uu___130_8163.proof_ns);
         synth = (uu___130_8163.synth)
       })
let uvars_in_env:
  env -> (FStar_Syntax_Syntax.uvar* FStar_Syntax_Syntax.typ) FStar_Util.set =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_univ uu____8213)::tl1 -> aux out tl1
      | (Binding_lid (uu____8216,(uu____8217,t)))::tl1 ->
          let uu____8226 =
            let uu____8230 = FStar_Syntax_Free.uvars t in ext out uu____8230 in
          aux uu____8226 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____8234;
            FStar_Syntax_Syntax.index = uu____8235;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____8241 =
            let uu____8245 = FStar_Syntax_Free.uvars t in ext out uu____8245 in
          aux uu____8241 tl1
      | (Binding_sig uu____8249)::uu____8250 -> out
      | (Binding_sig_inst uu____8255)::uu____8256 -> out in
    aux no_uvs env.gamma
let univ_vars: env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____8293)::tl1 -> aux out tl1
      | (Binding_univ uu____8300)::tl1 -> aux out tl1
      | (Binding_lid (uu____8303,(uu____8304,t)))::tl1 ->
          let uu____8313 =
            let uu____8315 = FStar_Syntax_Free.univs t in ext out uu____8315 in
          aux uu____8313 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____8317;
            FStar_Syntax_Syntax.index = uu____8318;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____8324 =
            let uu____8326 = FStar_Syntax_Free.univs t in ext out uu____8326 in
          aux uu____8324 tl1
      | (Binding_sig uu____8328)::uu____8329 -> out in
    aux no_univs env.gamma
let univnames: env -> FStar_Syntax_Syntax.univ_name FStar_Util.set =
  fun env  ->
    let no_univ_names = FStar_Syntax_Syntax.no_universe_names in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____8366)::tl1 -> aux out tl1
      | (Binding_univ uname)::tl1 ->
          let uu____8376 = FStar_Util.set_add uname out in aux uu____8376 tl1
      | (Binding_lid (uu____8378,(uu____8379,t)))::tl1 ->
          let uu____8388 =
            let uu____8390 = FStar_Syntax_Free.univnames t in
            ext out uu____8390 in
          aux uu____8388 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____8392;
            FStar_Syntax_Syntax.index = uu____8393;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____8399 =
            let uu____8401 = FStar_Syntax_Free.univnames t in
            ext out uu____8401 in
          aux uu____8399 tl1
      | (Binding_sig uu____8403)::uu____8404 -> out in
    aux no_univ_names env.gamma
let bound_vars_of_bindings:
  binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___109_8420  ->
            match uu___109_8420 with
            | Binding_var x -> [x]
            | Binding_lid uu____8423 -> []
            | Binding_sig uu____8426 -> []
            | Binding_univ uu____8430 -> []
            | Binding_sig_inst uu____8431 -> []))
let binders_of_bindings:
  binding Prims.list -> FStar_Syntax_Syntax.binder Prims.list =
  fun bs  ->
    let uu____8441 =
      let uu____8443 = bound_vars_of_bindings bs in
      FStar_All.pipe_right uu____8443
        (FStar_List.map FStar_Syntax_Syntax.mk_binder) in
    FStar_All.pipe_right uu____8441 FStar_List.rev
let bound_vars: env -> FStar_Syntax_Syntax.bv Prims.list =
  fun env  -> bound_vars_of_bindings env.gamma
let all_binders: env -> FStar_Syntax_Syntax.binders =
  fun env  -> binders_of_bindings env.gamma
let print_gamma: env -> Prims.unit =
  fun env  ->
    let uu____8459 =
      let uu____8460 =
        FStar_All.pipe_right env.gamma
          (FStar_List.map
             (fun uu___110_8464  ->
                match uu___110_8464 with
                | Binding_var x ->
                    let uu____8466 = FStar_Syntax_Print.bv_to_string x in
                    Prims.strcat "Binding_var " uu____8466
                | Binding_univ u ->
                    Prims.strcat "Binding_univ " u.FStar_Ident.idText
                | Binding_lid (l,uu____8469) ->
                    let uu____8470 = FStar_Ident.string_of_lid l in
                    Prims.strcat "Binding_lid " uu____8470
                | Binding_sig (ls,uu____8472) ->
                    let uu____8475 =
                      let uu____8476 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____8476
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig " uu____8475
                | Binding_sig_inst (ls,uu____8482,uu____8483) ->
                    let uu____8486 =
                      let uu____8487 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____8487
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig_inst " uu____8486)) in
      FStar_All.pipe_right uu____8460 (FStar_String.concat "::\n") in
    FStar_All.pipe_right uu____8459 (FStar_Util.print1 "%s\n")
let eq_gamma: env -> env -> Prims.bool =
  fun env  ->
    fun env'  ->
      let uu____8499 = FStar_Util.physical_equality env.gamma env'.gamma in
      if uu____8499
      then true
      else
        (let g = all_binders env in
         let g' = all_binders env' in
         ((FStar_List.length g) = (FStar_List.length g')) &&
           (FStar_List.forall2
              (fun uu____8520  ->
                 fun uu____8521  ->
                   match (uu____8520, uu____8521) with
                   | ((b1,uu____8531),(b2,uu____8533)) ->
                       FStar_Syntax_Syntax.bv_eq b1 b2) g g'))
let fold_env env f a =
  FStar_List.fold_right (fun e  -> fun a1  -> f a1 e) env.gamma a
let lidents: env -> FStar_Ident.lident Prims.list =
  fun env  ->
    let keys =
      FStar_List.fold_left
        (fun keys  ->
           fun uu___111_8576  ->
             match uu___111_8576 with
             | Binding_sig (lids,uu____8580) -> FStar_List.append lids keys
             | uu____8583 -> keys) [] env.gamma in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____8585  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
let should_enc_path: env -> Prims.string Prims.list -> Prims.bool =
  fun env  ->
    fun path  ->
      let rec list_prefix xs ys =
        match (xs, ys) with
        | ([],uu____8610) -> true
        | (x::xs1,y::ys1) -> (x = y) && (list_prefix xs1 ys1)
        | (uu____8622,uu____8623) -> false in
      let rec should_enc_path' pns path1 =
        match pns with
        | [] -> true
        | (p,b)::pns1 ->
            let uu____8647 = list_prefix p path1 in
            if uu____8647 then b else should_enc_path' pns1 path1 in
      should_enc_path' (FStar_List.flatten env.proof_ns) path
let should_enc_lid: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____8657 = FStar_Ident.path_of_lid lid in
      should_enc_path env uu____8657
let cons_proof_ns: Prims.bool -> env -> name_prefix -> env =
  fun b  ->
    fun e  ->
      fun path  ->
        match e.proof_ns with
        | [] -> failwith "empty proof_ns stack!"
        | pns::rest ->
            let pns' = (path, b) :: pns in
            let uu___131_8677 = e in
            {
              solver = (uu___131_8677.solver);
              range = (uu___131_8677.range);
              curmodule = (uu___131_8677.curmodule);
              gamma = (uu___131_8677.gamma);
              gamma_cache = (uu___131_8677.gamma_cache);
              modules = (uu___131_8677.modules);
              expected_typ = (uu___131_8677.expected_typ);
              sigtab = (uu___131_8677.sigtab);
              is_pattern = (uu___131_8677.is_pattern);
              instantiate_imp = (uu___131_8677.instantiate_imp);
              effects = (uu___131_8677.effects);
              generalize = (uu___131_8677.generalize);
              letrecs = (uu___131_8677.letrecs);
              top_level = (uu___131_8677.top_level);
              check_uvars = (uu___131_8677.check_uvars);
              use_eq = (uu___131_8677.use_eq);
              is_iface = (uu___131_8677.is_iface);
              admit = (uu___131_8677.admit);
              lax = (uu___131_8677.lax);
              lax_universes = (uu___131_8677.lax_universes);
              type_of = (uu___131_8677.type_of);
              universe_of = (uu___131_8677.universe_of);
              use_bv_sorts = (uu___131_8677.use_bv_sorts);
              qname_and_index = (uu___131_8677.qname_and_index);
              proof_ns = (pns' :: rest);
              synth = (uu___131_8677.synth)
            }
let add_proof_ns: env -> name_prefix -> env =
  fun e  -> fun path  -> cons_proof_ns true e path
let rem_proof_ns: env -> name_prefix -> env =
  fun e  -> fun path  -> cons_proof_ns false e path
let push_proof_ns: env -> env =
  fun e  ->
    let uu___132_8696 = e in
    {
      solver = (uu___132_8696.solver);
      range = (uu___132_8696.range);
      curmodule = (uu___132_8696.curmodule);
      gamma = (uu___132_8696.gamma);
      gamma_cache = (uu___132_8696.gamma_cache);
      modules = (uu___132_8696.modules);
      expected_typ = (uu___132_8696.expected_typ);
      sigtab = (uu___132_8696.sigtab);
      is_pattern = (uu___132_8696.is_pattern);
      instantiate_imp = (uu___132_8696.instantiate_imp);
      effects = (uu___132_8696.effects);
      generalize = (uu___132_8696.generalize);
      letrecs = (uu___132_8696.letrecs);
      top_level = (uu___132_8696.top_level);
      check_uvars = (uu___132_8696.check_uvars);
      use_eq = (uu___132_8696.use_eq);
      is_iface = (uu___132_8696.is_iface);
      admit = (uu___132_8696.admit);
      lax = (uu___132_8696.lax);
      lax_universes = (uu___132_8696.lax_universes);
      type_of = (uu___132_8696.type_of);
      universe_of = (uu___132_8696.universe_of);
      use_bv_sorts = (uu___132_8696.use_bv_sorts);
      qname_and_index = (uu___132_8696.qname_and_index);
      proof_ns = ([] :: (e.proof_ns));
      synth = (uu___132_8696.synth)
    }
let pop_proof_ns: env -> env =
  fun e  ->
    match e.proof_ns with
    | [] -> failwith "empty proof_ns stack!"
    | uu____8705::rest ->
        let uu___133_8708 = e in
        {
          solver = (uu___133_8708.solver);
          range = (uu___133_8708.range);
          curmodule = (uu___133_8708.curmodule);
          gamma = (uu___133_8708.gamma);
          gamma_cache = (uu___133_8708.gamma_cache);
          modules = (uu___133_8708.modules);
          expected_typ = (uu___133_8708.expected_typ);
          sigtab = (uu___133_8708.sigtab);
          is_pattern = (uu___133_8708.is_pattern);
          instantiate_imp = (uu___133_8708.instantiate_imp);
          effects = (uu___133_8708.effects);
          generalize = (uu___133_8708.generalize);
          letrecs = (uu___133_8708.letrecs);
          top_level = (uu___133_8708.top_level);
          check_uvars = (uu___133_8708.check_uvars);
          use_eq = (uu___133_8708.use_eq);
          is_iface = (uu___133_8708.is_iface);
          admit = (uu___133_8708.admit);
          lax = (uu___133_8708.lax);
          lax_universes = (uu___133_8708.lax_universes);
          type_of = (uu___133_8708.type_of);
          universe_of = (uu___133_8708.universe_of);
          use_bv_sorts = (uu___133_8708.use_bv_sorts);
          qname_and_index = (uu___133_8708.qname_and_index);
          proof_ns = rest;
          synth = (uu___133_8708.synth)
        }
let get_proof_ns: env -> proof_namespace = fun e  -> e.proof_ns
let set_proof_ns: proof_namespace -> env -> env =
  fun ns  ->
    fun e  ->
      let uu___134_8718 = e in
      {
        solver = (uu___134_8718.solver);
        range = (uu___134_8718.range);
        curmodule = (uu___134_8718.curmodule);
        gamma = (uu___134_8718.gamma);
        gamma_cache = (uu___134_8718.gamma_cache);
        modules = (uu___134_8718.modules);
        expected_typ = (uu___134_8718.expected_typ);
        sigtab = (uu___134_8718.sigtab);
        is_pattern = (uu___134_8718.is_pattern);
        instantiate_imp = (uu___134_8718.instantiate_imp);
        effects = (uu___134_8718.effects);
        generalize = (uu___134_8718.generalize);
        letrecs = (uu___134_8718.letrecs);
        top_level = (uu___134_8718.top_level);
        check_uvars = (uu___134_8718.check_uvars);
        use_eq = (uu___134_8718.use_eq);
        is_iface = (uu___134_8718.is_iface);
        admit = (uu___134_8718.admit);
        lax = (uu___134_8718.lax);
        lax_universes = (uu___134_8718.lax_universes);
        type_of = (uu___134_8718.type_of);
        universe_of = (uu___134_8718.universe_of);
        use_bv_sorts = (uu___134_8718.use_bv_sorts);
        qname_and_index = (uu___134_8718.qname_and_index);
        proof_ns = ns;
        synth = (uu___134_8718.synth)
      }
let string_of_proof_ns: env -> Prims.string =
  fun env  ->
    let string_of_proof_ns' pns =
      let uu____8736 =
        FStar_List.map
          (fun fpns  ->
             let uu____8747 =
               let uu____8748 =
                 let uu____8749 =
                   FStar_List.map
                     (fun uu____8754  ->
                        match uu____8754 with
                        | (p,b) ->
                            Prims.strcat (if b then "+" else "-")
                              (FStar_String.concat "." p)) fpns in
                 FStar_String.concat "," uu____8749 in
               Prims.strcat uu____8748 "]" in
             Prims.strcat "[" uu____8747) pns in
      FStar_String.concat ";" uu____8736 in
    string_of_proof_ns' env.proof_ns
let dummy_solver: solver_t =
  {
    init = (fun uu____8763  -> ());
    push = (fun uu____8764  -> ());
    pop = (fun uu____8765  -> ());
    mark = (fun uu____8766  -> ());
    reset_mark = (fun uu____8767  -> ());
    commit_mark = (fun uu____8768  -> ());
    encode_modul = (fun uu____8769  -> fun uu____8770  -> ());
    encode_sig = (fun uu____8771  -> fun uu____8772  -> ());
    preprocess = (fun e  -> fun g  -> [(e, g)]);
    solve = (fun uu____8779  -> fun uu____8780  -> fun uu____8781  -> ());
    is_trivial = (fun uu____8785  -> fun uu____8786  -> false);
    finish = (fun uu____8787  -> ());
    refresh = (fun uu____8788  -> ())
  }