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
    match projectee with | Binding_var _0 -> true | uu____35 -> false
let __proj__Binding_var__item___0: binding -> FStar_Syntax_Syntax.bv =
  fun projectee  -> match projectee with | Binding_var _0 -> _0
let uu___is_Binding_lid: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_lid _0 -> true | uu____51 -> false
let __proj__Binding_lid__item___0:
  binding -> (FStar_Ident.lident* FStar_Syntax_Syntax.tscheme) =
  fun projectee  -> match projectee with | Binding_lid _0 -> _0
let uu___is_Binding_sig: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_sig _0 -> true | uu____74 -> false
let __proj__Binding_sig__item___0:
  binding -> (FStar_Ident.lident Prims.list* FStar_Syntax_Syntax.sigelt) =
  fun projectee  -> match projectee with | Binding_sig _0 -> _0
let uu___is_Binding_univ: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_univ _0 -> true | uu____97 -> false
let __proj__Binding_univ__item___0: binding -> FStar_Syntax_Syntax.univ_name
  = fun projectee  -> match projectee with | Binding_univ _0 -> _0
let uu___is_Binding_sig_inst: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_sig_inst _0 -> true | uu____115 -> false
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
    match projectee with | NoDelta  -> true | uu____144 -> false
let uu___is_Inlining: delta_level -> Prims.bool =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____149 -> false
let uu___is_Eager_unfolding_only: delta_level -> Prims.bool =
  fun projectee  ->
    match projectee with | Eager_unfolding_only  -> true | uu____154 -> false
let uu___is_Unfold: delta_level -> Prims.bool =
  fun projectee  ->
    match projectee with | Unfold _0 -> true | uu____160 -> false
let __proj__Unfold__item___0: delta_level -> FStar_Syntax_Syntax.delta_depth
  = fun projectee  -> match projectee with | Unfold _0 -> _0
let uu___is_UnfoldTac: delta_level -> Prims.bool =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____173 -> false
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
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term;
  is_native_tactic: FStar_Ident.lid -> Prims.bool;}
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
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;_} -> __fname__solver
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
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;_} -> __fname__range
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
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;_} -> __fname__curmodule
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
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;_} -> __fname__gamma
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
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;_} ->
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
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;_} -> __fname__modules
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
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;_} ->
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
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;_} -> __fname__sigtab
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
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;_} ->
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
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;_} ->
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
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;_} -> __fname__effects
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
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;_} ->
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
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;_} -> __fname__letrecs
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
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;_} -> __fname__top_level
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
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;_} ->
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
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;_} -> __fname__use_eq
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
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;_} -> __fname__is_iface
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
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;_} -> __fname__admit
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
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;_} -> __fname__lax
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
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;_} ->
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
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;_} -> __fname__type_of
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
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;_} ->
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
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;_} ->
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
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;_} ->
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
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;_} -> __fname__proof_ns
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
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;_} -> __fname__synth
let __proj__Mkenv__item__is_native_tactic:
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
      | (NoDelta ,uu____3489) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____3490,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) ->
          true
      | (Unfold uu____3491,FStar_Syntax_Syntax.Visible_default ) -> true
      | (Inlining ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____3492 -> false
let default_table_size: Prims.int = Prims.parse_int "200"
let new_sigtab uu____3504 = FStar_Util.smap_create default_table_size
let new_gamma_cache uu____3514 =
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
          let uu____3557 = new_gamma_cache () in
          let uu____3559 = new_sigtab () in
          let uu____3561 =
            let uu____3562 = FStar_Options.using_facts_from () in
            match uu____3562 with
            | Some ns ->
                let uu____3568 =
                  let uu____3573 =
                    FStar_List.map
                      (fun s  -> ((FStar_Ident.path_of_text s), true)) ns in
                  FStar_List.append uu____3573 [([], false)] in
                [uu____3568]
            | None  -> [[]] in
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
let sigtab: env -> FStar_Syntax_Syntax.sigelt FStar_Util.smap =
  fun env  -> env.sigtab
let gamma_cache: env -> cached_elt FStar_Util.smap =
  fun env  -> env.gamma_cache
let query_indices:
  (FStar_Ident.lident* Prims.int) Prims.list Prims.list FStar_ST.ref =
  FStar_Util.mk_ref [[]]
let push_query_indices: Prims.unit -> Prims.unit =
  fun uu____3658  ->
    let uu____3659 = FStar_ST.read query_indices in
    match uu____3659 with
    | [] -> failwith "Empty query indices!"
    | uu____3673 ->
        let uu____3678 =
          let uu____3683 =
            let uu____3687 = FStar_ST.read query_indices in
            FStar_List.hd uu____3687 in
          let uu____3701 = FStar_ST.read query_indices in uu____3683 ::
            uu____3701 in
        FStar_ST.write query_indices uu____3678
let pop_query_indices: Prims.unit -> Prims.unit =
  fun uu____3724  ->
    let uu____3725 = FStar_ST.read query_indices in
    match uu____3725 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.write query_indices tl1
let add_query_index: (FStar_Ident.lident* Prims.int) -> Prims.unit =
  fun uu____3762  ->
    match uu____3762 with
    | (l,n1) ->
        let uu____3767 = FStar_ST.read query_indices in
        (match uu____3767 with
         | hd1::tl1 -> FStar_ST.write query_indices (((l, n1) :: hd1) :: tl1)
         | uu____3801 -> failwith "Empty query indices")
let peek_query_indices:
  Prims.unit -> (FStar_Ident.lident* Prims.int) Prims.list =
  fun uu____3812  ->
    let uu____3813 = FStar_ST.read query_indices in FStar_List.hd uu____3813
let commit_query_index_mark: Prims.unit -> Prims.unit =
  fun uu____3830  ->
    let uu____3831 = FStar_ST.read query_indices in
    match uu____3831 with
    | hd1::uu____3843::tl1 -> FStar_ST.write query_indices (hd1 :: tl1)
    | uu____3870 -> failwith "Unmarked query index stack"
let stack: env Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let push_stack: env -> env =
  fun env  ->
    (let uu____1490 =
       let uu____1492 = FStar_ST.read stack in env :: uu____1492 in
     FStar_ST.write stack uu____1490);
    (let uu___114_1500 = env in
     let uu____1501 = FStar_Util.smap_copy (gamma_cache env) in
     let uu____1503 = FStar_Util.smap_copy (sigtab env) in
     {
       solver = (uu___114_1500.solver);
       range = (uu___114_1500.range);
       curmodule = (uu___114_1500.curmodule);
       gamma = (uu___114_1500.gamma);
       gamma_cache = uu____1501;
       modules = (uu___114_1500.modules);
       expected_typ = (uu___114_1500.expected_typ);
       sigtab = uu____1503;
       is_pattern = (uu___114_1500.is_pattern);
       instantiate_imp = (uu___114_1500.instantiate_imp);
       effects = (uu___114_1500.effects);
       generalize = (uu___114_1500.generalize);
       letrecs = (uu___114_1500.letrecs);
       top_level = (uu___114_1500.top_level);
       check_uvars = (uu___114_1500.check_uvars);
       use_eq = (uu___114_1500.use_eq);
       is_iface = (uu___114_1500.is_iface);
       admit = (uu___114_1500.admit);
       lax = (uu___114_1500.lax);
       lax_universes = (uu___114_1500.lax_universes);
       type_of = (uu___114_1500.type_of);
       universe_of = (uu___114_1500.universe_of);
       use_bv_sorts = (uu___114_1500.use_bv_sorts);
       qname_and_index = (uu___114_1500.qname_and_index);
       proof_ns = (uu___114_1500.proof_ns);
       synth = (uu___114_1500.synth);
       is_native_tactic = (uu___114_1500.is_native_tactic)
     })
let pop_stack: Prims.unit -> env =
  fun uu____3903  ->
    let uu____3904 = FStar_ST.read stack in
    match uu____3904 with
    | env::tl1 -> (FStar_ST.write stack tl1; env)
    | uu____3916 -> failwith "Impossible: Too many pops"
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
    (let uu____3955 = pop_stack () in ());
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
        let uu____3976 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____3988  ->
                  match uu____3988 with
                  | (m,uu____3992) -> FStar_Ident.lid_equals l m)) in
        (match uu____3976 with
         | None  ->
             let next = n1 + (Prims.parse_int "1") in
             (add_query_index (l, next);
              (let uu___115_1602 = env in
               {
                 solver = (uu___115_1602.solver);
                 range = (uu___115_1602.range);
                 curmodule = (uu___115_1602.curmodule);
                 gamma = (uu___115_1602.gamma);
                 gamma_cache = (uu___115_1602.gamma_cache);
                 modules = (uu___115_1602.modules);
                 expected_typ = (uu___115_1602.expected_typ);
                 sigtab = (uu___115_1602.sigtab);
                 is_pattern = (uu___115_1602.is_pattern);
                 instantiate_imp = (uu___115_1602.instantiate_imp);
                 effects = (uu___115_1602.effects);
                 generalize = (uu___115_1602.generalize);
                 letrecs = (uu___115_1602.letrecs);
                 top_level = (uu___115_1602.top_level);
                 check_uvars = (uu___115_1602.check_uvars);
                 use_eq = (uu___115_1602.use_eq);
                 is_iface = (uu___115_1602.is_iface);
                 admit = (uu___115_1602.admit);
                 lax = (uu___115_1602.lax);
                 lax_universes = (uu___115_1602.lax_universes);
                 type_of = (uu___115_1602.type_of);
                 universe_of = (uu___115_1602.universe_of);
                 use_bv_sorts = (uu___115_1602.use_bv_sorts);
                 qname_and_index = (Some (l, next));
                 proof_ns = (uu___115_1602.proof_ns);
                 synth = (uu___115_1602.synth);
                 is_native_tactic = (uu___115_1602.is_native_tactic)
               }))
         | Some (uu____4000,m) ->
             let next = m + (Prims.parse_int "1") in
             (add_query_index (l, next);
              (let uu___116_1611 = env in
               {
                 solver = (uu___116_1611.solver);
                 range = (uu___116_1611.range);
                 curmodule = (uu___116_1611.curmodule);
                 gamma = (uu___116_1611.gamma);
                 gamma_cache = (uu___116_1611.gamma_cache);
                 modules = (uu___116_1611.modules);
                 expected_typ = (uu___116_1611.expected_typ);
                 sigtab = (uu___116_1611.sigtab);
                 is_pattern = (uu___116_1611.is_pattern);
                 instantiate_imp = (uu___116_1611.instantiate_imp);
                 effects = (uu___116_1611.effects);
                 generalize = (uu___116_1611.generalize);
                 letrecs = (uu___116_1611.letrecs);
                 top_level = (uu___116_1611.top_level);
                 check_uvars = (uu___116_1611.check_uvars);
                 use_eq = (uu___116_1611.use_eq);
                 is_iface = (uu___116_1611.is_iface);
                 admit = (uu___116_1611.admit);
                 lax = (uu___116_1611.lax);
                 lax_universes = (uu___116_1611.lax_universes);
                 type_of = (uu___116_1611.type_of);
                 universe_of = (uu___116_1611.universe_of);
                 use_bv_sorts = (uu___116_1611.use_bv_sorts);
                 qname_and_index = (Some (l, next));
                 proof_ns = (uu___116_1611.proof_ns);
                 synth = (uu___116_1611.synth);
                 is_native_tactic = (uu___116_1611.is_native_tactic)
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
        (let uu___117_1631 = e in
         {
           solver = (uu___117_1631.solver);
           range = r;
           curmodule = (uu___117_1631.curmodule);
           gamma = (uu___117_1631.gamma);
           gamma_cache = (uu___117_1631.gamma_cache);
           modules = (uu___117_1631.modules);
           expected_typ = (uu___117_1631.expected_typ);
           sigtab = (uu___117_1631.sigtab);
           is_pattern = (uu___117_1631.is_pattern);
           instantiate_imp = (uu___117_1631.instantiate_imp);
           effects = (uu___117_1631.effects);
           generalize = (uu___117_1631.generalize);
           letrecs = (uu___117_1631.letrecs);
           top_level = (uu___117_1631.top_level);
           check_uvars = (uu___117_1631.check_uvars);
           use_eq = (uu___117_1631.use_eq);
           is_iface = (uu___117_1631.is_iface);
           admit = (uu___117_1631.admit);
           lax = (uu___117_1631.lax);
           lax_universes = (uu___117_1631.lax_universes);
           type_of = (uu___117_1631.type_of);
           universe_of = (uu___117_1631.universe_of);
           use_bv_sorts = (uu___117_1631.use_bv_sorts);
           qname_and_index = (uu___117_1631.qname_and_index);
           proof_ns = (uu___117_1631.proof_ns);
           synth = (uu___117_1631.synth);
           is_native_tactic = (uu___117_1631.is_native_tactic)
         })
let get_range: env -> FStar_Range.range = fun e  -> e.range
let modules: env -> FStar_Syntax_Syntax.modul Prims.list =
  fun env  -> env.modules
let current_module: env -> FStar_Ident.lident = fun env  -> env.curmodule
let set_current_module: env -> FStar_Ident.lident -> env =
  fun env  ->
    fun lid  ->
      let uu___118_1653 = env in
      {
        solver = (uu___118_1653.solver);
        range = (uu___118_1653.range);
        curmodule = lid;
        gamma = (uu___118_1653.gamma);
        gamma_cache = (uu___118_1653.gamma_cache);
        modules = (uu___118_1653.modules);
        expected_typ = (uu___118_1653.expected_typ);
        sigtab = (uu___118_1653.sigtab);
        is_pattern = (uu___118_1653.is_pattern);
        instantiate_imp = (uu___118_1653.instantiate_imp);
        effects = (uu___118_1653.effects);
        generalize = (uu___118_1653.generalize);
        letrecs = (uu___118_1653.letrecs);
        top_level = (uu___118_1653.top_level);
        check_uvars = (uu___118_1653.check_uvars);
        use_eq = (uu___118_1653.use_eq);
        is_iface = (uu___118_1653.is_iface);
        admit = (uu___118_1653.admit);
        lax = (uu___118_1653.lax);
        lax_universes = (uu___118_1653.lax_universes);
        type_of = (uu___118_1653.type_of);
        universe_of = (uu___118_1653.universe_of);
        use_bv_sorts = (uu___118_1653.use_bv_sorts);
        qname_and_index = (uu___118_1653.qname_and_index);
        proof_ns = (uu___118_1653.proof_ns);
        synth = (uu___118_1653.synth);
        is_native_tactic = (uu___118_1653.is_native_tactic)
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
    let uu____4076 = FStar_Syntax_Print.bv_to_string v1 in
    FStar_Util.format1 "Variable \"%s\" not found" uu____4076
let new_u_univ: Prims.unit -> FStar_Syntax_Syntax.universe =
  fun uu____4080  ->
    let uu____4081 = FStar_Syntax_Unionfind.univ_fresh () in
    FStar_Syntax_Syntax.U_unif uu____4081
let inst_tscheme_with:
  FStar_Syntax_Syntax.tscheme ->
    FStar_Syntax_Syntax.universes ->
      (FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.term)
  =
  fun ts  ->
    fun us  ->
      match (ts, us) with
      | (([],t),[]) -> ([], t)
      | ((formals,t),uu____4105) ->
          let n1 = (FStar_List.length formals) - (Prims.parse_int "1") in
          let vs =
            FStar_All.pipe_right us
              (FStar_List.mapi
                 (fun i  -> fun u  -> FStar_Syntax_Syntax.UN ((n1 - i), u))) in
          let uu____4124 = FStar_Syntax_Subst.subst vs t in (us, uu____4124)
let inst_tscheme:
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.term)
  =
  fun uu___102_1735  ->
    match uu___102_1735 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____4144  -> new_u_univ ())) in
        inst_tscheme_with (us, t) us'
let inst_tscheme_with_range:
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.term)
  =
  fun r  ->
    fun t  ->
      let uu____4156 = inst_tscheme t in
      match uu____4156 with
      | (us,t1) ->
          let uu____4163 = FStar_Syntax_Subst.set_use_range r t1 in
          (us, uu____4163)
let inst_effect_fun_with:
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
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____4197 =
                         let uu____4198 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1) in
                         let uu____4203 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts) in
                         let uu____4208 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname in
                         let uu____4209 = FStar_Syntax_Print.term_to_string t in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____4198 uu____4203 uu____4208 uu____4209 in
                       failwith uu____4197)
                    else ();
                    (let uu____4211 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts in
                     snd uu____4211))
               | uu____4215 ->
                   let uu____4216 =
                     let uu____4217 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____4217 in
                   failwith uu____4216)
type tri =
  | Yes
  | No
  | Maybe
let uu___is_Yes: tri -> Prims.bool =
  fun projectee  -> match projectee with | Yes  -> true | uu____4222 -> false
let uu___is_No: tri -> Prims.bool =
  fun projectee  -> match projectee with | No  -> true | uu____4227 -> false
let uu___is_Maybe: tri -> Prims.bool =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____4232 -> false
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
             | ([],uu____4260) -> Maybe
             | (uu____4264,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____4276 -> No in
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
          let uu____4338 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str in
          match uu____4338 with
          | None  ->
              FStar_Util.find_map env.gamma
                (fun uu___103_1964  ->
                   match uu___103_1964 with
                   | Binding_lid (l,t) ->
                       if FStar_Ident.lid_equals lid l
                       then
                         let uu____4382 =
                           let uu____4392 =
                             let uu____4400 = inst_tscheme t in
                             FStar_Util.Inl uu____4400 in
                           (uu____4392, (FStar_Ident.range_of_lid l)) in
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
                                     FStar_Syntax_Syntax.sigmeta = uu____4439;_})
                       ->
                       FStar_Util.find_map ses
                         (fun se  ->
                            let uu____4448 =
                              FStar_All.pipe_right
                                (FStar_Syntax_Util.lids_of_sigelt se)
                                (FStar_Util.for_some
                                   (FStar_Ident.lid_equals lid)) in
                            if uu____4448
                            then
                              cache
                                ((FStar_Util.Inr (se, None)),
                                  (FStar_Syntax_Util.range_of_sigelt se))
                            else None)
                   | Binding_sig (lids,s) ->
                       let maybe_cache t =
                         match s.FStar_Syntax_Syntax.sigel with
                         | FStar_Syntax_Syntax.Sig_declare_typ uu____4475 ->
                             Some t
                         | uu____4479 -> cache t in
                       let uu____4480 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids in
                       (match uu____4480 with
                        | None  -> None
                        | Some l ->
                            maybe_cache
                              ((FStar_Util.Inr (s, None)),
                                (FStar_Ident.range_of_lid l)))
                   | Binding_sig_inst (lids,s,us) ->
                       let uu____4520 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids in
                       (match uu____4520 with
                        | None  -> None
                        | Some l ->
                            Some
                              ((FStar_Util.Inr (s, (Some us))),
                                (FStar_Ident.range_of_lid l)))
                   | uu____4564 -> None)
          | se -> se
        else None in
      if FStar_Util.is_some found
      then found
      else
        (let uu____4606 =
           (cur_mod <> Yes) || (has_interface env env.curmodule) in
         if uu____4606
         then
           let uu____4617 = find_in_sigtab env lid in
           match uu____4617 with
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
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____4683) ->
          add_sigelts env ses
      | uu____4688 ->
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
            | uu____4697 -> ()))
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
        (fun uu___104_2322  ->
           match uu___104_2322 with
           | Binding_var id when FStar_Syntax_Syntax.bv_eq id bv ->
               Some
                 ((id.FStar_Syntax_Syntax.sort),
                   ((id.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____4730 -> None)
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
          ((uu____4753,lb::[]),uu____4755,uu____4756) ->
          let uu____4765 =
            let uu____4770 =
              inst_tscheme
                ((lb.FStar_Syntax_Syntax.lbunivs),
                  (lb.FStar_Syntax_Syntax.lbtyp)) in
            let uu____4776 =
              FStar_Syntax_Syntax.range_of_lbname
                lb.FStar_Syntax_Syntax.lbname in
            (uu____4770, uu____4776) in
          Some uu____4765
      | FStar_Syntax_Syntax.Sig_let ((uu____4783,lbs),uu____4785,uu____4786)
          ->
          FStar_Util.find_map lbs
            (fun lb  ->
               match lb.FStar_Syntax_Syntax.lbname with
               | FStar_Util.Inl uu____4806 -> failwith "impossible"
               | FStar_Util.Inr fv ->
                   let uu____4813 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                   if uu____4813
                   then
                     let uu____4819 =
                       let uu____4824 =
                         inst_tscheme
                           ((lb.FStar_Syntax_Syntax.lbunivs),
                             (lb.FStar_Syntax_Syntax.lbtyp)) in
                       let uu____4830 = FStar_Syntax_Syntax.range_of_fv fv in
                       (uu____4824, uu____4830) in
                     Some uu____4819
                   else None)
      | uu____4842 -> None
let effect_signature:
  FStar_Syntax_Syntax.sigelt ->
    ((FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.term)*
      FStar_Range.range) option
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne ->
        let uu____4862 =
          let uu____4867 =
            let uu____4870 =
              let uu____4871 =
                let uu____4874 =
                  FStar_Syntax_Syntax.mk_Total
                    ne.FStar_Syntax_Syntax.signature in
                FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                  uu____4874 in
              ((ne.FStar_Syntax_Syntax.univs), uu____4871) in
            inst_tscheme uu____4870 in
          (uu____4867, (se.FStar_Syntax_Syntax.sigrng)) in
        Some uu____4862
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,us,binders,uu____4888,uu____4889) ->
        let uu____4892 =
          let uu____4897 =
            let uu____4900 =
              let uu____4901 =
                let uu____4904 =
                  FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff in
                FStar_Syntax_Util.arrow binders uu____4904 in
              (us, uu____4901) in
            inst_tscheme uu____4900 in
          (uu____4897, (se.FStar_Syntax_Syntax.sigrng)) in
        Some uu____4892
    | uu____4915 -> None
let try_lookup_lid_aux:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes*
        (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax)* FStar_Range.range) option
  =
  fun env  ->
    fun lid  ->
      let mapper uu____4952 =
        match uu____4952 with
        | (lr,rng) ->
            (match lr with
             | FStar_Util.Inl t -> Some (t, rng)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_datacon
                      (uu____5002,uvs,t,uu____5005,uu____5006,uu____5007);
                    FStar_Syntax_Syntax.sigrng = uu____5008;
                    FStar_Syntax_Syntax.sigquals = uu____5009;
                    FStar_Syntax_Syntax.sigmeta = uu____5010;_},None
                  )
                 ->
                 let uu____5020 =
                   let uu____5025 = inst_tscheme (uvs, t) in
                   (uu____5025, rng) in
                 Some uu____5020
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                    FStar_Syntax_Syntax.sigrng = uu____5037;
                    FStar_Syntax_Syntax.sigquals = qs;
                    FStar_Syntax_Syntax.sigmeta = uu____5039;_},None
                  )
                 ->
                 let uu____5047 =
                   let uu____5048 = in_cur_mod env l in uu____5048 = Yes in
                 if uu____5047
                 then
                   let uu____5054 =
                     (FStar_All.pipe_right qs
                        (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                       || env.is_iface in
                   (if uu____5054
                    then
                      let uu____5061 =
                        let uu____5066 = inst_tscheme (uvs, t) in
                        (uu____5066, rng) in
                      Some uu____5061
                    else None)
                 else
                   (let uu____5081 =
                      let uu____5086 = inst_tscheme (uvs, t) in
                      (uu____5086, rng) in
                    Some uu____5081)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____5099,uu____5100);
                    FStar_Syntax_Syntax.sigrng = uu____5101;
                    FStar_Syntax_Syntax.sigquals = uu____5102;
                    FStar_Syntax_Syntax.sigmeta = uu____5103;_},None
                  )
                 ->
                 (match tps with
                  | [] ->
                      let uu____5122 =
                        let uu____5127 = inst_tscheme (uvs, k) in
                        (uu____5127, rng) in
                      Some uu____5122
                  | uu____5136 ->
                      let uu____5137 =
                        let uu____5142 =
                          let uu____5145 =
                            let uu____5146 =
                              let uu____5149 = FStar_Syntax_Syntax.mk_Total k in
                              FStar_Syntax_Util.flat_arrow tps uu____5149 in
                            (uvs, uu____5146) in
                          inst_tscheme uu____5145 in
                        (uu____5142, rng) in
                      Some uu____5137)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____5164,uu____5165);
                    FStar_Syntax_Syntax.sigrng = uu____5166;
                    FStar_Syntax_Syntax.sigquals = uu____5167;
                    FStar_Syntax_Syntax.sigmeta = uu____5168;_},Some
                  us)
                 ->
                 (match tps with
                  | [] ->
                      let uu____5188 =
                        let uu____5193 = inst_tscheme_with (uvs, k) us in
                        (uu____5193, rng) in
                      Some uu____5188
                  | uu____5202 ->
                      let uu____5203 =
                        let uu____5208 =
                          let uu____5211 =
                            let uu____5212 =
                              let uu____5215 = FStar_Syntax_Syntax.mk_Total k in
                              FStar_Syntax_Util.flat_arrow tps uu____5215 in
                            (uvs, uu____5212) in
                          inst_tscheme_with uu____5211 us in
                        (uu____5208, rng) in
                      Some uu____5203)
             | FStar_Util.Inr se ->
                 let uu____5235 =
                   match se with
                   | ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let uu____5246;
                        FStar_Syntax_Syntax.sigrng = uu____5247;
                        FStar_Syntax_Syntax.sigquals = uu____5248;
                        FStar_Syntax_Syntax.sigmeta = uu____5249;_},None
                      ) -> lookup_type_of_let (fst se) lid
                   | uu____5258 -> effect_signature (fst se) in
                 FStar_All.pipe_right uu____5235
                   (FStar_Util.map_option
                      (fun uu____5281  ->
                         match uu____5281 with | (us_t,rng1) -> (us_t, rng1)))) in
      let uu____5298 =
        let uu____5304 = lookup_qname env lid in
        FStar_Util.bind_opt uu____5304 mapper in
      match uu____5298 with
      | Some ((us,t),r) ->
          Some
            ((us,
               (let uu___119_2961 = t in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___119_2961.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___119_2961.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid);
                  FStar_Syntax_Syntax.vars =
                    (uu___119_2961.FStar_Syntax_Syntax.vars)
                })), r)
      | None  -> None
let lid_exists: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____5379 = lookup_qname env l in
      match uu____5379 with | None  -> false | Some uu____5399 -> true
let lookup_bv:
  env ->
    FStar_Syntax_Syntax.bv -> (FStar_Syntax_Syntax.typ* FStar_Range.range)
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv in
      let uu____5429 = try_lookup_bv env bv in
      match uu____5429 with
      | None  ->
          let uu____5437 =
            let uu____5438 =
              let uu____5441 = variable_not_found bv in (uu____5441, bvr) in
            FStar_Errors.Error uu____5438 in
          raise uu____5437
      | Some (t,r) ->
          let uu____5448 = FStar_Syntax_Subst.set_use_range bvr t in
          let uu____5449 = FStar_Range.set_use_range r bvr in
          (uu____5448, uu____5449)
let try_lookup_lid:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.typ)*
        FStar_Range.range) option
  =
  fun env  ->
    fun l  ->
      let uu____5463 = try_lookup_lid_aux env l in
      match uu____5463 with
      | None  -> None
      | Some ((us,t),r) ->
          let use_range = FStar_Ident.range_of_lid l in
          let r1 = FStar_Range.set_use_range r use_range in
          let uu____5505 =
            let uu____5510 =
              let uu____5513 = FStar_Syntax_Subst.set_use_range use_range t in
              (us, uu____5513) in
            (uu____5510, r1) in
          Some uu____5505
let lookup_lid:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.typ)*
        FStar_Range.range)
  =
  fun env  ->
    fun l  ->
      let uu____5532 = try_lookup_lid env l in
      match uu____5532 with
      | None  ->
          let uu____5546 =
            let uu____5547 =
              let uu____5550 = name_not_found l in
              (uu____5550, (FStar_Ident.range_of_lid l)) in
            FStar_Errors.Error uu____5547 in
          raise uu____5546
      | Some v1 -> v1
let lookup_univ: env -> FStar_Syntax_Syntax.univ_name -> Prims.bool =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___105_3178  ->
              match uu___105_3178 with
              | Binding_univ y -> x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____5575 -> false) env.gamma) FStar_Option.isSome
let try_lookup_val_decl:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme* FStar_Syntax_Syntax.qualifier Prims.list)
        option
  =
  fun env  ->
    fun lid  ->
      let uu____5588 = lookup_qname env lid in
      match uu____5588 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____5603,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____5606;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____5608;_},None
            ),uu____5609)
          ->
          let uu____5633 =
            let uu____5639 =
              let uu____5642 =
                FStar_Syntax_Subst.set_use_range
                  (FStar_Ident.range_of_lid lid) t in
              (uvs, uu____5642) in
            (uu____5639, q) in
          Some uu____5633
      | uu____5651 -> None
let lookup_val_decl:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun lid  ->
      let uu____5675 = lookup_qname env lid in
      match uu____5675 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____5688,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____5691;
              FStar_Syntax_Syntax.sigquals = uu____5692;
              FStar_Syntax_Syntax.sigmeta = uu____5693;_},None
            ),uu____5694)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____5718 ->
          let uu____5729 =
            let uu____5730 =
              let uu____5733 = name_not_found lid in
              (uu____5733, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____5730 in
          raise uu____5729
let lookup_datacon:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun lid  ->
      let uu____5746 = lookup_qname env lid in
      match uu____5746 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____5759,uvs,t,uu____5762,uu____5763,uu____5764);
              FStar_Syntax_Syntax.sigrng = uu____5765;
              FStar_Syntax_Syntax.sigquals = uu____5766;
              FStar_Syntax_Syntax.sigmeta = uu____5767;_},None
            ),uu____5768)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____5794 ->
          let uu____5805 =
            let uu____5806 =
              let uu____5809 = name_not_found lid in
              (uu____5809, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____5806 in
          raise uu____5805
let datacons_of_typ:
  env -> FStar_Ident.lident -> (Prims.bool* FStar_Ident.lident Prims.list) =
  fun env  ->
    fun lid  ->
      let uu____5823 = lookup_qname env lid in
      match uu____5823 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____5837,uu____5838,uu____5839,uu____5840,uu____5841,dcs);
              FStar_Syntax_Syntax.sigrng = uu____5843;
              FStar_Syntax_Syntax.sigquals = uu____5844;
              FStar_Syntax_Syntax.sigmeta = uu____5845;_},uu____5846),uu____5847)
          -> (true, dcs)
      | uu____5877 -> (false, [])
let typ_of_datacon: env -> FStar_Ident.lident -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      let uu____5897 = lookup_qname env lid in
      match uu____5897 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____5908,uu____5909,uu____5910,l,uu____5912,uu____5913);
              FStar_Syntax_Syntax.sigrng = uu____5914;
              FStar_Syntax_Syntax.sigquals = uu____5915;
              FStar_Syntax_Syntax.sigmeta = uu____5916;_},uu____5917),uu____5918)
          -> l
      | uu____5945 ->
          let uu____5956 =
            let uu____5957 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format1 "Not a datacon: %s" uu____5957 in
          failwith uu____5956
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
        let uu____5984 = lookup_qname env lid in
        match uu____5984 with
        | Some (FStar_Util.Inr (se,None ),uu____5999) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_let
                 ((uu____6025,lbs),uu____6027,uu____6028) when
                 visible se.FStar_Syntax_Syntax.sigquals ->
                 FStar_Util.find_map lbs
                   (fun lb  ->
                      let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                      let uu____6045 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                      if uu____6045
                      then
                        Some
                          ((lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbdef))
                      else None)
             | uu____6066 -> None)
        | uu____6069 -> None
let try_lookup_effect_lid:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.typ option =
  fun env  ->
    fun ftv  ->
      let uu____6092 = lookup_qname env ftv in
      match uu____6092 with
      | Some (FStar_Util.Inr (se,None ),uu____6105) ->
          let uu____6128 = effect_signature se in
          (match uu____6128 with
           | None  -> None
           | Some ((uu____6139,t),r) ->
               let uu____6148 =
                 FStar_Syntax_Subst.set_use_range
                   (FStar_Ident.range_of_lid ftv) t in
               Some uu____6148)
      | uu____6149 -> None
let lookup_effect_lid: env -> FStar_Ident.lident -> FStar_Syntax_Syntax.typ =
  fun env  ->
    fun ftv  ->
      let uu____6168 = try_lookup_effect_lid env ftv in
      match uu____6168 with
      | None  ->
          let uu____6170 =
            let uu____6171 =
              let uu____6174 = name_not_found ftv in
              (uu____6174, (FStar_Ident.range_of_lid ftv)) in
            FStar_Errors.Error uu____6171 in
          raise uu____6170
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
        let uu____6191 = lookup_qname env lid0 in
        match uu____6191 with
        | Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____6209);
                FStar_Syntax_Syntax.sigrng = uu____6210;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____6212;_},None
              ),uu____6213)
            ->
            let lid1 =
              let uu____6240 =
                FStar_Range.set_use_range (FStar_Ident.range_of_lid lid)
                  (FStar_Ident.range_of_lid lid0) in
              FStar_Ident.set_lid_range lid uu____6240 in
            let uu____6241 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___106_3848  ->
                      match uu___106_3848 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____6244 -> false)) in
            if uu____6241
            then None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____6261 =
                      let uu____6262 = FStar_Syntax_Print.lid_to_string lid1 in
                      let uu____6263 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int in
                      FStar_Util.format2
                        "Unexpected instantiation of effect %s with %s universes"
                        uu____6262 uu____6263 in
                    failwith uu____6261) in
               match (binders, univs1) with
               | ([],uu____6271) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____6280,uu____6281::uu____6282::uu____6283) ->
                   let uu____6286 =
                     let uu____6287 = FStar_Syntax_Print.lid_to_string lid1 in
                     let uu____6288 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1) in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____6287 uu____6288 in
                   failwith uu____6286
               | uu____6296 ->
                   let uu____6299 =
                     let uu____6302 =
                       let uu____6303 = FStar_Syntax_Util.arrow binders c in
                       (univs1, uu____6303) in
                     inst_tscheme_with uu____6302 insts in
                   (match uu____6299 with
                    | (uu____6311,t) ->
                        let t1 =
                          FStar_Syntax_Subst.set_use_range
                            (FStar_Ident.range_of_lid lid1) t in
                        let uu____6314 =
                          let uu____6315 = FStar_Syntax_Subst.compress t1 in
                          uu____6315.FStar_Syntax_Syntax.n in
                        (match uu____6314 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             Some (binders1, c1)
                         | uu____6345 -> failwith "Impossible")))
        | uu____6349 -> None
let norm_eff_name: env -> FStar_Ident.lident -> FStar_Ident.lident =
  let cache = FStar_Util.smap_create (Prims.parse_int "20") in
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____6377 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1 in
        match uu____6377 with
        | None  -> None
        | Some (uu____6384,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c in
            let uu____6389 = find1 l2 in
            (match uu____6389 with | None  -> Some l2 | Some l' -> Some l') in
      let res =
        let uu____6394 = FStar_Util.smap_try_find cache l.FStar_Ident.str in
        match uu____6394 with
        | Some l1 -> l1
        | None  ->
            let uu____6397 = find1 l in
            (match uu____6397 with
             | None  -> l
             | Some m -> (FStar_Util.smap_add cache l.FStar_Ident.str m; m)) in
      FStar_Ident.set_lid_range res (FStar_Ident.range_of_lid l)
let lookup_effect_quals:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l in
      let uu____6411 = lookup_qname env l1 in
      match uu____6411 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____6423;
              FStar_Syntax_Syntax.sigrng = uu____6424;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____6426;_},uu____6427),uu____6428)
          -> q
      | uu____6453 -> []
let lookup_projector:
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail uu____6479 =
          let uu____6480 =
            let uu____6481 = FStar_Util.string_of_int i in
            let uu____6482 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____6481 uu____6482 in
          failwith uu____6480 in
        let uu____6483 = lookup_datacon env lid in
        match uu____6483 with
        | (uu____6486,t) ->
            let uu____6488 =
              let uu____6489 = FStar_Syntax_Subst.compress t in
              uu____6489.FStar_Syntax_Syntax.n in
            (match uu____6488 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____6493) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail ()
                 else
                   (let b = FStar_List.nth binders i in
                    let uu____6516 =
                      FStar_Syntax_Util.mk_field_projector_name lid (fst b) i in
                    FStar_All.pipe_right uu____6516 FStar_Pervasives.fst)
             | uu____6521 -> fail ())
let is_projector: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____6530 = lookup_qname env l in
      match uu____6530 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____6541,uu____6542,uu____6543);
              FStar_Syntax_Syntax.sigrng = uu____6544;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____6546;_},uu____6547),uu____6548)
          ->
          FStar_Util.for_some
            (fun uu___107_4178  ->
               match uu___107_4178 with
               | FStar_Syntax_Syntax.Projector uu____4179 -> true
               | uu____4182 -> false) quals
      | uu____4183 -> false
let is_datacon: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____6597 = lookup_qname env lid in
      match uu____6597 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____6608,uu____6609,uu____6610,uu____6611,uu____6612,uu____6613);
              FStar_Syntax_Syntax.sigrng = uu____6614;
              FStar_Syntax_Syntax.sigquals = uu____6615;
              FStar_Syntax_Syntax.sigmeta = uu____6616;_},uu____6617),uu____6618)
          -> true
      | uu____6645 -> false
let is_record: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____6664 = lookup_qname env lid in
      match uu____6664 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____6675,uu____6676,uu____6677,uu____6678,uu____6679,uu____6680);
              FStar_Syntax_Syntax.sigrng = uu____6681;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____6683;_},uu____6684),uu____6685)
          ->
          FStar_Util.for_some
            (fun uu___108_4319  ->
               match uu___108_4319 with
               | FStar_Syntax_Syntax.RecordType uu____4320 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____4325 -> true
               | uu____4330 -> false) quals
      | uu____4331 -> false
let is_action: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____6745 = lookup_qname env lid in
      match uu____6745 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                (uu____6756,uu____6757,uu____6758);
              FStar_Syntax_Syntax.sigrng = uu____6759;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____6761;_},uu____6762),uu____6763)
          ->
          FStar_Util.for_some
            (fun uu___109_4397  ->
               match uu___109_4397 with
               | FStar_Syntax_Syntax.Action uu____4398 -> true
               | uu____4399 -> false) quals
      | uu____4400 -> false
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
      let uu____6816 =
        let uu____6817 = FStar_Syntax_Util.un_uinst head1 in
        uu____6817.FStar_Syntax_Syntax.n in
      match uu____6816 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          fv.FStar_Syntax_Syntax.fv_delta =
            FStar_Syntax_Syntax.Delta_equational
      | uu____6821 -> false
let is_type_constructor: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let mapper x =
        match fst x with
        | FStar_Util.Inl uu____6861 -> Some false
        | FStar_Util.Inr (se,uu____6870) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____6879 ->
                 Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____6883 -> Some true
             | uu____6892 -> Some false) in
      let uu____6893 =
        let uu____6895 = lookup_qname env lid in
        FStar_Util.bind_opt uu____6895 mapper in
      match uu____6893 with | Some b -> b | None  -> false
let num_inductive_ty_params: env -> FStar_Ident.lident -> Prims.int =
  fun env  ->
    fun lid  ->
      let uu____6924 = lookup_qname env lid in
      match uu____6924 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____6935,uu____6936,tps,uu____6938,uu____6939,uu____6940);
              FStar_Syntax_Syntax.sigrng = uu____6941;
              FStar_Syntax_Syntax.sigquals = uu____6942;
              FStar_Syntax_Syntax.sigmeta = uu____6943;_},uu____6944),uu____6945)
          -> FStar_List.length tps
      | uu____6978 ->
          let uu____6989 =
            let uu____6990 =
              let uu____6993 = name_not_found lid in
              (uu____6993, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____6990 in
          raise uu____6989
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
           (fun uu____7017  ->
              match uu____7017 with
              | (d,uu____7022) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
let get_effect_decl:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl =
  fun env  ->
    fun l  ->
      let uu____7033 = effect_decl_opt env l in
      match uu____7033 with
      | None  ->
          let uu____7041 =
            let uu____7042 =
              let uu____7045 = name_not_found l in
              (uu____7045, (FStar_Ident.range_of_lid l)) in
            FStar_Errors.Error uu____7042 in
          raise uu____7041
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
            (let uu____7091 =
               FStar_All.pipe_right (env.effects).joins
                 (FStar_Util.find_opt
                    (fun uu____7115  ->
                       match uu____7115 with
                       | (m1,m2,uu____7123,uu____7124,uu____7125) ->
                           (FStar_Ident.lid_equals l1 m1) &&
                             (FStar_Ident.lid_equals l2 m2))) in
             match uu____7091 with
             | None  ->
                 let uu____7134 =
                   let uu____7135 =
                     let uu____7138 =
                       let uu____7139 = FStar_Syntax_Print.lid_to_string l1 in
                       let uu____7140 = FStar_Syntax_Print.lid_to_string l2 in
                       FStar_Util.format2
                         "Effects %s and %s cannot be composed" uu____7139
                         uu____7140 in
                     (uu____7138, (env.range)) in
                   FStar_Errors.Error uu____7135 in
                 raise uu____7134
             | Some (uu____7144,uu____7145,m3,j1,j2) -> (m3, j1, j2))
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
  let uu____7198 =
    FStar_All.pipe_right decls
      (FStar_Util.find_opt
         (fun uu____7210  ->
            match uu____7210 with
            | (d,uu____7214) ->
                FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m)) in
  match uu____7198 with
  | None  ->
      let uu____7221 =
        FStar_Util.format1 "Impossible: declaration for monad %s not found"
          m.FStar_Ident.str in
      failwith uu____7221
  | Some (md,_q) ->
      let uu____7230 =
        inst_tscheme
          ((md.FStar_Syntax_Syntax.univs),
            (md.FStar_Syntax_Syntax.signature)) in
      (match uu____7230 with
       | (uu____7237,s) ->
           let s1 = FStar_Syntax_Subst.compress s in
           (match ((md.FStar_Syntax_Syntax.binders),
                    (s1.FStar_Syntax_Syntax.n))
            with
            | ([],FStar_Syntax_Syntax.Tm_arrow
               ((a,uu____7245)::(wp,uu____7247)::[],c)) when
                FStar_Syntax_Syntax.is_teff (FStar_Syntax_Util.comp_result c)
                -> (a, (wp.FStar_Syntax_Syntax.sort))
            | uu____7269 -> failwith "Impossible"))
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
                 let uu____7311 = get_range env in
                 let uu____7312 =
                   let uu____7315 =
                     let uu____7316 =
                       let uu____7326 =
                         let uu____7328 = FStar_Syntax_Syntax.as_arg res_t in
                         [uu____7328] in
                       (null_wp, uu____7326) in
                     FStar_Syntax_Syntax.Tm_app uu____7316 in
                   FStar_Syntax_Syntax.mk uu____7315 in
                 uu____7312 None uu____7311 in
               let uu____7338 =
                 let uu____7339 =
                   let uu____7345 = FStar_Syntax_Syntax.as_arg null_wp_res in
                   [uu____7345] in
                 {
                   FStar_Syntax_Syntax.comp_univs = [res_u];
                   FStar_Syntax_Syntax.effect_name = eff_name1;
                   FStar_Syntax_Syntax.result_typ = res_t;
                   FStar_Syntax_Syntax.effect_args = uu____7339;
                   FStar_Syntax_Syntax.flags = []
                 } in
               FStar_Syntax_Syntax.mk_Comp uu____7338)
let build_lattice: env -> FStar_Syntax_Syntax.sigelt -> env =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___120_4961 = env.effects in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___120_4961.order);
              joins = (uu___120_4961.joins)
            } in
          let uu___121_4966 = env in
          {
            solver = (uu___121_4966.solver);
            range = (uu___121_4966.range);
            curmodule = (uu___121_4966.curmodule);
            gamma = (uu___121_4966.gamma);
            gamma_cache = (uu___121_4966.gamma_cache);
            modules = (uu___121_4966.modules);
            expected_typ = (uu___121_4966.expected_typ);
            sigtab = (uu___121_4966.sigtab);
            is_pattern = (uu___121_4966.is_pattern);
            instantiate_imp = (uu___121_4966.instantiate_imp);
            effects;
            generalize = (uu___121_4966.generalize);
            letrecs = (uu___121_4966.letrecs);
            top_level = (uu___121_4966.top_level);
            check_uvars = (uu___121_4966.check_uvars);
            use_eq = (uu___121_4966.use_eq);
            is_iface = (uu___121_4966.is_iface);
            admit = (uu___121_4966.admit);
            lax = (uu___121_4966.lax);
            lax_universes = (uu___121_4966.lax_universes);
            type_of = (uu___121_4966.type_of);
            universe_of = (uu___121_4966.universe_of);
            use_bv_sorts = (uu___121_4966.use_bv_sorts);
            qname_and_index = (uu___121_4966.qname_and_index);
            proof_ns = (uu___121_4966.proof_ns);
            synth = (uu___121_4966.synth);
            is_native_tactic = (uu___121_4966.is_native_tactic)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp r wp1 =
                let uu____7378 = (e1.mlift).mlift_wp r wp1 in
                (e2.mlift).mlift_wp r uu____7378 in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (Some l1,Some l2) ->
                    Some
                      ((fun t  ->
                          fun wp  ->
                            fun e  ->
                              let uu____7457 = (e1.mlift).mlift_wp t wp in
                              let uu____7458 = l1 t wp e in
                              l2 t uu____7457 uu____7458))
                | uu____7459 -> None in
              { mlift_wp; mlift_term } in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            } in
          let mk_mlift_wp lift_t r wp1 =
            let uu____7494 = inst_tscheme lift_t in
            match uu____7494 with
            | (uu____7499,lift_t1) ->
                let uu____7501 =
                  let uu____7504 =
                    let uu____7505 =
                      let uu____7515 =
                        let uu____7517 = FStar_Syntax_Syntax.as_arg r in
                        let uu____7518 =
                          let uu____7520 = FStar_Syntax_Syntax.as_arg wp1 in
                          [uu____7520] in
                        uu____7517 :: uu____7518 in
                      (lift_t1, uu____7515) in
                    FStar_Syntax_Syntax.Tm_app uu____7505 in
                  FStar_Syntax_Syntax.mk uu____7504 in
                uu____7501 None wp1.FStar_Syntax_Syntax.pos in
          let sub_mlift_wp =
            match sub1.FStar_Syntax_Syntax.lift_wp with
            | Some sub_lift_wp -> mk_mlift_wp sub_lift_wp
            | None  ->
                failwith "sub effect should've been elaborated at this stage" in
          let mk_mlift_term lift_t r wp1 e =
            let uu____7565 = inst_tscheme lift_t in
            match uu____7565 with
            | (uu____7570,lift_t1) ->
                let uu____7572 =
                  let uu____7575 =
                    let uu____7576 =
                      let uu____7586 =
                        let uu____7588 = FStar_Syntax_Syntax.as_arg r in
                        let uu____7589 =
                          let uu____7591 = FStar_Syntax_Syntax.as_arg wp1 in
                          let uu____7592 =
                            let uu____7594 = FStar_Syntax_Syntax.as_arg e in
                            [uu____7594] in
                          uu____7591 :: uu____7592 in
                        uu____7588 :: uu____7589 in
                      (lift_t1, uu____7586) in
                    FStar_Syntax_Syntax.Tm_app uu____7576 in
                  FStar_Syntax_Syntax.mk uu____7575 in
                uu____7572 None e.FStar_Syntax_Syntax.pos in
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
              let uu____7635 =
                let uu____7636 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange in
                FStar_Syntax_Syntax.lid_as_fv uu____7636
                  FStar_Syntax_Syntax.Delta_constant None in
              FStar_Syntax_Syntax.fv_to_tm uu____7635 in
            let arg = bogus_term "ARG" in
            let wp = bogus_term "WP" in
            let e = bogus_term "COMP" in
            let uu____7640 =
              let uu____7641 = l.mlift_wp arg wp in
              FStar_Syntax_Print.term_to_string uu____7641 in
            let uu____7642 =
              let uu____7643 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____7658 = l1 arg wp e in
                     FStar_Syntax_Print.term_to_string uu____7658) in
              FStar_Util.dflt "none" uu____7643 in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____7640
              uu____7642 in
          let order = edge :: ((env.effects).order) in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____7671  ->
                    match uu____7671 with
                    | (e,uu____7676) -> e.FStar_Syntax_Syntax.mname)) in
          let find_edge order1 uu____7689 =
            match uu____7689 with
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
              let uu____7714 =
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
                                    (let uu____7726 =
                                       let uu____7731 =
                                         find_edge order1 (i, k) in
                                       let uu____7733 =
                                         find_edge order1 (k, j) in
                                       (uu____7731, uu____7733) in
                                     match uu____7726 with
                                     | (Some e1,Some e2) ->
                                         let uu____7742 = compose_edges e1 e2 in
                                         [uu____7742]
                                     | uu____7743 -> []))))) in
              FStar_List.append order1 uu____7714 in
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
                   let uu____7758 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Syntax_Const.effect_DIV_lid)
                       &&
                       (let uu____7759 =
                          lookup_effect_quals env edge1.mtarget in
                        FStar_All.pipe_right uu____7759
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect)) in
                   if uu____7758
                   then
                     let uu____7762 =
                       let uu____7763 =
                         let uu____7766 =
                           FStar_Util.format1
                             "Divergent computations cannot be included in an effect %s marked 'total'"
                             (edge1.mtarget).FStar_Ident.str in
                         let uu____7767 = get_range env in
                         (uu____7766, uu____7767) in
                       FStar_Errors.Error uu____7763 in
                     raise uu____7762
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
                                            let uu____7830 =
                                              let uu____7835 =
                                                find_edge order2 (i, k) in
                                              let uu____7837 =
                                                find_edge order2 (j, k) in
                                              (uu____7835, uu____7837) in
                                            match uu____7830 with
                                            | (Some ik,Some jk) ->
                                                (match bopt with
                                                 | None  -> Some (k, ik, jk)
                                                 | Some
                                                     (ub,uu____7860,uu____7861)
                                                     ->
                                                     let uu____7865 =
                                                       let uu____7868 =
                                                         let uu____7869 =
                                                           find_edge order2
                                                             (k, ub) in
                                                         FStar_Util.is_some
                                                           uu____7869 in
                                                       let uu____7871 =
                                                         let uu____7872 =
                                                           find_edge order2
                                                             (ub, k) in
                                                         FStar_Util.is_some
                                                           uu____7872 in
                                                       (uu____7868,
                                                         uu____7871) in
                                                     (match uu____7865 with
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
                                            | uu____7891 -> bopt) None) in
                              match join_opt with
                              | None  -> []
                              | Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))])))) in
            let effects =
              let uu___122_5535 = env.effects in
              { decls = (uu___122_5535.decls); order = order2; joins } in
            let uu___123_5536 = env in
            {
              solver = (uu___123_5536.solver);
              range = (uu___123_5536.range);
              curmodule = (uu___123_5536.curmodule);
              gamma = (uu___123_5536.gamma);
              gamma_cache = (uu___123_5536.gamma_cache);
              modules = (uu___123_5536.modules);
              expected_typ = (uu___123_5536.expected_typ);
              sigtab = (uu___123_5536.sigtab);
              is_pattern = (uu___123_5536.is_pattern);
              instantiate_imp = (uu___123_5536.instantiate_imp);
              effects;
              generalize = (uu___123_5536.generalize);
              letrecs = (uu___123_5536.letrecs);
              top_level = (uu___123_5536.top_level);
              check_uvars = (uu___123_5536.check_uvars);
              use_eq = (uu___123_5536.use_eq);
              is_iface = (uu___123_5536.is_iface);
              admit = (uu___123_5536.admit);
              lax = (uu___123_5536.lax);
              lax_universes = (uu___123_5536.lax_universes);
              type_of = (uu___123_5536.type_of);
              universe_of = (uu___123_5536.universe_of);
              use_bv_sorts = (uu___123_5536.use_bv_sorts);
              qname_and_index = (uu___123_5536.qname_and_index);
              proof_ns = (uu___123_5536.proof_ns);
              synth = (uu___123_5536.synth);
              is_native_tactic = (uu___123_5536.is_native_tactic)
            }))
      | uu____7932 -> env
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
        | uu____7956 -> c in
      FStar_Syntax_Util.comp_to_comp_typ c1
let rec unfold_effect_abbrev:
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp in
      let uu____7966 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name in
      match uu____7966 with
      | None  -> c
      | Some (binders,cdef) ->
          let uu____7976 = FStar_Syntax_Subst.open_comp binders cdef in
          (match uu____7976 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____7998 =
                     let uu____7999 =
                       let uu____8002 =
                         let uu____8003 =
                           FStar_Util.string_of_int
                             (FStar_List.length binders1) in
                         let uu____8012 =
                           FStar_Util.string_of_int
                             ((FStar_List.length
                                 c.FStar_Syntax_Syntax.effect_args)
                                + (Prims.parse_int "1")) in
                         let uu____8023 =
                           let uu____8024 = FStar_Syntax_Syntax.mk_Comp c in
                           FStar_Syntax_Print.comp_to_string uu____8024 in
                         FStar_Util.format3
                           "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                           uu____8003 uu____8012 uu____8023 in
                       (uu____8002, (comp.FStar_Syntax_Syntax.pos)) in
                     FStar_Errors.Error uu____7999 in
                   raise uu____7998)
                else ();
                (let inst1 =
                   let uu____8028 =
                     let uu____8034 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ in
                     uu____8034 :: (c.FStar_Syntax_Syntax.effect_args) in
                   FStar_List.map2
                     (fun uu____8041  ->
                        fun uu____8042  ->
                          match (uu____8041, uu____8042) with
                          | ((x,uu____8056),(t,uu____8058)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____8028 in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1 in
                 let c2 =
                   let uu____5678 =
                     let uu___124_5679 = comp_to_comp_typ env c1 in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___124_5679.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___124_5679.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___124_5679.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___124_5679.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     } in
                   FStar_All.pipe_right uu____8073
                     FStar_Syntax_Syntax.mk_Comp in
                 unfold_effect_abbrev env c2)))
let effect_repr_aux only_reifiable env c u_c =
  let uu____8109 =
    let uu____8114 = norm_eff_name env (FStar_Syntax_Util.comp_effect_name c) in
    effect_decl_opt env uu____8114 in
  match uu____8109 with
  | None  -> None
  | Some (ed,qualifiers) ->
      let uu____8130 =
        only_reifiable &&
          (let uu____8131 =
             FStar_All.pipe_right qualifiers
               (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
           Prims.op_Negation uu____8131) in
      if uu____8130
      then None
      else
        (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_unknown  -> None
         | uu____8144 ->
             let c1 = unfold_effect_abbrev env c in
             let uu____8146 =
               let uu____8155 =
                 FStar_List.hd c1.FStar_Syntax_Syntax.effect_args in
               ((c1.FStar_Syntax_Syntax.result_typ), uu____8155) in
             (match uu____8146 with
              | (res_typ,wp) ->
                  let repr =
                    inst_effect_fun_with [u_c] env ed
                      ([], (ed.FStar_Syntax_Syntax.repr)) in
                  let uu____8189 =
                    let uu____8192 = get_range env in
                    let uu____8193 =
                      let uu____8196 =
                        let uu____8197 =
                          let uu____8207 =
                            let uu____8209 =
                              FStar_Syntax_Syntax.as_arg res_typ in
                            [uu____8209; wp] in
                          (repr, uu____8207) in
                        FStar_Syntax_Syntax.Tm_app uu____8197 in
                      FStar_Syntax_Syntax.mk uu____8196 in
                    uu____8193 None uu____8192 in
                  Some uu____8189))
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
          let uu____8259 =
            let uu____8260 =
              let uu____8263 =
                let uu____8264 = FStar_Ident.string_of_lid l in
                FStar_Util.format1 "Effect %s cannot be reified" uu____8264 in
              let uu____8265 = get_range env in (uu____8263, uu____8265) in
            FStar_Errors.Error uu____8260 in
          raise uu____8259 in
        let uu____8266 = effect_repr_aux true env c u_c in
        match uu____8266 with
        | None  -> no_reify (FStar_Syntax_Util.comp_effect_name c)
        | Some tm -> tm
let is_reifiable_effect: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun effect_lid  ->
      let quals = lookup_effect_quals env effect_lid in
      FStar_List.contains FStar_Syntax_Syntax.Reifiable quals
let is_reifiable: env -> FStar_Syntax_Syntax.residual_comp -> Prims.bool =
  fun env  ->
    fun c  -> is_reifiable_effect env c.FStar_Syntax_Syntax.residual_effect
let is_reifiable_comp: env -> FStar_Syntax_Syntax.comp -> Prims.bool =
  fun env  ->
    fun c  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Comp ct ->
          is_reifiable_effect env ct.FStar_Syntax_Syntax.effect_name
      | uu____5909 -> false
let is_reifiable_function: env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____5918 =
        let uu____5919 = FStar_Syntax_Subst.compress t in
        uu____5919.FStar_Syntax_Syntax.n in
      match uu____5918 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____5922,c) ->
          is_reifiable_comp env c
      | uu____5934 -> false
let push_in_gamma: env -> binding -> env =
  fun env  ->
    fun s  ->
      let rec push1 x rest =
        match rest with
        | (Binding_sig uu____5954)::uu____5955 -> x :: rest
        | (Binding_sig_inst uu____5960)::uu____5961 -> x :: rest
        | [] -> [x]
        | local::rest1 ->
            let uu____5970 = push1 x rest1 in local :: uu____5970 in
      let uu___125_5972 = env in
      let uu____5973 = push1 s env.gamma in
      {
        solver = (uu___125_5972.solver);
        range = (uu___125_5972.range);
        curmodule = (uu___125_5972.curmodule);
        gamma = uu____5973;
        gamma_cache = (uu___125_5972.gamma_cache);
        modules = (uu___125_5972.modules);
        expected_typ = (uu___125_5972.expected_typ);
        sigtab = (uu___125_5972.sigtab);
        is_pattern = (uu___125_5972.is_pattern);
        instantiate_imp = (uu___125_5972.instantiate_imp);
        effects = (uu___125_5972.effects);
        generalize = (uu___125_5972.generalize);
        letrecs = (uu___125_5972.letrecs);
        top_level = (uu___125_5972.top_level);
        check_uvars = (uu___125_5972.check_uvars);
        use_eq = (uu___125_5972.use_eq);
        is_iface = (uu___125_5972.is_iface);
        admit = (uu___125_5972.admit);
        lax = (uu___125_5972.lax);
        lax_universes = (uu___125_5972.lax_universes);
        type_of = (uu___125_5972.type_of);
        universe_of = (uu___125_5972.universe_of);
        use_bv_sorts = (uu___125_5972.use_bv_sorts);
        qname_and_index = (uu___125_5972.qname_and_index);
        proof_ns = (uu___125_5972.proof_ns);
        synth = (uu___125_5972.synth);
        is_native_tactic = (uu___125_5972.is_native_tactic)
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
      let uu___126_6007 = env in
      {
        solver = (uu___126_6007.solver);
        range = (uu___126_6007.range);
        curmodule = (uu___126_6007.curmodule);
        gamma = (b :: (env.gamma));
        gamma_cache = (uu___126_6007.gamma_cache);
        modules = (uu___126_6007.modules);
        expected_typ = (uu___126_6007.expected_typ);
        sigtab = (uu___126_6007.sigtab);
        is_pattern = (uu___126_6007.is_pattern);
        instantiate_imp = (uu___126_6007.instantiate_imp);
        effects = (uu___126_6007.effects);
        generalize = (uu___126_6007.generalize);
        letrecs = (uu___126_6007.letrecs);
        top_level = (uu___126_6007.top_level);
        check_uvars = (uu___126_6007.check_uvars);
        use_eq = (uu___126_6007.use_eq);
        is_iface = (uu___126_6007.is_iface);
        admit = (uu___126_6007.admit);
        lax = (uu___126_6007.lax);
        lax_universes = (uu___126_6007.lax_universes);
        type_of = (uu___126_6007.type_of);
        universe_of = (uu___126_6007.universe_of);
        use_bv_sorts = (uu___126_6007.use_bv_sorts);
        qname_and_index = (uu___126_6007.qname_and_index);
        proof_ns = (uu___126_6007.proof_ns);
        synth = (uu___126_6007.synth);
        is_native_tactic = (uu___126_6007.is_native_tactic)
      }
let push_bv: env -> FStar_Syntax_Syntax.bv -> env =
  fun env  -> fun x  -> push_local_binding env (Binding_var x)
let pop_bv: env -> (FStar_Syntax_Syntax.bv* env) option =
  fun env  ->
    match env.gamma with
    | (Binding_var x)::rest ->
        Some
          (x,
            (let uu___127_6031 = env in
             {
               solver = (uu___127_6031.solver);
               range = (uu___127_6031.range);
               curmodule = (uu___127_6031.curmodule);
               gamma = rest;
               gamma_cache = (uu___127_6031.gamma_cache);
               modules = (uu___127_6031.modules);
               expected_typ = (uu___127_6031.expected_typ);
               sigtab = (uu___127_6031.sigtab);
               is_pattern = (uu___127_6031.is_pattern);
               instantiate_imp = (uu___127_6031.instantiate_imp);
               effects = (uu___127_6031.effects);
               generalize = (uu___127_6031.generalize);
               letrecs = (uu___127_6031.letrecs);
               top_level = (uu___127_6031.top_level);
               check_uvars = (uu___127_6031.check_uvars);
               use_eq = (uu___127_6031.use_eq);
               is_iface = (uu___127_6031.is_iface);
               admit = (uu___127_6031.admit);
               lax = (uu___127_6031.lax);
               lax_universes = (uu___127_6031.lax_universes);
               type_of = (uu___127_6031.type_of);
               universe_of = (uu___127_6031.universe_of);
               use_bv_sorts = (uu___127_6031.use_bv_sorts);
               qname_and_index = (uu___127_6031.qname_and_index);
               proof_ns = (uu___127_6031.proof_ns);
               synth = (uu___127_6031.synth);
               is_native_tactic = (uu___127_6031.is_native_tactic)
             }))
    | uu____6032 -> None
let push_binders: env -> FStar_Syntax_Syntax.binders -> env =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____6047  ->
             match uu____6047 with | (x,uu____6051) -> push_bv env1 x) env bs
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
            let uu___128_6073 = x1 in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___128_6073.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___128_6073.FStar_Syntax_Syntax.index);
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
      (let uu___129_6108 = env in
       {
         solver = (uu___129_6108.solver);
         range = (uu___129_6108.range);
         curmodule = (uu___129_6108.curmodule);
         gamma = [];
         gamma_cache = (uu___129_6108.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = None;
         sigtab = (uu___129_6108.sigtab);
         is_pattern = (uu___129_6108.is_pattern);
         instantiate_imp = (uu___129_6108.instantiate_imp);
         effects = (uu___129_6108.effects);
         generalize = (uu___129_6108.generalize);
         letrecs = (uu___129_6108.letrecs);
         top_level = (uu___129_6108.top_level);
         check_uvars = (uu___129_6108.check_uvars);
         use_eq = (uu___129_6108.use_eq);
         is_iface = (uu___129_6108.is_iface);
         admit = (uu___129_6108.admit);
         lax = (uu___129_6108.lax);
         lax_universes = (uu___129_6108.lax_universes);
         type_of = (uu___129_6108.type_of);
         universe_of = (uu___129_6108.universe_of);
         use_bv_sorts = (uu___129_6108.use_bv_sorts);
         qname_and_index = (uu___129_6108.qname_and_index);
         proof_ns = (uu___129_6108.proof_ns);
         synth = (uu___129_6108.synth);
         is_native_tactic = (uu___129_6108.is_native_tactic)
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
        let uu____6137 = FStar_Syntax_Subst.univ_var_opening uvs in
        match uu____6137 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars in
            let uu____6153 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms in
            (env', univ_vars, uu____6153)
let set_expected_typ: env -> FStar_Syntax_Syntax.typ -> env =
  fun env  ->
    fun t  ->
      let uu___130_6165 = env in
      {
        solver = (uu___130_6165.solver);
        range = (uu___130_6165.range);
        curmodule = (uu___130_6165.curmodule);
        gamma = (uu___130_6165.gamma);
        gamma_cache = (uu___130_6165.gamma_cache);
        modules = (uu___130_6165.modules);
        expected_typ = (Some t);
        sigtab = (uu___130_6165.sigtab);
        is_pattern = (uu___130_6165.is_pattern);
        instantiate_imp = (uu___130_6165.instantiate_imp);
        effects = (uu___130_6165.effects);
        generalize = (uu___130_6165.generalize);
        letrecs = (uu___130_6165.letrecs);
        top_level = (uu___130_6165.top_level);
        check_uvars = (uu___130_6165.check_uvars);
        use_eq = false;
        is_iface = (uu___130_6165.is_iface);
        admit = (uu___130_6165.admit);
        lax = (uu___130_6165.lax);
        lax_universes = (uu___130_6165.lax_universes);
        type_of = (uu___130_6165.type_of);
        universe_of = (uu___130_6165.universe_of);
        use_bv_sorts = (uu___130_6165.use_bv_sorts);
        qname_and_index = (uu___130_6165.qname_and_index);
        proof_ns = (uu___130_6165.proof_ns);
        synth = (uu___130_6165.synth);
        is_native_tactic = (uu___130_6165.is_native_tactic)
      }
let expected_typ: env -> FStar_Syntax_Syntax.typ option =
  fun env  -> match env.expected_typ with | None  -> None | Some t -> Some t
let clear_expected_typ: env -> (env* FStar_Syntax_Syntax.typ option) =
  fun env_  ->
    let uu____6183 = expected_typ env_ in
    ((let uu___131_6186 = env_ in
      {
        solver = (uu___131_6186.solver);
        range = (uu___131_6186.range);
        curmodule = (uu___131_6186.curmodule);
        gamma = (uu___131_6186.gamma);
        gamma_cache = (uu___131_6186.gamma_cache);
        modules = (uu___131_6186.modules);
        expected_typ = None;
        sigtab = (uu___131_6186.sigtab);
        is_pattern = (uu___131_6186.is_pattern);
        instantiate_imp = (uu___131_6186.instantiate_imp);
        effects = (uu___131_6186.effects);
        generalize = (uu___131_6186.generalize);
        letrecs = (uu___131_6186.letrecs);
        top_level = (uu___131_6186.top_level);
        check_uvars = (uu___131_6186.check_uvars);
        use_eq = false;
        is_iface = (uu___131_6186.is_iface);
        admit = (uu___131_6186.admit);
        lax = (uu___131_6186.lax);
        lax_universes = (uu___131_6186.lax_universes);
        type_of = (uu___131_6186.type_of);
        universe_of = (uu___131_6186.universe_of);
        use_bv_sorts = (uu___131_6186.use_bv_sorts);
        qname_and_index = (uu___131_6186.qname_and_index);
        proof_ns = (uu___131_6186.proof_ns);
        synth = (uu___131_6186.synth);
        is_native_tactic = (uu___131_6186.is_native_tactic)
      }), uu____6183)
let finish_module: env -> FStar_Syntax_Syntax.modul -> env =
  let empty_lid = FStar_Ident.lid_of_ids [FStar_Ident.id_of_text ""] in
  fun env  ->
    fun m  ->
      let sigs =
        if
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Syntax_Const.prims_lid
        then
          let uu____6199 =
            FStar_All.pipe_right env.gamma
              (FStar_List.collect
                 (fun uu___110_6203  ->
                    match uu___110_6203 with
                    | Binding_sig (uu____6205,se) -> [se]
                    | uu____6209 -> [])) in
          FStar_All.pipe_right uu____6199 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports in
      add_sigelts env sigs;
      (let uu___132_6214 = env in
       {
         solver = (uu___132_6214.solver);
         range = (uu___132_6214.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_cache = (uu___132_6214.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___132_6214.expected_typ);
         sigtab = (uu___132_6214.sigtab);
         is_pattern = (uu___132_6214.is_pattern);
         instantiate_imp = (uu___132_6214.instantiate_imp);
         effects = (uu___132_6214.effects);
         generalize = (uu___132_6214.generalize);
         letrecs = (uu___132_6214.letrecs);
         top_level = (uu___132_6214.top_level);
         check_uvars = (uu___132_6214.check_uvars);
         use_eq = (uu___132_6214.use_eq);
         is_iface = (uu___132_6214.is_iface);
         admit = (uu___132_6214.admit);
         lax = (uu___132_6214.lax);
         lax_universes = (uu___132_6214.lax_universes);
         type_of = (uu___132_6214.type_of);
         universe_of = (uu___132_6214.universe_of);
         use_bv_sorts = (uu___132_6214.use_bv_sorts);
         qname_and_index = (uu___132_6214.qname_and_index);
         proof_ns = (uu___132_6214.proof_ns);
         synth = (uu___132_6214.synth);
         is_native_tactic = (uu___132_6214.is_native_tactic)
       })
let uvars_in_env:
  env -> (FStar_Syntax_Syntax.uvar* FStar_Syntax_Syntax.typ) FStar_Util.set =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_univ uu____6265)::tl1 -> aux out tl1
      | (Binding_lid (uu____6268,(uu____6269,t)))::tl1 ->
          let uu____6278 =
            let uu____6282 = FStar_Syntax_Free.uvars t in ext out uu____6282 in
          aux uu____6278 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____6286;
            FStar_Syntax_Syntax.index = uu____6287;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____6293 =
            let uu____6297 = FStar_Syntax_Free.uvars t in ext out uu____6297 in
          aux uu____6293 tl1
      | (Binding_sig uu____6301)::uu____6302 -> out
      | (Binding_sig_inst uu____6307)::uu____6308 -> out in
    aux no_uvs env.gamma
let univ_vars: env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____6346)::tl1 -> aux out tl1
      | (Binding_univ uu____6353)::tl1 -> aux out tl1
      | (Binding_lid (uu____6356,(uu____6357,t)))::tl1 ->
          let uu____6366 =
            let uu____6368 = FStar_Syntax_Free.univs t in ext out uu____6368 in
          aux uu____6366 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____6370;
            FStar_Syntax_Syntax.index = uu____6371;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____6377 =
            let uu____6379 = FStar_Syntax_Free.univs t in ext out uu____6379 in
          aux uu____6377 tl1
      | (Binding_sig uu____6381)::uu____6382 -> out in
    aux no_univs env.gamma
let univnames: env -> FStar_Syntax_Syntax.univ_name FStar_Util.set =
  fun env  ->
    let no_univ_names = FStar_Syntax_Syntax.no_universe_names in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____6420)::tl1 -> aux out tl1
      | (Binding_univ uname)::tl1 ->
          let uu____6430 = FStar_Util.set_add uname out in aux uu____6430 tl1
      | (Binding_lid (uu____6432,(uu____6433,t)))::tl1 ->
          let uu____6442 =
            let uu____6444 = FStar_Syntax_Free.univnames t in
            ext out uu____6444 in
          aux uu____6442 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____6446;
            FStar_Syntax_Syntax.index = uu____6447;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____6453 =
            let uu____6455 = FStar_Syntax_Free.univnames t in
            ext out uu____6455 in
          aux uu____6453 tl1
      | (Binding_sig uu____6457)::uu____6458 -> out in
    aux no_univ_names env.gamma
let bound_vars_of_bindings:
  binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___111_6475  ->
            match uu___111_6475 with
            | Binding_var x -> [x]
            | Binding_lid uu____6478 -> []
            | Binding_sig uu____6481 -> []
            | Binding_univ uu____6485 -> []
            | Binding_sig_inst uu____6486 -> []))
let binders_of_bindings:
  binding Prims.list -> FStar_Syntax_Syntax.binder Prims.list =
  fun bs  ->
    let uu____6497 =
      let uu____6499 = bound_vars_of_bindings bs in
      FStar_All.pipe_right uu____6499
        (FStar_List.map FStar_Syntax_Syntax.mk_binder) in
    FStar_All.pipe_right uu____6497 FStar_List.rev
let bound_vars: env -> FStar_Syntax_Syntax.bv Prims.list =
  fun env  -> bound_vars_of_bindings env.gamma
let all_binders: env -> FStar_Syntax_Syntax.binders =
  fun env  -> binders_of_bindings env.gamma
let print_gamma: env -> Prims.unit =
  fun env  ->
    let uu____6518 =
      let uu____6519 =
        FStar_All.pipe_right env.gamma
          (FStar_List.map
             (fun uu___112_6523  ->
                match uu___112_6523 with
                | Binding_var x ->
                    let uu____6525 = FStar_Syntax_Print.bv_to_string x in
                    Prims.strcat "Binding_var " uu____6525
                | Binding_univ u ->
                    Prims.strcat "Binding_univ " u.FStar_Ident.idText
                | Binding_lid (l,uu____6528) ->
                    let uu____6529 = FStar_Ident.string_of_lid l in
                    Prims.strcat "Binding_lid " uu____6529
                | Binding_sig (ls,uu____6531) ->
                    let uu____6534 =
                      let uu____6535 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____6535
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig " uu____6534
                | Binding_sig_inst (ls,uu____6541,uu____6542) ->
                    let uu____6545 =
                      let uu____6546 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____6546
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig_inst " uu____6545)) in
      FStar_All.pipe_right uu____6519 (FStar_String.concat "::\n") in
    FStar_All.pipe_right uu____6518 (FStar_Util.print1 "%s\n")
let eq_gamma: env -> env -> Prims.bool =
  fun env  ->
    fun env'  ->
      let uu____6560 = FStar_Util.physical_equality env.gamma env'.gamma in
      if uu____6560
      then true
      else
        (let g = all_binders env in
         let g' = all_binders env' in
         ((FStar_List.length g) = (FStar_List.length g')) &&
           (FStar_List.forall2
              (fun uu____6581  ->
                 fun uu____6582  ->
                   match (uu____6581, uu____6582) with
                   | ((b1,uu____6592),(b2,uu____6594)) ->
                       FStar_Syntax_Syntax.bv_eq b1 b2) g g'))
let fold_env env f a =
  FStar_List.fold_right (fun e  -> fun a1  -> f a1 e) env.gamma a
let lidents: env -> FStar_Ident.lident Prims.list =
  fun env  ->
    let keys =
      FStar_List.fold_left
        (fun keys  ->
           fun uu___113_6642  ->
             match uu___113_6642 with
             | Binding_sig (lids,uu____6646) -> FStar_List.append lids keys
             | uu____6649 -> keys) [] env.gamma in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____6651  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
let should_enc_path: env -> Prims.string Prims.list -> Prims.bool =
  fun env  ->
    fun path  ->
      let rec list_prefix xs ys =
        match (xs, ys) with
        | ([],uu____6678) -> true
        | (x::xs1,y::ys1) -> (x = y) && (list_prefix xs1 ys1)
        | (uu____6690,uu____6691) -> false in
      let rec should_enc_path' pns path1 =
        match pns with
        | [] -> true
        | (p,b)::pns1 ->
            let uu____6715 = list_prefix p path1 in
            if uu____6715 then b else should_enc_path' pns1 path1 in
      should_enc_path' (FStar_List.flatten env.proof_ns) path
let should_enc_lid: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____6727 = FStar_Ident.path_of_lid lid in
      should_enc_path env uu____6727
let cons_proof_ns: Prims.bool -> env -> name_prefix -> env =
  fun b  ->
    fun e  ->
      fun path  ->
        match e.proof_ns with
        | [] -> failwith "empty proof_ns stack!"
        | pns::rest ->
            let pns' = (path, b) :: pns in
            let uu___133_6750 = e in
            {
              solver = (uu___133_6750.solver);
              range = (uu___133_6750.range);
              curmodule = (uu___133_6750.curmodule);
              gamma = (uu___133_6750.gamma);
              gamma_cache = (uu___133_6750.gamma_cache);
              modules = (uu___133_6750.modules);
              expected_typ = (uu___133_6750.expected_typ);
              sigtab = (uu___133_6750.sigtab);
              is_pattern = (uu___133_6750.is_pattern);
              instantiate_imp = (uu___133_6750.instantiate_imp);
              effects = (uu___133_6750.effects);
              generalize = (uu___133_6750.generalize);
              letrecs = (uu___133_6750.letrecs);
              top_level = (uu___133_6750.top_level);
              check_uvars = (uu___133_6750.check_uvars);
              use_eq = (uu___133_6750.use_eq);
              is_iface = (uu___133_6750.is_iface);
              admit = (uu___133_6750.admit);
              lax = (uu___133_6750.lax);
              lax_universes = (uu___133_6750.lax_universes);
              type_of = (uu___133_6750.type_of);
              universe_of = (uu___133_6750.universe_of);
              use_bv_sorts = (uu___133_6750.use_bv_sorts);
              qname_and_index = (uu___133_6750.qname_and_index);
              proof_ns = (pns' :: rest);
              synth = (uu___133_6750.synth);
              is_native_tactic = (uu___133_6750.is_native_tactic)
            }
let add_proof_ns: env -> name_prefix -> env =
  fun e  -> fun path  -> cons_proof_ns true e path
let rem_proof_ns: env -> name_prefix -> env =
  fun e  -> fun path  -> cons_proof_ns false e path
let push_proof_ns: env -> env =
  fun e  ->
    let uu___134_6774 = e in
    {
      solver = (uu___134_6774.solver);
      range = (uu___134_6774.range);
      curmodule = (uu___134_6774.curmodule);
      gamma = (uu___134_6774.gamma);
      gamma_cache = (uu___134_6774.gamma_cache);
      modules = (uu___134_6774.modules);
      expected_typ = (uu___134_6774.expected_typ);
      sigtab = (uu___134_6774.sigtab);
      is_pattern = (uu___134_6774.is_pattern);
      instantiate_imp = (uu___134_6774.instantiate_imp);
      effects = (uu___134_6774.effects);
      generalize = (uu___134_6774.generalize);
      letrecs = (uu___134_6774.letrecs);
      top_level = (uu___134_6774.top_level);
      check_uvars = (uu___134_6774.check_uvars);
      use_eq = (uu___134_6774.use_eq);
      is_iface = (uu___134_6774.is_iface);
      admit = (uu___134_6774.admit);
      lax = (uu___134_6774.lax);
      lax_universes = (uu___134_6774.lax_universes);
      type_of = (uu___134_6774.type_of);
      universe_of = (uu___134_6774.universe_of);
      use_bv_sorts = (uu___134_6774.use_bv_sorts);
      qname_and_index = (uu___134_6774.qname_and_index);
      proof_ns = ([] :: (e.proof_ns));
      synth = (uu___134_6774.synth);
      is_native_tactic = (uu___134_6774.is_native_tactic)
    }
let pop_proof_ns: env -> env =
  fun e  ->
    match e.proof_ns with
    | [] -> failwith "empty proof_ns stack!"
    | uu____6784::rest ->
        let uu___135_6787 = e in
        {
          solver = (uu___135_6787.solver);
          range = (uu___135_6787.range);
          curmodule = (uu___135_6787.curmodule);
          gamma = (uu___135_6787.gamma);
          gamma_cache = (uu___135_6787.gamma_cache);
          modules = (uu___135_6787.modules);
          expected_typ = (uu___135_6787.expected_typ);
          sigtab = (uu___135_6787.sigtab);
          is_pattern = (uu___135_6787.is_pattern);
          instantiate_imp = (uu___135_6787.instantiate_imp);
          effects = (uu___135_6787.effects);
          generalize = (uu___135_6787.generalize);
          letrecs = (uu___135_6787.letrecs);
          top_level = (uu___135_6787.top_level);
          check_uvars = (uu___135_6787.check_uvars);
          use_eq = (uu___135_6787.use_eq);
          is_iface = (uu___135_6787.is_iface);
          admit = (uu___135_6787.admit);
          lax = (uu___135_6787.lax);
          lax_universes = (uu___135_6787.lax_universes);
          type_of = (uu___135_6787.type_of);
          universe_of = (uu___135_6787.universe_of);
          use_bv_sorts = (uu___135_6787.use_bv_sorts);
          qname_and_index = (uu___135_6787.qname_and_index);
          proof_ns = rest;
          synth = (uu___135_6787.synth);
          is_native_tactic = (uu___135_6787.is_native_tactic)
        }
let get_proof_ns: env -> proof_namespace = fun e  -> e.proof_ns
let set_proof_ns: proof_namespace -> env -> env =
  fun ns  ->
    fun e  ->
      let uu___136_6800 = e in
      {
        solver = (uu___136_6800.solver);
        range = (uu___136_6800.range);
        curmodule = (uu___136_6800.curmodule);
        gamma = (uu___136_6800.gamma);
        gamma_cache = (uu___136_6800.gamma_cache);
        modules = (uu___136_6800.modules);
        expected_typ = (uu___136_6800.expected_typ);
        sigtab = (uu___136_6800.sigtab);
        is_pattern = (uu___136_6800.is_pattern);
        instantiate_imp = (uu___136_6800.instantiate_imp);
        effects = (uu___136_6800.effects);
        generalize = (uu___136_6800.generalize);
        letrecs = (uu___136_6800.letrecs);
        top_level = (uu___136_6800.top_level);
        check_uvars = (uu___136_6800.check_uvars);
        use_eq = (uu___136_6800.use_eq);
        is_iface = (uu___136_6800.is_iface);
        admit = (uu___136_6800.admit);
        lax = (uu___136_6800.lax);
        lax_universes = (uu___136_6800.lax_universes);
        type_of = (uu___136_6800.type_of);
        universe_of = (uu___136_6800.universe_of);
        use_bv_sorts = (uu___136_6800.use_bv_sorts);
        qname_and_index = (uu___136_6800.qname_and_index);
        proof_ns = ns;
        synth = (uu___136_6800.synth);
        is_native_tactic = (uu___136_6800.is_native_tactic)
      }
let string_of_proof_ns: env -> Prims.string =
  fun env  ->
    let string_of_proof_ns' pns =
      let uu____6819 =
        FStar_List.map
          (fun fpns  ->
             let uu____6830 =
               let uu____6831 =
                 let uu____6832 =
                   FStar_List.map
                     (fun uu____6837  ->
                        match uu____6837 with
                        | (p,b) ->
                            Prims.strcat (if b then "+" else "-")
                              (FStar_String.concat "." p)) fpns in
                 FStar_String.concat "," uu____6832 in
               Prims.strcat uu____6831 "]" in
             Prims.strcat "[" uu____6830) pns in
      FStar_String.concat ";" uu____6819 in
    string_of_proof_ns' env.proof_ns
let dummy_solver: solver_t =
  {
    init = (fun uu____6846  -> ());
    push = (fun uu____6847  -> ());
    pop = (fun uu____6848  -> ());
    mark = (fun uu____6849  -> ());
    reset_mark = (fun uu____6850  -> ());
    commit_mark = (fun uu____6851  -> ());
    encode_modul = (fun uu____6852  -> fun uu____6853  -> ());
    encode_sig = (fun uu____6854  -> fun uu____6855  -> ());
    preprocess = (fun e  -> fun g  -> [(e, g)]);
    solve = (fun uu____6862  -> fun uu____6863  -> fun uu____6864  -> ());
    is_trivial = (fun uu____6868  -> fun uu____6869  -> false);
    finish = (fun uu____6870  -> ());
    refresh = (fun uu____6871  -> ())
  }