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
    (let uu____3885 =
       let uu____3887 = FStar_ST.read stack in env :: uu____3887 in
     FStar_ST.write stack uu____3885);
    (let uu___112_3895 = env in
     let uu____3896 = FStar_Util.smap_copy (gamma_cache env) in
     let uu____3898 = FStar_Util.smap_copy (sigtab env) in
     {
       solver = (uu___112_3895.solver);
       range = (uu___112_3895.range);
       curmodule = (uu___112_3895.curmodule);
       gamma = (uu___112_3895.gamma);
       gamma_cache = uu____3896;
       modules = (uu___112_3895.modules);
       expected_typ = (uu___112_3895.expected_typ);
       sigtab = uu____3898;
       is_pattern = (uu___112_3895.is_pattern);
       instantiate_imp = (uu___112_3895.instantiate_imp);
       effects = (uu___112_3895.effects);
       generalize = (uu___112_3895.generalize);
       letrecs = (uu___112_3895.letrecs);
       top_level = (uu___112_3895.top_level);
       check_uvars = (uu___112_3895.check_uvars);
       use_eq = (uu___112_3895.use_eq);
       is_iface = (uu___112_3895.is_iface);
       admit = (uu___112_3895.admit);
       lax = (uu___112_3895.lax);
       lax_universes = (uu___112_3895.lax_universes);
       type_of = (uu___112_3895.type_of);
       universe_of = (uu___112_3895.universe_of);
       use_bv_sorts = (uu___112_3895.use_bv_sorts);
       qname_and_index = (uu___112_3895.qname_and_index);
       proof_ns = (uu___112_3895.proof_ns);
       synth = (uu___112_3895.synth);
       is_native_tactic = (uu___112_3895.is_native_tactic)
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
              (let uu___113_3997 = env in
               {
                 solver = (uu___113_3997.solver);
                 range = (uu___113_3997.range);
                 curmodule = (uu___113_3997.curmodule);
                 gamma = (uu___113_3997.gamma);
                 gamma_cache = (uu___113_3997.gamma_cache);
                 modules = (uu___113_3997.modules);
                 expected_typ = (uu___113_3997.expected_typ);
                 sigtab = (uu___113_3997.sigtab);
                 is_pattern = (uu___113_3997.is_pattern);
                 instantiate_imp = (uu___113_3997.instantiate_imp);
                 effects = (uu___113_3997.effects);
                 generalize = (uu___113_3997.generalize);
                 letrecs = (uu___113_3997.letrecs);
                 top_level = (uu___113_3997.top_level);
                 check_uvars = (uu___113_3997.check_uvars);
                 use_eq = (uu___113_3997.use_eq);
                 is_iface = (uu___113_3997.is_iface);
                 admit = (uu___113_3997.admit);
                 lax = (uu___113_3997.lax);
                 lax_universes = (uu___113_3997.lax_universes);
                 type_of = (uu___113_3997.type_of);
                 universe_of = (uu___113_3997.universe_of);
                 use_bv_sorts = (uu___113_3997.use_bv_sorts);
                 qname_and_index = (Some (l, next));
                 proof_ns = (uu___113_3997.proof_ns);
                 synth = (uu___113_3997.synth);
                 is_native_tactic = (uu___113_3997.is_native_tactic)
               }))
         | Some (uu____4000,m) ->
             let next = m + (Prims.parse_int "1") in
             (add_query_index (l, next);
              (let uu___114_4006 = env in
               {
                 solver = (uu___114_4006.solver);
                 range = (uu___114_4006.range);
                 curmodule = (uu___114_4006.curmodule);
                 gamma = (uu___114_4006.gamma);
                 gamma_cache = (uu___114_4006.gamma_cache);
                 modules = (uu___114_4006.modules);
                 expected_typ = (uu___114_4006.expected_typ);
                 sigtab = (uu___114_4006.sigtab);
                 is_pattern = (uu___114_4006.is_pattern);
                 instantiate_imp = (uu___114_4006.instantiate_imp);
                 effects = (uu___114_4006.effects);
                 generalize = (uu___114_4006.generalize);
                 letrecs = (uu___114_4006.letrecs);
                 top_level = (uu___114_4006.top_level);
                 check_uvars = (uu___114_4006.check_uvars);
                 use_eq = (uu___114_4006.use_eq);
                 is_iface = (uu___114_4006.is_iface);
                 admit = (uu___114_4006.admit);
                 lax = (uu___114_4006.lax);
                 lax_universes = (uu___114_4006.lax_universes);
                 type_of = (uu___114_4006.type_of);
                 universe_of = (uu___114_4006.universe_of);
                 use_bv_sorts = (uu___114_4006.use_bv_sorts);
                 qname_and_index = (Some (l, next));
                 proof_ns = (uu___114_4006.proof_ns);
                 synth = (uu___114_4006.synth);
                 is_native_tactic = (uu___114_4006.is_native_tactic)
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
        (let uu___115_4026 = e in
         {
           solver = (uu___115_4026.solver);
           range = r;
           curmodule = (uu___115_4026.curmodule);
           gamma = (uu___115_4026.gamma);
           gamma_cache = (uu___115_4026.gamma_cache);
           modules = (uu___115_4026.modules);
           expected_typ = (uu___115_4026.expected_typ);
           sigtab = (uu___115_4026.sigtab);
           is_pattern = (uu___115_4026.is_pattern);
           instantiate_imp = (uu___115_4026.instantiate_imp);
           effects = (uu___115_4026.effects);
           generalize = (uu___115_4026.generalize);
           letrecs = (uu___115_4026.letrecs);
           top_level = (uu___115_4026.top_level);
           check_uvars = (uu___115_4026.check_uvars);
           use_eq = (uu___115_4026.use_eq);
           is_iface = (uu___115_4026.is_iface);
           admit = (uu___115_4026.admit);
           lax = (uu___115_4026.lax);
           lax_universes = (uu___115_4026.lax_universes);
           type_of = (uu___115_4026.type_of);
           universe_of = (uu___115_4026.universe_of);
           use_bv_sorts = (uu___115_4026.use_bv_sorts);
           qname_and_index = (uu___115_4026.qname_and_index);
           proof_ns = (uu___115_4026.proof_ns);
           synth = (uu___115_4026.synth);
           is_native_tactic = (uu___115_4026.is_native_tactic)
         })
let get_range: env -> FStar_Range.range = fun e  -> e.range
let modules: env -> FStar_Syntax_Syntax.modul Prims.list =
  fun env  -> env.modules
let current_module: env -> FStar_Ident.lident = fun env  -> env.curmodule
let set_current_module: env -> FStar_Ident.lident -> env =
  fun env  ->
    fun lid  ->
      let uu___116_4048 = env in
      {
        solver = (uu___116_4048.solver);
        range = (uu___116_4048.range);
        curmodule = lid;
        gamma = (uu___116_4048.gamma);
        gamma_cache = (uu___116_4048.gamma_cache);
        modules = (uu___116_4048.modules);
        expected_typ = (uu___116_4048.expected_typ);
        sigtab = (uu___116_4048.sigtab);
        is_pattern = (uu___116_4048.is_pattern);
        instantiate_imp = (uu___116_4048.instantiate_imp);
        effects = (uu___116_4048.effects);
        generalize = (uu___116_4048.generalize);
        letrecs = (uu___116_4048.letrecs);
        top_level = (uu___116_4048.top_level);
        check_uvars = (uu___116_4048.check_uvars);
        use_eq = (uu___116_4048.use_eq);
        is_iface = (uu___116_4048.is_iface);
        admit = (uu___116_4048.admit);
        lax = (uu___116_4048.lax);
        lax_universes = (uu___116_4048.lax_universes);
        type_of = (uu___116_4048.type_of);
        universe_of = (uu___116_4048.universe_of);
        use_bv_sorts = (uu___116_4048.use_bv_sorts);
        qname_and_index = (uu___116_4048.qname_and_index);
        proof_ns = (uu___116_4048.proof_ns);
        synth = (uu___116_4048.synth);
        is_native_tactic = (uu___116_4048.is_native_tactic)
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
  fun uu___100_4130  ->
    match uu___100_4130 with
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
                (fun uu___101_4359  ->
                   match uu___101_4359 with
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
        (fun uu___102_4717  ->
           match uu___102_4717 with
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
               (let uu___117_5356 = t in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___117_5356.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___117_5356.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid);
                  FStar_Syntax_Syntax.vars =
                    (uu___117_5356.FStar_Syntax_Syntax.vars)
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
           (fun uu___103_5573  ->
              match uu___103_5573 with
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
                   (fun uu___104_6243  ->
                      match uu___104_6243 with
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
            (fun uu___105_6573  ->
               match uu___105_6573 with
               | FStar_Syntax_Syntax.Projector uu____6574 -> true
               | uu____6577 -> false) quals
      | uu____6578 -> false
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
            (fun uu___106_6714  ->
               match uu___106_6714 with
               | FStar_Syntax_Syntax.RecordType uu____6715 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____6720 -> true
               | uu____6725 -> false) quals
      | uu____6726 -> false
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
            (fun uu___107_6792  ->
               match uu___107_6792 with
               | FStar_Syntax_Syntax.Action uu____6793 -> true
               | uu____6794 -> false) quals
      | uu____6795 -> false
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
            let uu___118_7356 = env.effects in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___118_7356.order);
              joins = (uu___118_7356.joins)
            } in
          let uu___119_7361 = env in
          {
            solver = (uu___119_7361.solver);
            range = (uu___119_7361.range);
            curmodule = (uu___119_7361.curmodule);
            gamma = (uu___119_7361.gamma);
            gamma_cache = (uu___119_7361.gamma_cache);
            modules = (uu___119_7361.modules);
            expected_typ = (uu___119_7361.expected_typ);
            sigtab = (uu___119_7361.sigtab);
            is_pattern = (uu___119_7361.is_pattern);
            instantiate_imp = (uu___119_7361.instantiate_imp);
            effects;
            generalize = (uu___119_7361.generalize);
            letrecs = (uu___119_7361.letrecs);
            top_level = (uu___119_7361.top_level);
            check_uvars = (uu___119_7361.check_uvars);
            use_eq = (uu___119_7361.use_eq);
            is_iface = (uu___119_7361.is_iface);
            admit = (uu___119_7361.admit);
            lax = (uu___119_7361.lax);
            lax_universes = (uu___119_7361.lax_universes);
            type_of = (uu___119_7361.type_of);
            universe_of = (uu___119_7361.universe_of);
            use_bv_sorts = (uu___119_7361.use_bv_sorts);
            qname_and_index = (uu___119_7361.qname_and_index);
            proof_ns = (uu___119_7361.proof_ns);
            synth = (uu___119_7361.synth);
            is_native_tactic = (uu___119_7361.is_native_tactic)
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
              let uu___120_7930 = env.effects in
              { decls = (uu___120_7930.decls); order = order2; joins } in
            let uu___121_7931 = env in
            {
              solver = (uu___121_7931.solver);
              range = (uu___121_7931.range);
              curmodule = (uu___121_7931.curmodule);
              gamma = (uu___121_7931.gamma);
              gamma_cache = (uu___121_7931.gamma_cache);
              modules = (uu___121_7931.modules);
              expected_typ = (uu___121_7931.expected_typ);
              sigtab = (uu___121_7931.sigtab);
              is_pattern = (uu___121_7931.is_pattern);
              instantiate_imp = (uu___121_7931.instantiate_imp);
              effects;
              generalize = (uu___121_7931.generalize);
              letrecs = (uu___121_7931.letrecs);
              top_level = (uu___121_7931.top_level);
              check_uvars = (uu___121_7931.check_uvars);
              use_eq = (uu___121_7931.use_eq);
              is_iface = (uu___121_7931.is_iface);
              admit = (uu___121_7931.admit);
              lax = (uu___121_7931.lax);
              lax_universes = (uu___121_7931.lax_universes);
              type_of = (uu___121_7931.type_of);
              universe_of = (uu___121_7931.universe_of);
              use_bv_sorts = (uu___121_7931.use_bv_sorts);
              qname_and_index = (uu___121_7931.qname_and_index);
              proof_ns = (uu___121_7931.proof_ns);
              synth = (uu___121_7931.synth);
              is_native_tactic = (uu___121_7931.is_native_tactic)
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
                   let uu____8073 =
                     let uu___122_8074 = comp_to_comp_typ env c1 in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___122_8074.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___122_8074.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___122_8074.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___122_8074.FStar_Syntax_Syntax.effect_args);
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
        | FStar_Util.Inr (eff_name,uu____8302) -> eff_name in
      is_reifiable_effect env effect_lid
let is_reifiable_comp: env -> FStar_Syntax_Syntax.comp -> Prims.bool =
  fun env  ->
    fun c  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Comp ct ->
          is_reifiable_effect env ct.FStar_Syntax_Syntax.effect_name
      | uu____8317 -> false
let is_reifiable_function: env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____8326 =
        let uu____8327 = FStar_Syntax_Subst.compress t in
        uu____8327.FStar_Syntax_Syntax.n in
      match uu____8326 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____8330,c) ->
          is_reifiable_comp env c
      | uu____8342 -> false
let push_in_gamma: env -> binding -> env =
  fun env  ->
    fun s  ->
      let rec push1 x rest =
        match rest with
        | (Binding_sig uu____8362)::uu____8363 -> x :: rest
        | (Binding_sig_inst uu____8368)::uu____8369 -> x :: rest
        | [] -> [x]
        | local::rest1 ->
            let uu____8378 = push1 x rest1 in local :: uu____8378 in
      let uu___123_8380 = env in
      let uu____8381 = push1 s env.gamma in
      {
        solver = (uu___123_8380.solver);
        range = (uu___123_8380.range);
        curmodule = (uu___123_8380.curmodule);
        gamma = uu____8381;
        gamma_cache = (uu___123_8380.gamma_cache);
        modules = (uu___123_8380.modules);
        expected_typ = (uu___123_8380.expected_typ);
        sigtab = (uu___123_8380.sigtab);
        is_pattern = (uu___123_8380.is_pattern);
        instantiate_imp = (uu___123_8380.instantiate_imp);
        effects = (uu___123_8380.effects);
        generalize = (uu___123_8380.generalize);
        letrecs = (uu___123_8380.letrecs);
        top_level = (uu___123_8380.top_level);
        check_uvars = (uu___123_8380.check_uvars);
        use_eq = (uu___123_8380.use_eq);
        is_iface = (uu___123_8380.is_iface);
        admit = (uu___123_8380.admit);
        lax = (uu___123_8380.lax);
        lax_universes = (uu___123_8380.lax_universes);
        type_of = (uu___123_8380.type_of);
        universe_of = (uu___123_8380.universe_of);
        use_bv_sorts = (uu___123_8380.use_bv_sorts);
        qname_and_index = (uu___123_8380.qname_and_index);
        proof_ns = (uu___123_8380.proof_ns);
        synth = (uu___123_8380.synth);
        is_native_tactic = (uu___123_8380.is_native_tactic)
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
      let uu___124_8415 = env in
      {
        solver = (uu___124_8415.solver);
        range = (uu___124_8415.range);
        curmodule = (uu___124_8415.curmodule);
        gamma = (b :: (env.gamma));
        gamma_cache = (uu___124_8415.gamma_cache);
        modules = (uu___124_8415.modules);
        expected_typ = (uu___124_8415.expected_typ);
        sigtab = (uu___124_8415.sigtab);
        is_pattern = (uu___124_8415.is_pattern);
        instantiate_imp = (uu___124_8415.instantiate_imp);
        effects = (uu___124_8415.effects);
        generalize = (uu___124_8415.generalize);
        letrecs = (uu___124_8415.letrecs);
        top_level = (uu___124_8415.top_level);
        check_uvars = (uu___124_8415.check_uvars);
        use_eq = (uu___124_8415.use_eq);
        is_iface = (uu___124_8415.is_iface);
        admit = (uu___124_8415.admit);
        lax = (uu___124_8415.lax);
        lax_universes = (uu___124_8415.lax_universes);
        type_of = (uu___124_8415.type_of);
        universe_of = (uu___124_8415.universe_of);
        use_bv_sorts = (uu___124_8415.use_bv_sorts);
        qname_and_index = (uu___124_8415.qname_and_index);
        proof_ns = (uu___124_8415.proof_ns);
        synth = (uu___124_8415.synth);
        is_native_tactic = (uu___124_8415.is_native_tactic)
      }
let push_bv: env -> FStar_Syntax_Syntax.bv -> env =
  fun env  -> fun x  -> push_local_binding env (Binding_var x)
let pop_bv: env -> (FStar_Syntax_Syntax.bv* env) option =
  fun env  ->
    match env.gamma with
    | (Binding_var x)::rest ->
        Some
          (x,
            (let uu___125_8439 = env in
             {
               solver = (uu___125_8439.solver);
               range = (uu___125_8439.range);
               curmodule = (uu___125_8439.curmodule);
               gamma = rest;
               gamma_cache = (uu___125_8439.gamma_cache);
               modules = (uu___125_8439.modules);
               expected_typ = (uu___125_8439.expected_typ);
               sigtab = (uu___125_8439.sigtab);
               is_pattern = (uu___125_8439.is_pattern);
               instantiate_imp = (uu___125_8439.instantiate_imp);
               effects = (uu___125_8439.effects);
               generalize = (uu___125_8439.generalize);
               letrecs = (uu___125_8439.letrecs);
               top_level = (uu___125_8439.top_level);
               check_uvars = (uu___125_8439.check_uvars);
               use_eq = (uu___125_8439.use_eq);
               is_iface = (uu___125_8439.is_iface);
               admit = (uu___125_8439.admit);
               lax = (uu___125_8439.lax);
               lax_universes = (uu___125_8439.lax_universes);
               type_of = (uu___125_8439.type_of);
               universe_of = (uu___125_8439.universe_of);
               use_bv_sorts = (uu___125_8439.use_bv_sorts);
               qname_and_index = (uu___125_8439.qname_and_index);
               proof_ns = (uu___125_8439.proof_ns);
               synth = (uu___125_8439.synth);
               is_native_tactic = (uu___125_8439.is_native_tactic)
             }))
    | uu____8440 -> None
let push_binders: env -> FStar_Syntax_Syntax.binders -> env =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____8455  ->
             match uu____8455 with | (x,uu____8459) -> push_bv env1 x) env bs
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
            let uu___126_8481 = x1 in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___126_8481.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___126_8481.FStar_Syntax_Syntax.index);
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
      (let uu___127_8516 = env in
       {
         solver = (uu___127_8516.solver);
         range = (uu___127_8516.range);
         curmodule = (uu___127_8516.curmodule);
         gamma = [];
         gamma_cache = (uu___127_8516.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = None;
         sigtab = (uu___127_8516.sigtab);
         is_pattern = (uu___127_8516.is_pattern);
         instantiate_imp = (uu___127_8516.instantiate_imp);
         effects = (uu___127_8516.effects);
         generalize = (uu___127_8516.generalize);
         letrecs = (uu___127_8516.letrecs);
         top_level = (uu___127_8516.top_level);
         check_uvars = (uu___127_8516.check_uvars);
         use_eq = (uu___127_8516.use_eq);
         is_iface = (uu___127_8516.is_iface);
         admit = (uu___127_8516.admit);
         lax = (uu___127_8516.lax);
         lax_universes = (uu___127_8516.lax_universes);
         type_of = (uu___127_8516.type_of);
         universe_of = (uu___127_8516.universe_of);
         use_bv_sorts = (uu___127_8516.use_bv_sorts);
         qname_and_index = (uu___127_8516.qname_and_index);
         proof_ns = (uu___127_8516.proof_ns);
         synth = (uu___127_8516.synth);
         is_native_tactic = (uu___127_8516.is_native_tactic)
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
        let uu____8545 = FStar_Syntax_Subst.univ_var_opening uvs in
        match uu____8545 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars in
            let uu____8561 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms in
            (env', univ_vars, uu____8561)
let set_expected_typ: env -> FStar_Syntax_Syntax.typ -> env =
  fun env  ->
    fun t  ->
      let uu___128_8573 = env in
      {
        solver = (uu___128_8573.solver);
        range = (uu___128_8573.range);
        curmodule = (uu___128_8573.curmodule);
        gamma = (uu___128_8573.gamma);
        gamma_cache = (uu___128_8573.gamma_cache);
        modules = (uu___128_8573.modules);
        expected_typ = (Some t);
        sigtab = (uu___128_8573.sigtab);
        is_pattern = (uu___128_8573.is_pattern);
        instantiate_imp = (uu___128_8573.instantiate_imp);
        effects = (uu___128_8573.effects);
        generalize = (uu___128_8573.generalize);
        letrecs = (uu___128_8573.letrecs);
        top_level = (uu___128_8573.top_level);
        check_uvars = (uu___128_8573.check_uvars);
        use_eq = false;
        is_iface = (uu___128_8573.is_iface);
        admit = (uu___128_8573.admit);
        lax = (uu___128_8573.lax);
        lax_universes = (uu___128_8573.lax_universes);
        type_of = (uu___128_8573.type_of);
        universe_of = (uu___128_8573.universe_of);
        use_bv_sorts = (uu___128_8573.use_bv_sorts);
        qname_and_index = (uu___128_8573.qname_and_index);
        proof_ns = (uu___128_8573.proof_ns);
        synth = (uu___128_8573.synth);
        is_native_tactic = (uu___128_8573.is_native_tactic)
      }
let expected_typ: env -> FStar_Syntax_Syntax.typ option =
  fun env  -> match env.expected_typ with | None  -> None | Some t -> Some t
let clear_expected_typ: env -> (env* FStar_Syntax_Syntax.typ option) =
  fun env_  ->
    let uu____8591 = expected_typ env_ in
    ((let uu___129_8594 = env_ in
      {
        solver = (uu___129_8594.solver);
        range = (uu___129_8594.range);
        curmodule = (uu___129_8594.curmodule);
        gamma = (uu___129_8594.gamma);
        gamma_cache = (uu___129_8594.gamma_cache);
        modules = (uu___129_8594.modules);
        expected_typ = None;
        sigtab = (uu___129_8594.sigtab);
        is_pattern = (uu___129_8594.is_pattern);
        instantiate_imp = (uu___129_8594.instantiate_imp);
        effects = (uu___129_8594.effects);
        generalize = (uu___129_8594.generalize);
        letrecs = (uu___129_8594.letrecs);
        top_level = (uu___129_8594.top_level);
        check_uvars = (uu___129_8594.check_uvars);
        use_eq = false;
        is_iface = (uu___129_8594.is_iface);
        admit = (uu___129_8594.admit);
        lax = (uu___129_8594.lax);
        lax_universes = (uu___129_8594.lax_universes);
        type_of = (uu___129_8594.type_of);
        universe_of = (uu___129_8594.universe_of);
        use_bv_sorts = (uu___129_8594.use_bv_sorts);
        qname_and_index = (uu___129_8594.qname_and_index);
        proof_ns = (uu___129_8594.proof_ns);
        synth = (uu___129_8594.synth);
        is_native_tactic = (uu___129_8594.is_native_tactic)
      }), uu____8591)
let finish_module: env -> FStar_Syntax_Syntax.modul -> env =
  let empty_lid = FStar_Ident.lid_of_ids [FStar_Ident.id_of_text ""] in
  fun env  ->
    fun m  ->
      let sigs =
        if
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Syntax_Const.prims_lid
        then
          let uu____8607 =
            FStar_All.pipe_right env.gamma
              (FStar_List.collect
                 (fun uu___108_8611  ->
                    match uu___108_8611 with
                    | Binding_sig (uu____8613,se) -> [se]
                    | uu____8617 -> [])) in
          FStar_All.pipe_right uu____8607 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports in
      add_sigelts env sigs;
      (let uu___130_8622 = env in
       {
         solver = (uu___130_8622.solver);
         range = (uu___130_8622.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_cache = (uu___130_8622.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___130_8622.expected_typ);
         sigtab = (uu___130_8622.sigtab);
         is_pattern = (uu___130_8622.is_pattern);
         instantiate_imp = (uu___130_8622.instantiate_imp);
         effects = (uu___130_8622.effects);
         generalize = (uu___130_8622.generalize);
         letrecs = (uu___130_8622.letrecs);
         top_level = (uu___130_8622.top_level);
         check_uvars = (uu___130_8622.check_uvars);
         use_eq = (uu___130_8622.use_eq);
         is_iface = (uu___130_8622.is_iface);
         admit = (uu___130_8622.admit);
         lax = (uu___130_8622.lax);
         lax_universes = (uu___130_8622.lax_universes);
         type_of = (uu___130_8622.type_of);
         universe_of = (uu___130_8622.universe_of);
         use_bv_sorts = (uu___130_8622.use_bv_sorts);
         qname_and_index = (uu___130_8622.qname_and_index);
         proof_ns = (uu___130_8622.proof_ns);
         synth = (uu___130_8622.synth);
         is_native_tactic = (uu___130_8622.is_native_tactic)
       })
let uvars_in_env:
  env -> (FStar_Syntax_Syntax.uvar* FStar_Syntax_Syntax.typ) FStar_Util.set =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_univ uu____8673)::tl1 -> aux out tl1
      | (Binding_lid (uu____8676,(uu____8677,t)))::tl1 ->
          let uu____8686 =
            let uu____8690 = FStar_Syntax_Free.uvars t in ext out uu____8690 in
          aux uu____8686 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____8694;
            FStar_Syntax_Syntax.index = uu____8695;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____8701 =
            let uu____8705 = FStar_Syntax_Free.uvars t in ext out uu____8705 in
          aux uu____8701 tl1
      | (Binding_sig uu____8709)::uu____8710 -> out
      | (Binding_sig_inst uu____8715)::uu____8716 -> out in
    aux no_uvs env.gamma
let univ_vars: env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____8754)::tl1 -> aux out tl1
      | (Binding_univ uu____8761)::tl1 -> aux out tl1
      | (Binding_lid (uu____8764,(uu____8765,t)))::tl1 ->
          let uu____8774 =
            let uu____8776 = FStar_Syntax_Free.univs t in ext out uu____8776 in
          aux uu____8774 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____8778;
            FStar_Syntax_Syntax.index = uu____8779;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____8785 =
            let uu____8787 = FStar_Syntax_Free.univs t in ext out uu____8787 in
          aux uu____8785 tl1
      | (Binding_sig uu____8789)::uu____8790 -> out in
    aux no_univs env.gamma
let univnames: env -> FStar_Syntax_Syntax.univ_name FStar_Util.set =
  fun env  ->
    let no_univ_names = FStar_Syntax_Syntax.no_universe_names in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____8828)::tl1 -> aux out tl1
      | (Binding_univ uname)::tl1 ->
          let uu____8838 = FStar_Util.set_add uname out in aux uu____8838 tl1
      | (Binding_lid (uu____8840,(uu____8841,t)))::tl1 ->
          let uu____8850 =
            let uu____8852 = FStar_Syntax_Free.univnames t in
            ext out uu____8852 in
          aux uu____8850 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____8854;
            FStar_Syntax_Syntax.index = uu____8855;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____8861 =
            let uu____8863 = FStar_Syntax_Free.univnames t in
            ext out uu____8863 in
          aux uu____8861 tl1
      | (Binding_sig uu____8865)::uu____8866 -> out in
    aux no_univ_names env.gamma
let bound_vars_of_bindings:
  binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___109_8883  ->
            match uu___109_8883 with
            | Binding_var x -> [x]
            | Binding_lid uu____8886 -> []
            | Binding_sig uu____8889 -> []
            | Binding_univ uu____8893 -> []
            | Binding_sig_inst uu____8894 -> []))
let binders_of_bindings:
  binding Prims.list -> FStar_Syntax_Syntax.binder Prims.list =
  fun bs  ->
    let uu____8905 =
      let uu____8907 = bound_vars_of_bindings bs in
      FStar_All.pipe_right uu____8907
        (FStar_List.map FStar_Syntax_Syntax.mk_binder) in
    FStar_All.pipe_right uu____8905 FStar_List.rev
let bound_vars: env -> FStar_Syntax_Syntax.bv Prims.list =
  fun env  -> bound_vars_of_bindings env.gamma
let all_binders: env -> FStar_Syntax_Syntax.binders =
  fun env  -> binders_of_bindings env.gamma
let print_gamma: env -> Prims.unit =
  fun env  ->
    let uu____8926 =
      let uu____8927 =
        FStar_All.pipe_right env.gamma
          (FStar_List.map
             (fun uu___110_8931  ->
                match uu___110_8931 with
                | Binding_var x ->
                    let uu____8933 = FStar_Syntax_Print.bv_to_string x in
                    Prims.strcat "Binding_var " uu____8933
                | Binding_univ u ->
                    Prims.strcat "Binding_univ " u.FStar_Ident.idText
                | Binding_lid (l,uu____8936) ->
                    let uu____8937 = FStar_Ident.string_of_lid l in
                    Prims.strcat "Binding_lid " uu____8937
                | Binding_sig (ls,uu____8939) ->
                    let uu____8942 =
                      let uu____8943 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____8943
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig " uu____8942
                | Binding_sig_inst (ls,uu____8949,uu____8950) ->
                    let uu____8953 =
                      let uu____8954 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____8954
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig_inst " uu____8953)) in
      FStar_All.pipe_right uu____8927 (FStar_String.concat "::\n") in
    FStar_All.pipe_right uu____8926 (FStar_Util.print1 "%s\n")
let eq_gamma: env -> env -> Prims.bool =
  fun env  ->
    fun env'  ->
      let uu____8968 = FStar_Util.physical_equality env.gamma env'.gamma in
      if uu____8968
      then true
      else
        (let g = all_binders env in
         let g' = all_binders env' in
         ((FStar_List.length g) = (FStar_List.length g')) &&
           (FStar_List.forall2
              (fun uu____8989  ->
                 fun uu____8990  ->
                   match (uu____8989, uu____8990) with
                   | ((b1,uu____9000),(b2,uu____9002)) ->
                       FStar_Syntax_Syntax.bv_eq b1 b2) g g'))
let fold_env env f a =
  FStar_List.fold_right (fun e  -> fun a1  -> f a1 e) env.gamma a
let lidents: env -> FStar_Ident.lident Prims.list =
  fun env  ->
    let keys =
      FStar_List.fold_left
        (fun keys  ->
           fun uu___111_9050  ->
             match uu___111_9050 with
             | Binding_sig (lids,uu____9054) -> FStar_List.append lids keys
             | uu____9057 -> keys) [] env.gamma in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____9059  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
let should_enc_path: env -> Prims.string Prims.list -> Prims.bool =
  fun env  ->
    fun path  ->
      let rec list_prefix xs ys =
        match (xs, ys) with
        | ([],uu____9086) -> true
        | (x::xs1,y::ys1) -> (x = y) && (list_prefix xs1 ys1)
        | (uu____9098,uu____9099) -> false in
      let rec should_enc_path' pns path1 =
        match pns with
        | [] -> true
        | (p,b)::pns1 ->
            let uu____9123 = list_prefix p path1 in
            if uu____9123 then b else should_enc_path' pns1 path1 in
      should_enc_path' (FStar_List.flatten env.proof_ns) path
let should_enc_lid: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____9135 = FStar_Ident.path_of_lid lid in
      should_enc_path env uu____9135
let cons_proof_ns: Prims.bool -> env -> name_prefix -> env =
  fun b  ->
    fun e  ->
      fun path  ->
        match e.proof_ns with
        | [] -> failwith "empty proof_ns stack!"
        | pns::rest ->
            let pns' = (path, b) :: pns in
            let uu___131_9158 = e in
            {
              solver = (uu___131_9158.solver);
              range = (uu___131_9158.range);
              curmodule = (uu___131_9158.curmodule);
              gamma = (uu___131_9158.gamma);
              gamma_cache = (uu___131_9158.gamma_cache);
              modules = (uu___131_9158.modules);
              expected_typ = (uu___131_9158.expected_typ);
              sigtab = (uu___131_9158.sigtab);
              is_pattern = (uu___131_9158.is_pattern);
              instantiate_imp = (uu___131_9158.instantiate_imp);
              effects = (uu___131_9158.effects);
              generalize = (uu___131_9158.generalize);
              letrecs = (uu___131_9158.letrecs);
              top_level = (uu___131_9158.top_level);
              check_uvars = (uu___131_9158.check_uvars);
              use_eq = (uu___131_9158.use_eq);
              is_iface = (uu___131_9158.is_iface);
              admit = (uu___131_9158.admit);
              lax = (uu___131_9158.lax);
              lax_universes = (uu___131_9158.lax_universes);
              type_of = (uu___131_9158.type_of);
              universe_of = (uu___131_9158.universe_of);
              use_bv_sorts = (uu___131_9158.use_bv_sorts);
              qname_and_index = (uu___131_9158.qname_and_index);
              proof_ns = (pns' :: rest);
              synth = (uu___131_9158.synth);
              is_native_tactic = (uu___131_9158.is_native_tactic)
            }
let add_proof_ns: env -> name_prefix -> env =
  fun e  -> fun path  -> cons_proof_ns true e path
let rem_proof_ns: env -> name_prefix -> env =
  fun e  -> fun path  -> cons_proof_ns false e path
let push_proof_ns: env -> env =
  fun e  ->
    let uu___132_9182 = e in
    {
      solver = (uu___132_9182.solver);
      range = (uu___132_9182.range);
      curmodule = (uu___132_9182.curmodule);
      gamma = (uu___132_9182.gamma);
      gamma_cache = (uu___132_9182.gamma_cache);
      modules = (uu___132_9182.modules);
      expected_typ = (uu___132_9182.expected_typ);
      sigtab = (uu___132_9182.sigtab);
      is_pattern = (uu___132_9182.is_pattern);
      instantiate_imp = (uu___132_9182.instantiate_imp);
      effects = (uu___132_9182.effects);
      generalize = (uu___132_9182.generalize);
      letrecs = (uu___132_9182.letrecs);
      top_level = (uu___132_9182.top_level);
      check_uvars = (uu___132_9182.check_uvars);
      use_eq = (uu___132_9182.use_eq);
      is_iface = (uu___132_9182.is_iface);
      admit = (uu___132_9182.admit);
      lax = (uu___132_9182.lax);
      lax_universes = (uu___132_9182.lax_universes);
      type_of = (uu___132_9182.type_of);
      universe_of = (uu___132_9182.universe_of);
      use_bv_sorts = (uu___132_9182.use_bv_sorts);
      qname_and_index = (uu___132_9182.qname_and_index);
      proof_ns = ([] :: (e.proof_ns));
      synth = (uu___132_9182.synth);
      is_native_tactic = (uu___132_9182.is_native_tactic)
    }
let pop_proof_ns: env -> env =
  fun e  ->
    match e.proof_ns with
    | [] -> failwith "empty proof_ns stack!"
    | uu____9192::rest ->
        let uu___133_9195 = e in
        {
          solver = (uu___133_9195.solver);
          range = (uu___133_9195.range);
          curmodule = (uu___133_9195.curmodule);
          gamma = (uu___133_9195.gamma);
          gamma_cache = (uu___133_9195.gamma_cache);
          modules = (uu___133_9195.modules);
          expected_typ = (uu___133_9195.expected_typ);
          sigtab = (uu___133_9195.sigtab);
          is_pattern = (uu___133_9195.is_pattern);
          instantiate_imp = (uu___133_9195.instantiate_imp);
          effects = (uu___133_9195.effects);
          generalize = (uu___133_9195.generalize);
          letrecs = (uu___133_9195.letrecs);
          top_level = (uu___133_9195.top_level);
          check_uvars = (uu___133_9195.check_uvars);
          use_eq = (uu___133_9195.use_eq);
          is_iface = (uu___133_9195.is_iface);
          admit = (uu___133_9195.admit);
          lax = (uu___133_9195.lax);
          lax_universes = (uu___133_9195.lax_universes);
          type_of = (uu___133_9195.type_of);
          universe_of = (uu___133_9195.universe_of);
          use_bv_sorts = (uu___133_9195.use_bv_sorts);
          qname_and_index = (uu___133_9195.qname_and_index);
          proof_ns = rest;
          synth = (uu___133_9195.synth);
          is_native_tactic = (uu___133_9195.is_native_tactic)
        }
let get_proof_ns: env -> proof_namespace = fun e  -> e.proof_ns
let set_proof_ns: proof_namespace -> env -> env =
  fun ns  ->
    fun e  ->
      let uu___134_9208 = e in
      {
        solver = (uu___134_9208.solver);
        range = (uu___134_9208.range);
        curmodule = (uu___134_9208.curmodule);
        gamma = (uu___134_9208.gamma);
        gamma_cache = (uu___134_9208.gamma_cache);
        modules = (uu___134_9208.modules);
        expected_typ = (uu___134_9208.expected_typ);
        sigtab = (uu___134_9208.sigtab);
        is_pattern = (uu___134_9208.is_pattern);
        instantiate_imp = (uu___134_9208.instantiate_imp);
        effects = (uu___134_9208.effects);
        generalize = (uu___134_9208.generalize);
        letrecs = (uu___134_9208.letrecs);
        top_level = (uu___134_9208.top_level);
        check_uvars = (uu___134_9208.check_uvars);
        use_eq = (uu___134_9208.use_eq);
        is_iface = (uu___134_9208.is_iface);
        admit = (uu___134_9208.admit);
        lax = (uu___134_9208.lax);
        lax_universes = (uu___134_9208.lax_universes);
        type_of = (uu___134_9208.type_of);
        universe_of = (uu___134_9208.universe_of);
        use_bv_sorts = (uu___134_9208.use_bv_sorts);
        qname_and_index = (uu___134_9208.qname_and_index);
        proof_ns = ns;
        synth = (uu___134_9208.synth);
        is_native_tactic = (uu___134_9208.is_native_tactic)
      }
let string_of_proof_ns: env -> Prims.string =
  fun env  ->
    let string_of_proof_ns' pns =
      let uu____9227 =
        FStar_List.map
          (fun fpns  ->
             let uu____9238 =
               let uu____9239 =
                 let uu____9240 =
                   FStar_List.map
                     (fun uu____9245  ->
                        match uu____9245 with
                        | (p,b) ->
                            Prims.strcat (if b then "+" else "-")
                              (FStar_String.concat "." p)) fpns in
                 FStar_String.concat "," uu____9240 in
               Prims.strcat uu____9239 "]" in
             Prims.strcat "[" uu____9238) pns in
      FStar_String.concat ";" uu____9227 in
    string_of_proof_ns' env.proof_ns
let dummy_solver: solver_t =
  {
    init = (fun uu____9254  -> ());
    push = (fun uu____9255  -> ());
    pop = (fun uu____9256  -> ());
    mark = (fun uu____9257  -> ());
    reset_mark = (fun uu____9258  -> ());
    commit_mark = (fun uu____9259  -> ());
    encode_modul = (fun uu____9260  -> fun uu____9261  -> ());
    encode_sig = (fun uu____9262  -> fun uu____9263  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____9266 =
             let uu____9270 = FStar_Options.peek () in (e, g, uu____9270) in
           [uu____9266]);
    solve = (fun uu____9277  -> fun uu____9278  -> fun uu____9279  -> ());
    is_trivial = (fun uu____9283  -> fun uu____9284  -> false);
    finish = (fun uu____9285  -> ());
    refresh = (fun uu____9286  -> ())
  }