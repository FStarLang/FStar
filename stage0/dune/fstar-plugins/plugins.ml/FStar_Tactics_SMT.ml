open Fstarcompiler
open Prims
let smt_sync (uu___ : unit) : (unit, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = FStarC_Tactics_V2_Builtins.get_vconfig () ps in
    FStarC_Tactics_V2_Builtins.t_smt_sync x ps
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.SMT.smt_sync" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.SMT.smt_sync (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_1 smt_sync)
               Fstarcompiler.FStarC_Syntax_Embeddings.e_unit
               Fstarcompiler.FStarC_Syntax_Embeddings.e_unit psc ncb us args)
let smt_sync' (fuel : Prims.nat) (ifuel : Prims.nat) :
  (unit, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = FStarC_Tactics_V2_Builtins.get_vconfig () ps in
    let x1 =
      {
        FStarC_VConfig.initial_fuel = fuel;
        FStarC_VConfig.max_fuel = fuel;
        FStarC_VConfig.initial_ifuel = ifuel;
        FStarC_VConfig.max_ifuel = ifuel;
        FStarC_VConfig.detail_errors = (x.FStarC_VConfig.detail_errors);
        FStarC_VConfig.detail_hint_replay =
          (x.FStarC_VConfig.detail_hint_replay);
        FStarC_VConfig.no_smt = (x.FStarC_VConfig.no_smt);
        FStarC_VConfig.quake_lo = (x.FStarC_VConfig.quake_lo);
        FStarC_VConfig.quake_hi = (x.FStarC_VConfig.quake_hi);
        FStarC_VConfig.quake_keep = (x.FStarC_VConfig.quake_keep);
        FStarC_VConfig.retry = (x.FStarC_VConfig.retry);
        FStarC_VConfig.smtencoding_elim_box =
          (x.FStarC_VConfig.smtencoding_elim_box);
        FStarC_VConfig.smtencoding_nl_arith_repr =
          (x.FStarC_VConfig.smtencoding_nl_arith_repr);
        FStarC_VConfig.smtencoding_l_arith_repr =
          (x.FStarC_VConfig.smtencoding_l_arith_repr);
        FStarC_VConfig.smtencoding_valid_intro =
          (x.FStarC_VConfig.smtencoding_valid_intro);
        FStarC_VConfig.smtencoding_valid_elim =
          (x.FStarC_VConfig.smtencoding_valid_elim);
        FStarC_VConfig.tcnorm = (x.FStarC_VConfig.tcnorm);
        FStarC_VConfig.no_plugins = (x.FStarC_VConfig.no_plugins);
        FStarC_VConfig.no_tactics = (x.FStarC_VConfig.no_tactics);
        FStarC_VConfig.z3cliopt = (x.FStarC_VConfig.z3cliopt);
        FStarC_VConfig.z3smtopt = (x.FStarC_VConfig.z3smtopt);
        FStarC_VConfig.z3refresh = (x.FStarC_VConfig.z3refresh);
        FStarC_VConfig.z3rlimit = (x.FStarC_VConfig.z3rlimit);
        FStarC_VConfig.z3rlimit_factor = (x.FStarC_VConfig.z3rlimit_factor);
        FStarC_VConfig.z3seed = (x.FStarC_VConfig.z3seed);
        FStarC_VConfig.z3version = (x.FStarC_VConfig.z3version);
        FStarC_VConfig.trivial_pre_for_unannotated_effectful_fns =
          (x.FStarC_VConfig.trivial_pre_for_unannotated_effectful_fns);
        FStarC_VConfig.reuse_hint_for = (x.FStarC_VConfig.reuse_hint_for)
      } in
    FStarC_Tactics_V2_Builtins.t_smt_sync x1 ps
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.SMT.smt_sync'" (Prims.of_int (3))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_2
               "FStar.Tactics.SMT.smt_sync' (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_2 smt_sync')
               Fstarcompiler.FStarC_Syntax_Embeddings.e_int
               Fstarcompiler.FStarC_Syntax_Embeddings.e_int
               Fstarcompiler.FStarC_Syntax_Embeddings.e_unit psc ncb us args)
let get_rlimit (uu___ : unit) :
  (Prims.int, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = FStarC_Tactics_V2_Builtins.get_vconfig () ps in
    x.FStarC_VConfig.z3rlimit
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.SMT.get_rlimit" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.SMT.get_rlimit (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_1 get_rlimit)
               Fstarcompiler.FStarC_Syntax_Embeddings.e_unit
               Fstarcompiler.FStarC_Syntax_Embeddings.e_int psc ncb us args)
let set_rlimit (v : Prims.int) : (unit, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x =
      let x1 = FStarC_Tactics_V2_Builtins.get_vconfig () ps in
      {
        FStarC_VConfig.initial_fuel = (x1.FStarC_VConfig.initial_fuel);
        FStarC_VConfig.max_fuel = (x1.FStarC_VConfig.max_fuel);
        FStarC_VConfig.initial_ifuel = (x1.FStarC_VConfig.initial_ifuel);
        FStarC_VConfig.max_ifuel = (x1.FStarC_VConfig.max_ifuel);
        FStarC_VConfig.detail_errors = (x1.FStarC_VConfig.detail_errors);
        FStarC_VConfig.detail_hint_replay =
          (x1.FStarC_VConfig.detail_hint_replay);
        FStarC_VConfig.no_smt = (x1.FStarC_VConfig.no_smt);
        FStarC_VConfig.quake_lo = (x1.FStarC_VConfig.quake_lo);
        FStarC_VConfig.quake_hi = (x1.FStarC_VConfig.quake_hi);
        FStarC_VConfig.quake_keep = (x1.FStarC_VConfig.quake_keep);
        FStarC_VConfig.retry = (x1.FStarC_VConfig.retry);
        FStarC_VConfig.smtencoding_elim_box =
          (x1.FStarC_VConfig.smtencoding_elim_box);
        FStarC_VConfig.smtencoding_nl_arith_repr =
          (x1.FStarC_VConfig.smtencoding_nl_arith_repr);
        FStarC_VConfig.smtencoding_l_arith_repr =
          (x1.FStarC_VConfig.smtencoding_l_arith_repr);
        FStarC_VConfig.smtencoding_valid_intro =
          (x1.FStarC_VConfig.smtencoding_valid_intro);
        FStarC_VConfig.smtencoding_valid_elim =
          (x1.FStarC_VConfig.smtencoding_valid_elim);
        FStarC_VConfig.tcnorm = (x1.FStarC_VConfig.tcnorm);
        FStarC_VConfig.no_plugins = (x1.FStarC_VConfig.no_plugins);
        FStarC_VConfig.no_tactics = (x1.FStarC_VConfig.no_tactics);
        FStarC_VConfig.z3cliopt = (x1.FStarC_VConfig.z3cliopt);
        FStarC_VConfig.z3smtopt = (x1.FStarC_VConfig.z3smtopt);
        FStarC_VConfig.z3refresh = (x1.FStarC_VConfig.z3refresh);
        FStarC_VConfig.z3rlimit = v;
        FStarC_VConfig.z3rlimit_factor = (x1.FStarC_VConfig.z3rlimit_factor);
        FStarC_VConfig.z3seed = (x1.FStarC_VConfig.z3seed);
        FStarC_VConfig.z3version = (x1.FStarC_VConfig.z3version);
        FStarC_VConfig.trivial_pre_for_unannotated_effectful_fns =
          (x1.FStarC_VConfig.trivial_pre_for_unannotated_effectful_fns);
        FStarC_VConfig.reuse_hint_for = (x1.FStarC_VConfig.reuse_hint_for)
      } in
    FStarC_Tactics_V2_Builtins.set_vconfig x ps
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.SMT.set_rlimit" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.SMT.set_rlimit (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_1 set_rlimit)
               Fstarcompiler.FStarC_Syntax_Embeddings.e_int
               Fstarcompiler.FStarC_Syntax_Embeddings.e_unit psc ncb us args)
let get_initial_fuel (uu___ : unit) :
  (Prims.int, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = FStarC_Tactics_V2_Builtins.get_vconfig () ps in
    x.FStarC_VConfig.initial_fuel
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.SMT.get_initial_fuel" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.SMT.get_initial_fuel (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_1
                  get_initial_fuel)
               Fstarcompiler.FStarC_Syntax_Embeddings.e_unit
               Fstarcompiler.FStarC_Syntax_Embeddings.e_int psc ncb us args)
let get_initial_ifuel (uu___ : unit) :
  (Prims.int, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = FStarC_Tactics_V2_Builtins.get_vconfig () ps in
    x.FStarC_VConfig.initial_ifuel
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.SMT.get_initial_ifuel" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.SMT.get_initial_ifuel (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_1
                  get_initial_ifuel)
               Fstarcompiler.FStarC_Syntax_Embeddings.e_unit
               Fstarcompiler.FStarC_Syntax_Embeddings.e_int psc ncb us args)
let get_max_fuel (uu___ : unit) :
  (Prims.int, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = FStarC_Tactics_V2_Builtins.get_vconfig () ps in
    x.FStarC_VConfig.max_fuel
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.SMT.get_max_fuel" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.SMT.get_max_fuel (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_1
                  get_max_fuel) Fstarcompiler.FStarC_Syntax_Embeddings.e_unit
               Fstarcompiler.FStarC_Syntax_Embeddings.e_int psc ncb us args)
let get_max_ifuel (uu___ : unit) :
  (Prims.int, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = FStarC_Tactics_V2_Builtins.get_vconfig () ps in
    x.FStarC_VConfig.max_ifuel
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.SMT.get_max_ifuel" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.SMT.get_max_ifuel (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_1
                  get_max_ifuel)
               Fstarcompiler.FStarC_Syntax_Embeddings.e_unit
               Fstarcompiler.FStarC_Syntax_Embeddings.e_int psc ncb us args)
let set_initial_fuel (v : Prims.int) :
  (unit, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x =
      let x1 = FStarC_Tactics_V2_Builtins.get_vconfig () ps in
      {
        FStarC_VConfig.initial_fuel = v;
        FStarC_VConfig.max_fuel = (x1.FStarC_VConfig.max_fuel);
        FStarC_VConfig.initial_ifuel = (x1.FStarC_VConfig.initial_ifuel);
        FStarC_VConfig.max_ifuel = (x1.FStarC_VConfig.max_ifuel);
        FStarC_VConfig.detail_errors = (x1.FStarC_VConfig.detail_errors);
        FStarC_VConfig.detail_hint_replay =
          (x1.FStarC_VConfig.detail_hint_replay);
        FStarC_VConfig.no_smt = (x1.FStarC_VConfig.no_smt);
        FStarC_VConfig.quake_lo = (x1.FStarC_VConfig.quake_lo);
        FStarC_VConfig.quake_hi = (x1.FStarC_VConfig.quake_hi);
        FStarC_VConfig.quake_keep = (x1.FStarC_VConfig.quake_keep);
        FStarC_VConfig.retry = (x1.FStarC_VConfig.retry);
        FStarC_VConfig.smtencoding_elim_box =
          (x1.FStarC_VConfig.smtencoding_elim_box);
        FStarC_VConfig.smtencoding_nl_arith_repr =
          (x1.FStarC_VConfig.smtencoding_nl_arith_repr);
        FStarC_VConfig.smtencoding_l_arith_repr =
          (x1.FStarC_VConfig.smtencoding_l_arith_repr);
        FStarC_VConfig.smtencoding_valid_intro =
          (x1.FStarC_VConfig.smtencoding_valid_intro);
        FStarC_VConfig.smtencoding_valid_elim =
          (x1.FStarC_VConfig.smtencoding_valid_elim);
        FStarC_VConfig.tcnorm = (x1.FStarC_VConfig.tcnorm);
        FStarC_VConfig.no_plugins = (x1.FStarC_VConfig.no_plugins);
        FStarC_VConfig.no_tactics = (x1.FStarC_VConfig.no_tactics);
        FStarC_VConfig.z3cliopt = (x1.FStarC_VConfig.z3cliopt);
        FStarC_VConfig.z3smtopt = (x1.FStarC_VConfig.z3smtopt);
        FStarC_VConfig.z3refresh = (x1.FStarC_VConfig.z3refresh);
        FStarC_VConfig.z3rlimit = (x1.FStarC_VConfig.z3rlimit);
        FStarC_VConfig.z3rlimit_factor = (x1.FStarC_VConfig.z3rlimit_factor);
        FStarC_VConfig.z3seed = (x1.FStarC_VConfig.z3seed);
        FStarC_VConfig.z3version = (x1.FStarC_VConfig.z3version);
        FStarC_VConfig.trivial_pre_for_unannotated_effectful_fns =
          (x1.FStarC_VConfig.trivial_pre_for_unannotated_effectful_fns);
        FStarC_VConfig.reuse_hint_for = (x1.FStarC_VConfig.reuse_hint_for)
      } in
    FStarC_Tactics_V2_Builtins.set_vconfig x ps
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.SMT.set_initial_fuel" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.SMT.set_initial_fuel (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_1
                  set_initial_fuel)
               Fstarcompiler.FStarC_Syntax_Embeddings.e_int
               Fstarcompiler.FStarC_Syntax_Embeddings.e_unit psc ncb us args)
let set_initial_ifuel (v : Prims.int) :
  (unit, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x =
      let x1 = FStarC_Tactics_V2_Builtins.get_vconfig () ps in
      {
        FStarC_VConfig.initial_fuel = (x1.FStarC_VConfig.initial_fuel);
        FStarC_VConfig.max_fuel = (x1.FStarC_VConfig.max_fuel);
        FStarC_VConfig.initial_ifuel = v;
        FStarC_VConfig.max_ifuel = (x1.FStarC_VConfig.max_ifuel);
        FStarC_VConfig.detail_errors = (x1.FStarC_VConfig.detail_errors);
        FStarC_VConfig.detail_hint_replay =
          (x1.FStarC_VConfig.detail_hint_replay);
        FStarC_VConfig.no_smt = (x1.FStarC_VConfig.no_smt);
        FStarC_VConfig.quake_lo = (x1.FStarC_VConfig.quake_lo);
        FStarC_VConfig.quake_hi = (x1.FStarC_VConfig.quake_hi);
        FStarC_VConfig.quake_keep = (x1.FStarC_VConfig.quake_keep);
        FStarC_VConfig.retry = (x1.FStarC_VConfig.retry);
        FStarC_VConfig.smtencoding_elim_box =
          (x1.FStarC_VConfig.smtencoding_elim_box);
        FStarC_VConfig.smtencoding_nl_arith_repr =
          (x1.FStarC_VConfig.smtencoding_nl_arith_repr);
        FStarC_VConfig.smtencoding_l_arith_repr =
          (x1.FStarC_VConfig.smtencoding_l_arith_repr);
        FStarC_VConfig.smtencoding_valid_intro =
          (x1.FStarC_VConfig.smtencoding_valid_intro);
        FStarC_VConfig.smtencoding_valid_elim =
          (x1.FStarC_VConfig.smtencoding_valid_elim);
        FStarC_VConfig.tcnorm = (x1.FStarC_VConfig.tcnorm);
        FStarC_VConfig.no_plugins = (x1.FStarC_VConfig.no_plugins);
        FStarC_VConfig.no_tactics = (x1.FStarC_VConfig.no_tactics);
        FStarC_VConfig.z3cliopt = (x1.FStarC_VConfig.z3cliopt);
        FStarC_VConfig.z3smtopt = (x1.FStarC_VConfig.z3smtopt);
        FStarC_VConfig.z3refresh = (x1.FStarC_VConfig.z3refresh);
        FStarC_VConfig.z3rlimit = (x1.FStarC_VConfig.z3rlimit);
        FStarC_VConfig.z3rlimit_factor = (x1.FStarC_VConfig.z3rlimit_factor);
        FStarC_VConfig.z3seed = (x1.FStarC_VConfig.z3seed);
        FStarC_VConfig.z3version = (x1.FStarC_VConfig.z3version);
        FStarC_VConfig.trivial_pre_for_unannotated_effectful_fns =
          (x1.FStarC_VConfig.trivial_pre_for_unannotated_effectful_fns);
        FStarC_VConfig.reuse_hint_for = (x1.FStarC_VConfig.reuse_hint_for)
      } in
    FStarC_Tactics_V2_Builtins.set_vconfig x ps
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.SMT.set_initial_ifuel" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.SMT.set_initial_ifuel (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_1
                  set_initial_ifuel)
               Fstarcompiler.FStarC_Syntax_Embeddings.e_int
               Fstarcompiler.FStarC_Syntax_Embeddings.e_unit psc ncb us args)
let set_max_fuel (v : Prims.int) :
  (unit, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x =
      let x1 = FStarC_Tactics_V2_Builtins.get_vconfig () ps in
      {
        FStarC_VConfig.initial_fuel = (x1.FStarC_VConfig.initial_fuel);
        FStarC_VConfig.max_fuel = v;
        FStarC_VConfig.initial_ifuel = (x1.FStarC_VConfig.initial_ifuel);
        FStarC_VConfig.max_ifuel = (x1.FStarC_VConfig.max_ifuel);
        FStarC_VConfig.detail_errors = (x1.FStarC_VConfig.detail_errors);
        FStarC_VConfig.detail_hint_replay =
          (x1.FStarC_VConfig.detail_hint_replay);
        FStarC_VConfig.no_smt = (x1.FStarC_VConfig.no_smt);
        FStarC_VConfig.quake_lo = (x1.FStarC_VConfig.quake_lo);
        FStarC_VConfig.quake_hi = (x1.FStarC_VConfig.quake_hi);
        FStarC_VConfig.quake_keep = (x1.FStarC_VConfig.quake_keep);
        FStarC_VConfig.retry = (x1.FStarC_VConfig.retry);
        FStarC_VConfig.smtencoding_elim_box =
          (x1.FStarC_VConfig.smtencoding_elim_box);
        FStarC_VConfig.smtencoding_nl_arith_repr =
          (x1.FStarC_VConfig.smtencoding_nl_arith_repr);
        FStarC_VConfig.smtencoding_l_arith_repr =
          (x1.FStarC_VConfig.smtencoding_l_arith_repr);
        FStarC_VConfig.smtencoding_valid_intro =
          (x1.FStarC_VConfig.smtencoding_valid_intro);
        FStarC_VConfig.smtencoding_valid_elim =
          (x1.FStarC_VConfig.smtencoding_valid_elim);
        FStarC_VConfig.tcnorm = (x1.FStarC_VConfig.tcnorm);
        FStarC_VConfig.no_plugins = (x1.FStarC_VConfig.no_plugins);
        FStarC_VConfig.no_tactics = (x1.FStarC_VConfig.no_tactics);
        FStarC_VConfig.z3cliopt = (x1.FStarC_VConfig.z3cliopt);
        FStarC_VConfig.z3smtopt = (x1.FStarC_VConfig.z3smtopt);
        FStarC_VConfig.z3refresh = (x1.FStarC_VConfig.z3refresh);
        FStarC_VConfig.z3rlimit = (x1.FStarC_VConfig.z3rlimit);
        FStarC_VConfig.z3rlimit_factor = (x1.FStarC_VConfig.z3rlimit_factor);
        FStarC_VConfig.z3seed = (x1.FStarC_VConfig.z3seed);
        FStarC_VConfig.z3version = (x1.FStarC_VConfig.z3version);
        FStarC_VConfig.trivial_pre_for_unannotated_effectful_fns =
          (x1.FStarC_VConfig.trivial_pre_for_unannotated_effectful_fns);
        FStarC_VConfig.reuse_hint_for = (x1.FStarC_VConfig.reuse_hint_for)
      } in
    FStarC_Tactics_V2_Builtins.set_vconfig x ps
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.SMT.set_max_fuel" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.SMT.set_max_fuel (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_1
                  set_max_fuel) Fstarcompiler.FStarC_Syntax_Embeddings.e_int
               Fstarcompiler.FStarC_Syntax_Embeddings.e_unit psc ncb us args)
let set_max_ifuel (v : Prims.int) :
  (unit, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x =
      let x1 = FStarC_Tactics_V2_Builtins.get_vconfig () ps in
      {
        FStarC_VConfig.initial_fuel = (x1.FStarC_VConfig.initial_fuel);
        FStarC_VConfig.max_fuel = (x1.FStarC_VConfig.max_fuel);
        FStarC_VConfig.initial_ifuel = (x1.FStarC_VConfig.initial_ifuel);
        FStarC_VConfig.max_ifuel = v;
        FStarC_VConfig.detail_errors = (x1.FStarC_VConfig.detail_errors);
        FStarC_VConfig.detail_hint_replay =
          (x1.FStarC_VConfig.detail_hint_replay);
        FStarC_VConfig.no_smt = (x1.FStarC_VConfig.no_smt);
        FStarC_VConfig.quake_lo = (x1.FStarC_VConfig.quake_lo);
        FStarC_VConfig.quake_hi = (x1.FStarC_VConfig.quake_hi);
        FStarC_VConfig.quake_keep = (x1.FStarC_VConfig.quake_keep);
        FStarC_VConfig.retry = (x1.FStarC_VConfig.retry);
        FStarC_VConfig.smtencoding_elim_box =
          (x1.FStarC_VConfig.smtencoding_elim_box);
        FStarC_VConfig.smtencoding_nl_arith_repr =
          (x1.FStarC_VConfig.smtencoding_nl_arith_repr);
        FStarC_VConfig.smtencoding_l_arith_repr =
          (x1.FStarC_VConfig.smtencoding_l_arith_repr);
        FStarC_VConfig.smtencoding_valid_intro =
          (x1.FStarC_VConfig.smtencoding_valid_intro);
        FStarC_VConfig.smtencoding_valid_elim =
          (x1.FStarC_VConfig.smtencoding_valid_elim);
        FStarC_VConfig.tcnorm = (x1.FStarC_VConfig.tcnorm);
        FStarC_VConfig.no_plugins = (x1.FStarC_VConfig.no_plugins);
        FStarC_VConfig.no_tactics = (x1.FStarC_VConfig.no_tactics);
        FStarC_VConfig.z3cliopt = (x1.FStarC_VConfig.z3cliopt);
        FStarC_VConfig.z3smtopt = (x1.FStarC_VConfig.z3smtopt);
        FStarC_VConfig.z3refresh = (x1.FStarC_VConfig.z3refresh);
        FStarC_VConfig.z3rlimit = (x1.FStarC_VConfig.z3rlimit);
        FStarC_VConfig.z3rlimit_factor = (x1.FStarC_VConfig.z3rlimit_factor);
        FStarC_VConfig.z3seed = (x1.FStarC_VConfig.z3seed);
        FStarC_VConfig.z3version = (x1.FStarC_VConfig.z3version);
        FStarC_VConfig.trivial_pre_for_unannotated_effectful_fns =
          (x1.FStarC_VConfig.trivial_pre_for_unannotated_effectful_fns);
        FStarC_VConfig.reuse_hint_for = (x1.FStarC_VConfig.reuse_hint_for)
      } in
    FStarC_Tactics_V2_Builtins.set_vconfig x ps
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.SMT.set_max_ifuel" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.SMT.set_max_ifuel (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_1
                  set_max_ifuel) Fstarcompiler.FStarC_Syntax_Embeddings.e_int
               Fstarcompiler.FStarC_Syntax_Embeddings.e_unit psc ncb us args)
let set_fuel (v : Prims.int) : (unit, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x =
      let x1 = FStarC_Tactics_V2_Builtins.get_vconfig () ps in
      {
        FStarC_VConfig.initial_fuel = v;
        FStarC_VConfig.max_fuel = v;
        FStarC_VConfig.initial_ifuel = (x1.FStarC_VConfig.initial_ifuel);
        FStarC_VConfig.max_ifuel = (x1.FStarC_VConfig.max_ifuel);
        FStarC_VConfig.detail_errors = (x1.FStarC_VConfig.detail_errors);
        FStarC_VConfig.detail_hint_replay =
          (x1.FStarC_VConfig.detail_hint_replay);
        FStarC_VConfig.no_smt = (x1.FStarC_VConfig.no_smt);
        FStarC_VConfig.quake_lo = (x1.FStarC_VConfig.quake_lo);
        FStarC_VConfig.quake_hi = (x1.FStarC_VConfig.quake_hi);
        FStarC_VConfig.quake_keep = (x1.FStarC_VConfig.quake_keep);
        FStarC_VConfig.retry = (x1.FStarC_VConfig.retry);
        FStarC_VConfig.smtencoding_elim_box =
          (x1.FStarC_VConfig.smtencoding_elim_box);
        FStarC_VConfig.smtencoding_nl_arith_repr =
          (x1.FStarC_VConfig.smtencoding_nl_arith_repr);
        FStarC_VConfig.smtencoding_l_arith_repr =
          (x1.FStarC_VConfig.smtencoding_l_arith_repr);
        FStarC_VConfig.smtencoding_valid_intro =
          (x1.FStarC_VConfig.smtencoding_valid_intro);
        FStarC_VConfig.smtencoding_valid_elim =
          (x1.FStarC_VConfig.smtencoding_valid_elim);
        FStarC_VConfig.tcnorm = (x1.FStarC_VConfig.tcnorm);
        FStarC_VConfig.no_plugins = (x1.FStarC_VConfig.no_plugins);
        FStarC_VConfig.no_tactics = (x1.FStarC_VConfig.no_tactics);
        FStarC_VConfig.z3cliopt = (x1.FStarC_VConfig.z3cliopt);
        FStarC_VConfig.z3smtopt = (x1.FStarC_VConfig.z3smtopt);
        FStarC_VConfig.z3refresh = (x1.FStarC_VConfig.z3refresh);
        FStarC_VConfig.z3rlimit = (x1.FStarC_VConfig.z3rlimit);
        FStarC_VConfig.z3rlimit_factor = (x1.FStarC_VConfig.z3rlimit_factor);
        FStarC_VConfig.z3seed = (x1.FStarC_VConfig.z3seed);
        FStarC_VConfig.z3version = (x1.FStarC_VConfig.z3version);
        FStarC_VConfig.trivial_pre_for_unannotated_effectful_fns =
          (x1.FStarC_VConfig.trivial_pre_for_unannotated_effectful_fns);
        FStarC_VConfig.reuse_hint_for = (x1.FStarC_VConfig.reuse_hint_for)
      } in
    FStarC_Tactics_V2_Builtins.set_vconfig x ps
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.SMT.set_fuel" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.SMT.set_fuel (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_1 set_fuel)
               Fstarcompiler.FStarC_Syntax_Embeddings.e_int
               Fstarcompiler.FStarC_Syntax_Embeddings.e_unit psc ncb us args)
let set_ifuel (v : Prims.int) : (unit, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x =
      let x1 = FStarC_Tactics_V2_Builtins.get_vconfig () ps in
      {
        FStarC_VConfig.initial_fuel = (x1.FStarC_VConfig.initial_fuel);
        FStarC_VConfig.max_fuel = (x1.FStarC_VConfig.max_fuel);
        FStarC_VConfig.initial_ifuel = v;
        FStarC_VConfig.max_ifuel = v;
        FStarC_VConfig.detail_errors = (x1.FStarC_VConfig.detail_errors);
        FStarC_VConfig.detail_hint_replay =
          (x1.FStarC_VConfig.detail_hint_replay);
        FStarC_VConfig.no_smt = (x1.FStarC_VConfig.no_smt);
        FStarC_VConfig.quake_lo = (x1.FStarC_VConfig.quake_lo);
        FStarC_VConfig.quake_hi = (x1.FStarC_VConfig.quake_hi);
        FStarC_VConfig.quake_keep = (x1.FStarC_VConfig.quake_keep);
        FStarC_VConfig.retry = (x1.FStarC_VConfig.retry);
        FStarC_VConfig.smtencoding_elim_box =
          (x1.FStarC_VConfig.smtencoding_elim_box);
        FStarC_VConfig.smtencoding_nl_arith_repr =
          (x1.FStarC_VConfig.smtencoding_nl_arith_repr);
        FStarC_VConfig.smtencoding_l_arith_repr =
          (x1.FStarC_VConfig.smtencoding_l_arith_repr);
        FStarC_VConfig.smtencoding_valid_intro =
          (x1.FStarC_VConfig.smtencoding_valid_intro);
        FStarC_VConfig.smtencoding_valid_elim =
          (x1.FStarC_VConfig.smtencoding_valid_elim);
        FStarC_VConfig.tcnorm = (x1.FStarC_VConfig.tcnorm);
        FStarC_VConfig.no_plugins = (x1.FStarC_VConfig.no_plugins);
        FStarC_VConfig.no_tactics = (x1.FStarC_VConfig.no_tactics);
        FStarC_VConfig.z3cliopt = (x1.FStarC_VConfig.z3cliopt);
        FStarC_VConfig.z3smtopt = (x1.FStarC_VConfig.z3smtopt);
        FStarC_VConfig.z3refresh = (x1.FStarC_VConfig.z3refresh);
        FStarC_VConfig.z3rlimit = (x1.FStarC_VConfig.z3rlimit);
        FStarC_VConfig.z3rlimit_factor = (x1.FStarC_VConfig.z3rlimit_factor);
        FStarC_VConfig.z3seed = (x1.FStarC_VConfig.z3seed);
        FStarC_VConfig.z3version = (x1.FStarC_VConfig.z3version);
        FStarC_VConfig.trivial_pre_for_unannotated_effectful_fns =
          (x1.FStarC_VConfig.trivial_pre_for_unannotated_effectful_fns);
        FStarC_VConfig.reuse_hint_for = (x1.FStarC_VConfig.reuse_hint_for)
      } in
    FStarC_Tactics_V2_Builtins.set_vconfig x ps
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.SMT.set_ifuel" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.SMT.set_ifuel (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_1 set_ifuel)
               Fstarcompiler.FStarC_Syntax_Embeddings.e_int
               Fstarcompiler.FStarC_Syntax_Embeddings.e_unit psc ncb us args)
