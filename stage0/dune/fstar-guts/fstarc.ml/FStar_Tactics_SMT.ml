open Prims
let smt_sync (uu___ : unit) : (unit, Obj.t) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = FStarC_Tactics_V2_Builtins.get_vconfig () ps in
    FStarC_Tactics_V2_Builtins.t_smt_sync x ps
let _ =
  FStarC_Tactics_Native.register_tactic "FStar.Tactics.SMT.smt_sync"
    (Prims.of_int 2)
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.SMT.smt_sync (plugin)"
               (FStarC_Tactics_Native.from_tactic_1 smt_sync)
               FStarC_Syntax_Embeddings.e_unit
               FStarC_Syntax_Embeddings.e_unit psc ncb us args)
let smt_sync' (fuel : Prims.nat) (ifuel : Prims.nat) :
  (unit, Obj.t) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = FStarC_Tactics_V2_Builtins.get_vconfig () ps in
    let x1 =
      {
        FStar_VConfig.initial_fuel = fuel;
        FStar_VConfig.max_fuel = fuel;
        FStar_VConfig.initial_ifuel = ifuel;
        FStar_VConfig.max_ifuel = ifuel;
        FStar_VConfig.detail_errors = (x.FStar_VConfig.detail_errors);
        FStar_VConfig.detail_hint_replay =
          (x.FStar_VConfig.detail_hint_replay);
        FStar_VConfig.no_smt = (x.FStar_VConfig.no_smt);
        FStar_VConfig.quake_lo = (x.FStar_VConfig.quake_lo);
        FStar_VConfig.quake_hi = (x.FStar_VConfig.quake_hi);
        FStar_VConfig.quake_keep = (x.FStar_VConfig.quake_keep);
        FStar_VConfig.retry = (x.FStar_VConfig.retry);
        FStar_VConfig.smtencoding_elim_box =
          (x.FStar_VConfig.smtencoding_elim_box);
        FStar_VConfig.smtencoding_nl_arith_repr =
          (x.FStar_VConfig.smtencoding_nl_arith_repr);
        FStar_VConfig.smtencoding_l_arith_repr =
          (x.FStar_VConfig.smtencoding_l_arith_repr);
        FStar_VConfig.tcnorm = (x.FStar_VConfig.tcnorm);
        FStar_VConfig.no_plugins = (x.FStar_VConfig.no_plugins);
        FStar_VConfig.no_tactics = (x.FStar_VConfig.no_tactics);
        FStar_VConfig.z3cliopt = (x.FStar_VConfig.z3cliopt);
        FStar_VConfig.z3smtopt = (x.FStar_VConfig.z3smtopt);
        FStar_VConfig.z3refresh = (x.FStar_VConfig.z3refresh);
        FStar_VConfig.z3rlimit = (x.FStar_VConfig.z3rlimit);
        FStar_VConfig.z3rlimit_factor = (x.FStar_VConfig.z3rlimit_factor);
        FStar_VConfig.z3seed = (x.FStar_VConfig.z3seed);
        FStar_VConfig.z3version = (x.FStar_VConfig.z3version);
        FStar_VConfig.trivial_pre_for_unannotated_effectful_fns =
          (x.FStar_VConfig.trivial_pre_for_unannotated_effectful_fns);
        FStar_VConfig.reuse_hint_for = (x.FStar_VConfig.reuse_hint_for)
      } in
    FStarC_Tactics_V2_Builtins.t_smt_sync x1 ps
let _ =
  FStarC_Tactics_Native.register_tactic "FStar.Tactics.SMT.smt_sync'"
    (Prims.of_int 3)
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_2
               "FStar.Tactics.SMT.smt_sync' (plugin)"
               (FStarC_Tactics_Native.from_tactic_2 smt_sync')
               FStarC_Syntax_Embeddings.e_int FStarC_Syntax_Embeddings.e_int
               FStarC_Syntax_Embeddings.e_unit psc ncb us args)
let get_rlimit (uu___ : unit) :
  (Prims.int, Obj.t) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = FStarC_Tactics_V2_Builtins.get_vconfig () ps in
    x.FStar_VConfig.z3rlimit
let _ =
  FStarC_Tactics_Native.register_tactic "FStar.Tactics.SMT.get_rlimit"
    (Prims.of_int 2)
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.SMT.get_rlimit (plugin)"
               (FStarC_Tactics_Native.from_tactic_1 get_rlimit)
               FStarC_Syntax_Embeddings.e_unit FStarC_Syntax_Embeddings.e_int
               psc ncb us args)
let set_rlimit (v : Prims.int) : (unit, Obj.t) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x =
      let x1 = FStarC_Tactics_V2_Builtins.get_vconfig () ps in
      {
        FStar_VConfig.initial_fuel = (x1.FStar_VConfig.initial_fuel);
        FStar_VConfig.max_fuel = (x1.FStar_VConfig.max_fuel);
        FStar_VConfig.initial_ifuel = (x1.FStar_VConfig.initial_ifuel);
        FStar_VConfig.max_ifuel = (x1.FStar_VConfig.max_ifuel);
        FStar_VConfig.detail_errors = (x1.FStar_VConfig.detail_errors);
        FStar_VConfig.detail_hint_replay =
          (x1.FStar_VConfig.detail_hint_replay);
        FStar_VConfig.no_smt = (x1.FStar_VConfig.no_smt);
        FStar_VConfig.quake_lo = (x1.FStar_VConfig.quake_lo);
        FStar_VConfig.quake_hi = (x1.FStar_VConfig.quake_hi);
        FStar_VConfig.quake_keep = (x1.FStar_VConfig.quake_keep);
        FStar_VConfig.retry = (x1.FStar_VConfig.retry);
        FStar_VConfig.smtencoding_elim_box =
          (x1.FStar_VConfig.smtencoding_elim_box);
        FStar_VConfig.smtencoding_nl_arith_repr =
          (x1.FStar_VConfig.smtencoding_nl_arith_repr);
        FStar_VConfig.smtencoding_l_arith_repr =
          (x1.FStar_VConfig.smtencoding_l_arith_repr);
        FStar_VConfig.tcnorm = (x1.FStar_VConfig.tcnorm);
        FStar_VConfig.no_plugins = (x1.FStar_VConfig.no_plugins);
        FStar_VConfig.no_tactics = (x1.FStar_VConfig.no_tactics);
        FStar_VConfig.z3cliopt = (x1.FStar_VConfig.z3cliopt);
        FStar_VConfig.z3smtopt = (x1.FStar_VConfig.z3smtopt);
        FStar_VConfig.z3refresh = (x1.FStar_VConfig.z3refresh);
        FStar_VConfig.z3rlimit = v;
        FStar_VConfig.z3rlimit_factor = (x1.FStar_VConfig.z3rlimit_factor);
        FStar_VConfig.z3seed = (x1.FStar_VConfig.z3seed);
        FStar_VConfig.z3version = (x1.FStar_VConfig.z3version);
        FStar_VConfig.trivial_pre_for_unannotated_effectful_fns =
          (x1.FStar_VConfig.trivial_pre_for_unannotated_effectful_fns);
        FStar_VConfig.reuse_hint_for = (x1.FStar_VConfig.reuse_hint_for)
      } in
    FStarC_Tactics_V2_Builtins.set_vconfig x ps
let _ =
  FStarC_Tactics_Native.register_tactic "FStar.Tactics.SMT.set_rlimit"
    (Prims.of_int 2)
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.SMT.set_rlimit (plugin)"
               (FStarC_Tactics_Native.from_tactic_1 set_rlimit)
               FStarC_Syntax_Embeddings.e_int FStarC_Syntax_Embeddings.e_unit
               psc ncb us args)
let get_initial_fuel (uu___ : unit) :
  (Prims.int, Obj.t) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = FStarC_Tactics_V2_Builtins.get_vconfig () ps in
    x.FStar_VConfig.initial_fuel
let _ =
  FStarC_Tactics_Native.register_tactic "FStar.Tactics.SMT.get_initial_fuel"
    (Prims.of_int 2)
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.SMT.get_initial_fuel (plugin)"
               (FStarC_Tactics_Native.from_tactic_1 get_initial_fuel)
               FStarC_Syntax_Embeddings.e_unit FStarC_Syntax_Embeddings.e_int
               psc ncb us args)
let get_initial_ifuel (uu___ : unit) :
  (Prims.int, Obj.t) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = FStarC_Tactics_V2_Builtins.get_vconfig () ps in
    x.FStar_VConfig.initial_ifuel
let _ =
  FStarC_Tactics_Native.register_tactic "FStar.Tactics.SMT.get_initial_ifuel"
    (Prims.of_int 2)
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.SMT.get_initial_ifuel (plugin)"
               (FStarC_Tactics_Native.from_tactic_1 get_initial_ifuel)
               FStarC_Syntax_Embeddings.e_unit FStarC_Syntax_Embeddings.e_int
               psc ncb us args)
let get_max_fuel (uu___ : unit) :
  (Prims.int, Obj.t) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = FStarC_Tactics_V2_Builtins.get_vconfig () ps in
    x.FStar_VConfig.max_fuel
let _ =
  FStarC_Tactics_Native.register_tactic "FStar.Tactics.SMT.get_max_fuel"
    (Prims.of_int 2)
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.SMT.get_max_fuel (plugin)"
               (FStarC_Tactics_Native.from_tactic_1 get_max_fuel)
               FStarC_Syntax_Embeddings.e_unit FStarC_Syntax_Embeddings.e_int
               psc ncb us args)
let get_max_ifuel (uu___ : unit) :
  (Prims.int, Obj.t) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = FStarC_Tactics_V2_Builtins.get_vconfig () ps in
    x.FStar_VConfig.max_ifuel
let _ =
  FStarC_Tactics_Native.register_tactic "FStar.Tactics.SMT.get_max_ifuel"
    (Prims.of_int 2)
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.SMT.get_max_ifuel (plugin)"
               (FStarC_Tactics_Native.from_tactic_1 get_max_ifuel)
               FStarC_Syntax_Embeddings.e_unit FStarC_Syntax_Embeddings.e_int
               psc ncb us args)
let set_initial_fuel (v : Prims.int) :
  (unit, Obj.t) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x =
      let x1 = FStarC_Tactics_V2_Builtins.get_vconfig () ps in
      {
        FStar_VConfig.initial_fuel = v;
        FStar_VConfig.max_fuel = (x1.FStar_VConfig.max_fuel);
        FStar_VConfig.initial_ifuel = (x1.FStar_VConfig.initial_ifuel);
        FStar_VConfig.max_ifuel = (x1.FStar_VConfig.max_ifuel);
        FStar_VConfig.detail_errors = (x1.FStar_VConfig.detail_errors);
        FStar_VConfig.detail_hint_replay =
          (x1.FStar_VConfig.detail_hint_replay);
        FStar_VConfig.no_smt = (x1.FStar_VConfig.no_smt);
        FStar_VConfig.quake_lo = (x1.FStar_VConfig.quake_lo);
        FStar_VConfig.quake_hi = (x1.FStar_VConfig.quake_hi);
        FStar_VConfig.quake_keep = (x1.FStar_VConfig.quake_keep);
        FStar_VConfig.retry = (x1.FStar_VConfig.retry);
        FStar_VConfig.smtencoding_elim_box =
          (x1.FStar_VConfig.smtencoding_elim_box);
        FStar_VConfig.smtencoding_nl_arith_repr =
          (x1.FStar_VConfig.smtencoding_nl_arith_repr);
        FStar_VConfig.smtencoding_l_arith_repr =
          (x1.FStar_VConfig.smtencoding_l_arith_repr);
        FStar_VConfig.tcnorm = (x1.FStar_VConfig.tcnorm);
        FStar_VConfig.no_plugins = (x1.FStar_VConfig.no_plugins);
        FStar_VConfig.no_tactics = (x1.FStar_VConfig.no_tactics);
        FStar_VConfig.z3cliopt = (x1.FStar_VConfig.z3cliopt);
        FStar_VConfig.z3smtopt = (x1.FStar_VConfig.z3smtopt);
        FStar_VConfig.z3refresh = (x1.FStar_VConfig.z3refresh);
        FStar_VConfig.z3rlimit = (x1.FStar_VConfig.z3rlimit);
        FStar_VConfig.z3rlimit_factor = (x1.FStar_VConfig.z3rlimit_factor);
        FStar_VConfig.z3seed = (x1.FStar_VConfig.z3seed);
        FStar_VConfig.z3version = (x1.FStar_VConfig.z3version);
        FStar_VConfig.trivial_pre_for_unannotated_effectful_fns =
          (x1.FStar_VConfig.trivial_pre_for_unannotated_effectful_fns);
        FStar_VConfig.reuse_hint_for = (x1.FStar_VConfig.reuse_hint_for)
      } in
    FStarC_Tactics_V2_Builtins.set_vconfig x ps
let _ =
  FStarC_Tactics_Native.register_tactic "FStar.Tactics.SMT.set_initial_fuel"
    (Prims.of_int 2)
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.SMT.set_initial_fuel (plugin)"
               (FStarC_Tactics_Native.from_tactic_1 set_initial_fuel)
               FStarC_Syntax_Embeddings.e_int FStarC_Syntax_Embeddings.e_unit
               psc ncb us args)
let set_initial_ifuel (v : Prims.int) :
  (unit, Obj.t) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x =
      let x1 = FStarC_Tactics_V2_Builtins.get_vconfig () ps in
      {
        FStar_VConfig.initial_fuel = (x1.FStar_VConfig.initial_fuel);
        FStar_VConfig.max_fuel = (x1.FStar_VConfig.max_fuel);
        FStar_VConfig.initial_ifuel = v;
        FStar_VConfig.max_ifuel = (x1.FStar_VConfig.max_ifuel);
        FStar_VConfig.detail_errors = (x1.FStar_VConfig.detail_errors);
        FStar_VConfig.detail_hint_replay =
          (x1.FStar_VConfig.detail_hint_replay);
        FStar_VConfig.no_smt = (x1.FStar_VConfig.no_smt);
        FStar_VConfig.quake_lo = (x1.FStar_VConfig.quake_lo);
        FStar_VConfig.quake_hi = (x1.FStar_VConfig.quake_hi);
        FStar_VConfig.quake_keep = (x1.FStar_VConfig.quake_keep);
        FStar_VConfig.retry = (x1.FStar_VConfig.retry);
        FStar_VConfig.smtencoding_elim_box =
          (x1.FStar_VConfig.smtencoding_elim_box);
        FStar_VConfig.smtencoding_nl_arith_repr =
          (x1.FStar_VConfig.smtencoding_nl_arith_repr);
        FStar_VConfig.smtencoding_l_arith_repr =
          (x1.FStar_VConfig.smtencoding_l_arith_repr);
        FStar_VConfig.tcnorm = (x1.FStar_VConfig.tcnorm);
        FStar_VConfig.no_plugins = (x1.FStar_VConfig.no_plugins);
        FStar_VConfig.no_tactics = (x1.FStar_VConfig.no_tactics);
        FStar_VConfig.z3cliopt = (x1.FStar_VConfig.z3cliopt);
        FStar_VConfig.z3smtopt = (x1.FStar_VConfig.z3smtopt);
        FStar_VConfig.z3refresh = (x1.FStar_VConfig.z3refresh);
        FStar_VConfig.z3rlimit = (x1.FStar_VConfig.z3rlimit);
        FStar_VConfig.z3rlimit_factor = (x1.FStar_VConfig.z3rlimit_factor);
        FStar_VConfig.z3seed = (x1.FStar_VConfig.z3seed);
        FStar_VConfig.z3version = (x1.FStar_VConfig.z3version);
        FStar_VConfig.trivial_pre_for_unannotated_effectful_fns =
          (x1.FStar_VConfig.trivial_pre_for_unannotated_effectful_fns);
        FStar_VConfig.reuse_hint_for = (x1.FStar_VConfig.reuse_hint_for)
      } in
    FStarC_Tactics_V2_Builtins.set_vconfig x ps
let _ =
  FStarC_Tactics_Native.register_tactic "FStar.Tactics.SMT.set_initial_ifuel"
    (Prims.of_int 2)
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.SMT.set_initial_ifuel (plugin)"
               (FStarC_Tactics_Native.from_tactic_1 set_initial_ifuel)
               FStarC_Syntax_Embeddings.e_int FStarC_Syntax_Embeddings.e_unit
               psc ncb us args)
let set_max_fuel (v : Prims.int) :
  (unit, Obj.t) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x =
      let x1 = FStarC_Tactics_V2_Builtins.get_vconfig () ps in
      {
        FStar_VConfig.initial_fuel = (x1.FStar_VConfig.initial_fuel);
        FStar_VConfig.max_fuel = v;
        FStar_VConfig.initial_ifuel = (x1.FStar_VConfig.initial_ifuel);
        FStar_VConfig.max_ifuel = (x1.FStar_VConfig.max_ifuel);
        FStar_VConfig.detail_errors = (x1.FStar_VConfig.detail_errors);
        FStar_VConfig.detail_hint_replay =
          (x1.FStar_VConfig.detail_hint_replay);
        FStar_VConfig.no_smt = (x1.FStar_VConfig.no_smt);
        FStar_VConfig.quake_lo = (x1.FStar_VConfig.quake_lo);
        FStar_VConfig.quake_hi = (x1.FStar_VConfig.quake_hi);
        FStar_VConfig.quake_keep = (x1.FStar_VConfig.quake_keep);
        FStar_VConfig.retry = (x1.FStar_VConfig.retry);
        FStar_VConfig.smtencoding_elim_box =
          (x1.FStar_VConfig.smtencoding_elim_box);
        FStar_VConfig.smtencoding_nl_arith_repr =
          (x1.FStar_VConfig.smtencoding_nl_arith_repr);
        FStar_VConfig.smtencoding_l_arith_repr =
          (x1.FStar_VConfig.smtencoding_l_arith_repr);
        FStar_VConfig.tcnorm = (x1.FStar_VConfig.tcnorm);
        FStar_VConfig.no_plugins = (x1.FStar_VConfig.no_plugins);
        FStar_VConfig.no_tactics = (x1.FStar_VConfig.no_tactics);
        FStar_VConfig.z3cliopt = (x1.FStar_VConfig.z3cliopt);
        FStar_VConfig.z3smtopt = (x1.FStar_VConfig.z3smtopt);
        FStar_VConfig.z3refresh = (x1.FStar_VConfig.z3refresh);
        FStar_VConfig.z3rlimit = (x1.FStar_VConfig.z3rlimit);
        FStar_VConfig.z3rlimit_factor = (x1.FStar_VConfig.z3rlimit_factor);
        FStar_VConfig.z3seed = (x1.FStar_VConfig.z3seed);
        FStar_VConfig.z3version = (x1.FStar_VConfig.z3version);
        FStar_VConfig.trivial_pre_for_unannotated_effectful_fns =
          (x1.FStar_VConfig.trivial_pre_for_unannotated_effectful_fns);
        FStar_VConfig.reuse_hint_for = (x1.FStar_VConfig.reuse_hint_for)
      } in
    FStarC_Tactics_V2_Builtins.set_vconfig x ps
let _ =
  FStarC_Tactics_Native.register_tactic "FStar.Tactics.SMT.set_max_fuel"
    (Prims.of_int 2)
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.SMT.set_max_fuel (plugin)"
               (FStarC_Tactics_Native.from_tactic_1 set_max_fuel)
               FStarC_Syntax_Embeddings.e_int FStarC_Syntax_Embeddings.e_unit
               psc ncb us args)
let set_max_ifuel (v : Prims.int) :
  (unit, Obj.t) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x =
      let x1 = FStarC_Tactics_V2_Builtins.get_vconfig () ps in
      {
        FStar_VConfig.initial_fuel = (x1.FStar_VConfig.initial_fuel);
        FStar_VConfig.max_fuel = (x1.FStar_VConfig.max_fuel);
        FStar_VConfig.initial_ifuel = (x1.FStar_VConfig.initial_ifuel);
        FStar_VConfig.max_ifuel = v;
        FStar_VConfig.detail_errors = (x1.FStar_VConfig.detail_errors);
        FStar_VConfig.detail_hint_replay =
          (x1.FStar_VConfig.detail_hint_replay);
        FStar_VConfig.no_smt = (x1.FStar_VConfig.no_smt);
        FStar_VConfig.quake_lo = (x1.FStar_VConfig.quake_lo);
        FStar_VConfig.quake_hi = (x1.FStar_VConfig.quake_hi);
        FStar_VConfig.quake_keep = (x1.FStar_VConfig.quake_keep);
        FStar_VConfig.retry = (x1.FStar_VConfig.retry);
        FStar_VConfig.smtencoding_elim_box =
          (x1.FStar_VConfig.smtencoding_elim_box);
        FStar_VConfig.smtencoding_nl_arith_repr =
          (x1.FStar_VConfig.smtencoding_nl_arith_repr);
        FStar_VConfig.smtencoding_l_arith_repr =
          (x1.FStar_VConfig.smtencoding_l_arith_repr);
        FStar_VConfig.tcnorm = (x1.FStar_VConfig.tcnorm);
        FStar_VConfig.no_plugins = (x1.FStar_VConfig.no_plugins);
        FStar_VConfig.no_tactics = (x1.FStar_VConfig.no_tactics);
        FStar_VConfig.z3cliopt = (x1.FStar_VConfig.z3cliopt);
        FStar_VConfig.z3smtopt = (x1.FStar_VConfig.z3smtopt);
        FStar_VConfig.z3refresh = (x1.FStar_VConfig.z3refresh);
        FStar_VConfig.z3rlimit = (x1.FStar_VConfig.z3rlimit);
        FStar_VConfig.z3rlimit_factor = (x1.FStar_VConfig.z3rlimit_factor);
        FStar_VConfig.z3seed = (x1.FStar_VConfig.z3seed);
        FStar_VConfig.z3version = (x1.FStar_VConfig.z3version);
        FStar_VConfig.trivial_pre_for_unannotated_effectful_fns =
          (x1.FStar_VConfig.trivial_pre_for_unannotated_effectful_fns);
        FStar_VConfig.reuse_hint_for = (x1.FStar_VConfig.reuse_hint_for)
      } in
    FStarC_Tactics_V2_Builtins.set_vconfig x ps
let _ =
  FStarC_Tactics_Native.register_tactic "FStar.Tactics.SMT.set_max_ifuel"
    (Prims.of_int 2)
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.SMT.set_max_ifuel (plugin)"
               (FStarC_Tactics_Native.from_tactic_1 set_max_ifuel)
               FStarC_Syntax_Embeddings.e_int FStarC_Syntax_Embeddings.e_unit
               psc ncb us args)
let set_fuel (v : Prims.int) : (unit, Obj.t) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x =
      let x1 = FStarC_Tactics_V2_Builtins.get_vconfig () ps in
      {
        FStar_VConfig.initial_fuel = v;
        FStar_VConfig.max_fuel = v;
        FStar_VConfig.initial_ifuel = (x1.FStar_VConfig.initial_ifuel);
        FStar_VConfig.max_ifuel = (x1.FStar_VConfig.max_ifuel);
        FStar_VConfig.detail_errors = (x1.FStar_VConfig.detail_errors);
        FStar_VConfig.detail_hint_replay =
          (x1.FStar_VConfig.detail_hint_replay);
        FStar_VConfig.no_smt = (x1.FStar_VConfig.no_smt);
        FStar_VConfig.quake_lo = (x1.FStar_VConfig.quake_lo);
        FStar_VConfig.quake_hi = (x1.FStar_VConfig.quake_hi);
        FStar_VConfig.quake_keep = (x1.FStar_VConfig.quake_keep);
        FStar_VConfig.retry = (x1.FStar_VConfig.retry);
        FStar_VConfig.smtencoding_elim_box =
          (x1.FStar_VConfig.smtencoding_elim_box);
        FStar_VConfig.smtencoding_nl_arith_repr =
          (x1.FStar_VConfig.smtencoding_nl_arith_repr);
        FStar_VConfig.smtencoding_l_arith_repr =
          (x1.FStar_VConfig.smtencoding_l_arith_repr);
        FStar_VConfig.tcnorm = (x1.FStar_VConfig.tcnorm);
        FStar_VConfig.no_plugins = (x1.FStar_VConfig.no_plugins);
        FStar_VConfig.no_tactics = (x1.FStar_VConfig.no_tactics);
        FStar_VConfig.z3cliopt = (x1.FStar_VConfig.z3cliopt);
        FStar_VConfig.z3smtopt = (x1.FStar_VConfig.z3smtopt);
        FStar_VConfig.z3refresh = (x1.FStar_VConfig.z3refresh);
        FStar_VConfig.z3rlimit = (x1.FStar_VConfig.z3rlimit);
        FStar_VConfig.z3rlimit_factor = (x1.FStar_VConfig.z3rlimit_factor);
        FStar_VConfig.z3seed = (x1.FStar_VConfig.z3seed);
        FStar_VConfig.z3version = (x1.FStar_VConfig.z3version);
        FStar_VConfig.trivial_pre_for_unannotated_effectful_fns =
          (x1.FStar_VConfig.trivial_pre_for_unannotated_effectful_fns);
        FStar_VConfig.reuse_hint_for = (x1.FStar_VConfig.reuse_hint_for)
      } in
    FStarC_Tactics_V2_Builtins.set_vconfig x ps
let _ =
  FStarC_Tactics_Native.register_tactic "FStar.Tactics.SMT.set_fuel"
    (Prims.of_int 2)
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.SMT.set_fuel (plugin)"
               (FStarC_Tactics_Native.from_tactic_1 set_fuel)
               FStarC_Syntax_Embeddings.e_int FStarC_Syntax_Embeddings.e_unit
               psc ncb us args)
let set_ifuel (v : Prims.int) : (unit, Obj.t) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x =
      let x1 = FStarC_Tactics_V2_Builtins.get_vconfig () ps in
      {
        FStar_VConfig.initial_fuel = (x1.FStar_VConfig.initial_fuel);
        FStar_VConfig.max_fuel = (x1.FStar_VConfig.max_fuel);
        FStar_VConfig.initial_ifuel = v;
        FStar_VConfig.max_ifuel = v;
        FStar_VConfig.detail_errors = (x1.FStar_VConfig.detail_errors);
        FStar_VConfig.detail_hint_replay =
          (x1.FStar_VConfig.detail_hint_replay);
        FStar_VConfig.no_smt = (x1.FStar_VConfig.no_smt);
        FStar_VConfig.quake_lo = (x1.FStar_VConfig.quake_lo);
        FStar_VConfig.quake_hi = (x1.FStar_VConfig.quake_hi);
        FStar_VConfig.quake_keep = (x1.FStar_VConfig.quake_keep);
        FStar_VConfig.retry = (x1.FStar_VConfig.retry);
        FStar_VConfig.smtencoding_elim_box =
          (x1.FStar_VConfig.smtencoding_elim_box);
        FStar_VConfig.smtencoding_nl_arith_repr =
          (x1.FStar_VConfig.smtencoding_nl_arith_repr);
        FStar_VConfig.smtencoding_l_arith_repr =
          (x1.FStar_VConfig.smtencoding_l_arith_repr);
        FStar_VConfig.tcnorm = (x1.FStar_VConfig.tcnorm);
        FStar_VConfig.no_plugins = (x1.FStar_VConfig.no_plugins);
        FStar_VConfig.no_tactics = (x1.FStar_VConfig.no_tactics);
        FStar_VConfig.z3cliopt = (x1.FStar_VConfig.z3cliopt);
        FStar_VConfig.z3smtopt = (x1.FStar_VConfig.z3smtopt);
        FStar_VConfig.z3refresh = (x1.FStar_VConfig.z3refresh);
        FStar_VConfig.z3rlimit = (x1.FStar_VConfig.z3rlimit);
        FStar_VConfig.z3rlimit_factor = (x1.FStar_VConfig.z3rlimit_factor);
        FStar_VConfig.z3seed = (x1.FStar_VConfig.z3seed);
        FStar_VConfig.z3version = (x1.FStar_VConfig.z3version);
        FStar_VConfig.trivial_pre_for_unannotated_effectful_fns =
          (x1.FStar_VConfig.trivial_pre_for_unannotated_effectful_fns);
        FStar_VConfig.reuse_hint_for = (x1.FStar_VConfig.reuse_hint_for)
      } in
    FStarC_Tactics_V2_Builtins.set_vconfig x ps
let _ =
  FStarC_Tactics_Native.register_tactic "FStar.Tactics.SMT.set_ifuel"
    (Prims.of_int 2)
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.SMT.set_ifuel (plugin)"
               (FStarC_Tactics_Native.from_tactic_1 set_ifuel)
               FStarC_Syntax_Embeddings.e_int FStarC_Syntax_Embeddings.e_unit
               psc ncb us args)
