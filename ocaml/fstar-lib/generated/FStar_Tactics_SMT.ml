open Prims
let (smt_sync : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.SMT.fst" (Prims.of_int (8))
               (Prims.of_int (40)) (Prims.of_int (8)) (Prims.of_int (56)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.SMT.fst" (Prims.of_int (8))
               (Prims.of_int (29)) (Prims.of_int (8)) (Prims.of_int (56)))))
      (Obj.magic (FStar_Tactics_V2_Builtins.get_vconfig ()))
      (fun uu___1 ->
         (fun uu___1 ->
            Obj.magic (FStar_Tactics_V2_Builtins.t_smt_sync uu___1)) uu___1)
let (smt_sync' :
  Prims.nat -> Prims.nat -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun fuel ->
    fun ifuel ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.SMT.fst"
                 (Prims.of_int (12)) (Prims.of_int (15)) (Prims.of_int (12))
                 (Prims.of_int (29)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.SMT.fst"
                 (Prims.of_int (12)) (Prims.of_int (32)) (Prims.of_int (16))
                 (Prims.of_int (20)))))
        (Obj.magic (FStar_Tactics_V2_Builtins.get_vconfig ()))
        (fun uu___ ->
           (fun vcfg ->
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.SMT.fst"
                            (Prims.of_int (13)) (Prims.of_int (18))
                            (Prims.of_int (14)) (Prims.of_int (68)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.SMT.fst"
                            (Prims.of_int (16)) (Prims.of_int (4))
                            (Prims.of_int (16)) (Prims.of_int (20)))))
                   (FStar_Tactics_Effect.lift_div_tac
                      (fun uu___ ->
                         {
                           FStar_VConfig.initial_fuel = fuel;
                           FStar_VConfig.max_fuel = fuel;
                           FStar_VConfig.initial_ifuel = ifuel;
                           FStar_VConfig.max_ifuel = ifuel;
                           FStar_VConfig.detail_errors =
                             (vcfg.FStar_VConfig.detail_errors);
                           FStar_VConfig.detail_hint_replay =
                             (vcfg.FStar_VConfig.detail_hint_replay);
                           FStar_VConfig.no_smt = (vcfg.FStar_VConfig.no_smt);
                           FStar_VConfig.quake_lo =
                             (vcfg.FStar_VConfig.quake_lo);
                           FStar_VConfig.quake_hi =
                             (vcfg.FStar_VConfig.quake_hi);
                           FStar_VConfig.quake_keep =
                             (vcfg.FStar_VConfig.quake_keep);
                           FStar_VConfig.retry = (vcfg.FStar_VConfig.retry);
                           FStar_VConfig.smtencoding_elim_box =
                             (vcfg.FStar_VConfig.smtencoding_elim_box);
                           FStar_VConfig.smtencoding_nl_arith_repr =
                             (vcfg.FStar_VConfig.smtencoding_nl_arith_repr);
                           FStar_VConfig.smtencoding_l_arith_repr =
                             (vcfg.FStar_VConfig.smtencoding_l_arith_repr);
                           FStar_VConfig.smtencoding_valid_intro =
                             (vcfg.FStar_VConfig.smtencoding_valid_intro);
                           FStar_VConfig.smtencoding_valid_elim =
                             (vcfg.FStar_VConfig.smtencoding_valid_elim);
                           FStar_VConfig.tcnorm = (vcfg.FStar_VConfig.tcnorm);
                           FStar_VConfig.no_plugins =
                             (vcfg.FStar_VConfig.no_plugins);
                           FStar_VConfig.no_tactics =
                             (vcfg.FStar_VConfig.no_tactics);
                           FStar_VConfig.z3cliopt =
                             (vcfg.FStar_VConfig.z3cliopt);
                           FStar_VConfig.z3smtopt =
                             (vcfg.FStar_VConfig.z3smtopt);
                           FStar_VConfig.z3refresh =
                             (vcfg.FStar_VConfig.z3refresh);
                           FStar_VConfig.z3rlimit =
                             (vcfg.FStar_VConfig.z3rlimit);
                           FStar_VConfig.z3rlimit_factor =
                             (vcfg.FStar_VConfig.z3rlimit_factor);
                           FStar_VConfig.z3seed = (vcfg.FStar_VConfig.z3seed);
                           FStar_VConfig.z3version =
                             (vcfg.FStar_VConfig.z3version);
                           FStar_VConfig.trivial_pre_for_unannotated_effectful_fns
                             =
                             (vcfg.FStar_VConfig.trivial_pre_for_unannotated_effectful_fns);
                           FStar_VConfig.reuse_hint_for =
                             (vcfg.FStar_VConfig.reuse_hint_for)
                         }))
                   (fun uu___ ->
                      (fun vcfg' ->
                         Obj.magic
                           (FStar_Tactics_V2_Builtins.t_smt_sync vcfg'))
                        uu___))) uu___)
let (get_rlimit : unit -> (Prims.int, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.SMT.fst" (Prims.of_int (20))
               (Prims.of_int (45)) (Prims.of_int (20)) (Prims.of_int (60)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.SMT.fst" (Prims.of_int (20))
               (Prims.of_int (45)) (Prims.of_int (20)) (Prims.of_int (69)))))
      (Obj.magic (FStar_Tactics_V2_Builtins.get_vconfig ()))
      (fun uu___1 ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___2 -> uu___1.FStar_VConfig.z3rlimit))
let (set_rlimit : Prims.int -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun v ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.SMT.fst" (Prims.of_int (21))
               (Prims.of_int (59)) (Prims.of_int (21)) (Prims.of_int (91)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.SMT.fst" (Prims.of_int (21))
               (Prims.of_int (45)) (Prims.of_int (21)) (Prims.of_int (93)))))
      (Obj.magic
         (FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.Tactics.SMT.fst"
                     (Prims.of_int (21)) (Prims.of_int (59))
                     (Prims.of_int (21)) (Prims.of_int (73)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.Tactics.SMT.fst"
                     (Prims.of_int (21)) (Prims.of_int (59))
                     (Prims.of_int (21)) (Prims.of_int (91)))))
            (Obj.magic (FStar_Tactics_V2_Builtins.get_vconfig ()))
            (fun uu___ ->
               FStar_Tactics_Effect.lift_div_tac
                 (fun uu___1 ->
                    {
                      FStar_VConfig.initial_fuel =
                        (uu___.FStar_VConfig.initial_fuel);
                      FStar_VConfig.max_fuel = (uu___.FStar_VConfig.max_fuel);
                      FStar_VConfig.initial_ifuel =
                        (uu___.FStar_VConfig.initial_ifuel);
                      FStar_VConfig.max_ifuel =
                        (uu___.FStar_VConfig.max_ifuel);
                      FStar_VConfig.detail_errors =
                        (uu___.FStar_VConfig.detail_errors);
                      FStar_VConfig.detail_hint_replay =
                        (uu___.FStar_VConfig.detail_hint_replay);
                      FStar_VConfig.no_smt = (uu___.FStar_VConfig.no_smt);
                      FStar_VConfig.quake_lo = (uu___.FStar_VConfig.quake_lo);
                      FStar_VConfig.quake_hi = (uu___.FStar_VConfig.quake_hi);
                      FStar_VConfig.quake_keep =
                        (uu___.FStar_VConfig.quake_keep);
                      FStar_VConfig.retry = (uu___.FStar_VConfig.retry);
                      FStar_VConfig.smtencoding_elim_box =
                        (uu___.FStar_VConfig.smtencoding_elim_box);
                      FStar_VConfig.smtencoding_nl_arith_repr =
                        (uu___.FStar_VConfig.smtencoding_nl_arith_repr);
                      FStar_VConfig.smtencoding_l_arith_repr =
                        (uu___.FStar_VConfig.smtencoding_l_arith_repr);
                      FStar_VConfig.smtencoding_valid_intro =
                        (uu___.FStar_VConfig.smtencoding_valid_intro);
                      FStar_VConfig.smtencoding_valid_elim =
                        (uu___.FStar_VConfig.smtencoding_valid_elim);
                      FStar_VConfig.tcnorm = (uu___.FStar_VConfig.tcnorm);
                      FStar_VConfig.no_plugins =
                        (uu___.FStar_VConfig.no_plugins);
                      FStar_VConfig.no_tactics =
                        (uu___.FStar_VConfig.no_tactics);
                      FStar_VConfig.z3cliopt = (uu___.FStar_VConfig.z3cliopt);
                      FStar_VConfig.z3smtopt = (uu___.FStar_VConfig.z3smtopt);
                      FStar_VConfig.z3refresh =
                        (uu___.FStar_VConfig.z3refresh);
                      FStar_VConfig.z3rlimit = v;
                      FStar_VConfig.z3rlimit_factor =
                        (uu___.FStar_VConfig.z3rlimit_factor);
                      FStar_VConfig.z3seed = (uu___.FStar_VConfig.z3seed);
                      FStar_VConfig.z3version =
                        (uu___.FStar_VConfig.z3version);
                      FStar_VConfig.trivial_pre_for_unannotated_effectful_fns
                        =
                        (uu___.FStar_VConfig.trivial_pre_for_unannotated_effectful_fns);
                      FStar_VConfig.reuse_hint_for =
                        (uu___.FStar_VConfig.reuse_hint_for)
                    }))))
      (fun uu___ ->
         (fun uu___ ->
            Obj.magic (FStar_Tactics_V2_Builtins.set_vconfig uu___)) uu___)
let (get_initial_fuel :
  unit -> (Prims.int, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.SMT.fst" (Prims.of_int (23))
               (Prims.of_int (45)) (Prims.of_int (23)) (Prims.of_int (61)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.SMT.fst" (Prims.of_int (23))
               (Prims.of_int (45)) (Prims.of_int (23)) (Prims.of_int (74)))))
      (Obj.magic (FStar_Tactics_V2_Builtins.get_vconfig ()))
      (fun uu___1 ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___2 -> uu___1.FStar_VConfig.initial_fuel))
let (get_initial_ifuel :
  unit -> (Prims.int, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.SMT.fst" (Prims.of_int (24))
               (Prims.of_int (45)) (Prims.of_int (24)) (Prims.of_int (61)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.SMT.fst" (Prims.of_int (24))
               (Prims.of_int (45)) (Prims.of_int (24)) (Prims.of_int (75)))))
      (Obj.magic (FStar_Tactics_V2_Builtins.get_vconfig ()))
      (fun uu___1 ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___2 -> uu___1.FStar_VConfig.initial_ifuel))
let (get_max_fuel : unit -> (Prims.int, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.SMT.fst" (Prims.of_int (25))
               (Prims.of_int (45)) (Prims.of_int (25)) (Prims.of_int (61)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.SMT.fst" (Prims.of_int (25))
               (Prims.of_int (45)) (Prims.of_int (25)) (Prims.of_int (70)))))
      (Obj.magic (FStar_Tactics_V2_Builtins.get_vconfig ()))
      (fun uu___1 ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___2 -> uu___1.FStar_VConfig.max_fuel))
let (get_max_ifuel : unit -> (Prims.int, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.SMT.fst" (Prims.of_int (26))
               (Prims.of_int (45)) (Prims.of_int (26)) (Prims.of_int (61)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.SMT.fst" (Prims.of_int (26))
               (Prims.of_int (45)) (Prims.of_int (26)) (Prims.of_int (71)))))
      (Obj.magic (FStar_Tactics_V2_Builtins.get_vconfig ()))
      (fun uu___1 ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___2 -> uu___1.FStar_VConfig.max_ifuel))
let (set_initial_fuel :
  Prims.int -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun v ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.SMT.fst" (Prims.of_int (28))
               (Prims.of_int (59)) (Prims.of_int (28)) (Prims.of_int (96)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.SMT.fst" (Prims.of_int (28))
               (Prims.of_int (45)) (Prims.of_int (28)) (Prims.of_int (98)))))
      (Obj.magic
         (FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.Tactics.SMT.fst"
                     (Prims.of_int (28)) (Prims.of_int (59))
                     (Prims.of_int (28)) (Prims.of_int (73)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.Tactics.SMT.fst"
                     (Prims.of_int (28)) (Prims.of_int (59))
                     (Prims.of_int (28)) (Prims.of_int (96)))))
            (Obj.magic (FStar_Tactics_V2_Builtins.get_vconfig ()))
            (fun uu___ ->
               FStar_Tactics_Effect.lift_div_tac
                 (fun uu___1 ->
                    {
                      FStar_VConfig.initial_fuel = v;
                      FStar_VConfig.max_fuel = (uu___.FStar_VConfig.max_fuel);
                      FStar_VConfig.initial_ifuel =
                        (uu___.FStar_VConfig.initial_ifuel);
                      FStar_VConfig.max_ifuel =
                        (uu___.FStar_VConfig.max_ifuel);
                      FStar_VConfig.detail_errors =
                        (uu___.FStar_VConfig.detail_errors);
                      FStar_VConfig.detail_hint_replay =
                        (uu___.FStar_VConfig.detail_hint_replay);
                      FStar_VConfig.no_smt = (uu___.FStar_VConfig.no_smt);
                      FStar_VConfig.quake_lo = (uu___.FStar_VConfig.quake_lo);
                      FStar_VConfig.quake_hi = (uu___.FStar_VConfig.quake_hi);
                      FStar_VConfig.quake_keep =
                        (uu___.FStar_VConfig.quake_keep);
                      FStar_VConfig.retry = (uu___.FStar_VConfig.retry);
                      FStar_VConfig.smtencoding_elim_box =
                        (uu___.FStar_VConfig.smtencoding_elim_box);
                      FStar_VConfig.smtencoding_nl_arith_repr =
                        (uu___.FStar_VConfig.smtencoding_nl_arith_repr);
                      FStar_VConfig.smtencoding_l_arith_repr =
                        (uu___.FStar_VConfig.smtencoding_l_arith_repr);
                      FStar_VConfig.smtencoding_valid_intro =
                        (uu___.FStar_VConfig.smtencoding_valid_intro);
                      FStar_VConfig.smtencoding_valid_elim =
                        (uu___.FStar_VConfig.smtencoding_valid_elim);
                      FStar_VConfig.tcnorm = (uu___.FStar_VConfig.tcnorm);
                      FStar_VConfig.no_plugins =
                        (uu___.FStar_VConfig.no_plugins);
                      FStar_VConfig.no_tactics =
                        (uu___.FStar_VConfig.no_tactics);
                      FStar_VConfig.z3cliopt = (uu___.FStar_VConfig.z3cliopt);
                      FStar_VConfig.z3smtopt = (uu___.FStar_VConfig.z3smtopt);
                      FStar_VConfig.z3refresh =
                        (uu___.FStar_VConfig.z3refresh);
                      FStar_VConfig.z3rlimit = (uu___.FStar_VConfig.z3rlimit);
                      FStar_VConfig.z3rlimit_factor =
                        (uu___.FStar_VConfig.z3rlimit_factor);
                      FStar_VConfig.z3seed = (uu___.FStar_VConfig.z3seed);
                      FStar_VConfig.z3version =
                        (uu___.FStar_VConfig.z3version);
                      FStar_VConfig.trivial_pre_for_unannotated_effectful_fns
                        =
                        (uu___.FStar_VConfig.trivial_pre_for_unannotated_effectful_fns);
                      FStar_VConfig.reuse_hint_for =
                        (uu___.FStar_VConfig.reuse_hint_for)
                    }))))
      (fun uu___ ->
         (fun uu___ ->
            Obj.magic (FStar_Tactics_V2_Builtins.set_vconfig uu___)) uu___)
let (set_initial_ifuel :
  Prims.int -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun v ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.SMT.fst" (Prims.of_int (29))
               (Prims.of_int (59)) (Prims.of_int (29)) (Prims.of_int (96)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.SMT.fst" (Prims.of_int (29))
               (Prims.of_int (45)) (Prims.of_int (29)) (Prims.of_int (98)))))
      (Obj.magic
         (FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.Tactics.SMT.fst"
                     (Prims.of_int (29)) (Prims.of_int (59))
                     (Prims.of_int (29)) (Prims.of_int (73)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.Tactics.SMT.fst"
                     (Prims.of_int (29)) (Prims.of_int (59))
                     (Prims.of_int (29)) (Prims.of_int (96)))))
            (Obj.magic (FStar_Tactics_V2_Builtins.get_vconfig ()))
            (fun uu___ ->
               FStar_Tactics_Effect.lift_div_tac
                 (fun uu___1 ->
                    {
                      FStar_VConfig.initial_fuel =
                        (uu___.FStar_VConfig.initial_fuel);
                      FStar_VConfig.max_fuel = (uu___.FStar_VConfig.max_fuel);
                      FStar_VConfig.initial_ifuel = v;
                      FStar_VConfig.max_ifuel =
                        (uu___.FStar_VConfig.max_ifuel);
                      FStar_VConfig.detail_errors =
                        (uu___.FStar_VConfig.detail_errors);
                      FStar_VConfig.detail_hint_replay =
                        (uu___.FStar_VConfig.detail_hint_replay);
                      FStar_VConfig.no_smt = (uu___.FStar_VConfig.no_smt);
                      FStar_VConfig.quake_lo = (uu___.FStar_VConfig.quake_lo);
                      FStar_VConfig.quake_hi = (uu___.FStar_VConfig.quake_hi);
                      FStar_VConfig.quake_keep =
                        (uu___.FStar_VConfig.quake_keep);
                      FStar_VConfig.retry = (uu___.FStar_VConfig.retry);
                      FStar_VConfig.smtencoding_elim_box =
                        (uu___.FStar_VConfig.smtencoding_elim_box);
                      FStar_VConfig.smtencoding_nl_arith_repr =
                        (uu___.FStar_VConfig.smtencoding_nl_arith_repr);
                      FStar_VConfig.smtencoding_l_arith_repr =
                        (uu___.FStar_VConfig.smtencoding_l_arith_repr);
                      FStar_VConfig.smtencoding_valid_intro =
                        (uu___.FStar_VConfig.smtencoding_valid_intro);
                      FStar_VConfig.smtencoding_valid_elim =
                        (uu___.FStar_VConfig.smtencoding_valid_elim);
                      FStar_VConfig.tcnorm = (uu___.FStar_VConfig.tcnorm);
                      FStar_VConfig.no_plugins =
                        (uu___.FStar_VConfig.no_plugins);
                      FStar_VConfig.no_tactics =
                        (uu___.FStar_VConfig.no_tactics);
                      FStar_VConfig.z3cliopt = (uu___.FStar_VConfig.z3cliopt);
                      FStar_VConfig.z3smtopt = (uu___.FStar_VConfig.z3smtopt);
                      FStar_VConfig.z3refresh =
                        (uu___.FStar_VConfig.z3refresh);
                      FStar_VConfig.z3rlimit = (uu___.FStar_VConfig.z3rlimit);
                      FStar_VConfig.z3rlimit_factor =
                        (uu___.FStar_VConfig.z3rlimit_factor);
                      FStar_VConfig.z3seed = (uu___.FStar_VConfig.z3seed);
                      FStar_VConfig.z3version =
                        (uu___.FStar_VConfig.z3version);
                      FStar_VConfig.trivial_pre_for_unannotated_effectful_fns
                        =
                        (uu___.FStar_VConfig.trivial_pre_for_unannotated_effectful_fns);
                      FStar_VConfig.reuse_hint_for =
                        (uu___.FStar_VConfig.reuse_hint_for)
                    }))))
      (fun uu___ ->
         (fun uu___ ->
            Obj.magic (FStar_Tactics_V2_Builtins.set_vconfig uu___)) uu___)
let (set_max_fuel : Prims.int -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun v ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.SMT.fst" (Prims.of_int (30))
               (Prims.of_int (59)) (Prims.of_int (30)) (Prims.of_int (96)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.SMT.fst" (Prims.of_int (30))
               (Prims.of_int (45)) (Prims.of_int (30)) (Prims.of_int (98)))))
      (Obj.magic
         (FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.Tactics.SMT.fst"
                     (Prims.of_int (30)) (Prims.of_int (59))
                     (Prims.of_int (30)) (Prims.of_int (73)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.Tactics.SMT.fst"
                     (Prims.of_int (30)) (Prims.of_int (59))
                     (Prims.of_int (30)) (Prims.of_int (96)))))
            (Obj.magic (FStar_Tactics_V2_Builtins.get_vconfig ()))
            (fun uu___ ->
               FStar_Tactics_Effect.lift_div_tac
                 (fun uu___1 ->
                    {
                      FStar_VConfig.initial_fuel =
                        (uu___.FStar_VConfig.initial_fuel);
                      FStar_VConfig.max_fuel = v;
                      FStar_VConfig.initial_ifuel =
                        (uu___.FStar_VConfig.initial_ifuel);
                      FStar_VConfig.max_ifuel =
                        (uu___.FStar_VConfig.max_ifuel);
                      FStar_VConfig.detail_errors =
                        (uu___.FStar_VConfig.detail_errors);
                      FStar_VConfig.detail_hint_replay =
                        (uu___.FStar_VConfig.detail_hint_replay);
                      FStar_VConfig.no_smt = (uu___.FStar_VConfig.no_smt);
                      FStar_VConfig.quake_lo = (uu___.FStar_VConfig.quake_lo);
                      FStar_VConfig.quake_hi = (uu___.FStar_VConfig.quake_hi);
                      FStar_VConfig.quake_keep =
                        (uu___.FStar_VConfig.quake_keep);
                      FStar_VConfig.retry = (uu___.FStar_VConfig.retry);
                      FStar_VConfig.smtencoding_elim_box =
                        (uu___.FStar_VConfig.smtencoding_elim_box);
                      FStar_VConfig.smtencoding_nl_arith_repr =
                        (uu___.FStar_VConfig.smtencoding_nl_arith_repr);
                      FStar_VConfig.smtencoding_l_arith_repr =
                        (uu___.FStar_VConfig.smtencoding_l_arith_repr);
                      FStar_VConfig.smtencoding_valid_intro =
                        (uu___.FStar_VConfig.smtencoding_valid_intro);
                      FStar_VConfig.smtencoding_valid_elim =
                        (uu___.FStar_VConfig.smtencoding_valid_elim);
                      FStar_VConfig.tcnorm = (uu___.FStar_VConfig.tcnorm);
                      FStar_VConfig.no_plugins =
                        (uu___.FStar_VConfig.no_plugins);
                      FStar_VConfig.no_tactics =
                        (uu___.FStar_VConfig.no_tactics);
                      FStar_VConfig.z3cliopt = (uu___.FStar_VConfig.z3cliopt);
                      FStar_VConfig.z3smtopt = (uu___.FStar_VConfig.z3smtopt);
                      FStar_VConfig.z3refresh =
                        (uu___.FStar_VConfig.z3refresh);
                      FStar_VConfig.z3rlimit = (uu___.FStar_VConfig.z3rlimit);
                      FStar_VConfig.z3rlimit_factor =
                        (uu___.FStar_VConfig.z3rlimit_factor);
                      FStar_VConfig.z3seed = (uu___.FStar_VConfig.z3seed);
                      FStar_VConfig.z3version =
                        (uu___.FStar_VConfig.z3version);
                      FStar_VConfig.trivial_pre_for_unannotated_effectful_fns
                        =
                        (uu___.FStar_VConfig.trivial_pre_for_unannotated_effectful_fns);
                      FStar_VConfig.reuse_hint_for =
                        (uu___.FStar_VConfig.reuse_hint_for)
                    }))))
      (fun uu___ ->
         (fun uu___ ->
            Obj.magic (FStar_Tactics_V2_Builtins.set_vconfig uu___)) uu___)
let (set_max_ifuel : Prims.int -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun v ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.SMT.fst" (Prims.of_int (31))
               (Prims.of_int (59)) (Prims.of_int (31)) (Prims.of_int (96)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.SMT.fst" (Prims.of_int (31))
               (Prims.of_int (45)) (Prims.of_int (31)) (Prims.of_int (98)))))
      (Obj.magic
         (FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.Tactics.SMT.fst"
                     (Prims.of_int (31)) (Prims.of_int (59))
                     (Prims.of_int (31)) (Prims.of_int (73)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.Tactics.SMT.fst"
                     (Prims.of_int (31)) (Prims.of_int (59))
                     (Prims.of_int (31)) (Prims.of_int (96)))))
            (Obj.magic (FStar_Tactics_V2_Builtins.get_vconfig ()))
            (fun uu___ ->
               FStar_Tactics_Effect.lift_div_tac
                 (fun uu___1 ->
                    {
                      FStar_VConfig.initial_fuel =
                        (uu___.FStar_VConfig.initial_fuel);
                      FStar_VConfig.max_fuel = (uu___.FStar_VConfig.max_fuel);
                      FStar_VConfig.initial_ifuel =
                        (uu___.FStar_VConfig.initial_ifuel);
                      FStar_VConfig.max_ifuel = v;
                      FStar_VConfig.detail_errors =
                        (uu___.FStar_VConfig.detail_errors);
                      FStar_VConfig.detail_hint_replay =
                        (uu___.FStar_VConfig.detail_hint_replay);
                      FStar_VConfig.no_smt = (uu___.FStar_VConfig.no_smt);
                      FStar_VConfig.quake_lo = (uu___.FStar_VConfig.quake_lo);
                      FStar_VConfig.quake_hi = (uu___.FStar_VConfig.quake_hi);
                      FStar_VConfig.quake_keep =
                        (uu___.FStar_VConfig.quake_keep);
                      FStar_VConfig.retry = (uu___.FStar_VConfig.retry);
                      FStar_VConfig.smtencoding_elim_box =
                        (uu___.FStar_VConfig.smtencoding_elim_box);
                      FStar_VConfig.smtencoding_nl_arith_repr =
                        (uu___.FStar_VConfig.smtencoding_nl_arith_repr);
                      FStar_VConfig.smtencoding_l_arith_repr =
                        (uu___.FStar_VConfig.smtencoding_l_arith_repr);
                      FStar_VConfig.smtencoding_valid_intro =
                        (uu___.FStar_VConfig.smtencoding_valid_intro);
                      FStar_VConfig.smtencoding_valid_elim =
                        (uu___.FStar_VConfig.smtencoding_valid_elim);
                      FStar_VConfig.tcnorm = (uu___.FStar_VConfig.tcnorm);
                      FStar_VConfig.no_plugins =
                        (uu___.FStar_VConfig.no_plugins);
                      FStar_VConfig.no_tactics =
                        (uu___.FStar_VConfig.no_tactics);
                      FStar_VConfig.z3cliopt = (uu___.FStar_VConfig.z3cliopt);
                      FStar_VConfig.z3smtopt = (uu___.FStar_VConfig.z3smtopt);
                      FStar_VConfig.z3refresh =
                        (uu___.FStar_VConfig.z3refresh);
                      FStar_VConfig.z3rlimit = (uu___.FStar_VConfig.z3rlimit);
                      FStar_VConfig.z3rlimit_factor =
                        (uu___.FStar_VConfig.z3rlimit_factor);
                      FStar_VConfig.z3seed = (uu___.FStar_VConfig.z3seed);
                      FStar_VConfig.z3version =
                        (uu___.FStar_VConfig.z3version);
                      FStar_VConfig.trivial_pre_for_unannotated_effectful_fns
                        =
                        (uu___.FStar_VConfig.trivial_pre_for_unannotated_effectful_fns);
                      FStar_VConfig.reuse_hint_for =
                        (uu___.FStar_VConfig.reuse_hint_for)
                    }))))
      (fun uu___ ->
         (fun uu___ ->
            Obj.magic (FStar_Tactics_V2_Builtins.set_vconfig uu___)) uu___)
let (set_fuel : Prims.int -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun v ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.SMT.fst" (Prims.of_int (34))
               (Prims.of_int (59)) (Prims.of_int (34)) (Prims.of_int (111)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.SMT.fst" (Prims.of_int (34))
               (Prims.of_int (45)) (Prims.of_int (34)) (Prims.of_int (113)))))
      (Obj.magic
         (FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.Tactics.SMT.fst"
                     (Prims.of_int (34)) (Prims.of_int (59))
                     (Prims.of_int (34)) (Prims.of_int (73)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.Tactics.SMT.fst"
                     (Prims.of_int (34)) (Prims.of_int (59))
                     (Prims.of_int (34)) (Prims.of_int (111)))))
            (Obj.magic (FStar_Tactics_V2_Builtins.get_vconfig ()))
            (fun uu___ ->
               FStar_Tactics_Effect.lift_div_tac
                 (fun uu___1 ->
                    {
                      FStar_VConfig.initial_fuel = v;
                      FStar_VConfig.max_fuel = v;
                      FStar_VConfig.initial_ifuel =
                        (uu___.FStar_VConfig.initial_ifuel);
                      FStar_VConfig.max_ifuel =
                        (uu___.FStar_VConfig.max_ifuel);
                      FStar_VConfig.detail_errors =
                        (uu___.FStar_VConfig.detail_errors);
                      FStar_VConfig.detail_hint_replay =
                        (uu___.FStar_VConfig.detail_hint_replay);
                      FStar_VConfig.no_smt = (uu___.FStar_VConfig.no_smt);
                      FStar_VConfig.quake_lo = (uu___.FStar_VConfig.quake_lo);
                      FStar_VConfig.quake_hi = (uu___.FStar_VConfig.quake_hi);
                      FStar_VConfig.quake_keep =
                        (uu___.FStar_VConfig.quake_keep);
                      FStar_VConfig.retry = (uu___.FStar_VConfig.retry);
                      FStar_VConfig.smtencoding_elim_box =
                        (uu___.FStar_VConfig.smtencoding_elim_box);
                      FStar_VConfig.smtencoding_nl_arith_repr =
                        (uu___.FStar_VConfig.smtencoding_nl_arith_repr);
                      FStar_VConfig.smtencoding_l_arith_repr =
                        (uu___.FStar_VConfig.smtencoding_l_arith_repr);
                      FStar_VConfig.smtencoding_valid_intro =
                        (uu___.FStar_VConfig.smtencoding_valid_intro);
                      FStar_VConfig.smtencoding_valid_elim =
                        (uu___.FStar_VConfig.smtencoding_valid_elim);
                      FStar_VConfig.tcnorm = (uu___.FStar_VConfig.tcnorm);
                      FStar_VConfig.no_plugins =
                        (uu___.FStar_VConfig.no_plugins);
                      FStar_VConfig.no_tactics =
                        (uu___.FStar_VConfig.no_tactics);
                      FStar_VConfig.z3cliopt = (uu___.FStar_VConfig.z3cliopt);
                      FStar_VConfig.z3smtopt = (uu___.FStar_VConfig.z3smtopt);
                      FStar_VConfig.z3refresh =
                        (uu___.FStar_VConfig.z3refresh);
                      FStar_VConfig.z3rlimit = (uu___.FStar_VConfig.z3rlimit);
                      FStar_VConfig.z3rlimit_factor =
                        (uu___.FStar_VConfig.z3rlimit_factor);
                      FStar_VConfig.z3seed = (uu___.FStar_VConfig.z3seed);
                      FStar_VConfig.z3version =
                        (uu___.FStar_VConfig.z3version);
                      FStar_VConfig.trivial_pre_for_unannotated_effectful_fns
                        =
                        (uu___.FStar_VConfig.trivial_pre_for_unannotated_effectful_fns);
                      FStar_VConfig.reuse_hint_for =
                        (uu___.FStar_VConfig.reuse_hint_for)
                    }))))
      (fun uu___ ->
         (fun uu___ ->
            Obj.magic (FStar_Tactics_V2_Builtins.set_vconfig uu___)) uu___)
let (set_ifuel : Prims.int -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun v ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.SMT.fst" (Prims.of_int (35))
               (Prims.of_int (59)) (Prims.of_int (35)) (Prims.of_int (111)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.SMT.fst" (Prims.of_int (35))
               (Prims.of_int (45)) (Prims.of_int (35)) (Prims.of_int (113)))))
      (Obj.magic
         (FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.Tactics.SMT.fst"
                     (Prims.of_int (35)) (Prims.of_int (59))
                     (Prims.of_int (35)) (Prims.of_int (73)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.Tactics.SMT.fst"
                     (Prims.of_int (35)) (Prims.of_int (59))
                     (Prims.of_int (35)) (Prims.of_int (111)))))
            (Obj.magic (FStar_Tactics_V2_Builtins.get_vconfig ()))
            (fun uu___ ->
               FStar_Tactics_Effect.lift_div_tac
                 (fun uu___1 ->
                    {
                      FStar_VConfig.initial_fuel =
                        (uu___.FStar_VConfig.initial_fuel);
                      FStar_VConfig.max_fuel = (uu___.FStar_VConfig.max_fuel);
                      FStar_VConfig.initial_ifuel = v;
                      FStar_VConfig.max_ifuel = v;
                      FStar_VConfig.detail_errors =
                        (uu___.FStar_VConfig.detail_errors);
                      FStar_VConfig.detail_hint_replay =
                        (uu___.FStar_VConfig.detail_hint_replay);
                      FStar_VConfig.no_smt = (uu___.FStar_VConfig.no_smt);
                      FStar_VConfig.quake_lo = (uu___.FStar_VConfig.quake_lo);
                      FStar_VConfig.quake_hi = (uu___.FStar_VConfig.quake_hi);
                      FStar_VConfig.quake_keep =
                        (uu___.FStar_VConfig.quake_keep);
                      FStar_VConfig.retry = (uu___.FStar_VConfig.retry);
                      FStar_VConfig.smtencoding_elim_box =
                        (uu___.FStar_VConfig.smtencoding_elim_box);
                      FStar_VConfig.smtencoding_nl_arith_repr =
                        (uu___.FStar_VConfig.smtencoding_nl_arith_repr);
                      FStar_VConfig.smtencoding_l_arith_repr =
                        (uu___.FStar_VConfig.smtencoding_l_arith_repr);
                      FStar_VConfig.smtencoding_valid_intro =
                        (uu___.FStar_VConfig.smtencoding_valid_intro);
                      FStar_VConfig.smtencoding_valid_elim =
                        (uu___.FStar_VConfig.smtencoding_valid_elim);
                      FStar_VConfig.tcnorm = (uu___.FStar_VConfig.tcnorm);
                      FStar_VConfig.no_plugins =
                        (uu___.FStar_VConfig.no_plugins);
                      FStar_VConfig.no_tactics =
                        (uu___.FStar_VConfig.no_tactics);
                      FStar_VConfig.z3cliopt = (uu___.FStar_VConfig.z3cliopt);
                      FStar_VConfig.z3smtopt = (uu___.FStar_VConfig.z3smtopt);
                      FStar_VConfig.z3refresh =
                        (uu___.FStar_VConfig.z3refresh);
                      FStar_VConfig.z3rlimit = (uu___.FStar_VConfig.z3rlimit);
                      FStar_VConfig.z3rlimit_factor =
                        (uu___.FStar_VConfig.z3rlimit_factor);
                      FStar_VConfig.z3seed = (uu___.FStar_VConfig.z3seed);
                      FStar_VConfig.z3version =
                        (uu___.FStar_VConfig.z3version);
                      FStar_VConfig.trivial_pre_for_unannotated_effectful_fns
                        =
                        (uu___.FStar_VConfig.trivial_pre_for_unannotated_effectful_fns);
                      FStar_VConfig.reuse_hint_for =
                        (uu___.FStar_VConfig.reuse_hint_for)
                    }))))
      (fun uu___ ->
         (fun uu___ ->
            Obj.magic (FStar_Tactics_V2_Builtins.set_vconfig uu___)) uu___)