open Prims
type label = FStarC_SMTEncoding_Term.error_label
type labels = label Prims.list
exception Not_a_wp_implication of Prims.string 
let (uu___is_Not_a_wp_implication : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Not_a_wp_implication uu___ -> true
    | uu___ -> false
let (__proj__Not_a_wp_implication__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee -> match projectee with | Not_a_wp_implication uu___ -> uu___
let (sort_labels :
  (FStarC_SMTEncoding_Term.error_label * Prims.bool) Prims.list ->
    ((FStarC_SMTEncoding_Term.fv * FStarC_Errors_Msg.error_message *
      FStarC_Compiler_Range_Type.range) * Prims.bool) Prims.list)
  =
  fun l ->
    FStarC_Compiler_List.sortWith
      (fun uu___ ->
         fun uu___1 ->
           match (uu___, uu___1) with
           | (((uu___2, uu___3, r1), uu___4), ((uu___5, uu___6, r2), uu___7))
               -> FStarC_Compiler_Range_Ops.compare r1 r2) l
let (remove_dups :
  labels ->
    (FStarC_SMTEncoding_Term.fv * FStarC_Errors_Msg.error_message *
      FStarC_Compiler_Range_Type.range) Prims.list)
  =
  fun l ->
    FStarC_Compiler_Util.remove_dups
      (fun uu___ ->
         fun uu___1 ->
           match (uu___, uu___1) with
           | ((uu___2, m1, r1), (uu___3, m2, r2)) -> (r1 = r2) && (m1 = m2))
      l
type msg = (Prims.string * FStarC_Compiler_Range_Type.range)
type ranges =
  (Prims.string FStar_Pervasives_Native.option *
    FStarC_Compiler_Range_Type.range) Prims.list
let (__ctr : Prims.int FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Util.mk_ref Prims.int_zero
let (fresh_label :
  FStarC_Errors_Msg.error_message ->
    FStarC_Compiler_Range_Type.range ->
      FStarC_SMTEncoding_Term.term -> (label * FStarC_SMTEncoding_Term.term))
  =
  fun message ->
    fun range ->
      fun t ->
        let l =
          FStarC_Compiler_Util.incr __ctr;
          (let uu___1 =
             let uu___2 = FStarC_Compiler_Effect.op_Bang __ctr in
             FStarC_Compiler_Util.string_of_int uu___2 in
           FStarC_Compiler_Util.format1 "label_%s" uu___1) in
        let lvar =
          FStarC_SMTEncoding_Term.mk_fv
            (l, FStarC_SMTEncoding_Term.Bool_sort) in
        let label1 = (lvar, message, range) in
        let lterm = FStarC_SMTEncoding_Util.mkFreeV lvar in
        let lt = FStarC_SMTEncoding_Term.mkOr (lterm, t) range in
        (label1, lt)
let (label_goals :
  (unit -> Prims.string) FStar_Pervasives_Native.option ->
    FStarC_Compiler_Range_Type.range ->
      FStarC_SMTEncoding_Term.term -> (labels * FStarC_SMTEncoding_Term.term))
  =
  fun use_env_msg ->
    fun r ->
      fun q ->
        let rec is_a_post_condition post_name_opt tm =
          match (post_name_opt, (tm.FStarC_SMTEncoding_Term.tm)) with
          | (FStar_Pervasives_Native.None, uu___) -> false
          | (FStar_Pervasives_Native.Some nm, FStarC_SMTEncoding_Term.FreeV
             fv) ->
              let uu___ = FStarC_SMTEncoding_Term.fv_name fv in nm = uu___
          | (uu___, FStarC_SMTEncoding_Term.App
             (FStarC_SMTEncoding_Term.Var "Valid", tm1::[])) ->
              is_a_post_condition post_name_opt tm1
          | (uu___, FStarC_SMTEncoding_Term.App
             (FStarC_SMTEncoding_Term.Var "ApplyTT", tm1::uu___1)) ->
              is_a_post_condition post_name_opt tm1
          | uu___ -> false in
        let conjuncts t =
          match t.FStarC_SMTEncoding_Term.tm with
          | FStarC_SMTEncoding_Term.App (FStarC_SMTEncoding_Term.And, cs) ->
              cs
          | uu___ -> [t] in
        let is_guard_free tm =
          match tm.FStarC_SMTEncoding_Term.tm with
          | FStarC_SMTEncoding_Term.Quant
              (FStarC_SMTEncoding_Term.Forall,
               ({
                  FStarC_SMTEncoding_Term.tm = FStarC_SMTEncoding_Term.App
                    (FStarC_SMTEncoding_Term.Var "Prims.guard_free", p::[]);
                  FStarC_SMTEncoding_Term.freevars = uu___;
                  FStarC_SMTEncoding_Term.rng = uu___1;_}::[])::[],
               iopt, uu___2,
               {
                 FStarC_SMTEncoding_Term.tm = FStarC_SMTEncoding_Term.App
                   (FStarC_SMTEncoding_Term.Imp, l::r1::[]);
                 FStarC_SMTEncoding_Term.freevars = uu___3;
                 FStarC_SMTEncoding_Term.rng = uu___4;_})
              -> true
          | uu___ -> false in
        let is_a_named_continuation lhs =
          FStarC_Compiler_Util.for_some is_guard_free (conjuncts lhs) in
        let uu___ =
          match use_env_msg with
          | FStar_Pervasives_Native.None -> (false, FStarC_Pprint.empty)
          | FStar_Pervasives_Native.Some f ->
              let uu___1 =
                let uu___2 = f () in FStarC_Pprint.doc_of_string uu___2 in
              (true, uu___1) in
        match uu___ with
        | (flag, msg_prefix) ->
            let fresh_label1 msg1 ropt rng t =
              let msg2 =
                if flag
                then
                  let uu___1 =
                    let uu___2 =
                      FStarC_Errors_Msg.text
                        "Failed to verify implicit argument: " in
                    FStarC_Pprint.op_Hat_Hat uu___2 msg_prefix in
                  uu___1 :: msg1
                else msg1 in
              let rng1 =
                match ropt with
                | FStar_Pervasives_Native.None -> rng
                | FStar_Pervasives_Native.Some r1 ->
                    let uu___1 =
                      let uu___2 = FStarC_Compiler_Range_Type.use_range rng in
                      let uu___3 = FStarC_Compiler_Range_Type.use_range r1 in
                      FStarC_Compiler_Range_Ops.rng_included uu___2 uu___3 in
                    if uu___1
                    then rng
                    else
                      (let uu___3 = FStarC_Compiler_Range_Type.def_range rng in
                       FStarC_Compiler_Range_Type.set_def_range r1 uu___3) in
              fresh_label msg2 rng1 t in
            let rec aux default_msg ropt post_name_opt labels1 q1 =
              match q1.FStarC_SMTEncoding_Term.tm with
              | FStarC_SMTEncoding_Term.BoundV uu___1 -> (labels1, q1)
              | FStarC_SMTEncoding_Term.Integer uu___1 -> (labels1, q1)
              | FStarC_SMTEncoding_Term.String uu___1 -> (labels1, q1)
              | FStarC_SMTEncoding_Term.Real uu___1 -> (labels1, q1)
              | FStarC_SMTEncoding_Term.LblPos uu___1 ->
                  failwith "Impossible"
              | FStarC_SMTEncoding_Term.Labeled (arg, d::[], label_range)
                  when
                  let uu___1 = FStarC_Errors_Msg.renderdoc d in
                  uu___1 = "Could not prove post-condition" ->
                  let fallback debug_msg =
                    aux default_msg
                      (FStar_Pervasives_Native.Some label_range)
                      post_name_opt labels1 arg in
                  (try
                     (fun uu___1 ->
                        match () with
                        | () ->
                            (match arg.FStarC_SMTEncoding_Term.tm with
                             | FStarC_SMTEncoding_Term.Quant
                                 (FStarC_SMTEncoding_Term.Forall, pats, iopt,
                                  post::sorts,
                                  {
                                    FStarC_SMTEncoding_Term.tm =
                                      FStarC_SMTEncoding_Term.App
                                      (FStarC_SMTEncoding_Term.Imp,
                                       lhs::rhs::[]);
                                    FStarC_SMTEncoding_Term.freevars = uu___2;
                                    FStarC_SMTEncoding_Term.rng = rng;_})
                                 ->
                                 let post_name =
                                   let uu___3 =
                                     let uu___4 = FStarC_GenSym.next_id () in
                                     FStarC_Compiler_Util.string_of_int
                                       uu___4 in
                                   Prims.strcat "^^post_condition_" uu___3 in
                                 let names =
                                   let uu___3 =
                                     FStarC_SMTEncoding_Term.mk_fv
                                       (post_name, post) in
                                   let uu___4 =
                                     FStarC_Compiler_List.map
                                       (fun s ->
                                          let uu___5 =
                                            let uu___6 =
                                              let uu___7 =
                                                let uu___8 =
                                                  FStarC_GenSym.next_id () in
                                                FStarC_Compiler_Util.string_of_int
                                                  uu___8 in
                                              Prims.strcat "^^" uu___7 in
                                            (uu___6, s) in
                                          FStarC_SMTEncoding_Term.mk_fv
                                            uu___5) sorts in
                                   uu___3 :: uu___4 in
                                 let instantiation =
                                   FStarC_Compiler_List.map
                                     FStarC_SMTEncoding_Util.mkFreeV names in
                                 let uu___3 =
                                   let uu___4 =
                                     FStarC_SMTEncoding_Term.inst
                                       instantiation lhs in
                                   let uu___5 =
                                     FStarC_SMTEncoding_Term.inst
                                       instantiation rhs in
                                   (uu___4, uu___5) in
                                 (match uu___3 with
                                  | (lhs1, rhs1) ->
                                      let uu___4 =
                                        match lhs1.FStarC_SMTEncoding_Term.tm
                                        with
                                        | FStarC_SMTEncoding_Term.App
                                            (FStarC_SMTEncoding_Term.And,
                                             clauses_lhs)
                                            ->
                                            let uu___5 =
                                              FStarC_Compiler_Util.prefix
                                                clauses_lhs in
                                            (match uu___5 with
                                             | (req, ens) ->
                                                 (match ens.FStarC_SMTEncoding_Term.tm
                                                  with
                                                  | FStarC_SMTEncoding_Term.Quant
                                                      (FStarC_SMTEncoding_Term.Forall,
                                                       pats_ens, iopt_ens,
                                                       sorts_ens,
                                                       {
                                                         FStarC_SMTEncoding_Term.tm
                                                           =
                                                           FStarC_SMTEncoding_Term.App
                                                           (FStarC_SMTEncoding_Term.Imp,
                                                            ensures_conjuncts::post1::[]);
                                                         FStarC_SMTEncoding_Term.freevars
                                                           = uu___6;
                                                         FStarC_SMTEncoding_Term.rng
                                                           = rng_ens;_})
                                                      ->
                                                      let uu___7 =
                                                        is_a_post_condition
                                                          (FStar_Pervasives_Native.Some
                                                             post_name) post1 in
                                                      if uu___7
                                                      then
                                                        let uu___8 =
                                                          let uu___9 =
                                                            FStarC_Errors_Msg.mkmsg
                                                              "Could not prove post-condition" in
                                                          aux uu___9
                                                            FStar_Pervasives_Native.None
                                                            (FStar_Pervasives_Native.Some
                                                               post_name)
                                                            labels1
                                                            ensures_conjuncts in
                                                        (match uu___8 with
                                                         | (labels2,
                                                            ensures_conjuncts1)
                                                             ->
                                                             let pats_ens1 =
                                                               match pats_ens
                                                               with
                                                               | [] ->
                                                                   [[post1]]
                                                               | []::[] ->
                                                                   [[post1]]
                                                               | uu___9 ->
                                                                   pats_ens in
                                                             let ens1 =
                                                               let uu___9 =
                                                                 let uu___10
                                                                   =
                                                                   let uu___11
                                                                    =
                                                                    FStarC_SMTEncoding_Term.mk
                                                                    (FStarC_SMTEncoding_Term.App
                                                                    (FStarC_SMTEncoding_Term.Imp,
                                                                    [ensures_conjuncts1;
                                                                    post1]))
                                                                    rng_ens in
                                                                   (FStarC_SMTEncoding_Term.Forall,
                                                                    pats_ens1,
                                                                    iopt_ens,
                                                                    sorts_ens,
                                                                    uu___11) in
                                                                 FStarC_SMTEncoding_Term.Quant
                                                                   uu___10 in
                                                               FStarC_SMTEncoding_Term.mk
                                                                 uu___9
                                                                 ens.FStarC_SMTEncoding_Term.rng in
                                                             let lhs2 =
                                                               FStarC_SMTEncoding_Term.mk
                                                                 (FStarC_SMTEncoding_Term.App
                                                                    (FStarC_SMTEncoding_Term.And,
                                                                    (FStarC_Compiler_List.op_At
                                                                    req
                                                                    [ens1])))
                                                                 lhs1.FStarC_SMTEncoding_Term.rng in
                                                             let uu___9 =
                                                               FStarC_SMTEncoding_Term.abstr
                                                                 names lhs2 in
                                                             (labels2,
                                                               uu___9))
                                                      else
                                                        (let uu___9 =
                                                           let uu___10 =
                                                             let uu___11 =
                                                               let uu___12 =
                                                                 let uu___13
                                                                   =
                                                                   FStarC_SMTEncoding_Term.print_smt_term
                                                                    post1 in
                                                                 Prims.strcat
                                                                   "  ... "
                                                                   uu___13 in
                                                               Prims.strcat
                                                                 post_name
                                                                 uu___12 in
                                                             Prims.strcat
                                                               "Ensures clause doesn't match post name:  "
                                                               uu___11 in
                                                           Not_a_wp_implication
                                                             uu___10 in
                                                         FStarC_Compiler_Effect.raise
                                                           uu___9)
                                                  | uu___6 ->
                                                      let uu___7 =
                                                        let uu___8 =
                                                          let uu___9 =
                                                            let uu___10 =
                                                              let uu___11 =
                                                                FStarC_SMTEncoding_Term.print_smt_term
                                                                  ens in
                                                              Prims.strcat
                                                                "  ... "
                                                                uu___11 in
                                                            Prims.strcat
                                                              post_name
                                                              uu___10 in
                                                          Prims.strcat
                                                            "Ensures clause doesn't have the expected shape for post-condition "
                                                            uu___9 in
                                                        Not_a_wp_implication
                                                          uu___8 in
                                                      FStarC_Compiler_Effect.raise
                                                        uu___7))
                                        | uu___5 ->
                                            let uu___6 =
                                              let uu___7 =
                                                let uu___8 =
                                                  FStarC_SMTEncoding_Term.print_smt_term
                                                    lhs1 in
                                                Prims.strcat
                                                  "LHS not a conjunct: "
                                                  uu___8 in
                                              Not_a_wp_implication uu___7 in
                                            FStarC_Compiler_Effect.raise
                                              uu___6 in
                                      (match uu___4 with
                                       | (labels2, lhs2) ->
                                           let uu___5 =
                                             let uu___6 =
                                               aux default_msg
                                                 FStar_Pervasives_Native.None
                                                 (FStar_Pervasives_Native.Some
                                                    post_name) labels2 rhs1 in
                                             match uu___6 with
                                             | (labels3, rhs2) ->
                                                 let uu___7 =
                                                   FStarC_SMTEncoding_Term.abstr
                                                     names rhs2 in
                                                 (labels3, uu___7) in
                                           (match uu___5 with
                                            | (labels3, rhs2) ->
                                                let body =
                                                  FStarC_SMTEncoding_Term.mkImp
                                                    (lhs2, rhs2) rng in
                                                let uu___6 =
                                                  FStarC_SMTEncoding_Term.mk
                                                    (FStarC_SMTEncoding_Term.Quant
                                                       (FStarC_SMTEncoding_Term.Forall,
                                                         pats, iopt, (post ::
                                                         sorts), body))
                                                    q1.FStarC_SMTEncoding_Term.rng in
                                                (labels3, uu___6))))
                             | uu___2 -> fallback "arg not a quant: ")) ()
                   with | Not_a_wp_implication msg1 -> fallback msg1)
              | FStarC_SMTEncoding_Term.Labeled (arg, reason, r1) ->
                  aux reason (FStar_Pervasives_Native.Some r1) post_name_opt
                    labels1 arg
              | FStarC_SMTEncoding_Term.Quant
                  (FStarC_SMTEncoding_Term.Forall, [],
                   FStar_Pervasives_Native.None, sorts,
                   {
                     FStarC_SMTEncoding_Term.tm = FStarC_SMTEncoding_Term.App
                       (FStarC_SMTEncoding_Term.Imp, lhs::rhs::[]);
                     FStarC_SMTEncoding_Term.freevars = uu___1;
                     FStarC_SMTEncoding_Term.rng = rng;_})
                  when is_a_named_continuation lhs ->
                  let uu___2 = FStarC_Compiler_Util.prefix sorts in
                  (match uu___2 with
                   | (sorts', post) ->
                       let new_post_name =
                         let uu___3 =
                           let uu___4 = FStarC_GenSym.next_id () in
                           FStarC_Compiler_Util.string_of_int uu___4 in
                         Prims.strcat "^^post_condition_" uu___3 in
                       let names =
                         let uu___3 =
                           FStarC_Compiler_List.map
                             (fun s ->
                                let uu___4 =
                                  let uu___5 =
                                    let uu___6 =
                                      let uu___7 = FStarC_GenSym.next_id () in
                                      FStarC_Compiler_Util.string_of_int
                                        uu___7 in
                                    Prims.strcat "^^" uu___6 in
                                  (uu___5, s) in
                                FStarC_SMTEncoding_Term.mk_fv uu___4) sorts' in
                         let uu___4 =
                           let uu___5 =
                             FStarC_SMTEncoding_Term.mk_fv
                               (new_post_name, post) in
                           [uu___5] in
                         FStarC_Compiler_List.op_At uu___3 uu___4 in
                       let instantiation =
                         FStarC_Compiler_List.map
                           FStarC_SMTEncoding_Util.mkFreeV names in
                       let uu___3 =
                         let uu___4 =
                           FStarC_SMTEncoding_Term.inst instantiation lhs in
                         let uu___5 =
                           FStarC_SMTEncoding_Term.inst instantiation rhs in
                         (uu___4, uu___5) in
                       (match uu___3 with
                        | (lhs1, rhs1) ->
                            let uu___4 =
                              FStarC_Compiler_Util.fold_map
                                (fun labels2 ->
                                   fun tm ->
                                     match tm.FStarC_SMTEncoding_Term.tm with
                                     | FStarC_SMTEncoding_Term.Quant
                                         (FStarC_SMTEncoding_Term.Forall,
                                          ({
                                             FStarC_SMTEncoding_Term.tm =
                                               FStarC_SMTEncoding_Term.App
                                               (FStarC_SMTEncoding_Term.Var
                                                "Prims.guard_free", p::[]);
                                             FStarC_SMTEncoding_Term.freevars
                                               = uu___5;
                                             FStarC_SMTEncoding_Term.rng =
                                               uu___6;_}::[])::[],
                                          iopt, sorts1,
                                          {
                                            FStarC_SMTEncoding_Term.tm =
                                              FStarC_SMTEncoding_Term.App
                                              (FStarC_SMTEncoding_Term.Imp,
                                               l0::r1::[]);
                                            FStarC_SMTEncoding_Term.freevars
                                              = uu___7;
                                            FStarC_SMTEncoding_Term.rng =
                                              uu___8;_})
                                         ->
                                         let uu___9 =
                                           is_a_post_condition
                                             (FStar_Pervasives_Native.Some
                                                new_post_name) r1 in
                                         if uu___9
                                         then
                                           let uu___10 =
                                             aux default_msg
                                               FStar_Pervasives_Native.None
                                               post_name_opt labels2 l0 in
                                           (match uu___10 with
                                            | (labels3, l) ->
                                                let uu___11 =
                                                  let uu___12 =
                                                    let uu___13 =
                                                      let uu___14 =
                                                        FStarC_SMTEncoding_Util.norng
                                                          FStarC_SMTEncoding_Term.mk
                                                          (FStarC_SMTEncoding_Term.App
                                                             (FStarC_SMTEncoding_Term.Imp,
                                                               [l; r1])) in
                                                      (FStarC_SMTEncoding_Term.Forall,
                                                        [[p]],
                                                        (FStar_Pervasives_Native.Some
                                                           Prims.int_zero),
                                                        sorts1, uu___14) in
                                                    FStarC_SMTEncoding_Term.Quant
                                                      uu___13 in
                                                  FStarC_SMTEncoding_Term.mk
                                                    uu___12
                                                    q1.FStarC_SMTEncoding_Term.rng in
                                                (labels3, uu___11))
                                         else (labels2, tm)
                                     | uu___5 -> (labels2, tm)) labels1
                                (conjuncts lhs1) in
                            (match uu___4 with
                             | (labels2, lhs_conjs) ->
                                 let uu___5 =
                                   aux default_msg
                                     FStar_Pervasives_Native.None
                                     (FStar_Pervasives_Native.Some
                                        new_post_name) labels2 rhs1 in
                                 (match uu___5 with
                                  | (labels3, rhs2) ->
                                      let body =
                                        let uu___6 =
                                          let uu___7 =
                                            let uu___8 =
                                              FStarC_SMTEncoding_Term.mk_and_l
                                                lhs_conjs
                                                lhs1.FStarC_SMTEncoding_Term.rng in
                                            (uu___8, rhs2) in
                                          FStarC_SMTEncoding_Term.mkImp
                                            uu___7 rng in
                                        FStarC_SMTEncoding_Term.abstr names
                                          uu___6 in
                                      let q2 =
                                        FStarC_SMTEncoding_Term.mk
                                          (FStarC_SMTEncoding_Term.Quant
                                             (FStarC_SMTEncoding_Term.Forall,
                                               [],
                                               FStar_Pervasives_Native.None,
                                               sorts, body))
                                          q1.FStarC_SMTEncoding_Term.rng in
                                      (labels3, q2)))))
              | FStarC_SMTEncoding_Term.App
                  (FStarC_SMTEncoding_Term.Imp, lhs::rhs::[]) ->
                  let uu___1 = aux default_msg ropt post_name_opt labels1 rhs in
                  (match uu___1 with
                   | (labels2, rhs1) ->
                       let uu___2 = FStarC_SMTEncoding_Util.mkImp (lhs, rhs1) in
                       (labels2, uu___2))
              | FStarC_SMTEncoding_Term.App
                  (FStarC_SMTEncoding_Term.And, conjuncts1) ->
                  let uu___1 =
                    FStarC_Compiler_Util.fold_map
                      (aux default_msg ropt post_name_opt) labels1 conjuncts1 in
                  (match uu___1 with
                   | (labels2, conjuncts2) ->
                       let uu___2 =
                         FStarC_SMTEncoding_Term.mk_and_l conjuncts2
                           q1.FStarC_SMTEncoding_Term.rng in
                       (labels2, uu___2))
              | FStarC_SMTEncoding_Term.App
                  (FStarC_SMTEncoding_Term.ITE, hd::q11::q2::[]) ->
                  let uu___1 = aux default_msg ropt post_name_opt labels1 q11 in
                  (match uu___1 with
                   | (labels2, q12) ->
                       let uu___2 =
                         aux default_msg ropt post_name_opt labels2 q2 in
                       (match uu___2 with
                        | (labels3, q21) ->
                            let uu___3 =
                              FStarC_SMTEncoding_Term.mkITE (hd, q12, q21)
                                q1.FStarC_SMTEncoding_Term.rng in
                            (labels3, uu___3)))
              | FStarC_SMTEncoding_Term.Quant
                  (FStarC_SMTEncoding_Term.Exists, uu___1, uu___2, uu___3,
                   uu___4)
                  ->
                  let uu___5 =
                    fresh_label1 default_msg ropt
                      q1.FStarC_SMTEncoding_Term.rng q1 in
                  (match uu___5 with | (lab, q2) -> ((lab :: labels1), q2))
              | FStarC_SMTEncoding_Term.App
                  (FStarC_SMTEncoding_Term.Iff, uu___1) ->
                  let uu___2 =
                    fresh_label1 default_msg ropt
                      q1.FStarC_SMTEncoding_Term.rng q1 in
                  (match uu___2 with | (lab, q2) -> ((lab :: labels1), q2))
              | FStarC_SMTEncoding_Term.App
                  (FStarC_SMTEncoding_Term.Or, uu___1) ->
                  let uu___2 =
                    fresh_label1 default_msg ropt
                      q1.FStarC_SMTEncoding_Term.rng q1 in
                  (match uu___2 with | (lab, q2) -> ((lab :: labels1), q2))
              | FStarC_SMTEncoding_Term.App
                  (FStarC_SMTEncoding_Term.Var "Unreachable", uu___1) ->
                  (labels1, q1)
              | FStarC_SMTEncoding_Term.App
                  (FStarC_SMTEncoding_Term.Var uu___1, uu___2) when
                  is_a_post_condition post_name_opt q1 -> (labels1, q1)
              | FStarC_SMTEncoding_Term.FreeV uu___1 ->
                  let uu___2 =
                    fresh_label1 default_msg ropt
                      q1.FStarC_SMTEncoding_Term.rng q1 in
                  (match uu___2 with | (lab, q2) -> ((lab :: labels1), q2))
              | FStarC_SMTEncoding_Term.App
                  (FStarC_SMTEncoding_Term.TrueOp, uu___1) ->
                  let uu___2 =
                    fresh_label1 default_msg ropt
                      q1.FStarC_SMTEncoding_Term.rng q1 in
                  (match uu___2 with | (lab, q2) -> ((lab :: labels1), q2))
              | FStarC_SMTEncoding_Term.App
                  (FStarC_SMTEncoding_Term.FalseOp, uu___1) ->
                  let uu___2 =
                    fresh_label1 default_msg ropt
                      q1.FStarC_SMTEncoding_Term.rng q1 in
                  (match uu___2 with | (lab, q2) -> ((lab :: labels1), q2))
              | FStarC_SMTEncoding_Term.App
                  (FStarC_SMTEncoding_Term.Not, uu___1) ->
                  let uu___2 =
                    fresh_label1 default_msg ropt
                      q1.FStarC_SMTEncoding_Term.rng q1 in
                  (match uu___2 with | (lab, q2) -> ((lab :: labels1), q2))
              | FStarC_SMTEncoding_Term.App
                  (FStarC_SMTEncoding_Term.Eq, uu___1) ->
                  let uu___2 =
                    fresh_label1 default_msg ropt
                      q1.FStarC_SMTEncoding_Term.rng q1 in
                  (match uu___2 with | (lab, q2) -> ((lab :: labels1), q2))
              | FStarC_SMTEncoding_Term.App
                  (FStarC_SMTEncoding_Term.LT, uu___1) ->
                  let uu___2 =
                    fresh_label1 default_msg ropt
                      q1.FStarC_SMTEncoding_Term.rng q1 in
                  (match uu___2 with | (lab, q2) -> ((lab :: labels1), q2))
              | FStarC_SMTEncoding_Term.App
                  (FStarC_SMTEncoding_Term.LTE, uu___1) ->
                  let uu___2 =
                    fresh_label1 default_msg ropt
                      q1.FStarC_SMTEncoding_Term.rng q1 in
                  (match uu___2 with | (lab, q2) -> ((lab :: labels1), q2))
              | FStarC_SMTEncoding_Term.App
                  (FStarC_SMTEncoding_Term.GT, uu___1) ->
                  let uu___2 =
                    fresh_label1 default_msg ropt
                      q1.FStarC_SMTEncoding_Term.rng q1 in
                  (match uu___2 with | (lab, q2) -> ((lab :: labels1), q2))
              | FStarC_SMTEncoding_Term.App
                  (FStarC_SMTEncoding_Term.GTE, uu___1) ->
                  let uu___2 =
                    fresh_label1 default_msg ropt
                      q1.FStarC_SMTEncoding_Term.rng q1 in
                  (match uu___2 with | (lab, q2) -> ((lab :: labels1), q2))
              | FStarC_SMTEncoding_Term.App
                  (FStarC_SMTEncoding_Term.BvUlt, uu___1) ->
                  let uu___2 =
                    fresh_label1 default_msg ropt
                      q1.FStarC_SMTEncoding_Term.rng q1 in
                  (match uu___2 with | (lab, q2) -> ((lab :: labels1), q2))
              | FStarC_SMTEncoding_Term.App
                  (FStarC_SMTEncoding_Term.Var uu___1, uu___2) ->
                  let uu___3 =
                    fresh_label1 default_msg ropt
                      q1.FStarC_SMTEncoding_Term.rng q1 in
                  (match uu___3 with | (lab, q2) -> ((lab :: labels1), q2))
              | FStarC_SMTEncoding_Term.App
                  (FStarC_SMTEncoding_Term.RealDiv, uu___1) ->
                  failwith "Impossible: non-propositional term"
              | FStarC_SMTEncoding_Term.App
                  (FStarC_SMTEncoding_Term.Add, uu___1) ->
                  failwith "Impossible: non-propositional term"
              | FStarC_SMTEncoding_Term.App
                  (FStarC_SMTEncoding_Term.Sub, uu___1) ->
                  failwith "Impossible: non-propositional term"
              | FStarC_SMTEncoding_Term.App
                  (FStarC_SMTEncoding_Term.Div, uu___1) ->
                  failwith "Impossible: non-propositional term"
              | FStarC_SMTEncoding_Term.App
                  (FStarC_SMTEncoding_Term.Mul, uu___1) ->
                  failwith "Impossible: non-propositional term"
              | FStarC_SMTEncoding_Term.App
                  (FStarC_SMTEncoding_Term.Minus, uu___1) ->
                  failwith "Impossible: non-propositional term"
              | FStarC_SMTEncoding_Term.App
                  (FStarC_SMTEncoding_Term.Mod, uu___1) ->
                  failwith "Impossible: non-propositional term"
              | FStarC_SMTEncoding_Term.App
                  (FStarC_SMTEncoding_Term.BvAnd, uu___1) ->
                  failwith "Impossible: non-propositional term"
              | FStarC_SMTEncoding_Term.App
                  (FStarC_SMTEncoding_Term.BvXor, uu___1) ->
                  failwith "Impossible: non-propositional term"
              | FStarC_SMTEncoding_Term.App
                  (FStarC_SMTEncoding_Term.BvOr, uu___1) ->
                  failwith "Impossible: non-propositional term"
              | FStarC_SMTEncoding_Term.App
                  (FStarC_SMTEncoding_Term.BvAdd, uu___1) ->
                  failwith "Impossible: non-propositional term"
              | FStarC_SMTEncoding_Term.App
                  (FStarC_SMTEncoding_Term.BvSub, uu___1) ->
                  failwith "Impossible: non-propositional term"
              | FStarC_SMTEncoding_Term.App
                  (FStarC_SMTEncoding_Term.BvShl, uu___1) ->
                  failwith "Impossible: non-propositional term"
              | FStarC_SMTEncoding_Term.App
                  (FStarC_SMTEncoding_Term.BvShr, uu___1) ->
                  failwith "Impossible: non-propositional term"
              | FStarC_SMTEncoding_Term.App
                  (FStarC_SMTEncoding_Term.BvUdiv, uu___1) ->
                  failwith "Impossible: non-propositional term"
              | FStarC_SMTEncoding_Term.App
                  (FStarC_SMTEncoding_Term.BvMod, uu___1) ->
                  failwith "Impossible: non-propositional term"
              | FStarC_SMTEncoding_Term.App
                  (FStarC_SMTEncoding_Term.BvMul, uu___1) ->
                  failwith "Impossible: non-propositional term"
              | FStarC_SMTEncoding_Term.App
                  (FStarC_SMTEncoding_Term.BvUext uu___1, uu___2) ->
                  failwith "Impossible: non-propositional term"
              | FStarC_SMTEncoding_Term.App
                  (FStarC_SMTEncoding_Term.BvToNat, uu___1) ->
                  failwith "Impossible: non-propositional term"
              | FStarC_SMTEncoding_Term.App
                  (FStarC_SMTEncoding_Term.NatToBv uu___1, uu___2) ->
                  failwith "Impossible: non-propositional term"
              | FStarC_SMTEncoding_Term.App
                  (FStarC_SMTEncoding_Term.ITE, uu___1) ->
                  failwith "Impossible: arity mismatch"
              | FStarC_SMTEncoding_Term.App
                  (FStarC_SMTEncoding_Term.Imp, uu___1) ->
                  failwith "Impossible: arity mismatch"
              | FStarC_SMTEncoding_Term.Quant
                  (FStarC_SMTEncoding_Term.Forall, pats, iopt, sorts, body)
                  ->
                  let uu___1 =
                    aux default_msg ropt post_name_opt labels1 body in
                  (match uu___1 with
                   | (labels2, body1) ->
                       let uu___2 =
                         FStarC_SMTEncoding_Term.mk
                           (FStarC_SMTEncoding_Term.Quant
                              (FStarC_SMTEncoding_Term.Forall, pats, iopt,
                                sorts, body1)) q1.FStarC_SMTEncoding_Term.rng in
                       (labels2, uu___2))
              | FStarC_SMTEncoding_Term.Let (es, body) ->
                  let uu___1 =
                    aux default_msg ropt post_name_opt labels1 body in
                  (match uu___1 with
                   | (labels2, body1) ->
                       let uu___2 =
                         FStarC_SMTEncoding_Term.mkLet (es, body1)
                           q1.FStarC_SMTEncoding_Term.rng in
                       (labels2, uu___2)) in
            (FStarC_Compiler_Effect.op_Colon_Equals __ctr Prims.int_zero;
             (let uu___2 = FStarC_Errors_Msg.mkmsg "Assertion failed" in
              aux uu___2 FStar_Pervasives_Native.None
                FStar_Pervasives_Native.None [] q))
let (detail_errors :
  Prims.bool ->
    FStarC_TypeChecker_Env.env ->
      labels ->
        (FStarC_SMTEncoding_Term.decl Prims.list ->
           FStarC_SMTEncoding_Z3.z3result)
          -> unit)
  =
  fun hint_replay ->
    fun env ->
      fun all_labels ->
        fun askZ3 ->
          let print_banner uu___ =
            let msg1 =
              let uu___1 =
                let uu___2 = FStarC_TypeChecker_Env.get_range env in
                FStarC_Compiler_Range_Ops.string_of_range uu___2 in
              let uu___2 =
                FStarC_Compiler_Util.string_of_int (Prims.of_int (5)) in
              let uu___3 =
                FStarC_Compiler_Util.string_of_int
                  (FStarC_Compiler_List.length all_labels) in
              FStarC_Compiler_Util.format4
                "Detailed %s report follows for %s\nTaking %s seconds per proof obligation (%s proofs in total)\n"
                (if hint_replay then "hint replay" else "error") uu___1
                uu___2 uu___3 in
            FStarC_Compiler_Util.print_error msg1 in
          let print_result uu___ =
            match uu___ with
            | ((uu___1, msg1, r), success) ->
                if success
                then
                  let uu___2 = FStarC_Compiler_Range_Ops.string_of_range r in
                  FStarC_Compiler_Util.print1
                    "OK: proof obligation at %s was proven in isolation\n"
                    uu___2
                else
                  if hint_replay
                  then
                    (let uu___3 =
                       let uu___4 =
                         FStarC_Errors_Msg.text
                           "Hint failed to replay this sub-proof" in
                       uu___4 :: msg1 in
                     FStarC_Errors.log_issue
                       FStarC_Class_HasRange.hasRange_range r
                       FStarC_Errors_Codes.Warning_HintFailedToReplayProof ()
                       (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
                       (Obj.magic uu___3))
                  else
                    (let uu___4 =
                       let uu___5 =
                         let uu___6 =
                           let uu___7 =
                             let uu___8 =
                               FStarC_Class_Show.show
                                 FStarC_Compiler_Range_Ops.showable_range r in
                             FStarC_Compiler_Util.format1
                               "XX: proof obligation at %s failed." uu___8 in
                           FStarC_Errors_Msg.text uu___7 in
                         [uu___6] in
                       FStarC_Compiler_List.op_At uu___5 msg1 in
                     FStarC_Errors.log_issue
                       FStarC_Class_HasRange.hasRange_range r
                       FStarC_Errors_Codes.Error_ProofObligationFailed ()
                       (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
                       (Obj.magic uu___4)) in
          let elim labs =
            FStarC_Compiler_List.map
              (fun uu___ ->
                 match uu___ with
                 | (l, uu___1, uu___2) ->
                     let tm =
                       let uu___3 =
                         let uu___4 = FStarC_SMTEncoding_Util.mkFreeV l in
                         (uu___4, FStarC_SMTEncoding_Util.mkTrue) in
                       FStarC_SMTEncoding_Util.mkEq uu___3 in
                     let a =
                       let uu___3 =
                         let uu___4 =
                           let uu___5 = FStarC_SMTEncoding_Util.mkFreeV l in
                           (uu___5, FStarC_SMTEncoding_Util.mkTrue) in
                         FStarC_SMTEncoding_Util.mkEq uu___4 in
                       let uu___4 =
                         let uu___5 = FStarC_SMTEncoding_Term.fv_name l in
                         Prims.strcat "@disable_label_" uu___5 in
                       let uu___5 =
                         FStarC_SMTEncoding_Term.free_top_level_names tm in
                       {
                         FStarC_SMTEncoding_Term.assumption_term = uu___3;
                         FStarC_SMTEncoding_Term.assumption_caption =
                           (FStar_Pervasives_Native.Some "Disabling label");
                         FStarC_SMTEncoding_Term.assumption_name = uu___4;
                         FStarC_SMTEncoding_Term.assumption_fact_ids = [];
                         FStarC_SMTEncoding_Term.assumption_free_names =
                           uu___5
                       } in
                     FStarC_SMTEncoding_Term.Assume a) labs in
          let rec linear_check eliminated errors active =
            FStarC_SMTEncoding_Z3.refresh
              (FStar_Pervasives_Native.Some
                 (env.FStarC_TypeChecker_Env.proof_ns));
            (match active with
             | [] ->
                 let results =
                   let uu___1 =
                     FStarC_Compiler_List.map (fun x -> (x, true)) eliminated in
                   let uu___2 =
                     FStarC_Compiler_List.map (fun x -> (x, false)) errors in
                   FStarC_Compiler_List.op_At uu___1 uu___2 in
                 sort_labels results
             | hd::tl ->
                 ((let uu___2 =
                     FStarC_Compiler_Util.string_of_int
                       (FStarC_Compiler_List.length active) in
                   FStarC_Compiler_Util.print1 "%s, " uu___2);
                  (let decls =
                     elim
                       (FStarC_Compiler_List.op_At eliminated
                          (FStarC_Compiler_List.op_At errors tl)) in
                   let result = askZ3 decls in
                   match result.FStarC_SMTEncoding_Z3.z3result_status with
                   | FStarC_SMTEncoding_Z3.UNSAT uu___2 ->
                       linear_check (hd :: eliminated) errors tl
                   | uu___2 -> linear_check eliminated (hd :: errors) tl))) in
          print_banner ();
          FStarC_Options.set_option "z3rlimit"
            (FStarC_Options.Int (Prims.of_int (5)));
          (let res = linear_check [] [] all_labels in
           FStarC_Compiler_Util.print_string "\n";
           FStarC_Compiler_List.iter print_result res;
           (let uu___4 =
              FStarC_Compiler_Util.for_all FStar_Pervasives_Native.snd res in
            if uu___4
            then
              FStarC_Compiler_Util.print_string
                "Failed: the heuristic of trying each proof in isolation failed to identify a precise error\n"
            else ()))