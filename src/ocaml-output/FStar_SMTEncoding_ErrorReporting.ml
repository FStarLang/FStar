open Prims
type label = FStar_SMTEncoding_Term.error_label
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
  (FStar_SMTEncoding_Term.error_label * Prims.bool) Prims.list ->
    ((FStar_SMTEncoding_Term.fv * Prims.string * FStar_Compiler_Range.range)
      * Prims.bool) Prims.list)
  =
  fun l ->
    FStar_Compiler_List.sortWith
      (fun uu___ ->
         fun uu___1 ->
           match (uu___, uu___1) with
           | (((uu___2, uu___3, r1), uu___4), ((uu___5, uu___6, r2), uu___7))
               -> FStar_Compiler_Range.compare r1 r2) l
let (remove_dups :
  labels ->
    (FStar_SMTEncoding_Term.fv * Prims.string * FStar_Compiler_Range.range)
      Prims.list)
  =
  fun l ->
    FStar_Compiler_Util.remove_dups
      (fun uu___ ->
         fun uu___1 ->
           match (uu___, uu___1) with
           | ((uu___2, m1, r1), (uu___3, m2, r2)) -> (r1 = r2) && (m1 = m2))
      l
type msg = (Prims.string * FStar_Compiler_Range.range)
type ranges =
  (Prims.string FStar_Pervasives_Native.option * FStar_Compiler_Range.range)
    Prims.list
let (fresh_label :
  Prims.string ->
    FStar_Compiler_Range.range ->
      FStar_SMTEncoding_Term.term -> (label * FStar_SMTEncoding_Term.term))
  =
  let ctr = FStar_Compiler_Util.mk_ref Prims.int_zero in
  fun message ->
    fun range ->
      fun t ->
        let l =
          FStar_Compiler_Util.incr ctr;
          (let uu___1 =
             let uu___2 = FStar_Compiler_Effect.op_Bang ctr in
             FStar_Compiler_Util.string_of_int uu___2 in
           FStar_Compiler_Util.format1 "label_%s" uu___1) in
        let lvar =
          FStar_SMTEncoding_Term.mk_fv (l, FStar_SMTEncoding_Term.Bool_sort) in
        let label1 = (lvar, message, range) in
        let lterm = FStar_SMTEncoding_Util.mkFreeV lvar in
        let lt = FStar_SMTEncoding_Term.mkOr (lterm, t) range in (label1, lt)
let (label_goals :
  (unit -> Prims.string) FStar_Pervasives_Native.option ->
    FStar_Compiler_Range.range ->
      FStar_SMTEncoding_Term.term -> (labels * FStar_SMTEncoding_Term.term))
  =
  fun use_env_msg ->
    fun r ->
      fun q ->
        let rec is_a_post_condition post_name_opt tm =
          match (post_name_opt, (tm.FStar_SMTEncoding_Term.tm)) with
          | (FStar_Pervasives_Native.None, uu___) -> false
          | (FStar_Pervasives_Native.Some nm, FStar_SMTEncoding_Term.FreeV
             fv) ->
              let uu___ = FStar_SMTEncoding_Term.fv_name fv in nm = uu___
          | (uu___, FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var "Valid", tm1::[])) ->
              is_a_post_condition post_name_opt tm1
          | (uu___, FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var "ApplyTT", tm1::uu___1)) ->
              is_a_post_condition post_name_opt tm1
          | uu___ -> false in
        let conjuncts t =
          match t.FStar_SMTEncoding_Term.tm with
          | FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And, cs) -> cs
          | uu___ -> [t] in
        let is_guard_free tm =
          match tm.FStar_SMTEncoding_Term.tm with
          | FStar_SMTEncoding_Term.Quant
              (FStar_SMTEncoding_Term.Forall,
               ({
                  FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App
                    (FStar_SMTEncoding_Term.Var "Prims.guard_free", p::[]);
                  FStar_SMTEncoding_Term.freevars = uu___;
                  FStar_SMTEncoding_Term.rng = uu___1;_}::[])::[],
               iopt, uu___2,
               {
                 FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App
                   (FStar_SMTEncoding_Term.Imp, l::r1::[]);
                 FStar_SMTEncoding_Term.freevars = uu___3;
                 FStar_SMTEncoding_Term.rng = uu___4;_})
              -> true
          | uu___ -> false in
        let is_a_named_continuation lhs =
          FStar_Compiler_Effect.op_Bar_Greater (conjuncts lhs)
            (FStar_Compiler_Util.for_some is_guard_free) in
        let uu___ =
          match use_env_msg with
          | FStar_Pervasives_Native.None -> (false, "")
          | FStar_Pervasives_Native.Some f ->
              let uu___1 = f () in (true, uu___1) in
        match uu___ with
        | (flag, msg_prefix) ->
            let fresh_label1 msg1 ropt rng t =
              let msg2 =
                if flag
                then
                  Prims.op_Hat "Failed to verify implicit argument: "
                    (Prims.op_Hat msg_prefix (Prims.op_Hat " :: " msg1))
                else msg1 in
              let rng1 =
                match ropt with
                | FStar_Pervasives_Native.None -> rng
                | FStar_Pervasives_Native.Some r1 ->
                    let uu___1 =
                      let uu___2 = FStar_Compiler_Range.use_range rng in
                      let uu___3 = FStar_Compiler_Range.use_range r1 in
                      FStar_Compiler_Range.rng_included uu___2 uu___3 in
                    if uu___1
                    then rng
                    else
                      (let uu___3 = FStar_Compiler_Range.def_range rng in
                       FStar_Compiler_Range.set_def_range r1 uu___3) in
              fresh_label msg2 rng1 t in
            let rec aux default_msg ropt post_name_opt labels1 q1 =
              match q1.FStar_SMTEncoding_Term.tm with
              | FStar_SMTEncoding_Term.BoundV uu___1 -> (labels1, q1)
              | FStar_SMTEncoding_Term.Integer uu___1 -> (labels1, q1)
              | FStar_SMTEncoding_Term.String uu___1 -> (labels1, q1)
              | FStar_SMTEncoding_Term.Real uu___1 -> (labels1, q1)
              | FStar_SMTEncoding_Term.LblPos uu___1 -> failwith "Impossible"
              | FStar_SMTEncoding_Term.Labeled (arg, msg1, label_range) when
                  msg1 = "could not prove post-condition" ->
                  let fallback debug_msg =
                    aux default_msg
                      (FStar_Pervasives_Native.Some label_range)
                      post_name_opt labels1 arg in
                  (try
                     (fun uu___1 ->
                        match () with
                        | () ->
                            (match arg.FStar_SMTEncoding_Term.tm with
                             | FStar_SMTEncoding_Term.Quant
                                 (FStar_SMTEncoding_Term.Forall, pats, iopt,
                                  post::sorts,
                                  {
                                    FStar_SMTEncoding_Term.tm =
                                      FStar_SMTEncoding_Term.App
                                      (FStar_SMTEncoding_Term.Imp,
                                       lhs::rhs::[]);
                                    FStar_SMTEncoding_Term.freevars = uu___2;
                                    FStar_SMTEncoding_Term.rng = rng;_})
                                 ->
                                 let post_name =
                                   let uu___3 =
                                     let uu___4 = FStar_Ident.next_id () in
                                     FStar_Compiler_Effect.op_Less_Bar
                                       FStar_Compiler_Util.string_of_int
                                       uu___4 in
                                   Prims.op_Hat "^^post_condition_" uu___3 in
                                 let names =
                                   let uu___3 =
                                     FStar_SMTEncoding_Term.mk_fv
                                       (post_name, post) in
                                   let uu___4 =
                                     FStar_Compiler_List.map
                                       (fun s ->
                                          let uu___5 =
                                            let uu___6 =
                                              let uu___7 =
                                                let uu___8 =
                                                  FStar_Ident.next_id () in
                                                FStar_Compiler_Effect.op_Less_Bar
                                                  FStar_Compiler_Util.string_of_int
                                                  uu___8 in
                                              Prims.op_Hat "^^" uu___7 in
                                            (uu___6, s) in
                                          FStar_SMTEncoding_Term.mk_fv uu___5)
                                       sorts in
                                   uu___3 :: uu___4 in
                                 let instantiation =
                                   FStar_Compiler_List.map
                                     FStar_SMTEncoding_Util.mkFreeV names in
                                 let uu___3 =
                                   let uu___4 =
                                     FStar_SMTEncoding_Term.inst
                                       instantiation lhs in
                                   let uu___5 =
                                     FStar_SMTEncoding_Term.inst
                                       instantiation rhs in
                                   (uu___4, uu___5) in
                                 (match uu___3 with
                                  | (lhs1, rhs1) ->
                                      let uu___4 =
                                        match lhs1.FStar_SMTEncoding_Term.tm
                                        with
                                        | FStar_SMTEncoding_Term.App
                                            (FStar_SMTEncoding_Term.And,
                                             clauses_lhs)
                                            ->
                                            let uu___5 =
                                              FStar_Compiler_Util.prefix
                                                clauses_lhs in
                                            (match uu___5 with
                                             | (req, ens) ->
                                                 (match ens.FStar_SMTEncoding_Term.tm
                                                  with
                                                  | FStar_SMTEncoding_Term.Quant
                                                      (FStar_SMTEncoding_Term.Forall,
                                                       pats_ens, iopt_ens,
                                                       sorts_ens,
                                                       {
                                                         FStar_SMTEncoding_Term.tm
                                                           =
                                                           FStar_SMTEncoding_Term.App
                                                           (FStar_SMTEncoding_Term.Imp,
                                                            ensures_conjuncts::post1::[]);
                                                         FStar_SMTEncoding_Term.freevars
                                                           = uu___6;
                                                         FStar_SMTEncoding_Term.rng
                                                           = rng_ens;_})
                                                      ->
                                                      let uu___7 =
                                                        is_a_post_condition
                                                          (FStar_Pervasives_Native.Some
                                                             post_name) post1 in
                                                      if uu___7
                                                      then
                                                        let uu___8 =
                                                          aux
                                                            "could not prove post-condition"
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
                                                                    FStar_SMTEncoding_Term.mk
                                                                    (FStar_SMTEncoding_Term.App
                                                                    (FStar_SMTEncoding_Term.Imp,
                                                                    [ensures_conjuncts1;
                                                                    post1]))
                                                                    rng_ens in
                                                                   (FStar_SMTEncoding_Term.Forall,
                                                                    pats_ens1,
                                                                    iopt_ens,
                                                                    sorts_ens,
                                                                    uu___11) in
                                                                 FStar_SMTEncoding_Term.Quant
                                                                   uu___10 in
                                                               FStar_SMTEncoding_Term.mk
                                                                 uu___9
                                                                 ens.FStar_SMTEncoding_Term.rng in
                                                             let lhs2 =
                                                               FStar_SMTEncoding_Term.mk
                                                                 (FStar_SMTEncoding_Term.App
                                                                    (FStar_SMTEncoding_Term.And,
                                                                    (FStar_Compiler_List.op_At
                                                                    req
                                                                    [ens1])))
                                                                 lhs1.FStar_SMTEncoding_Term.rng in
                                                             let uu___9 =
                                                               FStar_SMTEncoding_Term.abstr
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
                                                                   FStar_SMTEncoding_Term.print_smt_term
                                                                    post1 in
                                                                 Prims.op_Hat
                                                                   "  ... "
                                                                   uu___13 in
                                                               Prims.op_Hat
                                                                 post_name
                                                                 uu___12 in
                                                             Prims.op_Hat
                                                               "Ensures clause doesn't match post name:  "
                                                               uu___11 in
                                                           Not_a_wp_implication
                                                             uu___10 in
                                                         FStar_Compiler_Effect.raise
                                                           uu___9)
                                                  | uu___6 ->
                                                      let uu___7 =
                                                        let uu___8 =
                                                          let uu___9 =
                                                            let uu___10 =
                                                              let uu___11 =
                                                                FStar_SMTEncoding_Term.print_smt_term
                                                                  ens in
                                                              Prims.op_Hat
                                                                "  ... "
                                                                uu___11 in
                                                            Prims.op_Hat
                                                              post_name
                                                              uu___10 in
                                                          Prims.op_Hat
                                                            "Ensures clause doesn't have the expected shape for post-condition "
                                                            uu___9 in
                                                        Not_a_wp_implication
                                                          uu___8 in
                                                      FStar_Compiler_Effect.raise
                                                        uu___7))
                                        | uu___5 ->
                                            let uu___6 =
                                              let uu___7 =
                                                let uu___8 =
                                                  FStar_SMTEncoding_Term.print_smt_term
                                                    lhs1 in
                                                Prims.op_Hat
                                                  "LHS not a conjunct: "
                                                  uu___8 in
                                              Not_a_wp_implication uu___7 in
                                            FStar_Compiler_Effect.raise
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
                                                   FStar_SMTEncoding_Term.abstr
                                                     names rhs2 in
                                                 (labels3, uu___7) in
                                           (match uu___5 with
                                            | (labels3, rhs2) ->
                                                let body =
                                                  FStar_SMTEncoding_Term.mkImp
                                                    (lhs2, rhs2) rng in
                                                let uu___6 =
                                                  FStar_SMTEncoding_Term.mk
                                                    (FStar_SMTEncoding_Term.Quant
                                                       (FStar_SMTEncoding_Term.Forall,
                                                         pats, iopt, (post ::
                                                         sorts), body))
                                                    q1.FStar_SMTEncoding_Term.rng in
                                                (labels3, uu___6))))
                             | uu___2 ->
                                 let uu___3 =
                                   let uu___4 =
                                     FStar_SMTEncoding_Term.print_smt_term
                                       arg in
                                   Prims.op_Hat "arg not a quant: " uu___4 in
                                 fallback uu___3)) ()
                   with | Not_a_wp_implication msg2 -> fallback msg2)
              | FStar_SMTEncoding_Term.Labeled (arg, reason, r1) ->
                  aux reason (FStar_Pervasives_Native.Some r1) post_name_opt
                    labels1 arg
              | FStar_SMTEncoding_Term.Quant
                  (FStar_SMTEncoding_Term.Forall, [],
                   FStar_Pervasives_Native.None, sorts,
                   {
                     FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App
                       (FStar_SMTEncoding_Term.Imp, lhs::rhs::[]);
                     FStar_SMTEncoding_Term.freevars = uu___1;
                     FStar_SMTEncoding_Term.rng = rng;_})
                  when is_a_named_continuation lhs ->
                  let uu___2 = FStar_Compiler_Util.prefix sorts in
                  (match uu___2 with
                   | (sorts', post) ->
                       let new_post_name =
                         let uu___3 =
                           let uu___4 = FStar_Ident.next_id () in
                           FStar_Compiler_Effect.op_Less_Bar
                             FStar_Compiler_Util.string_of_int uu___4 in
                         Prims.op_Hat "^^post_condition_" uu___3 in
                       let names =
                         let uu___3 =
                           FStar_Compiler_List.map
                             (fun s ->
                                let uu___4 =
                                  let uu___5 =
                                    let uu___6 =
                                      let uu___7 = FStar_Ident.next_id () in
                                      FStar_Compiler_Effect.op_Less_Bar
                                        FStar_Compiler_Util.string_of_int
                                        uu___7 in
                                    Prims.op_Hat "^^" uu___6 in
                                  (uu___5, s) in
                                FStar_SMTEncoding_Term.mk_fv uu___4) sorts' in
                         let uu___4 =
                           let uu___5 =
                             FStar_SMTEncoding_Term.mk_fv
                               (new_post_name, post) in
                           [uu___5] in
                         FStar_Compiler_List.op_At uu___3 uu___4 in
                       let instantiation =
                         FStar_Compiler_List.map
                           FStar_SMTEncoding_Util.mkFreeV names in
                       let uu___3 =
                         let uu___4 =
                           FStar_SMTEncoding_Term.inst instantiation lhs in
                         let uu___5 =
                           FStar_SMTEncoding_Term.inst instantiation rhs in
                         (uu___4, uu___5) in
                       (match uu___3 with
                        | (lhs1, rhs1) ->
                            let uu___4 =
                              FStar_Compiler_Util.fold_map
                                (fun labels2 ->
                                   fun tm ->
                                     match tm.FStar_SMTEncoding_Term.tm with
                                     | FStar_SMTEncoding_Term.Quant
                                         (FStar_SMTEncoding_Term.Forall,
                                          ({
                                             FStar_SMTEncoding_Term.tm =
                                               FStar_SMTEncoding_Term.App
                                               (FStar_SMTEncoding_Term.Var
                                                "Prims.guard_free", p::[]);
                                             FStar_SMTEncoding_Term.freevars
                                               = uu___5;
                                             FStar_SMTEncoding_Term.rng =
                                               uu___6;_}::[])::[],
                                          iopt, sorts1,
                                          {
                                            FStar_SMTEncoding_Term.tm =
                                              FStar_SMTEncoding_Term.App
                                              (FStar_SMTEncoding_Term.Imp,
                                               l0::r1::[]);
                                            FStar_SMTEncoding_Term.freevars =
                                              uu___7;
                                            FStar_SMTEncoding_Term.rng =
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
                                                        FStar_SMTEncoding_Util.norng
                                                          FStar_SMTEncoding_Term.mk
                                                          (FStar_SMTEncoding_Term.App
                                                             (FStar_SMTEncoding_Term.Imp,
                                                               [l; r1])) in
                                                      (FStar_SMTEncoding_Term.Forall,
                                                        [[p]],
                                                        (FStar_Pervasives_Native.Some
                                                           Prims.int_zero),
                                                        sorts1, uu___14) in
                                                    FStar_SMTEncoding_Term.Quant
                                                      uu___13 in
                                                  FStar_SMTEncoding_Term.mk
                                                    uu___12
                                                    q1.FStar_SMTEncoding_Term.rng in
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
                                              FStar_SMTEncoding_Term.mk_and_l
                                                lhs_conjs
                                                lhs1.FStar_SMTEncoding_Term.rng in
                                            (uu___8, rhs2) in
                                          FStar_SMTEncoding_Term.mkImp uu___7
                                            rng in
                                        FStar_Compiler_Effect.op_Bar_Greater
                                          uu___6
                                          (FStar_SMTEncoding_Term.abstr names) in
                                      let q2 =
                                        FStar_SMTEncoding_Term.mk
                                          (FStar_SMTEncoding_Term.Quant
                                             (FStar_SMTEncoding_Term.Forall,
                                               [],
                                               FStar_Pervasives_Native.None,
                                               sorts, body))
                                          q1.FStar_SMTEncoding_Term.rng in
                                      (labels3, q2)))))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Imp, lhs::rhs::[]) ->
                  let uu___1 = aux default_msg ropt post_name_opt labels1 rhs in
                  (match uu___1 with
                   | (labels2, rhs1) ->
                       let uu___2 = FStar_SMTEncoding_Util.mkImp (lhs, rhs1) in
                       (labels2, uu___2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.And, conjuncts1) ->
                  let uu___1 =
                    FStar_Compiler_Util.fold_map
                      (aux default_msg ropt post_name_opt) labels1 conjuncts1 in
                  (match uu___1 with
                   | (labels2, conjuncts2) ->
                       let uu___2 =
                         FStar_SMTEncoding_Term.mk_and_l conjuncts2
                           q1.FStar_SMTEncoding_Term.rng in
                       (labels2, uu___2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.ITE, hd::q11::q2::[]) ->
                  let uu___1 = aux default_msg ropt post_name_opt labels1 q11 in
                  (match uu___1 with
                   | (labels2, q12) ->
                       let uu___2 =
                         aux default_msg ropt post_name_opt labels2 q2 in
                       (match uu___2 with
                        | (labels3, q21) ->
                            let uu___3 =
                              FStar_SMTEncoding_Term.mkITE (hd, q12, q21)
                                q1.FStar_SMTEncoding_Term.rng in
                            (labels3, uu___3)))
              | FStar_SMTEncoding_Term.Quant
                  (FStar_SMTEncoding_Term.Exists, uu___1, uu___2, uu___3,
                   uu___4)
                  ->
                  let uu___5 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu___5 with | (lab, q2) -> ((lab :: labels1), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Iff, uu___1) ->
                  let uu___2 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu___2 with | (lab, q2) -> ((lab :: labels1), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Or, uu___1) ->
                  let uu___2 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu___2 with | (lab, q2) -> ((lab :: labels1), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Var "Unreachable", uu___1) ->
                  (labels1, q1)
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Var uu___1, uu___2) when
                  is_a_post_condition post_name_opt q1 -> (labels1, q1)
              | FStar_SMTEncoding_Term.FreeV uu___1 ->
                  let uu___2 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu___2 with | (lab, q2) -> ((lab :: labels1), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.TrueOp, uu___1) ->
                  let uu___2 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu___2 with | (lab, q2) -> ((lab :: labels1), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.FalseOp, uu___1) ->
                  let uu___2 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu___2 with | (lab, q2) -> ((lab :: labels1), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Not, uu___1) ->
                  let uu___2 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu___2 with | (lab, q2) -> ((lab :: labels1), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Eq, uu___1) ->
                  let uu___2 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu___2 with | (lab, q2) -> ((lab :: labels1), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.LT, uu___1) ->
                  let uu___2 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu___2 with | (lab, q2) -> ((lab :: labels1), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.LTE, uu___1) ->
                  let uu___2 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu___2 with | (lab, q2) -> ((lab :: labels1), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.GT, uu___1) ->
                  let uu___2 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu___2 with | (lab, q2) -> ((lab :: labels1), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.GTE, uu___1) ->
                  let uu___2 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu___2 with | (lab, q2) -> ((lab :: labels1), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvUlt, uu___1) ->
                  let uu___2 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu___2 with | (lab, q2) -> ((lab :: labels1), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Var uu___1, uu___2) ->
                  let uu___3 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu___3 with | (lab, q2) -> ((lab :: labels1), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.RealDiv, uu___1) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Add, uu___1) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Sub, uu___1) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Div, uu___1) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Mul, uu___1) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Minus, uu___1) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Mod, uu___1) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvAnd, uu___1) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvXor, uu___1) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvOr, uu___1) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvAdd, uu___1) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvSub, uu___1) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvShl, uu___1) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvShr, uu___1) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvUdiv, uu___1) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvMod, uu___1) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvMul, uu___1) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvUext uu___1, uu___2) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvToNat, uu___1) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.NatToBv uu___1, uu___2) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.ITE, uu___1) ->
                  failwith "Impossible: arity mismatch"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Imp, uu___1) ->
                  failwith "Impossible: arity mismatch"
              | FStar_SMTEncoding_Term.Quant
                  (FStar_SMTEncoding_Term.Forall, pats, iopt, sorts, body) ->
                  let uu___1 =
                    aux default_msg ropt post_name_opt labels1 body in
                  (match uu___1 with
                   | (labels2, body1) ->
                       let uu___2 =
                         FStar_SMTEncoding_Term.mk
                           (FStar_SMTEncoding_Term.Quant
                              (FStar_SMTEncoding_Term.Forall, pats, iopt,
                                sorts, body1)) q1.FStar_SMTEncoding_Term.rng in
                       (labels2, uu___2))
              | FStar_SMTEncoding_Term.Let (es, body) ->
                  let uu___1 =
                    aux default_msg ropt post_name_opt labels1 body in
                  (match uu___1 with
                   | (labels2, body1) ->
                       let uu___2 =
                         FStar_SMTEncoding_Term.mkLet (es, body1)
                           q1.FStar_SMTEncoding_Term.rng in
                       (labels2, uu___2)) in
            aux "assertion failed" FStar_Pervasives_Native.None
              FStar_Pervasives_Native.None [] q
let (detail_errors :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      labels ->
        (FStar_SMTEncoding_Term.decl Prims.list ->
           FStar_SMTEncoding_Z3.z3result)
          -> unit)
  =
  fun hint_replay ->
    fun env ->
      fun all_labels ->
        fun askZ3 ->
          let print_banner uu___ =
            let msg1 =
              let uu___1 =
                let uu___2 = FStar_TypeChecker_Env.get_range env in
                FStar_Compiler_Range.string_of_range uu___2 in
              let uu___2 =
                FStar_Compiler_Util.string_of_int (Prims.of_int (5)) in
              let uu___3 =
                FStar_Compiler_Util.string_of_int
                  (FStar_Compiler_List.length all_labels) in
              FStar_Compiler_Util.format4
                "Detailed %s report follows for %s\nTaking %s seconds per proof obligation (%s proofs in total)\n"
                (if hint_replay then "hint replay" else "error") uu___1
                uu___2 uu___3 in
            FStar_Compiler_Util.print_error msg1 in
          let print_result uu___ =
            match uu___ with
            | ((uu___1, msg1, r), success) ->
                if success
                then
                  let uu___2 = FStar_Compiler_Range.string_of_range r in
                  FStar_Compiler_Util.print1
                    "OK: proof obligation at %s was proven in isolation\n"
                    uu___2
                else
                  if hint_replay
                  then
                    FStar_Errors.log_issue r
                      (FStar_Errors.Warning_HintFailedToReplayProof,
                        (Prims.op_Hat
                           "Hint failed to replay this sub-proof: " msg1))
                  else
                    (let uu___4 =
                       let uu___5 =
                         let uu___6 = FStar_Compiler_Range.string_of_range r in
                         FStar_Compiler_Util.format2
                           "XX: proof obligation at %s failed\n\t%s\n" uu___6
                           msg1 in
                       (FStar_Errors.Error_ProofObligationFailed, uu___5) in
                     FStar_Errors.log_issue r uu___4) in
          let elim labs =
            FStar_Compiler_Effect.op_Bar_Greater labs
              (FStar_Compiler_List.map
                 (fun uu___ ->
                    match uu___ with
                    | (l, uu___1, uu___2) ->
                        let a =
                          let uu___3 =
                            let uu___4 =
                              let uu___5 = FStar_SMTEncoding_Util.mkFreeV l in
                              (uu___5, FStar_SMTEncoding_Util.mkTrue) in
                            FStar_SMTEncoding_Util.mkEq uu___4 in
                          let uu___4 =
                            let uu___5 = FStar_SMTEncoding_Term.fv_name l in
                            Prims.op_Hat "@disable_label_" uu___5 in
                          {
                            FStar_SMTEncoding_Term.assumption_term = uu___3;
                            FStar_SMTEncoding_Term.assumption_caption =
                              (FStar_Pervasives_Native.Some "Disabling label");
                            FStar_SMTEncoding_Term.assumption_name = uu___4;
                            FStar_SMTEncoding_Term.assumption_fact_ids = []
                          } in
                        FStar_SMTEncoding_Term.Assume a)) in
          let rec linear_check eliminated errors active =
            FStar_SMTEncoding_Z3.refresh ();
            (match active with
             | [] ->
                 let results =
                   let uu___1 =
                     FStar_Compiler_List.map (fun x -> (x, true)) eliminated in
                   let uu___2 =
                     FStar_Compiler_List.map (fun x -> (x, false)) errors in
                   FStar_Compiler_List.op_At uu___1 uu___2 in
                 sort_labels results
             | hd::tl ->
                 ((let uu___2 =
                     FStar_Compiler_Util.string_of_int
                       (FStar_Compiler_List.length active) in
                   FStar_Compiler_Util.print1 "%s, " uu___2);
                  (let decls =
                     FStar_Compiler_Effect.op_Less_Bar elim
                       (FStar_Compiler_List.op_At eliminated
                          (FStar_Compiler_List.op_At errors tl)) in
                   let result = askZ3 decls in
                   match result.FStar_SMTEncoding_Z3.z3result_status with
                   | FStar_SMTEncoding_Z3.UNSAT uu___2 ->
                       linear_check (hd :: eliminated) errors tl
                   | uu___2 -> linear_check eliminated (hd :: errors) tl))) in
          print_banner ();
          FStar_Options.set_option "z3rlimit"
            (FStar_Options.Int (Prims.of_int (5)));
          (let res = linear_check [] [] all_labels in
           FStar_Compiler_Util.print_string "\n";
           FStar_Compiler_Effect.op_Bar_Greater res
             (FStar_Compiler_List.iter print_result);
           (let uu___4 =
              FStar_Compiler_Util.for_all FStar_Pervasives_Native.snd res in
            if uu___4
            then
              FStar_Compiler_Util.print_string
                "Failed: the heuristic of trying each proof in isolation failed to identify a precise error\n"
            else ()))