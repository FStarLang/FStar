open Prims
exception Not_a_wp_implication of Prims.string 
let (uu___is_Not_a_wp_implication : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Not_a_wp_implication uu____9 -> true
    | uu____10 -> false
let (__proj__Not_a_wp_implication__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee ->
    match projectee with | Not_a_wp_implication uu____16 -> uu____16
type label = FStar_SMTEncoding_Term.error_label
type labels = FStar_SMTEncoding_Term.error_labels
let (sort_labels :
  (FStar_SMTEncoding_Term.error_label * Prims.bool) Prims.list ->
    ((FStar_SMTEncoding_Term.fv * Prims.string * FStar_Range.range) *
      Prims.bool) Prims.list)
  =
  fun l ->
    FStar_List.sortWith
      (fun uu____66 ->
         fun uu____67 ->
           match (uu____66, uu____67) with
           | (((uu____108, uu____109, r1), uu____111),
              ((uu____112, uu____113, r2), uu____115)) ->
               FStar_Range.compare r1 r2) l
let (remove_dups :
  labels ->
    (FStar_SMTEncoding_Term.fv * Prims.string * FStar_Range.range) Prims.list)
  =
  fun l ->
    FStar_Util.remove_dups
      (fun uu____175 ->
         fun uu____176 ->
           match (uu____175, uu____176) with
           | ((uu____201, m1, r1), (uu____204, m2, r2)) ->
               (r1 = r2) && (m1 = m2)) l
type msg = (Prims.string * FStar_Range.range)
type ranges =
  (Prims.string FStar_Pervasives_Native.option * FStar_Range.range)
    Prims.list
let (fresh_label :
  Prims.string ->
    FStar_Range.range ->
      FStar_SMTEncoding_Term.term -> (label * FStar_SMTEncoding_Term.term))
  =
  let ctr = FStar_Util.mk_ref Prims.int_zero in
  fun message ->
    fun range ->
      fun t ->
        let l =
          FStar_Util.incr ctr;
          (let uu____255 =
             let uu____256 = FStar_ST.op_Bang ctr in
             FStar_Util.string_of_int uu____256 in
           FStar_Util.format1 "label_%s" uu____255) in
        let lvar =
          FStar_SMTEncoding_Term.mk_fv (l, FStar_SMTEncoding_Term.Bool_sort) in
        let label1 = (lvar, message, range) in
        let lterm = FStar_SMTEncoding_Util.mkFreeV lvar in
        let lt = FStar_SMTEncoding_Term.mkOr (lterm, t) range in (label1, lt)
let (label_goals :
  (unit -> Prims.string) FStar_Pervasives_Native.option ->
    FStar_Range.range ->
      FStar_SMTEncoding_Term.term -> (labels * FStar_SMTEncoding_Term.term))
  =
  fun use_env_msg ->
    fun r ->
      fun q ->
        let rec is_a_post_condition post_name_opt tm =
          match (post_name_opt, (tm.FStar_SMTEncoding_Term.tm)) with
          | (FStar_Pervasives_Native.None, uu____322) -> false
          | (FStar_Pervasives_Native.Some nm, FStar_SMTEncoding_Term.FreeV
             fv) ->
              let uu____335 = FStar_SMTEncoding_Term.fv_name fv in
              nm = uu____335
          | (uu____336, FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var "Valid", tm1::[])) ->
              is_a_post_condition post_name_opt tm1
          | (uu____344, FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var "ApplyTT", tm1::uu____346)) ->
              is_a_post_condition post_name_opt tm1
          | uu____355 -> false in
        let conjuncts t =
          match t.FStar_SMTEncoding_Term.tm with
          | FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And, cs) -> cs
          | uu____377 -> [t] in
        let is_guard_free tm =
          match tm.FStar_SMTEncoding_Term.tm with
          | FStar_SMTEncoding_Term.Quant
              (FStar_SMTEncoding_Term.Forall,
               ({
                  FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App
                    (FStar_SMTEncoding_Term.Var "Prims.guard_free", p::[]);
                  FStar_SMTEncoding_Term.freevars = uu____385;
                  FStar_SMTEncoding_Term.rng = uu____386;_}::[])::[],
               iopt, uu____388,
               {
                 FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App
                   (FStar_SMTEncoding_Term.Imp, l::r1::[]);
                 FStar_SMTEncoding_Term.freevars = uu____391;
                 FStar_SMTEncoding_Term.rng = uu____392;_})
              -> true
          | uu____433 -> false in
        let is_a_named_continuation lhs =
          FStar_All.pipe_right (conjuncts lhs)
            (FStar_Util.for_some is_guard_free) in
        let uu____442 =
          match use_env_msg with
          | FStar_Pervasives_Native.None -> (false, "")
          | FStar_Pervasives_Native.Some f ->
              let uu____461 = f () in (true, uu____461) in
        match uu____442 with
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
                    let uu____501 =
                      let uu____502 = FStar_Range.use_range rng in
                      let uu____503 = FStar_Range.use_range r1 in
                      FStar_Range.rng_included uu____502 uu____503 in
                    if uu____501
                    then rng
                    else
                      (let uu____505 = FStar_Range.def_range rng in
                       FStar_Range.set_def_range r1 uu____505) in
              fresh_label msg2 rng1 t in
            let rec aux default_msg ropt post_name_opt labels1 q1 =
              match q1.FStar_SMTEncoding_Term.tm with
              | FStar_SMTEncoding_Term.BoundV uu____556 -> (labels1, q1)
              | FStar_SMTEncoding_Term.Integer uu____559 -> (labels1, q1)
              | FStar_SMTEncoding_Term.String uu____562 -> (labels1, q1)
              | FStar_SMTEncoding_Term.Real uu____565 -> (labels1, q1)
              | FStar_SMTEncoding_Term.LblPos uu____568 ->
                  failwith "Impossible"
              | FStar_SMTEncoding_Term.Labeled
                  (arg, "could not prove post-condition", uu____580) ->
                  let fallback msg1 =
                    aux default_msg ropt post_name_opt labels1 arg in
                  (try
                     (fun uu___144_622 ->
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
                                    FStar_SMTEncoding_Term.freevars =
                                      uu____641;
                                    FStar_SMTEncoding_Term.rng = rng;_})
                                 ->
                                 let post_name =
                                   let uu____672 =
                                     let uu____673 = FStar_Ident.next_id () in
                                     FStar_All.pipe_left
                                       FStar_Util.string_of_int uu____673 in
                                   Prims.op_Hat "^^post_condition_" uu____672 in
                                 let names =
                                   let uu____677 =
                                     FStar_SMTEncoding_Term.mk_fv
                                       (post_name, post) in
                                   let uu____678 =
                                     FStar_List.map
                                       (fun s ->
                                          let uu____684 =
                                            let uu____689 =
                                              let uu____690 =
                                                let uu____691 =
                                                  FStar_Ident.next_id () in
                                                FStar_All.pipe_left
                                                  FStar_Util.string_of_int
                                                  uu____691 in
                                              Prims.op_Hat "^^" uu____690 in
                                            (uu____689, s) in
                                          FStar_SMTEncoding_Term.mk_fv
                                            uu____684) sorts in
                                   uu____677 :: uu____678 in
                                 let instantiation =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV names in
                                 let uu____695 =
                                   let uu____700 =
                                     FStar_SMTEncoding_Term.inst
                                       instantiation lhs in
                                   let uu____701 =
                                     FStar_SMTEncoding_Term.inst
                                       instantiation rhs in
                                   (uu____700, uu____701) in
                                 (match uu____695 with
                                  | (lhs1, rhs1) ->
                                      let uu____710 =
                                        match lhs1.FStar_SMTEncoding_Term.tm
                                        with
                                        | FStar_SMTEncoding_Term.App
                                            (FStar_SMTEncoding_Term.And,
                                             clauses_lhs)
                                            ->
                                            let uu____728 =
                                              FStar_Util.prefix clauses_lhs in
                                            (match uu____728 with
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
                                                           = uu____758;
                                                         FStar_SMTEncoding_Term.rng
                                                           = rng_ens;_})
                                                      ->
                                                      let uu____788 =
                                                        is_a_post_condition
                                                          (FStar_Pervasives_Native.Some
                                                             post_name) post1 in
                                                      if uu____788
                                                      then
                                                        let uu____795 =
                                                          aux
                                                            "could not prove post-condition"
                                                            FStar_Pervasives_Native.None
                                                            (FStar_Pervasives_Native.Some
                                                               post_name)
                                                            labels1
                                                            ensures_conjuncts in
                                                        (match uu____795 with
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
                                                               | uu____837 ->
                                                                   pats_ens in
                                                             let ens1 =
                                                               let uu____843
                                                                 =
                                                                 let uu____844
                                                                   =
                                                                   let uu____863
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
                                                                    uu____863) in
                                                                 FStar_SMTEncoding_Term.Quant
                                                                   uu____844 in
                                                               FStar_SMTEncoding_Term.mk
                                                                 uu____843
                                                                 ens.FStar_SMTEncoding_Term.rng in
                                                             let lhs2 =
                                                               FStar_SMTEncoding_Term.mk
                                                                 (FStar_SMTEncoding_Term.App
                                                                    (FStar_SMTEncoding_Term.And,
                                                                    (FStar_List.append
                                                                    req
                                                                    [ens1])))
                                                                 lhs1.FStar_SMTEncoding_Term.rng in
                                                             let uu____877 =
                                                               FStar_SMTEncoding_Term.abstr
                                                                 names lhs2 in
                                                             (labels2,
                                                               uu____877))
                                                      else
                                                        (let uu____881 =
                                                           let uu____882 =
                                                             let uu____883 =
                                                               let uu____884
                                                                 =
                                                                 let uu____885
                                                                   =
                                                                   FStar_SMTEncoding_Term.print_smt_term
                                                                    post1 in
                                                                 Prims.op_Hat
                                                                   "  ... "
                                                                   uu____885 in
                                                               Prims.op_Hat
                                                                 post_name
                                                                 uu____884 in
                                                             Prims.op_Hat
                                                               "Ensures clause doesn't match post name:  "
                                                               uu____883 in
                                                           Not_a_wp_implication
                                                             uu____882 in
                                                         FStar_Exn.raise
                                                           uu____881)
                                                  | uu____892 ->
                                                      let uu____893 =
                                                        let uu____894 =
                                                          let uu____895 =
                                                            let uu____896 =
                                                              let uu____897 =
                                                                FStar_SMTEncoding_Term.print_smt_term
                                                                  ens in
                                                              Prims.op_Hat
                                                                "  ... "
                                                                uu____897 in
                                                            Prims.op_Hat
                                                              post_name
                                                              uu____896 in
                                                          Prims.op_Hat
                                                            "Ensures clause doesn't have the expected shape for post-condition "
                                                            uu____895 in
                                                        Not_a_wp_implication
                                                          uu____894 in
                                                      FStar_Exn.raise
                                                        uu____893))
                                        | uu____904 ->
                                            let uu____905 =
                                              let uu____906 =
                                                let uu____907 =
                                                  FStar_SMTEncoding_Term.print_smt_term
                                                    lhs1 in
                                                Prims.op_Hat
                                                  "LHS not a conjunct: "
                                                  uu____907 in
                                              Not_a_wp_implication uu____906 in
                                            FStar_Exn.raise uu____905 in
                                      (match uu____710 with
                                       | (labels2, lhs2) ->
                                           let uu____926 =
                                             let uu____933 =
                                               aux default_msg
                                                 FStar_Pervasives_Native.None
                                                 (FStar_Pervasives_Native.Some
                                                    post_name) labels2 rhs1 in
                                             match uu____933 with
                                             | (labels3, rhs2) ->
                                                 let uu____952 =
                                                   FStar_SMTEncoding_Term.abstr
                                                     names rhs2 in
                                                 (labels3, uu____952) in
                                           (match uu____926 with
                                            | (labels3, rhs2) ->
                                                let body =
                                                  FStar_SMTEncoding_Term.mkImp
                                                    (lhs2, rhs2) rng in
                                                let uu____968 =
                                                  FStar_SMTEncoding_Term.mk
                                                    (FStar_SMTEncoding_Term.Quant
                                                       (FStar_SMTEncoding_Term.Forall,
                                                         pats, iopt, (post ::
                                                         sorts), body))
                                                    q1.FStar_SMTEncoding_Term.rng in
                                                (labels3, uu____968))))
                             | uu____979 ->
                                 let uu____980 =
                                   let uu____981 =
                                     FStar_SMTEncoding_Term.print_smt_term
                                       arg in
                                   Prims.op_Hat "arg not a quant: " uu____981 in
                                 fallback uu____980)) ()
                   with | Not_a_wp_implication msg1 -> fallback msg1)
              | FStar_SMTEncoding_Term.Labeled (arg, reason, r1) ->
                  aux reason (FStar_Pervasives_Native.Some r1) post_name_opt
                    labels1 arg
              | FStar_SMTEncoding_Term.Quant
                  (FStar_SMTEncoding_Term.Forall, [],
                   FStar_Pervasives_Native.None, sorts,
                   {
                     FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App
                       (FStar_SMTEncoding_Term.Imp, lhs::rhs::[]);
                     FStar_SMTEncoding_Term.freevars = uu____998;
                     FStar_SMTEncoding_Term.rng = rng;_})
                  when is_a_named_continuation lhs ->
                  let uu____1024 = FStar_Util.prefix sorts in
                  (match uu____1024 with
                   | (sorts', post) ->
                       let new_post_name =
                         let uu____1044 =
                           let uu____1045 = FStar_Ident.next_id () in
                           FStar_All.pipe_left FStar_Util.string_of_int
                             uu____1045 in
                         Prims.op_Hat "^^post_condition_" uu____1044 in
                       let names =
                         let uu____1049 =
                           FStar_List.map
                             (fun s ->
                                let uu____1055 =
                                  let uu____1060 =
                                    let uu____1061 =
                                      let uu____1062 = FStar_Ident.next_id () in
                                      FStar_All.pipe_left
                                        FStar_Util.string_of_int uu____1062 in
                                    Prims.op_Hat "^^" uu____1061 in
                                  (uu____1060, s) in
                                FStar_SMTEncoding_Term.mk_fv uu____1055)
                             sorts' in
                         let uu____1063 =
                           let uu____1066 =
                             FStar_SMTEncoding_Term.mk_fv
                               (new_post_name, post) in
                           [uu____1066] in
                         FStar_List.append uu____1049 uu____1063 in
                       let instantiation =
                         FStar_List.map FStar_SMTEncoding_Util.mkFreeV names in
                       let uu____1070 =
                         let uu____1075 =
                           FStar_SMTEncoding_Term.inst instantiation lhs in
                         let uu____1076 =
                           FStar_SMTEncoding_Term.inst instantiation rhs in
                         (uu____1075, uu____1076) in
                       (match uu____1070 with
                        | (lhs1, rhs1) ->
                            let uu____1085 =
                              FStar_Util.fold_map
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
                                               = uu____1123;
                                             FStar_SMTEncoding_Term.rng =
                                               uu____1124;_}::[])::[],
                                          iopt, sorts1,
                                          {
                                            FStar_SMTEncoding_Term.tm =
                                              FStar_SMTEncoding_Term.App
                                              (FStar_SMTEncoding_Term.Imp,
                                               l0::r1::[]);
                                            FStar_SMTEncoding_Term.freevars =
                                              uu____1129;
                                            FStar_SMTEncoding_Term.rng =
                                              uu____1130;_})
                                         ->
                                         let uu____1171 =
                                           is_a_post_condition
                                             (FStar_Pervasives_Native.Some
                                                new_post_name) r1 in
                                         if uu____1171
                                         then
                                           let uu____1178 =
                                             aux default_msg
                                               FStar_Pervasives_Native.None
                                               post_name_opt labels2 l0 in
                                           (match uu____1178 with
                                            | (labels3, l) ->
                                                let uu____1197 =
                                                  let uu____1198 =
                                                    let uu____1199 =
                                                      let uu____1218 =
                                                        FStar_SMTEncoding_Util.norng
                                                          FStar_SMTEncoding_Term.mk
                                                          (FStar_SMTEncoding_Term.App
                                                             (FStar_SMTEncoding_Term.Imp,
                                                               [l; r1])) in
                                                      (FStar_SMTEncoding_Term.Forall,
                                                        [[p]],
                                                        (FStar_Pervasives_Native.Some
                                                           Prims.int_zero),
                                                        sorts1, uu____1218) in
                                                    FStar_SMTEncoding_Term.Quant
                                                      uu____1199 in
                                                  FStar_SMTEncoding_Term.mk
                                                    uu____1198
                                                    q1.FStar_SMTEncoding_Term.rng in
                                                (labels3, uu____1197))
                                         else (labels2, tm)
                                     | uu____1238 -> (labels2, tm)) labels1
                                (conjuncts lhs1) in
                            (match uu____1085 with
                             | (labels2, lhs_conjs) ->
                                 let uu____1257 =
                                   aux default_msg
                                     FStar_Pervasives_Native.None
                                     (FStar_Pervasives_Native.Some
                                        new_post_name) labels2 rhs1 in
                                 (match uu____1257 with
                                  | (labels3, rhs2) ->
                                      let body =
                                        let uu____1277 =
                                          let uu____1278 =
                                            let uu____1283 =
                                              FStar_SMTEncoding_Term.mk_and_l
                                                lhs_conjs
                                                lhs1.FStar_SMTEncoding_Term.rng in
                                            (uu____1283, rhs2) in
                                          FStar_SMTEncoding_Term.mkImp
                                            uu____1278 rng in
                                        FStar_All.pipe_right uu____1277
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
                  let uu____1301 =
                    aux default_msg ropt post_name_opt labels1 rhs in
                  (match uu____1301 with
                   | (labels2, rhs1) ->
                       let uu____1320 =
                         FStar_SMTEncoding_Util.mkImp (lhs, rhs1) in
                       (labels2, uu____1320))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.And, conjuncts1) ->
                  let uu____1328 =
                    FStar_Util.fold_map (aux default_msg ropt post_name_opt)
                      labels1 conjuncts1 in
                  (match uu____1328 with
                   | (labels2, conjuncts2) ->
                       let uu____1355 =
                         FStar_SMTEncoding_Term.mk_and_l conjuncts2
                           q1.FStar_SMTEncoding_Term.rng in
                       (labels2, uu____1355))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.ITE, hd::q11::q2::[]) ->
                  let uu____1363 =
                    aux default_msg ropt post_name_opt labels1 q11 in
                  (match uu____1363 with
                   | (labels2, q12) ->
                       let uu____1382 =
                         aux default_msg ropt post_name_opt labels2 q2 in
                       (match uu____1382 with
                        | (labels3, q21) ->
                            let uu____1401 =
                              FStar_SMTEncoding_Term.mkITE (hd, q12, q21)
                                q1.FStar_SMTEncoding_Term.rng in
                            (labels3, uu____1401)))
              | FStar_SMTEncoding_Term.Quant
                  (FStar_SMTEncoding_Term.Exists, uu____1404, uu____1405,
                   uu____1406, uu____1407)
                  ->
                  let uu____1424 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____1424 with
                   | (lab, q2) -> ((lab :: labels1), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Iff, uu____1439) ->
                  let uu____1444 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____1444 with
                   | (lab, q2) -> ((lab :: labels1), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Or, uu____1459) ->
                  let uu____1464 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____1464 with
                   | (lab, q2) -> ((lab :: labels1), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Var uu____1479, uu____1480) when
                  is_a_post_condition post_name_opt q1 -> (labels1, q1)
              | FStar_SMTEncoding_Term.FreeV uu____1487 ->
                  let uu____1494 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____1494 with
                   | (lab, q2) -> ((lab :: labels1), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.TrueOp, uu____1509) ->
                  let uu____1514 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____1514 with
                   | (lab, q2) -> ((lab :: labels1), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.FalseOp, uu____1529) ->
                  let uu____1534 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____1534 with
                   | (lab, q2) -> ((lab :: labels1), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Not, uu____1549) ->
                  let uu____1554 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____1554 with
                   | (lab, q2) -> ((lab :: labels1), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Eq, uu____1569) ->
                  let uu____1574 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____1574 with
                   | (lab, q2) -> ((lab :: labels1), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.LT, uu____1589) ->
                  let uu____1594 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____1594 with
                   | (lab, q2) -> ((lab :: labels1), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.LTE, uu____1609) ->
                  let uu____1614 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____1614 with
                   | (lab, q2) -> ((lab :: labels1), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.GT, uu____1629) ->
                  let uu____1634 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____1634 with
                   | (lab, q2) -> ((lab :: labels1), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.GTE, uu____1649) ->
                  let uu____1654 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____1654 with
                   | (lab, q2) -> ((lab :: labels1), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvUlt, uu____1669) ->
                  let uu____1674 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____1674 with
                   | (lab, q2) -> ((lab :: labels1), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Var uu____1689, uu____1690) ->
                  let uu____1695 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____1695 with
                   | (lab, q2) -> ((lab :: labels1), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.RealDiv, uu____1710) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Add, uu____1721) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Sub, uu____1732) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Div, uu____1743) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Mul, uu____1754) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Minus, uu____1765) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Mod, uu____1776) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvAnd, uu____1787) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvXor, uu____1798) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvOr, uu____1809) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvAdd, uu____1820) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvSub, uu____1831) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvShl, uu____1842) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvShr, uu____1853) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvUdiv, uu____1864) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvMod, uu____1875) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvMul, uu____1886) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvUext uu____1897, uu____1898) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvToNat, uu____1909) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.NatToBv uu____1920, uu____1921) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.ITE, uu____1932) ->
                  failwith "Impossible: arity mismatch"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Imp, uu____1943) ->
                  failwith "Impossible: arity mismatch"
              | FStar_SMTEncoding_Term.Quant
                  (FStar_SMTEncoding_Term.Forall, pats, iopt, sorts, body) ->
                  let uu____1974 =
                    aux default_msg ropt post_name_opt labels1 body in
                  (match uu____1974 with
                   | (labels2, body1) ->
                       let uu____1993 =
                         FStar_SMTEncoding_Term.mk
                           (FStar_SMTEncoding_Term.Quant
                              (FStar_SMTEncoding_Term.Forall, pats, iopt,
                                sorts, body1)) q1.FStar_SMTEncoding_Term.rng in
                       (labels2, uu____1993))
              | FStar_SMTEncoding_Term.Let (es, body) ->
                  let uu____2010 =
                    aux default_msg ropt post_name_opt labels1 body in
                  (match uu____2010 with
                   | (labels2, body1) ->
                       let uu____2029 =
                         FStar_SMTEncoding_Term.mkLet (es, body1)
                           q1.FStar_SMTEncoding_Term.rng in
                       (labels2, uu____2029)) in
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
          let print_banner uu____2068 =
            let msg1 =
              let uu____2070 =
                let uu____2071 = FStar_TypeChecker_Env.get_range env in
                FStar_Range.string_of_range uu____2071 in
              let uu____2072 = FStar_Util.string_of_int (Prims.of_int (5)) in
              let uu____2073 =
                FStar_Util.string_of_int (FStar_List.length all_labels) in
              FStar_Util.format4
                "Detailed %s report follows for %s\nTaking %s seconds per proof obligation (%s proofs in total)\n"
                (if hint_replay then "hint replay" else "error") uu____2070
                uu____2072 uu____2073 in
            FStar_Util.print_error msg1 in
          let print_result uu____2090 =
            match uu____2090 with
            | ((uu____2101, msg1, r), success) ->
                if success
                then
                  let uu____2111 = FStar_Range.string_of_range r in
                  FStar_Util.print1
                    "OK: proof obligation at %s was proven in isolation\n"
                    uu____2111
                else
                  if hint_replay
                  then
                    FStar_Errors.log_issue r
                      (FStar_Errors.Warning_HintFailedToReplayProof,
                        (Prims.op_Hat
                           "Hint failed to replay this sub-proof: " msg1))
                  else
                    (let uu____2114 =
                       let uu____2119 =
                         let uu____2120 = FStar_Range.string_of_range r in
                         FStar_Util.format2
                           "XX: proof obligation at %s failed\n\t%s\n"
                           uu____2120 msg1 in
                       (FStar_Errors.Error_ProofObligationFailed, uu____2119) in
                     FStar_Errors.log_issue r uu____2114) in
          let elim labs =
            FStar_All.pipe_right labs
              (FStar_List.map
                 (fun uu____2166 ->
                    match uu____2166 with
                    | (l, uu____2174, uu____2175) ->
                        let a =
                          let uu____2177 =
                            let uu____2178 =
                              let uu____2183 =
                                FStar_SMTEncoding_Util.mkFreeV l in
                              (uu____2183, FStar_SMTEncoding_Util.mkTrue) in
                            FStar_SMTEncoding_Util.mkEq uu____2178 in
                          let uu____2184 =
                            let uu____2185 = FStar_SMTEncoding_Term.fv_name l in
                            Prims.op_Hat "@disable_label_" uu____2185 in
                          {
                            FStar_SMTEncoding_Term.assumption_term =
                              uu____2177;
                            FStar_SMTEncoding_Term.assumption_caption =
                              (FStar_Pervasives_Native.Some "Disabling label");
                            FStar_SMTEncoding_Term.assumption_name =
                              uu____2184;
                            FStar_SMTEncoding_Term.assumption_fact_ids = []
                          } in
                        FStar_SMTEncoding_Term.Assume a)) in
          let rec linear_check eliminated errors active =
            FStar_SMTEncoding_Z3.refresh ();
            (match active with
             | [] ->
                 let results =
                   let uu____2246 =
                     FStar_List.map (fun x -> (x, true)) eliminated in
                   let uu____2259 =
                     FStar_List.map (fun x -> (x, false)) errors in
                   FStar_List.append uu____2246 uu____2259 in
                 sort_labels results
             | hd::tl ->
                 ((let uu____2281 =
                     FStar_Util.string_of_int (FStar_List.length active) in
                   FStar_Util.print1 "%s, " uu____2281);
                  (let decls =
                     FStar_All.pipe_left elim
                       (FStar_List.append eliminated
                          (FStar_List.append errors tl)) in
                   let result = askZ3 decls in
                   match result.FStar_SMTEncoding_Z3.z3result_status with
                   | FStar_SMTEncoding_Z3.UNSAT uu____2308 ->
                       linear_check (hd :: eliminated) errors tl
                   | uu____2309 -> linear_check eliminated (hd :: errors) tl))) in
          print_banner ();
          FStar_Options.set_option "z3rlimit"
            (FStar_Options.Int (Prims.of_int (5)));
          (let res = linear_check [] [] all_labels in
           FStar_Util.print_string "\n";
           FStar_All.pipe_right res (FStar_List.iter print_result);
           (let uu____2349 =
              FStar_Util.for_all FStar_Pervasives_Native.snd res in
            if uu____2349
            then
              FStar_Util.print_string
                "Failed: the heuristic of trying each proof in isolation failed to identify a precise error\n"
            else ()))