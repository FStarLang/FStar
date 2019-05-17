open Prims
exception Not_a_wp_implication of Prims.string 
let (uu___is_Not_a_wp_implication : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Not_a_wp_implication uu____12 -> true
    | uu____15 -> false
let (__proj__Not_a_wp_implication__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee ->
    match projectee with | Not_a_wp_implication uu____25 -> uu____25
type label = FStar_SMTEncoding_Term.error_label
type labels = FStar_SMTEncoding_Term.error_labels
let (sort_labels :
  (FStar_SMTEncoding_Term.error_label * Prims.bool) Prims.list ->
    ((FStar_SMTEncoding_Term.fv * Prims.string * FStar_Range.range) *
      Prims.bool) Prims.list)
  =
  fun l ->
    FStar_List.sortWith
      (fun uu____83 ->
         fun uu____84 ->
           match (uu____83, uu____84) with
           | (((uu____134, uu____135, r1), uu____137),
              ((uu____138, uu____139, r2), uu____141)) ->
               FStar_Range.compare r1 r2) l
let (remove_dups :
  labels ->
    (FStar_SMTEncoding_Term.fv * Prims.string * FStar_Range.range) Prims.list)
  =
  fun l ->
    FStar_Util.remove_dups
      (fun uu____218 ->
         fun uu____219 ->
           match (uu____218, uu____219) with
           | ((uu____249, m1, r1), (uu____252, m2, r2)) ->
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
  let ctr = FStar_Util.mk_ref (Prims.parse_int "0") in
  fun message ->
    fun range ->
      fun t ->
        let l =
          FStar_Util.incr ctr;
          (let uu____319 =
             let uu____321 = FStar_ST.op_Bang ctr in
             FStar_Util.string_of_int uu____321 in
           FStar_Util.format1 "label_%s" uu____319) in
        let lvar =
          FStar_SMTEncoding_Term.mk_fv (l, FStar_SMTEncoding_Term.Bool_sort) in
        let label = (lvar, message, range) in
        let lterm = FStar_SMTEncoding_Util.mkFreeV lvar in
        let lt1 = FStar_SMTEncoding_Term.mkOr (lterm, t) range in
        (label, lt1)
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
          | (FStar_Pervasives_Native.None, uu____415) -> false
          | (FStar_Pervasives_Native.Some nm, FStar_SMTEncoding_Term.FreeV
             fv) ->
              let uu____436 = FStar_SMTEncoding_Term.fv_name fv in
              nm = uu____436
          | (uu____439, FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var "Valid", tm1::[])) ->
              is_a_post_condition post_name_opt tm1
          | (uu____450, FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var "ApplyTT", tm1::uu____452)) ->
              is_a_post_condition post_name_opt tm1
          | uu____464 -> false in
        let conjuncts t =
          match t.FStar_SMTEncoding_Term.tm with
          | FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And, cs) -> cs
          | uu____488 -> [t] in
        let is_guard_free tm =
          match tm.FStar_SMTEncoding_Term.tm with
          | FStar_SMTEncoding_Term.Quant
              (FStar_SMTEncoding_Term.Forall,
               ({
                  FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App
                    (FStar_SMTEncoding_Term.Var "Prims.guard_free", p::[]);
                  FStar_SMTEncoding_Term.freevars = uu____498;
                  FStar_SMTEncoding_Term.rng = uu____499;_}::[])::[],
               iopt, uu____501,
               {
                 FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App
                   (FStar_SMTEncoding_Term.Imp, l::r1::[]);
                 FStar_SMTEncoding_Term.freevars = uu____504;
                 FStar_SMTEncoding_Term.rng = uu____505;_})
              -> true
          | uu____554 -> false in
        let is_a_named_continuation lhs =
          FStar_All.pipe_right (conjuncts lhs)
            (FStar_Util.for_some is_guard_free) in
        let uu____566 =
          match use_env_msg with
          | FStar_Pervasives_Native.None -> (false, "")
          | FStar_Pervasives_Native.Some f ->
              let uu____596 = f () in (true, uu____596) in
        match uu____566 with
        | (flag, msg_prefix) ->
            let fresh_label1 msg ropt rng t =
              let msg1 =
                if flag
                then
                  Prims.op_Hat "Failed to verify implicit argument: "
                    (Prims.op_Hat msg_prefix (Prims.op_Hat " :: " msg))
                else msg in
              let rng1 =
                match ropt with
                | FStar_Pervasives_Native.None -> rng
                | FStar_Pervasives_Native.Some r1 ->
                    let uu____652 =
                      let uu____654 = FStar_Range.use_range rng in
                      let uu____655 = FStar_Range.use_range r1 in
                      FStar_Range.rng_included uu____654 uu____655 in
                    if uu____652
                    then rng
                    else
                      (let uu____659 = FStar_Range.def_range rng in
                       FStar_Range.set_def_range r1 uu____659) in
              fresh_label msg1 rng1 t in
            let rec aux default_msg ropt post_name_opt labels q1 =
              match q1.FStar_SMTEncoding_Term.tm with
              | FStar_SMTEncoding_Term.BoundV uu____714 -> (labels, q1)
              | FStar_SMTEncoding_Term.Integer uu____718 -> (labels, q1)
              | FStar_SMTEncoding_Term.Real uu____722 -> (labels, q1)
              | FStar_SMTEncoding_Term.LblPos uu____726 ->
                  failwith "Impossible"
              | FStar_SMTEncoding_Term.Labeled
                  (arg, "could not prove post-condition", uu____740) ->
                  let fallback msg =
                    aux default_msg ropt post_name_opt labels arg in
                  (try
                     (fun uu___142_786 ->
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
                                      uu____805;
                                    FStar_SMTEncoding_Term.rng = rng;_})
                                 ->
                                 let post_name =
                                   let uu____841 =
                                     let uu____843 = FStar_Ident.next_id () in
                                     FStar_All.pipe_left
                                       FStar_Util.string_of_int uu____843 in
                                   Prims.op_Hat "^^post_condition_" uu____841 in
                                 let names1 =
                                   let uu____851 =
                                     FStar_SMTEncoding_Term.mk_fv
                                       (post_name, post) in
                                   let uu____853 =
                                     FStar_List.map
                                       (fun s ->
                                          let uu____859 =
                                            let uu____865 =
                                              let uu____867 =
                                                let uu____869 =
                                                  FStar_Ident.next_id () in
                                                FStar_All.pipe_left
                                                  FStar_Util.string_of_int
                                                  uu____869 in
                                              Prims.op_Hat "^^" uu____867 in
                                            (uu____865, s) in
                                          FStar_SMTEncoding_Term.mk_fv
                                            uu____859) sorts in
                                   uu____851 :: uu____853 in
                                 let instantiation =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV names1 in
                                 let uu____878 =
                                   let uu____883 =
                                     FStar_SMTEncoding_Term.inst
                                       instantiation lhs in
                                   let uu____884 =
                                     FStar_SMTEncoding_Term.inst
                                       instantiation rhs in
                                   (uu____883, uu____884) in
                                 (match uu____878 with
                                  | (lhs1, rhs1) ->
                                      let uu____893 =
                                        match lhs1.FStar_SMTEncoding_Term.tm
                                        with
                                        | FStar_SMTEncoding_Term.App
                                            (FStar_SMTEncoding_Term.And,
                                             clauses_lhs)
                                            ->
                                            let uu____911 =
                                              FStar_Util.prefix clauses_lhs in
                                            (match uu____911 with
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
                                                           = uu____941;
                                                         FStar_SMTEncoding_Term.rng
                                                           = rng_ens;_})
                                                      ->
                                                      let uu____975 =
                                                        is_a_post_condition
                                                          (FStar_Pervasives_Native.Some
                                                             post_name) post1 in
                                                      if uu____975
                                                      then
                                                        let uu____985 =
                                                          aux
                                                            "could not prove post-condition"
                                                            FStar_Pervasives_Native.None
                                                            (FStar_Pervasives_Native.Some
                                                               post_name)
                                                            labels
                                                            ensures_conjuncts in
                                                        (match uu____985 with
                                                         | (labels1,
                                                            ensures_conjuncts1)
                                                             ->
                                                             let pats_ens1 =
                                                               match pats_ens
                                                               with
                                                               | [] ->
                                                                   [[post1]]
                                                               | []::[] ->
                                                                   [[post1]]
                                                               | uu____1029
                                                                   ->
                                                                   pats_ens in
                                                             let ens1 =
                                                               let uu____1035
                                                                 =
                                                                 let uu____1036
                                                                   =
                                                                   let uu____1056
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
                                                                    uu____1056) in
                                                                 FStar_SMTEncoding_Term.Quant
                                                                   uu____1036 in
                                                               FStar_SMTEncoding_Term.mk
                                                                 uu____1035
                                                                 ens.FStar_SMTEncoding_Term.rng in
                                                             let lhs2 =
                                                               FStar_SMTEncoding_Term.mk
                                                                 (FStar_SMTEncoding_Term.App
                                                                    (FStar_SMTEncoding_Term.And,
                                                                    (FStar_List.append
                                                                    req
                                                                    [ens1])))
                                                                 lhs1.FStar_SMTEncoding_Term.rng in
                                                             let uu____1071 =
                                                               FStar_SMTEncoding_Term.abstr
                                                                 names1 lhs2 in
                                                             (labels1,
                                                               uu____1071))
                                                      else
                                                        (let uu____1076 =
                                                           let uu____1077 =
                                                             let uu____1079 =
                                                               let uu____1081
                                                                 =
                                                                 let uu____1083
                                                                   =
                                                                   FStar_SMTEncoding_Term.print_smt_term
                                                                    post1 in
                                                                 Prims.op_Hat
                                                                   "  ... "
                                                                   uu____1083 in
                                                               Prims.op_Hat
                                                                 post_name
                                                                 uu____1081 in
                                                             Prims.op_Hat
                                                               "Ensures clause doesn't match post name:  "
                                                               uu____1079 in
                                                           Not_a_wp_implication
                                                             uu____1077 in
                                                         FStar_Exn.raise
                                                           uu____1076)
                                                  | uu____1093 ->
                                                      let uu____1094 =
                                                        let uu____1095 =
                                                          let uu____1097 =
                                                            let uu____1099 =
                                                              let uu____1101
                                                                =
                                                                FStar_SMTEncoding_Term.print_smt_term
                                                                  ens in
                                                              Prims.op_Hat
                                                                "  ... "
                                                                uu____1101 in
                                                            Prims.op_Hat
                                                              post_name
                                                              uu____1099 in
                                                          Prims.op_Hat
                                                            "Ensures clause doesn't have the expected shape for post-condition "
                                                            uu____1097 in
                                                        Not_a_wp_implication
                                                          uu____1095 in
                                                      FStar_Exn.raise
                                                        uu____1094))
                                        | uu____1111 ->
                                            let uu____1112 =
                                              let uu____1113 =
                                                let uu____1115 =
                                                  FStar_SMTEncoding_Term.print_smt_term
                                                    lhs1 in
                                                Prims.op_Hat
                                                  "LHS not a conjunct: "
                                                  uu____1115 in
                                              Not_a_wp_implication uu____1113 in
                                            FStar_Exn.raise uu____1112 in
                                      (match uu____893 with
                                       | (labels1, lhs2) ->
                                           let uu____1136 =
                                             let uu____1143 =
                                               aux default_msg
                                                 FStar_Pervasives_Native.None
                                                 (FStar_Pervasives_Native.Some
                                                    post_name) labels1 rhs1 in
                                             match uu____1143 with
                                             | (labels2, rhs2) ->
                                                 let uu____1163 =
                                                   FStar_SMTEncoding_Term.abstr
                                                     names1 rhs2 in
                                                 (labels2, uu____1163) in
                                           (match uu____1136 with
                                            | (labels2, rhs2) ->
                                                let body =
                                                  FStar_SMTEncoding_Term.mkImp
                                                    (lhs2, rhs2) rng in
                                                let uu____1179 =
                                                  FStar_SMTEncoding_Term.mk
                                                    (FStar_SMTEncoding_Term.Quant
                                                       (FStar_SMTEncoding_Term.Forall,
                                                         pats, iopt, (post ::
                                                         sorts), body))
                                                    q1.FStar_SMTEncoding_Term.rng in
                                                (labels2, uu____1179))))
                             | uu____1191 ->
                                 let uu____1192 =
                                   let uu____1194 =
                                     FStar_SMTEncoding_Term.print_smt_term
                                       arg in
                                   Prims.op_Hat "arg not a quant: "
                                     uu____1194 in
                                 fallback uu____1192)) ()
                   with | Not_a_wp_implication msg -> fallback msg)
              | FStar_SMTEncoding_Term.Labeled (arg, reason, r1) ->
                  aux reason (FStar_Pervasives_Native.Some r1) post_name_opt
                    labels arg
              | FStar_SMTEncoding_Term.Quant
                  (FStar_SMTEncoding_Term.Forall, [],
                   FStar_Pervasives_Native.None, sorts,
                   {
                     FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App
                       (FStar_SMTEncoding_Term.Imp, lhs::rhs::[]);
                     FStar_SMTEncoding_Term.freevars = uu____1216;
                     FStar_SMTEncoding_Term.rng = rng;_})
                  when is_a_named_continuation lhs ->
                  let uu____1246 = FStar_Util.prefix sorts in
                  (match uu____1246 with
                   | (sorts', post) ->
                       let new_post_name =
                         let uu____1267 =
                           let uu____1269 = FStar_Ident.next_id () in
                           FStar_All.pipe_left FStar_Util.string_of_int
                             uu____1269 in
                         Prims.op_Hat "^^post_condition_" uu____1267 in
                       let names1 =
                         let uu____1277 =
                           FStar_List.map
                             (fun s ->
                                let uu____1283 =
                                  let uu____1289 =
                                    let uu____1291 =
                                      let uu____1293 = FStar_Ident.next_id () in
                                      FStar_All.pipe_left
                                        FStar_Util.string_of_int uu____1293 in
                                    Prims.op_Hat "^^" uu____1291 in
                                  (uu____1289, s) in
                                FStar_SMTEncoding_Term.mk_fv uu____1283)
                             sorts' in
                         let uu____1299 =
                           let uu____1302 =
                             FStar_SMTEncoding_Term.mk_fv
                               (new_post_name, post) in
                           [uu____1302] in
                         FStar_List.append uu____1277 uu____1299 in
                       let instantiation =
                         FStar_List.map FStar_SMTEncoding_Util.mkFreeV names1 in
                       let uu____1307 =
                         let uu____1312 =
                           FStar_SMTEncoding_Term.inst instantiation lhs in
                         let uu____1313 =
                           FStar_SMTEncoding_Term.inst instantiation rhs in
                         (uu____1312, uu____1313) in
                       (match uu____1307 with
                        | (lhs1, rhs1) ->
                            let uu____1322 =
                              FStar_Util.fold_map
                                (fun labels1 ->
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
                                               = uu____1360;
                                             FStar_SMTEncoding_Term.rng =
                                               uu____1361;_}::[])::[],
                                          iopt, sorts1,
                                          {
                                            FStar_SMTEncoding_Term.tm =
                                              FStar_SMTEncoding_Term.App
                                              (FStar_SMTEncoding_Term.Imp,
                                               l0::r1::[]);
                                            FStar_SMTEncoding_Term.freevars =
                                              uu____1366;
                                            FStar_SMTEncoding_Term.rng =
                                              uu____1367;_})
                                         ->
                                         let uu____1415 =
                                           is_a_post_condition
                                             (FStar_Pervasives_Native.Some
                                                new_post_name) r1 in
                                         if uu____1415
                                         then
                                           let uu____1425 =
                                             aux default_msg
                                               FStar_Pervasives_Native.None
                                               post_name_opt labels1 l0 in
                                           (match uu____1425 with
                                            | (labels2, l) ->
                                                let uu____1444 =
                                                  let uu____1445 =
                                                    let uu____1446 =
                                                      let uu____1466 =
                                                        FStar_SMTEncoding_Util.norng
                                                          FStar_SMTEncoding_Term.mk
                                                          (FStar_SMTEncoding_Term.App
                                                             (FStar_SMTEncoding_Term.Imp,
                                                               [l; r1])) in
                                                      (FStar_SMTEncoding_Term.Forall,
                                                        [[p]],
                                                        (FStar_Pervasives_Native.Some
                                                           (Prims.parse_int "0")),
                                                        sorts1, uu____1466) in
                                                    FStar_SMTEncoding_Term.Quant
                                                      uu____1446 in
                                                  FStar_SMTEncoding_Term.mk
                                                    uu____1445
                                                    q1.FStar_SMTEncoding_Term.rng in
                                                (labels2, uu____1444))
                                         else (labels1, tm)
                                     | uu____1490 -> (labels1, tm)) labels
                                (conjuncts lhs1) in
                            (match uu____1322 with
                             | (labels1, lhs_conjs) ->
                                 let uu____1509 =
                                   aux default_msg
                                     FStar_Pervasives_Native.None
                                     (FStar_Pervasives_Native.Some
                                        new_post_name) labels1 rhs1 in
                                 (match uu____1509 with
                                  | (labels2, rhs2) ->
                                      let body =
                                        let uu____1530 =
                                          let uu____1531 =
                                            let uu____1536 =
                                              FStar_SMTEncoding_Term.mk_and_l
                                                lhs_conjs
                                                lhs1.FStar_SMTEncoding_Term.rng in
                                            (uu____1536, rhs2) in
                                          FStar_SMTEncoding_Term.mkImp
                                            uu____1531 rng in
                                        FStar_All.pipe_right uu____1530
                                          (FStar_SMTEncoding_Term.abstr
                                             names1) in
                                      let q2 =
                                        FStar_SMTEncoding_Term.mk
                                          (FStar_SMTEncoding_Term.Quant
                                             (FStar_SMTEncoding_Term.Forall,
                                               [],
                                               FStar_Pervasives_Native.None,
                                               sorts, body))
                                          q1.FStar_SMTEncoding_Term.rng in
                                      (labels2, q2)))))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Imp, lhs::rhs::[]) ->
                  let uu____1556 =
                    aux default_msg ropt post_name_opt labels rhs in
                  (match uu____1556 with
                   | (labels1, rhs1) ->
                       let uu____1575 =
                         FStar_SMTEncoding_Util.mkImp (lhs, rhs1) in
                       (labels1, uu____1575))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.And, conjuncts1) ->
                  let uu____1583 =
                    FStar_Util.fold_map (aux default_msg ropt post_name_opt)
                      labels conjuncts1 in
                  (match uu____1583 with
                   | (labels1, conjuncts2) ->
                       let uu____1610 =
                         FStar_SMTEncoding_Term.mk_and_l conjuncts2
                           q1.FStar_SMTEncoding_Term.rng in
                       (labels1, uu____1610))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.ITE, hd1::q11::q2::[]) ->
                  let uu____1618 =
                    aux default_msg ropt post_name_opt labels q11 in
                  (match uu____1618 with
                   | (labels1, q12) ->
                       let uu____1637 =
                         aux default_msg ropt post_name_opt labels1 q2 in
                       (match uu____1637 with
                        | (labels2, q21) ->
                            let uu____1656 =
                              FStar_SMTEncoding_Term.mkITE (hd1, q12, q21)
                                q1.FStar_SMTEncoding_Term.rng in
                            (labels2, uu____1656)))
              | FStar_SMTEncoding_Term.Quant
                  (FStar_SMTEncoding_Term.Exists, uu____1659, uu____1660,
                   uu____1661, uu____1662)
                  ->
                  let uu____1681 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____1681 with | (lab, q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Iff, uu____1696) ->
                  let uu____1701 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____1701 with | (lab, q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Or, uu____1716) ->
                  let uu____1721 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____1721 with | (lab, q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Var uu____1736, uu____1737) when
                  is_a_post_condition post_name_opt q1 -> (labels, q1)
              | FStar_SMTEncoding_Term.FreeV uu____1745 ->
                  let uu____1754 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____1754 with | (lab, q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.TrueOp, uu____1769) ->
                  let uu____1774 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____1774 with | (lab, q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.FalseOp, uu____1789) ->
                  let uu____1794 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____1794 with | (lab, q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Not, uu____1809) ->
                  let uu____1814 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____1814 with | (lab, q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Eq, uu____1829) ->
                  let uu____1834 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____1834 with | (lab, q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.LT, uu____1849) ->
                  let uu____1854 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____1854 with | (lab, q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.LTE, uu____1869) ->
                  let uu____1874 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____1874 with | (lab, q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.GT, uu____1889) ->
                  let uu____1894 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____1894 with | (lab, q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.GTE, uu____1909) ->
                  let uu____1914 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____1914 with | (lab, q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvUlt, uu____1929) ->
                  let uu____1934 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____1934 with | (lab, q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Var uu____1949, uu____1950) ->
                  let uu____1956 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____1956 with | (lab, q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.RealDiv, uu____1971) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Add, uu____1983) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Sub, uu____1995) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Div, uu____2007) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Mul, uu____2019) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Minus, uu____2031) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Mod, uu____2043) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvAnd, uu____2055) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvXor, uu____2067) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvOr, uu____2079) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvAdd, uu____2091) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvSub, uu____2103) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvShl, uu____2115) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvShr, uu____2127) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvUdiv, uu____2139) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvMod, uu____2151) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvMul, uu____2163) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvUext uu____2175, uu____2176) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvToNat, uu____2189) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.NatToBv uu____2201, uu____2202) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.ITE, uu____2215) ->
                  failwith "Impossible: arity mismatch"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Imp, uu____2227) ->
                  failwith "Impossible: arity mismatch"
              | FStar_SMTEncoding_Term.Quant
                  (FStar_SMTEncoding_Term.Forall, pats, iopt, sorts, body) ->
                  let uu____2261 =
                    aux default_msg ropt post_name_opt labels body in
                  (match uu____2261 with
                   | (labels1, body1) ->
                       let uu____2280 =
                         FStar_SMTEncoding_Term.mk
                           (FStar_SMTEncoding_Term.Quant
                              (FStar_SMTEncoding_Term.Forall, pats, iopt,
                                sorts, body1)) q1.FStar_SMTEncoding_Term.rng in
                       (labels1, uu____2280))
              | FStar_SMTEncoding_Term.Let (es, body) ->
                  let uu____2298 =
                    aux default_msg ropt post_name_opt labels body in
                  (match uu____2298 with
                   | (labels1, body1) ->
                       let uu____2317 =
                         FStar_SMTEncoding_Term.mkLet (es, body1)
                           q1.FStar_SMTEncoding_Term.rng in
                       (labels1, uu____2317)) in
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
          let print_banner uu____2361 =
            let msg =
              let uu____2364 =
                let uu____2366 = FStar_TypeChecker_Env.get_range env in
                FStar_Range.string_of_range uu____2366 in
              let uu____2367 = FStar_Util.string_of_int (Prims.parse_int "5") in
              let uu____2370 =
                FStar_Util.string_of_int (FStar_List.length all_labels) in
              FStar_Util.format4
                "Detailed %s report follows for %s\nTaking %s seconds per proof obligation (%s proofs in total)\n"
                (if hint_replay then "hint replay" else "error") uu____2364
                uu____2367 uu____2370 in
            FStar_Util.print_error msg in
          let print_result uu____2396 =
            match uu____2396 with
            | ((uu____2409, msg, r), success) ->
                if success
                then
                  let uu____2425 = FStar_Range.string_of_range r in
                  FStar_Util.print1
                    "OK: proof obligation at %s was proven in isolation\n"
                    uu____2425
                else
                  if hint_replay
                  then
                    FStar_Errors.log_issue r
                      (FStar_Errors.Warning_HintFailedToReplayProof,
                        (Prims.op_Hat
                           "Hint failed to replay this sub-proof: " msg))
                  else
                    (let uu____2435 =
                       let uu____2441 =
                         let uu____2443 = FStar_Range.string_of_range r in
                         FStar_Util.format2
                           "XX: proof obligation at %s failed\n\t%s\n"
                           uu____2443 msg in
                       (FStar_Errors.Error_ProofObligationFailed, uu____2441) in
                     FStar_Errors.log_issue r uu____2435) in
          let elim labs =
            FStar_All.pipe_right labs
              (FStar_List.map
                 (fun uu____2496 ->
                    match uu____2496 with
                    | (l, uu____2505, uu____2506) ->
                        let a =
                          let uu____2510 =
                            let uu____2511 =
                              let uu____2516 =
                                FStar_SMTEncoding_Util.mkFreeV l in
                              (uu____2516, FStar_SMTEncoding_Util.mkTrue) in
                            FStar_SMTEncoding_Util.mkEq uu____2511 in
                          let uu____2517 =
                            let uu____2519 = FStar_SMTEncoding_Term.fv_name l in
                            Prims.op_Hat "@disable_label_" uu____2519 in
                          {
                            FStar_SMTEncoding_Term.assumption_term =
                              uu____2510;
                            FStar_SMTEncoding_Term.assumption_caption =
                              (FStar_Pervasives_Native.Some "Disabling label");
                            FStar_SMTEncoding_Term.assumption_name =
                              uu____2517;
                            FStar_SMTEncoding_Term.assumption_fact_ids = []
                          } in
                        FStar_SMTEncoding_Term.Assume a)) in
          let rec linear_check eliminated errors active =
            FStar_SMTEncoding_Z3.refresh ();
            (match active with
             | [] ->
                 let results =
                   let uu____2589 =
                     FStar_List.map (fun x -> (x, true)) eliminated in
                   let uu____2606 =
                     FStar_List.map (fun x -> (x, false)) errors in
                   FStar_List.append uu____2589 uu____2606 in
                 sort_labels results
             | hd1::tl1 ->
                 ((let uu____2633 =
                     FStar_Util.string_of_int (FStar_List.length active) in
                   FStar_Util.print1 "%s, " uu____2633);
                  (let decls =
                     FStar_All.pipe_left elim
                       (FStar_List.append eliminated
                          (FStar_List.append errors tl1)) in
                   let result = askZ3 decls in
                   match result.FStar_SMTEncoding_Z3.z3result_status with
                   | FStar_SMTEncoding_Z3.UNSAT uu____2665 ->
                       linear_check (hd1 :: eliminated) errors tl1
                   | uu____2666 ->
                       linear_check eliminated (hd1 :: errors) tl1))) in
          print_banner ();
          FStar_Options.set_option "z3rlimit"
            (FStar_Options.Int (Prims.parse_int "5"));
          (let res = linear_check [] [] all_labels in
           FStar_Util.print_string "\n";
           FStar_All.pipe_right res (FStar_List.iter print_result);
           (let uu____2715 =
              FStar_Util.for_all FStar_Pervasives_Native.snd res in
            if uu____2715
            then
              FStar_Util.print_string
                "Failed: the heuristic of trying each proof in isolation failed to identify a precise error\n"
            else ()))