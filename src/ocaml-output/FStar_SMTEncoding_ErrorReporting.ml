open Prims
exception Not_a_wp_implication of Prims.string 
let (uu___is_Not_a_wp_implication : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Not_a_wp_implication uu____7 -> true
    | uu____8 -> false
let (__proj__Not_a_wp_implication__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee ->
    match projectee with | Not_a_wp_implication uu____15 -> uu____15
type label = FStar_SMTEncoding_Term.error_label[@@deriving show]
type labels = FStar_SMTEncoding_Term.error_labels[@@deriving show]
let (sort_labels :
  (FStar_SMTEncoding_Term.error_label, Prims.bool)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    ((FStar_SMTEncoding_Term.fv, Prims.string, FStar_Range.range)
       FStar_Pervasives_Native.tuple3,
      Prims.bool) FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun l ->
    FStar_List.sortWith
      (fun uu____63 ->
         fun uu____64 ->
           match (uu____63, uu____64) with
           | (((uu____105, uu____106, r1), uu____108),
              ((uu____109, uu____110, r2), uu____112)) ->
               FStar_Range.compare r1 r2) l
let (remove_dups :
  labels ->
    (FStar_SMTEncoding_Term.fv, Prims.string, FStar_Range.range)
      FStar_Pervasives_Native.tuple3 Prims.list)
  =
  fun l ->
    FStar_Util.remove_dups
      (fun uu____170 ->
         fun uu____171 ->
           match (uu____170, uu____171) with
           | ((uu____196, m1, r1), (uu____199, m2, r2)) ->
               (r1 = r2) && (m1 = m2)) l
type msg = (Prims.string, FStar_Range.range) FStar_Pervasives_Native.tuple2
[@@deriving show]
type ranges =
  (Prims.string FStar_Pervasives_Native.option, FStar_Range.range)
    FStar_Pervasives_Native.tuple2 Prims.list[@@deriving show]
let (fresh_label :
  Prims.string ->
    FStar_Range.range ->
      FStar_SMTEncoding_Term.term ->
        (label, FStar_SMTEncoding_Term.term) FStar_Pervasives_Native.tuple2)
  =
  let ctr = FStar_Util.mk_ref (Prims.parse_int "0") in
  fun message ->
    fun range ->
      fun t ->
        let l =
          FStar_Util.incr ctr;
          (let uu____349 =
             let uu____350 = FStar_ST.op_Bang ctr in
             FStar_Util.string_of_int uu____350 in
           FStar_Util.format1 "label_%s" uu____349) in
        let lvar = (l, FStar_SMTEncoding_Term.Bool_sort) in
        let label = (lvar, message, range) in
        let lterm = FStar_SMTEncoding_Util.mkFreeV lvar in
        let lt1 = FStar_SMTEncoding_Term.mkOr (lterm, t) range in
        (label, lt1)
let (label_goals :
  (Prims.unit -> Prims.string) FStar_Pervasives_Native.option ->
    FStar_Range.range ->
      FStar_SMTEncoding_Term.term ->
        (labels, FStar_SMTEncoding_Term.term) FStar_Pervasives_Native.tuple2)
  =
  fun use_env_msg ->
    fun r ->
      fun q ->
        let rec is_a_post_condition post_name_opt tm =
          match (post_name_opt, (tm.FStar_SMTEncoding_Term.tm)) with
          | (FStar_Pervasives_Native.None, uu____517) -> false
          | (FStar_Pervasives_Native.Some nm, FStar_SMTEncoding_Term.FreeV
             (nm', uu____522)) -> nm = nm'
          | (uu____525, FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var "Valid", tm1::[])) ->
              is_a_post_condition post_name_opt tm1
          | (uu____533, FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var "ApplyTT", tm1::uu____535)) ->
              is_a_post_condition post_name_opt tm1
          | uu____544 -> false in
        let conjuncts t =
          match t.FStar_SMTEncoding_Term.tm with
          | FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And, cs) -> cs
          | uu____564 -> [t] in
        let is_guard_free tm =
          match tm.FStar_SMTEncoding_Term.tm with
          | FStar_SMTEncoding_Term.Quant
              (FStar_SMTEncoding_Term.Forall,
               ({
                  FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App
                    (FStar_SMTEncoding_Term.Var "Prims.guard_free", p::[]);
                  FStar_SMTEncoding_Term.freevars = uu____570;
                  FStar_SMTEncoding_Term.rng = uu____571;_}::[])::[],
               iopt, uu____573,
               {
                 FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App
                   (FStar_SMTEncoding_Term.Iff, l::r1::[]);
                 FStar_SMTEncoding_Term.freevars = uu____576;
                 FStar_SMTEncoding_Term.rng = uu____577;_})
              -> true
          | uu____614 -> false in
        let is_a_named_continuation lhs =
          FStar_All.pipe_right (conjuncts lhs)
            (FStar_Util.for_some is_guard_free) in
        let uu____621 =
          match use_env_msg with
          | FStar_Pervasives_Native.None -> (false, "")
          | FStar_Pervasives_Native.Some f ->
              let uu____637 = f () in (true, uu____637) in
        match uu____621 with
        | (flag, msg_prefix) ->
            let fresh_label1 msg ropt rng t =
              let msg1 =
                if flag
                then Prims.strcat "Failed to verify implicit argument: " msg
                else msg in
              let rng1 =
                match ropt with
                | FStar_Pervasives_Native.None -> rng
                | FStar_Pervasives_Native.Some r1 ->
                    let uu____669 = FStar_Range.def_range rng in
                    FStar_Range.set_def_range r1 uu____669 in
              fresh_label msg1 rng1 t in
            let rec aux default_msg ropt post_name_opt labels q1 =
              match q1.FStar_SMTEncoding_Term.tm with
              | FStar_SMTEncoding_Term.BoundV uu____710 -> (labels, q1)
              | FStar_SMTEncoding_Term.Integer uu____713 -> (labels, q1)
              | FStar_SMTEncoding_Term.LblPos uu____716 ->
                  failwith "Impossible"
              | FStar_SMTEncoding_Term.Labeled
                  (arg, "could not prove post-condition", uu____728) ->
                  let fallback msg =
                    aux default_msg ropt post_name_opt labels arg in
                  (try
                     match arg.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.Quant
                         (FStar_SMTEncoding_Term.Forall, pats, iopt,
                          post::sorts,
                          {
                            FStar_SMTEncoding_Term.tm =
                              FStar_SMTEncoding_Term.App
                              (FStar_SMTEncoding_Term.Imp, lhs::rhs::[]);
                            FStar_SMTEncoding_Term.freevars = uu____787;
                            FStar_SMTEncoding_Term.rng = rng;_})
                         ->
                         let post_name =
                           let uu____816 =
                             let uu____817 = FStar_Syntax_Syntax.next_id () in
                             FStar_All.pipe_left FStar_Util.string_of_int
                               uu____817 in
                           Prims.strcat "^^post_condition_" uu____816 in
                         let names1 =
                           let uu____825 =
                             FStar_List.mapi
                               (fun i ->
                                  fun s ->
                                    let uu____841 =
                                      let uu____842 =
                                        FStar_Util.string_of_int i in
                                      Prims.strcat "^^" uu____842 in
                                    (uu____841, s)) sorts in
                           (post_name, post) :: uu____825 in
                         let instantiation =
                           FStar_List.map FStar_SMTEncoding_Util.mkFreeV
                             names1 in
                         let uu____854 =
                           let uu____859 =
                             FStar_SMTEncoding_Term.inst instantiation lhs in
                           let uu____860 =
                             FStar_SMTEncoding_Term.inst instantiation rhs in
                           (uu____859, uu____860) in
                         (match uu____854 with
                          | (lhs1, rhs1) ->
                              let uu____869 =
                                match lhs1.FStar_SMTEncoding_Term.tm with
                                | FStar_SMTEncoding_Term.App
                                    (FStar_SMTEncoding_Term.And, clauses_lhs)
                                    ->
                                    let uu____887 =
                                      FStar_Util.prefix clauses_lhs in
                                    (match uu____887 with
                                     | (req, ens) ->
                                         (match ens.FStar_SMTEncoding_Term.tm
                                          with
                                          | FStar_SMTEncoding_Term.Quant
                                              (FStar_SMTEncoding_Term.Forall,
                                               pats_ens, iopt_ens, sorts_ens,
                                               {
                                                 FStar_SMTEncoding_Term.tm =
                                                   FStar_SMTEncoding_Term.App
                                                   (FStar_SMTEncoding_Term.Imp,
                                                    ensures_conjuncts::post1::[]);
                                                 FStar_SMTEncoding_Term.freevars
                                                   = uu____917;
                                                 FStar_SMTEncoding_Term.rng =
                                                   rng_ens;_})
                                              when
                                              is_a_post_condition
                                                (FStar_Pervasives_Native.Some
                                                   post_name) post1
                                              ->
                                              let uu____945 =
                                                aux
                                                  "could not prove post-condition"
                                                  FStar_Pervasives_Native.None
                                                  (FStar_Pervasives_Native.Some
                                                     post_name) labels
                                                  ensures_conjuncts in
                                              (match uu____945 with
                                               | (labels1,
                                                  ensures_conjuncts1) ->
                                                   let pats_ens1 =
                                                     match pats_ens with
                                                     | [] -> [[post1]]
                                                     | []::[] -> [[post1]]
                                                     | uu____987 -> pats_ens in
                                                   let ens1 =
                                                     let uu____993 =
                                                       let uu____994 =
                                                         let uu____1013 =
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
                                                           uu____1013) in
                                                       FStar_SMTEncoding_Term.Quant
                                                         uu____994 in
                                                     FStar_SMTEncoding_Term.mk
                                                       uu____993
                                                       ens.FStar_SMTEncoding_Term.rng in
                                                   let lhs2 =
                                                     FStar_SMTEncoding_Term.mk
                                                       (FStar_SMTEncoding_Term.App
                                                          (FStar_SMTEncoding_Term.And,
                                                            (FStar_List.append
                                                               req [ens1])))
                                                       lhs1.FStar_SMTEncoding_Term.rng in
                                                   let uu____1027 =
                                                     FStar_SMTEncoding_Term.abstr
                                                       names1 lhs2 in
                                                   (labels1, uu____1027))
                                          | uu____1030 ->
                                              let uu____1031 =
                                                let uu____1032 =
                                                  let uu____1033 =
                                                    let uu____1034 =
                                                      let uu____1035 =
                                                        FStar_SMTEncoding_Term.print_smt_term
                                                          ens in
                                                      Prims.strcat "  ... "
                                                        uu____1035 in
                                                    Prims.strcat post_name
                                                      uu____1034 in
                                                  Prims.strcat
                                                    "Ensures clause doesn't match post name:  "
                                                    uu____1033 in
                                                Not_a_wp_implication
                                                  uu____1032 in
                                              FStar_Exn.raise uu____1031))
                                | uu____1042 ->
                                    let uu____1043 =
                                      let uu____1044 =
                                        let uu____1045 =
                                          FStar_SMTEncoding_Term.print_smt_term
                                            lhs1 in
                                        Prims.strcat "LHS not a conjunct: "
                                          uu____1045 in
                                      Not_a_wp_implication uu____1044 in
                                    FStar_Exn.raise uu____1043 in
                              (match uu____869 with
                               | (labels1, lhs2) ->
                                   let uu____1064 =
                                     let uu____1071 =
                                       aux default_msg
                                         FStar_Pervasives_Native.None
                                         (FStar_Pervasives_Native.Some
                                            post_name) labels1 rhs1 in
                                     match uu____1071 with
                                     | (labels2, rhs2) ->
                                         let uu____1090 =
                                           FStar_SMTEncoding_Term.abstr
                                             names1 rhs2 in
                                         (labels2, uu____1090) in
                                   (match uu____1064 with
                                    | (labels2, rhs2) ->
                                        let body =
                                          FStar_SMTEncoding_Term.mkImp
                                            (lhs2, rhs2) rng in
                                        let uu____1106 =
                                          FStar_SMTEncoding_Term.mk
                                            (FStar_SMTEncoding_Term.Quant
                                               (FStar_SMTEncoding_Term.Forall,
                                                 pats, iopt, (post :: sorts),
                                                 body))
                                            q1.FStar_SMTEncoding_Term.rng in
                                        (labels2, uu____1106))))
                     | uu____1117 ->
                         let uu____1118 =
                           let uu____1119 =
                             FStar_SMTEncoding_Term.print_smt_term arg in
                           Prims.strcat "arg not a quant: " uu____1119 in
                         fallback uu____1118
                   with | Not_a_wp_implication msg -> fallback msg)
              | FStar_SMTEncoding_Term.Labeled (arg, reason, r1) ->
                  aux reason (FStar_Pervasives_Native.Some r1) post_name_opt
                    labels arg
              | FStar_SMTEncoding_Term.Quant
                  (FStar_SMTEncoding_Term.Forall, [],
                   FStar_Pervasives_Native.None, post::[],
                   {
                     FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App
                       (FStar_SMTEncoding_Term.Imp, lhs::rhs::[]);
                     FStar_SMTEncoding_Term.freevars = uu____1136;
                     FStar_SMTEncoding_Term.rng = rng;_})
                  when is_a_named_continuation lhs ->
                  let post_name =
                    let uu____1159 =
                      let uu____1160 = FStar_Syntax_Syntax.next_id () in
                      FStar_All.pipe_left FStar_Util.string_of_int uu____1160 in
                    Prims.strcat "^^post_condition_" uu____1159 in
                  let names1 = (post_name, post) in
                  let instantiation =
                    let uu____1169 = FStar_SMTEncoding_Util.mkFreeV names1 in
                    [uu____1169] in
                  let uu____1170 =
                    let uu____1175 =
                      FStar_SMTEncoding_Term.inst instantiation lhs in
                    let uu____1176 =
                      FStar_SMTEncoding_Term.inst instantiation rhs in
                    (uu____1175, uu____1176) in
                  (match uu____1170 with
                   | (lhs1, rhs1) ->
                       let uu____1185 =
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
                                        FStar_SMTEncoding_Term.freevars =
                                          uu____1222;
                                        FStar_SMTEncoding_Term.rng =
                                          uu____1223;_}::[])::[],
                                     iopt, sorts,
                                     {
                                       FStar_SMTEncoding_Term.tm =
                                         FStar_SMTEncoding_Term.App
                                         (FStar_SMTEncoding_Term.Iff,
                                          l::r1::[]);
                                       FStar_SMTEncoding_Term.freevars =
                                         uu____1228;
                                       FStar_SMTEncoding_Term.rng =
                                         uu____1229;_})
                                    ->
                                    let uu____1266 =
                                      aux default_msg
                                        FStar_Pervasives_Native.None
                                        post_name_opt labels1 r1 in
                                    (match uu____1266 with
                                     | (labels2, r2) ->
                                         let uu____1285 =
                                           let uu____1286 =
                                             let uu____1287 =
                                               let uu____1306 =
                                                 FStar_SMTEncoding_Util.norng
                                                   FStar_SMTEncoding_Term.mk
                                                   (FStar_SMTEncoding_Term.App
                                                      (FStar_SMTEncoding_Term.Iff,
                                                        [l; r2])) in
                                               (FStar_SMTEncoding_Term.Forall,
                                                 [[p]],
                                                 (FStar_Pervasives_Native.Some
                                                    (Prims.parse_int "0")),
                                                 sorts, uu____1306) in
                                             FStar_SMTEncoding_Term.Quant
                                               uu____1287 in
                                           FStar_SMTEncoding_Term.mk
                                             uu____1286
                                             q1.FStar_SMTEncoding_Term.rng in
                                         (labels2, uu____1285))
                                | uu____1323 -> (labels1, tm)) labels
                           (conjuncts lhs1) in
                       (match uu____1185 with
                        | (labels1, lhs_conjs) ->
                            let uu____1342 =
                              aux default_msg FStar_Pervasives_Native.None
                                (FStar_Pervasives_Native.Some post_name)
                                labels1 rhs1 in
                            (match uu____1342 with
                             | (labels2, rhs2) ->
                                 let body =
                                   let uu____1362 =
                                     let uu____1363 =
                                       let uu____1368 =
                                         FStar_SMTEncoding_Term.mk_and_l
                                           lhs_conjs
                                           lhs1.FStar_SMTEncoding_Term.rng in
                                       (uu____1368, rhs2) in
                                     FStar_SMTEncoding_Term.mkImp uu____1363
                                       rng in
                                   FStar_All.pipe_right uu____1362
                                     (FStar_SMTEncoding_Term.abstr [names1]) in
                                 let q2 =
                                   FStar_SMTEncoding_Term.mk
                                     (FStar_SMTEncoding_Term.Quant
                                        (FStar_SMTEncoding_Term.Forall, [],
                                          FStar_Pervasives_Native.None,
                                          [post], body))
                                     q1.FStar_SMTEncoding_Term.rng in
                                 (labels2, q2))))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Imp, lhs::rhs::[]) ->
                  let uu____1394 =
                    aux default_msg ropt post_name_opt labels rhs in
                  (match uu____1394 with
                   | (labels1, rhs1) ->
                       let uu____1413 =
                         FStar_SMTEncoding_Util.mkImp (lhs, rhs1) in
                       (labels1, uu____1413))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.And, conjuncts1) ->
                  let uu____1421 =
                    FStar_Util.fold_map (aux default_msg ropt post_name_opt)
                      labels conjuncts1 in
                  (match uu____1421 with
                   | (labels1, conjuncts2) ->
                       let uu____1448 =
                         FStar_SMTEncoding_Term.mk_and_l conjuncts2
                           q1.FStar_SMTEncoding_Term.rng in
                       (labels1, uu____1448))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.ITE, hd1::q11::q2::[]) ->
                  let uu____1456 =
                    aux default_msg ropt post_name_opt labels q11 in
                  (match uu____1456 with
                   | (labels1, q12) ->
                       let uu____1475 =
                         aux default_msg ropt post_name_opt labels1 q2 in
                       (match uu____1475 with
                        | (labels2, q21) ->
                            let uu____1494 =
                              FStar_SMTEncoding_Term.mkITE (hd1, q12, q21)
                                q1.FStar_SMTEncoding_Term.rng in
                            (labels2, uu____1494)))
              | FStar_SMTEncoding_Term.Quant
                  (FStar_SMTEncoding_Term.Exists, uu____1497, uu____1498,
                   uu____1499, uu____1500)
                  ->
                  let uu____1517 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____1517 with | (lab, q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Iff, uu____1532) ->
                  let uu____1537 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____1537 with | (lab, q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Or, uu____1552) ->
                  let uu____1557 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____1557 with | (lab, q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Var uu____1572, uu____1573) when
                  is_a_post_condition post_name_opt q1 -> (labels, q1)
              | FStar_SMTEncoding_Term.FreeV uu____1580 ->
                  let uu____1585 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____1585 with | (lab, q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.TrueOp, uu____1600) ->
                  let uu____1605 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____1605 with | (lab, q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.FalseOp, uu____1620) ->
                  let uu____1625 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____1625 with | (lab, q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Not, uu____1640) ->
                  let uu____1645 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____1645 with | (lab, q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Eq, uu____1660) ->
                  let uu____1665 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____1665 with | (lab, q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.LT, uu____1680) ->
                  let uu____1685 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____1685 with | (lab, q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.LTE, uu____1700) ->
                  let uu____1705 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____1705 with | (lab, q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.GT, uu____1720) ->
                  let uu____1725 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____1725 with | (lab, q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.GTE, uu____1740) ->
                  let uu____1745 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____1745 with | (lab, q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvUlt, uu____1760) ->
                  let uu____1765 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____1765 with | (lab, q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Var uu____1780, uu____1781) ->
                  let uu____1786 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____1786 with | (lab, q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Add, uu____1801) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Sub, uu____1812) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Div, uu____1823) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Mul, uu____1834) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Minus, uu____1845) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Mod, uu____1856) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvAnd, uu____1867) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvXor, uu____1878) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvOr, uu____1889) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvAdd, uu____1900) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvSub, uu____1911) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvShl, uu____1922) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvShr, uu____1933) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvUdiv, uu____1944) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvMod, uu____1955) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvMul, uu____1966) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvUext uu____1977, uu____1978) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvToNat, uu____1989) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.NatToBv uu____2000, uu____2001) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.ITE, uu____2012) ->
                  failwith "Impossible: arity mismatch"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Imp, uu____2023) ->
                  failwith "Impossible: arity mismatch"
              | FStar_SMTEncoding_Term.Quant
                  (FStar_SMTEncoding_Term.Forall, pats, iopt, sorts, body) ->
                  let uu____2054 =
                    aux default_msg ropt post_name_opt labels body in
                  (match uu____2054 with
                   | (labels1, body1) ->
                       let uu____2073 =
                         FStar_SMTEncoding_Term.mk
                           (FStar_SMTEncoding_Term.Quant
                              (FStar_SMTEncoding_Term.Forall, pats, iopt,
                                sorts, body1)) q1.FStar_SMTEncoding_Term.rng in
                       (labels1, uu____2073))
              | FStar_SMTEncoding_Term.Let (es, body) ->
                  let uu____2090 =
                    aux default_msg ropt post_name_opt labels body in
                  (match uu____2090 with
                   | (labels1, body1) ->
                       let uu____2109 =
                         FStar_SMTEncoding_Term.mkLet (es, body1)
                           q1.FStar_SMTEncoding_Term.rng in
                       (labels1, uu____2109)) in
            aux "assertion failed" FStar_Pervasives_Native.None
              FStar_Pervasives_Native.None [] q
let (detail_errors :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      labels ->
        (FStar_SMTEncoding_Term.decls_t -> FStar_SMTEncoding_Z3.z3result) ->
          Prims.unit)
  =
  fun hint_replay ->
    fun env ->
      fun all_labels ->
        fun askZ3 ->
          let print_banner uu____2134 =
            let msg =
              let uu____2136 =
                let uu____2137 = FStar_TypeChecker_Env.get_range env in
                FStar_Range.string_of_range uu____2137 in
              let uu____2138 = FStar_Util.string_of_int (Prims.parse_int "5") in
              let uu____2139 =
                FStar_Util.string_of_int (FStar_List.length all_labels) in
              FStar_Util.format4
                "Detailed %s report follows for %s\nTaking %s seconds per proof obligation (%s proofs in total)\n"
                (if hint_replay then "hint replay" else "error") uu____2136
                uu____2138 uu____2139 in
            FStar_Util.print_error msg in
          let print_result uu____2154 =
            match uu____2154 with
            | ((uu____2165, msg, r), success) ->
                if success
                then
                  let uu____2175 = FStar_Range.string_of_range r in
                  FStar_Util.print1 "OK: proof obligation at %s was proven\n"
                    uu____2175
                else
                  if hint_replay
                  then
                    FStar_Errors.log_issue r
                      (FStar_Errors.Warning_HintFailedToReplayProof,
                        (Prims.strcat
                           "Hint failed to replay this sub-proof: " msg))
                  else
                    (let uu____2178 =
                       let uu____2183 =
                         let uu____2184 = FStar_Range.string_of_range r in
                         FStar_Util.format2
                           "XX: proof obligation at %s failed\n\t%s\n"
                           uu____2184 msg in
                       (FStar_Errors.Error_ProofObligationFailed, uu____2183) in
                     FStar_Errors.log_issue r uu____2178) in
          let elim labs =
            FStar_All.pipe_right labs
              (FStar_List.map
                 (fun uu____2244 ->
                    match uu____2244 with
                    | (l, uu____2256, uu____2257) ->
                        let a =
                          let uu____2267 =
                            let uu____2268 =
                              let uu____2273 =
                                FStar_SMTEncoding_Util.mkFreeV l in
                              (uu____2273, FStar_SMTEncoding_Util.mkTrue) in
                            FStar_SMTEncoding_Util.mkEq uu____2268 in
                          {
                            FStar_SMTEncoding_Term.assumption_term =
                              uu____2267;
                            FStar_SMTEncoding_Term.assumption_caption =
                              (FStar_Pervasives_Native.Some "Disabling label");
                            FStar_SMTEncoding_Term.assumption_name =
                              (Prims.strcat "@disable_label_"
                                 (FStar_Pervasives_Native.fst l));
                            FStar_SMTEncoding_Term.assumption_fact_ids = []
                          } in
                        FStar_SMTEncoding_Term.Assume a)) in
          let rec linear_check eliminated errors active =
            FStar_SMTEncoding_Z3.refresh ();
            (match active with
             | [] ->
                 let results =
                   let uu____2328 =
                     FStar_List.map (fun x -> (x, true)) eliminated in
                   let uu____2341 =
                     FStar_List.map (fun x -> (x, false)) errors in
                   FStar_List.append uu____2328 uu____2341 in
                 sort_labels results
             | hd1::tl1 ->
                 ((let uu____2363 =
                     FStar_Util.string_of_int (FStar_List.length active) in
                   FStar_Util.print1 "%s, " uu____2363);
                  (let decls =
                     FStar_All.pipe_left elim
                       (FStar_List.append eliminated
                          (FStar_List.append errors tl1)) in
                   let result = askZ3 decls in
                   match result.FStar_SMTEncoding_Z3.z3result_status with
                   | FStar_SMTEncoding_Z3.UNSAT uu____2394 ->
                       linear_check (hd1 :: eliminated) errors tl1
                   | uu____2395 ->
                       linear_check eliminated (hd1 :: errors) tl1))) in
          print_banner ();
          FStar_Options.set_option "z3rlimit"
            (FStar_Options.Int (Prims.parse_int "5"));
          (let res = linear_check [] [] all_labels in
           FStar_Util.print_string "\n";
           FStar_All.pipe_right res (FStar_List.iter print_result))