open Prims
exception Not_a_wp_implication of Prims.string
let uu___is_Not_a_wp_implication: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Not_a_wp_implication uu____7 -> true
    | uu____8 -> false
let __proj__Not_a_wp_implication__item__uu___: Prims.exn -> Prims.string =
  fun projectee  ->
    match projectee with | Not_a_wp_implication uu____15 -> uu____15
type label = FStar_SMTEncoding_Term.error_label[@@deriving show]
type labels = FStar_SMTEncoding_Term.error_labels[@@deriving show]
let sort_labels:
  (FStar_SMTEncoding_Term.error_label,Prims.bool)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    ((FStar_SMTEncoding_Term.fv,Prims.string,FStar_Range.range)
       FStar_Pervasives_Native.tuple3,Prims.bool)
      FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun l  ->
    FStar_List.sortWith
      (fun uu____63  ->
         fun uu____64  ->
           match (uu____63, uu____64) with
           | (((uu____105,uu____106,r1),uu____108),((uu____109,uu____110,r2),uu____112))
               -> FStar_Range.compare r1 r2) l
let remove_dups:
  labels ->
    (FStar_SMTEncoding_Term.fv,Prims.string,FStar_Range.range)
      FStar_Pervasives_Native.tuple3 Prims.list
  =
  fun l  ->
    FStar_Util.remove_dups
      (fun uu____170  ->
         fun uu____171  ->
           match (uu____170, uu____171) with
           | ((uu____196,m1,r1),(uu____199,m2,r2)) -> (r1 = r2) && (m1 = m2))
      l
type msg = (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2
[@@deriving show]
type ranges =
  (Prims.string FStar_Pervasives_Native.option,FStar_Range.range)
    FStar_Pervasives_Native.tuple2 Prims.list[@@deriving show]
let fresh_label:
  Prims.string ->
    FStar_Range.range ->
      FStar_SMTEncoding_Term.term ->
        (label,FStar_SMTEncoding_Term.term) FStar_Pervasives_Native.tuple2
  =
  let ctr = FStar_Util.mk_ref (Prims.parse_int "0") in
  fun message  ->
    fun range  ->
      fun t  ->
        let l =
          FStar_Util.incr ctr;
          (let uu____265 =
             let uu____266 = FStar_ST.op_Bang ctr in
             FStar_Util.string_of_int uu____266 in
           FStar_Util.format1 "label_%s" uu____265) in
        let lvar = (l, FStar_SMTEncoding_Term.Bool_sort) in
        let label = (lvar, message, range) in
        let lterm = FStar_SMTEncoding_Util.mkFreeV lvar in
        let lt1 = FStar_SMTEncoding_Term.mkOr (lterm, t) range in
        (label, lt1)
let label_goals:
  (Prims.unit -> Prims.string) FStar_Pervasives_Native.option ->
    FStar_Range.range ->
      FStar_SMTEncoding_Term.term ->
        (labels,FStar_SMTEncoding_Term.term) FStar_Pervasives_Native.tuple2
  =
  fun use_env_msg  ->
    fun r  ->
      fun q  ->
        let rec is_a_post_condition post_name_opt tm =
          match (post_name_opt, (tm.FStar_SMTEncoding_Term.tm)) with
          | (FStar_Pervasives_Native.None ,uu____398) -> false
          | (FStar_Pervasives_Native.Some nm,FStar_SMTEncoding_Term.FreeV
             (nm',uu____403)) -> nm = nm'
          | (uu____406,FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var "Valid",tm1::[])) ->
              is_a_post_condition post_name_opt tm1
          | (uu____414,FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var "ApplyTT",tm1::uu____416)) ->
              is_a_post_condition post_name_opt tm1
          | uu____425 -> false in
        let conjuncts t =
          match t.FStar_SMTEncoding_Term.tm with
          | FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And ,cs) -> cs
          | uu____445 -> [t] in
        let is_guard_free tm =
          match tm.FStar_SMTEncoding_Term.tm with
          | FStar_SMTEncoding_Term.Quant
              (FStar_SMTEncoding_Term.Forall
               ,({
                   FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App
                     (FStar_SMTEncoding_Term.Var "Prims.guard_free",p::[]);
                   FStar_SMTEncoding_Term.freevars = uu____451;
                   FStar_SMTEncoding_Term.rng = uu____452;_}::[])::[],iopt,uu____454,
               {
                 FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App
                   (FStar_SMTEncoding_Term.Iff ,l::r1::[]);
                 FStar_SMTEncoding_Term.freevars = uu____457;
                 FStar_SMTEncoding_Term.rng = uu____458;_})
              -> true
          | uu____495 -> false in
        let is_a_named_continuation lhs =
          FStar_All.pipe_right (conjuncts lhs)
            (FStar_Util.for_some is_guard_free) in
        let uu____502 =
          match use_env_msg with
          | FStar_Pervasives_Native.None  -> (false, "")
          | FStar_Pervasives_Native.Some f ->
              let uu____518 = f () in (true, uu____518) in
        match uu____502 with
        | (flag,msg_prefix) ->
            let fresh_label1 msg ropt rng t =
              let msg1 =
                if flag
                then Prims.strcat "Failed to verify implicit argument: " msg
                else msg in
              let rng1 =
                match ropt with
                | FStar_Pervasives_Native.None  -> rng
                | FStar_Pervasives_Native.Some r1 ->
                    let uu____550 = FStar_Range.def_range rng in
                    FStar_Range.set_def_range r1 uu____550 in
              fresh_label msg1 rng1 t in
            let rec aux default_msg ropt post_name_opt labels q1 =
              match q1.FStar_SMTEncoding_Term.tm with
              | FStar_SMTEncoding_Term.BoundV uu____591 -> (labels, q1)
              | FStar_SMTEncoding_Term.Integer uu____594 -> (labels, q1)
              | FStar_SMTEncoding_Term.LblPos uu____597 ->
                  failwith "Impossible"
              | FStar_SMTEncoding_Term.Labeled
                  (arg,"could not prove post-condition",uu____609) ->
                  let fallback msg =
                    aux default_msg ropt post_name_opt labels arg in
                  (try
                     match arg.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.Quant
                         (FStar_SMTEncoding_Term.Forall
                          ,pats,iopt,post::sorts,{
                                                   FStar_SMTEncoding_Term.tm
                                                     =
                                                     FStar_SMTEncoding_Term.App
                                                     (FStar_SMTEncoding_Term.Imp
                                                      ,lhs::rhs::[]);
                                                   FStar_SMTEncoding_Term.freevars
                                                     = uu____668;
                                                   FStar_SMTEncoding_Term.rng
                                                     = rng;_})
                         ->
                         let post_name =
                           let uu____697 =
                             let uu____698 = FStar_Syntax_Syntax.next_id () in
                             FStar_All.pipe_left FStar_Util.string_of_int
                               uu____698 in
                           Prims.strcat "^^post_condition_" uu____697 in
                         let names1 =
                           let uu____706 =
                             FStar_List.mapi
                               (fun i  ->
                                  fun s  ->
                                    let uu____722 =
                                      let uu____723 =
                                        FStar_Util.string_of_int i in
                                      Prims.strcat "^^" uu____723 in
                                    (uu____722, s)) sorts in
                           (post_name, post) :: uu____706 in
                         let instantiation =
                           FStar_List.map FStar_SMTEncoding_Util.mkFreeV
                             names1 in
                         let uu____735 =
                           let uu____740 =
                             FStar_SMTEncoding_Term.inst instantiation lhs in
                           let uu____741 =
                             FStar_SMTEncoding_Term.inst instantiation rhs in
                           (uu____740, uu____741) in
                         (match uu____735 with
                          | (lhs1,rhs1) ->
                              let uu____750 =
                                match lhs1.FStar_SMTEncoding_Term.tm with
                                | FStar_SMTEncoding_Term.App
                                    (FStar_SMTEncoding_Term.And ,clauses_lhs)
                                    ->
                                    let uu____768 =
                                      FStar_Util.prefix clauses_lhs in
                                    (match uu____768 with
                                     | (req,ens) ->
                                         (match ens.FStar_SMTEncoding_Term.tm
                                          with
                                          | FStar_SMTEncoding_Term.Quant
                                              (FStar_SMTEncoding_Term.Forall
                                               ,pats_ens,iopt_ens,sorts_ens,
                                               {
                                                 FStar_SMTEncoding_Term.tm =
                                                   FStar_SMTEncoding_Term.App
                                                   (FStar_SMTEncoding_Term.Imp
                                                    ,ensures_conjuncts::post1::[]);
                                                 FStar_SMTEncoding_Term.freevars
                                                   = uu____798;
                                                 FStar_SMTEncoding_Term.rng =
                                                   rng_ens;_})
                                              when
                                              is_a_post_condition
                                                (FStar_Pervasives_Native.Some
                                                   post_name) post1
                                              ->
                                              let uu____826 =
                                                aux
                                                  "could not prove post-condition"
                                                  FStar_Pervasives_Native.None
                                                  (FStar_Pervasives_Native.Some
                                                     post_name) labels
                                                  ensures_conjuncts in
                                              (match uu____826 with
                                               | (labels1,ensures_conjuncts1)
                                                   ->
                                                   let pats_ens1 =
                                                     match pats_ens with
                                                     | [] -> [[post1]]
                                                     | []::[] -> [[post1]]
                                                     | uu____868 -> pats_ens in
                                                   let ens1 =
                                                     let uu____874 =
                                                       let uu____875 =
                                                         let uu____894 =
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
                                                           uu____894) in
                                                       FStar_SMTEncoding_Term.Quant
                                                         uu____875 in
                                                     FStar_SMTEncoding_Term.mk
                                                       uu____874
                                                       ens.FStar_SMTEncoding_Term.rng in
                                                   let lhs2 =
                                                     FStar_SMTEncoding_Term.mk
                                                       (FStar_SMTEncoding_Term.App
                                                          (FStar_SMTEncoding_Term.And,
                                                            (FStar_List.append
                                                               req [ens1])))
                                                       lhs1.FStar_SMTEncoding_Term.rng in
                                                   let uu____908 =
                                                     FStar_SMTEncoding_Term.abstr
                                                       names1 lhs2 in
                                                   (labels1, uu____908))
                                          | uu____911 ->
                                              let uu____912 =
                                                let uu____913 =
                                                  let uu____914 =
                                                    let uu____915 =
                                                      let uu____916 =
                                                        FStar_SMTEncoding_Term.print_smt_term
                                                          ens in
                                                      Prims.strcat "  ... "
                                                        uu____916 in
                                                    Prims.strcat post_name
                                                      uu____915 in
                                                  Prims.strcat
                                                    "Ensures clause doesn't match post name:  "
                                                    uu____914 in
                                                Not_a_wp_implication
                                                  uu____913 in
                                              FStar_Exn.raise uu____912))
                                | uu____923 ->
                                    let uu____924 =
                                      let uu____925 =
                                        let uu____926 =
                                          FStar_SMTEncoding_Term.print_smt_term
                                            lhs1 in
                                        Prims.strcat "LHS not a conjunct: "
                                          uu____926 in
                                      Not_a_wp_implication uu____925 in
                                    FStar_Exn.raise uu____924 in
                              (match uu____750 with
                               | (labels1,lhs2) ->
                                   let uu____945 =
                                     let uu____952 =
                                       aux default_msg
                                         FStar_Pervasives_Native.None
                                         (FStar_Pervasives_Native.Some
                                            post_name) labels1 rhs1 in
                                     match uu____952 with
                                     | (labels2,rhs2) ->
                                         let uu____971 =
                                           FStar_SMTEncoding_Term.abstr
                                             names1 rhs2 in
                                         (labels2, uu____971) in
                                   (match uu____945 with
                                    | (labels2,rhs2) ->
                                        let body =
                                          FStar_SMTEncoding_Term.mkImp
                                            (lhs2, rhs2) rng in
                                        let uu____987 =
                                          FStar_SMTEncoding_Term.mk
                                            (FStar_SMTEncoding_Term.Quant
                                               (FStar_SMTEncoding_Term.Forall,
                                                 pats, iopt, (post :: sorts),
                                                 body))
                                            q1.FStar_SMTEncoding_Term.rng in
                                        (labels2, uu____987))))
                     | uu____998 ->
                         let uu____999 =
                           let uu____1000 =
                             FStar_SMTEncoding_Term.print_smt_term arg in
                           Prims.strcat "arg not a quant: " uu____1000 in
                         fallback uu____999
                   with | Not_a_wp_implication msg -> fallback msg)
              | FStar_SMTEncoding_Term.Labeled (arg,reason,r1) ->
                  aux reason (FStar_Pervasives_Native.Some r1) post_name_opt
                    labels arg
              | FStar_SMTEncoding_Term.Quant
                  (FStar_SMTEncoding_Term.Forall
                   ,[],FStar_Pervasives_Native.None
                   ,post::[],{
                               FStar_SMTEncoding_Term.tm =
                                 FStar_SMTEncoding_Term.App
                                 (FStar_SMTEncoding_Term.Imp ,lhs::rhs::[]);
                               FStar_SMTEncoding_Term.freevars = uu____1017;
                               FStar_SMTEncoding_Term.rng = rng;_})
                  when is_a_named_continuation lhs ->
                  let post_name =
                    let uu____1040 =
                      let uu____1041 = FStar_Syntax_Syntax.next_id () in
                      FStar_All.pipe_left FStar_Util.string_of_int uu____1041 in
                    Prims.strcat "^^post_condition_" uu____1040 in
                  let names1 = (post_name, post) in
                  let instantiation =
                    let uu____1050 = FStar_SMTEncoding_Util.mkFreeV names1 in
                    [uu____1050] in
                  let uu____1051 =
                    let uu____1056 =
                      FStar_SMTEncoding_Term.inst instantiation lhs in
                    let uu____1057 =
                      FStar_SMTEncoding_Term.inst instantiation rhs in
                    (uu____1056, uu____1057) in
                  (match uu____1051 with
                   | (lhs1,rhs1) ->
                       let uu____1066 =
                         FStar_Util.fold_map
                           (fun labels1  ->
                              fun tm  ->
                                match tm.FStar_SMTEncoding_Term.tm with
                                | FStar_SMTEncoding_Term.Quant
                                    (FStar_SMTEncoding_Term.Forall
                                     ,({
                                         FStar_SMTEncoding_Term.tm =
                                           FStar_SMTEncoding_Term.App
                                           (FStar_SMTEncoding_Term.Var
                                            "Prims.guard_free",p::[]);
                                         FStar_SMTEncoding_Term.freevars =
                                           uu____1103;
                                         FStar_SMTEncoding_Term.rng =
                                           uu____1104;_}::[])::[],iopt,sorts,
                                     {
                                       FStar_SMTEncoding_Term.tm =
                                         FStar_SMTEncoding_Term.App
                                         (FStar_SMTEncoding_Term.Iff
                                          ,l::r1::[]);
                                       FStar_SMTEncoding_Term.freevars =
                                         uu____1109;
                                       FStar_SMTEncoding_Term.rng =
                                         uu____1110;_})
                                    ->
                                    let uu____1147 =
                                      aux default_msg
                                        FStar_Pervasives_Native.None
                                        post_name_opt labels1 r1 in
                                    (match uu____1147 with
                                     | (labels2,r2) ->
                                         let uu____1166 =
                                           let uu____1167 =
                                             let uu____1168 =
                                               let uu____1187 =
                                                 FStar_SMTEncoding_Util.norng
                                                   FStar_SMTEncoding_Term.mk
                                                   (FStar_SMTEncoding_Term.App
                                                      (FStar_SMTEncoding_Term.Iff,
                                                        [l; r2])) in
                                               (FStar_SMTEncoding_Term.Forall,
                                                 [[p]],
                                                 (FStar_Pervasives_Native.Some
                                                    (Prims.parse_int "0")),
                                                 sorts, uu____1187) in
                                             FStar_SMTEncoding_Term.Quant
                                               uu____1168 in
                                           FStar_SMTEncoding_Term.mk
                                             uu____1167
                                             q1.FStar_SMTEncoding_Term.rng in
                                         (labels2, uu____1166))
                                | uu____1204 -> (labels1, tm)) labels
                           (conjuncts lhs1) in
                       (match uu____1066 with
                        | (labels1,lhs_conjs) ->
                            let uu____1223 =
                              aux default_msg FStar_Pervasives_Native.None
                                (FStar_Pervasives_Native.Some post_name)
                                labels1 rhs1 in
                            (match uu____1223 with
                             | (labels2,rhs2) ->
                                 let body =
                                   let uu____1243 =
                                     let uu____1244 =
                                       let uu____1249 =
                                         FStar_SMTEncoding_Term.mk_and_l
                                           lhs_conjs
                                           lhs1.FStar_SMTEncoding_Term.rng in
                                       (uu____1249, rhs2) in
                                     FStar_SMTEncoding_Term.mkImp uu____1244
                                       rng in
                                   FStar_All.pipe_right uu____1243
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
                  (FStar_SMTEncoding_Term.Imp ,lhs::rhs::[]) ->
                  let uu____1275 =
                    aux default_msg ropt post_name_opt labels rhs in
                  (match uu____1275 with
                   | (labels1,rhs1) ->
                       let uu____1294 =
                         FStar_SMTEncoding_Util.mkImp (lhs, rhs1) in
                       (labels1, uu____1294))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.And ,conjuncts1) ->
                  let uu____1302 =
                    FStar_Util.fold_map (aux default_msg ropt post_name_opt)
                      labels conjuncts1 in
                  (match uu____1302 with
                   | (labels1,conjuncts2) ->
                       let uu____1329 =
                         FStar_SMTEncoding_Term.mk_and_l conjuncts2
                           q1.FStar_SMTEncoding_Term.rng in
                       (labels1, uu____1329))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.ITE ,hd1::q11::q2::[]) ->
                  let uu____1337 =
                    aux default_msg ropt post_name_opt labels q11 in
                  (match uu____1337 with
                   | (labels1,q12) ->
                       let uu____1356 =
                         aux default_msg ropt post_name_opt labels1 q2 in
                       (match uu____1356 with
                        | (labels2,q21) ->
                            let uu____1375 =
                              FStar_SMTEncoding_Term.mkITE (hd1, q12, q21)
                                q1.FStar_SMTEncoding_Term.rng in
                            (labels2, uu____1375)))
              | FStar_SMTEncoding_Term.Quant
                  (FStar_SMTEncoding_Term.Exists
                   ,uu____1378,uu____1379,uu____1380,uu____1381)
                  ->
                  let uu____1398 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____1398 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Iff ,uu____1413) ->
                  let uu____1418 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____1418 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Or ,uu____1433) ->
                  let uu____1438 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____1438 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Var uu____1453,uu____1454) when
                  is_a_post_condition post_name_opt q1 -> (labels, q1)
              | FStar_SMTEncoding_Term.FreeV uu____1461 ->
                  let uu____1466 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____1466 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.TrueOp ,uu____1481) ->
                  let uu____1486 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____1486 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.FalseOp ,uu____1501) ->
                  let uu____1506 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____1506 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Not ,uu____1521) ->
                  let uu____1526 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____1526 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Eq ,uu____1541) ->
                  let uu____1546 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____1546 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.LT ,uu____1561) ->
                  let uu____1566 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____1566 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.LTE ,uu____1581) ->
                  let uu____1586 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____1586 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.GT ,uu____1601) ->
                  let uu____1606 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____1606 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.GTE ,uu____1621) ->
                  let uu____1626 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____1626 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvUlt ,uu____1641) ->
                  let uu____1646 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____1646 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Var uu____1661,uu____1662) ->
                  let uu____1667 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____1667 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Add ,uu____1682) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Sub ,uu____1693) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Div ,uu____1704) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Mul ,uu____1715) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Minus ,uu____1726) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Mod ,uu____1737) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvAnd ,uu____1748) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvXor ,uu____1759) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvOr ,uu____1770) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvAdd ,uu____1781) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvSub ,uu____1792) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvShl ,uu____1803) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvShr ,uu____1814) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvUdiv ,uu____1825) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvMod ,uu____1836) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvMul ,uu____1847) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvUext uu____1858,uu____1859) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvToNat ,uu____1870) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.NatToBv uu____1881,uu____1882) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.ITE ,uu____1893) ->
                  failwith "Impossible: arity mismatch"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Imp ,uu____1904) ->
                  failwith "Impossible: arity mismatch"
              | FStar_SMTEncoding_Term.Quant
                  (FStar_SMTEncoding_Term.Forall ,pats,iopt,sorts,body) ->
                  let uu____1935 =
                    aux default_msg ropt post_name_opt labels body in
                  (match uu____1935 with
                   | (labels1,body1) ->
                       let uu____1954 =
                         FStar_SMTEncoding_Term.mk
                           (FStar_SMTEncoding_Term.Quant
                              (FStar_SMTEncoding_Term.Forall, pats, iopt,
                                sorts, body1)) q1.FStar_SMTEncoding_Term.rng in
                       (labels1, uu____1954))
              | FStar_SMTEncoding_Term.Let (es,body) ->
                  let uu____1971 =
                    aux default_msg ropt post_name_opt labels body in
                  (match uu____1971 with
                   | (labels1,body1) ->
                       let uu____1990 =
                         FStar_SMTEncoding_Term.mkLet (es, body1)
                           q1.FStar_SMTEncoding_Term.rng in
                       (labels1, uu____1990)) in
            aux "assertion failed" FStar_Pervasives_Native.None
              FStar_Pervasives_Native.None [] q
let detail_errors:
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      labels ->
        (FStar_SMTEncoding_Term.decls_t -> FStar_SMTEncoding_Z3.z3result) ->
          Prims.unit
  =
  fun hint_replay  ->
    fun env  ->
      fun all_labels  ->
        fun askZ3  ->
          let print_banner uu____2015 =
            let msg =
              let uu____2017 =
                let uu____2018 = FStar_TypeChecker_Env.get_range env in
                FStar_Range.string_of_range uu____2018 in
              let uu____2019 = FStar_Util.string_of_int (Prims.parse_int "5") in
              let uu____2020 =
                FStar_Util.string_of_int (FStar_List.length all_labels) in
              FStar_Util.format4
                "Detailed %s report follows for %s\nTaking %s seconds per proof obligation (%s proofs in total)\n"
                (if hint_replay then "hint replay" else "error") uu____2017
                uu____2019 uu____2020 in
            FStar_Util.print_error msg in
          let print_result uu____2035 =
            match uu____2035 with
            | ((uu____2046,msg,r),success) ->
                if success
                then
                  let uu____2056 = FStar_Range.string_of_range r in
                  FStar_Util.print1_error
                    "OK: proof obligation at %s was proven\n" uu____2056
                else
                  if hint_replay
                  then
                    FStar_Errors.warn r
                      (Prims.strcat "Hint failed to replay this sub-proof: "
                         msg)
                  else
                    ((let uu____2060 = FStar_Range.string_of_range r in
                      FStar_Util.print2_error
                        "XX: proof obligation at %s failed\n\t%s\n"
                        uu____2060 msg);
                     FStar_Errors.err r msg) in
          let elim labs =
            FStar_All.pipe_right labs
              (FStar_List.map
                 (fun uu____2120  ->
                    match uu____2120 with
                    | (l,uu____2132,uu____2133) ->
                        let a =
                          let uu____2143 =
                            let uu____2144 =
                              let uu____2149 =
                                FStar_SMTEncoding_Util.mkFreeV l in
                              (uu____2149, FStar_SMTEncoding_Util.mkTrue) in
                            FStar_SMTEncoding_Util.mkEq uu____2144 in
                          {
                            FStar_SMTEncoding_Term.assumption_term =
                              uu____2143;
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
                   let uu____2204 =
                     FStar_List.map (fun x  -> (x, true)) eliminated in
                   let uu____2217 =
                     FStar_List.map (fun x  -> (x, false)) errors in
                   FStar_List.append uu____2204 uu____2217 in
                 sort_labels results
             | hd1::tl1 ->
                 ((let uu____2239 =
                     FStar_Util.string_of_int (FStar_List.length active) in
                   FStar_Util.print1 "%s, " uu____2239);
                  (let decls =
                     FStar_All.pipe_left elim
                       (FStar_List.append eliminated
                          (FStar_List.append errors tl1)) in
                   let result = askZ3 decls in
                   match result.FStar_SMTEncoding_Z3.z3result_status with
                   | FStar_SMTEncoding_Z3.UNSAT uu____2270 ->
                       linear_check (hd1 :: eliminated) errors tl1
                   | uu____2271 ->
                       linear_check eliminated (hd1 :: errors) tl1))) in
          print_banner ();
          FStar_Options.set_option "z3rlimit"
            (FStar_Options.Int (Prims.parse_int "5"));
          (let res = linear_check [] [] all_labels in
           FStar_Util.print_string "\n";
           FStar_All.pipe_right res (FStar_List.iter print_result))