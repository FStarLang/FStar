open Prims
exception Not_a_wp_implication of Prims.string
let uu___is_Not_a_wp_implication: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Not_a_wp_implication uu____8 -> true
    | uu____9 -> false
let __proj__Not_a_wp_implication__item__uu___: Prims.exn -> Prims.string =
  fun projectee  ->
    match projectee with | Not_a_wp_implication uu____17 -> uu____17
type label = FStar_SMTEncoding_Term.error_label
type labels = FStar_SMTEncoding_Term.error_labels
let sort_labels:
  (FStar_SMTEncoding_Term.error_label,Prims.bool)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    ((FStar_SMTEncoding_Term.fv,Prims.string,FStar_Range.range)
       FStar_Pervasives_Native.tuple3,Prims.bool)
      FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun l  ->
    FStar_List.sortWith
      (fun uu____66  ->
         fun uu____67  ->
           match (uu____66, uu____67) with
           | (((uu____108,uu____109,r1),uu____111),((uu____112,uu____113,r2),uu____115))
               -> FStar_Range.compare r1 r2) l
let remove_dups:
  labels ->
    (FStar_SMTEncoding_Term.fv,Prims.string,FStar_Range.range)
      FStar_Pervasives_Native.tuple3 Prims.list
  =
  fun l  ->
    FStar_Util.remove_dups
      (fun uu____174  ->
         fun uu____175  ->
           match (uu____174, uu____175) with
           | ((uu____200,m1,r1),(uu____203,m2,r2)) -> (r1 = r2) && (m1 = m2))
      l
type msg = (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2
type ranges =
  (Prims.string FStar_Pervasives_Native.option,FStar_Range.range)
    FStar_Pervasives_Native.tuple2 Prims.list
let fresh_label:
  Prims.string ->
    FStar_Range.range ->
      FStar_SMTEncoding_Term.term ->
        (((Prims.string,FStar_SMTEncoding_Term.sort)
            FStar_Pervasives_Native.tuple2,Prims.string,FStar_Range.range)
           FStar_Pervasives_Native.tuple3,FStar_SMTEncoding_Term.term)
          FStar_Pervasives_Native.tuple2
  =
  let ctr = FStar_Util.mk_ref (Prims.parse_int "0") in
  fun message  ->
    fun range  ->
      fun t  ->
        let l =
          FStar_Util.incr ctr;
          (let uu____254 =
             let uu____255 = FStar_ST.read ctr in
             FStar_Util.string_of_int uu____255 in
           FStar_Util.format1 "label_%s" uu____254) in
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
          | (FStar_Pervasives_Native.None ,uu____332) -> false
          | (FStar_Pervasives_Native.Some nm,FStar_SMTEncoding_Term.FreeV
             (nm',uu____337)) -> nm = nm'
          | (uu____340,FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var "Valid",tm1::[])) ->
              is_a_post_condition post_name_opt tm1
          | (uu____348,FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var "ApplyTT",tm1::uu____350)) ->
              is_a_post_condition post_name_opt tm1
          | uu____359 -> false in
        let conjuncts t =
          match t.FStar_SMTEncoding_Term.tm with
          | FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And ,cs) -> cs
          | uu____379 -> [t] in
        let is_guard_free tm =
          match tm.FStar_SMTEncoding_Term.tm with
          | FStar_SMTEncoding_Term.Quant
              (FStar_SMTEncoding_Term.Forall
               ,({
                   FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App
                     (FStar_SMTEncoding_Term.Var "Prims.guard_free",p::[]);
                   FStar_SMTEncoding_Term.freevars = uu____385;
                   FStar_SMTEncoding_Term.rng = uu____386;_}::[])::[],iopt,uu____388,
               {
                 FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App
                   (FStar_SMTEncoding_Term.Iff ,l::r1::[]);
                 FStar_SMTEncoding_Term.freevars = uu____391;
                 FStar_SMTEncoding_Term.rng = uu____392;_})
              -> true
          | uu____429 -> false in
        let is_a_named_continuation lhs =
          FStar_All.pipe_right (conjuncts lhs)
            (FStar_Util.for_some is_guard_free) in
        let uu____436 =
          match use_env_msg with
          | FStar_Pervasives_Native.None  -> (false, "")
          | FStar_Pervasives_Native.Some f ->
              let uu____452 = f () in (true, uu____452) in
        match uu____436 with
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
                    let uu___105_484 = r1 in
                    {
                      FStar_Range.def_range = (rng.FStar_Range.def_range);
                      FStar_Range.use_range =
                        (uu___105_484.FStar_Range.use_range)
                    } in
              fresh_label msg1 rng1 t in
            let rec aux default_msg ropt post_name_opt labels q1 =
              match q1.FStar_SMTEncoding_Term.tm with
              | FStar_SMTEncoding_Term.BoundV uu____525 -> (labels, q1)
              | FStar_SMTEncoding_Term.Integer uu____528 -> (labels, q1)
              | FStar_SMTEncoding_Term.LblPos uu____531 ->
                  failwith "Impossible"
              | FStar_SMTEncoding_Term.Labeled
                  (arg,"could not prove post-condition",uu____543) ->
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
                                                     = uu____602;
                                                   FStar_SMTEncoding_Term.rng
                                                     = rng;_})
                         ->
                         let post_name =
                           let uu____631 =
                             let uu____632 = FStar_Syntax_Syntax.next_id () in
                             FStar_All.pipe_left FStar_Util.string_of_int
                               uu____632 in
                           Prims.strcat "^^post_condition_" uu____631 in
                         let names1 =
                           let uu____640 =
                             FStar_List.mapi
                               (fun i  ->
                                  fun s  ->
                                    let uu____656 =
                                      let uu____657 =
                                        FStar_Util.string_of_int i in
                                      Prims.strcat "^^" uu____657 in
                                    (uu____656, s)) sorts in
                           (post_name, post) :: uu____640 in
                         let instantiation =
                           FStar_List.map FStar_SMTEncoding_Util.mkFreeV
                             names1 in
                         let uu____669 =
                           let uu____674 =
                             FStar_SMTEncoding_Term.inst instantiation lhs in
                           let uu____675 =
                             FStar_SMTEncoding_Term.inst instantiation rhs in
                           (uu____674, uu____675) in
                         (match uu____669 with
                          | (lhs1,rhs1) ->
                              let uu____684 =
                                match lhs1.FStar_SMTEncoding_Term.tm with
                                | FStar_SMTEncoding_Term.App
                                    (FStar_SMTEncoding_Term.And ,clauses_lhs)
                                    ->
                                    let uu____702 =
                                      FStar_Util.prefix clauses_lhs in
                                    (match uu____702 with
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
                                                   = uu____732;
                                                 FStar_SMTEncoding_Term.rng =
                                                   rng_ens;_})
                                              when
                                              is_a_post_condition
                                                (FStar_Pervasives_Native.Some
                                                   post_name) post1
                                              ->
                                              let uu____760 =
                                                aux
                                                  "could not prove post-condition"
                                                  FStar_Pervasives_Native.None
                                                  (FStar_Pervasives_Native.Some
                                                     post_name) labels
                                                  ensures_conjuncts in
                                              (match uu____760 with
                                               | (labels1,ensures_conjuncts1)
                                                   ->
                                                   let pats_ens1 =
                                                     match pats_ens with
                                                     | [] -> [[post1]]
                                                     | []::[] -> [[post1]]
                                                     | uu____802 -> pats_ens in
                                                   let ens1 =
                                                     let uu____808 =
                                                       let uu____809 =
                                                         let uu____828 =
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
                                                           uu____828) in
                                                       FStar_SMTEncoding_Term.Quant
                                                         uu____809 in
                                                     FStar_SMTEncoding_Term.mk
                                                       uu____808
                                                       ens.FStar_SMTEncoding_Term.rng in
                                                   let lhs2 =
                                                     FStar_SMTEncoding_Term.mk
                                                       (FStar_SMTEncoding_Term.App
                                                          (FStar_SMTEncoding_Term.And,
                                                            (FStar_List.append
                                                               req [ens1])))
                                                       lhs1.FStar_SMTEncoding_Term.rng in
                                                   let uu____842 =
                                                     FStar_SMTEncoding_Term.abstr
                                                       names1 lhs2 in
                                                   (labels1, uu____842))
                                          | uu____845 ->
                                              let uu____846 =
                                                let uu____847 =
                                                  let uu____848 =
                                                    let uu____849 =
                                                      let uu____850 =
                                                        FStar_SMTEncoding_Term.print_smt_term
                                                          ens in
                                                      Prims.strcat "  ... "
                                                        uu____850 in
                                                    Prims.strcat post_name
                                                      uu____849 in
                                                  Prims.strcat
                                                    "Ensures clause doesn't match post name:  "
                                                    uu____848 in
                                                Not_a_wp_implication
                                                  uu____847 in
                                              raise uu____846))
                                | uu____857 ->
                                    let uu____858 =
                                      let uu____859 =
                                        let uu____860 =
                                          FStar_SMTEncoding_Term.print_smt_term
                                            lhs1 in
                                        Prims.strcat "LHS not a conjunct: "
                                          uu____860 in
                                      Not_a_wp_implication uu____859 in
                                    raise uu____858 in
                              (match uu____684 with
                               | (labels1,lhs2) ->
                                   let uu____879 =
                                     let uu____886 =
                                       aux default_msg
                                         FStar_Pervasives_Native.None
                                         (FStar_Pervasives_Native.Some
                                            post_name) labels1 rhs1 in
                                     match uu____886 with
                                     | (labels2,rhs2) ->
                                         let uu____905 =
                                           FStar_SMTEncoding_Term.abstr
                                             names1 rhs2 in
                                         (labels2, uu____905) in
                                   (match uu____879 with
                                    | (labels2,rhs2) ->
                                        let body =
                                          FStar_SMTEncoding_Term.mkImp
                                            (lhs2, rhs2) rng in
                                        let uu____921 =
                                          FStar_SMTEncoding_Term.mk
                                            (FStar_SMTEncoding_Term.Quant
                                               (FStar_SMTEncoding_Term.Forall,
                                                 pats, iopt, (post :: sorts),
                                                 body))
                                            q1.FStar_SMTEncoding_Term.rng in
                                        (labels2, uu____921))))
                     | uu____932 ->
                         let uu____933 =
                           let uu____934 =
                             FStar_SMTEncoding_Term.print_smt_term arg in
                           Prims.strcat "arg not a quant: " uu____934 in
                         fallback uu____933
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
                               FStar_SMTEncoding_Term.freevars = uu____951;
                               FStar_SMTEncoding_Term.rng = rng;_})
                  when is_a_named_continuation lhs ->
                  let post_name =
                    let uu____974 =
                      let uu____975 = FStar_Syntax_Syntax.next_id () in
                      FStar_All.pipe_left FStar_Util.string_of_int uu____975 in
                    Prims.strcat "^^post_condition_" uu____974 in
                  let names1 = (post_name, post) in
                  let instantiation =
                    let uu____984 = FStar_SMTEncoding_Util.mkFreeV names1 in
                    [uu____984] in
                  let uu____985 =
                    let uu____990 =
                      FStar_SMTEncoding_Term.inst instantiation lhs in
                    let uu____991 =
                      FStar_SMTEncoding_Term.inst instantiation rhs in
                    (uu____990, uu____991) in
                  (match uu____985 with
                   | (lhs1,rhs1) ->
                       let uu____1000 =
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
                                           uu____1037;
                                         FStar_SMTEncoding_Term.rng =
                                           uu____1038;_}::[])::[],iopt,sorts,
                                     {
                                       FStar_SMTEncoding_Term.tm =
                                         FStar_SMTEncoding_Term.App
                                         (FStar_SMTEncoding_Term.Iff
                                          ,l::r1::[]);
                                       FStar_SMTEncoding_Term.freevars =
                                         uu____1043;
                                       FStar_SMTEncoding_Term.rng =
                                         uu____1044;_})
                                    ->
                                    let uu____1081 =
                                      aux default_msg
                                        FStar_Pervasives_Native.None
                                        post_name_opt labels1 r1 in
                                    (match uu____1081 with
                                     | (labels2,r2) ->
                                         let uu____1100 =
                                           let uu____1101 =
                                             let uu____1102 =
                                               let uu____1121 =
                                                 FStar_SMTEncoding_Util.norng
                                                   FStar_SMTEncoding_Term.mk
                                                   (FStar_SMTEncoding_Term.App
                                                      (FStar_SMTEncoding_Term.Iff,
                                                        [l; r2])) in
                                               (FStar_SMTEncoding_Term.Forall,
                                                 [[p]],
                                                 (FStar_Pervasives_Native.Some
                                                    (Prims.parse_int "0")),
                                                 sorts, uu____1121) in
                                             FStar_SMTEncoding_Term.Quant
                                               uu____1102 in
                                           FStar_SMTEncoding_Term.mk
                                             uu____1101
                                             q1.FStar_SMTEncoding_Term.rng in
                                         (labels2, uu____1100))
                                | uu____1138 -> (labels1, tm)) labels
                           (conjuncts lhs1) in
                       (match uu____1000 with
                        | (labels1,lhs_conjs) ->
                            let uu____1157 =
                              aux default_msg FStar_Pervasives_Native.None
                                (FStar_Pervasives_Native.Some post_name)
                                labels1 rhs1 in
                            (match uu____1157 with
                             | (labels2,rhs2) ->
                                 let body =
                                   let uu____1177 =
                                     let uu____1178 =
                                       let uu____1183 =
                                         FStar_SMTEncoding_Term.mk_and_l
                                           lhs_conjs
                                           lhs1.FStar_SMTEncoding_Term.rng in
                                       (uu____1183, rhs2) in
                                     FStar_SMTEncoding_Term.mkImp uu____1178
                                       rng in
                                   FStar_All.pipe_right uu____1177
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
                  let uu____1209 =
                    aux default_msg ropt post_name_opt labels rhs in
                  (match uu____1209 with
                   | (labels1,rhs1) ->
                       let uu____1228 =
                         FStar_SMTEncoding_Util.mkImp (lhs, rhs1) in
                       (labels1, uu____1228))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.And ,conjuncts1) ->
                  let uu____1236 =
                    FStar_Util.fold_map (aux default_msg ropt post_name_opt)
                      labels conjuncts1 in
                  (match uu____1236 with
                   | (labels1,conjuncts2) ->
                       let uu____1263 =
                         FStar_SMTEncoding_Term.mk_and_l conjuncts2
                           q1.FStar_SMTEncoding_Term.rng in
                       (labels1, uu____1263))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.ITE ,hd1::q11::q2::[]) ->
                  let uu____1271 =
                    aux default_msg ropt post_name_opt labels q11 in
                  (match uu____1271 with
                   | (labels1,q12) ->
                       let uu____1290 =
                         aux default_msg ropt post_name_opt labels1 q2 in
                       (match uu____1290 with
                        | (labels2,q21) ->
                            let uu____1309 =
                              FStar_SMTEncoding_Term.mkITE (hd1, q12, q21)
                                q1.FStar_SMTEncoding_Term.rng in
                            (labels2, uu____1309)))
              | FStar_SMTEncoding_Term.Quant
                  (FStar_SMTEncoding_Term.Exists
                   ,uu____1312,uu____1313,uu____1314,uu____1315)
                  ->
                  let uu____1332 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____1332 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Iff ,uu____1347) ->
                  let uu____1352 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____1352 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Or ,uu____1367) ->
                  let uu____1372 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____1372 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Var uu____1387,uu____1388) when
                  is_a_post_condition post_name_opt q1 -> (labels, q1)
              | FStar_SMTEncoding_Term.FreeV uu____1395 ->
                  let uu____1400 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____1400 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.TrueOp ,uu____1415) ->
                  let uu____1420 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____1420 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.FalseOp ,uu____1435) ->
                  let uu____1440 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____1440 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Not ,uu____1455) ->
                  let uu____1460 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____1460 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Eq ,uu____1475) ->
                  let uu____1480 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____1480 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.LT ,uu____1495) ->
                  let uu____1500 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____1500 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.LTE ,uu____1515) ->
                  let uu____1520 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____1520 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.GT ,uu____1535) ->
                  let uu____1540 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____1540 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.GTE ,uu____1555) ->
                  let uu____1560 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____1560 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvUlt ,uu____1575) ->
                  let uu____1580 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____1580 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Var uu____1595,uu____1596) ->
                  let uu____1601 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____1601 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Add ,uu____1616) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Sub ,uu____1627) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Div ,uu____1638) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Mul ,uu____1649) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Minus ,uu____1660) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Mod ,uu____1671) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvAnd ,uu____1682) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvXor ,uu____1693) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvOr ,uu____1704) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvShl ,uu____1715) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvShr ,uu____1726) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvUdiv ,uu____1737) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvMod ,uu____1748) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvMul ,uu____1759) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvUext uu____1770,uu____1771) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvToNat ,uu____1782) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.NatToBv uu____1793,uu____1794) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.ITE ,uu____1805) ->
                  failwith "Impossible: arity mismatch"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Imp ,uu____1816) ->
                  failwith "Impossible: arity mismatch"
              | FStar_SMTEncoding_Term.Quant
                  (FStar_SMTEncoding_Term.Forall ,pats,iopt,sorts,body) ->
                  let uu____1847 =
                    aux default_msg ropt post_name_opt labels body in
                  (match uu____1847 with
                   | (labels1,body1) ->
                       let uu____1866 =
                         FStar_SMTEncoding_Term.mk
                           (FStar_SMTEncoding_Term.Quant
                              (FStar_SMTEncoding_Term.Forall, pats, iopt,
                                sorts, body1)) q1.FStar_SMTEncoding_Term.rng in
                       (labels1, uu____1866))
              | FStar_SMTEncoding_Term.Let (es,body) ->
                  let uu____1883 =
                    aux default_msg ropt post_name_opt labels body in
                  (match uu____1883 with
                   | (labels1,body1) ->
                       let uu____1902 =
                         FStar_SMTEncoding_Term.mkLet (es, body1)
                           q1.FStar_SMTEncoding_Term.rng in
                       (labels1, uu____1902)) in
            aux "assertion failed" FStar_Pervasives_Native.None
              FStar_Pervasives_Native.None [] q
let detail_errors:
  FStar_TypeChecker_Env.env ->
    labels ->
      (FStar_SMTEncoding_Term.decls_t ->
         ((FStar_SMTEncoding_Z3.unsat_core,(FStar_SMTEncoding_Term.error_labels,
                                             FStar_SMTEncoding_Z3.error_kind)
                                             FStar_Pervasives_Native.tuple2)
            FStar_Util.either,Prims.int,FStar_SMTEncoding_Z3.z3statistics)
           FStar_Pervasives_Native.tuple3)
        -> FStar_SMTEncoding_Term.error_label Prims.list
  =
  fun env  ->
    fun all_labels  ->
      fun askZ3  ->
        let print_banner uu____1955 =
          let uu____1956 =
            let uu____1957 = FStar_TypeChecker_Env.get_range env in
            FStar_Range.string_of_range uu____1957 in
          let uu____1958 = FStar_Util.string_of_int (Prims.parse_int "5") in
          let uu____1959 =
            FStar_Util.string_of_int (FStar_List.length all_labels) in
          FStar_Util.print3_error
            "Detailed error report follows for %s\nTaking %s seconds per proof obligation (%s proofs in total)\n"
            uu____1956 uu____1958 uu____1959 in
        let print_result uu____1973 =
          match uu____1973 with
          | ((uu____1984,msg,r),success) ->
              if success
              then
                let uu____1994 = FStar_Range.string_of_range r in
                FStar_Util.print1_error
                  "OK: proof obligation at %s was proven\n" uu____1994
              else FStar_Errors.err r msg in
        let elim labs =
          FStar_All.pipe_right labs
            (FStar_List.map
               (fun uu____2055  ->
                  match uu____2055 with
                  | (l,uu____2067,uu____2068) ->
                      let a =
                        let uu____2078 =
                          let uu____2079 =
                            let uu____2084 = FStar_SMTEncoding_Util.mkFreeV l in
                            (uu____2084, FStar_SMTEncoding_Util.mkTrue) in
                          FStar_SMTEncoding_Util.mkEq uu____2079 in
                        {
                          FStar_SMTEncoding_Term.assumption_term = uu____2078;
                          FStar_SMTEncoding_Term.assumption_caption =
                            (FStar_Pervasives_Native.Some "Disabling label");
                          FStar_SMTEncoding_Term.assumption_name =
                            (Prims.strcat "disable_label_"
                               (FStar_Pervasives_Native.fst l));
                          FStar_SMTEncoding_Term.assumption_fact_ids = []
                        } in
                      FStar_SMTEncoding_Term.Assume a)) in
        let rec linear_check eliminated errors active =
          match active with
          | [] ->
              let results =
                let uu____2138 =
                  FStar_List.map (fun x  -> (x, true)) eliminated in
                let uu____2151 = FStar_List.map (fun x  -> (x, false)) errors in
                FStar_List.append uu____2138 uu____2151 in
              sort_labels results
          | hd1::tl1 ->
              ((let uu____2173 =
                  FStar_Util.string_of_int (FStar_List.length active) in
                FStar_Util.print1 "%s, " uu____2173);
               FStar_SMTEncoding_Z3.refresh ();
               (let uu____2175 =
                  let uu____2190 =
                    FStar_All.pipe_left elim
                      (FStar_List.append eliminated
                         (FStar_List.append errors tl1)) in
                  askZ3 uu____2190 in
                match uu____2175 with
                | (result,uu____2218,uu____2219) ->
                    let uu____2236 = FStar_Util.is_left result in
                    if uu____2236
                    then linear_check (hd1 :: eliminated) errors tl1
                    else linear_check eliminated (hd1 :: errors) tl1)) in
        print_banner ();
        FStar_Options.set_option "z3rlimit"
          (FStar_Options.Int (Prims.parse_int "5"));
        (let res = linear_check [] [] all_labels in
         FStar_Util.print_string "\n";
         FStar_All.pipe_right res (FStar_List.iter print_result);
         [])