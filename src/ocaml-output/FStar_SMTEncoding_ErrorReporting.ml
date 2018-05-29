open Prims
exception Not_a_wp_implication of Prims.string 
let (uu___is_Not_a_wp_implication : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Not_a_wp_implication uu____10 -> true
    | uu____11 -> false
  
let (__proj__Not_a_wp_implication__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | Not_a_wp_implication uu____18 -> uu____18
  
type label = FStar_SMTEncoding_Term.error_label
type labels = FStar_SMTEncoding_Term.error_labels
let (sort_labels :
  (FStar_SMTEncoding_Term.error_label,Prims.bool)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    ((FStar_SMTEncoding_Term.fv,Prims.string,FStar_Range.range)
       FStar_Pervasives_Native.tuple3,Prims.bool)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun l  ->
    FStar_List.sortWith
      (fun uu____68  ->
         fun uu____69  ->
           match (uu____68, uu____69) with
           | (((uu____110,uu____111,r1),uu____113),((uu____114,uu____115,r2),uu____117))
               -> FStar_Range.compare r1 r2) l
  
let (remove_dups :
  labels ->
    (FStar_SMTEncoding_Term.fv,Prims.string,FStar_Range.range)
      FStar_Pervasives_Native.tuple3 Prims.list)
  =
  fun l  ->
    FStar_Util.remove_dups
      (fun uu____177  ->
         fun uu____178  ->
           match (uu____177, uu____178) with
           | ((uu____203,m1,r1),(uu____206,m2,r2)) -> (r1 = r2) && (m1 = m2))
      l
  
type msg = (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2
type ranges =
  (Prims.string FStar_Pervasives_Native.option,FStar_Range.range)
    FStar_Pervasives_Native.tuple2 Prims.list
let (fresh_label :
  Prims.string ->
    FStar_Range.range ->
      FStar_SMTEncoding_Term.term ->
        (label,FStar_SMTEncoding_Term.term) FStar_Pervasives_Native.tuple2)
  =
  let ctr = FStar_Util.mk_ref (Prims.parse_int "0")  in
  fun message  ->
    fun range  ->
      fun t  ->
        let l =
          FStar_Util.incr ctr;
          (let uu____290 =
             let uu____291 = FStar_ST.op_Bang ctr  in
             FStar_Util.string_of_int uu____291  in
           FStar_Util.format1 "label_%s" uu____290)
           in
        let lvar = (l, FStar_SMTEncoding_Term.Bool_sort)  in
        let label = (lvar, message, range)  in
        let lterm = FStar_SMTEncoding_Util.mkFreeV lvar  in
        let lt1 = FStar_SMTEncoding_Term.mkOr (lterm, t) range  in
        (label, lt1)
  
let (label_goals :
  (unit -> Prims.string) FStar_Pervasives_Native.option ->
    FStar_Range.range ->
      FStar_SMTEncoding_Term.term ->
        (labels,FStar_SMTEncoding_Term.term) FStar_Pervasives_Native.tuple2)
  =
  fun use_env_msg  ->
    fun r  ->
      fun q  ->
        let rec is_a_post_condition post_name_opt tm =
          match (post_name_opt, (tm.FStar_SMTEncoding_Term.tm)) with
          | (FStar_Pervasives_Native.None ,uu____400) -> false
          | (FStar_Pervasives_Native.Some nm,FStar_SMTEncoding_Term.FreeV
             (nm',uu____405)) -> nm = nm'
          | (uu____408,FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var "Valid",tm1::[])) ->
              is_a_post_condition post_name_opt tm1
          | (uu____416,FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var "ApplyTT",tm1::uu____418)) ->
              is_a_post_condition post_name_opt tm1
          | uu____427 -> false  in
        let conjuncts t =
          match t.FStar_SMTEncoding_Term.tm with
          | FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And ,cs) -> cs
          | uu____449 -> [t]  in
        let is_guard_free tm =
          match tm.FStar_SMTEncoding_Term.tm with
          | FStar_SMTEncoding_Term.Quant
              (FStar_SMTEncoding_Term.Forall
               ,({
                   FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App
                     (FStar_SMTEncoding_Term.Var "Prims.guard_free",p::[]);
                   FStar_SMTEncoding_Term.freevars = uu____457;
                   FStar_SMTEncoding_Term.rng = uu____458;_}::[])::[],iopt,uu____460,
               {
                 FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App
                   (FStar_SMTEncoding_Term.Imp ,l::r1::[]);
                 FStar_SMTEncoding_Term.freevars = uu____463;
                 FStar_SMTEncoding_Term.rng = uu____464;_})
              -> true
          | uu____501 -> false  in
        let is_a_named_continuation lhs =
          FStar_All.pipe_right (conjuncts lhs)
            (FStar_Util.for_some is_guard_free)
           in
        let uu____510 =
          match use_env_msg with
          | FStar_Pervasives_Native.None  -> (false, "")
          | FStar_Pervasives_Native.Some f ->
              let uu____529 = f ()  in (true, uu____529)
           in
        match uu____510 with
        | (flag,msg_prefix) ->
            let fresh_label1 msg ropt rng t =
              let msg1 =
                if flag
                then
                  Prims.strcat "Failed to verify implicit argument: "
                    (Prims.strcat msg_prefix (Prims.strcat " :: " msg))
                else msg  in
              let rng1 =
                match ropt with
                | FStar_Pervasives_Native.None  -> rng
                | FStar_Pervasives_Native.Some r1 ->
                    let uu____569 =
                      let uu____570 = FStar_Range.use_range rng  in
                      let uu____571 = FStar_Range.use_range r1  in
                      FStar_Range.rng_included uu____570 uu____571  in
                    if uu____569
                    then rng
                    else
                      (let uu____573 = FStar_Range.def_range rng  in
                       FStar_Range.set_def_range r1 uu____573)
                 in
              fresh_label msg1 rng1 t  in
            let rec aux default_msg ropt post_name_opt labels q1 =
              match q1.FStar_SMTEncoding_Term.tm with
              | FStar_SMTEncoding_Term.BoundV uu____624 -> (labels, q1)
              | FStar_SMTEncoding_Term.Integer uu____627 -> (labels, q1)
              | FStar_SMTEncoding_Term.LblPos uu____630 ->
                  failwith "Impossible"
              | FStar_SMTEncoding_Term.Labeled
                  (arg,"could not prove post-condition",uu____642) ->
                  let fallback msg =
                    aux default_msg ropt post_name_opt labels arg  in
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
                                                     = uu____703;
                                                   FStar_SMTEncoding_Term.rng
                                                     = rng;_})
                         ->
                         let post_name =
                           let uu____732 =
                             let uu____733 = FStar_Syntax_Syntax.next_id ()
                                in
                             FStar_All.pipe_left FStar_Util.string_of_int
                               uu____733
                              in
                           Prims.strcat "^^post_condition_" uu____732  in
                         let names1 =
                           let uu____741 =
                             FStar_List.mapi
                               (fun i  ->
                                  fun s  ->
                                    let uu____757 =
                                      let uu____758 =
                                        FStar_Util.string_of_int i  in
                                      Prims.strcat "^^" uu____758  in
                                    (uu____757, s)) sorts
                              in
                           (post_name, post) :: uu____741  in
                         let instantiation =
                           FStar_List.map FStar_SMTEncoding_Util.mkFreeV
                             names1
                            in
                         let uu____770 =
                           let uu____775 =
                             FStar_SMTEncoding_Term.inst instantiation lhs
                              in
                           let uu____776 =
                             FStar_SMTEncoding_Term.inst instantiation rhs
                              in
                           (uu____775, uu____776)  in
                         (match uu____770 with
                          | (lhs1,rhs1) ->
                              let uu____785 =
                                match lhs1.FStar_SMTEncoding_Term.tm with
                                | FStar_SMTEncoding_Term.App
                                    (FStar_SMTEncoding_Term.And ,clauses_lhs)
                                    ->
                                    let uu____803 =
                                      FStar_Util.prefix clauses_lhs  in
                                    (match uu____803 with
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
                                                   = uu____833;
                                                 FStar_SMTEncoding_Term.rng =
                                                   rng_ens;_})
                                              when
                                              is_a_post_condition
                                                (FStar_Pervasives_Native.Some
                                                   post_name) post1
                                              ->
                                              let uu____861 =
                                                aux
                                                  "could not prove post-condition"
                                                  FStar_Pervasives_Native.None
                                                  (FStar_Pervasives_Native.Some
                                                     post_name) labels
                                                  ensures_conjuncts
                                                 in
                                              (match uu____861 with
                                               | (labels1,ensures_conjuncts1)
                                                   ->
                                                   let pats_ens1 =
                                                     match pats_ens with
                                                     | [] -> [[post1]]
                                                     | []::[] -> [[post1]]
                                                     | uu____903 -> pats_ens
                                                      in
                                                   let ens1 =
                                                     let uu____909 =
                                                       let uu____910 =
                                                         let uu____929 =
                                                           FStar_SMTEncoding_Term.mk
                                                             (FStar_SMTEncoding_Term.App
                                                                (FStar_SMTEncoding_Term.Imp,
                                                                  [ensures_conjuncts1;
                                                                  post1]))
                                                             rng_ens
                                                            in
                                                         (FStar_SMTEncoding_Term.Forall,
                                                           pats_ens1,
                                                           iopt_ens,
                                                           sorts_ens,
                                                           uu____929)
                                                          in
                                                       FStar_SMTEncoding_Term.Quant
                                                         uu____910
                                                        in
                                                     FStar_SMTEncoding_Term.mk
                                                       uu____909
                                                       ens.FStar_SMTEncoding_Term.rng
                                                      in
                                                   let lhs2 =
                                                     FStar_SMTEncoding_Term.mk
                                                       (FStar_SMTEncoding_Term.App
                                                          (FStar_SMTEncoding_Term.And,
                                                            (FStar_List.append
                                                               req [ens1])))
                                                       lhs1.FStar_SMTEncoding_Term.rng
                                                      in
                                                   let uu____943 =
                                                     FStar_SMTEncoding_Term.abstr
                                                       names1 lhs2
                                                      in
                                                   (labels1, uu____943))
                                          | uu____946 ->
                                              let uu____947 =
                                                let uu____948 =
                                                  let uu____949 =
                                                    let uu____950 =
                                                      let uu____951 =
                                                        FStar_SMTEncoding_Term.print_smt_term
                                                          ens
                                                         in
                                                      Prims.strcat "  ... "
                                                        uu____951
                                                       in
                                                    Prims.strcat post_name
                                                      uu____950
                                                     in
                                                  Prims.strcat
                                                    "Ensures clause doesn't match post name:  "
                                                    uu____949
                                                   in
                                                Not_a_wp_implication
                                                  uu____948
                                                 in
                                              FStar_Exn.raise uu____947))
                                | uu____958 ->
                                    let uu____959 =
                                      let uu____960 =
                                        let uu____961 =
                                          FStar_SMTEncoding_Term.print_smt_term
                                            lhs1
                                           in
                                        Prims.strcat "LHS not a conjunct: "
                                          uu____961
                                         in
                                      Not_a_wp_implication uu____960  in
                                    FStar_Exn.raise uu____959
                                 in
                              (match uu____785 with
                               | (labels1,lhs2) ->
                                   let uu____980 =
                                     let uu____987 =
                                       aux default_msg
                                         FStar_Pervasives_Native.None
                                         (FStar_Pervasives_Native.Some
                                            post_name) labels1 rhs1
                                        in
                                     match uu____987 with
                                     | (labels2,rhs2) ->
                                         let uu____1006 =
                                           FStar_SMTEncoding_Term.abstr
                                             names1 rhs2
                                            in
                                         (labels2, uu____1006)
                                      in
                                   (match uu____980 with
                                    | (labels2,rhs2) ->
                                        let body =
                                          FStar_SMTEncoding_Term.mkImp
                                            (lhs2, rhs2) rng
                                           in
                                        let uu____1022 =
                                          FStar_SMTEncoding_Term.mk
                                            (FStar_SMTEncoding_Term.Quant
                                               (FStar_SMTEncoding_Term.Forall,
                                                 pats, iopt, (post :: sorts),
                                                 body))
                                            q1.FStar_SMTEncoding_Term.rng
                                           in
                                        (labels2, uu____1022))))
                     | uu____1033 ->
                         let uu____1034 =
                           let uu____1035 =
                             FStar_SMTEncoding_Term.print_smt_term arg  in
                           Prims.strcat "arg not a quant: " uu____1035  in
                         fallback uu____1034
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
                               FStar_SMTEncoding_Term.freevars = uu____1052;
                               FStar_SMTEncoding_Term.rng = rng;_})
                  when is_a_named_continuation lhs ->
                  let post_name =
                    let uu____1075 =
                      let uu____1076 = FStar_Syntax_Syntax.next_id ()  in
                      FStar_All.pipe_left FStar_Util.string_of_int uu____1076
                       in
                    Prims.strcat "^^post_condition_" uu____1075  in
                  let names1 = (post_name, post)  in
                  let instantiation =
                    let uu____1085 = FStar_SMTEncoding_Util.mkFreeV names1
                       in
                    [uu____1085]  in
                  let uu____1086 =
                    let uu____1091 =
                      FStar_SMTEncoding_Term.inst instantiation lhs  in
                    let uu____1092 =
                      FStar_SMTEncoding_Term.inst instantiation rhs  in
                    (uu____1091, uu____1092)  in
                  (match uu____1086 with
                   | (lhs1,rhs1) ->
                       let uu____1101 =
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
                                           uu____1138;
                                         FStar_SMTEncoding_Term.rng =
                                           uu____1139;_}::[])::[],iopt,sorts,
                                     {
                                       FStar_SMTEncoding_Term.tm =
                                         FStar_SMTEncoding_Term.App
                                         (FStar_SMTEncoding_Term.Imp
                                          ,l::r1::[]);
                                       FStar_SMTEncoding_Term.freevars =
                                         uu____1144;
                                       FStar_SMTEncoding_Term.rng =
                                         uu____1145;_})
                                    ->
                                    let uu____1182 =
                                      aux default_msg
                                        FStar_Pervasives_Native.None
                                        post_name_opt labels1 r1
                                       in
                                    (match uu____1182 with
                                     | (labels2,r2) ->
                                         let uu____1201 =
                                           let uu____1202 =
                                             let uu____1203 =
                                               let uu____1222 =
                                                 FStar_SMTEncoding_Util.norng
                                                   FStar_SMTEncoding_Term.mk
                                                   (FStar_SMTEncoding_Term.App
                                                      (FStar_SMTEncoding_Term.Imp,
                                                        [l; r2]))
                                                  in
                                               (FStar_SMTEncoding_Term.Forall,
                                                 [[p]],
                                                 (FStar_Pervasives_Native.Some
                                                    (Prims.parse_int "0")),
                                                 sorts, uu____1222)
                                                in
                                             FStar_SMTEncoding_Term.Quant
                                               uu____1203
                                              in
                                           FStar_SMTEncoding_Term.mk
                                             uu____1202
                                             q1.FStar_SMTEncoding_Term.rng
                                            in
                                         (labels2, uu____1201))
                                | uu____1239 -> (labels1, tm)) labels
                           (conjuncts lhs1)
                          in
                       (match uu____1101 with
                        | (labels1,lhs_conjs) ->
                            let uu____1258 =
                              aux default_msg FStar_Pervasives_Native.None
                                (FStar_Pervasives_Native.Some post_name)
                                labels1 rhs1
                               in
                            (match uu____1258 with
                             | (labels2,rhs2) ->
                                 let body =
                                   let uu____1278 =
                                     let uu____1279 =
                                       let uu____1284 =
                                         FStar_SMTEncoding_Term.mk_and_l
                                           lhs_conjs
                                           lhs1.FStar_SMTEncoding_Term.rng
                                          in
                                       (uu____1284, rhs2)  in
                                     FStar_SMTEncoding_Term.mkImp uu____1279
                                       rng
                                      in
                                   FStar_All.pipe_right uu____1278
                                     (FStar_SMTEncoding_Term.abstr [names1])
                                    in
                                 let q2 =
                                   FStar_SMTEncoding_Term.mk
                                     (FStar_SMTEncoding_Term.Quant
                                        (FStar_SMTEncoding_Term.Forall, [],
                                          FStar_Pervasives_Native.None,
                                          [post], body))
                                     q1.FStar_SMTEncoding_Term.rng
                                    in
                                 (labels2, q2))))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Imp ,lhs::rhs::[]) ->
                  let uu____1302 =
                    aux default_msg ropt post_name_opt labels rhs  in
                  (match uu____1302 with
                   | (labels1,rhs1) ->
                       let uu____1321 =
                         FStar_SMTEncoding_Util.mkImp (lhs, rhs1)  in
                       (labels1, uu____1321))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.And ,conjuncts1) ->
                  let uu____1329 =
                    FStar_Util.fold_map (aux default_msg ropt post_name_opt)
                      labels conjuncts1
                     in
                  (match uu____1329 with
                   | (labels1,conjuncts2) ->
                       let uu____1356 =
                         FStar_SMTEncoding_Term.mk_and_l conjuncts2
                           q1.FStar_SMTEncoding_Term.rng
                          in
                       (labels1, uu____1356))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.ITE ,hd1::q11::q2::[]) ->
                  let uu____1364 =
                    aux default_msg ropt post_name_opt labels q11  in
                  (match uu____1364 with
                   | (labels1,q12) ->
                       let uu____1383 =
                         aux default_msg ropt post_name_opt labels1 q2  in
                       (match uu____1383 with
                        | (labels2,q21) ->
                            let uu____1402 =
                              FStar_SMTEncoding_Term.mkITE (hd1, q12, q21)
                                q1.FStar_SMTEncoding_Term.rng
                               in
                            (labels2, uu____1402)))
              | FStar_SMTEncoding_Term.Quant
                  (FStar_SMTEncoding_Term.Exists
                   ,uu____1405,uu____1406,uu____1407,uu____1408)
                  ->
                  let uu____1425 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____1425 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Iff ,uu____1440) ->
                  let uu____1445 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____1445 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Or ,uu____1460) ->
                  let uu____1465 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____1465 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Var uu____1480,uu____1481) when
                  is_a_post_condition post_name_opt q1 -> (labels, q1)
              | FStar_SMTEncoding_Term.FreeV uu____1488 ->
                  let uu____1493 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____1493 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.TrueOp ,uu____1508) ->
                  let uu____1513 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____1513 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.FalseOp ,uu____1528) ->
                  let uu____1533 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____1533 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Not ,uu____1548) ->
                  let uu____1553 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____1553 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Eq ,uu____1568) ->
                  let uu____1573 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____1573 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.LT ,uu____1588) ->
                  let uu____1593 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____1593 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.LTE ,uu____1608) ->
                  let uu____1613 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____1613 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.GT ,uu____1628) ->
                  let uu____1633 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____1633 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.GTE ,uu____1648) ->
                  let uu____1653 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____1653 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvUlt ,uu____1668) ->
                  let uu____1673 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____1673 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Var uu____1688,uu____1689) ->
                  let uu____1694 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____1694 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Add ,uu____1709) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Sub ,uu____1720) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Div ,uu____1731) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Mul ,uu____1742) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Minus ,uu____1753) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Mod ,uu____1764) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvAnd ,uu____1775) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvXor ,uu____1786) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvOr ,uu____1797) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvAdd ,uu____1808) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvSub ,uu____1819) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvShl ,uu____1830) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvShr ,uu____1841) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvUdiv ,uu____1852) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvMod ,uu____1863) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvMul ,uu____1874) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvUext uu____1885,uu____1886) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvToNat ,uu____1897) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.NatToBv uu____1908,uu____1909) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.ITE ,uu____1920) ->
                  failwith "Impossible: arity mismatch"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Imp ,uu____1931) ->
                  failwith "Impossible: arity mismatch"
              | FStar_SMTEncoding_Term.Quant
                  (FStar_SMTEncoding_Term.Forall ,pats,iopt,sorts,body) ->
                  let uu____1962 =
                    aux default_msg ropt post_name_opt labels body  in
                  (match uu____1962 with
                   | (labels1,body1) ->
                       let uu____1981 =
                         FStar_SMTEncoding_Term.mk
                           (FStar_SMTEncoding_Term.Quant
                              (FStar_SMTEncoding_Term.Forall, pats, iopt,
                                sorts, body1)) q1.FStar_SMTEncoding_Term.rng
                          in
                       (labels1, uu____1981))
              | FStar_SMTEncoding_Term.Let (es,body) ->
                  let uu____1998 =
                    aux default_msg ropt post_name_opt labels body  in
                  (match uu____1998 with
                   | (labels1,body1) ->
                       let uu____2017 =
                         FStar_SMTEncoding_Term.mkLet (es, body1)
                           q1.FStar_SMTEncoding_Term.rng
                          in
                       (labels1, uu____2017))
               in
            aux "assertion failed" FStar_Pervasives_Native.None
              FStar_Pervasives_Native.None [] q
  
let (detail_errors :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      labels ->
        (FStar_SMTEncoding_Term.decls_t -> FStar_SMTEncoding_Z3.z3result) ->
          unit)
  =
  fun hint_replay  ->
    fun env  ->
      fun all_labels  ->
        fun askZ3  ->
          let print_banner uu____2052 =
            let msg =
              let uu____2054 =
                let uu____2055 = FStar_TypeChecker_Env.get_range env  in
                FStar_Range.string_of_range uu____2055  in
              let uu____2056 = FStar_Util.string_of_int (Prims.parse_int "5")
                 in
              let uu____2057 =
                FStar_Util.string_of_int (FStar_List.length all_labels)  in
              FStar_Util.format4
                "Detailed %s report follows for %s\nTaking %s seconds per proof obligation (%s proofs in total)\n"
                (if hint_replay then "hint replay" else "error") uu____2054
                uu____2056 uu____2057
               in
            FStar_Util.print_error msg  in
          let print_result uu____2074 =
            match uu____2074 with
            | ((uu____2085,msg,r),success) ->
                if success
                then
                  let uu____2095 = FStar_Range.string_of_range r  in
                  FStar_Util.print1
                    "OK: proof obligation at %s was proven in isolation\n"
                    uu____2095
                else
                  if hint_replay
                  then
                    FStar_Errors.log_issue r
                      (FStar_Errors.Warning_HintFailedToReplayProof,
                        (Prims.strcat
                           "Hint failed to replay this sub-proof: " msg))
                  else
                    (let uu____2098 =
                       let uu____2103 =
                         let uu____2104 = FStar_Range.string_of_range r  in
                         FStar_Util.format2
                           "XX: proof obligation at %s failed\n\t%s\n"
                           uu____2104 msg
                          in
                       (FStar_Errors.Error_ProofObligationFailed, uu____2103)
                        in
                     FStar_Errors.log_issue r uu____2098)
             in
          let elim labs =
            FStar_All.pipe_right labs
              (FStar_List.map
                 (fun uu____2166  ->
                    match uu____2166 with
                    | (l,uu____2178,uu____2179) ->
                        let a =
                          let uu____2189 =
                            let uu____2190 =
                              let uu____2195 =
                                FStar_SMTEncoding_Util.mkFreeV l  in
                              (uu____2195, FStar_SMTEncoding_Util.mkTrue)  in
                            FStar_SMTEncoding_Util.mkEq uu____2190  in
                          {
                            FStar_SMTEncoding_Term.assumption_term =
                              uu____2189;
                            FStar_SMTEncoding_Term.assumption_caption =
                              (FStar_Pervasives_Native.Some "Disabling label");
                            FStar_SMTEncoding_Term.assumption_name =
                              (Prims.strcat "@disable_label_"
                                 (FStar_Pervasives_Native.fst l));
                            FStar_SMTEncoding_Term.assumption_fact_ids = []
                          }  in
                        FStar_SMTEncoding_Term.Assume a))
             in
          let rec linear_check eliminated errors active =
            FStar_SMTEncoding_Z3.refresh ();
            (match active with
             | [] ->
                 let results =
                   let uu____2256 =
                     FStar_List.map (fun x  -> (x, true)) eliminated  in
                   let uu____2269 =
                     FStar_List.map (fun x  -> (x, false)) errors  in
                   FStar_List.append uu____2256 uu____2269  in
                 sort_labels results
             | hd1::tl1 ->
                 ((let uu____2291 =
                     FStar_Util.string_of_int (FStar_List.length active)  in
                   FStar_Util.print1 "%s, " uu____2291);
                  (let decls =
                     FStar_All.pipe_left elim
                       (FStar_List.append eliminated
                          (FStar_List.append errors tl1))
                      in
                   let result = askZ3 decls  in
                   match result.FStar_SMTEncoding_Z3.z3result_status with
                   | FStar_SMTEncoding_Z3.UNSAT uu____2318 ->
                       linear_check (hd1 :: eliminated) errors tl1
                   | uu____2319 ->
                       linear_check eliminated (hd1 :: errors) tl1)))
             in
          print_banner ();
          FStar_Options.set_option "z3rlimit"
            (FStar_Options.Int (Prims.parse_int "5"));
          (let res = linear_check [] [] all_labels  in
           FStar_Util.print_string "\n";
           FStar_All.pipe_right res (FStar_List.iter print_result);
           (let uu____2359 =
              FStar_Util.for_all FStar_Pervasives_Native.snd res  in
            if uu____2359
            then
              FStar_Util.print_string
                "Failed: the heuristic of trying each proof in isolation failed to identify a precise error\n"
            else ()))
  