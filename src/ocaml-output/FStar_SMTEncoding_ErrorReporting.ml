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
          | (FStar_Pervasives_Native.None ,uu____396) -> false
          | (FStar_Pervasives_Native.Some nm,FStar_SMTEncoding_Term.FreeV
             (nm',uu____401)) -> nm = nm'
          | (uu____404,FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var "Valid",tm1::[])) ->
              is_a_post_condition post_name_opt tm1
          | (uu____412,FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var "ApplyTT",tm1::uu____414)) ->
              is_a_post_condition post_name_opt tm1
          | uu____423 -> false  in
        let conjuncts t =
          match t.FStar_SMTEncoding_Term.tm with
          | FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And ,cs) -> cs
          | uu____445 -> [t]  in
        let is_guard_free tm =
          match tm.FStar_SMTEncoding_Term.tm with
          | FStar_SMTEncoding_Term.Quant
              (FStar_SMTEncoding_Term.Forall
               ,({
                   FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App
                     (FStar_SMTEncoding_Term.Var "Prims.guard_free",p::[]);
                   FStar_SMTEncoding_Term.freevars = uu____453;
                   FStar_SMTEncoding_Term.rng = uu____454;_}::[])::[],iopt,uu____456,
               {
                 FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App
                   (FStar_SMTEncoding_Term.Imp ,l::r1::[]);
                 FStar_SMTEncoding_Term.freevars = uu____459;
                 FStar_SMTEncoding_Term.rng = uu____460;_})
              -> true
          | uu____497 -> false  in
        let is_a_named_continuation lhs =
          FStar_All.pipe_right (conjuncts lhs)
            (FStar_Util.for_some is_guard_free)
           in
        let uu____506 =
          match use_env_msg with
          | FStar_Pervasives_Native.None  -> (false, "")
          | FStar_Pervasives_Native.Some f ->
              let uu____525 = f ()  in (true, uu____525)
           in
        match uu____506 with
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
                    let uu____565 =
                      let uu____566 = FStar_Range.use_range rng  in
                      let uu____567 = FStar_Range.use_range r1  in
                      FStar_Range.rng_included uu____566 uu____567  in
                    if uu____565
                    then rng
                    else
                      (let uu____569 = FStar_Range.def_range rng  in
                       FStar_Range.set_def_range r1 uu____569)
                 in
              fresh_label msg1 rng1 t  in
            let rec aux default_msg ropt post_name_opt labels q1 =
              match q1.FStar_SMTEncoding_Term.tm with
              | FStar_SMTEncoding_Term.BoundV uu____620 -> (labels, q1)
              | FStar_SMTEncoding_Term.Integer uu____623 -> (labels, q1)
              | FStar_SMTEncoding_Term.LblPos uu____626 ->
                  failwith "Impossible"
              | FStar_SMTEncoding_Term.Labeled
                  (arg,"could not prove post-condition",uu____638) ->
                  let fallback msg =
                    aux default_msg ropt post_name_opt labels arg  in
                  (try
                     (fun uu___265_680  ->
                        match () with
                        | () ->
                            (match arg.FStar_SMTEncoding_Term.tm with
                             | FStar_SMTEncoding_Term.Quant
                                 (FStar_SMTEncoding_Term.Forall
                                  ,pats,iopt,post::sorts,{
                                                           FStar_SMTEncoding_Term.tm
                                                             =
                                                             FStar_SMTEncoding_Term.App
                                                             (FStar_SMTEncoding_Term.Imp
                                                              ,lhs::rhs::[]);
                                                           FStar_SMTEncoding_Term.freevars
                                                             = uu____699;
                                                           FStar_SMTEncoding_Term.rng
                                                             = rng;_})
                                 ->
                                 let post_name =
                                   let uu____728 =
                                     let uu____729 =
                                       FStar_Syntax_Syntax.next_id ()  in
                                     FStar_All.pipe_left
                                       FStar_Util.string_of_int uu____729
                                      in
                                   Prims.strcat "^^post_condition_" uu____728
                                    in
                                 let names1 =
                                   let uu____737 =
                                     FStar_List.map
                                       (fun s  ->
                                          let uu____751 =
                                            let uu____752 =
                                              let uu____753 =
                                                FStar_Syntax_Syntax.next_id
                                                  ()
                                                 in
                                              FStar_All.pipe_left
                                                FStar_Util.string_of_int
                                                uu____753
                                               in
                                            Prims.strcat "^^" uu____752  in
                                          (uu____751, s)) sorts
                                      in
                                   (post_name, post) :: uu____737  in
                                 let instantiation =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV names1
                                    in
                                 let uu____765 =
                                   let uu____770 =
                                     FStar_SMTEncoding_Term.inst
                                       instantiation lhs
                                      in
                                   let uu____771 =
                                     FStar_SMTEncoding_Term.inst
                                       instantiation rhs
                                      in
                                   (uu____770, uu____771)  in
                                 (match uu____765 with
                                  | (lhs1,rhs1) ->
                                      let uu____780 =
                                        match lhs1.FStar_SMTEncoding_Term.tm
                                        with
                                        | FStar_SMTEncoding_Term.App
                                            (FStar_SMTEncoding_Term.And
                                             ,clauses_lhs)
                                            ->
                                            let uu____798 =
                                              FStar_Util.prefix clauses_lhs
                                               in
                                            (match uu____798 with
                                             | (req,ens) ->
                                                 (match ens.FStar_SMTEncoding_Term.tm
                                                  with
                                                  | FStar_SMTEncoding_Term.Quant
                                                      (FStar_SMTEncoding_Term.Forall
                                                       ,pats_ens,iopt_ens,sorts_ens,
                                                       {
                                                         FStar_SMTEncoding_Term.tm
                                                           =
                                                           FStar_SMTEncoding_Term.App
                                                           (FStar_SMTEncoding_Term.Imp
                                                            ,ensures_conjuncts::post1::[]);
                                                         FStar_SMTEncoding_Term.freevars
                                                           = uu____828;
                                                         FStar_SMTEncoding_Term.rng
                                                           = rng_ens;_})
                                                      ->
                                                      let uu____856 =
                                                        is_a_post_condition
                                                          (FStar_Pervasives_Native.Some
                                                             post_name) post1
                                                         in
                                                      if uu____856
                                                      then
                                                        let uu____863 =
                                                          aux
                                                            "could not prove post-condition"
                                                            FStar_Pervasives_Native.None
                                                            (FStar_Pervasives_Native.Some
                                                               post_name)
                                                            labels
                                                            ensures_conjuncts
                                                           in
                                                        (match uu____863 with
                                                         | (labels1,ensures_conjuncts1)
                                                             ->
                                                             let pats_ens1 =
                                                               match pats_ens
                                                               with
                                                               | [] ->
                                                                   [[post1]]
                                                               | []::[] ->
                                                                   [[post1]]
                                                               | uu____905 ->
                                                                   pats_ens
                                                                in
                                                             let ens1 =
                                                               let uu____911
                                                                 =
                                                                 let uu____912
                                                                   =
                                                                   let uu____931
                                                                    =
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
                                                                    uu____931)
                                                                    in
                                                                 FStar_SMTEncoding_Term.Quant
                                                                   uu____912
                                                                  in
                                                               FStar_SMTEncoding_Term.mk
                                                                 uu____911
                                                                 ens.FStar_SMTEncoding_Term.rng
                                                                in
                                                             let lhs2 =
                                                               FStar_SMTEncoding_Term.mk
                                                                 (FStar_SMTEncoding_Term.App
                                                                    (FStar_SMTEncoding_Term.And,
                                                                    (FStar_List.append
                                                                    req
                                                                    [ens1])))
                                                                 lhs1.FStar_SMTEncoding_Term.rng
                                                                in
                                                             let uu____945 =
                                                               FStar_SMTEncoding_Term.abstr
                                                                 names1 lhs2
                                                                in
                                                             (labels1,
                                                               uu____945))
                                                      else
                                                        (let uu____949 =
                                                           let uu____950 =
                                                             let uu____951 =
                                                               let uu____952
                                                                 =
                                                                 let uu____953
                                                                   =
                                                                   FStar_SMTEncoding_Term.print_smt_term
                                                                    post1
                                                                    in
                                                                 Prims.strcat
                                                                   "  ... "
                                                                   uu____953
                                                                  in
                                                               Prims.strcat
                                                                 post_name
                                                                 uu____952
                                                                in
                                                             Prims.strcat
                                                               "Ensures clause doesn't match post name:  "
                                                               uu____951
                                                              in
                                                           Not_a_wp_implication
                                                             uu____950
                                                            in
                                                         FStar_Exn.raise
                                                           uu____949)
                                                  | uu____960 ->
                                                      let uu____961 =
                                                        let uu____962 =
                                                          let uu____963 =
                                                            let uu____964 =
                                                              let uu____965 =
                                                                FStar_SMTEncoding_Term.print_smt_term
                                                                  ens
                                                                 in
                                                              Prims.strcat
                                                                "  ... "
                                                                uu____965
                                                               in
                                                            Prims.strcat
                                                              post_name
                                                              uu____964
                                                             in
                                                          Prims.strcat
                                                            "Ensures clause doesn't have the expected shape for post-condition "
                                                            uu____963
                                                           in
                                                        Not_a_wp_implication
                                                          uu____962
                                                         in
                                                      FStar_Exn.raise
                                                        uu____961))
                                        | uu____972 ->
                                            let uu____973 =
                                              let uu____974 =
                                                let uu____975 =
                                                  FStar_SMTEncoding_Term.print_smt_term
                                                    lhs1
                                                   in
                                                Prims.strcat
                                                  "LHS not a conjunct: "
                                                  uu____975
                                                 in
                                              Not_a_wp_implication uu____974
                                               in
                                            FStar_Exn.raise uu____973
                                         in
                                      (match uu____780 with
                                       | (labels1,lhs2) ->
                                           let uu____994 =
                                             let uu____1001 =
                                               aux default_msg
                                                 FStar_Pervasives_Native.None
                                                 (FStar_Pervasives_Native.Some
                                                    post_name) labels1 rhs1
                                                in
                                             match uu____1001 with
                                             | (labels2,rhs2) ->
                                                 let uu____1020 =
                                                   FStar_SMTEncoding_Term.abstr
                                                     names1 rhs2
                                                    in
                                                 (labels2, uu____1020)
                                              in
                                           (match uu____994 with
                                            | (labels2,rhs2) ->
                                                let body =
                                                  FStar_SMTEncoding_Term.mkImp
                                                    (lhs2, rhs2) rng
                                                   in
                                                let uu____1036 =
                                                  FStar_SMTEncoding_Term.mk
                                                    (FStar_SMTEncoding_Term.Quant
                                                       (FStar_SMTEncoding_Term.Forall,
                                                         pats, iopt, (post ::
                                                         sorts), body))
                                                    q1.FStar_SMTEncoding_Term.rng
                                                   in
                                                (labels2, uu____1036))))
                             | uu____1047 ->
                                 let uu____1048 =
                                   let uu____1049 =
                                     FStar_SMTEncoding_Term.print_smt_term
                                       arg
                                      in
                                   Prims.strcat "arg not a quant: "
                                     uu____1049
                                    in
                                 fallback uu____1048)) ()
                   with | Not_a_wp_implication msg -> fallback msg)
              | FStar_SMTEncoding_Term.Labeled (arg,reason,r1) ->
                  aux reason (FStar_Pervasives_Native.Some r1) post_name_opt
                    labels arg
              | FStar_SMTEncoding_Term.Quant
                  (FStar_SMTEncoding_Term.Forall
                   ,[],FStar_Pervasives_Native.None
                   ,sorts,{
                            FStar_SMTEncoding_Term.tm =
                              FStar_SMTEncoding_Term.App
                              (FStar_SMTEncoding_Term.Imp ,lhs::rhs::[]);
                            FStar_SMTEncoding_Term.freevars = uu____1066;
                            FStar_SMTEncoding_Term.rng = rng;_})
                  when is_a_named_continuation lhs ->
                  let uu____1090 = FStar_Util.prefix sorts  in
                  (match uu____1090 with
                   | (sorts',post) ->
                       let new_post_name =
                         let uu____1110 =
                           let uu____1111 = FStar_Syntax_Syntax.next_id ()
                              in
                           FStar_All.pipe_left FStar_Util.string_of_int
                             uu____1111
                            in
                         Prims.strcat "^^post_condition_" uu____1110  in
                       let names1 =
                         let uu____1119 =
                           FStar_List.map
                             (fun s  ->
                                let uu____1133 =
                                  let uu____1134 =
                                    let uu____1135 =
                                      FStar_Syntax_Syntax.next_id ()  in
                                    FStar_All.pipe_left
                                      FStar_Util.string_of_int uu____1135
                                     in
                                  Prims.strcat "^^" uu____1134  in
                                (uu____1133, s)) sorts'
                            in
                         FStar_List.append uu____1119 [(new_post_name, post)]
                          in
                       let instantiation =
                         FStar_List.map FStar_SMTEncoding_Util.mkFreeV names1
                          in
                       let uu____1155 =
                         let uu____1160 =
                           FStar_SMTEncoding_Term.inst instantiation lhs  in
                         let uu____1161 =
                           FStar_SMTEncoding_Term.inst instantiation rhs  in
                         (uu____1160, uu____1161)  in
                       (match uu____1155 with
                        | (lhs1,rhs1) ->
                            let uu____1170 =
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
                                              FStar_SMTEncoding_Term.freevars
                                                = uu____1208;
                                              FStar_SMTEncoding_Term.rng =
                                                uu____1209;_}::[])::[],iopt,sorts1,
                                          {
                                            FStar_SMTEncoding_Term.tm =
                                              FStar_SMTEncoding_Term.App
                                              (FStar_SMTEncoding_Term.Imp
                                               ,l0::r1::[]);
                                            FStar_SMTEncoding_Term.freevars =
                                              uu____1214;
                                            FStar_SMTEncoding_Term.rng =
                                              uu____1215;_})
                                         ->
                                         let uu____1252 =
                                           is_a_post_condition
                                             (FStar_Pervasives_Native.Some
                                                new_post_name) r1
                                            in
                                         if uu____1252
                                         then
                                           let uu____1259 =
                                             aux default_msg
                                               FStar_Pervasives_Native.None
                                               post_name_opt labels1 l0
                                              in
                                           (match uu____1259 with
                                            | (labels2,l) ->
                                                let uu____1278 =
                                                  let uu____1279 =
                                                    let uu____1280 =
                                                      let uu____1299 =
                                                        FStar_SMTEncoding_Util.norng
                                                          FStar_SMTEncoding_Term.mk
                                                          (FStar_SMTEncoding_Term.App
                                                             (FStar_SMTEncoding_Term.Imp,
                                                               [l; r1]))
                                                         in
                                                      (FStar_SMTEncoding_Term.Forall,
                                                        [[p]],
                                                        (FStar_Pervasives_Native.Some
                                                           (Prims.parse_int "0")),
                                                        sorts1, uu____1299)
                                                       in
                                                    FStar_SMTEncoding_Term.Quant
                                                      uu____1280
                                                     in
                                                  FStar_SMTEncoding_Term.mk
                                                    uu____1279
                                                    q1.FStar_SMTEncoding_Term.rng
                                                   in
                                                (labels2, uu____1278))
                                         else (labels1, tm)
                                     | uu____1319 -> (labels1, tm)) labels
                                (conjuncts lhs1)
                               in
                            (match uu____1170 with
                             | (labels1,lhs_conjs) ->
                                 let uu____1338 =
                                   aux default_msg
                                     FStar_Pervasives_Native.None
                                     (FStar_Pervasives_Native.Some
                                        new_post_name) labels1 rhs1
                                    in
                                 (match uu____1338 with
                                  | (labels2,rhs2) ->
                                      let body =
                                        let uu____1358 =
                                          let uu____1359 =
                                            let uu____1364 =
                                              FStar_SMTEncoding_Term.mk_and_l
                                                lhs_conjs
                                                lhs1.FStar_SMTEncoding_Term.rng
                                               in
                                            (uu____1364, rhs2)  in
                                          FStar_SMTEncoding_Term.mkImp
                                            uu____1359 rng
                                           in
                                        FStar_All.pipe_right uu____1358
                                          (FStar_SMTEncoding_Term.abstr
                                             names1)
                                         in
                                      let q2 =
                                        FStar_SMTEncoding_Term.mk
                                          (FStar_SMTEncoding_Term.Quant
                                             (FStar_SMTEncoding_Term.Forall,
                                               [],
                                               FStar_Pervasives_Native.None,
                                               sorts, body))
                                          q1.FStar_SMTEncoding_Term.rng
                                         in
                                      (labels2, q2)))))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Imp ,lhs::rhs::[]) ->
                  let uu____1382 =
                    aux default_msg ropt post_name_opt labels rhs  in
                  (match uu____1382 with
                   | (labels1,rhs1) ->
                       let uu____1401 =
                         FStar_SMTEncoding_Util.mkImp (lhs, rhs1)  in
                       (labels1, uu____1401))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.And ,conjuncts1) ->
                  let uu____1409 =
                    FStar_Util.fold_map (aux default_msg ropt post_name_opt)
                      labels conjuncts1
                     in
                  (match uu____1409 with
                   | (labels1,conjuncts2) ->
                       let uu____1436 =
                         FStar_SMTEncoding_Term.mk_and_l conjuncts2
                           q1.FStar_SMTEncoding_Term.rng
                          in
                       (labels1, uu____1436))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.ITE ,hd1::q11::q2::[]) ->
                  let uu____1444 =
                    aux default_msg ropt post_name_opt labels q11  in
                  (match uu____1444 with
                   | (labels1,q12) ->
                       let uu____1463 =
                         aux default_msg ropt post_name_opt labels1 q2  in
                       (match uu____1463 with
                        | (labels2,q21) ->
                            let uu____1482 =
                              FStar_SMTEncoding_Term.mkITE (hd1, q12, q21)
                                q1.FStar_SMTEncoding_Term.rng
                               in
                            (labels2, uu____1482)))
              | FStar_SMTEncoding_Term.Quant
                  (FStar_SMTEncoding_Term.Exists
                   ,uu____1485,uu____1486,uu____1487,uu____1488)
                  ->
                  let uu____1505 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____1505 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Iff ,uu____1520) ->
                  let uu____1525 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____1525 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Or ,uu____1540) ->
                  let uu____1545 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____1545 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Var uu____1560,uu____1561) when
                  is_a_post_condition post_name_opt q1 -> (labels, q1)
              | FStar_SMTEncoding_Term.FreeV uu____1568 ->
                  let uu____1573 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____1573 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.TrueOp ,uu____1588) ->
                  let uu____1593 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____1593 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.FalseOp ,uu____1608) ->
                  let uu____1613 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____1613 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Not ,uu____1628) ->
                  let uu____1633 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____1633 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Eq ,uu____1648) ->
                  let uu____1653 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____1653 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.LT ,uu____1668) ->
                  let uu____1673 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____1673 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.LTE ,uu____1688) ->
                  let uu____1693 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____1693 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.GT ,uu____1708) ->
                  let uu____1713 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____1713 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.GTE ,uu____1728) ->
                  let uu____1733 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____1733 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvUlt ,uu____1748) ->
                  let uu____1753 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____1753 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Var uu____1768,uu____1769) ->
                  let uu____1774 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____1774 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Add ,uu____1789) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Sub ,uu____1800) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Div ,uu____1811) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Mul ,uu____1822) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Minus ,uu____1833) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Mod ,uu____1844) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvAnd ,uu____1855) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvXor ,uu____1866) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvOr ,uu____1877) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvAdd ,uu____1888) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvSub ,uu____1899) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvShl ,uu____1910) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvShr ,uu____1921) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvUdiv ,uu____1932) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvMod ,uu____1943) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvMul ,uu____1954) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvUext uu____1965,uu____1966) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvToNat ,uu____1977) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.NatToBv uu____1988,uu____1989) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.ITE ,uu____2000) ->
                  failwith "Impossible: arity mismatch"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Imp ,uu____2011) ->
                  failwith "Impossible: arity mismatch"
              | FStar_SMTEncoding_Term.Quant
                  (FStar_SMTEncoding_Term.Forall ,pats,iopt,sorts,body) ->
                  let uu____2042 =
                    aux default_msg ropt post_name_opt labels body  in
                  (match uu____2042 with
                   | (labels1,body1) ->
                       let uu____2061 =
                         FStar_SMTEncoding_Term.mk
                           (FStar_SMTEncoding_Term.Quant
                              (FStar_SMTEncoding_Term.Forall, pats, iopt,
                                sorts, body1)) q1.FStar_SMTEncoding_Term.rng
                          in
                       (labels1, uu____2061))
              | FStar_SMTEncoding_Term.Let (es,body) ->
                  let uu____2078 =
                    aux default_msg ropt post_name_opt labels body  in
                  (match uu____2078 with
                   | (labels1,body1) ->
                       let uu____2097 =
                         FStar_SMTEncoding_Term.mkLet (es, body1)
                           q1.FStar_SMTEncoding_Term.rng
                          in
                       (labels1, uu____2097))
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
          let print_banner uu____2132 =
            let msg =
              let uu____2134 =
                let uu____2135 = FStar_TypeChecker_Env.get_range env  in
                FStar_Range.string_of_range uu____2135  in
              let uu____2136 = FStar_Util.string_of_int (Prims.parse_int "5")
                 in
              let uu____2137 =
                FStar_Util.string_of_int (FStar_List.length all_labels)  in
              FStar_Util.format4
                "Detailed %s report follows for %s\nTaking %s seconds per proof obligation (%s proofs in total)\n"
                (if hint_replay then "hint replay" else "error") uu____2134
                uu____2136 uu____2137
               in
            FStar_Util.print_error msg  in
          let print_result uu____2154 =
            match uu____2154 with
            | ((uu____2165,msg,r),success) ->
                if success
                then
                  let uu____2175 = FStar_Range.string_of_range r  in
                  FStar_Util.print1
                    "OK: proof obligation at %s was proven in isolation\n"
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
                         let uu____2184 = FStar_Range.string_of_range r  in
                         FStar_Util.format2
                           "XX: proof obligation at %s failed\n\t%s\n"
                           uu____2184 msg
                          in
                       (FStar_Errors.Error_ProofObligationFailed, uu____2183)
                        in
                     FStar_Errors.log_issue r uu____2178)
             in
          let elim labs =
            FStar_All.pipe_right labs
              (FStar_List.map
                 (fun uu____2246  ->
                    match uu____2246 with
                    | (l,uu____2258,uu____2259) ->
                        let a =
                          let uu____2269 =
                            let uu____2270 =
                              let uu____2275 =
                                FStar_SMTEncoding_Util.mkFreeV l  in
                              (uu____2275, FStar_SMTEncoding_Util.mkTrue)  in
                            FStar_SMTEncoding_Util.mkEq uu____2270  in
                          {
                            FStar_SMTEncoding_Term.assumption_term =
                              uu____2269;
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
                   let uu____2336 =
                     FStar_List.map (fun x  -> (x, true)) eliminated  in
                   let uu____2349 =
                     FStar_List.map (fun x  -> (x, false)) errors  in
                   FStar_List.append uu____2336 uu____2349  in
                 sort_labels results
             | hd1::tl1 ->
                 ((let uu____2371 =
                     FStar_Util.string_of_int (FStar_List.length active)  in
                   FStar_Util.print1 "%s, " uu____2371);
                  (let decls =
                     FStar_All.pipe_left elim
                       (FStar_List.append eliminated
                          (FStar_List.append errors tl1))
                      in
                   let result = askZ3 decls  in
                   match result.FStar_SMTEncoding_Z3.z3result_status with
                   | FStar_SMTEncoding_Z3.UNSAT uu____2398 ->
                       linear_check (hd1 :: eliminated) errors tl1
                   | uu____2399 ->
                       linear_check eliminated (hd1 :: errors) tl1)))
             in
          print_banner ();
          FStar_Options.set_option "z3rlimit"
            (FStar_Options.Int (Prims.parse_int "5"));
          (let res = linear_check [] [] all_labels  in
           FStar_Util.print_string "\n";
           FStar_All.pipe_right res (FStar_List.iter print_result);
           (let uu____2439 =
              FStar_Util.for_all FStar_Pervasives_Native.snd res  in
            if uu____2439
            then
              FStar_Util.print_string
                "Failed: the heuristic of trying each proof in isolation failed to identify a precise error\n"
            else ()))
  