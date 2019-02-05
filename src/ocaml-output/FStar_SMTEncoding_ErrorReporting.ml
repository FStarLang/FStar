open Prims
exception Not_a_wp_implication of Prims.string 
let (uu___is_Not_a_wp_implication : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Not_a_wp_implication uu____13 -> true
    | uu____16 -> false
  
let (__proj__Not_a_wp_implication__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | Not_a_wp_implication uu____27 -> uu____27
  
type label = FStar_SMTEncoding_Term.error_label
type labels = FStar_SMTEncoding_Term.error_labels
let (sort_labels :
  (FStar_SMTEncoding_Term.error_label * Prims.bool) Prims.list ->
    ((FStar_SMTEncoding_Term.fv * Prims.string * FStar_Range.range) *
      Prims.bool) Prims.list)
  =
  fun l  ->
    FStar_List.sortWith
      (fun uu____85  ->
         fun uu____86  ->
           match (uu____85, uu____86) with
           | (((uu____136,uu____137,r1),uu____139),((uu____140,uu____141,r2),uu____143))
               -> FStar_Range.compare r1 r2) l
  
let (remove_dups :
  labels ->
    (FStar_SMTEncoding_Term.fv * Prims.string * FStar_Range.range) Prims.list)
  =
  fun l  ->
    FStar_Util.remove_dups
      (fun uu____220  ->
         fun uu____221  ->
           match (uu____220, uu____221) with
           | ((uu____251,m1,r1),(uu____254,m2,r2)) -> (r1 = r2) && (m1 = m2))
      l
  
type msg = (Prims.string * FStar_Range.range)
type ranges =
  (Prims.string FStar_Pervasives_Native.option * FStar_Range.range)
    Prims.list
let (fresh_label :
  Prims.string ->
    FStar_Range.range ->
      FStar_SMTEncoding_Term.term -> (label * FStar_SMTEncoding_Term.term))
  =
  let ctr = FStar_Util.mk_ref (Prims.parse_int "0")  in
  fun message  ->
    fun range  ->
      fun t  ->
        let l =
          FStar_Util.incr ctr;
          (let uu____354 =
             let uu____356 = FStar_ST.op_Bang ctr  in
             FStar_Util.string_of_int uu____356  in
           FStar_Util.format1 "label_%s" uu____354)
           in
        let lvar = (l, FStar_SMTEncoding_Term.Bool_sort)  in
        let label = (lvar, message, range)  in
        let lterm = FStar_SMTEncoding_Util.mkFreeV lvar  in
        let lt1 = FStar_SMTEncoding_Term.mkOr (lterm, t) range  in
        (label, lt1)
  
let (label_goals :
  (unit -> Prims.string) FStar_Pervasives_Native.option ->
    FStar_Range.range ->
      FStar_SMTEncoding_Term.term -> (labels * FStar_SMTEncoding_Term.term))
  =
  fun use_env_msg  ->
    fun r  ->
      fun q  ->
        let rec is_a_post_condition post_name_opt tm =
          match (post_name_opt, (tm.FStar_SMTEncoding_Term.tm)) with
          | (FStar_Pervasives_Native.None ,uu____477) -> false
          | (FStar_Pervasives_Native.Some nm,FStar_SMTEncoding_Term.FreeV
             (nm',uu____485)) -> nm = nm'
          | (uu____494,FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var "Valid",tm1::[])) ->
              is_a_post_condition post_name_opt tm1
          | (uu____505,FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var "ApplyTT",tm1::uu____507)) ->
              is_a_post_condition post_name_opt tm1
          | uu____519 -> false  in
        let conjuncts t =
          match t.FStar_SMTEncoding_Term.tm with
          | FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And ,cs) -> cs
          | uu____543 -> [t]  in
        let is_guard_free tm =
          match tm.FStar_SMTEncoding_Term.tm with
          | FStar_SMTEncoding_Term.Quant
              (FStar_SMTEncoding_Term.Forall
               ,({
                   FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App
                     (FStar_SMTEncoding_Term.Var "Prims.guard_free",p::[]);
                   FStar_SMTEncoding_Term.freevars = uu____553;
                   FStar_SMTEncoding_Term.rng = uu____554;_}::[])::[],iopt,uu____556,
               {
                 FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App
                   (FStar_SMTEncoding_Term.Imp ,l::r1::[]);
                 FStar_SMTEncoding_Term.freevars = uu____559;
                 FStar_SMTEncoding_Term.rng = uu____560;_})
              -> true
          | uu____603 -> false  in
        let is_a_named_continuation lhs =
          FStar_All.pipe_right (conjuncts lhs)
            (FStar_Util.for_some is_guard_free)
           in
        let uu____615 =
          match use_env_msg with
          | FStar_Pervasives_Native.None  -> (false, "")
          | FStar_Pervasives_Native.Some f ->
              let uu____645 = f ()  in (true, uu____645)
           in
        match uu____615 with
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
                    let uu____701 =
                      let uu____703 = FStar_Range.use_range rng  in
                      let uu____704 = FStar_Range.use_range r1  in
                      FStar_Range.rng_included uu____703 uu____704  in
                    if uu____701
                    then rng
                    else
                      (let uu____708 = FStar_Range.def_range rng  in
                       FStar_Range.set_def_range r1 uu____708)
                 in
              fresh_label msg1 rng1 t  in
            let rec aux default_msg ropt post_name_opt labels q1 =
              match q1.FStar_SMTEncoding_Term.tm with
              | FStar_SMTEncoding_Term.BoundV uu____763 -> (labels, q1)
              | FStar_SMTEncoding_Term.Integer uu____767 -> (labels, q1)
              | FStar_SMTEncoding_Term.LblPos uu____771 ->
                  failwith "Impossible"
              | FStar_SMTEncoding_Term.Labeled
                  (arg,"could not prove post-condition",uu____785) ->
                  let fallback msg =
                    aux default_msg ropt post_name_opt labels arg  in
                  (try
                     (fun uu___272_831  ->
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
                                                             = uu____850;
                                                           FStar_SMTEncoding_Term.rng
                                                             = rng;_})
                                 ->
                                 let post_name =
                                   let uu____883 =
                                     let uu____885 =
                                       FStar_Syntax_Syntax.next_id ()  in
                                     FStar_All.pipe_left
                                       FStar_Util.string_of_int uu____885
                                      in
                                   Prims.strcat "^^post_condition_" uu____883
                                    in
                                 let names1 =
                                   let uu____898 =
                                     FStar_List.map
                                       (fun s  ->
                                          let uu____914 =
                                            let uu____916 =
                                              let uu____918 =
                                                FStar_Syntax_Syntax.next_id
                                                  ()
                                                 in
                                              FStar_All.pipe_left
                                                FStar_Util.string_of_int
                                                uu____918
                                               in
                                            Prims.strcat "^^" uu____916  in
                                          (uu____914, s)) sorts
                                      in
                                   (post_name, post) :: uu____898  in
                                 let instantiation =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV names1
                                    in
                                 let uu____938 =
                                   let uu____943 =
                                     FStar_SMTEncoding_Term.inst
                                       instantiation lhs
                                      in
                                   let uu____944 =
                                     FStar_SMTEncoding_Term.inst
                                       instantiation rhs
                                      in
                                   (uu____943, uu____944)  in
                                 (match uu____938 with
                                  | (lhs1,rhs1) ->
                                      let uu____953 =
                                        match lhs1.FStar_SMTEncoding_Term.tm
                                        with
                                        | FStar_SMTEncoding_Term.App
                                            (FStar_SMTEncoding_Term.And
                                             ,clauses_lhs)
                                            ->
                                            let uu____971 =
                                              FStar_Util.prefix clauses_lhs
                                               in
                                            (match uu____971 with
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
                                                           = uu____1001;
                                                         FStar_SMTEncoding_Term.rng
                                                           = rng_ens;_})
                                                      ->
                                                      let uu____1032 =
                                                        is_a_post_condition
                                                          (FStar_Pervasives_Native.Some
                                                             post_name) post1
                                                         in
                                                      if uu____1032
                                                      then
                                                        let uu____1042 =
                                                          aux
                                                            "could not prove post-condition"
                                                            FStar_Pervasives_Native.None
                                                            (FStar_Pervasives_Native.Some
                                                               post_name)
                                                            labels
                                                            ensures_conjuncts
                                                           in
                                                        (match uu____1042
                                                         with
                                                         | (labels1,ensures_conjuncts1)
                                                             ->
                                                             let pats_ens1 =
                                                               match pats_ens
                                                               with
                                                               | [] ->
                                                                   [[post1]]
                                                               | []::[] ->
                                                                   [[post1]]
                                                               | uu____1086
                                                                   ->
                                                                   pats_ens
                                                                in
                                                             let ens1 =
                                                               let uu____1092
                                                                 =
                                                                 let uu____1093
                                                                   =
                                                                   let uu____1113
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
                                                                    uu____1113)
                                                                    in
                                                                 FStar_SMTEncoding_Term.Quant
                                                                   uu____1093
                                                                  in
                                                               FStar_SMTEncoding_Term.mk
                                                                 uu____1092
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
                                                             let uu____1128 =
                                                               FStar_SMTEncoding_Term.abstr
                                                                 names1 lhs2
                                                                in
                                                             (labels1,
                                                               uu____1128))
                                                      else
                                                        (let uu____1133 =
                                                           let uu____1134 =
                                                             let uu____1136 =
                                                               let uu____1138
                                                                 =
                                                                 let uu____1140
                                                                   =
                                                                   FStar_SMTEncoding_Term.print_smt_term
                                                                    post1
                                                                    in
                                                                 Prims.strcat
                                                                   "  ... "
                                                                   uu____1140
                                                                  in
                                                               Prims.strcat
                                                                 post_name
                                                                 uu____1138
                                                                in
                                                             Prims.strcat
                                                               "Ensures clause doesn't match post name:  "
                                                               uu____1136
                                                              in
                                                           Not_a_wp_implication
                                                             uu____1134
                                                            in
                                                         FStar_Exn.raise
                                                           uu____1133)
                                                  | uu____1150 ->
                                                      let uu____1151 =
                                                        let uu____1152 =
                                                          let uu____1154 =
                                                            let uu____1156 =
                                                              let uu____1158
                                                                =
                                                                FStar_SMTEncoding_Term.print_smt_term
                                                                  ens
                                                                 in
                                                              Prims.strcat
                                                                "  ... "
                                                                uu____1158
                                                               in
                                                            Prims.strcat
                                                              post_name
                                                              uu____1156
                                                             in
                                                          Prims.strcat
                                                            "Ensures clause doesn't have the expected shape for post-condition "
                                                            uu____1154
                                                           in
                                                        Not_a_wp_implication
                                                          uu____1152
                                                         in
                                                      FStar_Exn.raise
                                                        uu____1151))
                                        | uu____1168 ->
                                            let uu____1169 =
                                              let uu____1170 =
                                                let uu____1172 =
                                                  FStar_SMTEncoding_Term.print_smt_term
                                                    lhs1
                                                   in
                                                Prims.strcat
                                                  "LHS not a conjunct: "
                                                  uu____1172
                                                 in
                                              Not_a_wp_implication uu____1170
                                               in
                                            FStar_Exn.raise uu____1169
                                         in
                                      (match uu____953 with
                                       | (labels1,lhs2) ->
                                           let uu____1193 =
                                             let uu____1200 =
                                               aux default_msg
                                                 FStar_Pervasives_Native.None
                                                 (FStar_Pervasives_Native.Some
                                                    post_name) labels1 rhs1
                                                in
                                             match uu____1200 with
                                             | (labels2,rhs2) ->
                                                 let uu____1220 =
                                                   FStar_SMTEncoding_Term.abstr
                                                     names1 rhs2
                                                    in
                                                 (labels2, uu____1220)
                                              in
                                           (match uu____1193 with
                                            | (labels2,rhs2) ->
                                                let body =
                                                  FStar_SMTEncoding_Term.mkImp
                                                    (lhs2, rhs2) rng
                                                   in
                                                let uu____1236 =
                                                  FStar_SMTEncoding_Term.mk
                                                    (FStar_SMTEncoding_Term.Quant
                                                       (FStar_SMTEncoding_Term.Forall,
                                                         pats, iopt, (post ::
                                                         sorts), body))
                                                    q1.FStar_SMTEncoding_Term.rng
                                                   in
                                                (labels2, uu____1236))))
                             | uu____1248 ->
                                 let uu____1249 =
                                   let uu____1251 =
                                     FStar_SMTEncoding_Term.print_smt_term
                                       arg
                                      in
                                   Prims.strcat "arg not a quant: "
                                     uu____1251
                                    in
                                 fallback uu____1249)) ()
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
                            FStar_SMTEncoding_Term.freevars = uu____1273;
                            FStar_SMTEncoding_Term.rng = rng;_})
                  when is_a_named_continuation lhs ->
                  let uu____1300 = FStar_Util.prefix sorts  in
                  (match uu____1300 with
                   | (sorts',post) ->
                       let new_post_name =
                         let uu____1321 =
                           let uu____1323 = FStar_Syntax_Syntax.next_id ()
                              in
                           FStar_All.pipe_left FStar_Util.string_of_int
                             uu____1323
                            in
                         Prims.strcat "^^post_condition_" uu____1321  in
                       let names1 =
                         let uu____1336 =
                           FStar_List.map
                             (fun s  ->
                                let uu____1352 =
                                  let uu____1354 =
                                    let uu____1356 =
                                      FStar_Syntax_Syntax.next_id ()  in
                                    FStar_All.pipe_left
                                      FStar_Util.string_of_int uu____1356
                                     in
                                  Prims.strcat "^^" uu____1354  in
                                (uu____1352, s)) sorts'
                            in
                         FStar_List.append uu____1336 [(new_post_name, post)]
                          in
                       let instantiation =
                         FStar_List.map FStar_SMTEncoding_Util.mkFreeV names1
                          in
                       let uu____1386 =
                         let uu____1391 =
                           FStar_SMTEncoding_Term.inst instantiation lhs  in
                         let uu____1392 =
                           FStar_SMTEncoding_Term.inst instantiation rhs  in
                         (uu____1391, uu____1392)  in
                       (match uu____1386 with
                        | (lhs1,rhs1) ->
                            let uu____1401 =
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
                                                = uu____1439;
                                              FStar_SMTEncoding_Term.rng =
                                                uu____1440;_}::[])::[],iopt,sorts1,
                                          {
                                            FStar_SMTEncoding_Term.tm =
                                              FStar_SMTEncoding_Term.App
                                              (FStar_SMTEncoding_Term.Imp
                                               ,l0::r1::[]);
                                            FStar_SMTEncoding_Term.freevars =
                                              uu____1445;
                                            FStar_SMTEncoding_Term.rng =
                                              uu____1446;_})
                                         ->
                                         let uu____1488 =
                                           is_a_post_condition
                                             (FStar_Pervasives_Native.Some
                                                new_post_name) r1
                                            in
                                         if uu____1488
                                         then
                                           let uu____1498 =
                                             aux default_msg
                                               FStar_Pervasives_Native.None
                                               post_name_opt labels1 l0
                                              in
                                           (match uu____1498 with
                                            | (labels2,l) ->
                                                let uu____1517 =
                                                  let uu____1518 =
                                                    let uu____1519 =
                                                      let uu____1539 =
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
                                                        sorts1, uu____1539)
                                                       in
                                                    FStar_SMTEncoding_Term.Quant
                                                      uu____1519
                                                     in
                                                  FStar_SMTEncoding_Term.mk
                                                    uu____1518
                                                    q1.FStar_SMTEncoding_Term.rng
                                                   in
                                                (labels2, uu____1517))
                                         else (labels1, tm)
                                     | uu____1563 -> (labels1, tm)) labels
                                (conjuncts lhs1)
                               in
                            (match uu____1401 with
                             | (labels1,lhs_conjs) ->
                                 let uu____1582 =
                                   aux default_msg
                                     FStar_Pervasives_Native.None
                                     (FStar_Pervasives_Native.Some
                                        new_post_name) labels1 rhs1
                                    in
                                 (match uu____1582 with
                                  | (labels2,rhs2) ->
                                      let body =
                                        let uu____1603 =
                                          let uu____1604 =
                                            let uu____1609 =
                                              FStar_SMTEncoding_Term.mk_and_l
                                                lhs_conjs
                                                lhs1.FStar_SMTEncoding_Term.rng
                                               in
                                            (uu____1609, rhs2)  in
                                          FStar_SMTEncoding_Term.mkImp
                                            uu____1604 rng
                                           in
                                        FStar_All.pipe_right uu____1603
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
                  let uu____1629 =
                    aux default_msg ropt post_name_opt labels rhs  in
                  (match uu____1629 with
                   | (labels1,rhs1) ->
                       let uu____1648 =
                         FStar_SMTEncoding_Util.mkImp (lhs, rhs1)  in
                       (labels1, uu____1648))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.And ,conjuncts1) ->
                  let uu____1656 =
                    FStar_Util.fold_map (aux default_msg ropt post_name_opt)
                      labels conjuncts1
                     in
                  (match uu____1656 with
                   | (labels1,conjuncts2) ->
                       let uu____1683 =
                         FStar_SMTEncoding_Term.mk_and_l conjuncts2
                           q1.FStar_SMTEncoding_Term.rng
                          in
                       (labels1, uu____1683))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.ITE ,hd1::q11::q2::[]) ->
                  let uu____1691 =
                    aux default_msg ropt post_name_opt labels q11  in
                  (match uu____1691 with
                   | (labels1,q12) ->
                       let uu____1710 =
                         aux default_msg ropt post_name_opt labels1 q2  in
                       (match uu____1710 with
                        | (labels2,q21) ->
                            let uu____1729 =
                              FStar_SMTEncoding_Term.mkITE (hd1, q12, q21)
                                q1.FStar_SMTEncoding_Term.rng
                               in
                            (labels2, uu____1729)))
              | FStar_SMTEncoding_Term.Quant
                  (FStar_SMTEncoding_Term.Exists
                   ,uu____1732,uu____1733,uu____1734,uu____1735)
                  ->
                  let uu____1754 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____1754 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Iff ,uu____1769) ->
                  let uu____1774 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____1774 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Or ,uu____1789) ->
                  let uu____1794 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____1794 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Var uu____1809,uu____1810) when
                  is_a_post_condition post_name_opt q1 -> (labels, q1)
              | FStar_SMTEncoding_Term.FreeV uu____1818 ->
                  let uu____1824 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____1824 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.TrueOp ,uu____1839) ->
                  let uu____1844 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____1844 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.FalseOp ,uu____1859) ->
                  let uu____1864 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____1864 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Not ,uu____1879) ->
                  let uu____1884 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____1884 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Eq ,uu____1899) ->
                  let uu____1904 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____1904 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.LT ,uu____1919) ->
                  let uu____1924 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____1924 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.LTE ,uu____1939) ->
                  let uu____1944 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____1944 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.GT ,uu____1959) ->
                  let uu____1964 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____1964 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.GTE ,uu____1979) ->
                  let uu____1984 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____1984 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvUlt ,uu____1999) ->
                  let uu____2004 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____2004 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Var uu____2019,uu____2020) ->
                  let uu____2026 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____2026 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Add ,uu____2041) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Sub ,uu____2053) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Div ,uu____2065) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Mul ,uu____2077) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Minus ,uu____2089) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Mod ,uu____2101) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvAnd ,uu____2113) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvXor ,uu____2125) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvOr ,uu____2137) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvAdd ,uu____2149) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvSub ,uu____2161) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvShl ,uu____2173) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvShr ,uu____2185) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvUdiv ,uu____2197) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvMod ,uu____2209) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvMul ,uu____2221) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvUext uu____2233,uu____2234) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvToNat ,uu____2247) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.NatToBv uu____2259,uu____2260) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.ITE ,uu____2273) ->
                  failwith "Impossible: arity mismatch"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Imp ,uu____2285) ->
                  failwith "Impossible: arity mismatch"
              | FStar_SMTEncoding_Term.Quant
                  (FStar_SMTEncoding_Term.Forall ,pats,iopt,sorts,body) ->
                  let uu____2319 =
                    aux default_msg ropt post_name_opt labels body  in
                  (match uu____2319 with
                   | (labels1,body1) ->
                       let uu____2338 =
                         FStar_SMTEncoding_Term.mk
                           (FStar_SMTEncoding_Term.Quant
                              (FStar_SMTEncoding_Term.Forall, pats, iopt,
                                sorts, body1)) q1.FStar_SMTEncoding_Term.rng
                          in
                       (labels1, uu____2338))
              | FStar_SMTEncoding_Term.Let (es,body) ->
                  let uu____2356 =
                    aux default_msg ropt post_name_opt labels body  in
                  (match uu____2356 with
                   | (labels1,body1) ->
                       let uu____2375 =
                         FStar_SMTEncoding_Term.mkLet (es, body1)
                           q1.FStar_SMTEncoding_Term.rng
                          in
                       (labels1, uu____2375))
               in
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
  fun hint_replay  ->
    fun env  ->
      fun all_labels  ->
        fun askZ3  ->
          let print_banner uu____2419 =
            let msg =
              let uu____2422 =
                let uu____2424 = FStar_TypeChecker_Env.get_range env  in
                FStar_Range.string_of_range uu____2424  in
              let uu____2425 = FStar_Util.string_of_int (Prims.parse_int "5")
                 in
              let uu____2428 =
                FStar_Util.string_of_int (FStar_List.length all_labels)  in
              FStar_Util.format4
                "Detailed %s report follows for %s\nTaking %s seconds per proof obligation (%s proofs in total)\n"
                (if hint_replay then "hint replay" else "error") uu____2422
                uu____2425 uu____2428
               in
            FStar_Util.print_error msg  in
          let print_result uu____2454 =
            match uu____2454 with
            | ((uu____2467,msg,r),success) ->
                if success
                then
                  let uu____2483 = FStar_Range.string_of_range r  in
                  FStar_Util.print1
                    "OK: proof obligation at %s was proven in isolation\n"
                    uu____2483
                else
                  if hint_replay
                  then
                    FStar_Errors.log_issue r
                      (FStar_Errors.Warning_HintFailedToReplayProof,
                        (Prims.strcat
                           "Hint failed to replay this sub-proof: " msg))
                  else
                    (let uu____2493 =
                       let uu____2499 =
                         let uu____2501 = FStar_Range.string_of_range r  in
                         FStar_Util.format2
                           "XX: proof obligation at %s failed\n\t%s\n"
                           uu____2501 msg
                          in
                       (FStar_Errors.Error_ProofObligationFailed, uu____2499)
                        in
                     FStar_Errors.log_issue r uu____2493)
             in
          let elim labs =
            FStar_All.pipe_right labs
              (FStar_List.map
                 (fun uu____2574  ->
                    match uu____2574 with
                    | (l,uu____2588,uu____2589) ->
                        let a =
                          let uu____2603 =
                            let uu____2604 =
                              let uu____2609 =
                                FStar_SMTEncoding_Util.mkFreeV l  in
                              (uu____2609, FStar_SMTEncoding_Util.mkTrue)  in
                            FStar_SMTEncoding_Util.mkEq uu____2604  in
                          {
                            FStar_SMTEncoding_Term.assumption_term =
                              uu____2603;
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
                   let uu____2679 =
                     FStar_List.map (fun x  -> (x, true)) eliminated  in
                   let uu____2696 =
                     FStar_List.map (fun x  -> (x, false)) errors  in
                   FStar_List.append uu____2679 uu____2696  in
                 sort_labels results
             | hd1::tl1 ->
                 ((let uu____2723 =
                     FStar_Util.string_of_int (FStar_List.length active)  in
                   FStar_Util.print1 "%s, " uu____2723);
                  (let decls =
                     FStar_All.pipe_left elim
                       (FStar_List.append eliminated
                          (FStar_List.append errors tl1))
                      in
                   let result = askZ3 decls  in
                   match result.FStar_SMTEncoding_Z3.z3result_status with
                   | FStar_SMTEncoding_Z3.UNSAT uu____2760 ->
                       linear_check (hd1 :: eliminated) errors tl1
                   | uu____2761 ->
                       linear_check eliminated (hd1 :: errors) tl1)))
             in
          print_banner ();
          FStar_Options.set_option "z3rlimit"
            (FStar_Options.Int (Prims.parse_int "5"));
          (let res = linear_check [] [] all_labels  in
           FStar_Util.print_string "\n";
           FStar_All.pipe_right res (FStar_List.iter print_result);
           (let uu____2810 =
              FStar_Util.for_all FStar_Pervasives_Native.snd res  in
            if uu____2810
            then
              FStar_Util.print_string
                "Failed: the heuristic of trying each proof in isolation failed to identify a precise error\n"
            else ()))
  