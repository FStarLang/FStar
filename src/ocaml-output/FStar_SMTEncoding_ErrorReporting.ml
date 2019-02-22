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
        let lvar =
          FStar_SMTEncoding_Term.mk_fv (l, FStar_SMTEncoding_Term.Bool_sort)
           in
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
          | (FStar_Pervasives_Native.None ,uu____472) -> false
          | (FStar_Pervasives_Native.Some nm,FStar_SMTEncoding_Term.FreeV fv)
              ->
              let uu____493 = FStar_SMTEncoding_Term.fv_name fv  in
              nm = uu____493
          | (uu____496,FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var "Valid",tm1::[])) ->
              is_a_post_condition post_name_opt tm1
          | (uu____507,FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var "ApplyTT",tm1::uu____509)) ->
              is_a_post_condition post_name_opt tm1
          | uu____521 -> false  in
        let conjuncts t =
          match t.FStar_SMTEncoding_Term.tm with
          | FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And ,cs) -> cs
          | uu____545 -> [t]  in
        let is_guard_free tm =
          match tm.FStar_SMTEncoding_Term.tm with
          | FStar_SMTEncoding_Term.Quant
              (FStar_SMTEncoding_Term.Forall
               ,({
                   FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App
                     (FStar_SMTEncoding_Term.Var "Prims.guard_free",p::[]);
                   FStar_SMTEncoding_Term.freevars = uu____555;
                   FStar_SMTEncoding_Term.rng = uu____556;_}::[])::[],iopt,uu____558,
               {
                 FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App
                   (FStar_SMTEncoding_Term.Imp ,l::r1::[]);
                 FStar_SMTEncoding_Term.freevars = uu____561;
                 FStar_SMTEncoding_Term.rng = uu____562;_})
              -> true
          | uu____611 -> false  in
        let is_a_named_continuation lhs =
          FStar_All.pipe_right (conjuncts lhs)
            (FStar_Util.for_some is_guard_free)
           in
        let uu____623 =
          match use_env_msg with
          | FStar_Pervasives_Native.None  -> (false, "")
          | FStar_Pervasives_Native.Some f ->
              let uu____653 = f ()  in (true, uu____653)
           in
        match uu____623 with
        | (flag,msg_prefix) ->
            let fresh_label1 msg ropt rng t =
              let msg1 =
                if flag
                then
                  Prims.op_Hat "Failed to verify implicit argument: "
                    (Prims.op_Hat msg_prefix (Prims.op_Hat " :: " msg))
                else msg  in
              let rng1 =
                match ropt with
                | FStar_Pervasives_Native.None  -> rng
                | FStar_Pervasives_Native.Some r1 ->
                    let uu____709 =
                      let uu____711 = FStar_Range.use_range rng  in
                      let uu____712 = FStar_Range.use_range r1  in
                      FStar_Range.rng_included uu____711 uu____712  in
                    if uu____709
                    then rng
                    else
                      (let uu____716 = FStar_Range.def_range rng  in
                       FStar_Range.set_def_range r1 uu____716)
                 in
              fresh_label msg1 rng1 t  in
            let rec aux default_msg ropt post_name_opt labels q1 =
              match q1.FStar_SMTEncoding_Term.tm with
              | FStar_SMTEncoding_Term.BoundV uu____771 -> (labels, q1)
              | FStar_SMTEncoding_Term.Integer uu____775 -> (labels, q1)
              | FStar_SMTEncoding_Term.Real uu____779 -> (labels, q1)
              | FStar_SMTEncoding_Term.LblPos uu____783 ->
                  failwith "Impossible"
              | FStar_SMTEncoding_Term.Labeled
                  (arg,"could not prove post-condition",uu____797) ->
                  let fallback msg =
                    aux default_msg ropt post_name_opt labels arg  in
                  (try
                     (fun uu___12_843  ->
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
                                                             = uu____862;
                                                           FStar_SMTEncoding_Term.rng
                                                             = rng;_})
                                 ->
                                 let post_name =
                                   let uu____898 =
                                     let uu____900 =
                                       FStar_Syntax_Syntax.next_id ()  in
                                     FStar_All.pipe_left
                                       FStar_Util.string_of_int uu____900
                                      in
                                   Prims.op_Hat "^^post_condition_" uu____898
                                    in
                                 let names1 =
                                   let uu____908 =
                                     FStar_SMTEncoding_Term.mk_fv
                                       (post_name, post)
                                      in
                                   let uu____910 =
                                     FStar_List.map
                                       (fun s  ->
                                          let uu____916 =
                                            let uu____922 =
                                              let uu____924 =
                                                let uu____926 =
                                                  FStar_Syntax_Syntax.next_id
                                                    ()
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_Util.string_of_int
                                                  uu____926
                                                 in
                                              Prims.op_Hat "^^" uu____924  in
                                            (uu____922, s)  in
                                          FStar_SMTEncoding_Term.mk_fv
                                            uu____916) sorts
                                      in
                                   uu____908 :: uu____910  in
                                 let instantiation =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV names1
                                    in
                                 let uu____935 =
                                   let uu____940 =
                                     FStar_SMTEncoding_Term.inst
                                       instantiation lhs
                                      in
                                   let uu____941 =
                                     FStar_SMTEncoding_Term.inst
                                       instantiation rhs
                                      in
                                   (uu____940, uu____941)  in
                                 (match uu____935 with
                                  | (lhs1,rhs1) ->
                                      let uu____950 =
                                        match lhs1.FStar_SMTEncoding_Term.tm
                                        with
                                        | FStar_SMTEncoding_Term.App
                                            (FStar_SMTEncoding_Term.And
                                             ,clauses_lhs)
                                            ->
                                            let uu____968 =
                                              FStar_Util.prefix clauses_lhs
                                               in
                                            (match uu____968 with
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
                                                           = uu____998;
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
                                                                 Prims.op_Hat
                                                                   "  ... "
                                                                   uu____1140
                                                                  in
                                                               Prims.op_Hat
                                                                 post_name
                                                                 uu____1138
                                                                in
                                                             Prims.op_Hat
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
                                                              Prims.op_Hat
                                                                "  ... "
                                                                uu____1158
                                                               in
                                                            Prims.op_Hat
                                                              post_name
                                                              uu____1156
                                                             in
                                                          Prims.op_Hat
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
                                                Prims.op_Hat
                                                  "LHS not a conjunct: "
                                                  uu____1172
                                                 in
                                              Not_a_wp_implication uu____1170
                                               in
                                            FStar_Exn.raise uu____1169
                                         in
                                      (match uu____950 with
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
                                   Prims.op_Hat "arg not a quant: "
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
                  let uu____1303 = FStar_Util.prefix sorts  in
                  (match uu____1303 with
                   | (sorts',post) ->
                       let new_post_name =
                         let uu____1324 =
                           let uu____1326 = FStar_Syntax_Syntax.next_id ()
                              in
                           FStar_All.pipe_left FStar_Util.string_of_int
                             uu____1326
                            in
                         Prims.op_Hat "^^post_condition_" uu____1324  in
                       let names1 =
                         let uu____1334 =
                           FStar_List.map
                             (fun s  ->
                                let uu____1340 =
                                  let uu____1346 =
                                    let uu____1348 =
                                      let uu____1350 =
                                        FStar_Syntax_Syntax.next_id ()  in
                                      FStar_All.pipe_left
                                        FStar_Util.string_of_int uu____1350
                                       in
                                    Prims.op_Hat "^^" uu____1348  in
                                  (uu____1346, s)  in
                                FStar_SMTEncoding_Term.mk_fv uu____1340)
                             sorts'
                            in
                         let uu____1356 =
                           let uu____1359 =
                             FStar_SMTEncoding_Term.mk_fv
                               (new_post_name, post)
                              in
                           [uu____1359]  in
                         FStar_List.append uu____1334 uu____1356  in
                       let instantiation =
                         FStar_List.map FStar_SMTEncoding_Util.mkFreeV names1
                          in
                       let uu____1364 =
                         let uu____1369 =
                           FStar_SMTEncoding_Term.inst instantiation lhs  in
                         let uu____1370 =
                           FStar_SMTEncoding_Term.inst instantiation rhs  in
                         (uu____1369, uu____1370)  in
                       (match uu____1364 with
                        | (lhs1,rhs1) ->
                            let uu____1379 =
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
                                                = uu____1417;
                                              FStar_SMTEncoding_Term.rng =
                                                uu____1418;_}::[])::[],iopt,sorts1,
                                          {
                                            FStar_SMTEncoding_Term.tm =
                                              FStar_SMTEncoding_Term.App
                                              (FStar_SMTEncoding_Term.Imp
                                               ,l0::r1::[]);
                                            FStar_SMTEncoding_Term.freevars =
                                              uu____1423;
                                            FStar_SMTEncoding_Term.rng =
                                              uu____1424;_})
                                         ->
                                         let uu____1472 =
                                           is_a_post_condition
                                             (FStar_Pervasives_Native.Some
                                                new_post_name) r1
                                            in
                                         if uu____1472
                                         then
                                           let uu____1482 =
                                             aux default_msg
                                               FStar_Pervasives_Native.None
                                               post_name_opt labels1 l0
                                              in
                                           (match uu____1482 with
                                            | (labels2,l) ->
                                                let uu____1501 =
                                                  let uu____1502 =
                                                    let uu____1503 =
                                                      let uu____1523 =
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
                                                        sorts1, uu____1523)
                                                       in
                                                    FStar_SMTEncoding_Term.Quant
                                                      uu____1503
                                                     in
                                                  FStar_SMTEncoding_Term.mk
                                                    uu____1502
                                                    q1.FStar_SMTEncoding_Term.rng
                                                   in
                                                (labels2, uu____1501))
                                         else (labels1, tm)
                                     | uu____1547 -> (labels1, tm)) labels
                                (conjuncts lhs1)
                               in
                            (match uu____1379 with
                             | (labels1,lhs_conjs) ->
                                 let uu____1566 =
                                   aux default_msg
                                     FStar_Pervasives_Native.None
                                     (FStar_Pervasives_Native.Some
                                        new_post_name) labels1 rhs1
                                    in
                                 (match uu____1566 with
                                  | (labels2,rhs2) ->
                                      let body =
                                        let uu____1587 =
                                          let uu____1588 =
                                            let uu____1593 =
                                              FStar_SMTEncoding_Term.mk_and_l
                                                lhs_conjs
                                                lhs1.FStar_SMTEncoding_Term.rng
                                               in
                                            (uu____1593, rhs2)  in
                                          FStar_SMTEncoding_Term.mkImp
                                            uu____1588 rng
                                           in
                                        FStar_All.pipe_right uu____1587
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
                  let uu____1613 =
                    aux default_msg ropt post_name_opt labels rhs  in
                  (match uu____1613 with
                   | (labels1,rhs1) ->
                       let uu____1632 =
                         FStar_SMTEncoding_Util.mkImp (lhs, rhs1)  in
                       (labels1, uu____1632))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.And ,conjuncts1) ->
                  let uu____1640 =
                    FStar_Util.fold_map (aux default_msg ropt post_name_opt)
                      labels conjuncts1
                     in
                  (match uu____1640 with
                   | (labels1,conjuncts2) ->
                       let uu____1667 =
                         FStar_SMTEncoding_Term.mk_and_l conjuncts2
                           q1.FStar_SMTEncoding_Term.rng
                          in
                       (labels1, uu____1667))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.ITE ,hd1::q11::q2::[]) ->
                  let uu____1675 =
                    aux default_msg ropt post_name_opt labels q11  in
                  (match uu____1675 with
                   | (labels1,q12) ->
                       let uu____1694 =
                         aux default_msg ropt post_name_opt labels1 q2  in
                       (match uu____1694 with
                        | (labels2,q21) ->
                            let uu____1713 =
                              FStar_SMTEncoding_Term.mkITE (hd1, q12, q21)
                                q1.FStar_SMTEncoding_Term.rng
                               in
                            (labels2, uu____1713)))
              | FStar_SMTEncoding_Term.Quant
                  (FStar_SMTEncoding_Term.Exists
                   ,uu____1716,uu____1717,uu____1718,uu____1719)
                  ->
                  let uu____1738 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____1738 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Iff ,uu____1753) ->
                  let uu____1758 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____1758 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Or ,uu____1773) ->
                  let uu____1778 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____1778 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Var uu____1793,uu____1794) when
                  is_a_post_condition post_name_opt q1 -> (labels, q1)
              | FStar_SMTEncoding_Term.FreeV uu____1802 ->
                  let uu____1811 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____1811 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.TrueOp ,uu____1826) ->
                  let uu____1831 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____1831 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.FalseOp ,uu____1846) ->
                  let uu____1851 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____1851 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Not ,uu____1866) ->
                  let uu____1871 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____1871 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Eq ,uu____1886) ->
                  let uu____1891 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____1891 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.LT ,uu____1906) ->
                  let uu____1911 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____1911 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.LTE ,uu____1926) ->
                  let uu____1931 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____1931 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.GT ,uu____1946) ->
                  let uu____1951 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____1951 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.GTE ,uu____1966) ->
                  let uu____1971 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____1971 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvUlt ,uu____1986) ->
                  let uu____1991 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____1991 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Var uu____2006,uu____2007) ->
                  let uu____2013 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____2013 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Add ,uu____2028) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Sub ,uu____2040) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Div ,uu____2052) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Mul ,uu____2064) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Minus ,uu____2076) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Mod ,uu____2088) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvAnd ,uu____2100) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvXor ,uu____2112) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvOr ,uu____2124) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvAdd ,uu____2136) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvSub ,uu____2148) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvShl ,uu____2160) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvShr ,uu____2172) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvUdiv ,uu____2184) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvMod ,uu____2196) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvMul ,uu____2208) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvUext uu____2220,uu____2221) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvToNat ,uu____2234) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.NatToBv uu____2246,uu____2247) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.ITE ,uu____2260) ->
                  failwith "Impossible: arity mismatch"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Imp ,uu____2272) ->
                  failwith "Impossible: arity mismatch"
              | FStar_SMTEncoding_Term.Quant
                  (FStar_SMTEncoding_Term.Forall ,pats,iopt,sorts,body) ->
                  let uu____2306 =
                    aux default_msg ropt post_name_opt labels body  in
                  (match uu____2306 with
                   | (labels1,body1) ->
                       let uu____2325 =
                         FStar_SMTEncoding_Term.mk
                           (FStar_SMTEncoding_Term.Quant
                              (FStar_SMTEncoding_Term.Forall, pats, iopt,
                                sorts, body1)) q1.FStar_SMTEncoding_Term.rng
                          in
                       (labels1, uu____2325))
              | FStar_SMTEncoding_Term.Let (es,body) ->
                  let uu____2343 =
                    aux default_msg ropt post_name_opt labels body  in
                  (match uu____2343 with
                   | (labels1,body1) ->
                       let uu____2362 =
                         FStar_SMTEncoding_Term.mkLet (es, body1)
                           q1.FStar_SMTEncoding_Term.rng
                          in
                       (labels1, uu____2362))
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
          let print_banner uu____2406 =
            let msg =
              let uu____2409 =
                let uu____2411 = FStar_TypeChecker_Env.get_range env  in
                FStar_Range.string_of_range uu____2411  in
              let uu____2412 = FStar_Util.string_of_int (Prims.parse_int "5")
                 in
              let uu____2415 =
                FStar_Util.string_of_int (FStar_List.length all_labels)  in
              FStar_Util.format4
                "Detailed %s report follows for %s\nTaking %s seconds per proof obligation (%s proofs in total)\n"
                (if hint_replay then "hint replay" else "error") uu____2409
                uu____2412 uu____2415
               in
            FStar_Util.print_error msg  in
          let print_result uu____2441 =
            match uu____2441 with
            | ((uu____2454,msg,r),success) ->
                if success
                then
                  let uu____2470 = FStar_Range.string_of_range r  in
                  FStar_Util.print1
                    "OK: proof obligation at %s was proven in isolation\n"
                    uu____2470
                else
                  if hint_replay
                  then
                    FStar_Errors.log_issue r
                      (FStar_Errors.Warning_HintFailedToReplayProof,
                        (Prims.op_Hat
                           "Hint failed to replay this sub-proof: " msg))
                  else
                    (let uu____2480 =
                       let uu____2486 =
                         let uu____2488 = FStar_Range.string_of_range r  in
                         FStar_Util.format2
                           "XX: proof obligation at %s failed\n\t%s\n"
                           uu____2488 msg
                          in
                       (FStar_Errors.Error_ProofObligationFailed, uu____2486)
                        in
                     FStar_Errors.log_issue r uu____2480)
             in
          let elim labs =
            FStar_All.pipe_right labs
              (FStar_List.map
                 (fun uu____2541  ->
                    match uu____2541 with
                    | (l,uu____2550,uu____2551) ->
                        let a =
                          let uu____2555 =
                            let uu____2556 =
                              let uu____2561 =
                                FStar_SMTEncoding_Util.mkFreeV l  in
                              (uu____2561, FStar_SMTEncoding_Util.mkTrue)  in
                            FStar_SMTEncoding_Util.mkEq uu____2556  in
                          let uu____2562 =
                            let uu____2564 = FStar_SMTEncoding_Term.fv_name l
                               in
                            Prims.op_Hat "@disable_label_" uu____2564  in
                          {
                            FStar_SMTEncoding_Term.assumption_term =
                              uu____2555;
                            FStar_SMTEncoding_Term.assumption_caption =
                              (FStar_Pervasives_Native.Some "Disabling label");
                            FStar_SMTEncoding_Term.assumption_name =
                              uu____2562;
                            FStar_SMTEncoding_Term.assumption_fact_ids = []
                          }  in
                        FStar_SMTEncoding_Term.Assume a))
             in
          let rec linear_check eliminated errors active =
            FStar_SMTEncoding_Z3.refresh ();
            (match active with
             | [] ->
                 let results =
                   let uu____2634 =
                     FStar_List.map (fun x  -> (x, true)) eliminated  in
                   let uu____2651 =
                     FStar_List.map (fun x  -> (x, false)) errors  in
                   FStar_List.append uu____2634 uu____2651  in
                 sort_labels results
             | hd1::tl1 ->
                 ((let uu____2678 =
                     FStar_Util.string_of_int (FStar_List.length active)  in
                   FStar_Util.print1 "%s, " uu____2678);
                  (let decls =
                     FStar_All.pipe_left elim
                       (FStar_List.append eliminated
                          (FStar_List.append errors tl1))
                      in
                   let result = askZ3 decls  in
                   match result.FStar_SMTEncoding_Z3.z3result_status with
                   | FStar_SMTEncoding_Z3.UNSAT uu____2710 ->
                       linear_check (hd1 :: eliminated) errors tl1
                   | uu____2711 ->
                       linear_check eliminated (hd1 :: errors) tl1)))
             in
          print_banner ();
          FStar_Options.set_option "z3rlimit"
            (FStar_Options.Int (Prims.parse_int "5"));
          (let res = linear_check [] [] all_labels  in
           FStar_Util.print_string "\n";
           FStar_All.pipe_right res (FStar_List.iter print_result);
           (let uu____2760 =
              FStar_Util.for_all FStar_Pervasives_Native.snd res  in
            if uu____2760
            then
              FStar_Util.print_string
                "Failed: the heuristic of trying each proof in isolation failed to identify a precise error\n"
            else ()))
  