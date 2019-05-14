open Prims
exception Not_a_wp_implication of Prims.string 
let (uu___is_Not_a_wp_implication : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Not_a_wp_implication uu____12 -> true
    | uu____15 -> false
  
let (__proj__Not_a_wp_implication__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | Not_a_wp_implication uu____25 -> uu____25
  
type label = FStar_SMTEncoding_Term.error_label
type labels = FStar_SMTEncoding_Term.error_labels
let (sort_labels :
  (FStar_SMTEncoding_Term.error_label * Prims.bool) Prims.list ->
    ((FStar_SMTEncoding_Term.fv * Prims.string * FStar_Range.range) *
      Prims.bool) Prims.list)
  =
  fun l  ->
    FStar_List.sortWith
      (fun uu____83  ->
         fun uu____84  ->
           match (uu____83, uu____84) with
           | (((uu____134,uu____135,r1),uu____137),((uu____138,uu____139,r2),uu____141))
               -> FStar_Range.compare r1 r2) l
  
let (remove_dups :
  labels ->
    (FStar_SMTEncoding_Term.fv * Prims.string * FStar_Range.range) Prims.list)
  =
  fun l  ->
    FStar_Util.remove_dups
      (fun uu____218  ->
         fun uu____219  ->
           match (uu____218, uu____219) with
           | ((uu____249,m1,r1),(uu____252,m2,r2)) -> (r1 = r2) && (m1 = m2))
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
          (let uu____328 =
             let uu____330 = FStar_ST.op_Bang ctr  in
             FStar_Util.string_of_int uu____330  in
           FStar_Util.format1 "label_%s" uu____328)
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
          | (FStar_Pervasives_Native.None ,uu____463) -> false
          | (FStar_Pervasives_Native.Some nm,FStar_SMTEncoding_Term.FreeV fv)
              ->
              let uu____484 = FStar_SMTEncoding_Term.fv_name fv  in
              nm = uu____484
          | (uu____487,FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var "Valid",tm1::[])) ->
              is_a_post_condition post_name_opt tm1
          | (uu____510,FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var "ApplyTT",tm1::uu____512)) ->
              is_a_post_condition post_name_opt tm1
          | uu____536 -> false  in
        let conjuncts t =
          match t.FStar_SMTEncoding_Term.tm with
          | FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And ,cs) -> cs
          | uu____578 -> [t]  in
        let is_guard_free tm =
          match tm.FStar_SMTEncoding_Term.tm with
          | FStar_SMTEncoding_Term.Quant
              (FStar_SMTEncoding_Term.Forall
               ,({
                   FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App
                     (FStar_SMTEncoding_Term.Var "Prims.guard_free",p::[]);
                   FStar_SMTEncoding_Term.freevars = uu____600;
                   FStar_SMTEncoding_Term.rng = uu____601;_}::[])::[],iopt,uu____603,
               {
                 FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App
                   (FStar_SMTEncoding_Term.Imp ,l::r1::[]);
                 FStar_SMTEncoding_Term.freevars = uu____606;
                 FStar_SMTEncoding_Term.rng = uu____607;_})
              -> true
          | uu____704 -> false  in
        let is_a_named_continuation lhs =
          FStar_All.pipe_right (conjuncts lhs)
            (FStar_Util.for_some is_guard_free)
           in
        let uu____728 =
          match use_env_msg with
          | FStar_Pervasives_Native.None  -> (false, "")
          | FStar_Pervasives_Native.Some f ->
              let uu____758 = f ()  in (true, uu____758)
           in
        match uu____728 with
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
                    let uu____826 =
                      let uu____828 = FStar_Range.use_range rng  in
                      let uu____829 = FStar_Range.use_range r1  in
                      FStar_Range.rng_included uu____828 uu____829  in
                    if uu____826
                    then rng
                    else
                      (let uu____833 = FStar_Range.def_range rng  in
                       FStar_Range.set_def_range r1 uu____833)
                 in
              fresh_label msg1 rng1 t  in
            let rec aux default_msg ropt post_name_opt labels q1 =
              match q1.FStar_SMTEncoding_Term.tm with
              | FStar_SMTEncoding_Term.BoundV uu____900 -> (labels, q1)
              | FStar_SMTEncoding_Term.Integer uu____907 -> (labels, q1)
              | FStar_SMTEncoding_Term.Real uu____914 -> (labels, q1)
              | FStar_SMTEncoding_Term.LblPos uu____921 ->
                  failwith "Impossible"
              | FStar_SMTEncoding_Term.Labeled
                  (arg,"could not prove post-condition",uu____941) ->
                  let fallback msg =
                    aux default_msg ropt post_name_opt labels arg  in
                  (try
                     (fun uu___142_999  ->
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
                                                             = uu____1024;
                                                           FStar_SMTEncoding_Term.rng
                                                             = rng;_})
                                 ->
                                 let post_name =
                                   let uu____1087 =
                                     let uu____1089 = FStar_Ident.next_id ()
                                        in
                                     FStar_All.pipe_left
                                       FStar_Util.string_of_int uu____1089
                                      in
                                   Prims.op_Hat "^^post_condition_"
                                     uu____1087
                                    in
                                 let names1 =
                                   let uu____1097 =
                                     FStar_SMTEncoding_Term.mk_fv
                                       (post_name, post)
                                      in
                                   let uu____1099 =
                                     FStar_List.map
                                       (fun s  ->
                                          let uu____1105 =
                                            let uu____1111 =
                                              let uu____1113 =
                                                let uu____1115 =
                                                  FStar_Ident.next_id ()  in
                                                FStar_All.pipe_left
                                                  FStar_Util.string_of_int
                                                  uu____1115
                                                 in
                                              Prims.op_Hat "^^" uu____1113
                                               in
                                            (uu____1111, s)  in
                                          FStar_SMTEncoding_Term.mk_fv
                                            uu____1105) sorts
                                      in
                                   uu____1097 :: uu____1099  in
                                 let instantiation =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV names1
                                    in
                                 let uu____1130 =
                                   let uu____1141 =
                                     FStar_SMTEncoding_Term.inst
                                       instantiation lhs
                                      in
                                   let uu____1148 =
                                     FStar_SMTEncoding_Term.inst
                                       instantiation rhs
                                      in
                                   (uu____1141, uu____1148)  in
                                 (match uu____1130 with
                                  | (lhs1,rhs1) ->
                                      let uu____1184 =
                                        match lhs1.FStar_SMTEncoding_Term.tm
                                        with
                                        | FStar_SMTEncoding_Term.App
                                            (FStar_SMTEncoding_Term.And
                                             ,clauses_lhs)
                                            ->
                                            let uu____1214 =
                                              FStar_Util.prefix clauses_lhs
                                               in
                                            (match uu____1214 with
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
                                                           = uu____1271;
                                                         FStar_SMTEncoding_Term.rng
                                                           = rng_ens;_})
                                                      ->
                                                      let uu____1332 =
                                                        is_a_post_condition
                                                          (FStar_Pervasives_Native.Some
                                                             post_name) post1
                                                         in
                                                      if uu____1332
                                                      then
                                                        let uu____1345 =
                                                          aux
                                                            "could not prove post-condition"
                                                            FStar_Pervasives_Native.None
                                                            (FStar_Pervasives_Native.Some
                                                               post_name)
                                                            labels
                                                            ensures_conjuncts
                                                           in
                                                        (match uu____1345
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
                                                               | uu____1443
                                                                   ->
                                                                   pats_ens
                                                                in
                                                             let ens1 =
                                                               let uu____1458
                                                                 =
                                                                 let uu____1459
                                                                   =
                                                                   let uu____1485
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
                                                                    uu____1485)
                                                                    in
                                                                 FStar_SMTEncoding_Term.Quant
                                                                   uu____1459
                                                                  in
                                                               FStar_SMTEncoding_Term.mk
                                                                 uu____1458
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
                                                             let uu____1542 =
                                                               FStar_SMTEncoding_Term.abstr
                                                                 names1 lhs2
                                                                in
                                                             (labels1,
                                                               uu____1542))
                                                      else
                                                        (let uu____1556 =
                                                           let uu____1557 =
                                                             let uu____1559 =
                                                               let uu____1561
                                                                 =
                                                                 let uu____1563
                                                                   =
                                                                   FStar_SMTEncoding_Term.print_smt_term
                                                                    post1
                                                                    in
                                                                 Prims.op_Hat
                                                                   "  ... "
                                                                   uu____1563
                                                                  in
                                                               Prims.op_Hat
                                                                 post_name
                                                                 uu____1561
                                                                in
                                                             Prims.op_Hat
                                                               "Ensures clause doesn't match post name:  "
                                                               uu____1559
                                                              in
                                                           Not_a_wp_implication
                                                             uu____1557
                                                            in
                                                         FStar_Exn.raise
                                                           uu____1556)
                                                  | uu____1576 ->
                                                      let uu____1577 =
                                                        let uu____1578 =
                                                          let uu____1580 =
                                                            let uu____1582 =
                                                              let uu____1584
                                                                =
                                                                FStar_SMTEncoding_Term.print_smt_term
                                                                  ens
                                                                 in
                                                              Prims.op_Hat
                                                                "  ... "
                                                                uu____1584
                                                               in
                                                            Prims.op_Hat
                                                              post_name
                                                              uu____1582
                                                             in
                                                          Prims.op_Hat
                                                            "Ensures clause doesn't have the expected shape for post-condition "
                                                            uu____1580
                                                           in
                                                        Not_a_wp_implication
                                                          uu____1578
                                                         in
                                                      FStar_Exn.raise
                                                        uu____1577))
                                        | uu____1597 ->
                                            let uu____1598 =
                                              let uu____1599 =
                                                let uu____1601 =
                                                  FStar_SMTEncoding_Term.print_smt_term
                                                    lhs1
                                                   in
                                                Prims.op_Hat
                                                  "LHS not a conjunct: "
                                                  uu____1601
                                                 in
                                              Not_a_wp_implication uu____1599
                                               in
                                            FStar_Exn.raise uu____1598
                                         in
                                      (match uu____1184 with
                                       | (labels1,lhs2) ->
                                           let uu____1634 =
                                             let uu____1644 =
                                               aux default_msg
                                                 FStar_Pervasives_Native.None
                                                 (FStar_Pervasives_Native.Some
                                                    post_name) labels1 rhs1
                                                in
                                             match uu____1644 with
                                             | (labels2,rhs2) ->
                                                 let uu____1676 =
                                                   FStar_SMTEncoding_Term.abstr
                                                     names1 rhs2
                                                    in
                                                 (labels2, uu____1676)
                                              in
                                           (match uu____1634 with
                                            | (labels2,rhs2) ->
                                                let body =
                                                  FStar_SMTEncoding_Term.mkImp
                                                    (lhs2, rhs2) rng
                                                   in
                                                let uu____1722 =
                                                  FStar_SMTEncoding_Term.mk
                                                    (FStar_SMTEncoding_Term.Quant
                                                       (FStar_SMTEncoding_Term.Forall,
                                                         pats, iopt, (post ::
                                                         sorts), body))
                                                    q1.FStar_SMTEncoding_Term.rng
                                                   in
                                                (labels2, uu____1722))))
                             | uu____1749 ->
                                 let uu____1750 =
                                   let uu____1752 =
                                     FStar_SMTEncoding_Term.print_smt_term
                                       arg
                                      in
                                   Prims.op_Hat "arg not a quant: "
                                     uu____1752
                                    in
                                 fallback uu____1750)) ()
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
                            FStar_SMTEncoding_Term.freevars = uu____1783;
                            FStar_SMTEncoding_Term.rng = rng;_})
                  when is_a_named_continuation lhs ->
                  let uu____1840 = FStar_Util.prefix sorts  in
                  (match uu____1840 with
                   | (sorts',post) ->
                       let new_post_name =
                         let uu____1864 =
                           let uu____1866 = FStar_Ident.next_id ()  in
                           FStar_All.pipe_left FStar_Util.string_of_int
                             uu____1866
                            in
                         Prims.op_Hat "^^post_condition_" uu____1864  in
                       let names1 =
                         let uu____1874 =
                           FStar_List.map
                             (fun s  ->
                                let uu____1880 =
                                  let uu____1886 =
                                    let uu____1888 =
                                      let uu____1890 = FStar_Ident.next_id ()
                                         in
                                      FStar_All.pipe_left
                                        FStar_Util.string_of_int uu____1890
                                       in
                                    Prims.op_Hat "^^" uu____1888  in
                                  (uu____1886, s)  in
                                FStar_SMTEncoding_Term.mk_fv uu____1880)
                             sorts'
                            in
                         let uu____1896 =
                           let uu____1899 =
                             FStar_SMTEncoding_Term.mk_fv
                               (new_post_name, post)
                              in
                           [uu____1899]  in
                         FStar_List.append uu____1874 uu____1896  in
                       let instantiation =
                         FStar_List.map FStar_SMTEncoding_Util.mkFreeV names1
                          in
                       let uu____1910 =
                         let uu____1921 =
                           FStar_SMTEncoding_Term.inst instantiation lhs  in
                         let uu____1928 =
                           FStar_SMTEncoding_Term.inst instantiation rhs  in
                         (uu____1921, uu____1928)  in
                       (match uu____1910 with
                        | (lhs1,rhs1) ->
                            let uu____1964 =
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
                                                = uu____2017;
                                              FStar_SMTEncoding_Term.rng =
                                                uu____2018;_}::[])::[],iopt,sorts1,
                                          {
                                            FStar_SMTEncoding_Term.tm =
                                              FStar_SMTEncoding_Term.App
                                              (FStar_SMTEncoding_Term.Imp
                                               ,l0::r1::[]);
                                            FStar_SMTEncoding_Term.freevars =
                                              uu____2023;
                                            FStar_SMTEncoding_Term.rng =
                                              uu____2024;_})
                                         ->
                                         let uu____2120 =
                                           is_a_post_condition
                                             (FStar_Pervasives_Native.Some
                                                new_post_name) r1
                                            in
                                         if uu____2120
                                         then
                                           let uu____2133 =
                                             aux default_msg
                                               FStar_Pervasives_Native.None
                                               post_name_opt labels1 l0
                                              in
                                           (match uu____2133 with
                                            | (labels2,l) ->
                                                let uu____2164 =
                                                  let uu____2171 =
                                                    let uu____2172 =
                                                      let uu____2198 =
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
                                                        sorts1, uu____2198)
                                                       in
                                                    FStar_SMTEncoding_Term.Quant
                                                      uu____2172
                                                     in
                                                  FStar_SMTEncoding_Term.mk
                                                    uu____2171
                                                    q1.FStar_SMTEncoding_Term.rng
                                                   in
                                                (labels2, uu____2164))
                                         else (labels1, tm)
                                     | uu____2267 -> (labels1, tm)) labels
                                (conjuncts lhs1)
                               in
                            (match uu____1964 with
                             | (labels1,lhs_conjs) ->
                                 let uu____2298 =
                                   aux default_msg
                                     FStar_Pervasives_Native.None
                                     (FStar_Pervasives_Native.Some
                                        new_post_name) labels1 rhs1
                                    in
                                 (match uu____2298 with
                                  | (labels2,rhs2) ->
                                      let body =
                                        let uu____2337 =
                                          let uu____2344 =
                                            let uu____2355 =
                                              FStar_SMTEncoding_Term.mk_and_l
                                                lhs_conjs
                                                lhs1.FStar_SMTEncoding_Term.rng
                                               in
                                            (uu____2355, rhs2)  in
                                          FStar_SMTEncoding_Term.mkImp
                                            uu____2344 rng
                                           in
                                        FStar_All.pipe_right uu____2337
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
                  let uu____2429 =
                    aux default_msg ropt post_name_opt labels rhs  in
                  (match uu____2429 with
                   | (labels1,rhs1) ->
                       let uu____2460 =
                         FStar_SMTEncoding_Util.mkImp (lhs, rhs1)  in
                       (labels1, uu____2460))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.And ,conjuncts1) ->
                  let uu____2489 =
                    FStar_Util.fold_map (aux default_msg ropt post_name_opt)
                      labels conjuncts1
                     in
                  (match uu____2489 with
                   | (labels1,conjuncts2) ->
                       let uu____2534 =
                         FStar_SMTEncoding_Term.mk_and_l conjuncts2
                           q1.FStar_SMTEncoding_Term.rng
                          in
                       (labels1, uu____2534))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.ITE ,hd1::q11::q2::[]) ->
                  let uu____2575 =
                    aux default_msg ropt post_name_opt labels q11  in
                  (match uu____2575 with
                   | (labels1,q12) ->
                       let uu____2606 =
                         aux default_msg ropt post_name_opt labels1 q2  in
                       (match uu____2606 with
                        | (labels2,q21) ->
                            let uu____2637 =
                              FStar_SMTEncoding_Term.mkITE (hd1, q12, q21)
                                q1.FStar_SMTEncoding_Term.rng
                               in
                            (labels2, uu____2637)))
              | FStar_SMTEncoding_Term.Quant
                  (FStar_SMTEncoding_Term.Exists
                   ,uu____2658,uu____2659,uu____2660,uu____2661)
                  ->
                  let uu____2692 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____2692 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Iff ,uu____2722) ->
                  let uu____2733 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____2733 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Or ,uu____2763) ->
                  let uu____2774 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____2774 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Var uu____2804,uu____2805) when
                  is_a_post_condition post_name_opt q1 -> (labels, q1)
              | FStar_SMTEncoding_Term.FreeV uu____2822 ->
                  let uu____2831 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____2831 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.TrueOp ,uu____2861) ->
                  let uu____2872 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____2872 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.FalseOp ,uu____2902) ->
                  let uu____2913 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____2913 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Not ,uu____2943) ->
                  let uu____2954 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____2954 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Eq ,uu____2984) ->
                  let uu____2995 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____2995 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.LT ,uu____3025) ->
                  let uu____3036 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____3036 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.LTE ,uu____3066) ->
                  let uu____3077 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____3077 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.GT ,uu____3107) ->
                  let uu____3118 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____3118 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.GTE ,uu____3148) ->
                  let uu____3159 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____3159 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvUlt ,uu____3189) ->
                  let uu____3200 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____3200 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Var uu____3230,uu____3231) ->
                  let uu____3243 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____3243 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.RealDiv ,uu____3273) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Add ,uu____3294) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Sub ,uu____3315) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Div ,uu____3336) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Mul ,uu____3357) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Minus ,uu____3378) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Mod ,uu____3399) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvAnd ,uu____3420) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvXor ,uu____3441) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvOr ,uu____3462) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvAdd ,uu____3483) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvSub ,uu____3504) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvShl ,uu____3525) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvShr ,uu____3546) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvUdiv ,uu____3567) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvMod ,uu____3588) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvMul ,uu____3609) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvUext uu____3630,uu____3631) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvToNat ,uu____3653) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.NatToBv uu____3674,uu____3675) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.ITE ,uu____3697) ->
                  failwith "Impossible: arity mismatch"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Imp ,uu____3718) ->
                  failwith "Impossible: arity mismatch"
              | FStar_SMTEncoding_Term.Quant
                  (FStar_SMTEncoding_Term.Forall ,pats,iopt,sorts,body) ->
                  let uu____3773 =
                    aux default_msg ropt post_name_opt labels body  in
                  (match uu____3773 with
                   | (labels1,body1) ->
                       let uu____3804 =
                         FStar_SMTEncoding_Term.mk
                           (FStar_SMTEncoding_Term.Quant
                              (FStar_SMTEncoding_Term.Forall, pats, iopt,
                                sorts, body1)) q1.FStar_SMTEncoding_Term.rng
                          in
                       (labels1, uu____3804))
              | FStar_SMTEncoding_Term.Let (es,body) ->
                  let uu____3849 =
                    aux default_msg ropt post_name_opt labels body  in
                  (match uu____3849 with
                   | (labels1,body1) ->
                       let uu____3880 =
                         FStar_SMTEncoding_Term.mkLet (es, body1)
                           q1.FStar_SMTEncoding_Term.rng
                          in
                       (labels1, uu____3880))
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
          let print_banner uu____4057 =
            let msg =
              let uu____4060 =
                let uu____4062 = FStar_TypeChecker_Env.get_range env  in
                FStar_Range.string_of_range uu____4062  in
              let uu____4063 = FStar_Util.string_of_int (Prims.parse_int "5")
                 in
              let uu____4066 =
                FStar_Util.string_of_int (FStar_List.length all_labels)  in
              FStar_Util.format4
                "Detailed %s report follows for %s\nTaking %s seconds per proof obligation (%s proofs in total)\n"
                (if hint_replay then "hint replay" else "error") uu____4060
                uu____4063 uu____4066
               in
            FStar_Util.print_error msg  in
          let print_result uu____4092 =
            match uu____4092 with
            | ((uu____4105,msg,r),success) ->
                if success
                then
                  let uu____4121 = FStar_Range.string_of_range r  in
                  FStar_Util.print1
                    "OK: proof obligation at %s was proven in isolation\n"
                    uu____4121
                else
                  if hint_replay
                  then
                    FStar_Errors.log_issue r
                      (FStar_Errors.Warning_HintFailedToReplayProof,
                        (Prims.op_Hat
                           "Hint failed to replay this sub-proof: " msg))
                  else
                    (let uu____4131 =
                       let uu____4137 =
                         let uu____4139 = FStar_Range.string_of_range r  in
                         FStar_Util.format2
                           "XX: proof obligation at %s failed\n\t%s\n"
                           uu____4139 msg
                          in
                       (FStar_Errors.Error_ProofObligationFailed, uu____4137)
                        in
                     FStar_Errors.log_issue r uu____4131)
             in
          let elim labs =
            FStar_All.pipe_right labs
              (FStar_List.map
                 (fun uu____4192  ->
                    match uu____4192 with
                    | (l,uu____4201,uu____4202) ->
                        let a =
                          let uu____4220 =
                            let uu____4227 =
                              let uu____4238 =
                                FStar_SMTEncoding_Util.mkFreeV l  in
                              (uu____4238, FStar_SMTEncoding_Util.mkTrue)  in
                            FStar_SMTEncoding_Util.mkEq uu____4227  in
                          let uu____4251 =
                            let uu____4253 = FStar_SMTEncoding_Term.fv_name l
                               in
                            Prims.op_Hat "@disable_label_" uu____4253  in
                          {
                            FStar_SMTEncoding_Term.assumption_term =
                              uu____4220;
                            FStar_SMTEncoding_Term.assumption_caption =
                              (FStar_Pervasives_Native.Some "Disabling label");
                            FStar_SMTEncoding_Term.assumption_name =
                              uu____4251;
                            FStar_SMTEncoding_Term.assumption_fact_ids = []
                          }  in
                        FStar_SMTEncoding_Term.Assume a))
             in
          let rec linear_check eliminated errors active =
            FStar_SMTEncoding_Z3.refresh ();
            (match active with
             | [] ->
                 let results =
                   let uu____4323 =
                     FStar_List.map (fun x  -> (x, true)) eliminated  in
                   let uu____4340 =
                     FStar_List.map (fun x  -> (x, false)) errors  in
                   FStar_List.append uu____4323 uu____4340  in
                 sort_labels results
             | hd1::tl1 ->
                 ((let uu____4367 =
                     FStar_Util.string_of_int (FStar_List.length active)  in
                   FStar_Util.print1 "%s, " uu____4367);
                  (let decls =
                     FStar_All.pipe_left elim
                       (FStar_List.append eliminated
                          (FStar_List.append errors tl1))
                      in
                   let result = askZ3 decls  in
                   match result.FStar_SMTEncoding_Z3.z3result_status with
                   | FStar_SMTEncoding_Z3.UNSAT uu____4409 ->
                       linear_check (hd1 :: eliminated) errors tl1
                   | uu____4410 ->
                       linear_check eliminated (hd1 :: errors) tl1)))
             in
          print_banner ();
          FStar_Options.set_option "z3rlimit"
            (FStar_Options.Int (Prims.parse_int "5"));
          (let res = linear_check [] [] all_labels  in
           FStar_Util.print_string "\n";
           FStar_All.pipe_right res (FStar_List.iter print_result);
           (let uu____4459 =
              FStar_Util.for_all FStar_Pervasives_Native.snd res  in
            if uu____4459
            then
              FStar_Util.print_string
                "Failed: the heuristic of trying each proof in isolation failed to identify a precise error\n"
            else ()))
  