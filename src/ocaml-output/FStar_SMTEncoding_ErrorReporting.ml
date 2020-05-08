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
  let ctr = FStar_Util.mk_ref Prims.int_zero  in
  fun message  ->
    fun range  ->
      fun t  ->
        let l =
          FStar_Util.incr ctr;
          (let uu____319 =
             let uu____321 = FStar_ST.op_Bang ctr  in
             FStar_Util.string_of_int uu____321  in
           FStar_Util.format1 "label_%s" uu____319)
           in
        let lvar =
          FStar_SMTEncoding_Term.mk_fv (l, FStar_SMTEncoding_Term.Bool_sort)
           in
        let label1 = (lvar, message, range)  in
        let lterm = FStar_SMTEncoding_Util.mkFreeV lvar  in
        let lt = FStar_SMTEncoding_Term.mkOr (lterm, t) range  in
        (label1, lt)
  
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
          | (FStar_Pervasives_Native.None ,uu____415) -> false
          | (FStar_Pervasives_Native.Some nm,FStar_SMTEncoding_Term.FreeV fv)
              ->
              let uu____436 = FStar_SMTEncoding_Term.fv_name fv  in
              nm = uu____436
          | (uu____439,FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var "Valid",tm1::[])) ->
              is_a_post_condition post_name_opt tm1
          | (uu____450,FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var "ApplyTT",tm1::uu____452)) ->
              is_a_post_condition post_name_opt tm1
          | uu____464 -> false  in
        let conjuncts t =
          match t.FStar_SMTEncoding_Term.tm with
          | FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And ,cs) -> cs
          | uu____488 -> [t]  in
        let is_guard_free tm =
          match tm.FStar_SMTEncoding_Term.tm with
          | FStar_SMTEncoding_Term.Quant
              (FStar_SMTEncoding_Term.Forall
               ,({
                   FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App
                     (FStar_SMTEncoding_Term.Var "Prims.guard_free",p::[]);
                   FStar_SMTEncoding_Term.freevars = uu____498;
                   FStar_SMTEncoding_Term.rng = uu____499;_}::[])::[],iopt,uu____501,
               {
                 FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App
                   (FStar_SMTEncoding_Term.Imp ,l::r1::[]);
                 FStar_SMTEncoding_Term.freevars = uu____504;
                 FStar_SMTEncoding_Term.rng = uu____505;_})
              -> true
          | uu____554 -> false  in
        let is_a_named_continuation lhs =
          FStar_All.pipe_right (conjuncts lhs)
            (FStar_Util.for_some is_guard_free)
           in
        let uu____566 =
          match use_env_msg with
          | FStar_Pervasives_Native.None  -> (false, "")
          | FStar_Pervasives_Native.Some f ->
              let uu____596 = f ()  in (true, uu____596)
           in
        match uu____566 with
        | (flag,msg_prefix) ->
            let fresh_label1 msg1 ropt rng t =
              let msg2 =
                if flag
                then
                  Prims.op_Hat "Failed to verify implicit argument: "
                    (Prims.op_Hat msg_prefix (Prims.op_Hat " :: " msg1))
                else msg1  in
              let rng1 =
                match ropt with
                | FStar_Pervasives_Native.None  -> rng
                | FStar_Pervasives_Native.Some r1 ->
                    let uu____652 =
                      let uu____654 = FStar_Range.use_range rng  in
                      let uu____655 = FStar_Range.use_range r1  in
                      FStar_Range.rng_included uu____654 uu____655  in
                    if uu____652
                    then rng
                    else
                      (let uu____659 = FStar_Range.def_range rng  in
                       FStar_Range.set_def_range r1 uu____659)
                 in
              fresh_label msg2 rng1 t  in
            let rec aux default_msg ropt post_name_opt labels1 q1 =
              match q1.FStar_SMTEncoding_Term.tm with
              | FStar_SMTEncoding_Term.BoundV uu____714 -> (labels1, q1)
              | FStar_SMTEncoding_Term.Integer uu____718 -> (labels1, q1)
              | FStar_SMTEncoding_Term.String uu____722 -> (labels1, q1)
              | FStar_SMTEncoding_Term.Real uu____726 -> (labels1, q1)
              | FStar_SMTEncoding_Term.LblPos uu____730 ->
                  failwith "Impossible"
              | FStar_SMTEncoding_Term.Labeled
                  (arg,"could not prove post-condition",uu____744) ->
                  let fallback msg1 =
                    aux default_msg ropt post_name_opt labels1 arg  in
                  (try
                     (fun uu___144_790  ->
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
                                                             = uu____809;
                                                           FStar_SMTEncoding_Term.rng
                                                             = rng;_})
                                 ->
                                 let post_name =
                                   let uu____845 =
                                     let uu____847 = FStar_Ident.next_id ()
                                        in
                                     FStar_All.pipe_left
                                       FStar_Util.string_of_int uu____847
                                      in
                                   Prims.op_Hat "^^post_condition_" uu____845
                                    in
                                 let names =
                                   let uu____855 =
                                     FStar_SMTEncoding_Term.mk_fv
                                       (post_name, post)
                                      in
                                   let uu____857 =
                                     FStar_List.map
                                       (fun s  ->
                                          let uu____863 =
                                            let uu____869 =
                                              let uu____871 =
                                                let uu____873 =
                                                  FStar_Ident.next_id ()  in
                                                FStar_All.pipe_left
                                                  FStar_Util.string_of_int
                                                  uu____873
                                                 in
                                              Prims.op_Hat "^^" uu____871  in
                                            (uu____869, s)  in
                                          FStar_SMTEncoding_Term.mk_fv
                                            uu____863) sorts
                                      in
                                   uu____855 :: uu____857  in
                                 let instantiation =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV names
                                    in
                                 let uu____882 =
                                   let uu____887 =
                                     FStar_SMTEncoding_Term.inst
                                       instantiation lhs
                                      in
                                   let uu____888 =
                                     FStar_SMTEncoding_Term.inst
                                       instantiation rhs
                                      in
                                   (uu____887, uu____888)  in
                                 (match uu____882 with
                                  | (lhs1,rhs1) ->
                                      let uu____897 =
                                        match lhs1.FStar_SMTEncoding_Term.tm
                                        with
                                        | FStar_SMTEncoding_Term.App
                                            (FStar_SMTEncoding_Term.And
                                             ,clauses_lhs)
                                            ->
                                            let uu____915 =
                                              FStar_Util.prefix clauses_lhs
                                               in
                                            (match uu____915 with
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
                                                           = uu____945;
                                                         FStar_SMTEncoding_Term.rng
                                                           = rng_ens;_})
                                                      ->
                                                      let uu____979 =
                                                        is_a_post_condition
                                                          (FStar_Pervasives_Native.Some
                                                             post_name) post1
                                                         in
                                                      if uu____979
                                                      then
                                                        let uu____989 =
                                                          aux
                                                            "could not prove post-condition"
                                                            FStar_Pervasives_Native.None
                                                            (FStar_Pervasives_Native.Some
                                                               post_name)
                                                            labels1
                                                            ensures_conjuncts
                                                           in
                                                        (match uu____989 with
                                                         | (labels2,ensures_conjuncts1)
                                                             ->
                                                             let pats_ens1 =
                                                               match pats_ens
                                                               with
                                                               | [] ->
                                                                   [[post1]]
                                                               | []::[] ->
                                                                   [[post1]]
                                                               | uu____1033
                                                                   ->
                                                                   pats_ens
                                                                in
                                                             let ens1 =
                                                               let uu____1039
                                                                 =
                                                                 let uu____1040
                                                                   =
                                                                   let uu____1060
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
                                                                    uu____1060)
                                                                    in
                                                                 FStar_SMTEncoding_Term.Quant
                                                                   uu____1040
                                                                  in
                                                               FStar_SMTEncoding_Term.mk
                                                                 uu____1039
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
                                                             let uu____1075 =
                                                               FStar_SMTEncoding_Term.abstr
                                                                 names lhs2
                                                                in
                                                             (labels2,
                                                               uu____1075))
                                                      else
                                                        (let uu____1080 =
                                                           let uu____1081 =
                                                             let uu____1083 =
                                                               let uu____1085
                                                                 =
                                                                 let uu____1087
                                                                   =
                                                                   FStar_SMTEncoding_Term.print_smt_term
                                                                    post1
                                                                    in
                                                                 Prims.op_Hat
                                                                   "  ... "
                                                                   uu____1087
                                                                  in
                                                               Prims.op_Hat
                                                                 post_name
                                                                 uu____1085
                                                                in
                                                             Prims.op_Hat
                                                               "Ensures clause doesn't match post name:  "
                                                               uu____1083
                                                              in
                                                           Not_a_wp_implication
                                                             uu____1081
                                                            in
                                                         FStar_Exn.raise
                                                           uu____1080)
                                                  | uu____1097 ->
                                                      let uu____1098 =
                                                        let uu____1099 =
                                                          let uu____1101 =
                                                            let uu____1103 =
                                                              let uu____1105
                                                                =
                                                                FStar_SMTEncoding_Term.print_smt_term
                                                                  ens
                                                                 in
                                                              Prims.op_Hat
                                                                "  ... "
                                                                uu____1105
                                                               in
                                                            Prims.op_Hat
                                                              post_name
                                                              uu____1103
                                                             in
                                                          Prims.op_Hat
                                                            "Ensures clause doesn't have the expected shape for post-condition "
                                                            uu____1101
                                                           in
                                                        Not_a_wp_implication
                                                          uu____1099
                                                         in
                                                      FStar_Exn.raise
                                                        uu____1098))
                                        | uu____1115 ->
                                            let uu____1116 =
                                              let uu____1117 =
                                                let uu____1119 =
                                                  FStar_SMTEncoding_Term.print_smt_term
                                                    lhs1
                                                   in
                                                Prims.op_Hat
                                                  "LHS not a conjunct: "
                                                  uu____1119
                                                 in
                                              Not_a_wp_implication uu____1117
                                               in
                                            FStar_Exn.raise uu____1116
                                         in
                                      (match uu____897 with
                                       | (labels2,lhs2) ->
                                           let uu____1140 =
                                             let uu____1147 =
                                               aux default_msg
                                                 FStar_Pervasives_Native.None
                                                 (FStar_Pervasives_Native.Some
                                                    post_name) labels2 rhs1
                                                in
                                             match uu____1147 with
                                             | (labels3,rhs2) ->
                                                 let uu____1167 =
                                                   FStar_SMTEncoding_Term.abstr
                                                     names rhs2
                                                    in
                                                 (labels3, uu____1167)
                                              in
                                           (match uu____1140 with
                                            | (labels3,rhs2) ->
                                                let body =
                                                  FStar_SMTEncoding_Term.mkImp
                                                    (lhs2, rhs2) rng
                                                   in
                                                let uu____1183 =
                                                  FStar_SMTEncoding_Term.mk
                                                    (FStar_SMTEncoding_Term.Quant
                                                       (FStar_SMTEncoding_Term.Forall,
                                                         pats, iopt, (post ::
                                                         sorts), body))
                                                    q1.FStar_SMTEncoding_Term.rng
                                                   in
                                                (labels3, uu____1183))))
                             | uu____1195 ->
                                 let uu____1196 =
                                   let uu____1198 =
                                     FStar_SMTEncoding_Term.print_smt_term
                                       arg
                                      in
                                   Prims.op_Hat "arg not a quant: "
                                     uu____1198
                                    in
                                 fallback uu____1196)) ()
                   with | Not_a_wp_implication msg1 -> fallback msg1)
              | FStar_SMTEncoding_Term.Labeled (arg,reason,r1) ->
                  aux reason (FStar_Pervasives_Native.Some r1) post_name_opt
                    labels1 arg
              | FStar_SMTEncoding_Term.Quant
                  (FStar_SMTEncoding_Term.Forall
                   ,[],FStar_Pervasives_Native.None
                   ,sorts,{
                            FStar_SMTEncoding_Term.tm =
                              FStar_SMTEncoding_Term.App
                              (FStar_SMTEncoding_Term.Imp ,lhs::rhs::[]);
                            FStar_SMTEncoding_Term.freevars = uu____1220;
                            FStar_SMTEncoding_Term.rng = rng;_})
                  when is_a_named_continuation lhs ->
                  let uu____1250 = FStar_Util.prefix sorts  in
                  (match uu____1250 with
                   | (sorts',post) ->
                       let new_post_name =
                         let uu____1271 =
                           let uu____1273 = FStar_Ident.next_id ()  in
                           FStar_All.pipe_left FStar_Util.string_of_int
                             uu____1273
                            in
                         Prims.op_Hat "^^post_condition_" uu____1271  in
                       let names =
                         let uu____1281 =
                           FStar_List.map
                             (fun s  ->
                                let uu____1287 =
                                  let uu____1293 =
                                    let uu____1295 =
                                      let uu____1297 = FStar_Ident.next_id ()
                                         in
                                      FStar_All.pipe_left
                                        FStar_Util.string_of_int uu____1297
                                       in
                                    Prims.op_Hat "^^" uu____1295  in
                                  (uu____1293, s)  in
                                FStar_SMTEncoding_Term.mk_fv uu____1287)
                             sorts'
                            in
                         let uu____1303 =
                           let uu____1306 =
                             FStar_SMTEncoding_Term.mk_fv
                               (new_post_name, post)
                              in
                           [uu____1306]  in
                         FStar_List.append uu____1281 uu____1303  in
                       let instantiation =
                         FStar_List.map FStar_SMTEncoding_Util.mkFreeV names
                          in
                       let uu____1311 =
                         let uu____1316 =
                           FStar_SMTEncoding_Term.inst instantiation lhs  in
                         let uu____1317 =
                           FStar_SMTEncoding_Term.inst instantiation rhs  in
                         (uu____1316, uu____1317)  in
                       (match uu____1311 with
                        | (lhs1,rhs1) ->
                            let uu____1326 =
                              FStar_Util.fold_map
                                (fun labels2  ->
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
                                                = uu____1364;
                                              FStar_SMTEncoding_Term.rng =
                                                uu____1365;_}::[])::[],iopt,sorts1,
                                          {
                                            FStar_SMTEncoding_Term.tm =
                                              FStar_SMTEncoding_Term.App
                                              (FStar_SMTEncoding_Term.Imp
                                               ,l0::r1::[]);
                                            FStar_SMTEncoding_Term.freevars =
                                              uu____1370;
                                            FStar_SMTEncoding_Term.rng =
                                              uu____1371;_})
                                         ->
                                         let uu____1419 =
                                           is_a_post_condition
                                             (FStar_Pervasives_Native.Some
                                                new_post_name) r1
                                            in
                                         if uu____1419
                                         then
                                           let uu____1429 =
                                             aux default_msg
                                               FStar_Pervasives_Native.None
                                               post_name_opt labels2 l0
                                              in
                                           (match uu____1429 with
                                            | (labels3,l) ->
                                                let uu____1448 =
                                                  let uu____1449 =
                                                    let uu____1450 =
                                                      let uu____1470 =
                                                        FStar_SMTEncoding_Util.norng
                                                          FStar_SMTEncoding_Term.mk
                                                          (FStar_SMTEncoding_Term.App
                                                             (FStar_SMTEncoding_Term.Imp,
                                                               [l; r1]))
                                                         in
                                                      (FStar_SMTEncoding_Term.Forall,
                                                        [[p]],
                                                        (FStar_Pervasives_Native.Some
                                                           Prims.int_zero),
                                                        sorts1, uu____1470)
                                                       in
                                                    FStar_SMTEncoding_Term.Quant
                                                      uu____1450
                                                     in
                                                  FStar_SMTEncoding_Term.mk
                                                    uu____1449
                                                    q1.FStar_SMTEncoding_Term.rng
                                                   in
                                                (labels3, uu____1448))
                                         else (labels2, tm)
                                     | uu____1494 -> (labels2, tm)) labels1
                                (conjuncts lhs1)
                               in
                            (match uu____1326 with
                             | (labels2,lhs_conjs) ->
                                 let uu____1513 =
                                   aux default_msg
                                     FStar_Pervasives_Native.None
                                     (FStar_Pervasives_Native.Some
                                        new_post_name) labels2 rhs1
                                    in
                                 (match uu____1513 with
                                  | (labels3,rhs2) ->
                                      let body =
                                        let uu____1534 =
                                          let uu____1535 =
                                            let uu____1540 =
                                              FStar_SMTEncoding_Term.mk_and_l
                                                lhs_conjs
                                                lhs1.FStar_SMTEncoding_Term.rng
                                               in
                                            (uu____1540, rhs2)  in
                                          FStar_SMTEncoding_Term.mkImp
                                            uu____1535 rng
                                           in
                                        FStar_All.pipe_right uu____1534
                                          (FStar_SMTEncoding_Term.abstr names)
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
                                      (labels3, q2)))))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Imp ,lhs::rhs::[]) ->
                  let uu____1560 =
                    aux default_msg ropt post_name_opt labels1 rhs  in
                  (match uu____1560 with
                   | (labels2,rhs1) ->
                       let uu____1579 =
                         FStar_SMTEncoding_Util.mkImp (lhs, rhs1)  in
                       (labels2, uu____1579))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.And ,conjuncts1) ->
                  let uu____1587 =
                    FStar_Util.fold_map (aux default_msg ropt post_name_opt)
                      labels1 conjuncts1
                     in
                  (match uu____1587 with
                   | (labels2,conjuncts2) ->
                       let uu____1614 =
                         FStar_SMTEncoding_Term.mk_and_l conjuncts2
                           q1.FStar_SMTEncoding_Term.rng
                          in
                       (labels2, uu____1614))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.ITE ,hd::q11::q2::[]) ->
                  let uu____1622 =
                    aux default_msg ropt post_name_opt labels1 q11  in
                  (match uu____1622 with
                   | (labels2,q12) ->
                       let uu____1641 =
                         aux default_msg ropt post_name_opt labels2 q2  in
                       (match uu____1641 with
                        | (labels3,q21) ->
                            let uu____1660 =
                              FStar_SMTEncoding_Term.mkITE (hd, q12, q21)
                                q1.FStar_SMTEncoding_Term.rng
                               in
                            (labels3, uu____1660)))
              | FStar_SMTEncoding_Term.Quant
                  (FStar_SMTEncoding_Term.Exists
                   ,uu____1663,uu____1664,uu____1665,uu____1666)
                  ->
                  let uu____1685 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____1685 with | (lab,q2) -> ((lab :: labels1), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Iff ,uu____1700) ->
                  let uu____1705 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____1705 with | (lab,q2) -> ((lab :: labels1), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Or ,uu____1720) ->
                  let uu____1725 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____1725 with | (lab,q2) -> ((lab :: labels1), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Var uu____1740,uu____1741) when
                  is_a_post_condition post_name_opt q1 -> (labels1, q1)
              | FStar_SMTEncoding_Term.FreeV uu____1749 ->
                  let uu____1758 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____1758 with | (lab,q2) -> ((lab :: labels1), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.TrueOp ,uu____1773) ->
                  let uu____1778 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____1778 with | (lab,q2) -> ((lab :: labels1), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.FalseOp ,uu____1793) ->
                  let uu____1798 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____1798 with | (lab,q2) -> ((lab :: labels1), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Not ,uu____1813) ->
                  let uu____1818 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____1818 with | (lab,q2) -> ((lab :: labels1), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Eq ,uu____1833) ->
                  let uu____1838 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____1838 with | (lab,q2) -> ((lab :: labels1), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.LT ,uu____1853) ->
                  let uu____1858 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____1858 with | (lab,q2) -> ((lab :: labels1), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.LTE ,uu____1873) ->
                  let uu____1878 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____1878 with | (lab,q2) -> ((lab :: labels1), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.GT ,uu____1893) ->
                  let uu____1898 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____1898 with | (lab,q2) -> ((lab :: labels1), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.GTE ,uu____1913) ->
                  let uu____1918 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____1918 with | (lab,q2) -> ((lab :: labels1), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvUlt ,uu____1933) ->
                  let uu____1938 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____1938 with | (lab,q2) -> ((lab :: labels1), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Var uu____1953,uu____1954) ->
                  let uu____1960 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____1960 with | (lab,q2) -> ((lab :: labels1), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.RealDiv ,uu____1975) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Add ,uu____1987) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Sub ,uu____1999) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Div ,uu____2011) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Mul ,uu____2023) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Minus ,uu____2035) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Mod ,uu____2047) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvAnd ,uu____2059) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvXor ,uu____2071) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvOr ,uu____2083) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvAdd ,uu____2095) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvSub ,uu____2107) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvShl ,uu____2119) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvShr ,uu____2131) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvUdiv ,uu____2143) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvMod ,uu____2155) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvMul ,uu____2167) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvUext uu____2179,uu____2180) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvToNat ,uu____2193) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.NatToBv uu____2205,uu____2206) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.ITE ,uu____2219) ->
                  failwith "Impossible: arity mismatch"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Imp ,uu____2231) ->
                  failwith "Impossible: arity mismatch"
              | FStar_SMTEncoding_Term.Quant
                  (FStar_SMTEncoding_Term.Forall ,pats,iopt,sorts,body) ->
                  let uu____2265 =
                    aux default_msg ropt post_name_opt labels1 body  in
                  (match uu____2265 with
                   | (labels2,body1) ->
                       let uu____2284 =
                         FStar_SMTEncoding_Term.mk
                           (FStar_SMTEncoding_Term.Quant
                              (FStar_SMTEncoding_Term.Forall, pats, iopt,
                                sorts, body1)) q1.FStar_SMTEncoding_Term.rng
                          in
                       (labels2, uu____2284))
              | FStar_SMTEncoding_Term.Let (es,body) ->
                  let uu____2302 =
                    aux default_msg ropt post_name_opt labels1 body  in
                  (match uu____2302 with
                   | (labels2,body1) ->
                       let uu____2321 =
                         FStar_SMTEncoding_Term.mkLet (es, body1)
                           q1.FStar_SMTEncoding_Term.rng
                          in
                       (labels2, uu____2321))
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
          let print_banner uu____2365 =
            let msg1 =
              let uu____2368 =
                let uu____2370 = FStar_TypeChecker_Env.get_range env  in
                FStar_Range.string_of_range uu____2370  in
              let uu____2371 = FStar_Util.string_of_int (Prims.of_int (5))
                 in
              let uu____2374 =
                FStar_Util.string_of_int (FStar_List.length all_labels)  in
              FStar_Util.format4
                "Detailed %s report follows for %s\nTaking %s seconds per proof obligation (%s proofs in total)\n"
                (if hint_replay then "hint replay" else "error") uu____2368
                uu____2371 uu____2374
               in
            FStar_Util.print_error msg1  in
          let print_result uu____2400 =
            match uu____2400 with
            | ((uu____2413,msg1,r),success) ->
                if success
                then
                  let uu____2429 = FStar_Range.string_of_range r  in
                  FStar_Util.print1
                    "OK: proof obligation at %s was proven in isolation\n"
                    uu____2429
                else
                  if hint_replay
                  then
                    FStar_Errors.log_issue r
                      (FStar_Errors.Warning_HintFailedToReplayProof,
                        (Prims.op_Hat
                           "Hint failed to replay this sub-proof: " msg1))
                  else
                    (let uu____2439 =
                       let uu____2445 =
                         let uu____2447 = FStar_Range.string_of_range r  in
                         FStar_Util.format2
                           "XX: proof obligation at %s failed\n\t%s\n"
                           uu____2447 msg1
                          in
                       (FStar_Errors.Error_ProofObligationFailed, uu____2445)
                        in
                     FStar_Errors.log_issue r uu____2439)
             in
          let elim labs =
            FStar_All.pipe_right labs
              (FStar_List.map
                 (fun uu____2500  ->
                    match uu____2500 with
                    | (l,uu____2509,uu____2510) ->
                        let a =
                          let uu____2514 =
                            let uu____2515 =
                              let uu____2520 =
                                FStar_SMTEncoding_Util.mkFreeV l  in
                              (uu____2520, FStar_SMTEncoding_Util.mkTrue)  in
                            FStar_SMTEncoding_Util.mkEq uu____2515  in
                          let uu____2521 =
                            let uu____2523 = FStar_SMTEncoding_Term.fv_name l
                               in
                            Prims.op_Hat "@disable_label_" uu____2523  in
                          {
                            FStar_SMTEncoding_Term.assumption_term =
                              uu____2514;
                            FStar_SMTEncoding_Term.assumption_caption =
                              (FStar_Pervasives_Native.Some "Disabling label");
                            FStar_SMTEncoding_Term.assumption_name =
                              uu____2521;
                            FStar_SMTEncoding_Term.assumption_fact_ids = []
                          }  in
                        FStar_SMTEncoding_Term.Assume a))
             in
          let rec linear_check eliminated errors active =
            FStar_SMTEncoding_Z3.refresh ();
            (match active with
             | [] ->
                 let results =
                   let uu____2593 =
                     FStar_List.map (fun x  -> (x, true)) eliminated  in
                   let uu____2610 =
                     FStar_List.map (fun x  -> (x, false)) errors  in
                   FStar_List.append uu____2593 uu____2610  in
                 sort_labels results
             | hd::tl ->
                 ((let uu____2637 =
                     FStar_Util.string_of_int (FStar_List.length active)  in
                   FStar_Util.print1 "%s, " uu____2637);
                  (let decls =
                     FStar_All.pipe_left elim
                       (FStar_List.append eliminated
                          (FStar_List.append errors tl))
                      in
                   let result = askZ3 decls  in
                   match result.FStar_SMTEncoding_Z3.z3result_status with
                   | FStar_SMTEncoding_Z3.UNSAT uu____2669 ->
                       linear_check (hd :: eliminated) errors tl
                   | uu____2670 -> linear_check eliminated (hd :: errors) tl)))
             in
          print_banner ();
          FStar_Options.set_option "z3rlimit"
            (FStar_Options.Int (Prims.of_int (5)));
          (let res = linear_check [] [] all_labels  in
           FStar_Util.print_string "\n";
           FStar_All.pipe_right res (FStar_List.iter print_result);
           (let uu____2719 =
              FStar_Util.for_all FStar_Pervasives_Native.snd res  in
            if uu____2719
            then
              FStar_Util.print_string
                "Failed: the heuristic of trying each proof in isolation failed to identify a precise error\n"
            else ()))
  