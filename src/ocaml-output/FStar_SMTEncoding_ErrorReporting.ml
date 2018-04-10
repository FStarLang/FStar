open Prims
exception Not_a_wp_implication of Prims.string 
let (uu___is_Not_a_wp_implication : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Not_a_wp_implication uu____9 -> true
    | uu____10 -> false
  
let (__proj__Not_a_wp_implication__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | Not_a_wp_implication uu____17 -> uu____17
  
type label = FStar_SMTEncoding_Term.error_label[@@deriving show]
type labels = FStar_SMTEncoding_Term.error_labels[@@deriving show]
let (sort_labels :
  (FStar_SMTEncoding_Term.error_label,Prims.bool)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    ((FStar_SMTEncoding_Term.fv,Prims.string,FStar_Range.range)
       FStar_Pervasives_Native.tuple3,Prims.bool)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun l  ->
    FStar_List.sortWith
      (fun uu____67  ->
         fun uu____68  ->
           match (uu____67, uu____68) with
           | (((uu____109,uu____110,r1),uu____112),((uu____113,uu____114,r2),uu____116))
               -> FStar_Range.compare r1 r2) l
  
let (remove_dups :
  labels ->
    (FStar_SMTEncoding_Term.fv,Prims.string,FStar_Range.range)
      FStar_Pervasives_Native.tuple3 Prims.list)
  =
  fun l  ->
    FStar_Util.remove_dups
      (fun uu____176  ->
         fun uu____177  ->
           match (uu____176, uu____177) with
           | ((uu____202,m1,r1),(uu____205,m2,r2)) -> (r1 = r2) && (m1 = m2))
      l
  
type msg = (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2
[@@deriving show]
type ranges =
  (Prims.string FStar_Pervasives_Native.option,FStar_Range.range)
    FStar_Pervasives_Native.tuple2 Prims.list[@@deriving show]
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
          let uu____255 = FStar_Util.incr ctr  in
          let uu____289 =
            let uu____290 = FStar_ST.op_Bang ctr  in
            FStar_Util.string_of_int uu____290  in
          FStar_Util.format1 "label_%s" uu____289  in
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
          | (FStar_Pervasives_Native.None ,uu____415) -> false
          | (FStar_Pervasives_Native.Some nm,FStar_SMTEncoding_Term.FreeV
             (nm',uu____420)) -> nm = nm'
          | (uu____423,FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var "Valid",tm1::[])) ->
              is_a_post_condition post_name_opt tm1
          | (uu____431,FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var "ApplyTT",tm1::uu____433)) ->
              is_a_post_condition post_name_opt tm1
          | uu____442 -> false  in
        let conjuncts t =
          match t.FStar_SMTEncoding_Term.tm with
          | FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And ,cs) -> cs
          | uu____463 -> [t]  in
        let is_guard_free tm =
          match tm.FStar_SMTEncoding_Term.tm with
          | FStar_SMTEncoding_Term.Quant
              (FStar_SMTEncoding_Term.Forall
               ,({
                   FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App
                     (FStar_SMTEncoding_Term.Var "Prims.guard_free",p::[]);
                   FStar_SMTEncoding_Term.freevars = uu____470;
                   FStar_SMTEncoding_Term.rng = uu____471;_}::[])::[],iopt,uu____473,
               {
                 FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App
                   (FStar_SMTEncoding_Term.Iff ,l::r1::[]);
                 FStar_SMTEncoding_Term.freevars = uu____476;
                 FStar_SMTEncoding_Term.rng = uu____477;_})
              -> true
          | uu____514 -> false  in
        let is_a_named_continuation lhs =
          FStar_All.pipe_right (conjuncts lhs)
            (FStar_Util.for_some is_guard_free)
           in
        let uu____522 =
          match use_env_msg with
          | FStar_Pervasives_Native.None  -> (false, "")
          | FStar_Pervasives_Native.Some f ->
              let uu____541 = f ()  in (true, uu____541)
           in
        match uu____522 with
        | (flag,msg_prefix) ->
            let fresh_label1 msg ropt rng t =
              let msg1 =
                if flag
                then Prims.strcat "Failed to verify implicit argument: " msg
                else msg  in
              let rng1 =
                match ropt with
                | FStar_Pervasives_Native.None  -> rng
                | FStar_Pervasives_Native.Some r1 ->
                    let uu____577 = FStar_Range.def_range rng  in
                    FStar_Range.set_def_range r1 uu____577
                 in
              fresh_label msg1 rng1 t  in
            let rec aux default_msg ropt post_name_opt labels q1 =
              match q1.FStar_SMTEncoding_Term.tm with
              | FStar_SMTEncoding_Term.BoundV uu____623 -> (labels, q1)
              | FStar_SMTEncoding_Term.Integer uu____626 -> (labels, q1)
              | FStar_SMTEncoding_Term.LblPos uu____629 ->
                  failwith "Impossible"
              | FStar_SMTEncoding_Term.Labeled
                  (arg,"could not prove post-condition",uu____641) ->
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
                                                     = uu____701;
                                                   FStar_SMTEncoding_Term.rng
                                                     = rng;_})
                         ->
                         let post_name =
                           let uu____730 =
                             let uu____731 = FStar_Syntax_Syntax.next_id ()
                                in
                             FStar_All.pipe_left FStar_Util.string_of_int
                               uu____731
                              in
                           Prims.strcat "^^post_condition_" uu____730  in
                         let names1 =
                           let uu____739 =
                             FStar_List.mapi
                               (fun i  ->
                                  fun s  ->
                                    let uu____755 =
                                      let uu____756 =
                                        FStar_Util.string_of_int i  in
                                      Prims.strcat "^^" uu____756  in
                                    (uu____755, s)) sorts
                              in
                           (post_name, post) :: uu____739  in
                         let instantiation =
                           FStar_List.map FStar_SMTEncoding_Util.mkFreeV
                             names1
                            in
                         let uu____768 =
                           let uu____773 =
                             FStar_SMTEncoding_Term.inst instantiation lhs
                              in
                           let uu____774 =
                             FStar_SMTEncoding_Term.inst instantiation rhs
                              in
                           (uu____773, uu____774)  in
                         (match uu____768 with
                          | (lhs1,rhs1) ->
                              let uu____783 =
                                match lhs1.FStar_SMTEncoding_Term.tm with
                                | FStar_SMTEncoding_Term.App
                                    (FStar_SMTEncoding_Term.And ,clauses_lhs)
                                    ->
                                    let uu____801 =
                                      FStar_Util.prefix clauses_lhs  in
                                    (match uu____801 with
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
                                                   = uu____831;
                                                 FStar_SMTEncoding_Term.rng =
                                                   rng_ens;_})
                                              when
                                              is_a_post_condition
                                                (FStar_Pervasives_Native.Some
                                                   post_name) post1
                                              ->
                                              let uu____859 =
                                                aux
                                                  "could not prove post-condition"
                                                  FStar_Pervasives_Native.None
                                                  (FStar_Pervasives_Native.Some
                                                     post_name) labels
                                                  ensures_conjuncts
                                                 in
                                              (match uu____859 with
                                               | (labels1,ensures_conjuncts1)
                                                   ->
                                                   let pats_ens1 =
                                                     match pats_ens with
                                                     | [] -> [[post1]]
                                                     | []::[] -> [[post1]]
                                                     | uu____901 -> pats_ens
                                                      in
                                                   let ens1 =
                                                     let uu____907 =
                                                       let uu____908 =
                                                         let uu____927 =
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
                                                           uu____927)
                                                          in
                                                       FStar_SMTEncoding_Term.Quant
                                                         uu____908
                                                        in
                                                     FStar_SMTEncoding_Term.mk
                                                       uu____907
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
                                                   let uu____941 =
                                                     FStar_SMTEncoding_Term.abstr
                                                       names1 lhs2
                                                      in
                                                   (labels1, uu____941))
                                          | uu____944 ->
                                              let uu____945 =
                                                let uu____946 =
                                                  let uu____947 =
                                                    let uu____948 =
                                                      let uu____949 =
                                                        FStar_SMTEncoding_Term.print_smt_term
                                                          ens
                                                         in
                                                      Prims.strcat "  ... "
                                                        uu____949
                                                       in
                                                    Prims.strcat post_name
                                                      uu____948
                                                     in
                                                  Prims.strcat
                                                    "Ensures clause doesn't match post name:  "
                                                    uu____947
                                                   in
                                                Not_a_wp_implication
                                                  uu____946
                                                 in
                                              FStar_Exn.raise uu____945))
                                | uu____956 ->
                                    let uu____957 =
                                      let uu____958 =
                                        let uu____959 =
                                          FStar_SMTEncoding_Term.print_smt_term
                                            lhs1
                                           in
                                        Prims.strcat "LHS not a conjunct: "
                                          uu____959
                                         in
                                      Not_a_wp_implication uu____958  in
                                    FStar_Exn.raise uu____957
                                 in
                              (match uu____783 with
                               | (labels1,lhs2) ->
                                   let uu____978 =
                                     let uu____985 =
                                       aux default_msg
                                         FStar_Pervasives_Native.None
                                         (FStar_Pervasives_Native.Some
                                            post_name) labels1 rhs1
                                        in
                                     match uu____985 with
                                     | (labels2,rhs2) ->
                                         let uu____1004 =
                                           FStar_SMTEncoding_Term.abstr
                                             names1 rhs2
                                            in
                                         (labels2, uu____1004)
                                      in
                                   (match uu____978 with
                                    | (labels2,rhs2) ->
                                        let body =
                                          FStar_SMTEncoding_Term.mkImp
                                            (lhs2, rhs2) rng
                                           in
                                        let uu____1020 =
                                          FStar_SMTEncoding_Term.mk
                                            (FStar_SMTEncoding_Term.Quant
                                               (FStar_SMTEncoding_Term.Forall,
                                                 pats, iopt, (post :: sorts),
                                                 body))
                                            q1.FStar_SMTEncoding_Term.rng
                                           in
                                        (labels2, uu____1020))))
                     | uu____1031 ->
                         let uu____1032 =
                           let uu____1033 =
                             FStar_SMTEncoding_Term.print_smt_term arg  in
                           Prims.strcat "arg not a quant: " uu____1033  in
                         fallback uu____1032
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
                               FStar_SMTEncoding_Term.freevars = uu____1050;
                               FStar_SMTEncoding_Term.rng = rng;_})
                  when is_a_named_continuation lhs ->
                  let post_name =
                    let uu____1073 =
                      let uu____1074 = FStar_Syntax_Syntax.next_id ()  in
                      FStar_All.pipe_left FStar_Util.string_of_int uu____1074
                       in
                    Prims.strcat "^^post_condition_" uu____1073  in
                  let names1 = (post_name, post)  in
                  let instantiation =
                    let uu____1083 = FStar_SMTEncoding_Util.mkFreeV names1
                       in
                    [uu____1083]  in
                  let uu____1084 =
                    let uu____1089 =
                      FStar_SMTEncoding_Term.inst instantiation lhs  in
                    let uu____1090 =
                      FStar_SMTEncoding_Term.inst instantiation rhs  in
                    (uu____1089, uu____1090)  in
                  (match uu____1084 with
                   | (lhs1,rhs1) ->
                       let uu____1099 =
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
                                           uu____1136;
                                         FStar_SMTEncoding_Term.rng =
                                           uu____1137;_}::[])::[],iopt,sorts,
                                     {
                                       FStar_SMTEncoding_Term.tm =
                                         FStar_SMTEncoding_Term.App
                                         (FStar_SMTEncoding_Term.Iff
                                          ,l::r1::[]);
                                       FStar_SMTEncoding_Term.freevars =
                                         uu____1142;
                                       FStar_SMTEncoding_Term.rng =
                                         uu____1143;_})
                                    ->
                                    let uu____1180 =
                                      aux default_msg
                                        FStar_Pervasives_Native.None
                                        post_name_opt labels1 r1
                                       in
                                    (match uu____1180 with
                                     | (labels2,r2) ->
                                         let uu____1199 =
                                           let uu____1200 =
                                             let uu____1201 =
                                               let uu____1220 =
                                                 FStar_SMTEncoding_Util.norng
                                                   FStar_SMTEncoding_Term.mk
                                                   (FStar_SMTEncoding_Term.App
                                                      (FStar_SMTEncoding_Term.Iff,
                                                        [l; r2]))
                                                  in
                                               (FStar_SMTEncoding_Term.Forall,
                                                 [[p]],
                                                 (FStar_Pervasives_Native.Some
                                                    (Prims.parse_int "0")),
                                                 sorts, uu____1220)
                                                in
                                             FStar_SMTEncoding_Term.Quant
                                               uu____1201
                                              in
                                           FStar_SMTEncoding_Term.mk
                                             uu____1200
                                             q1.FStar_SMTEncoding_Term.rng
                                            in
                                         (labels2, uu____1199))
                                | uu____1237 -> (labels1, tm)) labels
                           (conjuncts lhs1)
                          in
                       (match uu____1099 with
                        | (labels1,lhs_conjs) ->
                            let uu____1256 =
                              aux default_msg FStar_Pervasives_Native.None
                                (FStar_Pervasives_Native.Some post_name)
                                labels1 rhs1
                               in
                            (match uu____1256 with
                             | (labels2,rhs2) ->
                                 let body =
                                   let uu____1276 =
                                     let uu____1277 =
                                       let uu____1282 =
                                         FStar_SMTEncoding_Term.mk_and_l
                                           lhs_conjs
                                           lhs1.FStar_SMTEncoding_Term.rng
                                          in
                                       (uu____1282, rhs2)  in
                                     FStar_SMTEncoding_Term.mkImp uu____1277
                                       rng
                                      in
                                   FStar_All.pipe_right uu____1276
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
                  let uu____1308 =
                    aux default_msg ropt post_name_opt labels rhs  in
                  (match uu____1308 with
                   | (labels1,rhs1) ->
                       let uu____1327 =
                         FStar_SMTEncoding_Util.mkImp (lhs, rhs1)  in
                       (labels1, uu____1327))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.And ,conjuncts1) ->
                  let uu____1335 =
                    FStar_Util.fold_map (aux default_msg ropt post_name_opt)
                      labels conjuncts1
                     in
                  (match uu____1335 with
                   | (labels1,conjuncts2) ->
                       let uu____1362 =
                         FStar_SMTEncoding_Term.mk_and_l conjuncts2
                           q1.FStar_SMTEncoding_Term.rng
                          in
                       (labels1, uu____1362))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.ITE ,hd1::q11::q2::[]) ->
                  let uu____1370 =
                    aux default_msg ropt post_name_opt labels q11  in
                  (match uu____1370 with
                   | (labels1,q12) ->
                       let uu____1389 =
                         aux default_msg ropt post_name_opt labels1 q2  in
                       (match uu____1389 with
                        | (labels2,q21) ->
                            let uu____1408 =
                              FStar_SMTEncoding_Term.mkITE (hd1, q12, q21)
                                q1.FStar_SMTEncoding_Term.rng
                               in
                            (labels2, uu____1408)))
              | FStar_SMTEncoding_Term.Quant
                  (FStar_SMTEncoding_Term.Exists
                   ,uu____1411,uu____1412,uu____1413,uu____1414)
                  ->
                  let uu____1431 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____1431 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Iff ,uu____1446) ->
                  let uu____1451 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____1451 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Or ,uu____1466) ->
                  let uu____1471 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____1471 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Var uu____1486,uu____1487) when
                  is_a_post_condition post_name_opt q1 -> (labels, q1)
              | FStar_SMTEncoding_Term.FreeV uu____1494 ->
                  let uu____1499 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____1499 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.TrueOp ,uu____1514) ->
                  let uu____1519 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____1519 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.FalseOp ,uu____1534) ->
                  let uu____1539 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____1539 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Not ,uu____1554) ->
                  let uu____1559 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____1559 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Eq ,uu____1574) ->
                  let uu____1579 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____1579 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.LT ,uu____1594) ->
                  let uu____1599 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____1599 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.LTE ,uu____1614) ->
                  let uu____1619 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____1619 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.GT ,uu____1634) ->
                  let uu____1639 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____1639 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.GTE ,uu____1654) ->
                  let uu____1659 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____1659 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvUlt ,uu____1674) ->
                  let uu____1679 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____1679 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Var uu____1694,uu____1695) ->
                  let uu____1700 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____1700 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Add ,uu____1715) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Sub ,uu____1726) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Div ,uu____1737) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Mul ,uu____1748) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Minus ,uu____1759) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Mod ,uu____1770) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvAnd ,uu____1781) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvXor ,uu____1792) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvOr ,uu____1803) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvAdd ,uu____1814) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvSub ,uu____1825) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvShl ,uu____1836) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvShr ,uu____1847) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvUdiv ,uu____1858) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvMod ,uu____1869) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvMul ,uu____1880) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvUext uu____1891,uu____1892) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvToNat ,uu____1903) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.NatToBv uu____1914,uu____1915) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.ITE ,uu____1926) ->
                  failwith "Impossible: arity mismatch"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Imp ,uu____1937) ->
                  failwith "Impossible: arity mismatch"
              | FStar_SMTEncoding_Term.Quant
                  (FStar_SMTEncoding_Term.Forall ,pats,iopt,sorts,body) ->
                  let uu____1968 =
                    aux default_msg ropt post_name_opt labels body  in
                  (match uu____1968 with
                   | (labels1,body1) ->
                       let uu____1987 =
                         FStar_SMTEncoding_Term.mk
                           (FStar_SMTEncoding_Term.Quant
                              (FStar_SMTEncoding_Term.Forall, pats, iopt,
                                sorts, body1)) q1.FStar_SMTEncoding_Term.rng
                          in
                       (labels1, uu____1987))
              | FStar_SMTEncoding_Term.Let (es,body) ->
                  let uu____2004 =
                    aux default_msg ropt post_name_opt labels body  in
                  (match uu____2004 with
                   | (labels1,body1) ->
                       let uu____2023 =
                         FStar_SMTEncoding_Term.mkLet (es, body1)
                           q1.FStar_SMTEncoding_Term.rng
                          in
                       (labels1, uu____2023))
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
          let print_banner uu____2057 =
            let msg =
              let uu____2059 =
                let uu____2060 = FStar_TypeChecker_Env.get_range env  in
                FStar_Range.string_of_range uu____2060  in
              let uu____2061 = FStar_Util.string_of_int (Prims.parse_int "5")
                 in
              let uu____2062 =
                FStar_Util.string_of_int (FStar_List.length all_labels)  in
              FStar_Util.format4
                "Detailed %s report follows for %s\nTaking %s seconds per proof obligation (%s proofs in total)\n"
                (if hint_replay then "hint replay" else "error") uu____2059
                uu____2061 uu____2062
               in
            FStar_Util.print_error msg  in
          let print_result uu____2078 =
            match uu____2078 with
            | ((uu____2089,msg,r),success) ->
                if success
                then
                  let uu____2099 = FStar_Range.string_of_range r  in
                  FStar_Util.print1 "OK: proof obligation at %s was proven\n"
                    uu____2099
                else
                  if hint_replay
                  then
                    FStar_Errors.log_issue r
                      (FStar_Errors.Warning_HintFailedToReplayProof,
                        (Prims.strcat
                           "Hint failed to replay this sub-proof: " msg))
                  else
                    (let uu____2102 =
                       let uu____2107 =
                         let uu____2108 = FStar_Range.string_of_range r  in
                         FStar_Util.format2
                           "XX: proof obligation at %s failed\n\t%s\n"
                           uu____2108 msg
                          in
                       (FStar_Errors.Error_ProofObligationFailed, uu____2107)
                        in
                     FStar_Errors.log_issue r uu____2102)
             in
          let elim labs =
            FStar_All.pipe_right labs
              (FStar_List.map
                 (fun uu____2169  ->
                    match uu____2169 with
                    | (l,uu____2181,uu____2182) ->
                        let a =
                          let uu____2192 =
                            let uu____2193 =
                              let uu____2198 =
                                FStar_SMTEncoding_Util.mkFreeV l  in
                              (uu____2198, FStar_SMTEncoding_Util.mkTrue)  in
                            FStar_SMTEncoding_Util.mkEq uu____2193  in
                          {
                            FStar_SMTEncoding_Term.assumption_term =
                              uu____2192;
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
            let uu____2236 = FStar_SMTEncoding_Z3.refresh ()  in
            match active with
            | [] ->
                let results =
                  let uu____2256 =
                    FStar_List.map (fun x  -> (x, true)) eliminated  in
                  let uu____2269 =
                    FStar_List.map (fun x  -> (x, false)) errors  in
                  FStar_List.append uu____2256 uu____2269  in
                sort_labels results
            | hd1::tl1 ->
                let uu____2290 =
                  let uu____2291 =
                    FStar_Util.string_of_int (FStar_List.length active)  in
                  FStar_Util.print1 "%s, " uu____2291  in
                let decls =
                  FStar_All.pipe_left elim
                    (FStar_List.append eliminated
                       (FStar_List.append errors tl1))
                   in
                let result = askZ3 decls  in
                (match result.FStar_SMTEncoding_Z3.z3result_status with
                 | FStar_SMTEncoding_Z3.UNSAT uu____2322 ->
                     linear_check (hd1 :: eliminated) errors tl1
                 | uu____2323 -> linear_check eliminated (hd1 :: errors) tl1)
             in
          let uu____2324 = print_banner ()  in
          let uu____2325 =
            FStar_Options.set_option "z3rlimit"
              (FStar_Options.Int (Prims.parse_int "5"))
             in
          let res = linear_check [] [] all_labels  in
          let uu____2339 = FStar_Util.print_string "\n"  in
          FStar_All.pipe_right res (FStar_List.iter print_result)
  