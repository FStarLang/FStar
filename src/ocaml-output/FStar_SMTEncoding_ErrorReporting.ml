open Prims
exception Not_a_wp_implication of Prims.string 
let uu___is_Not_a_wp_implication : Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Not_a_wp_implication uu____7 -> true
    | uu____8 -> false
  
let __proj__Not_a_wp_implication__item__uu___ : Prims.exn -> Prims.string =
  fun projectee  ->
    match projectee with | Not_a_wp_implication uu____15 -> uu____15
  
type label = FStar_SMTEncoding_Term.error_label[@@deriving show]
type labels = FStar_SMTEncoding_Term.error_labels[@@deriving show]
let sort_labels :
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
  
let remove_dups :
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
let fresh_label :
  Prims.string ->
    FStar_Range.range ->
      FStar_SMTEncoding_Term.term ->
        (label,FStar_SMTEncoding_Term.term) FStar_Pervasives_Native.tuple2
  =
  let ctr = FStar_Util.mk_ref (Prims.parse_int "0")  in
  fun message  ->
    fun range  ->
      fun t  ->
        let l =
          FStar_Util.incr ctr;
          (let uu____277 =
             let uu____278 = FStar_ST.op_Bang ctr  in
             FStar_Util.string_of_int uu____278  in
           FStar_Util.format1 "label_%s" uu____277)
           in
        let lvar = (l, FStar_SMTEncoding_Term.Bool_sort)  in
        let label = (lvar, message, range)  in
        let lterm = FStar_SMTEncoding_Util.mkFreeV lvar  in
        let lt1 = FStar_SMTEncoding_Term.mkOr (lterm, t) range  in
        (label, lt1)
  
let label_goals :
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
          | (FStar_Pervasives_Native.None ,uu____420) -> false
          | (FStar_Pervasives_Native.Some nm,FStar_SMTEncoding_Term.FreeV
             (nm',uu____425)) -> nm = nm'
          | (uu____428,FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var "Valid",tm1::[])) ->
              is_a_post_condition post_name_opt tm1
          | (uu____436,FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var "ApplyTT",tm1::uu____438)) ->
              is_a_post_condition post_name_opt tm1
          | uu____447 -> false  in
        let conjuncts t =
          match t.FStar_SMTEncoding_Term.tm with
          | FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And ,cs) -> cs
          | uu____467 -> [t]  in
        let is_guard_free tm =
          match tm.FStar_SMTEncoding_Term.tm with
          | FStar_SMTEncoding_Term.Quant
              (FStar_SMTEncoding_Term.Forall
               ,({
                   FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App
                     (FStar_SMTEncoding_Term.Var "Prims.guard_free",p::[]);
                   FStar_SMTEncoding_Term.freevars = uu____473;
                   FStar_SMTEncoding_Term.rng = uu____474;_}::[])::[],iopt,uu____476,
               {
                 FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App
                   (FStar_SMTEncoding_Term.Iff ,l::r1::[]);
                 FStar_SMTEncoding_Term.freevars = uu____479;
                 FStar_SMTEncoding_Term.rng = uu____480;_})
              -> true
          | uu____517 -> false  in
        let is_a_named_continuation lhs =
          FStar_All.pipe_right (conjuncts lhs)
            (FStar_Util.for_some is_guard_free)
           in
        let uu____524 =
          match use_env_msg with
          | FStar_Pervasives_Native.None  -> (false, "")
          | FStar_Pervasives_Native.Some f ->
              let uu____540 = f ()  in (true, uu____540)
           in
        match uu____524 with
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
                    let uu____572 = FStar_Range.def_range rng  in
                    FStar_Range.set_def_range r1 uu____572
                 in
              fresh_label msg1 rng1 t  in
            let rec aux default_msg ropt post_name_opt labels q1 =
              match q1.FStar_SMTEncoding_Term.tm with
              | FStar_SMTEncoding_Term.BoundV uu____613 -> (labels, q1)
              | FStar_SMTEncoding_Term.Integer uu____616 -> (labels, q1)
              | FStar_SMTEncoding_Term.LblPos uu____619 ->
                  failwith "Impossible"
              | FStar_SMTEncoding_Term.Labeled
                  (arg,"could not prove post-condition",uu____631) ->
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
                                                     = uu____690;
                                                   FStar_SMTEncoding_Term.rng
                                                     = rng;_})
                         ->
                         let post_name =
                           let uu____719 =
                             let uu____720 = FStar_Syntax_Syntax.next_id ()
                                in
                             FStar_All.pipe_left FStar_Util.string_of_int
                               uu____720
                              in
                           Prims.strcat "^^post_condition_" uu____719  in
                         let names1 =
                           let uu____728 =
                             FStar_List.mapi
                               (fun i  ->
                                  fun s  ->
                                    let uu____744 =
                                      let uu____745 =
                                        FStar_Util.string_of_int i  in
                                      Prims.strcat "^^" uu____745  in
                                    (uu____744, s)) sorts
                              in
                           (post_name, post) :: uu____728  in
                         let instantiation =
                           FStar_List.map FStar_SMTEncoding_Util.mkFreeV
                             names1
                            in
                         let uu____757 =
                           let uu____762 =
                             FStar_SMTEncoding_Term.inst instantiation lhs
                              in
                           let uu____763 =
                             FStar_SMTEncoding_Term.inst instantiation rhs
                              in
                           (uu____762, uu____763)  in
                         (match uu____757 with
                          | (lhs1,rhs1) ->
                              let uu____772 =
                                match lhs1.FStar_SMTEncoding_Term.tm with
                                | FStar_SMTEncoding_Term.App
                                    (FStar_SMTEncoding_Term.And ,clauses_lhs)
                                    ->
                                    let uu____790 =
                                      FStar_Util.prefix clauses_lhs  in
                                    (match uu____790 with
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
                                                   = uu____820;
                                                 FStar_SMTEncoding_Term.rng =
                                                   rng_ens;_})
                                              when
                                              is_a_post_condition
                                                (FStar_Pervasives_Native.Some
                                                   post_name) post1
                                              ->
                                              let uu____848 =
                                                aux
                                                  "could not prove post-condition"
                                                  FStar_Pervasives_Native.None
                                                  (FStar_Pervasives_Native.Some
                                                     post_name) labels
                                                  ensures_conjuncts
                                                 in
                                              (match uu____848 with
                                               | (labels1,ensures_conjuncts1)
                                                   ->
                                                   let pats_ens1 =
                                                     match pats_ens with
                                                     | [] -> [[post1]]
                                                     | []::[] -> [[post1]]
                                                     | uu____890 -> pats_ens
                                                      in
                                                   let ens1 =
                                                     let uu____896 =
                                                       let uu____897 =
                                                         let uu____916 =
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
                                                           uu____916)
                                                          in
                                                       FStar_SMTEncoding_Term.Quant
                                                         uu____897
                                                        in
                                                     FStar_SMTEncoding_Term.mk
                                                       uu____896
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
                                                   let uu____930 =
                                                     FStar_SMTEncoding_Term.abstr
                                                       names1 lhs2
                                                      in
                                                   (labels1, uu____930))
                                          | uu____933 ->
                                              let uu____934 =
                                                let uu____935 =
                                                  let uu____936 =
                                                    let uu____937 =
                                                      let uu____938 =
                                                        FStar_SMTEncoding_Term.print_smt_term
                                                          ens
                                                         in
                                                      Prims.strcat "  ... "
                                                        uu____938
                                                       in
                                                    Prims.strcat post_name
                                                      uu____937
                                                     in
                                                  Prims.strcat
                                                    "Ensures clause doesn't match post name:  "
                                                    uu____936
                                                   in
                                                Not_a_wp_implication
                                                  uu____935
                                                 in
                                              FStar_Exn.raise uu____934))
                                | uu____945 ->
                                    let uu____946 =
                                      let uu____947 =
                                        let uu____948 =
                                          FStar_SMTEncoding_Term.print_smt_term
                                            lhs1
                                           in
                                        Prims.strcat "LHS not a conjunct: "
                                          uu____948
                                         in
                                      Not_a_wp_implication uu____947  in
                                    FStar_Exn.raise uu____946
                                 in
                              (match uu____772 with
                               | (labels1,lhs2) ->
                                   let uu____967 =
                                     let uu____974 =
                                       aux default_msg
                                         FStar_Pervasives_Native.None
                                         (FStar_Pervasives_Native.Some
                                            post_name) labels1 rhs1
                                        in
                                     match uu____974 with
                                     | (labels2,rhs2) ->
                                         let uu____993 =
                                           FStar_SMTEncoding_Term.abstr
                                             names1 rhs2
                                            in
                                         (labels2, uu____993)
                                      in
                                   (match uu____967 with
                                    | (labels2,rhs2) ->
                                        let body =
                                          FStar_SMTEncoding_Term.mkImp
                                            (lhs2, rhs2) rng
                                           in
                                        let uu____1009 =
                                          FStar_SMTEncoding_Term.mk
                                            (FStar_SMTEncoding_Term.Quant
                                               (FStar_SMTEncoding_Term.Forall,
                                                 pats, iopt, (post :: sorts),
                                                 body))
                                            q1.FStar_SMTEncoding_Term.rng
                                           in
                                        (labels2, uu____1009))))
                     | uu____1020 ->
                         let uu____1021 =
                           let uu____1022 =
                             FStar_SMTEncoding_Term.print_smt_term arg  in
                           Prims.strcat "arg not a quant: " uu____1022  in
                         fallback uu____1021
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
                               FStar_SMTEncoding_Term.freevars = uu____1039;
                               FStar_SMTEncoding_Term.rng = rng;_})
                  when is_a_named_continuation lhs ->
                  let post_name =
                    let uu____1062 =
                      let uu____1063 = FStar_Syntax_Syntax.next_id ()  in
                      FStar_All.pipe_left FStar_Util.string_of_int uu____1063
                       in
                    Prims.strcat "^^post_condition_" uu____1062  in
                  let names1 = (post_name, post)  in
                  let instantiation =
                    let uu____1072 = FStar_SMTEncoding_Util.mkFreeV names1
                       in
                    [uu____1072]  in
                  let uu____1073 =
                    let uu____1078 =
                      FStar_SMTEncoding_Term.inst instantiation lhs  in
                    let uu____1079 =
                      FStar_SMTEncoding_Term.inst instantiation rhs  in
                    (uu____1078, uu____1079)  in
                  (match uu____1073 with
                   | (lhs1,rhs1) ->
                       let uu____1088 =
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
                                           uu____1125;
                                         FStar_SMTEncoding_Term.rng =
                                           uu____1126;_}::[])::[],iopt,sorts,
                                     {
                                       FStar_SMTEncoding_Term.tm =
                                         FStar_SMTEncoding_Term.App
                                         (FStar_SMTEncoding_Term.Iff
                                          ,l::r1::[]);
                                       FStar_SMTEncoding_Term.freevars =
                                         uu____1131;
                                       FStar_SMTEncoding_Term.rng =
                                         uu____1132;_})
                                    ->
                                    let uu____1169 =
                                      aux default_msg
                                        FStar_Pervasives_Native.None
                                        post_name_opt labels1 r1
                                       in
                                    (match uu____1169 with
                                     | (labels2,r2) ->
                                         let uu____1188 =
                                           let uu____1189 =
                                             let uu____1190 =
                                               let uu____1209 =
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
                                                 sorts, uu____1209)
                                                in
                                             FStar_SMTEncoding_Term.Quant
                                               uu____1190
                                              in
                                           FStar_SMTEncoding_Term.mk
                                             uu____1189
                                             q1.FStar_SMTEncoding_Term.rng
                                            in
                                         (labels2, uu____1188))
                                | uu____1226 -> (labels1, tm)) labels
                           (conjuncts lhs1)
                          in
                       (match uu____1088 with
                        | (labels1,lhs_conjs) ->
                            let uu____1245 =
                              aux default_msg FStar_Pervasives_Native.None
                                (FStar_Pervasives_Native.Some post_name)
                                labels1 rhs1
                               in
                            (match uu____1245 with
                             | (labels2,rhs2) ->
                                 let body =
                                   let uu____1265 =
                                     let uu____1266 =
                                       let uu____1271 =
                                         FStar_SMTEncoding_Term.mk_and_l
                                           lhs_conjs
                                           lhs1.FStar_SMTEncoding_Term.rng
                                          in
                                       (uu____1271, rhs2)  in
                                     FStar_SMTEncoding_Term.mkImp uu____1266
                                       rng
                                      in
                                   FStar_All.pipe_right uu____1265
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
                  let uu____1297 =
                    aux default_msg ropt post_name_opt labels rhs  in
                  (match uu____1297 with
                   | (labels1,rhs1) ->
                       let uu____1316 =
                         FStar_SMTEncoding_Util.mkImp (lhs, rhs1)  in
                       (labels1, uu____1316))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.And ,conjuncts1) ->
                  let uu____1324 =
                    FStar_Util.fold_map (aux default_msg ropt post_name_opt)
                      labels conjuncts1
                     in
                  (match uu____1324 with
                   | (labels1,conjuncts2) ->
                       let uu____1351 =
                         FStar_SMTEncoding_Term.mk_and_l conjuncts2
                           q1.FStar_SMTEncoding_Term.rng
                          in
                       (labels1, uu____1351))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.ITE ,hd1::q11::q2::[]) ->
                  let uu____1359 =
                    aux default_msg ropt post_name_opt labels q11  in
                  (match uu____1359 with
                   | (labels1,q12) ->
                       let uu____1378 =
                         aux default_msg ropt post_name_opt labels1 q2  in
                       (match uu____1378 with
                        | (labels2,q21) ->
                            let uu____1397 =
                              FStar_SMTEncoding_Term.mkITE (hd1, q12, q21)
                                q1.FStar_SMTEncoding_Term.rng
                               in
                            (labels2, uu____1397)))
              | FStar_SMTEncoding_Term.Quant
                  (FStar_SMTEncoding_Term.Exists
                   ,uu____1400,uu____1401,uu____1402,uu____1403)
                  ->
                  let uu____1420 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____1420 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Iff ,uu____1435) ->
                  let uu____1440 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____1440 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Or ,uu____1455) ->
                  let uu____1460 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____1460 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Var uu____1475,uu____1476) when
                  is_a_post_condition post_name_opt q1 -> (labels, q1)
              | FStar_SMTEncoding_Term.FreeV uu____1483 ->
                  let uu____1488 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____1488 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.TrueOp ,uu____1503) ->
                  let uu____1508 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____1508 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.FalseOp ,uu____1523) ->
                  let uu____1528 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____1528 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Not ,uu____1543) ->
                  let uu____1548 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____1548 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Eq ,uu____1563) ->
                  let uu____1568 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____1568 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.LT ,uu____1583) ->
                  let uu____1588 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____1588 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.LTE ,uu____1603) ->
                  let uu____1608 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____1608 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.GT ,uu____1623) ->
                  let uu____1628 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____1628 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.GTE ,uu____1643) ->
                  let uu____1648 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____1648 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvUlt ,uu____1663) ->
                  let uu____1668 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____1668 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Var uu____1683,uu____1684) ->
                  let uu____1689 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____1689 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Add ,uu____1704) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Sub ,uu____1715) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Div ,uu____1726) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Mul ,uu____1737) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Minus ,uu____1748) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Mod ,uu____1759) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvAnd ,uu____1770) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvXor ,uu____1781) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvOr ,uu____1792) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvAdd ,uu____1803) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvSub ,uu____1814) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvShl ,uu____1825) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvShr ,uu____1836) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvUdiv ,uu____1847) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvMod ,uu____1858) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvMul ,uu____1869) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvUext uu____1880,uu____1881) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvToNat ,uu____1892) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.NatToBv uu____1903,uu____1904) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.ITE ,uu____1915) ->
                  failwith "Impossible: arity mismatch"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Imp ,uu____1926) ->
                  failwith "Impossible: arity mismatch"
              | FStar_SMTEncoding_Term.Quant
                  (FStar_SMTEncoding_Term.Forall ,pats,iopt,sorts,body) ->
                  let uu____1957 =
                    aux default_msg ropt post_name_opt labels body  in
                  (match uu____1957 with
                   | (labels1,body1) ->
                       let uu____1976 =
                         FStar_SMTEncoding_Term.mk
                           (FStar_SMTEncoding_Term.Quant
                              (FStar_SMTEncoding_Term.Forall, pats, iopt,
                                sorts, body1)) q1.FStar_SMTEncoding_Term.rng
                          in
                       (labels1, uu____1976))
              | FStar_SMTEncoding_Term.Let (es,body) ->
                  let uu____1993 =
                    aux default_msg ropt post_name_opt labels body  in
                  (match uu____1993 with
                   | (labels1,body1) ->
                       let uu____2012 =
                         FStar_SMTEncoding_Term.mkLet (es, body1)
                           q1.FStar_SMTEncoding_Term.rng
                          in
                       (labels1, uu____2012))
               in
            aux "assertion failed" FStar_Pervasives_Native.None
              FStar_Pervasives_Native.None [] q
  
let detail_errors :
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
          let print_banner uu____2037 =
            let msg =
              let uu____2039 =
                let uu____2040 = FStar_TypeChecker_Env.get_range env  in
                FStar_Range.string_of_range uu____2040  in
              let uu____2041 = FStar_Util.string_of_int (Prims.parse_int "5")
                 in
              let uu____2042 =
                FStar_Util.string_of_int (FStar_List.length all_labels)  in
              FStar_Util.format4
                "Detailed %s report follows for %s\nTaking %s seconds per proof obligation (%s proofs in total)\n"
                (if hint_replay then "hint replay" else "error") uu____2039
                uu____2041 uu____2042
               in
            FStar_Util.print_error msg  in
          let print_result uu____2057 =
            match uu____2057 with
            | ((uu____2068,msg,r),success) ->
                if success
                then
                  let uu____2078 = FStar_Range.string_of_range r  in
                  FStar_Util.print1 "OK: proof obligation at %s was proven\n"
                    uu____2078
                else
                  if hint_replay
                  then
                    FStar_Errors.log_issue r
                      (FStar_Errors.Warning_HintFailedToReplayProof,
                        (Prims.strcat
                           "Hint failed to replay this sub-proof: " msg))
                  else
                    (let uu____2081 =
                       let uu____2086 =
                         let uu____2087 = FStar_Range.string_of_range r  in
                         FStar_Util.format2
                           "XX: proof obligation at %s failed\n\t%s\n"
                           uu____2087 msg
                          in
                       (FStar_Errors.Error_ProofObligationFailed, uu____2086)
                        in
                     FStar_Errors.log_issue r uu____2081)
             in
          let elim labs =
            FStar_All.pipe_right labs
              (FStar_List.map
                 (fun uu____2147  ->
                    match uu____2147 with
                    | (l,uu____2159,uu____2160) ->
                        let a =
                          let uu____2170 =
                            let uu____2171 =
                              let uu____2176 =
                                FStar_SMTEncoding_Util.mkFreeV l  in
                              (uu____2176, FStar_SMTEncoding_Util.mkTrue)  in
                            FStar_SMTEncoding_Util.mkEq uu____2171  in
                          {
                            FStar_SMTEncoding_Term.assumption_term =
                              uu____2170;
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
                   let uu____2231 =
                     FStar_List.map (fun x  -> (x, true)) eliminated  in
                   let uu____2244 =
                     FStar_List.map (fun x  -> (x, false)) errors  in
                   FStar_List.append uu____2231 uu____2244  in
                 sort_labels results
             | hd1::tl1 ->
                 ((let uu____2266 =
                     FStar_Util.string_of_int (FStar_List.length active)  in
                   FStar_Util.print1 "%s, " uu____2266);
                  (let decls =
                     FStar_All.pipe_left elim
                       (FStar_List.append eliminated
                          (FStar_List.append errors tl1))
                      in
                   let result = askZ3 decls  in
                   match result.FStar_SMTEncoding_Z3.z3result_status with
                   | FStar_SMTEncoding_Z3.UNSAT uu____2297 ->
                       linear_check (hd1 :: eliminated) errors tl1
                   | uu____2298 ->
                       linear_check eliminated (hd1 :: errors) tl1)))
             in
          print_banner ();
          FStar_Options.set_option "z3rlimit"
            (FStar_Options.Int (Prims.parse_int "5"));
          (let res = linear_check [] [] all_labels  in
           FStar_Util.print_string "\n";
           FStar_All.pipe_right res (FStar_List.iter print_result))
  