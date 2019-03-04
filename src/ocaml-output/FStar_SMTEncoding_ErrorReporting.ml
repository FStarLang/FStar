open Prims
exception Not_a_wp_implication of Prims.string 
let (uu___is_Not_a_wp_implication : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Not_a_wp_implication uu____68039 -> true
    | uu____68042 -> false
  
let (__proj__Not_a_wp_implication__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | Not_a_wp_implication uu____68053 -> uu____68053
  
type label = FStar_SMTEncoding_Term.error_label
type labels = FStar_SMTEncoding_Term.error_labels
let (sort_labels :
  (FStar_SMTEncoding_Term.error_label * Prims.bool) Prims.list ->
    ((FStar_SMTEncoding_Term.fv * Prims.string * FStar_Range.range) *
      Prims.bool) Prims.list)
  =
  fun l  ->
    FStar_List.sortWith
      (fun uu____68111  ->
         fun uu____68112  ->
           match (uu____68111, uu____68112) with
           | (((uu____68162,uu____68163,r1),uu____68165),((uu____68166,uu____68167,r2),uu____68169))
               -> FStar_Range.compare r1 r2) l
  
let (remove_dups :
  labels ->
    (FStar_SMTEncoding_Term.fv * Prims.string * FStar_Range.range) Prims.list)
  =
  fun l  ->
    FStar_Util.remove_dups
      (fun uu____68246  ->
         fun uu____68247  ->
           match (uu____68246, uu____68247) with
           | ((uu____68277,m1,r1),(uu____68280,m2,r2)) ->
               (r1 = r2) && (m1 = m2)) l
  
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
          (let uu____68380 =
             let uu____68382 = FStar_ST.op_Bang ctr  in
             FStar_Util.string_of_int uu____68382  in
           FStar_Util.format1 "label_%s" uu____68380)
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
          | (FStar_Pervasives_Native.None ,uu____68498) -> false
          | (FStar_Pervasives_Native.Some nm,FStar_SMTEncoding_Term.FreeV fv)
              ->
              let uu____68519 = FStar_SMTEncoding_Term.fv_name fv  in
              nm = uu____68519
          | (uu____68522,FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var "Valid",tm1::[])) ->
              is_a_post_condition post_name_opt tm1
          | (uu____68533,FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var "ApplyTT",tm1::uu____68535)) ->
              is_a_post_condition post_name_opt tm1
          | uu____68547 -> false  in
        let conjuncts t =
          match t.FStar_SMTEncoding_Term.tm with
          | FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And ,cs) -> cs
          | uu____68571 -> [t]  in
        let is_guard_free tm =
          match tm.FStar_SMTEncoding_Term.tm with
          | FStar_SMTEncoding_Term.Quant
              (FStar_SMTEncoding_Term.Forall
               ,({
                   FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App
                     (FStar_SMTEncoding_Term.Var "Prims.guard_free",p::[]);
                   FStar_SMTEncoding_Term.freevars = uu____68581;
                   FStar_SMTEncoding_Term.rng = uu____68582;_}::[])::[],iopt,uu____68584,
               {
                 FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App
                   (FStar_SMTEncoding_Term.Imp ,l::r1::[]);
                 FStar_SMTEncoding_Term.freevars = uu____68587;
                 FStar_SMTEncoding_Term.rng = uu____68588;_})
              -> true
          | uu____68637 -> false  in
        let is_a_named_continuation lhs =
          FStar_All.pipe_right (conjuncts lhs)
            (FStar_Util.for_some is_guard_free)
           in
        let uu____68649 =
          match use_env_msg with
          | FStar_Pervasives_Native.None  -> (false, "")
          | FStar_Pervasives_Native.Some f ->
              let uu____68679 = f ()  in (true, uu____68679)
           in
        match uu____68649 with
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
                    let uu____68735 =
                      let uu____68737 = FStar_Range.use_range rng  in
                      let uu____68738 = FStar_Range.use_range r1  in
                      FStar_Range.rng_included uu____68737 uu____68738  in
                    if uu____68735
                    then rng
                    else
                      (let uu____68742 = FStar_Range.def_range rng  in
                       FStar_Range.set_def_range r1 uu____68742)
                 in
              fresh_label msg1 rng1 t  in
            let rec aux default_msg ropt post_name_opt labels q1 =
              match q1.FStar_SMTEncoding_Term.tm with
              | FStar_SMTEncoding_Term.BoundV uu____68797 -> (labels, q1)
              | FStar_SMTEncoding_Term.Integer uu____68801 -> (labels, q1)
              | FStar_SMTEncoding_Term.Real uu____68805 -> (labels, q1)
              | FStar_SMTEncoding_Term.LblPos uu____68809 ->
                  failwith "Impossible"
              | FStar_SMTEncoding_Term.Labeled
                  (arg,"could not prove post-condition",uu____68823) ->
                  let fallback msg =
                    aux default_msg ropt post_name_opt labels arg  in
                  (try
                     (fun uu___747_68869  ->
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
                                                             = uu____68888;
                                                           FStar_SMTEncoding_Term.rng
                                                             = rng;_})
                                 ->
                                 let post_name =
                                   let uu____68924 =
                                     let uu____68926 = FStar_Ident.next_id ()
                                        in
                                     FStar_All.pipe_left
                                       FStar_Util.string_of_int uu____68926
                                      in
                                   Prims.op_Hat "^^post_condition_"
                                     uu____68924
                                    in
                                 let names1 =
                                   let uu____68934 =
                                     FStar_SMTEncoding_Term.mk_fv
                                       (post_name, post)
                                      in
                                   let uu____68936 =
                                     FStar_List.map
                                       (fun s  ->
                                          let uu____68942 =
                                            let uu____68948 =
                                              let uu____68950 =
                                                let uu____68952 =
                                                  FStar_Ident.next_id ()  in
                                                FStar_All.pipe_left
                                                  FStar_Util.string_of_int
                                                  uu____68952
                                                 in
                                              Prims.op_Hat "^^" uu____68950
                                               in
                                            (uu____68948, s)  in
                                          FStar_SMTEncoding_Term.mk_fv
                                            uu____68942) sorts
                                      in
                                   uu____68934 :: uu____68936  in
                                 let instantiation =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV names1
                                    in
                                 let uu____68961 =
                                   let uu____68966 =
                                     FStar_SMTEncoding_Term.inst
                                       instantiation lhs
                                      in
                                   let uu____68967 =
                                     FStar_SMTEncoding_Term.inst
                                       instantiation rhs
                                      in
                                   (uu____68966, uu____68967)  in
                                 (match uu____68961 with
                                  | (lhs1,rhs1) ->
                                      let uu____68976 =
                                        match lhs1.FStar_SMTEncoding_Term.tm
                                        with
                                        | FStar_SMTEncoding_Term.App
                                            (FStar_SMTEncoding_Term.And
                                             ,clauses_lhs)
                                            ->
                                            let uu____68994 =
                                              FStar_Util.prefix clauses_lhs
                                               in
                                            (match uu____68994 with
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
                                                           = uu____69024;
                                                         FStar_SMTEncoding_Term.rng
                                                           = rng_ens;_})
                                                      ->
                                                      let uu____69058 =
                                                        is_a_post_condition
                                                          (FStar_Pervasives_Native.Some
                                                             post_name) post1
                                                         in
                                                      if uu____69058
                                                      then
                                                        let uu____69068 =
                                                          aux
                                                            "could not prove post-condition"
                                                            FStar_Pervasives_Native.None
                                                            (FStar_Pervasives_Native.Some
                                                               post_name)
                                                            labels
                                                            ensures_conjuncts
                                                           in
                                                        (match uu____69068
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
                                                               | uu____69112
                                                                   ->
                                                                   pats_ens
                                                                in
                                                             let ens1 =
                                                               let uu____69118
                                                                 =
                                                                 let uu____69119
                                                                   =
                                                                   let uu____69139
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
                                                                    uu____69139)
                                                                    in
                                                                 FStar_SMTEncoding_Term.Quant
                                                                   uu____69119
                                                                  in
                                                               FStar_SMTEncoding_Term.mk
                                                                 uu____69118
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
                                                             let uu____69154
                                                               =
                                                               FStar_SMTEncoding_Term.abstr
                                                                 names1 lhs2
                                                                in
                                                             (labels1,
                                                               uu____69154))
                                                      else
                                                        (let uu____69159 =
                                                           let uu____69160 =
                                                             let uu____69162
                                                               =
                                                               let uu____69164
                                                                 =
                                                                 let uu____69166
                                                                   =
                                                                   FStar_SMTEncoding_Term.print_smt_term
                                                                    post1
                                                                    in
                                                                 Prims.op_Hat
                                                                   "  ... "
                                                                   uu____69166
                                                                  in
                                                               Prims.op_Hat
                                                                 post_name
                                                                 uu____69164
                                                                in
                                                             Prims.op_Hat
                                                               "Ensures clause doesn't match post name:  "
                                                               uu____69162
                                                              in
                                                           Not_a_wp_implication
                                                             uu____69160
                                                            in
                                                         FStar_Exn.raise
                                                           uu____69159)
                                                  | uu____69176 ->
                                                      let uu____69177 =
                                                        let uu____69178 =
                                                          let uu____69180 =
                                                            let uu____69182 =
                                                              let uu____69184
                                                                =
                                                                FStar_SMTEncoding_Term.print_smt_term
                                                                  ens
                                                                 in
                                                              Prims.op_Hat
                                                                "  ... "
                                                                uu____69184
                                                               in
                                                            Prims.op_Hat
                                                              post_name
                                                              uu____69182
                                                             in
                                                          Prims.op_Hat
                                                            "Ensures clause doesn't have the expected shape for post-condition "
                                                            uu____69180
                                                           in
                                                        Not_a_wp_implication
                                                          uu____69178
                                                         in
                                                      FStar_Exn.raise
                                                        uu____69177))
                                        | uu____69194 ->
                                            let uu____69195 =
                                              let uu____69196 =
                                                let uu____69198 =
                                                  FStar_SMTEncoding_Term.print_smt_term
                                                    lhs1
                                                   in
                                                Prims.op_Hat
                                                  "LHS not a conjunct: "
                                                  uu____69198
                                                 in
                                              Not_a_wp_implication
                                                uu____69196
                                               in
                                            FStar_Exn.raise uu____69195
                                         in
                                      (match uu____68976 with
                                       | (labels1,lhs2) ->
                                           let uu____69219 =
                                             let uu____69226 =
                                               aux default_msg
                                                 FStar_Pervasives_Native.None
                                                 (FStar_Pervasives_Native.Some
                                                    post_name) labels1 rhs1
                                                in
                                             match uu____69226 with
                                             | (labels2,rhs2) ->
                                                 let uu____69246 =
                                                   FStar_SMTEncoding_Term.abstr
                                                     names1 rhs2
                                                    in
                                                 (labels2, uu____69246)
                                              in
                                           (match uu____69219 with
                                            | (labels2,rhs2) ->
                                                let body =
                                                  FStar_SMTEncoding_Term.mkImp
                                                    (lhs2, rhs2) rng
                                                   in
                                                let uu____69262 =
                                                  FStar_SMTEncoding_Term.mk
                                                    (FStar_SMTEncoding_Term.Quant
                                                       (FStar_SMTEncoding_Term.Forall,
                                                         pats, iopt, (post ::
                                                         sorts), body))
                                                    q1.FStar_SMTEncoding_Term.rng
                                                   in
                                                (labels2, uu____69262))))
                             | uu____69274 ->
                                 let uu____69275 =
                                   let uu____69277 =
                                     FStar_SMTEncoding_Term.print_smt_term
                                       arg
                                      in
                                   Prims.op_Hat "arg not a quant: "
                                     uu____69277
                                    in
                                 fallback uu____69275)) ()
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
                            FStar_SMTEncoding_Term.freevars = uu____69299;
                            FStar_SMTEncoding_Term.rng = rng;_})
                  when is_a_named_continuation lhs ->
                  let uu____69329 = FStar_Util.prefix sorts  in
                  (match uu____69329 with
                   | (sorts',post) ->
                       let new_post_name =
                         let uu____69350 =
                           let uu____69352 = FStar_Ident.next_id ()  in
                           FStar_All.pipe_left FStar_Util.string_of_int
                             uu____69352
                            in
                         Prims.op_Hat "^^post_condition_" uu____69350  in
                       let names1 =
                         let uu____69360 =
                           FStar_List.map
                             (fun s  ->
                                let uu____69366 =
                                  let uu____69372 =
                                    let uu____69374 =
                                      let uu____69376 =
                                        FStar_Ident.next_id ()  in
                                      FStar_All.pipe_left
                                        FStar_Util.string_of_int uu____69376
                                       in
                                    Prims.op_Hat "^^" uu____69374  in
                                  (uu____69372, s)  in
                                FStar_SMTEncoding_Term.mk_fv uu____69366)
                             sorts'
                            in
                         let uu____69382 =
                           let uu____69385 =
                             FStar_SMTEncoding_Term.mk_fv
                               (new_post_name, post)
                              in
                           [uu____69385]  in
                         FStar_List.append uu____69360 uu____69382  in
                       let instantiation =
                         FStar_List.map FStar_SMTEncoding_Util.mkFreeV names1
                          in
                       let uu____69390 =
                         let uu____69395 =
                           FStar_SMTEncoding_Term.inst instantiation lhs  in
                         let uu____69396 =
                           FStar_SMTEncoding_Term.inst instantiation rhs  in
                         (uu____69395, uu____69396)  in
                       (match uu____69390 with
                        | (lhs1,rhs1) ->
                            let uu____69405 =
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
                                                = uu____69443;
                                              FStar_SMTEncoding_Term.rng =
                                                uu____69444;_}::[])::[],iopt,sorts1,
                                          {
                                            FStar_SMTEncoding_Term.tm =
                                              FStar_SMTEncoding_Term.App
                                              (FStar_SMTEncoding_Term.Imp
                                               ,l0::r1::[]);
                                            FStar_SMTEncoding_Term.freevars =
                                              uu____69449;
                                            FStar_SMTEncoding_Term.rng =
                                              uu____69450;_})
                                         ->
                                         let uu____69498 =
                                           is_a_post_condition
                                             (FStar_Pervasives_Native.Some
                                                new_post_name) r1
                                            in
                                         if uu____69498
                                         then
                                           let uu____69508 =
                                             aux default_msg
                                               FStar_Pervasives_Native.None
                                               post_name_opt labels1 l0
                                              in
                                           (match uu____69508 with
                                            | (labels2,l) ->
                                                let uu____69527 =
                                                  let uu____69528 =
                                                    let uu____69529 =
                                                      let uu____69549 =
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
                                                        sorts1, uu____69549)
                                                       in
                                                    FStar_SMTEncoding_Term.Quant
                                                      uu____69529
                                                     in
                                                  FStar_SMTEncoding_Term.mk
                                                    uu____69528
                                                    q1.FStar_SMTEncoding_Term.rng
                                                   in
                                                (labels2, uu____69527))
                                         else (labels1, tm)
                                     | uu____69573 -> (labels1, tm)) labels
                                (conjuncts lhs1)
                               in
                            (match uu____69405 with
                             | (labels1,lhs_conjs) ->
                                 let uu____69592 =
                                   aux default_msg
                                     FStar_Pervasives_Native.None
                                     (FStar_Pervasives_Native.Some
                                        new_post_name) labels1 rhs1
                                    in
                                 (match uu____69592 with
                                  | (labels2,rhs2) ->
                                      let body =
                                        let uu____69613 =
                                          let uu____69614 =
                                            let uu____69619 =
                                              FStar_SMTEncoding_Term.mk_and_l
                                                lhs_conjs
                                                lhs1.FStar_SMTEncoding_Term.rng
                                               in
                                            (uu____69619, rhs2)  in
                                          FStar_SMTEncoding_Term.mkImp
                                            uu____69614 rng
                                           in
                                        FStar_All.pipe_right uu____69613
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
                  let uu____69639 =
                    aux default_msg ropt post_name_opt labels rhs  in
                  (match uu____69639 with
                   | (labels1,rhs1) ->
                       let uu____69658 =
                         FStar_SMTEncoding_Util.mkImp (lhs, rhs1)  in
                       (labels1, uu____69658))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.And ,conjuncts1) ->
                  let uu____69666 =
                    FStar_Util.fold_map (aux default_msg ropt post_name_opt)
                      labels conjuncts1
                     in
                  (match uu____69666 with
                   | (labels1,conjuncts2) ->
                       let uu____69693 =
                         FStar_SMTEncoding_Term.mk_and_l conjuncts2
                           q1.FStar_SMTEncoding_Term.rng
                          in
                       (labels1, uu____69693))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.ITE ,hd1::q11::q2::[]) ->
                  let uu____69701 =
                    aux default_msg ropt post_name_opt labels q11  in
                  (match uu____69701 with
                   | (labels1,q12) ->
                       let uu____69720 =
                         aux default_msg ropt post_name_opt labels1 q2  in
                       (match uu____69720 with
                        | (labels2,q21) ->
                            let uu____69739 =
                              FStar_SMTEncoding_Term.mkITE (hd1, q12, q21)
                                q1.FStar_SMTEncoding_Term.rng
                               in
                            (labels2, uu____69739)))
              | FStar_SMTEncoding_Term.Quant
                  (FStar_SMTEncoding_Term.Exists
                   ,uu____69742,uu____69743,uu____69744,uu____69745)
                  ->
                  let uu____69764 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____69764 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Iff ,uu____69779) ->
                  let uu____69784 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____69784 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Or ,uu____69799) ->
                  let uu____69804 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____69804 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Var uu____69819,uu____69820) when
                  is_a_post_condition post_name_opt q1 -> (labels, q1)
              | FStar_SMTEncoding_Term.FreeV uu____69828 ->
                  let uu____69837 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____69837 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.TrueOp ,uu____69852) ->
                  let uu____69857 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____69857 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.FalseOp ,uu____69872) ->
                  let uu____69877 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____69877 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Not ,uu____69892) ->
                  let uu____69897 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____69897 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Eq ,uu____69912) ->
                  let uu____69917 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____69917 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.LT ,uu____69932) ->
                  let uu____69937 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____69937 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.LTE ,uu____69952) ->
                  let uu____69957 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____69957 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.GT ,uu____69972) ->
                  let uu____69977 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____69977 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.GTE ,uu____69992) ->
                  let uu____69997 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____69997 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvUlt ,uu____70012) ->
                  let uu____70017 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____70017 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Var uu____70032,uu____70033) ->
                  let uu____70039 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____70039 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.RealDiv ,uu____70054) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Add ,uu____70066) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Sub ,uu____70078) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Div ,uu____70090) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Mul ,uu____70102) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Minus ,uu____70114) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Mod ,uu____70126) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvAnd ,uu____70138) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvXor ,uu____70150) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvOr ,uu____70162) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvAdd ,uu____70174) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvSub ,uu____70186) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvShl ,uu____70198) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvShr ,uu____70210) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvUdiv ,uu____70222) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvMod ,uu____70234) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvMul ,uu____70246) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvUext uu____70258,uu____70259) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvToNat ,uu____70272) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.NatToBv uu____70284,uu____70285) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.ITE ,uu____70298) ->
                  failwith "Impossible: arity mismatch"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Imp ,uu____70310) ->
                  failwith "Impossible: arity mismatch"
              | FStar_SMTEncoding_Term.Quant
                  (FStar_SMTEncoding_Term.Forall ,pats,iopt,sorts,body) ->
                  let uu____70344 =
                    aux default_msg ropt post_name_opt labels body  in
                  (match uu____70344 with
                   | (labels1,body1) ->
                       let uu____70363 =
                         FStar_SMTEncoding_Term.mk
                           (FStar_SMTEncoding_Term.Quant
                              (FStar_SMTEncoding_Term.Forall, pats, iopt,
                                sorts, body1)) q1.FStar_SMTEncoding_Term.rng
                          in
                       (labels1, uu____70363))
              | FStar_SMTEncoding_Term.Let (es,body) ->
                  let uu____70381 =
                    aux default_msg ropt post_name_opt labels body  in
                  (match uu____70381 with
                   | (labels1,body1) ->
                       let uu____70400 =
                         FStar_SMTEncoding_Term.mkLet (es, body1)
                           q1.FStar_SMTEncoding_Term.rng
                          in
                       (labels1, uu____70400))
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
          let print_banner uu____70444 =
            let msg =
              let uu____70447 =
                let uu____70449 = FStar_TypeChecker_Env.get_range env  in
                FStar_Range.string_of_range uu____70449  in
              let uu____70450 =
                FStar_Util.string_of_int (Prims.parse_int "5")  in
              let uu____70453 =
                FStar_Util.string_of_int (FStar_List.length all_labels)  in
              FStar_Util.format4
                "Detailed %s report follows for %s\nTaking %s seconds per proof obligation (%s proofs in total)\n"
                (if hint_replay then "hint replay" else "error") uu____70447
                uu____70450 uu____70453
               in
            FStar_Util.print_error msg  in
          let print_result uu____70479 =
            match uu____70479 with
            | ((uu____70492,msg,r),success) ->
                if success
                then
                  let uu____70508 = FStar_Range.string_of_range r  in
                  FStar_Util.print1
                    "OK: proof obligation at %s was proven in isolation\n"
                    uu____70508
                else
                  if hint_replay
                  then
                    FStar_Errors.log_issue r
                      (FStar_Errors.Warning_HintFailedToReplayProof,
                        (Prims.op_Hat
                           "Hint failed to replay this sub-proof: " msg))
                  else
                    (let uu____70518 =
                       let uu____70524 =
                         let uu____70526 = FStar_Range.string_of_range r  in
                         FStar_Util.format2
                           "XX: proof obligation at %s failed\n\t%s\n"
                           uu____70526 msg
                          in
                       (FStar_Errors.Error_ProofObligationFailed,
                         uu____70524)
                        in
                     FStar_Errors.log_issue r uu____70518)
             in
          let elim labs =
            FStar_All.pipe_right labs
              (FStar_List.map
                 (fun uu____70579  ->
                    match uu____70579 with
                    | (l,uu____70588,uu____70589) ->
                        let a =
                          let uu____70593 =
                            let uu____70594 =
                              let uu____70599 =
                                FStar_SMTEncoding_Util.mkFreeV l  in
                              (uu____70599, FStar_SMTEncoding_Util.mkTrue)
                               in
                            FStar_SMTEncoding_Util.mkEq uu____70594  in
                          let uu____70600 =
                            let uu____70602 =
                              FStar_SMTEncoding_Term.fv_name l  in
                            Prims.op_Hat "@disable_label_" uu____70602  in
                          {
                            FStar_SMTEncoding_Term.assumption_term =
                              uu____70593;
                            FStar_SMTEncoding_Term.assumption_caption =
                              (FStar_Pervasives_Native.Some "Disabling label");
                            FStar_SMTEncoding_Term.assumption_name =
                              uu____70600;
                            FStar_SMTEncoding_Term.assumption_fact_ids = []
                          }  in
                        FStar_SMTEncoding_Term.Assume a))
             in
          let rec linear_check eliminated errors active =
            FStar_SMTEncoding_Z3.refresh ();
            (match active with
             | [] ->
                 let results =
                   let uu____70672 =
                     FStar_List.map (fun x  -> (x, true)) eliminated  in
                   let uu____70689 =
                     FStar_List.map (fun x  -> (x, false)) errors  in
                   FStar_List.append uu____70672 uu____70689  in
                 sort_labels results
             | hd1::tl1 ->
                 ((let uu____70716 =
                     FStar_Util.string_of_int (FStar_List.length active)  in
                   FStar_Util.print1 "%s, " uu____70716);
                  (let decls =
                     FStar_All.pipe_left elim
                       (FStar_List.append eliminated
                          (FStar_List.append errors tl1))
                      in
                   let result = askZ3 decls  in
                   match result.FStar_SMTEncoding_Z3.z3result_status with
                   | FStar_SMTEncoding_Z3.UNSAT uu____70748 ->
                       linear_check (hd1 :: eliminated) errors tl1
                   | uu____70749 ->
                       linear_check eliminated (hd1 :: errors) tl1)))
             in
          print_banner ();
          FStar_Options.set_option "z3rlimit"
            (FStar_Options.Int (Prims.parse_int "5"));
          (let res = linear_check [] [] all_labels  in
           FStar_Util.print_string "\n";
           FStar_All.pipe_right res (FStar_List.iter print_result);
           (let uu____70798 =
              FStar_Util.for_all FStar_Pervasives_Native.snd res  in
            if uu____70798
            then
              FStar_Util.print_string
                "Failed: the heuristic of trying each proof in isolation failed to identify a precise error\n"
            else ()))
  