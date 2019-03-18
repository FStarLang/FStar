open Prims
exception Not_a_wp_implication of Prims.string 
let (uu___is_Not_a_wp_implication : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Not_a_wp_implication uu____63111 -> true
    | uu____63114 -> false
  
let (__proj__Not_a_wp_implication__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | Not_a_wp_implication uu____63124 -> uu____63124
  
type label = FStar_SMTEncoding_Term.error_label
type labels = FStar_SMTEncoding_Term.error_labels
let (sort_labels :
  (FStar_SMTEncoding_Term.error_label * Prims.bool) Prims.list ->
    ((FStar_SMTEncoding_Term.fv * Prims.string * FStar_Range.range) *
      Prims.bool) Prims.list)
  =
  fun l  ->
    FStar_List.sortWith
      (fun uu____63182  ->
         fun uu____63183  ->
           match (uu____63182, uu____63183) with
           | (((uu____63233,uu____63234,r1),uu____63236),((uu____63237,uu____63238,r2),uu____63240))
               -> FStar_Range.compare r1 r2) l
  
let (remove_dups :
  labels ->
    (FStar_SMTEncoding_Term.fv * Prims.string * FStar_Range.range) Prims.list)
  =
  fun l  ->
    FStar_Util.remove_dups
      (fun uu____63317  ->
         fun uu____63318  ->
           match (uu____63317, uu____63318) with
           | ((uu____63348,m1,r1),(uu____63351,m2,r2)) ->
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
          (let uu____63418 =
             let uu____63420 = FStar_ST.op_Bang ctr  in
             FStar_Util.string_of_int uu____63420  in
           FStar_Util.format1 "label_%s" uu____63418)
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
          | (FStar_Pervasives_Native.None ,uu____63514) -> false
          | (FStar_Pervasives_Native.Some nm,FStar_SMTEncoding_Term.FreeV fv)
              ->
              let uu____63535 = FStar_SMTEncoding_Term.fv_name fv  in
              nm = uu____63535
          | (uu____63538,FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var "Valid",tm1::[])) ->
              is_a_post_condition post_name_opt tm1
          | (uu____63549,FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var "ApplyTT",tm1::uu____63551)) ->
              is_a_post_condition post_name_opt tm1
          | uu____63563 -> false  in
        let conjuncts t =
          match t.FStar_SMTEncoding_Term.tm with
          | FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And ,cs) -> cs
          | uu____63587 -> [t]  in
        let is_guard_free tm =
          match tm.FStar_SMTEncoding_Term.tm with
          | FStar_SMTEncoding_Term.Quant
              (FStar_SMTEncoding_Term.Forall
               ,({
                   FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App
                     (FStar_SMTEncoding_Term.Var "Prims.guard_free",p::[]);
                   FStar_SMTEncoding_Term.freevars = uu____63597;
                   FStar_SMTEncoding_Term.rng = uu____63598;_}::[])::[],iopt,uu____63600,
               {
                 FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App
                   (FStar_SMTEncoding_Term.Imp ,l::r1::[]);
                 FStar_SMTEncoding_Term.freevars = uu____63603;
                 FStar_SMTEncoding_Term.rng = uu____63604;_})
              -> true
          | uu____63653 -> false  in
        let is_a_named_continuation lhs =
          FStar_All.pipe_right (conjuncts lhs)
            (FStar_Util.for_some is_guard_free)
           in
        let uu____63665 =
          match use_env_msg with
          | FStar_Pervasives_Native.None  -> (false, "")
          | FStar_Pervasives_Native.Some f ->
              let uu____63695 = f ()  in (true, uu____63695)
           in
        match uu____63665 with
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
                    let uu____63751 =
                      let uu____63753 = FStar_Range.use_range rng  in
                      let uu____63754 = FStar_Range.use_range r1  in
                      FStar_Range.rng_included uu____63753 uu____63754  in
                    if uu____63751
                    then rng
                    else
                      (let uu____63758 = FStar_Range.def_range rng  in
                       FStar_Range.set_def_range r1 uu____63758)
                 in
              fresh_label msg1 rng1 t  in
            let rec aux default_msg ropt post_name_opt labels q1 =
              match q1.FStar_SMTEncoding_Term.tm with
              | FStar_SMTEncoding_Term.BoundV uu____63813 -> (labels, q1)
              | FStar_SMTEncoding_Term.Integer uu____63817 -> (labels, q1)
              | FStar_SMTEncoding_Term.Real uu____63821 -> (labels, q1)
              | FStar_SMTEncoding_Term.LblPos uu____63825 ->
                  failwith "Impossible"
              | FStar_SMTEncoding_Term.Labeled
                  (arg,"could not prove post-condition",uu____63839) ->
                  let fallback msg =
                    aux default_msg ropt post_name_opt labels arg  in
                  (try
                     (fun uu___747_63885  ->
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
                                                             = uu____63904;
                                                           FStar_SMTEncoding_Term.rng
                                                             = rng;_})
                                 ->
                                 let post_name =
                                   let uu____63940 =
                                     let uu____63942 = FStar_Ident.next_id ()
                                        in
                                     FStar_All.pipe_left
                                       FStar_Util.string_of_int uu____63942
                                      in
                                   Prims.op_Hat "^^post_condition_"
                                     uu____63940
                                    in
                                 let names1 =
                                   let uu____63950 =
                                     FStar_SMTEncoding_Term.mk_fv
                                       (post_name, post)
                                      in
                                   let uu____63952 =
                                     FStar_List.map
                                       (fun s  ->
                                          let uu____63958 =
                                            let uu____63964 =
                                              let uu____63966 =
                                                let uu____63968 =
                                                  FStar_Ident.next_id ()  in
                                                FStar_All.pipe_left
                                                  FStar_Util.string_of_int
                                                  uu____63968
                                                 in
                                              Prims.op_Hat "^^" uu____63966
                                               in
                                            (uu____63964, s)  in
                                          FStar_SMTEncoding_Term.mk_fv
                                            uu____63958) sorts
                                      in
                                   uu____63950 :: uu____63952  in
                                 let instantiation =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV names1
                                    in
                                 let uu____63977 =
                                   let uu____63982 =
                                     FStar_SMTEncoding_Term.inst
                                       instantiation lhs
                                      in
                                   let uu____63983 =
                                     FStar_SMTEncoding_Term.inst
                                       instantiation rhs
                                      in
                                   (uu____63982, uu____63983)  in
                                 (match uu____63977 with
                                  | (lhs1,rhs1) ->
                                      let uu____63992 =
                                        match lhs1.FStar_SMTEncoding_Term.tm
                                        with
                                        | FStar_SMTEncoding_Term.App
                                            (FStar_SMTEncoding_Term.And
                                             ,clauses_lhs)
                                            ->
                                            let uu____64010 =
                                              FStar_Util.prefix clauses_lhs
                                               in
                                            (match uu____64010 with
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
                                                           = uu____64040;
                                                         FStar_SMTEncoding_Term.rng
                                                           = rng_ens;_})
                                                      ->
                                                      let uu____64074 =
                                                        is_a_post_condition
                                                          (FStar_Pervasives_Native.Some
                                                             post_name) post1
                                                         in
                                                      if uu____64074
                                                      then
                                                        let uu____64084 =
                                                          aux
                                                            "could not prove post-condition"
                                                            FStar_Pervasives_Native.None
                                                            (FStar_Pervasives_Native.Some
                                                               post_name)
                                                            labels
                                                            ensures_conjuncts
                                                           in
                                                        (match uu____64084
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
                                                               | uu____64128
                                                                   ->
                                                                   pats_ens
                                                                in
                                                             let ens1 =
                                                               let uu____64134
                                                                 =
                                                                 let uu____64135
                                                                   =
                                                                   let uu____64155
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
                                                                    uu____64155)
                                                                    in
                                                                 FStar_SMTEncoding_Term.Quant
                                                                   uu____64135
                                                                  in
                                                               FStar_SMTEncoding_Term.mk
                                                                 uu____64134
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
                                                             let uu____64170
                                                               =
                                                               FStar_SMTEncoding_Term.abstr
                                                                 names1 lhs2
                                                                in
                                                             (labels1,
                                                               uu____64170))
                                                      else
                                                        (let uu____64175 =
                                                           let uu____64176 =
                                                             let uu____64178
                                                               =
                                                               let uu____64180
                                                                 =
                                                                 let uu____64182
                                                                   =
                                                                   FStar_SMTEncoding_Term.print_smt_term
                                                                    post1
                                                                    in
                                                                 Prims.op_Hat
                                                                   "  ... "
                                                                   uu____64182
                                                                  in
                                                               Prims.op_Hat
                                                                 post_name
                                                                 uu____64180
                                                                in
                                                             Prims.op_Hat
                                                               "Ensures clause doesn't match post name:  "
                                                               uu____64178
                                                              in
                                                           Not_a_wp_implication
                                                             uu____64176
                                                            in
                                                         FStar_Exn.raise
                                                           uu____64175)
                                                  | uu____64192 ->
                                                      let uu____64193 =
                                                        let uu____64194 =
                                                          let uu____64196 =
                                                            let uu____64198 =
                                                              let uu____64200
                                                                =
                                                                FStar_SMTEncoding_Term.print_smt_term
                                                                  ens
                                                                 in
                                                              Prims.op_Hat
                                                                "  ... "
                                                                uu____64200
                                                               in
                                                            Prims.op_Hat
                                                              post_name
                                                              uu____64198
                                                             in
                                                          Prims.op_Hat
                                                            "Ensures clause doesn't have the expected shape for post-condition "
                                                            uu____64196
                                                           in
                                                        Not_a_wp_implication
                                                          uu____64194
                                                         in
                                                      FStar_Exn.raise
                                                        uu____64193))
                                        | uu____64210 ->
                                            let uu____64211 =
                                              let uu____64212 =
                                                let uu____64214 =
                                                  FStar_SMTEncoding_Term.print_smt_term
                                                    lhs1
                                                   in
                                                Prims.op_Hat
                                                  "LHS not a conjunct: "
                                                  uu____64214
                                                 in
                                              Not_a_wp_implication
                                                uu____64212
                                               in
                                            FStar_Exn.raise uu____64211
                                         in
                                      (match uu____63992 with
                                       | (labels1,lhs2) ->
                                           let uu____64235 =
                                             let uu____64242 =
                                               aux default_msg
                                                 FStar_Pervasives_Native.None
                                                 (FStar_Pervasives_Native.Some
                                                    post_name) labels1 rhs1
                                                in
                                             match uu____64242 with
                                             | (labels2,rhs2) ->
                                                 let uu____64262 =
                                                   FStar_SMTEncoding_Term.abstr
                                                     names1 rhs2
                                                    in
                                                 (labels2, uu____64262)
                                              in
                                           (match uu____64235 with
                                            | (labels2,rhs2) ->
                                                let body =
                                                  FStar_SMTEncoding_Term.mkImp
                                                    (lhs2, rhs2) rng
                                                   in
                                                let uu____64278 =
                                                  FStar_SMTEncoding_Term.mk
                                                    (FStar_SMTEncoding_Term.Quant
                                                       (FStar_SMTEncoding_Term.Forall,
                                                         pats, iopt, (post ::
                                                         sorts), body))
                                                    q1.FStar_SMTEncoding_Term.rng
                                                   in
                                                (labels2, uu____64278))))
                             | uu____64290 ->
                                 let uu____64291 =
                                   let uu____64293 =
                                     FStar_SMTEncoding_Term.print_smt_term
                                       arg
                                      in
                                   Prims.op_Hat "arg not a quant: "
                                     uu____64293
                                    in
                                 fallback uu____64291)) ()
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
                            FStar_SMTEncoding_Term.freevars = uu____64315;
                            FStar_SMTEncoding_Term.rng = rng;_})
                  when is_a_named_continuation lhs ->
                  let uu____64345 = FStar_Util.prefix sorts  in
                  (match uu____64345 with
                   | (sorts',post) ->
                       let new_post_name =
                         let uu____64366 =
                           let uu____64368 = FStar_Ident.next_id ()  in
                           FStar_All.pipe_left FStar_Util.string_of_int
                             uu____64368
                            in
                         Prims.op_Hat "^^post_condition_" uu____64366  in
                       let names1 =
                         let uu____64376 =
                           FStar_List.map
                             (fun s  ->
                                let uu____64382 =
                                  let uu____64388 =
                                    let uu____64390 =
                                      let uu____64392 =
                                        FStar_Ident.next_id ()  in
                                      FStar_All.pipe_left
                                        FStar_Util.string_of_int uu____64392
                                       in
                                    Prims.op_Hat "^^" uu____64390  in
                                  (uu____64388, s)  in
                                FStar_SMTEncoding_Term.mk_fv uu____64382)
                             sorts'
                            in
                         let uu____64398 =
                           let uu____64401 =
                             FStar_SMTEncoding_Term.mk_fv
                               (new_post_name, post)
                              in
                           [uu____64401]  in
                         FStar_List.append uu____64376 uu____64398  in
                       let instantiation =
                         FStar_List.map FStar_SMTEncoding_Util.mkFreeV names1
                          in
                       let uu____64406 =
                         let uu____64411 =
                           FStar_SMTEncoding_Term.inst instantiation lhs  in
                         let uu____64412 =
                           FStar_SMTEncoding_Term.inst instantiation rhs  in
                         (uu____64411, uu____64412)  in
                       (match uu____64406 with
                        | (lhs1,rhs1) ->
                            let uu____64421 =
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
                                                = uu____64459;
                                              FStar_SMTEncoding_Term.rng =
                                                uu____64460;_}::[])::[],iopt,sorts1,
                                          {
                                            FStar_SMTEncoding_Term.tm =
                                              FStar_SMTEncoding_Term.App
                                              (FStar_SMTEncoding_Term.Imp
                                               ,l0::r1::[]);
                                            FStar_SMTEncoding_Term.freevars =
                                              uu____64465;
                                            FStar_SMTEncoding_Term.rng =
                                              uu____64466;_})
                                         ->
                                         let uu____64514 =
                                           is_a_post_condition
                                             (FStar_Pervasives_Native.Some
                                                new_post_name) r1
                                            in
                                         if uu____64514
                                         then
                                           let uu____64524 =
                                             aux default_msg
                                               FStar_Pervasives_Native.None
                                               post_name_opt labels1 l0
                                              in
                                           (match uu____64524 with
                                            | (labels2,l) ->
                                                let uu____64543 =
                                                  let uu____64544 =
                                                    let uu____64545 =
                                                      let uu____64565 =
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
                                                        sorts1, uu____64565)
                                                       in
                                                    FStar_SMTEncoding_Term.Quant
                                                      uu____64545
                                                     in
                                                  FStar_SMTEncoding_Term.mk
                                                    uu____64544
                                                    q1.FStar_SMTEncoding_Term.rng
                                                   in
                                                (labels2, uu____64543))
                                         else (labels1, tm)
                                     | uu____64589 -> (labels1, tm)) labels
                                (conjuncts lhs1)
                               in
                            (match uu____64421 with
                             | (labels1,lhs_conjs) ->
                                 let uu____64608 =
                                   aux default_msg
                                     FStar_Pervasives_Native.None
                                     (FStar_Pervasives_Native.Some
                                        new_post_name) labels1 rhs1
                                    in
                                 (match uu____64608 with
                                  | (labels2,rhs2) ->
                                      let body =
                                        let uu____64629 =
                                          let uu____64630 =
                                            let uu____64635 =
                                              FStar_SMTEncoding_Term.mk_and_l
                                                lhs_conjs
                                                lhs1.FStar_SMTEncoding_Term.rng
                                               in
                                            (uu____64635, rhs2)  in
                                          FStar_SMTEncoding_Term.mkImp
                                            uu____64630 rng
                                           in
                                        FStar_All.pipe_right uu____64629
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
                  let uu____64655 =
                    aux default_msg ropt post_name_opt labels rhs  in
                  (match uu____64655 with
                   | (labels1,rhs1) ->
                       let uu____64674 =
                         FStar_SMTEncoding_Util.mkImp (lhs, rhs1)  in
                       (labels1, uu____64674))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.And ,conjuncts1) ->
                  let uu____64682 =
                    FStar_Util.fold_map (aux default_msg ropt post_name_opt)
                      labels conjuncts1
                     in
                  (match uu____64682 with
                   | (labels1,conjuncts2) ->
                       let uu____64709 =
                         FStar_SMTEncoding_Term.mk_and_l conjuncts2
                           q1.FStar_SMTEncoding_Term.rng
                          in
                       (labels1, uu____64709))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.ITE ,hd1::q11::q2::[]) ->
                  let uu____64717 =
                    aux default_msg ropt post_name_opt labels q11  in
                  (match uu____64717 with
                   | (labels1,q12) ->
                       let uu____64736 =
                         aux default_msg ropt post_name_opt labels1 q2  in
                       (match uu____64736 with
                        | (labels2,q21) ->
                            let uu____64755 =
                              FStar_SMTEncoding_Term.mkITE (hd1, q12, q21)
                                q1.FStar_SMTEncoding_Term.rng
                               in
                            (labels2, uu____64755)))
              | FStar_SMTEncoding_Term.Quant
                  (FStar_SMTEncoding_Term.Exists
                   ,uu____64758,uu____64759,uu____64760,uu____64761)
                  ->
                  let uu____64780 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____64780 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Iff ,uu____64795) ->
                  let uu____64800 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____64800 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Or ,uu____64815) ->
                  let uu____64820 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____64820 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Var uu____64835,uu____64836) when
                  is_a_post_condition post_name_opt q1 -> (labels, q1)
              | FStar_SMTEncoding_Term.FreeV uu____64844 ->
                  let uu____64853 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____64853 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.TrueOp ,uu____64868) ->
                  let uu____64873 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____64873 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.FalseOp ,uu____64888) ->
                  let uu____64893 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____64893 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Not ,uu____64908) ->
                  let uu____64913 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____64913 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Eq ,uu____64928) ->
                  let uu____64933 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____64933 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.LT ,uu____64948) ->
                  let uu____64953 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____64953 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.LTE ,uu____64968) ->
                  let uu____64973 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____64973 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.GT ,uu____64988) ->
                  let uu____64993 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____64993 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.GTE ,uu____65008) ->
                  let uu____65013 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____65013 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvUlt ,uu____65028) ->
                  let uu____65033 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____65033 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Var uu____65048,uu____65049) ->
                  let uu____65055 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____65055 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.RealDiv ,uu____65070) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Add ,uu____65082) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Sub ,uu____65094) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Div ,uu____65106) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Mul ,uu____65118) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Minus ,uu____65130) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Mod ,uu____65142) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvAnd ,uu____65154) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvXor ,uu____65166) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvOr ,uu____65178) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvAdd ,uu____65190) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvSub ,uu____65202) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvShl ,uu____65214) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvShr ,uu____65226) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvUdiv ,uu____65238) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvMod ,uu____65250) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvMul ,uu____65262) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvUext uu____65274,uu____65275) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvToNat ,uu____65288) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.NatToBv uu____65300,uu____65301) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.ITE ,uu____65314) ->
                  failwith "Impossible: arity mismatch"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Imp ,uu____65326) ->
                  failwith "Impossible: arity mismatch"
              | FStar_SMTEncoding_Term.Quant
                  (FStar_SMTEncoding_Term.Forall ,pats,iopt,sorts,body) ->
                  let uu____65360 =
                    aux default_msg ropt post_name_opt labels body  in
                  (match uu____65360 with
                   | (labels1,body1) ->
                       let uu____65379 =
                         FStar_SMTEncoding_Term.mk
                           (FStar_SMTEncoding_Term.Quant
                              (FStar_SMTEncoding_Term.Forall, pats, iopt,
                                sorts, body1)) q1.FStar_SMTEncoding_Term.rng
                          in
                       (labels1, uu____65379))
              | FStar_SMTEncoding_Term.Let (es,body) ->
                  let uu____65397 =
                    aux default_msg ropt post_name_opt labels body  in
                  (match uu____65397 with
                   | (labels1,body1) ->
                       let uu____65416 =
                         FStar_SMTEncoding_Term.mkLet (es, body1)
                           q1.FStar_SMTEncoding_Term.rng
                          in
                       (labels1, uu____65416))
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
          let print_banner uu____65460 =
            let msg =
              let uu____65463 =
                let uu____65465 = FStar_TypeChecker_Env.get_range env  in
                FStar_Range.string_of_range uu____65465  in
              let uu____65466 =
                FStar_Util.string_of_int (Prims.parse_int "5")  in
              let uu____65469 =
                FStar_Util.string_of_int (FStar_List.length all_labels)  in
              FStar_Util.format4
                "Detailed %s report follows for %s\nTaking %s seconds per proof obligation (%s proofs in total)\n"
                (if hint_replay then "hint replay" else "error") uu____65463
                uu____65466 uu____65469
               in
            FStar_Util.print_error msg  in
          let print_result uu____65495 =
            match uu____65495 with
            | ((uu____65508,msg,r),success) ->
                if success
                then
                  let uu____65524 = FStar_Range.string_of_range r  in
                  FStar_Util.print1
                    "OK: proof obligation at %s was proven in isolation\n"
                    uu____65524
                else
                  if hint_replay
                  then
                    FStar_Errors.log_issue r
                      (FStar_Errors.Warning_HintFailedToReplayProof,
                        (Prims.op_Hat
                           "Hint failed to replay this sub-proof: " msg))
                  else
                    (let uu____65534 =
                       let uu____65540 =
                         let uu____65542 = FStar_Range.string_of_range r  in
                         FStar_Util.format2
                           "XX: proof obligation at %s failed\n\t%s\n"
                           uu____65542 msg
                          in
                       (FStar_Errors.Error_ProofObligationFailed,
                         uu____65540)
                        in
                     FStar_Errors.log_issue r uu____65534)
             in
          let elim labs =
            FStar_All.pipe_right labs
              (FStar_List.map
                 (fun uu____65595  ->
                    match uu____65595 with
                    | (l,uu____65604,uu____65605) ->
                        let a =
                          let uu____65609 =
                            let uu____65610 =
                              let uu____65615 =
                                FStar_SMTEncoding_Util.mkFreeV l  in
                              (uu____65615, FStar_SMTEncoding_Util.mkTrue)
                               in
                            FStar_SMTEncoding_Util.mkEq uu____65610  in
                          let uu____65616 =
                            let uu____65618 =
                              FStar_SMTEncoding_Term.fv_name l  in
                            Prims.op_Hat "@disable_label_" uu____65618  in
                          {
                            FStar_SMTEncoding_Term.assumption_term =
                              uu____65609;
                            FStar_SMTEncoding_Term.assumption_caption =
                              (FStar_Pervasives_Native.Some "Disabling label");
                            FStar_SMTEncoding_Term.assumption_name =
                              uu____65616;
                            FStar_SMTEncoding_Term.assumption_fact_ids = []
                          }  in
                        FStar_SMTEncoding_Term.Assume a))
             in
          let rec linear_check eliminated errors active =
            FStar_SMTEncoding_Z3.refresh ();
            (match active with
             | [] ->
                 let results =
                   let uu____65688 =
                     FStar_List.map (fun x  -> (x, true)) eliminated  in
                   let uu____65705 =
                     FStar_List.map (fun x  -> (x, false)) errors  in
                   FStar_List.append uu____65688 uu____65705  in
                 sort_labels results
             | hd1::tl1 ->
                 ((let uu____65732 =
                     FStar_Util.string_of_int (FStar_List.length active)  in
                   FStar_Util.print1 "%s, " uu____65732);
                  (let decls =
                     FStar_All.pipe_left elim
                       (FStar_List.append eliminated
                          (FStar_List.append errors tl1))
                      in
                   let result = askZ3 decls  in
                   match result.FStar_SMTEncoding_Z3.z3result_status with
                   | FStar_SMTEncoding_Z3.UNSAT uu____65764 ->
                       linear_check (hd1 :: eliminated) errors tl1
                   | uu____65765 ->
                       linear_check eliminated (hd1 :: errors) tl1)))
             in
          print_banner ();
          FStar_Options.set_option "z3rlimit"
            (FStar_Options.Int (Prims.parse_int "5"));
          (let res = linear_check [] [] all_labels  in
           FStar_Util.print_string "\n";
           FStar_All.pipe_right res (FStar_List.iter print_result);
           (let uu____65814 =
              FStar_Util.for_all FStar_Pervasives_Native.snd res  in
            if uu____65814
            then
              FStar_Util.print_string
                "Failed: the heuristic of trying each proof in isolation failed to identify a precise error\n"
            else ()))
  