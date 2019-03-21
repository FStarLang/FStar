open Prims
exception Not_a_wp_implication of Prims.string 
let (uu___is_Not_a_wp_implication : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Not_a_wp_implication uu____63144 -> true
    | uu____63147 -> false
  
let (__proj__Not_a_wp_implication__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | Not_a_wp_implication uu____63157 -> uu____63157
  
type label = FStar_SMTEncoding_Term.error_label
type labels = FStar_SMTEncoding_Term.error_labels
let (sort_labels :
  (FStar_SMTEncoding_Term.error_label * Prims.bool) Prims.list ->
    ((FStar_SMTEncoding_Term.fv * Prims.string * FStar_Range.range) *
      Prims.bool) Prims.list)
  =
  fun l  ->
    FStar_List.sortWith
      (fun uu____63215  ->
         fun uu____63216  ->
           match (uu____63215, uu____63216) with
           | (((uu____63266,uu____63267,r1),uu____63269),((uu____63270,uu____63271,r2),uu____63273))
               -> FStar_Range.compare r1 r2) l
  
let (remove_dups :
  labels ->
    (FStar_SMTEncoding_Term.fv * Prims.string * FStar_Range.range) Prims.list)
  =
  fun l  ->
    FStar_Util.remove_dups
      (fun uu____63350  ->
         fun uu____63351  ->
           match (uu____63350, uu____63351) with
           | ((uu____63381,m1,r1),(uu____63384,m2,r2)) ->
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
          (let uu____63451 =
             let uu____63453 = FStar_ST.op_Bang ctr  in
             FStar_Util.string_of_int uu____63453  in
           FStar_Util.format1 "label_%s" uu____63451)
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
          | (FStar_Pervasives_Native.None ,uu____63547) -> false
          | (FStar_Pervasives_Native.Some nm,FStar_SMTEncoding_Term.FreeV fv)
              ->
              let uu____63568 = FStar_SMTEncoding_Term.fv_name fv  in
              nm = uu____63568
          | (uu____63571,FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var "Valid",tm1::[])) ->
              is_a_post_condition post_name_opt tm1
          | (uu____63582,FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var "ApplyTT",tm1::uu____63584)) ->
              is_a_post_condition post_name_opt tm1
          | uu____63596 -> false  in
        let conjuncts t =
          match t.FStar_SMTEncoding_Term.tm with
          | FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And ,cs) -> cs
          | uu____63620 -> [t]  in
        let is_guard_free tm =
          match tm.FStar_SMTEncoding_Term.tm with
          | FStar_SMTEncoding_Term.Quant
              (FStar_SMTEncoding_Term.Forall
               ,({
                   FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App
                     (FStar_SMTEncoding_Term.Var "Prims.guard_free",p::[]);
                   FStar_SMTEncoding_Term.freevars = uu____63630;
                   FStar_SMTEncoding_Term.rng = uu____63631;_}::[])::[],iopt,uu____63633,
               {
                 FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App
                   (FStar_SMTEncoding_Term.Imp ,l::r1::[]);
                 FStar_SMTEncoding_Term.freevars = uu____63636;
                 FStar_SMTEncoding_Term.rng = uu____63637;_})
              -> true
          | uu____63686 -> false  in
        let is_a_named_continuation lhs =
          FStar_All.pipe_right (conjuncts lhs)
            (FStar_Util.for_some is_guard_free)
           in
        let uu____63698 =
          match use_env_msg with
          | FStar_Pervasives_Native.None  -> (false, "")
          | FStar_Pervasives_Native.Some f ->
              let uu____63728 = f ()  in (true, uu____63728)
           in
        match uu____63698 with
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
                    let uu____63784 =
                      let uu____63786 = FStar_Range.use_range rng  in
                      let uu____63787 = FStar_Range.use_range r1  in
                      FStar_Range.rng_included uu____63786 uu____63787  in
                    if uu____63784
                    then rng
                    else
                      (let uu____63791 = FStar_Range.def_range rng  in
                       FStar_Range.set_def_range r1 uu____63791)
                 in
              fresh_label msg1 rng1 t  in
            let rec aux default_msg ropt post_name_opt labels q1 =
              match q1.FStar_SMTEncoding_Term.tm with
              | FStar_SMTEncoding_Term.BoundV uu____63846 -> (labels, q1)
              | FStar_SMTEncoding_Term.Integer uu____63850 -> (labels, q1)
              | FStar_SMTEncoding_Term.Real uu____63854 -> (labels, q1)
              | FStar_SMTEncoding_Term.LblPos uu____63858 ->
                  failwith "Impossible"
              | FStar_SMTEncoding_Term.Labeled
                  (arg,"could not prove post-condition",uu____63872) ->
                  let fallback msg =
                    aux default_msg ropt post_name_opt labels arg  in
                  (try
                     (fun uu___747_63918  ->
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
                                                             = uu____63937;
                                                           FStar_SMTEncoding_Term.rng
                                                             = rng;_})
                                 ->
                                 let post_name =
                                   let uu____63973 =
                                     let uu____63975 = FStar_Ident.next_id ()
                                        in
                                     FStar_All.pipe_left
                                       FStar_Util.string_of_int uu____63975
                                      in
                                   Prims.op_Hat "^^post_condition_"
                                     uu____63973
                                    in
                                 let names1 =
                                   let uu____63983 =
                                     FStar_SMTEncoding_Term.mk_fv
                                       (post_name, post)
                                      in
                                   let uu____63985 =
                                     FStar_List.map
                                       (fun s  ->
                                          let uu____63991 =
                                            let uu____63997 =
                                              let uu____63999 =
                                                let uu____64001 =
                                                  FStar_Ident.next_id ()  in
                                                FStar_All.pipe_left
                                                  FStar_Util.string_of_int
                                                  uu____64001
                                                 in
                                              Prims.op_Hat "^^" uu____63999
                                               in
                                            (uu____63997, s)  in
                                          FStar_SMTEncoding_Term.mk_fv
                                            uu____63991) sorts
                                      in
                                   uu____63983 :: uu____63985  in
                                 let instantiation =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV names1
                                    in
                                 let uu____64010 =
                                   let uu____64015 =
                                     FStar_SMTEncoding_Term.inst
                                       instantiation lhs
                                      in
                                   let uu____64016 =
                                     FStar_SMTEncoding_Term.inst
                                       instantiation rhs
                                      in
                                   (uu____64015, uu____64016)  in
                                 (match uu____64010 with
                                  | (lhs1,rhs1) ->
                                      let uu____64025 =
                                        match lhs1.FStar_SMTEncoding_Term.tm
                                        with
                                        | FStar_SMTEncoding_Term.App
                                            (FStar_SMTEncoding_Term.And
                                             ,clauses_lhs)
                                            ->
                                            let uu____64043 =
                                              FStar_Util.prefix clauses_lhs
                                               in
                                            (match uu____64043 with
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
                                                           = uu____64073;
                                                         FStar_SMTEncoding_Term.rng
                                                           = rng_ens;_})
                                                      ->
                                                      let uu____64107 =
                                                        is_a_post_condition
                                                          (FStar_Pervasives_Native.Some
                                                             post_name) post1
                                                         in
                                                      if uu____64107
                                                      then
                                                        let uu____64117 =
                                                          aux
                                                            "could not prove post-condition"
                                                            FStar_Pervasives_Native.None
                                                            (FStar_Pervasives_Native.Some
                                                               post_name)
                                                            labels
                                                            ensures_conjuncts
                                                           in
                                                        (match uu____64117
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
                                                               | uu____64161
                                                                   ->
                                                                   pats_ens
                                                                in
                                                             let ens1 =
                                                               let uu____64167
                                                                 =
                                                                 let uu____64168
                                                                   =
                                                                   let uu____64188
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
                                                                    uu____64188)
                                                                    in
                                                                 FStar_SMTEncoding_Term.Quant
                                                                   uu____64168
                                                                  in
                                                               FStar_SMTEncoding_Term.mk
                                                                 uu____64167
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
                                                             let uu____64203
                                                               =
                                                               FStar_SMTEncoding_Term.abstr
                                                                 names1 lhs2
                                                                in
                                                             (labels1,
                                                               uu____64203))
                                                      else
                                                        (let uu____64208 =
                                                           let uu____64209 =
                                                             let uu____64211
                                                               =
                                                               let uu____64213
                                                                 =
                                                                 let uu____64215
                                                                   =
                                                                   FStar_SMTEncoding_Term.print_smt_term
                                                                    post1
                                                                    in
                                                                 Prims.op_Hat
                                                                   "  ... "
                                                                   uu____64215
                                                                  in
                                                               Prims.op_Hat
                                                                 post_name
                                                                 uu____64213
                                                                in
                                                             Prims.op_Hat
                                                               "Ensures clause doesn't match post name:  "
                                                               uu____64211
                                                              in
                                                           Not_a_wp_implication
                                                             uu____64209
                                                            in
                                                         FStar_Exn.raise
                                                           uu____64208)
                                                  | uu____64225 ->
                                                      let uu____64226 =
                                                        let uu____64227 =
                                                          let uu____64229 =
                                                            let uu____64231 =
                                                              let uu____64233
                                                                =
                                                                FStar_SMTEncoding_Term.print_smt_term
                                                                  ens
                                                                 in
                                                              Prims.op_Hat
                                                                "  ... "
                                                                uu____64233
                                                               in
                                                            Prims.op_Hat
                                                              post_name
                                                              uu____64231
                                                             in
                                                          Prims.op_Hat
                                                            "Ensures clause doesn't have the expected shape for post-condition "
                                                            uu____64229
                                                           in
                                                        Not_a_wp_implication
                                                          uu____64227
                                                         in
                                                      FStar_Exn.raise
                                                        uu____64226))
                                        | uu____64243 ->
                                            let uu____64244 =
                                              let uu____64245 =
                                                let uu____64247 =
                                                  FStar_SMTEncoding_Term.print_smt_term
                                                    lhs1
                                                   in
                                                Prims.op_Hat
                                                  "LHS not a conjunct: "
                                                  uu____64247
                                                 in
                                              Not_a_wp_implication
                                                uu____64245
                                               in
                                            FStar_Exn.raise uu____64244
                                         in
                                      (match uu____64025 with
                                       | (labels1,lhs2) ->
                                           let uu____64268 =
                                             let uu____64275 =
                                               aux default_msg
                                                 FStar_Pervasives_Native.None
                                                 (FStar_Pervasives_Native.Some
                                                    post_name) labels1 rhs1
                                                in
                                             match uu____64275 with
                                             | (labels2,rhs2) ->
                                                 let uu____64295 =
                                                   FStar_SMTEncoding_Term.abstr
                                                     names1 rhs2
                                                    in
                                                 (labels2, uu____64295)
                                              in
                                           (match uu____64268 with
                                            | (labels2,rhs2) ->
                                                let body =
                                                  FStar_SMTEncoding_Term.mkImp
                                                    (lhs2, rhs2) rng
                                                   in
                                                let uu____64311 =
                                                  FStar_SMTEncoding_Term.mk
                                                    (FStar_SMTEncoding_Term.Quant
                                                       (FStar_SMTEncoding_Term.Forall,
                                                         pats, iopt, (post ::
                                                         sorts), body))
                                                    q1.FStar_SMTEncoding_Term.rng
                                                   in
                                                (labels2, uu____64311))))
                             | uu____64323 ->
                                 let uu____64324 =
                                   let uu____64326 =
                                     FStar_SMTEncoding_Term.print_smt_term
                                       arg
                                      in
                                   Prims.op_Hat "arg not a quant: "
                                     uu____64326
                                    in
                                 fallback uu____64324)) ()
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
                            FStar_SMTEncoding_Term.freevars = uu____64348;
                            FStar_SMTEncoding_Term.rng = rng;_})
                  when is_a_named_continuation lhs ->
                  let uu____64378 = FStar_Util.prefix sorts  in
                  (match uu____64378 with
                   | (sorts',post) ->
                       let new_post_name =
                         let uu____64399 =
                           let uu____64401 = FStar_Ident.next_id ()  in
                           FStar_All.pipe_left FStar_Util.string_of_int
                             uu____64401
                            in
                         Prims.op_Hat "^^post_condition_" uu____64399  in
                       let names1 =
                         let uu____64409 =
                           FStar_List.map
                             (fun s  ->
                                let uu____64415 =
                                  let uu____64421 =
                                    let uu____64423 =
                                      let uu____64425 =
                                        FStar_Ident.next_id ()  in
                                      FStar_All.pipe_left
                                        FStar_Util.string_of_int uu____64425
                                       in
                                    Prims.op_Hat "^^" uu____64423  in
                                  (uu____64421, s)  in
                                FStar_SMTEncoding_Term.mk_fv uu____64415)
                             sorts'
                            in
                         let uu____64431 =
                           let uu____64434 =
                             FStar_SMTEncoding_Term.mk_fv
                               (new_post_name, post)
                              in
                           [uu____64434]  in
                         FStar_List.append uu____64409 uu____64431  in
                       let instantiation =
                         FStar_List.map FStar_SMTEncoding_Util.mkFreeV names1
                          in
                       let uu____64439 =
                         let uu____64444 =
                           FStar_SMTEncoding_Term.inst instantiation lhs  in
                         let uu____64445 =
                           FStar_SMTEncoding_Term.inst instantiation rhs  in
                         (uu____64444, uu____64445)  in
                       (match uu____64439 with
                        | (lhs1,rhs1) ->
                            let uu____64454 =
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
                                                = uu____64492;
                                              FStar_SMTEncoding_Term.rng =
                                                uu____64493;_}::[])::[],iopt,sorts1,
                                          {
                                            FStar_SMTEncoding_Term.tm =
                                              FStar_SMTEncoding_Term.App
                                              (FStar_SMTEncoding_Term.Imp
                                               ,l0::r1::[]);
                                            FStar_SMTEncoding_Term.freevars =
                                              uu____64498;
                                            FStar_SMTEncoding_Term.rng =
                                              uu____64499;_})
                                         ->
                                         let uu____64547 =
                                           is_a_post_condition
                                             (FStar_Pervasives_Native.Some
                                                new_post_name) r1
                                            in
                                         if uu____64547
                                         then
                                           let uu____64557 =
                                             aux default_msg
                                               FStar_Pervasives_Native.None
                                               post_name_opt labels1 l0
                                              in
                                           (match uu____64557 with
                                            | (labels2,l) ->
                                                let uu____64576 =
                                                  let uu____64577 =
                                                    let uu____64578 =
                                                      let uu____64598 =
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
                                                        sorts1, uu____64598)
                                                       in
                                                    FStar_SMTEncoding_Term.Quant
                                                      uu____64578
                                                     in
                                                  FStar_SMTEncoding_Term.mk
                                                    uu____64577
                                                    q1.FStar_SMTEncoding_Term.rng
                                                   in
                                                (labels2, uu____64576))
                                         else (labels1, tm)
                                     | uu____64622 -> (labels1, tm)) labels
                                (conjuncts lhs1)
                               in
                            (match uu____64454 with
                             | (labels1,lhs_conjs) ->
                                 let uu____64641 =
                                   aux default_msg
                                     FStar_Pervasives_Native.None
                                     (FStar_Pervasives_Native.Some
                                        new_post_name) labels1 rhs1
                                    in
                                 (match uu____64641 with
                                  | (labels2,rhs2) ->
                                      let body =
                                        let uu____64662 =
                                          let uu____64663 =
                                            let uu____64668 =
                                              FStar_SMTEncoding_Term.mk_and_l
                                                lhs_conjs
                                                lhs1.FStar_SMTEncoding_Term.rng
                                               in
                                            (uu____64668, rhs2)  in
                                          FStar_SMTEncoding_Term.mkImp
                                            uu____64663 rng
                                           in
                                        FStar_All.pipe_right uu____64662
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
                  let uu____64688 =
                    aux default_msg ropt post_name_opt labels rhs  in
                  (match uu____64688 with
                   | (labels1,rhs1) ->
                       let uu____64707 =
                         FStar_SMTEncoding_Util.mkImp (lhs, rhs1)  in
                       (labels1, uu____64707))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.And ,conjuncts1) ->
                  let uu____64715 =
                    FStar_Util.fold_map (aux default_msg ropt post_name_opt)
                      labels conjuncts1
                     in
                  (match uu____64715 with
                   | (labels1,conjuncts2) ->
                       let uu____64742 =
                         FStar_SMTEncoding_Term.mk_and_l conjuncts2
                           q1.FStar_SMTEncoding_Term.rng
                          in
                       (labels1, uu____64742))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.ITE ,hd1::q11::q2::[]) ->
                  let uu____64750 =
                    aux default_msg ropt post_name_opt labels q11  in
                  (match uu____64750 with
                   | (labels1,q12) ->
                       let uu____64769 =
                         aux default_msg ropt post_name_opt labels1 q2  in
                       (match uu____64769 with
                        | (labels2,q21) ->
                            let uu____64788 =
                              FStar_SMTEncoding_Term.mkITE (hd1, q12, q21)
                                q1.FStar_SMTEncoding_Term.rng
                               in
                            (labels2, uu____64788)))
              | FStar_SMTEncoding_Term.Quant
                  (FStar_SMTEncoding_Term.Exists
                   ,uu____64791,uu____64792,uu____64793,uu____64794)
                  ->
                  let uu____64813 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____64813 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Iff ,uu____64828) ->
                  let uu____64833 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____64833 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Or ,uu____64848) ->
                  let uu____64853 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____64853 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Var uu____64868,uu____64869) when
                  is_a_post_condition post_name_opt q1 -> (labels, q1)
              | FStar_SMTEncoding_Term.FreeV uu____64877 ->
                  let uu____64886 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____64886 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.TrueOp ,uu____64901) ->
                  let uu____64906 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____64906 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.FalseOp ,uu____64921) ->
                  let uu____64926 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____64926 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Not ,uu____64941) ->
                  let uu____64946 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____64946 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Eq ,uu____64961) ->
                  let uu____64966 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____64966 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.LT ,uu____64981) ->
                  let uu____64986 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____64986 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.LTE ,uu____65001) ->
                  let uu____65006 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____65006 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.GT ,uu____65021) ->
                  let uu____65026 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____65026 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.GTE ,uu____65041) ->
                  let uu____65046 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____65046 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvUlt ,uu____65061) ->
                  let uu____65066 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____65066 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Var uu____65081,uu____65082) ->
                  let uu____65088 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1
                     in
                  (match uu____65088 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.RealDiv ,uu____65103) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Add ,uu____65115) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Sub ,uu____65127) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Div ,uu____65139) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Mul ,uu____65151) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Minus ,uu____65163) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Mod ,uu____65175) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvAnd ,uu____65187) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvXor ,uu____65199) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvOr ,uu____65211) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvAdd ,uu____65223) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvSub ,uu____65235) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvShl ,uu____65247) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvShr ,uu____65259) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvUdiv ,uu____65271) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvMod ,uu____65283) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvMul ,uu____65295) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvUext uu____65307,uu____65308) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.BvToNat ,uu____65321) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.NatToBv uu____65333,uu____65334) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.ITE ,uu____65347) ->
                  failwith "Impossible: arity mismatch"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Imp ,uu____65359) ->
                  failwith "Impossible: arity mismatch"
              | FStar_SMTEncoding_Term.Quant
                  (FStar_SMTEncoding_Term.Forall ,pats,iopt,sorts,body) ->
                  let uu____65393 =
                    aux default_msg ropt post_name_opt labels body  in
                  (match uu____65393 with
                   | (labels1,body1) ->
                       let uu____65412 =
                         FStar_SMTEncoding_Term.mk
                           (FStar_SMTEncoding_Term.Quant
                              (FStar_SMTEncoding_Term.Forall, pats, iopt,
                                sorts, body1)) q1.FStar_SMTEncoding_Term.rng
                          in
                       (labels1, uu____65412))
              | FStar_SMTEncoding_Term.Let (es,body) ->
                  let uu____65430 =
                    aux default_msg ropt post_name_opt labels body  in
                  (match uu____65430 with
                   | (labels1,body1) ->
                       let uu____65449 =
                         FStar_SMTEncoding_Term.mkLet (es, body1)
                           q1.FStar_SMTEncoding_Term.rng
                          in
                       (labels1, uu____65449))
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
          let print_banner uu____65493 =
            let msg =
              let uu____65496 =
                let uu____65498 = FStar_TypeChecker_Env.get_range env  in
                FStar_Range.string_of_range uu____65498  in
              let uu____65499 =
                FStar_Util.string_of_int (Prims.parse_int "5")  in
              let uu____65502 =
                FStar_Util.string_of_int (FStar_List.length all_labels)  in
              FStar_Util.format4
                "Detailed %s report follows for %s\nTaking %s seconds per proof obligation (%s proofs in total)\n"
                (if hint_replay then "hint replay" else "error") uu____65496
                uu____65499 uu____65502
               in
            FStar_Util.print_error msg  in
          let print_result uu____65528 =
            match uu____65528 with
            | ((uu____65541,msg,r),success) ->
                if success
                then
                  let uu____65557 = FStar_Range.string_of_range r  in
                  FStar_Util.print1
                    "OK: proof obligation at %s was proven in isolation\n"
                    uu____65557
                else
                  if hint_replay
                  then
                    FStar_Errors.log_issue r
                      (FStar_Errors.Warning_HintFailedToReplayProof,
                        (Prims.op_Hat
                           "Hint failed to replay this sub-proof: " msg))
                  else
                    (let uu____65567 =
                       let uu____65573 =
                         let uu____65575 = FStar_Range.string_of_range r  in
                         FStar_Util.format2
                           "XX: proof obligation at %s failed\n\t%s\n"
                           uu____65575 msg
                          in
                       (FStar_Errors.Error_ProofObligationFailed,
                         uu____65573)
                        in
                     FStar_Errors.log_issue r uu____65567)
             in
          let elim labs =
            FStar_All.pipe_right labs
              (FStar_List.map
                 (fun uu____65628  ->
                    match uu____65628 with
                    | (l,uu____65637,uu____65638) ->
                        let a =
                          let uu____65642 =
                            let uu____65643 =
                              let uu____65648 =
                                FStar_SMTEncoding_Util.mkFreeV l  in
                              (uu____65648, FStar_SMTEncoding_Util.mkTrue)
                               in
                            FStar_SMTEncoding_Util.mkEq uu____65643  in
                          let uu____65649 =
                            let uu____65651 =
                              FStar_SMTEncoding_Term.fv_name l  in
                            Prims.op_Hat "@disable_label_" uu____65651  in
                          {
                            FStar_SMTEncoding_Term.assumption_term =
                              uu____65642;
                            FStar_SMTEncoding_Term.assumption_caption =
                              (FStar_Pervasives_Native.Some "Disabling label");
                            FStar_SMTEncoding_Term.assumption_name =
                              uu____65649;
                            FStar_SMTEncoding_Term.assumption_fact_ids = []
                          }  in
                        FStar_SMTEncoding_Term.Assume a))
             in
          let rec linear_check eliminated errors active =
            FStar_SMTEncoding_Z3.refresh ();
            (match active with
             | [] ->
                 let results =
                   let uu____65721 =
                     FStar_List.map (fun x  -> (x, true)) eliminated  in
                   let uu____65738 =
                     FStar_List.map (fun x  -> (x, false)) errors  in
                   FStar_List.append uu____65721 uu____65738  in
                 sort_labels results
             | hd1::tl1 ->
                 ((let uu____65765 =
                     FStar_Util.string_of_int (FStar_List.length active)  in
                   FStar_Util.print1 "%s, " uu____65765);
                  (let decls =
                     FStar_All.pipe_left elim
                       (FStar_List.append eliminated
                          (FStar_List.append errors tl1))
                      in
                   let result = askZ3 decls  in
                   match result.FStar_SMTEncoding_Z3.z3result_status with
                   | FStar_SMTEncoding_Z3.UNSAT uu____65797 ->
                       linear_check (hd1 :: eliminated) errors tl1
                   | uu____65798 ->
                       linear_check eliminated (hd1 :: errors) tl1)))
             in
          print_banner ();
          FStar_Options.set_option "z3rlimit"
            (FStar_Options.Int (Prims.parse_int "5"));
          (let res = linear_check [] [] all_labels  in
           FStar_Util.print_string "\n";
           FStar_All.pipe_right res (FStar_List.iter print_result);
           (let uu____65847 =
              FStar_Util.for_all FStar_Pervasives_Native.snd res  in
            if uu____65847
            then
              FStar_Util.print_string
                "Failed: the heuristic of trying each proof in isolation failed to identify a precise error\n"
            else ()))
  