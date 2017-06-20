open Prims
exception Not_a_wp_implication of Prims.string
let uu___is_Not_a_wp_implication: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Not_a_wp_implication uu____8 -> true
    | uu____9 -> false
let __proj__Not_a_wp_implication__item__uu___: Prims.exn -> Prims.string =
  fun projectee  ->
    match projectee with | Not_a_wp_implication uu____17 -> uu____17
type label = FStar_SMTEncoding_Term.error_label
type labels = FStar_SMTEncoding_Term.error_labels
let sort_labels:
  (FStar_SMTEncoding_Term.error_label* Prims.bool) Prims.list ->
    ((FStar_SMTEncoding_Term.fv* Prims.string* FStar_Range.range)*
      Prims.bool) Prims.list
  =
  fun l  ->
    FStar_List.sortWith
      (fun uu____39  ->
         fun uu____40  ->
           match (uu____39, uu____40) with
           | (((uu____61,uu____62,r1),uu____64),((uu____65,uu____66,r2),uu____68))
               -> FStar_Range.compare r1 r2) l
let remove_dups:
  labels ->
    (FStar_SMTEncoding_Term.fv* Prims.string* FStar_Range.range) Prims.list
  =
  fun l  ->
    FStar_Util.remove_dups
      (fun uu____96  ->
         fun uu____97  ->
           match (uu____96, uu____97) with
           | ((uu____110,m1,r1),(uu____113,m2,r2)) -> (r1 = r2) && (m1 = m2))
      l
type msg = (Prims.string* FStar_Range.range)
type ranges = (Prims.string option* FStar_Range.range) Prims.list
let fresh_label:
  Prims.string ->
    FStar_Range.range ->
      FStar_SMTEncoding_Term.term ->
        (((Prims.string* FStar_SMTEncoding_Term.sort)* Prims.string*
          FStar_Range.range)* FStar_SMTEncoding_Term.term)
  =
  let ctr = FStar_Util.mk_ref (Prims.parse_int "0") in
  fun message  ->
    fun range  ->
      fun t  ->
        let l =
          FStar_Util.incr ctr;
          (let uu____150 =
             let uu____151 = FStar_ST.read ctr in
             FStar_Util.string_of_int uu____151 in
           FStar_Util.format1 "label_%s" uu____150) in
        let lvar = (l, FStar_SMTEncoding_Term.Bool_sort) in
        let label = (lvar, message, range) in
        let lterm = FStar_SMTEncoding_Util.mkFreeV lvar in
        let lt1 = FStar_SMTEncoding_Term.mkOr (lterm, t) range in
        (label, lt1)
let label_goals:
  (Prims.unit -> Prims.string) option ->
    FStar_Range.range ->
      FStar_SMTEncoding_Term.term -> (labels* FStar_SMTEncoding_Term.term)
  =
  fun use_env_msg  ->
    fun r  ->
      fun q  ->
        let rec is_a_post_condition post_name_opt tm =
          match (post_name_opt, (tm.FStar_SMTEncoding_Term.tm)) with
          | (None ,uu____205) -> false
          | (Some nm,FStar_SMTEncoding_Term.FreeV (nm',uu____209)) ->
              nm = nm'
          | (uu____211,FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var "Valid",tm1::[])) ->
              is_a_post_condition post_name_opt tm1
          | (uu____216,FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var "ApplyTT",tm1::uu____218)) ->
              is_a_post_condition post_name_opt tm1
          | uu____223 -> false in
        let conjuncts t =
          match t.FStar_SMTEncoding_Term.tm with
          | FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And ,cs) -> cs
          | uu____236 -> [t] in
        let is_guard_free tm =
          match tm.FStar_SMTEncoding_Term.tm with
          | FStar_SMTEncoding_Term.Quant
              (FStar_SMTEncoding_Term.Forall
               ,({
                   FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App
                     (FStar_SMTEncoding_Term.Var "Prims.guard_free",p::[]);
                   FStar_SMTEncoding_Term.freevars = uu____242;
                   FStar_SMTEncoding_Term.rng = uu____243;_}::[])::[],iopt,uu____245,
               {
                 FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App
                   (FStar_SMTEncoding_Term.Iff ,l::r1::[]);
                 FStar_SMTEncoding_Term.freevars = uu____248;
                 FStar_SMTEncoding_Term.rng = uu____249;_})
              -> true
          | uu____268 -> false in
        let is_a_named_continuation lhs =
          FStar_All.pipe_right (conjuncts lhs)
            (FStar_Util.for_some is_guard_free) in
        let uu____274 =
          match use_env_msg with
          | None  -> (false, "")
          | Some f -> let uu____286 = f () in (true, uu____286) in
        match uu____274 with
        | (flag,msg_prefix) ->
            let fresh_label1 msg ropt rng t =
              let msg1 =
                if flag
                then Prims.strcat "Failed to verify implicit argument: " msg
                else msg in
              let rng1 =
                match ropt with
                | None  -> rng
                | Some r1 ->
                    let uu___105_312 = r1 in
                    {
                      FStar_Range.def_range = (rng.FStar_Range.def_range);
                      FStar_Range.use_range =
                        (uu___105_312.FStar_Range.use_range)
                    } in
              fresh_label msg1 rng1 t in
            let rec aux default_msg ropt post_name_opt labels q1 =
              match q1.FStar_SMTEncoding_Term.tm with
              | FStar_SMTEncoding_Term.BoundV uu____341 -> (labels, q1)
              | FStar_SMTEncoding_Term.Integer uu____343 -> (labels, q1)
              | FStar_SMTEncoding_Term.LblPos uu____345 ->
                  failwith "Impossible"
              | FStar_SMTEncoding_Term.Labeled
                  (arg,"could not prove post-condition",uu____352) ->
                  let fallback msg =
                    aux default_msg ropt post_name_opt labels arg in
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
                                                     = uu____376;
                                                   FStar_SMTEncoding_Term.rng
                                                     = rng;_})
                         ->
                         let post_name =
                           let uu____392 =
                             let uu____393 = FStar_Syntax_Syntax.next_id () in
                             FStar_All.pipe_left FStar_Util.string_of_int
                               uu____393 in
                           Prims.strcat "^^post_condition_" uu____392 in
                         let names1 =
                           let uu____398 =
                             FStar_List.mapi
                               (fun i  ->
                                  fun s  ->
                                    let uu____406 =
                                      let uu____407 =
                                        FStar_Util.string_of_int i in
                                      Prims.strcat "^^" uu____407 in
                                    (uu____406, s)) sorts in
                           (post_name, post) :: uu____398 in
                         let instantiation =
                           FStar_List.map FStar_SMTEncoding_Util.mkFreeV
                             names1 in
                         let uu____414 =
                           let uu____417 =
                             FStar_SMTEncoding_Term.inst instantiation lhs in
                           let uu____418 =
                             FStar_SMTEncoding_Term.inst instantiation rhs in
                           (uu____417, uu____418) in
                         (match uu____414 with
                          | (lhs1,rhs1) ->
                              let uu____424 =
                                match lhs1.FStar_SMTEncoding_Term.tm with
                                | FStar_SMTEncoding_Term.App
                                    (FStar_SMTEncoding_Term.And ,clauses_lhs)
                                    ->
                                    let uu____434 =
                                      FStar_Util.prefix clauses_lhs in
                                    (match uu____434 with
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
                                                   = uu____453;
                                                 FStar_SMTEncoding_Term.rng =
                                                   rng_ens;_})
                                              when
                                              is_a_post_condition
                                                (Some post_name) post1
                                              ->
                                              let uu____468 =
                                                aux
                                                  "could not prove post-condition"
                                                  None (Some post_name)
                                                  labels ensures_conjuncts in
                                              (match uu____468 with
                                               | (labels1,ensures_conjuncts1)
                                                   ->
                                                   let pats_ens1 =
                                                     match pats_ens with
                                                     | [] -> [[post1]]
                                                     | []::[] -> [[post1]]
                                                     | uu____491 -> pats_ens in
                                                   let ens1 =
                                                     let uu____495 =
                                                       let uu____496 =
                                                         let uu____506 =
                                                           FStar_SMTEncoding_Term.mk
                                                             (FStar_SMTEncoding_Term.App
                                                                (FStar_SMTEncoding_Term.Imp,
                                                                  [ensures_conjuncts1;
                                                                  post1]))
                                                             rng_ens in
                                                         (FStar_SMTEncoding_Term.Forall,
                                                           pats_ens1,
                                                           iopt_ens,
                                                           sorts_ens,
                                                           uu____506) in
                                                       FStar_SMTEncoding_Term.Quant
                                                         uu____496 in
                                                     FStar_SMTEncoding_Term.mk
                                                       uu____495
                                                       ens.FStar_SMTEncoding_Term.rng in
                                                   let lhs2 =
                                                     FStar_SMTEncoding_Term.mk
                                                       (FStar_SMTEncoding_Term.App
                                                          (FStar_SMTEncoding_Term.And,
                                                            (FStar_List.append
                                                               req [ens1])))
                                                       lhs1.FStar_SMTEncoding_Term.rng in
                                                   let uu____514 =
                                                     FStar_SMTEncoding_Term.abstr
                                                       names1 lhs2 in
                                                   (labels1, uu____514))
                                          | uu____516 ->
                                              let uu____517 =
                                                let uu____518 =
                                                  let uu____519 =
                                                    let uu____520 =
                                                      let uu____521 =
                                                        FStar_SMTEncoding_Term.print_smt_term
                                                          ens in
                                                      Prims.strcat "  ... "
                                                        uu____521 in
                                                    Prims.strcat post_name
                                                      uu____520 in
                                                  Prims.strcat
                                                    "Ensures clause doesn't match post name:  "
                                                    uu____519 in
                                                Not_a_wp_implication
                                                  uu____518 in
                                              raise uu____517))
                                | uu____525 ->
                                    let uu____526 =
                                      let uu____527 =
                                        let uu____528 =
                                          FStar_SMTEncoding_Term.print_smt_term
                                            lhs1 in
                                        Prims.strcat "LHS not a conjunct: "
                                          uu____528 in
                                      Not_a_wp_implication uu____527 in
                                    raise uu____526 in
                              (match uu____424 with
                               | (labels1,lhs2) ->
                                   let uu____539 =
                                     let uu____543 =
                                       aux default_msg None (Some post_name)
                                         labels1 rhs1 in
                                     match uu____543 with
                                     | (labels2,rhs2) ->
                                         let uu____554 =
                                           FStar_SMTEncoding_Term.abstr
                                             names1 rhs2 in
                                         (labels2, uu____554) in
                                   (match uu____539 with
                                    | (labels2,rhs2) ->
                                        let body =
                                          FStar_SMTEncoding_Term.mkImp
                                            (lhs2, rhs2) rng in
                                        let uu____564 =
                                          FStar_SMTEncoding_Term.mk
                                            (FStar_SMTEncoding_Term.Quant
                                               (FStar_SMTEncoding_Term.Forall,
                                                 pats, iopt, (post :: sorts),
                                                 body))
                                            q1.FStar_SMTEncoding_Term.rng in
                                        (labels2, uu____564))))
                     | uu____570 ->
                         let uu____571 =
                           let uu____572 =
                             FStar_SMTEncoding_Term.print_smt_term arg in
                           Prims.strcat "arg not a quant: " uu____572 in
                         fallback uu____571
                   with | Not_a_wp_implication msg -> fallback msg)
              | FStar_SMTEncoding_Term.Labeled (arg,reason,r1) ->
                  aux reason (Some r1) post_name_opt labels arg
              | FStar_SMTEncoding_Term.Quant
                  (FStar_SMTEncoding_Term.Forall ,[],None
                   ,post::[],{
                               FStar_SMTEncoding_Term.tm =
                                 FStar_SMTEncoding_Term.App
                                 (FStar_SMTEncoding_Term.Imp ,lhs::rhs::[]);
                               FStar_SMTEncoding_Term.freevars = uu____584;
                               FStar_SMTEncoding_Term.rng = rng;_})
                  when is_a_named_continuation lhs ->
                  let post_name =
                    let uu____597 =
                      let uu____598 = FStar_Syntax_Syntax.next_id () in
                      FStar_All.pipe_left FStar_Util.string_of_int uu____598 in
                    Prims.strcat "^^post_condition_" uu____597 in
                  let names1 = (post_name, post) in
                  let instantiation =
                    let uu____604 = FStar_SMTEncoding_Util.mkFreeV names1 in
                    [uu____604] in
                  let uu____605 =
                    let uu____608 =
                      FStar_SMTEncoding_Term.inst instantiation lhs in
                    let uu____609 =
                      FStar_SMTEncoding_Term.inst instantiation rhs in
                    (uu____608, uu____609) in
                  (match uu____605 with
                   | (lhs1,rhs1) ->
                       let uu____615 =
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
                                           uu____628;
                                         FStar_SMTEncoding_Term.rng =
                                           uu____629;_}::[])::[],iopt,sorts,
                                     {
                                       FStar_SMTEncoding_Term.tm =
                                         FStar_SMTEncoding_Term.App
                                         (FStar_SMTEncoding_Term.Iff
                                          ,l::r1::[]);
                                       FStar_SMTEncoding_Term.freevars =
                                         uu____634;
                                       FStar_SMTEncoding_Term.rng = uu____635;_})
                                    ->
                                    let uu____654 =
                                      aux default_msg None post_name_opt
                                        labels1 r1 in
                                    (match uu____654 with
                                     | (labels2,r2) ->
                                         let uu____665 =
                                           let uu____666 =
                                             let uu____667 =
                                               let uu____677 =
                                                 FStar_SMTEncoding_Util.norng
                                                   FStar_SMTEncoding_Term.mk
                                                   (FStar_SMTEncoding_Term.App
                                                      (FStar_SMTEncoding_Term.Iff,
                                                        [l; r2])) in
                                               (FStar_SMTEncoding_Term.Forall,
                                                 [[p]],
                                                 (Some (Prims.parse_int "0")),
                                                 sorts, uu____677) in
                                             FStar_SMTEncoding_Term.Quant
                                               uu____667 in
                                           FStar_SMTEncoding_Term.mk
                                             uu____666
                                             q1.FStar_SMTEncoding_Term.rng in
                                         (labels2, uu____665))
                                | uu____686 -> (labels1, tm)) labels
                           (conjuncts lhs1) in
                       (match uu____615 with
                        | (labels1,lhs_conjs) ->
                            let uu____697 =
                              aux default_msg None (Some post_name) labels1
                                rhs1 in
                            (match uu____697 with
                             | (labels2,rhs2) ->
                                 let body =
                                   let uu____709 =
                                     let uu____710 =
                                       let uu____713 =
                                         FStar_SMTEncoding_Term.mk_and_l
                                           lhs_conjs
                                           lhs1.FStar_SMTEncoding_Term.rng in
                                       (uu____713, rhs2) in
                                     FStar_SMTEncoding_Term.mkImp uu____710
                                       rng in
                                   FStar_All.pipe_right uu____709
                                     (FStar_SMTEncoding_Term.abstr [names1]) in
                                 let q2 =
                                   FStar_SMTEncoding_Term.mk
                                     (FStar_SMTEncoding_Term.Quant
                                        (FStar_SMTEncoding_Term.Forall, [],
                                          None, [post], body))
                                     q1.FStar_SMTEncoding_Term.rng in
                                 (labels2, q2))))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Imp ,lhs::rhs::[]) ->
                  let uu____728 =
                    aux default_msg ropt post_name_opt labels rhs in
                  (match uu____728 with
                   | (labels1,rhs1) ->
                       let uu____739 =
                         FStar_SMTEncoding_Util.mkImp (lhs, rhs1) in
                       (labels1, uu____739))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.And ,conjuncts1) ->
                  let uu____744 =
                    FStar_Util.fold_map (aux default_msg ropt post_name_opt)
                      labels conjuncts1 in
                  (match uu____744 with
                   | (labels1,conjuncts2) ->
                       let uu____759 =
                         FStar_SMTEncoding_Term.mk_and_l conjuncts2
                           q1.FStar_SMTEncoding_Term.rng in
                       (labels1, uu____759))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.ITE ,hd1::q11::q2::[]) ->
                  let uu____765 =
                    aux default_msg ropt post_name_opt labels q11 in
                  (match uu____765 with
                   | (labels1,q12) ->
                       let uu____776 =
                         aux default_msg ropt post_name_opt labels1 q2 in
                       (match uu____776 with
                        | (labels2,q21) ->
                            let uu____787 =
                              FStar_SMTEncoding_Term.mkITE (hd1, q12, q21)
                                q1.FStar_SMTEncoding_Term.rng in
                            (labels2, uu____787)))
              | FStar_SMTEncoding_Term.Quant
                  (FStar_SMTEncoding_Term.Exists
                   ,uu____789,uu____790,uu____791,uu____792)
                  ->
                  let uu____801 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____801 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Iff ,uu____810) ->
                  let uu____813 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____813 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Or ,uu____822) ->
                  let uu____825 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____825 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Var uu____834,uu____835) when
                  is_a_post_condition post_name_opt q1 -> (labels, q1)
              | FStar_SMTEncoding_Term.FreeV uu____839 ->
                  let uu____842 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____842 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.TrueOp ,uu____851) ->
                  let uu____854 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____854 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.FalseOp ,uu____863) ->
                  let uu____866 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____866 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Not ,uu____875) ->
                  let uu____878 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____878 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Eq ,uu____887) ->
                  let uu____890 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____890 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.LT ,uu____899) ->
                  let uu____902 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____902 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.LTE ,uu____911) ->
                  let uu____914 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____914 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.GT ,uu____923) ->
                  let uu____926 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____926 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.GTE ,uu____935) ->
                  let uu____938 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____938 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Var uu____947,uu____948) ->
                  let uu____951 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____951 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Add ,uu____960) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Sub ,uu____966) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Div ,uu____972) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Mul ,uu____978) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Minus ,uu____984) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Mod ,uu____990) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.ITE ,uu____996) ->
                  failwith "Impossible: arity mismatch"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Imp ,uu____1002) ->
                  failwith "Impossible: arity mismatch"
              | FStar_SMTEncoding_Term.Quant
                  (FStar_SMTEncoding_Term.Forall ,pats,iopt,sorts,body) ->
                  let uu____1020 =
                    aux default_msg ropt post_name_opt labels body in
                  (match uu____1020 with
                   | (labels1,body1) ->
                       let uu____1031 =
                         FStar_SMTEncoding_Term.mk
                           (FStar_SMTEncoding_Term.Quant
                              (FStar_SMTEncoding_Term.Forall, pats, iopt,
                                sorts, body1)) q1.FStar_SMTEncoding_Term.rng in
                       (labels1, uu____1031))
              | FStar_SMTEncoding_Term.Let (es,body) ->
                  let uu____1041 =
                    aux default_msg ropt post_name_opt labels body in
                  (match uu____1041 with
                   | (labels1,body1) ->
                       let uu____1052 =
                         FStar_SMTEncoding_Term.mkLet (es, body1)
                           q1.FStar_SMTEncoding_Term.rng in
                       (labels1, uu____1052)) in
            aux "assertion failed" None None [] q
let detail_errors:
  FStar_TypeChecker_Env.env ->
    labels ->
      (FStar_SMTEncoding_Term.decls_t ->
         ((FStar_SMTEncoding_Z3.unsat_core,(FStar_SMTEncoding_Term.error_labels*
                                             FStar_SMTEncoding_Z3.error_kind))
           FStar_Util.either* Prims.int* FStar_SMTEncoding_Z3.z3statistics))
        -> FStar_SMTEncoding_Term.error_label Prims.list
  =
  fun env  ->
    fun all_labels  ->
      fun askZ3  ->
        let print_banner uu____1089 =
          let uu____1090 =
            let uu____1091 = FStar_TypeChecker_Env.get_range env in
            FStar_Range.string_of_range uu____1091 in
          let uu____1092 = FStar_Util.string_of_int (Prims.parse_int "5") in
          let uu____1093 =
            FStar_Util.string_of_int (FStar_List.length all_labels) in
          FStar_Util.print3_error
            "Detailed error report follows for %s\nTaking %s seconds per proof obligation (%s proofs in total)\n"
            uu____1090 uu____1092 uu____1093 in
        let print_result uu____1108 =
          match uu____1108 with
          | ((uu____1114,msg,r),success) ->
              if success
              then
                let uu____1121 = FStar_Range.string_of_range r in
                FStar_Util.print1_error
                  "OK: proof obligation at %s was proven\n" uu____1121
              else FStar_Errors.err r msg in
        let elim labs =
          FStar_All.pipe_right labs
            (FStar_List.map
               (fun uu____1152  ->
                  match uu____1152 with
                  | (l,uu____1159,uu____1160) ->
                      let a =
                        let uu____1166 =
                          let uu____1167 =
                            let uu____1170 = FStar_SMTEncoding_Util.mkFreeV l in
                            (uu____1170, FStar_SMTEncoding_Util.mkTrue) in
                          FStar_SMTEncoding_Util.mkEq uu____1167 in
                        {
                          FStar_SMTEncoding_Term.assumption_term = uu____1166;
                          FStar_SMTEncoding_Term.assumption_caption =
                            (Some "Disabling label");
                          FStar_SMTEncoding_Term.assumption_name =
                            (Prims.strcat "disable_label_" (fst l));
                          FStar_SMTEncoding_Term.assumption_fact_ids = []
                        } in
                      FStar_SMTEncoding_Term.Assume a)) in
        let rec linear_check eliminated errors active =
          match active with
          | [] ->
              let results =
                let uu____1203 =
                  FStar_List.map (fun x  -> (x, true)) eliminated in
                let uu____1210 = FStar_List.map (fun x  -> (x, false)) errors in
                FStar_List.append uu____1203 uu____1210 in
              sort_labels results
          | hd1::tl1 ->
              ((let uu____1223 =
                  FStar_Util.string_of_int (FStar_List.length active) in
                FStar_Util.print1 "%s, " uu____1223);
               FStar_SMTEncoding_Z3.refresh ();
               (let uu____1231 =
                  let uu____1239 =
                    FStar_All.pipe_left elim
                      (FStar_List.append eliminated
                         (FStar_List.append errors tl1)) in
                  askZ3 uu____1239 in
                match uu____1231 with
                | (result,uu____1254,uu____1255) ->
                    let uu____1264 = FStar_Util.is_left result in
                    if uu____1264
                    then linear_check (hd1 :: eliminated) errors tl1
                    else linear_check eliminated (hd1 :: errors) tl1)) in
        print_banner ();
        FStar_Options.set_option "z3rlimit"
          (FStar_Options.Int (Prims.parse_int "5"));
        (let res = linear_check [] [] all_labels in
         FStar_Util.print_string "\n";
         FStar_All.pipe_right res (FStar_List.iter print_result);
         [])