open Prims
exception Not_a_wp_implication of Prims.string
let uu___is_Not_a_wp_implication: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Not_a_wp_implication uu____7 -> true
    | uu____8 -> false
let __proj__Not_a_wp_implication__item__uu___: Prims.exn -> Prims.string =
  fun projectee  ->
    match projectee with | Not_a_wp_implication uu____15 -> uu____15
type label = FStar_SMTEncoding_Term.error_label
type labels = FStar_SMTEncoding_Term.error_labels
let sort_labels:
  (FStar_SMTEncoding_Term.error_label* Prims.bool) Prims.list ->
    ((FStar_SMTEncoding_Term.fv* Prims.string* FStar_Range.range)*
      Prims.bool) Prims.list
  =
  fun l  ->
    FStar_List.sortWith
      (fun uu____36  ->
         fun uu____37  ->
           match (uu____36, uu____37) with
           | (((uu____58,uu____59,r1),uu____61),((uu____62,uu____63,r2),uu____65))
               -> FStar_Range.compare r1 r2) l
let remove_dups:
  labels ->
    (FStar_SMTEncoding_Term.fv* Prims.string* FStar_Range.range) Prims.list
  =
  fun l  ->
    FStar_Util.remove_dups
      (fun uu____92  ->
         fun uu____93  ->
           match (uu____92, uu____93) with
           | ((uu____106,m1,r1),(uu____109,m2,r2)) -> (r1 = r2) && (m1 = m2))
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
          (let uu____143 =
             let uu____144 = FStar_ST.read ctr in
             FStar_Util.string_of_int uu____144 in
           FStar_Util.format1 "label_%s" uu____143) in
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
          | (None ,uu____195) -> false
          | (Some nm,FStar_SMTEncoding_Term.FreeV (nm',uu____199)) ->
              nm = nm'
          | (uu____201,FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var "Valid",tm1::[])) ->
              is_a_post_condition post_name_opt tm1
          | (uu____206,FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var "ApplyTT",tm1::uu____208)) ->
              is_a_post_condition post_name_opt tm1
          | uu____213 -> false in
        let conjuncts t =
          match t.FStar_SMTEncoding_Term.tm with
          | FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And ,cs) -> cs
          | uu____226 -> [t] in
        let is_guard_free tm =
          match tm.FStar_SMTEncoding_Term.tm with
          | FStar_SMTEncoding_Term.Quant
              (FStar_SMTEncoding_Term.Forall
               ,({
                   FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App
                     (FStar_SMTEncoding_Term.Var "Prims.guard_free",p::[]);
                   FStar_SMTEncoding_Term.freevars = uu____232;
                   FStar_SMTEncoding_Term.rng = uu____233;_}::[])::[],iopt,uu____235,
               {
                 FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App
                   (FStar_SMTEncoding_Term.Iff ,l::r1::[]);
                 FStar_SMTEncoding_Term.freevars = uu____238;
                 FStar_SMTEncoding_Term.rng = uu____239;_})
              -> true
          | uu____258 -> false in
        let is_a_named_continuation lhs =
          FStar_All.pipe_right (conjuncts lhs)
            (FStar_Util.for_some is_guard_free) in
        let uu____264 =
          match use_env_msg with
          | None  -> (false, "")
          | Some f -> let uu____276 = f () in (true, uu____276) in
        match uu____264 with
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
                    let uu___103_302 = r1 in
                    {
                      FStar_Range.def_range = (rng.FStar_Range.def_range);
                      FStar_Range.use_range =
                        (uu___103_302.FStar_Range.use_range)
                    } in
              fresh_label msg1 rng1 t in
            let rec aux default_msg ropt post_name_opt labels q1 =
              match q1.FStar_SMTEncoding_Term.tm with
              | FStar_SMTEncoding_Term.BoundV uu____331 -> (labels, q1)
              | FStar_SMTEncoding_Term.Integer uu____333 -> (labels, q1)
              | FStar_SMTEncoding_Term.LblPos uu____335 ->
                  failwith "Impossible"
              | FStar_SMTEncoding_Term.Labeled
                  (arg,"could not prove post-condition",uu____342) ->
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
                                                     = uu____366;
                                                   FStar_SMTEncoding_Term.rng
                                                     = rng;_})
                         ->
                         let post_name =
                           let uu____382 =
                             let uu____383 = FStar_Syntax_Syntax.next_id () in
                             FStar_All.pipe_left FStar_Util.string_of_int
                               uu____383 in
                           Prims.strcat "^^post_condition_" uu____382 in
                         let names =
                           let uu____388 =
                             FStar_List.mapi
                               (fun i  ->
                                  fun s  ->
                                    let uu____396 =
                                      let uu____397 =
                                        FStar_Util.string_of_int i in
                                      Prims.strcat "^^" uu____397 in
                                    (uu____396, s)) sorts in
                           (post_name, post) :: uu____388 in
                         let instantiation =
                           FStar_List.map FStar_SMTEncoding_Util.mkFreeV
                             names in
                         let uu____404 =
                           let uu____407 =
                             FStar_SMTEncoding_Term.inst instantiation lhs in
                           let uu____408 =
                             FStar_SMTEncoding_Term.inst instantiation rhs in
                           (uu____407, uu____408) in
                         (match uu____404 with
                          | (lhs1,rhs1) ->
                              let uu____414 =
                                match lhs1.FStar_SMTEncoding_Term.tm with
                                | FStar_SMTEncoding_Term.App
                                    (FStar_SMTEncoding_Term.And ,clauses_lhs)
                                    ->
                                    let uu____424 =
                                      FStar_Util.prefix clauses_lhs in
                                    (match uu____424 with
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
                                                   = uu____443;
                                                 FStar_SMTEncoding_Term.rng =
                                                   rng_ens;_})
                                              when
                                              is_a_post_condition
                                                (Some post_name) post1
                                              ->
                                              let uu____458 =
                                                aux
                                                  "could not prove post-condition"
                                                  None (Some post_name)
                                                  labels ensures_conjuncts in
                                              (match uu____458 with
                                               | (labels1,ensures_conjuncts1)
                                                   ->
                                                   let pats_ens1 =
                                                     match pats_ens with
                                                     | [] -> [[post1]]
                                                     | []::[] -> [[post1]]
                                                     | uu____481 -> pats_ens in
                                                   let ens1 =
                                                     let uu____485 =
                                                       let uu____486 =
                                                         let uu____496 =
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
                                                           uu____496) in
                                                       FStar_SMTEncoding_Term.Quant
                                                         uu____486 in
                                                     FStar_SMTEncoding_Term.mk
                                                       uu____485
                                                       ens.FStar_SMTEncoding_Term.rng in
                                                   let lhs2 =
                                                     FStar_SMTEncoding_Term.mk
                                                       (FStar_SMTEncoding_Term.App
                                                          (FStar_SMTEncoding_Term.And,
                                                            (FStar_List.append
                                                               req [ens1])))
                                                       lhs1.FStar_SMTEncoding_Term.rng in
                                                   let uu____504 =
                                                     FStar_SMTEncoding_Term.abstr
                                                       names lhs2 in
                                                   (labels1, uu____504))
                                          | uu____506 ->
                                              let uu____507 =
                                                let uu____508 =
                                                  let uu____509 =
                                                    let uu____510 =
                                                      let uu____511 =
                                                        FStar_SMTEncoding_Term.print_smt_term
                                                          ens in
                                                      Prims.strcat "  ... "
                                                        uu____511 in
                                                    Prims.strcat post_name
                                                      uu____510 in
                                                  Prims.strcat
                                                    "Ensures clause doesn't match post name:  "
                                                    uu____509 in
                                                Not_a_wp_implication
                                                  uu____508 in
                                              raise uu____507))
                                | uu____515 ->
                                    let uu____516 =
                                      let uu____517 =
                                        let uu____518 =
                                          FStar_SMTEncoding_Term.print_smt_term
                                            lhs1 in
                                        Prims.strcat "LHS not a conjunct: "
                                          uu____518 in
                                      Not_a_wp_implication uu____517 in
                                    raise uu____516 in
                              (match uu____414 with
                               | (labels1,lhs2) ->
                                   let uu____529 =
                                     let uu____533 =
                                       aux default_msg None (Some post_name)
                                         labels1 rhs1 in
                                     match uu____533 with
                                     | (labels2,rhs2) ->
                                         let uu____544 =
                                           FStar_SMTEncoding_Term.abstr names
                                             rhs2 in
                                         (labels2, uu____544) in
                                   (match uu____529 with
                                    | (labels2,rhs2) ->
                                        let body =
                                          FStar_SMTEncoding_Term.mkImp
                                            (lhs2, rhs2) rng in
                                        let uu____554 =
                                          FStar_SMTEncoding_Term.mk
                                            (FStar_SMTEncoding_Term.Quant
                                               (FStar_SMTEncoding_Term.Forall,
                                                 pats, iopt, (post :: sorts),
                                                 body))
                                            q1.FStar_SMTEncoding_Term.rng in
                                        (labels2, uu____554))))
                     | uu____560 ->
                         let uu____561 =
                           let uu____562 =
                             FStar_SMTEncoding_Term.print_smt_term arg in
                           Prims.strcat "arg not a quant: " uu____562 in
                         fallback uu____561
                   with | Not_a_wp_implication msg -> fallback msg)
              | FStar_SMTEncoding_Term.Labeled (arg,reason,r1) ->
                  aux reason (Some r1) post_name_opt labels arg
              | FStar_SMTEncoding_Term.Quant
                  (FStar_SMTEncoding_Term.Forall ,[],None
                   ,post::[],{
                               FStar_SMTEncoding_Term.tm =
                                 FStar_SMTEncoding_Term.App
                                 (FStar_SMTEncoding_Term.Imp ,lhs::rhs::[]);
                               FStar_SMTEncoding_Term.freevars = uu____574;
                               FStar_SMTEncoding_Term.rng = rng;_})
                  when is_a_named_continuation lhs ->
                  let post_name =
                    let uu____587 =
                      let uu____588 = FStar_Syntax_Syntax.next_id () in
                      FStar_All.pipe_left FStar_Util.string_of_int uu____588 in
                    Prims.strcat "^^post_condition_" uu____587 in
                  let names = (post_name, post) in
                  let instantiation =
                    let uu____594 = FStar_SMTEncoding_Util.mkFreeV names in
                    [uu____594] in
                  let uu____595 =
                    let uu____598 =
                      FStar_SMTEncoding_Term.inst instantiation lhs in
                    let uu____599 =
                      FStar_SMTEncoding_Term.inst instantiation rhs in
                    (uu____598, uu____599) in
                  (match uu____595 with
                   | (lhs1,rhs1) ->
                       let uu____605 =
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
                                           uu____618;
                                         FStar_SMTEncoding_Term.rng =
                                           uu____619;_}::[])::[],iopt,sorts,
                                     {
                                       FStar_SMTEncoding_Term.tm =
                                         FStar_SMTEncoding_Term.App
                                         (FStar_SMTEncoding_Term.Iff
                                          ,l::r1::[]);
                                       FStar_SMTEncoding_Term.freevars =
                                         uu____624;
                                       FStar_SMTEncoding_Term.rng = uu____625;_})
                                    ->
                                    let uu____644 =
                                      aux default_msg None post_name_opt
                                        labels1 r1 in
                                    (match uu____644 with
                                     | (labels2,r2) ->
                                         let uu____655 =
                                           let uu____656 =
                                             let uu____657 =
                                               let uu____667 =
                                                 FStar_SMTEncoding_Util.norng
                                                   FStar_SMTEncoding_Term.mk
                                                   (FStar_SMTEncoding_Term.App
                                                      (FStar_SMTEncoding_Term.Iff,
                                                        [l; r2])) in
                                               (FStar_SMTEncoding_Term.Forall,
                                                 [[p]],
                                                 (Some (Prims.parse_int "0")),
                                                 sorts, uu____667) in
                                             FStar_SMTEncoding_Term.Quant
                                               uu____657 in
                                           FStar_SMTEncoding_Term.mk
                                             uu____656
                                             q1.FStar_SMTEncoding_Term.rng in
                                         (labels2, uu____655))
                                | uu____676 -> (labels1, tm)) labels
                           (conjuncts lhs1) in
                       (match uu____605 with
                        | (labels1,lhs_conjs) ->
                            let uu____687 =
                              aux default_msg None (Some post_name) labels1
                                rhs1 in
                            (match uu____687 with
                             | (labels2,rhs2) ->
                                 let body =
                                   let uu____699 =
                                     let uu____700 =
                                       let uu____703 =
                                         FStar_SMTEncoding_Term.mk_and_l
                                           lhs_conjs
                                           lhs1.FStar_SMTEncoding_Term.rng in
                                       (uu____703, rhs2) in
                                     FStar_SMTEncoding_Term.mkImp uu____700
                                       rng in
                                   FStar_All.pipe_right uu____699
                                     (FStar_SMTEncoding_Term.abstr [names]) in
                                 let q2 =
                                   FStar_SMTEncoding_Term.mk
                                     (FStar_SMTEncoding_Term.Quant
                                        (FStar_SMTEncoding_Term.Forall, [],
                                          None, [post], body))
                                     q1.FStar_SMTEncoding_Term.rng in
                                 (labels2, q2))))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Imp ,lhs::rhs::[]) ->
                  let uu____718 =
                    aux default_msg ropt post_name_opt labels rhs in
                  (match uu____718 with
                   | (labels1,rhs1) ->
                       let uu____729 =
                         FStar_SMTEncoding_Util.mkImp (lhs, rhs1) in
                       (labels1, uu____729))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.And ,conjuncts1) ->
                  let uu____734 =
                    FStar_Util.fold_map (aux default_msg ropt post_name_opt)
                      labels conjuncts1 in
                  (match uu____734 with
                   | (labels1,conjuncts2) ->
                       let uu____749 =
                         FStar_SMTEncoding_Term.mk_and_l conjuncts2
                           q1.FStar_SMTEncoding_Term.rng in
                       (labels1, uu____749))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.ITE ,hd1::q11::q2::[]) ->
                  let uu____755 =
                    aux default_msg ropt post_name_opt labels q11 in
                  (match uu____755 with
                   | (labels1,q12) ->
                       let uu____766 =
                         aux default_msg ropt post_name_opt labels1 q2 in
                       (match uu____766 with
                        | (labels2,q21) ->
                            let uu____777 =
                              FStar_SMTEncoding_Term.mkITE (hd1, q12, q21)
                                q1.FStar_SMTEncoding_Term.rng in
                            (labels2, uu____777)))
              | FStar_SMTEncoding_Term.Quant
                  (FStar_SMTEncoding_Term.Exists
                   ,uu____779,uu____780,uu____781,uu____782)
                  ->
                  let uu____791 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____791 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Iff ,uu____800) ->
                  let uu____803 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____803 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Or ,uu____812) ->
                  let uu____815 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____815 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Var uu____824,uu____825) when
                  is_a_post_condition post_name_opt q1 -> (labels, q1)
              | FStar_SMTEncoding_Term.FreeV uu____829 ->
                  let uu____832 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____832 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.TrueOp ,uu____841) ->
                  let uu____844 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____844 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.FalseOp ,uu____853) ->
                  let uu____856 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____856 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Not ,uu____865) ->
                  let uu____868 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____868 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Eq ,uu____877) ->
                  let uu____880 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____880 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.LT ,uu____889) ->
                  let uu____892 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____892 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.LTE ,uu____901) ->
                  let uu____904 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____904 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.GT ,uu____913) ->
                  let uu____916 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____916 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.GTE ,uu____925) ->
                  let uu____928 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____928 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Var uu____937,uu____938) ->
                  let uu____941 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____941 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Add ,uu____950) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Sub ,uu____956) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Div ,uu____962) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Mul ,uu____968) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Minus ,uu____974) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Mod ,uu____980) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.ITE ,uu____986) ->
                  failwith "Impossible: arity mismatch"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Imp ,uu____992) ->
                  failwith "Impossible: arity mismatch"
              | FStar_SMTEncoding_Term.Quant
                  (FStar_SMTEncoding_Term.Forall ,pats,iopt,sorts,body) ->
                  let uu____1010 =
                    aux default_msg ropt post_name_opt labels body in
                  (match uu____1010 with
                   | (labels1,body1) ->
                       let uu____1021 =
                         FStar_SMTEncoding_Term.mk
                           (FStar_SMTEncoding_Term.Quant
                              (FStar_SMTEncoding_Term.Forall, pats, iopt,
                                sorts, body1)) q1.FStar_SMTEncoding_Term.rng in
                       (labels1, uu____1021))
              | FStar_SMTEncoding_Term.Let (es,body) ->
                  let uu____1031 =
                    aux default_msg ropt post_name_opt labels body in
                  (match uu____1031 with
                   | (labels1,body1) ->
                       let uu____1042 =
                         FStar_SMTEncoding_Term.mkLet (es, body1)
                           q1.FStar_SMTEncoding_Term.rng in
                       (labels1, uu____1042)) in
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
        let print_banner uu____1076 =
          let uu____1077 =
            let uu____1078 = FStar_TypeChecker_Env.get_range env in
            FStar_Range.string_of_range uu____1078 in
          let uu____1079 = FStar_Util.string_of_int (Prims.parse_int "5") in
          let uu____1080 =
            FStar_Util.string_of_int (FStar_List.length all_labels) in
          FStar_Util.print3_error
            "Detailed error report follows for %s\nTaking %s seconds per proof obligation (%s proofs in total)\n"
            uu____1077 uu____1079 uu____1080 in
        let print_result uu____1092 =
          match uu____1092 with
          | ((uu____1098,msg,r),success) ->
              if success
              then
                let uu____1105 = FStar_Range.string_of_range r in
                FStar_Util.print1_error
                  "OK: proof obligation at %s was proven\n" uu____1105
              else FStar_Errors.err r msg in
        let elim labs =
          FStar_All.pipe_right labs
            (FStar_List.map
               (fun uu____1136  ->
                  match uu____1136 with
                  | (l,uu____1143,uu____1144) ->
                      let a =
                        let uu____1150 =
                          let uu____1151 =
                            let uu____1154 = FStar_SMTEncoding_Util.mkFreeV l in
                            (uu____1154, FStar_SMTEncoding_Util.mkTrue) in
                          FStar_SMTEncoding_Util.mkEq uu____1151 in
                        {
                          FStar_SMTEncoding_Term.assumption_term = uu____1150;
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
                let uu____1187 =
                  FStar_List.map (fun x  -> (x, true)) eliminated in
                let uu____1194 = FStar_List.map (fun x  -> (x, false)) errors in
                FStar_List.append uu____1187 uu____1194 in
              sort_labels results
          | hd1::tl1 ->
              ((let uu____1207 =
                  FStar_Util.string_of_int (FStar_List.length active) in
                FStar_Util.print1 "%s, " uu____1207);
               FStar_SMTEncoding_Z3.refresh ();
               (let uu____1212 =
                  let uu____1220 =
                    FStar_All.pipe_left elim
                      (FStar_List.append eliminated
                         (FStar_List.append errors tl1)) in
                  askZ3 uu____1220 in
                match uu____1212 with
                | (result,uu____1235,uu____1236) ->
                    let uu____1245 = FStar_Util.is_left result in
                    if uu____1245
                    then linear_check (hd1 :: eliminated) errors tl1
                    else linear_check eliminated (hd1 :: errors) tl1)) in
        print_banner ();
        FStar_Options.set_option "z3rlimit"
          (FStar_Options.Int (Prims.parse_int "5"));
        (let res = linear_check [] [] all_labels in
         FStar_Util.print_string "\n";
         FStar_All.pipe_right res (FStar_List.iter print_result);
         [])