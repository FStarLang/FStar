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
      (fun uu____46  ->
         fun uu____47  ->
           match (uu____46, uu____47) with
           | (((uu____68,uu____69,r1),uu____71),((uu____72,uu____73,r2),uu____75))
               -> FStar_Range.compare r1 r2) l
let remove_dups:
  labels ->
    (FStar_SMTEncoding_Term.fv* Prims.string* FStar_Range.range) Prims.list
  =
  fun l  ->
    FStar_Util.remove_dups
      (fun uu____110  ->
         fun uu____111  ->
           match (uu____110, uu____111) with
           | ((uu____124,m1,r1),(uu____127,m2,r2)) -> (r1 = r2) && (m1 = m2))
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
          (let uu____161 =
             let uu____162 = FStar_ST.read ctr in
             FStar_Util.string_of_int uu____162 in
           FStar_Util.format1 "label_%s" uu____161) in
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
          | (None ,uu____213) -> false
          | (Some nm,FStar_SMTEncoding_Term.FreeV (nm',uu____217)) ->
              nm = nm'
          | (uu____219,FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var "Valid",tm1::[])) ->
              is_a_post_condition post_name_opt tm1
          | (uu____224,FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var "ApplyTT",tm1::uu____226)) ->
              is_a_post_condition post_name_opt tm1
          | uu____231 -> false in
        let conjuncts t =
          match t.FStar_SMTEncoding_Term.tm with
          | FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And ,cs) -> cs
          | uu____244 -> [t] in
        let is_guard_free tm =
          match tm.FStar_SMTEncoding_Term.tm with
          | FStar_SMTEncoding_Term.Quant
              (FStar_SMTEncoding_Term.Forall
               ,({
                   FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App
                     (FStar_SMTEncoding_Term.Var "Prims.guard_free",p::[]);
                   FStar_SMTEncoding_Term.freevars = uu____250;
                   FStar_SMTEncoding_Term.rng = uu____251;_}::[])::[],iopt,uu____253,
               {
                 FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App
                   (FStar_SMTEncoding_Term.Iff ,l::r1::[]);
                 FStar_SMTEncoding_Term.freevars = uu____256;
                 FStar_SMTEncoding_Term.rng = uu____257;_})
              -> true
          | uu____276 -> false in
        let is_a_named_continuation lhs =
          FStar_All.pipe_right (conjuncts lhs)
            (FStar_Util.for_some is_guard_free) in
        let uu____282 =
          match use_env_msg with
          | None  -> (false, "")
          | Some f -> let uu____294 = f () in (true, uu____294) in
        match uu____282 with
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
                    let uu___103_320 = r1 in
                    {
                      FStar_Range.def_range = (rng.FStar_Range.def_range);
                      FStar_Range.use_range =
                        (uu___103_320.FStar_Range.use_range)
                    } in
              fresh_label msg1 rng1 t in
            let rec aux default_msg ropt post_name_opt labels q1 =
              match q1.FStar_SMTEncoding_Term.tm with
              | FStar_SMTEncoding_Term.BoundV uu____349 -> (labels, q1)
              | FStar_SMTEncoding_Term.Integer uu____351 -> (labels, q1)
              | FStar_SMTEncoding_Term.LblPos uu____353 ->
                  failwith "Impossible"
              | FStar_SMTEncoding_Term.Labeled
                  (arg,"could not prove post-condition",uu____360) ->
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
                                                     = uu____407;
                                                   FStar_SMTEncoding_Term.rng
                                                     = rng;_})
                         ->
                         let post_name =
                           let uu____423 =
                             let uu____424 = FStar_Syntax_Syntax.next_id () in
                             FStar_All.pipe_left FStar_Util.string_of_int
                               uu____424 in
                           Prims.strcat "^^post_condition_" uu____423 in
                         let names =
                           let uu____429 =
                             FStar_List.mapi
                               (fun i  ->
                                  fun s  ->
                                    let uu____440 =
                                      let uu____441 =
                                        FStar_Util.string_of_int i in
                                      Prims.strcat "^^" uu____441 in
                                    (uu____440, s)) sorts in
                           (post_name, post) :: uu____429 in
                         let instantiation =
                           FStar_List.map FStar_SMTEncoding_Util.mkFreeV
                             names in
                         let uu____448 =
                           let uu____451 =
                             FStar_SMTEncoding_Term.inst instantiation lhs in
                           let uu____452 =
                             FStar_SMTEncoding_Term.inst instantiation rhs in
                           (uu____451, uu____452) in
                         (match uu____448 with
                          | (lhs1,rhs1) ->
                              let uu____458 =
                                match lhs1.FStar_SMTEncoding_Term.tm with
                                | FStar_SMTEncoding_Term.App
                                    (FStar_SMTEncoding_Term.And ,clauses_lhs)
                                    ->
                                    let uu____468 =
                                      FStar_Util.prefix clauses_lhs in
                                    (match uu____468 with
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
                                                   = uu____487;
                                                 FStar_SMTEncoding_Term.rng =
                                                   rng_ens;_})
                                              when
                                              is_a_post_condition
                                                (Some post_name) post1
                                              ->
                                              let uu____502 =
                                                aux
                                                  "could not prove post-condition"
                                                  None (Some post_name)
                                                  labels ensures_conjuncts in
                                              (match uu____502 with
                                               | (labels1,ensures_conjuncts1)
                                                   ->
                                                   let pats_ens1 =
                                                     match pats_ens with
                                                     | [] -> [[post1]]
                                                     | []::[] -> [[post1]]
                                                     | uu____525 -> pats_ens in
                                                   let ens1 =
                                                     let uu____529 =
                                                       let uu____530 =
                                                         let uu____540 =
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
                                                           uu____540) in
                                                       FStar_SMTEncoding_Term.Quant
                                                         uu____530 in
                                                     FStar_SMTEncoding_Term.mk
                                                       uu____529
                                                       ens.FStar_SMTEncoding_Term.rng in
                                                   let lhs2 =
                                                     FStar_SMTEncoding_Term.mk
                                                       (FStar_SMTEncoding_Term.App
                                                          (FStar_SMTEncoding_Term.And,
                                                            (FStar_List.append
                                                               req [ens1])))
                                                       lhs1.FStar_SMTEncoding_Term.rng in
                                                   let uu____548 =
                                                     FStar_SMTEncoding_Term.abstr
                                                       names lhs2 in
                                                   (labels1, uu____548))
                                          | uu____550 ->
                                              let uu____551 =
                                                let uu____552 =
                                                  let uu____553 =
                                                    let uu____554 =
                                                      let uu____555 =
                                                        FStar_SMTEncoding_Term.print_smt_term
                                                          ens in
                                                      Prims.strcat "  ... "
                                                        uu____555 in
                                                    Prims.strcat post_name
                                                      uu____554 in
                                                  Prims.strcat
                                                    "Ensures clause doesn't match post name:  "
                                                    uu____553 in
                                                Not_a_wp_implication
                                                  uu____552 in
                                              raise uu____551))
                                | uu____559 ->
                                    let uu____560 =
                                      let uu____561 =
                                        let uu____562 =
                                          FStar_SMTEncoding_Term.print_smt_term
                                            lhs1 in
                                        Prims.strcat "LHS not a conjunct: "
                                          uu____562 in
                                      Not_a_wp_implication uu____561 in
                                    raise uu____560 in
                              (match uu____458 with
                               | (labels1,lhs2) ->
                                   let uu____573 =
                                     let uu____577 =
                                       aux default_msg None (Some post_name)
                                         labels1 rhs1 in
                                     match uu____577 with
                                     | (labels2,rhs2) ->
                                         let uu____588 =
                                           FStar_SMTEncoding_Term.abstr names
                                             rhs2 in
                                         (labels2, uu____588) in
                                   (match uu____573 with
                                    | (labels2,rhs2) ->
                                        let body =
                                          FStar_SMTEncoding_Term.mkImp
                                            (lhs2, rhs2) rng in
                                        let uu____598 =
                                          FStar_SMTEncoding_Term.mk
                                            (FStar_SMTEncoding_Term.Quant
                                               (FStar_SMTEncoding_Term.Forall,
                                                 pats, iopt, (post :: sorts),
                                                 body))
                                            q1.FStar_SMTEncoding_Term.rng in
                                        (labels2, uu____598))))
                     | uu____604 ->
                         let uu____605 =
                           let uu____606 =
                             FStar_SMTEncoding_Term.print_smt_term arg in
                           Prims.strcat "arg not a quant: " uu____606 in
                         fallback uu____605
                   with | Not_a_wp_implication msg -> fallback msg)
              | FStar_SMTEncoding_Term.Labeled (arg,reason,r1) ->
                  aux reason (Some r1) post_name_opt labels arg
              | FStar_SMTEncoding_Term.Quant
                  (FStar_SMTEncoding_Term.Forall ,[],None
                   ,post::[],{
                               FStar_SMTEncoding_Term.tm =
                                 FStar_SMTEncoding_Term.App
                                 (FStar_SMTEncoding_Term.Imp ,lhs::rhs::[]);
                               FStar_SMTEncoding_Term.freevars = uu____620;
                               FStar_SMTEncoding_Term.rng = rng;_})
                  when is_a_named_continuation lhs ->
                  let post_name =
                    let uu____633 =
                      let uu____634 = FStar_Syntax_Syntax.next_id () in
                      FStar_All.pipe_left FStar_Util.string_of_int uu____634 in
                    Prims.strcat "^^post_condition_" uu____633 in
                  let names = (post_name, post) in
                  let instantiation =
                    let uu____640 = FStar_SMTEncoding_Util.mkFreeV names in
                    [uu____640] in
                  let uu____641 =
                    let uu____644 =
                      FStar_SMTEncoding_Term.inst instantiation lhs in
                    let uu____645 =
                      FStar_SMTEncoding_Term.inst instantiation rhs in
                    (uu____644, uu____645) in
                  (match uu____641 with
                   | (lhs1,rhs1) ->
                       let uu____651 =
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
                                           uu____679;
                                         FStar_SMTEncoding_Term.rng =
                                           uu____680;_}::[])::[],iopt,sorts,
                                     {
                                       FStar_SMTEncoding_Term.tm =
                                         FStar_SMTEncoding_Term.App
                                         (FStar_SMTEncoding_Term.Iff
                                          ,l::r1::[]);
                                       FStar_SMTEncoding_Term.freevars =
                                         uu____685;
                                       FStar_SMTEncoding_Term.rng = uu____686;_})
                                    ->
                                    let uu____705 =
                                      aux default_msg None post_name_opt
                                        labels1 r1 in
                                    (match uu____705 with
                                     | (labels2,r2) ->
                                         let uu____716 =
                                           let uu____717 =
                                             let uu____718 =
                                               let uu____728 =
                                                 FStar_SMTEncoding_Util.norng
                                                   FStar_SMTEncoding_Term.mk
                                                   (FStar_SMTEncoding_Term.App
                                                      (FStar_SMTEncoding_Term.Iff,
                                                        [l; r2])) in
                                               (FStar_SMTEncoding_Term.Forall,
                                                 [[p]],
                                                 (Some (Prims.parse_int "0")),
                                                 sorts, uu____728) in
                                             FStar_SMTEncoding_Term.Quant
                                               uu____718 in
                                           FStar_SMTEncoding_Term.mk
                                             uu____717
                                             q1.FStar_SMTEncoding_Term.rng in
                                         (labels2, uu____716))
                                | uu____737 -> (labels1, tm)) labels
                           (conjuncts lhs1) in
                       (match uu____651 with
                        | (labels1,lhs_conjs) ->
                            let uu____748 =
                              aux default_msg None (Some post_name) labels1
                                rhs1 in
                            (match uu____748 with
                             | (labels2,rhs2) ->
                                 let body =
                                   let uu____760 =
                                     let uu____761 =
                                       let uu____764 =
                                         FStar_SMTEncoding_Term.mk_and_l
                                           lhs_conjs
                                           lhs1.FStar_SMTEncoding_Term.rng in
                                       (uu____764, rhs2) in
                                     FStar_SMTEncoding_Term.mkImp uu____761
                                       rng in
                                   FStar_All.pipe_right uu____760
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
                  let uu____779 =
                    aux default_msg ropt post_name_opt labels rhs in
                  (match uu____779 with
                   | (labels1,rhs1) ->
                       let uu____790 =
                         FStar_SMTEncoding_Util.mkImp (lhs, rhs1) in
                       (labels1, uu____790))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.And ,conjuncts1) ->
                  let uu____795 =
                    FStar_Util.fold_map (aux default_msg ropt post_name_opt)
                      labels conjuncts1 in
                  (match uu____795 with
                   | (labels1,conjuncts2) ->
                       let uu____810 =
                         FStar_SMTEncoding_Term.mk_and_l conjuncts2
                           q1.FStar_SMTEncoding_Term.rng in
                       (labels1, uu____810))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.ITE ,hd1::q11::q2::[]) ->
                  let uu____816 =
                    aux default_msg ropt post_name_opt labels q11 in
                  (match uu____816 with
                   | (labels1,q12) ->
                       let uu____827 =
                         aux default_msg ropt post_name_opt labels1 q2 in
                       (match uu____827 with
                        | (labels2,q21) ->
                            let uu____838 =
                              FStar_SMTEncoding_Term.mkITE (hd1, q12, q21)
                                q1.FStar_SMTEncoding_Term.rng in
                            (labels2, uu____838)))
              | FStar_SMTEncoding_Term.Quant
                  (FStar_SMTEncoding_Term.Exists
                   ,uu____840,uu____841,uu____842,uu____843)
                  ->
                  let uu____852 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____852 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Iff ,uu____861) ->
                  let uu____864 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____864 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Or ,uu____873) ->
                  let uu____876 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____876 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Var uu____885,uu____886) when
                  is_a_post_condition post_name_opt q1 -> (labels, q1)
              | FStar_SMTEncoding_Term.FreeV uu____890 ->
                  let uu____893 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____893 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.TrueOp ,uu____902) ->
                  let uu____905 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____905 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.FalseOp ,uu____914) ->
                  let uu____917 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____917 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Not ,uu____926) ->
                  let uu____929 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____929 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Eq ,uu____938) ->
                  let uu____941 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____941 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.LT ,uu____950) ->
                  let uu____953 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____953 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.LTE ,uu____962) ->
                  let uu____965 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____965 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.GT ,uu____974) ->
                  let uu____977 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____977 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.GTE ,uu____986) ->
                  let uu____989 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____989 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Var uu____998,uu____999) ->
                  let uu____1002 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____1002 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Add ,uu____1011) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Sub ,uu____1017) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Div ,uu____1023) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Mul ,uu____1029) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Minus ,uu____1035) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Mod ,uu____1041) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.ITE ,uu____1047) ->
                  failwith "Impossible: arity mismatch"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Imp ,uu____1053) ->
                  failwith "Impossible: arity mismatch"
              | FStar_SMTEncoding_Term.Quant
                  (FStar_SMTEncoding_Term.Forall ,pats,iopt,sorts,body) ->
                  let uu____1071 =
                    aux default_msg ropt post_name_opt labels body in
                  (match uu____1071 with
                   | (labels1,body1) ->
                       let uu____1082 =
                         FStar_SMTEncoding_Term.mk
                           (FStar_SMTEncoding_Term.Quant
                              (FStar_SMTEncoding_Term.Forall, pats, iopt,
                                sorts, body1)) q1.FStar_SMTEncoding_Term.rng in
                       (labels1, uu____1082))
              | FStar_SMTEncoding_Term.Let (es,body) ->
                  let uu____1092 =
                    aux default_msg ropt post_name_opt labels body in
                  (match uu____1092 with
                   | (labels1,body1) ->
                       let uu____1103 =
                         FStar_SMTEncoding_Term.mkLet (es, body1)
                           q1.FStar_SMTEncoding_Term.rng in
                       (labels1, uu____1103)) in
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
        let print_banner uu____1137 =
          let uu____1138 =
            let uu____1139 = FStar_TypeChecker_Env.get_range env in
            FStar_Range.string_of_range uu____1139 in
          let uu____1140 = FStar_Util.string_of_int (Prims.parse_int "5") in
          let uu____1141 =
            FStar_Util.string_of_int (FStar_List.length all_labels) in
          FStar_Util.print3_error
            "Detailed error report follows for %s\nTaking %s seconds per proof obligation (%s proofs in total)\n"
            uu____1138 uu____1140 uu____1141 in
        let print_result uu____1153 =
          match uu____1153 with
          | ((uu____1159,msg,r),success) ->
              if success
              then
                let uu____1166 = FStar_Range.string_of_range r in
                FStar_Util.print1_error
                  "OK: proof obligation at %s was proven\n" uu____1166
              else FStar_Errors.err r msg in
        let elim labs =
          FStar_All.pipe_right labs
            (FStar_List.map
               (fun uu____1202  ->
                  match uu____1202 with
                  | (l,uu____1209,uu____1210) ->
                      let a =
                        let uu____1216 =
                          let uu____1217 =
                            let uu____1220 = FStar_SMTEncoding_Util.mkFreeV l in
                            (uu____1220, FStar_SMTEncoding_Util.mkTrue) in
                          FStar_SMTEncoding_Util.mkEq uu____1217 in
                        {
                          FStar_SMTEncoding_Term.assumption_term = uu____1216;
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
                let uu____1253 =
                  FStar_List.map (fun x  -> (x, true)) eliminated in
                let uu____1261 = FStar_List.map (fun x  -> (x, false)) errors in
                FStar_List.append uu____1253 uu____1261 in
              sort_labels results
          | hd1::tl1 ->
              ((let uu____1275 =
                  FStar_Util.string_of_int (FStar_List.length active) in
                FStar_Util.print1 "%s, " uu____1275);
               FStar_SMTEncoding_Z3.refresh ();
               (let uu____1280 =
                  let uu____1288 =
                    FStar_All.pipe_left elim
                      (FStar_List.append eliminated
                         (FStar_List.append errors tl1)) in
                  askZ3 uu____1288 in
                match uu____1280 with
                | (result,uu____1303,uu____1304) ->
                    let uu____1313 = FStar_Util.is_left result in
                    if uu____1313
                    then linear_check (hd1 :: eliminated) errors tl1
                    else linear_check eliminated (hd1 :: errors) tl1)) in
        print_banner ();
        FStar_Options.set_option "z3rlimit"
          (FStar_Options.Int (Prims.parse_int "5"));
        (let res = linear_check [] [] all_labels in
         FStar_Util.print_string "\n";
         FStar_All.pipe_right res (FStar_List.iter print_result);
         [])