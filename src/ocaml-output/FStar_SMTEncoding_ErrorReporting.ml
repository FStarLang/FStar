open Prims
exception Not_a_wp_implication of Prims.string
let uu___is_Not_a_wp_implication: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Not_a_wp_implication uu____6 -> true
    | uu____7 -> false
let __proj__Not_a_wp_implication__item__uu___: Prims.exn -> Prims.string =
  fun projectee  ->
    match projectee with | Not_a_wp_implication uu____14 -> uu____14
type label = FStar_SMTEncoding_Term.error_label
type labels = FStar_SMTEncoding_Term.error_labels
let sort_labels:
  (FStar_SMTEncoding_Term.error_label* Prims.bool) Prims.list ->
    ((FStar_SMTEncoding_Term.fv* Prims.string* FStar_Range.range)*
      Prims.bool) Prims.list
  =
  fun l  ->
    FStar_List.sortWith
      (fun uu____35  ->
         fun uu____36  ->
           match (uu____35, uu____36) with
           | (((uu____57,uu____58,r1),uu____60),((uu____61,uu____62,r2),uu____64))
               -> FStar_Range.compare r1 r2) l
let remove_dups:
  labels ->
    (FStar_SMTEncoding_Term.fv* Prims.string* FStar_Range.range) Prims.list
  =
  fun l  ->
    FStar_Util.remove_dups
      (fun uu____91  ->
         fun uu____92  ->
           match (uu____91, uu____92) with
           | ((uu____105,m1,r1),(uu____108,m2,r2)) -> (r1 = r2) && (m1 = m2))
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
          (let uu____142 =
             let uu____143 = FStar_ST.read ctr in
             FStar_Util.string_of_int uu____143 in
           FStar_Util.format1 "label_%s" uu____142) in
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
          | (None ,uu____194) -> false
          | (Some nm,FStar_SMTEncoding_Term.FreeV (nm',uu____198)) ->
              nm = nm'
          | (uu____200,FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var "Valid",tm1::[])) ->
              is_a_post_condition post_name_opt tm1
          | (uu____205,FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var "ApplyTT",tm1::uu____207)) ->
              is_a_post_condition post_name_opt tm1
          | uu____212 -> false in
        let conjuncts t =
          match t.FStar_SMTEncoding_Term.tm with
          | FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And ,cs) -> cs
          | uu____225 -> [t] in
        let is_guard_free tm =
          match tm.FStar_SMTEncoding_Term.tm with
          | FStar_SMTEncoding_Term.Quant
              (FStar_SMTEncoding_Term.Forall
               ,({
                   FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App
                     (FStar_SMTEncoding_Term.Var "Prims.guard_free",p::[]);
                   FStar_SMTEncoding_Term.freevars = uu____231;
                   FStar_SMTEncoding_Term.rng = uu____232;_}::[])::[],iopt,uu____234,
               {
                 FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App
                   (FStar_SMTEncoding_Term.Iff ,l::r1::[]);
                 FStar_SMTEncoding_Term.freevars = uu____237;
                 FStar_SMTEncoding_Term.rng = uu____238;_})
              -> true
          | uu____257 -> false in
        let is_a_named_continuation lhs =
          FStar_All.pipe_right (conjuncts lhs)
            (FStar_Util.for_some is_guard_free) in
        let uu____263 =
          match use_env_msg with
          | None  -> (false, "")
          | Some f -> let uu____275 = f () in (true, uu____275) in
        match uu____263 with
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
                    let uu___104_301 = r1 in
                    {
                      FStar_Range.def_range = (rng.FStar_Range.def_range);
                      FStar_Range.use_range =
                        (uu___104_301.FStar_Range.use_range)
                    } in
              fresh_label msg1 rng1 t in
            let rec aux default_msg ropt post_name_opt labels q1 =
              match q1.FStar_SMTEncoding_Term.tm with
              | FStar_SMTEncoding_Term.BoundV uu____330 -> (labels, q1)
              | FStar_SMTEncoding_Term.Integer uu____332 -> (labels, q1)
              | FStar_SMTEncoding_Term.LblPos uu____334 ->
                  failwith "Impossible"
              | FStar_SMTEncoding_Term.Labeled
                  (arg,"could not prove post-condition",uu____341) ->
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
                                                     = uu____365;
                                                   FStar_SMTEncoding_Term.rng
                                                     = rng;_})
                         ->
                         let post_name =
                           let uu____381 =
                             let uu____382 = FStar_Syntax_Syntax.next_id () in
                             FStar_All.pipe_left FStar_Util.string_of_int
                               uu____382 in
                           Prims.strcat "^^post_condition_" uu____381 in
                         let names =
                           let uu____387 =
                             FStar_List.mapi
                               (fun i  ->
                                  fun s  ->
                                    let uu____395 =
                                      let uu____396 =
                                        FStar_Util.string_of_int i in
                                      Prims.strcat "^^" uu____396 in
                                    (uu____395, s)) sorts in
                           (post_name, post) :: uu____387 in
                         let instantiation =
                           FStar_List.map FStar_SMTEncoding_Util.mkFreeV
                             names in
                         let uu____403 =
                           let uu____406 =
                             FStar_SMTEncoding_Term.inst instantiation lhs in
                           let uu____407 =
                             FStar_SMTEncoding_Term.inst instantiation rhs in
                           (uu____406, uu____407) in
                         (match uu____403 with
                          | (lhs1,rhs1) ->
                              let uu____413 =
                                match lhs1.FStar_SMTEncoding_Term.tm with
                                | FStar_SMTEncoding_Term.App
                                    (FStar_SMTEncoding_Term.And ,clauses_lhs)
                                    ->
                                    let uu____423 =
                                      FStar_Util.prefix clauses_lhs in
                                    (match uu____423 with
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
                                                   = uu____442;
                                                 FStar_SMTEncoding_Term.rng =
                                                   rng_ens;_})
                                              when
                                              is_a_post_condition
                                                (Some post_name) post1
                                              ->
                                              let uu____457 =
                                                aux
                                                  "could not prove post-condition"
                                                  None (Some post_name)
                                                  labels ensures_conjuncts in
                                              (match uu____457 with
                                               | (labels1,ensures_conjuncts1)
                                                   ->
                                                   let pats_ens1 =
                                                     match pats_ens with
                                                     | [] -> [[post1]]
                                                     | []::[] -> [[post1]]
                                                     | uu____480 -> pats_ens in
                                                   let ens1 =
                                                     let uu____484 =
                                                       let uu____485 =
                                                         let uu____495 =
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
                                                           uu____495) in
                                                       FStar_SMTEncoding_Term.Quant
                                                         uu____485 in
                                                     FStar_SMTEncoding_Term.mk
                                                       uu____484
                                                       ens.FStar_SMTEncoding_Term.rng in
                                                   let lhs2 =
                                                     FStar_SMTEncoding_Term.mk
                                                       (FStar_SMTEncoding_Term.App
                                                          (FStar_SMTEncoding_Term.And,
                                                            (FStar_List.append
                                                               req [ens1])))
                                                       lhs1.FStar_SMTEncoding_Term.rng in
                                                   let uu____503 =
                                                     FStar_SMTEncoding_Term.abstr
                                                       names lhs2 in
                                                   (labels1, uu____503))
                                          | uu____505 ->
                                              let uu____506 =
                                                let uu____507 =
                                                  let uu____508 =
                                                    let uu____509 =
                                                      let uu____510 =
                                                        FStar_SMTEncoding_Term.print_smt_term
                                                          ens in
                                                      Prims.strcat "  ... "
                                                        uu____510 in
                                                    Prims.strcat post_name
                                                      uu____509 in
                                                  Prims.strcat
                                                    "Ensures clause doesn't match post name:  "
                                                    uu____508 in
                                                Not_a_wp_implication
                                                  uu____507 in
                                              raise uu____506))
                                | uu____514 ->
                                    let uu____515 =
                                      let uu____516 =
                                        let uu____517 =
                                          FStar_SMTEncoding_Term.print_smt_term
                                            lhs1 in
                                        Prims.strcat "LHS not a conjunct: "
                                          uu____517 in
                                      Not_a_wp_implication uu____516 in
                                    raise uu____515 in
                              (match uu____413 with
                               | (labels1,lhs2) ->
                                   let uu____528 =
                                     let uu____532 =
                                       aux default_msg None (Some post_name)
                                         labels1 rhs1 in
                                     match uu____532 with
                                     | (labels2,rhs2) ->
                                         let uu____543 =
                                           FStar_SMTEncoding_Term.abstr names
                                             rhs2 in
                                         (labels2, uu____543) in
                                   (match uu____528 with
                                    | (labels2,rhs2) ->
                                        let body =
                                          FStar_SMTEncoding_Term.mkImp
                                            (lhs2, rhs2) rng in
                                        let uu____553 =
                                          FStar_SMTEncoding_Term.mk
                                            (FStar_SMTEncoding_Term.Quant
                                               (FStar_SMTEncoding_Term.Forall,
                                                 pats, iopt, (post :: sorts),
                                                 body))
                                            q1.FStar_SMTEncoding_Term.rng in
                                        (labels2, uu____553))))
                     | uu____559 ->
                         let uu____560 =
                           let uu____561 =
                             FStar_SMTEncoding_Term.print_smt_term arg in
                           Prims.strcat "arg not a quant: " uu____561 in
                         fallback uu____560
                   with | Not_a_wp_implication msg -> fallback msg)
              | FStar_SMTEncoding_Term.Labeled (arg,reason,r1) ->
                  aux reason (Some r1) post_name_opt labels arg
              | FStar_SMTEncoding_Term.Quant
                  (FStar_SMTEncoding_Term.Forall ,[],None
                   ,post::[],{
                               FStar_SMTEncoding_Term.tm =
                                 FStar_SMTEncoding_Term.App
                                 (FStar_SMTEncoding_Term.Imp ,lhs::rhs::[]);
                               FStar_SMTEncoding_Term.freevars = uu____573;
                               FStar_SMTEncoding_Term.rng = rng;_})
                  when is_a_named_continuation lhs ->
                  let post_name =
                    let uu____586 =
                      let uu____587 = FStar_Syntax_Syntax.next_id () in
                      FStar_All.pipe_left FStar_Util.string_of_int uu____587 in
                    Prims.strcat "^^post_condition_" uu____586 in
                  let names = (post_name, post) in
                  let instantiation =
                    let uu____593 = FStar_SMTEncoding_Util.mkFreeV names in
                    [uu____593] in
                  let uu____594 =
                    let uu____597 =
                      FStar_SMTEncoding_Term.inst instantiation lhs in
                    let uu____598 =
                      FStar_SMTEncoding_Term.inst instantiation rhs in
                    (uu____597, uu____598) in
                  (match uu____594 with
                   | (lhs1,rhs1) ->
                       let uu____604 =
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
                                           uu____617;
                                         FStar_SMTEncoding_Term.rng =
                                           uu____618;_}::[])::[],iopt,sorts,
                                     {
                                       FStar_SMTEncoding_Term.tm =
                                         FStar_SMTEncoding_Term.App
                                         (FStar_SMTEncoding_Term.Iff
                                          ,l::r1::[]);
                                       FStar_SMTEncoding_Term.freevars =
                                         uu____623;
                                       FStar_SMTEncoding_Term.rng = uu____624;_})
                                    ->
                                    let uu____643 =
                                      aux default_msg None post_name_opt
                                        labels1 r1 in
                                    (match uu____643 with
                                     | (labels2,r2) ->
                                         let uu____654 =
                                           let uu____655 =
                                             let uu____656 =
                                               let uu____666 =
                                                 FStar_SMTEncoding_Util.norng
                                                   FStar_SMTEncoding_Term.mk
                                                   (FStar_SMTEncoding_Term.App
                                                      (FStar_SMTEncoding_Term.Iff,
                                                        [l; r2])) in
                                               (FStar_SMTEncoding_Term.Forall,
                                                 [[p]],
                                                 (Some (Prims.parse_int "0")),
                                                 sorts, uu____666) in
                                             FStar_SMTEncoding_Term.Quant
                                               uu____656 in
                                           FStar_SMTEncoding_Term.mk
                                             uu____655
                                             q1.FStar_SMTEncoding_Term.rng in
                                         (labels2, uu____654))
                                | uu____675 -> (labels1, tm)) labels
                           (conjuncts lhs1) in
                       (match uu____604 with
                        | (labels1,lhs_conjs) ->
                            let uu____686 =
                              aux default_msg None (Some post_name) labels1
                                rhs1 in
                            (match uu____686 with
                             | (labels2,rhs2) ->
                                 let body =
                                   let uu____698 =
                                     let uu____699 =
                                       let uu____702 =
                                         FStar_SMTEncoding_Term.mk_and_l
                                           lhs_conjs
                                           lhs1.FStar_SMTEncoding_Term.rng in
                                       (uu____702, rhs2) in
                                     FStar_SMTEncoding_Term.mkImp uu____699
                                       rng in
                                   FStar_All.pipe_right uu____698
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
                  let uu____717 =
                    aux default_msg ropt post_name_opt labels rhs in
                  (match uu____717 with
                   | (labels1,rhs1) ->
                       let uu____728 =
                         FStar_SMTEncoding_Util.mkImp (lhs, rhs1) in
                       (labels1, uu____728))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.And ,conjuncts1) ->
                  let uu____733 =
                    FStar_Util.fold_map (aux default_msg ropt post_name_opt)
                      labels conjuncts1 in
                  (match uu____733 with
                   | (labels1,conjuncts2) ->
                       let uu____748 =
                         FStar_SMTEncoding_Term.mk_and_l conjuncts2
                           q1.FStar_SMTEncoding_Term.rng in
                       (labels1, uu____748))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.ITE ,hd1::q11::q2::[]) ->
                  let uu____754 =
                    aux default_msg ropt post_name_opt labels q11 in
                  (match uu____754 with
                   | (labels1,q12) ->
                       let uu____765 =
                         aux default_msg ropt post_name_opt labels1 q2 in
                       (match uu____765 with
                        | (labels2,q21) ->
                            let uu____776 =
                              FStar_SMTEncoding_Term.mkITE (hd1, q12, q21)
                                q1.FStar_SMTEncoding_Term.rng in
                            (labels2, uu____776)))
              | FStar_SMTEncoding_Term.Quant
                  (FStar_SMTEncoding_Term.Exists
                   ,uu____778,uu____779,uu____780,uu____781)
                  ->
                  let uu____790 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____790 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Iff ,uu____799) ->
                  let uu____802 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____802 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Or ,uu____811) ->
                  let uu____814 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____814 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Var uu____823,uu____824) when
                  is_a_post_condition post_name_opt q1 -> (labels, q1)
              | FStar_SMTEncoding_Term.FreeV uu____828 ->
                  let uu____831 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____831 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.TrueOp ,uu____840) ->
                  let uu____843 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____843 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.FalseOp ,uu____852) ->
                  let uu____855 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____855 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Not ,uu____864) ->
                  let uu____867 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____867 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Eq ,uu____876) ->
                  let uu____879 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____879 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.LT ,uu____888) ->
                  let uu____891 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____891 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.LTE ,uu____900) ->
                  let uu____903 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____903 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.GT ,uu____912) ->
                  let uu____915 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____915 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.GTE ,uu____924) ->
                  let uu____927 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____927 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Var uu____936,uu____937) ->
                  let uu____940 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____940 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Add ,uu____949) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Sub ,uu____955) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Div ,uu____961) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Mul ,uu____967) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Minus ,uu____973) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Mod ,uu____979) ->
                  failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.ITE ,uu____985) ->
                  failwith "Impossible: arity mismatch"
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Imp ,uu____991) ->
                  failwith "Impossible: arity mismatch"
              | FStar_SMTEncoding_Term.Quant
                  (FStar_SMTEncoding_Term.Forall ,pats,iopt,sorts,body) ->
                  let uu____1009 =
                    aux default_msg ropt post_name_opt labels body in
                  (match uu____1009 with
                   | (labels1,body1) ->
                       let uu____1020 =
                         FStar_SMTEncoding_Term.mk
                           (FStar_SMTEncoding_Term.Quant
                              (FStar_SMTEncoding_Term.Forall, pats, iopt,
                                sorts, body1)) q1.FStar_SMTEncoding_Term.rng in
                       (labels1, uu____1020))
              | FStar_SMTEncoding_Term.Let (es,body) ->
                  let uu____1030 =
                    aux default_msg ropt post_name_opt labels body in
                  (match uu____1030 with
                   | (labels1,body1) ->
                       let uu____1041 =
                         FStar_SMTEncoding_Term.mkLet (es, body1)
                           q1.FStar_SMTEncoding_Term.rng in
                       (labels1, uu____1041)) in
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
        let print_banner uu____1075 =
          let uu____1076 =
            let uu____1077 = FStar_TypeChecker_Env.get_range env in
            FStar_Range.string_of_range uu____1077 in
          let uu____1078 = FStar_Util.string_of_int (Prims.parse_int "5") in
          let uu____1079 =
            FStar_Util.string_of_int (FStar_List.length all_labels) in
          FStar_Util.print3_error
            "Detailed error report follows for %s\nTaking %s seconds per proof obligation (%s proofs in total)\n"
            uu____1076 uu____1078 uu____1079 in
        let print_result uu____1094 =
          match uu____1094 with
          | ((uu____1100,msg,r),success) ->
              if success
              then
                let uu____1107 = FStar_Range.string_of_range r in
                FStar_Util.print1_error
                  "OK: proof obligation at %s was proven\n" uu____1107
              else FStar_Errors.err r msg in
        let elim labs =
          FStar_All.pipe_right labs
            (FStar_List.map
               (fun uu____1138  ->
                  match uu____1138 with
                  | (l,uu____1145,uu____1146) ->
                      let a =
                        let uu____1152 =
                          let uu____1153 =
                            let uu____1156 = FStar_SMTEncoding_Util.mkFreeV l in
                            (uu____1156, FStar_SMTEncoding_Util.mkTrue) in
                          FStar_SMTEncoding_Util.mkEq uu____1153 in
                        {
                          FStar_SMTEncoding_Term.assumption_term = uu____1152;
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
                let uu____1189 =
                  FStar_List.map (fun x  -> (x, true)) eliminated in
                let uu____1196 = FStar_List.map (fun x  -> (x, false)) errors in
                FStar_List.append uu____1189 uu____1196 in
              sort_labels results
          | hd1::tl1 ->
              ((let uu____1209 =
                  FStar_Util.string_of_int (FStar_List.length active) in
                FStar_Util.print1 "%s, " uu____1209);
               FStar_SMTEncoding_Z3.refresh ();
               (let uu____1217 =
                  let uu____1225 =
                    FStar_All.pipe_left elim
                      (FStar_List.append eliminated
                         (FStar_List.append errors tl1)) in
                  askZ3 uu____1225 in
                match uu____1217 with
                | (result,uu____1240,uu____1241) ->
                    let uu____1250 = FStar_Util.is_left result in
                    if uu____1250
                    then linear_check (hd1 :: eliminated) errors tl1
                    else linear_check eliminated (hd1 :: errors) tl1)) in
        print_banner ();
        FStar_Options.set_option "z3rlimit"
          (FStar_Options.Int (Prims.parse_int "5"));
        (let res = linear_check [] [] all_labels in
         FStar_Util.print_string "\n";
         FStar_All.pipe_right res (FStar_List.iter print_result);
         [])