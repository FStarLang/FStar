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
type ranges = (Prims.string Prims.option* FStar_Range.range) Prims.list
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
  (Prims.unit -> Prims.string) Prims.option ->
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
          | (_,FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var "Valid",tm1::[]))
            |(_,FStar_SMTEncoding_Term.App
              (FStar_SMTEncoding_Term.Var "ApplyTT",tm1::_)) ->
              is_a_post_condition post_name_opt tm1
          | uu____208 -> false in
        let conjuncts t =
          match t.FStar_SMTEncoding_Term.tm with
          | FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And ,cs) -> cs
          | uu____221 -> [t] in
        let is_guard_free tm =
          match tm.FStar_SMTEncoding_Term.tm with
          | FStar_SMTEncoding_Term.Quant
              (FStar_SMTEncoding_Term.Forall
               ,({
                   FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App
                     (FStar_SMTEncoding_Term.Var "Prims.guard_free",p::[]);
                   FStar_SMTEncoding_Term.freevars = uu____227;
                   FStar_SMTEncoding_Term.rng = uu____228;_}::[])::[],iopt,uu____230,
               {
                 FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App
                   (FStar_SMTEncoding_Term.Iff ,l::r1::[]);
                 FStar_SMTEncoding_Term.freevars = uu____233;
                 FStar_SMTEncoding_Term.rng = uu____234;_})
              -> true
          | uu____253 -> false in
        let is_a_named_continuation lhs =
          FStar_All.pipe_right (conjuncts lhs)
            (FStar_Util.for_some is_guard_free) in
        let uu____259 =
          match use_env_msg with
          | None  -> (false, "")
          | Some f -> let uu____271 = f () in (true, uu____271) in
        match uu____259 with
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
                    let uu___106_297 = r1 in
                    {
                      FStar_Range.def_range = (rng.FStar_Range.def_range);
                      FStar_Range.use_range =
                        (uu___106_297.FStar_Range.use_range)
                    } in
              fresh_label msg1 rng1 t in
            let rec aux default_msg ropt post_name_opt labels q1 =
              match q1.FStar_SMTEncoding_Term.tm with
              | FStar_SMTEncoding_Term.BoundV _
                |FStar_SMTEncoding_Term.Integer _ -> (labels, q1)
              | FStar_SMTEncoding_Term.LblPos uu____329 ->
                  failwith "Impossible"
              | FStar_SMTEncoding_Term.Labeled
                  (arg,"could not prove post-condition",uu____336) ->
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
                                                     = uu____360;
                                                   FStar_SMTEncoding_Term.rng
                                                     = rng;_})
                         ->
                         let post_name =
                           let uu____376 =
                             let uu____377 = FStar_Syntax_Syntax.next_id () in
                             FStar_All.pipe_left FStar_Util.string_of_int
                               uu____377 in
                           Prims.strcat "^^post_condition_" uu____376 in
                         let names =
                           let uu____382 =
                             FStar_List.mapi
                               (fun i  ->
                                  fun s  ->
                                    let uu____390 =
                                      let uu____391 =
                                        FStar_Util.string_of_int i in
                                      Prims.strcat "^^" uu____391 in
                                    (uu____390, s)) sorts in
                           (post_name, post) :: uu____382 in
                         let instantiation =
                           FStar_List.map FStar_SMTEncoding_Util.mkFreeV
                             names in
                         let uu____398 =
                           let uu____401 =
                             FStar_SMTEncoding_Term.inst instantiation lhs in
                           let uu____402 =
                             FStar_SMTEncoding_Term.inst instantiation rhs in
                           (uu____401, uu____402) in
                         (match uu____398 with
                          | (lhs1,rhs1) ->
                              let uu____408 =
                                match lhs1.FStar_SMTEncoding_Term.tm with
                                | FStar_SMTEncoding_Term.App
                                    (FStar_SMTEncoding_Term.And ,clauses_lhs)
                                    ->
                                    let uu____418 =
                                      FStar_Util.prefix clauses_lhs in
                                    (match uu____418 with
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
                                                   = uu____437;
                                                 FStar_SMTEncoding_Term.rng =
                                                   rng_ens;_})
                                              when
                                              is_a_post_condition
                                                (Some post_name) post1
                                              ->
                                              let uu____452 =
                                                aux
                                                  "could not prove post-condition"
                                                  None (Some post_name)
                                                  labels ensures_conjuncts in
                                              (match uu____452 with
                                               | (labels1,ensures_conjuncts1)
                                                   ->
                                                   let pats_ens1 =
                                                     match pats_ens with
                                                     | []|[]::[] -> [[post1]]
                                                     | uu____473 -> pats_ens in
                                                   let ens1 =
                                                     let uu____477 =
                                                       let uu____478 =
                                                         let uu____488 =
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
                                                           uu____488) in
                                                       FStar_SMTEncoding_Term.Quant
                                                         uu____478 in
                                                     FStar_SMTEncoding_Term.mk
                                                       uu____477
                                                       ens.FStar_SMTEncoding_Term.rng in
                                                   let lhs2 =
                                                     FStar_SMTEncoding_Term.mk
                                                       (FStar_SMTEncoding_Term.App
                                                          (FStar_SMTEncoding_Term.And,
                                                            (FStar_List.append
                                                               req [ens1])))
                                                       lhs1.FStar_SMTEncoding_Term.rng in
                                                   let uu____496 =
                                                     FStar_SMTEncoding_Term.abstr
                                                       names lhs2 in
                                                   (labels1, uu____496))
                                          | uu____498 ->
                                              let uu____499 =
                                                let uu____500 =
                                                  let uu____501 =
                                                    let uu____502 =
                                                      let uu____503 =
                                                        FStar_SMTEncoding_Term.print_smt_term
                                                          ens in
                                                      Prims.strcat "  ... "
                                                        uu____503 in
                                                    Prims.strcat post_name
                                                      uu____502 in
                                                  Prims.strcat
                                                    "Ensures clause doesn't match post name:  "
                                                    uu____501 in
                                                Not_a_wp_implication
                                                  uu____500 in
                                              Prims.raise uu____499))
                                | uu____507 ->
                                    let uu____508 =
                                      let uu____509 =
                                        let uu____510 =
                                          FStar_SMTEncoding_Term.print_smt_term
                                            lhs1 in
                                        Prims.strcat "LHS not a conjunct: "
                                          uu____510 in
                                      Not_a_wp_implication uu____509 in
                                    Prims.raise uu____508 in
                              (match uu____408 with
                               | (labels1,lhs2) ->
                                   let uu____521 =
                                     let uu____525 =
                                       aux default_msg None (Some post_name)
                                         labels1 rhs1 in
                                     match uu____525 with
                                     | (labels2,rhs2) ->
                                         let uu____536 =
                                           FStar_SMTEncoding_Term.abstr names
                                             rhs2 in
                                         (labels2, uu____536) in
                                   (match uu____521 with
                                    | (labels2,rhs2) ->
                                        let body =
                                          FStar_SMTEncoding_Term.mkImp
                                            (lhs2, rhs2) rng in
                                        let uu____546 =
                                          FStar_SMTEncoding_Term.mk
                                            (FStar_SMTEncoding_Term.Quant
                                               (FStar_SMTEncoding_Term.Forall,
                                                 pats, iopt, (post :: sorts),
                                                 body))
                                            q1.FStar_SMTEncoding_Term.rng in
                                        (labels2, uu____546))))
                     | uu____552 ->
                         let uu____553 =
                           let uu____554 =
                             FStar_SMTEncoding_Term.print_smt_term arg in
                           Prims.strcat "arg not a quant: " uu____554 in
                         fallback uu____553
                   with | Not_a_wp_implication msg -> fallback msg)
              | FStar_SMTEncoding_Term.Labeled (arg,reason,r1) ->
                  aux reason (Some r1) post_name_opt labels arg
              | FStar_SMTEncoding_Term.Quant
                  (FStar_SMTEncoding_Term.Forall ,[],None
                   ,post::[],{
                               FStar_SMTEncoding_Term.tm =
                                 FStar_SMTEncoding_Term.App
                                 (FStar_SMTEncoding_Term.Imp ,lhs::rhs::[]);
                               FStar_SMTEncoding_Term.freevars = uu____566;
                               FStar_SMTEncoding_Term.rng = rng;_})
                  when is_a_named_continuation lhs ->
                  let post_name =
                    let uu____579 =
                      let uu____580 = FStar_Syntax_Syntax.next_id () in
                      FStar_All.pipe_left FStar_Util.string_of_int uu____580 in
                    Prims.strcat "^^post_condition_" uu____579 in
                  let names = (post_name, post) in
                  let instantiation =
                    let uu____586 = FStar_SMTEncoding_Util.mkFreeV names in
                    [uu____586] in
                  let uu____587 =
                    let uu____590 =
                      FStar_SMTEncoding_Term.inst instantiation lhs in
                    let uu____591 =
                      FStar_SMTEncoding_Term.inst instantiation rhs in
                    (uu____590, uu____591) in
                  (match uu____587 with
                   | (lhs1,rhs1) ->
                       let uu____597 =
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
                                           uu____610;
                                         FStar_SMTEncoding_Term.rng =
                                           uu____611;_}::[])::[],iopt,sorts,
                                     {
                                       FStar_SMTEncoding_Term.tm =
                                         FStar_SMTEncoding_Term.App
                                         (FStar_SMTEncoding_Term.Iff
                                          ,l::r1::[]);
                                       FStar_SMTEncoding_Term.freevars =
                                         uu____616;
                                       FStar_SMTEncoding_Term.rng = uu____617;_})
                                    ->
                                    let uu____636 =
                                      aux default_msg None post_name_opt
                                        labels1 r1 in
                                    (match uu____636 with
                                     | (labels2,r2) ->
                                         let uu____647 =
                                           let uu____648 =
                                             let uu____649 =
                                               let uu____659 =
                                                 FStar_SMTEncoding_Util.norng
                                                   FStar_SMTEncoding_Term.mk
                                                   (FStar_SMTEncoding_Term.App
                                                      (FStar_SMTEncoding_Term.Iff,
                                                        [l; r2])) in
                                               (FStar_SMTEncoding_Term.Forall,
                                                 [[p]],
                                                 (Some (Prims.parse_int "0")),
                                                 sorts, uu____659) in
                                             FStar_SMTEncoding_Term.Quant
                                               uu____649 in
                                           FStar_SMTEncoding_Term.mk
                                             uu____648
                                             q1.FStar_SMTEncoding_Term.rng in
                                         (labels2, uu____647))
                                | uu____668 -> (labels1, tm)) labels
                           (conjuncts lhs1) in
                       (match uu____597 with
                        | (labels1,lhs_conjs) ->
                            let uu____679 =
                              aux default_msg None (Some post_name) labels1
                                rhs1 in
                            (match uu____679 with
                             | (labels2,rhs2) ->
                                 let body =
                                   let uu____691 =
                                     let uu____692 =
                                       let uu____695 =
                                         FStar_SMTEncoding_Term.mk_and_l
                                           lhs_conjs
                                           lhs1.FStar_SMTEncoding_Term.rng in
                                       (uu____695, rhs2) in
                                     FStar_SMTEncoding_Term.mkImp uu____692
                                       rng in
                                   FStar_All.pipe_right uu____691
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
                  let uu____710 =
                    aux default_msg ropt post_name_opt labels rhs in
                  (match uu____710 with
                   | (labels1,rhs1) ->
                       let uu____721 =
                         FStar_SMTEncoding_Util.mkImp (lhs, rhs1) in
                       (labels1, uu____721))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.And ,conjuncts1) ->
                  let uu____726 =
                    FStar_Util.fold_map (aux default_msg ropt post_name_opt)
                      labels conjuncts1 in
                  (match uu____726 with
                   | (labels1,conjuncts2) ->
                       let uu____741 =
                         FStar_SMTEncoding_Term.mk_and_l conjuncts2
                           q1.FStar_SMTEncoding_Term.rng in
                       (labels1, uu____741))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.ITE ,hd1::q11::q2::[]) ->
                  let uu____747 =
                    aux default_msg ropt post_name_opt labels q11 in
                  (match uu____747 with
                   | (labels1,q12) ->
                       let uu____758 =
                         aux default_msg ropt post_name_opt labels1 q2 in
                       (match uu____758 with
                        | (labels2,q21) ->
                            let uu____769 =
                              FStar_SMTEncoding_Term.mkITE (hd1, q12, q21)
                                q1.FStar_SMTEncoding_Term.rng in
                            (labels2, uu____769)))
              | FStar_SMTEncoding_Term.Quant
                (FStar_SMTEncoding_Term.Exists ,_,_,_,_)
                |FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Iff ,_)
                 |FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Or ,_)
                  ->
                  let uu____783 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____783 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Var uu____792,uu____793) when
                  is_a_post_condition post_name_opt q1 -> (labels, q1)
              | FStar_SMTEncoding_Term.FreeV _
                |FStar_SMTEncoding_Term.App
                 (FStar_SMTEncoding_Term.TrueOp ,_)
                 |FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.FalseOp ,_)
                  |FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Not ,_)
                   |FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Eq ,_)
                    |FStar_SMTEncoding_Term.App
                     (FStar_SMTEncoding_Term.LT ,_)
                     |FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.LTE ,_)
                      |FStar_SMTEncoding_Term.App
                       (FStar_SMTEncoding_Term.GT ,_)
                       |FStar_SMTEncoding_Term.App
                        (FStar_SMTEncoding_Term.GTE ,_)
                        |FStar_SMTEncoding_Term.App
                        (FStar_SMTEncoding_Term.Var _,_)
                  ->
                  let uu____817 =
                    fresh_label1 default_msg ropt
                      q1.FStar_SMTEncoding_Term.rng q1 in
                  (match uu____817 with | (lab,q2) -> ((lab :: labels), q2))
              | FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Add ,_)
                |FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Sub ,_)
                 |FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Div ,_)
                  |FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Mul ,_)
                   |FStar_SMTEncoding_Term.App
                    (FStar_SMTEncoding_Term.Minus ,_)
                    |FStar_SMTEncoding_Term.App
                    (FStar_SMTEncoding_Term.Mod ,_)
                  -> failwith "Impossible: non-propositional term"
              | FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE ,_)
                |FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp ,_)
                  -> failwith "Impossible: arity mismatch"
              | FStar_SMTEncoding_Term.Quant
                  (FStar_SMTEncoding_Term.Forall ,pats,iopt,sorts,body) ->
                  let uu____860 =
                    aux default_msg ropt post_name_opt labels body in
                  (match uu____860 with
                   | (labels1,body1) ->
                       let uu____871 =
                         FStar_SMTEncoding_Term.mk
                           (FStar_SMTEncoding_Term.Quant
                              (FStar_SMTEncoding_Term.Forall, pats, iopt,
                                sorts, body1)) q1.FStar_SMTEncoding_Term.rng in
                       (labels1, uu____871))
              | FStar_SMTEncoding_Term.Let (es,body) ->
                  let uu____881 =
                    aux default_msg ropt post_name_opt labels body in
                  (match uu____881 with
                   | (labels1,body1) ->
                       let uu____892 =
                         FStar_SMTEncoding_Term.mkLet (es, body1)
                           q1.FStar_SMTEncoding_Term.rng in
                       (labels1, uu____892)) in
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
        let print_banner uu____926 =
          let uu____927 =
            let uu____928 = FStar_TypeChecker_Env.get_range env in
            FStar_Range.string_of_range uu____928 in
          let uu____929 = FStar_Util.string_of_int (Prims.parse_int "5") in
          let uu____930 =
            FStar_Util.string_of_int (FStar_List.length all_labels) in
          FStar_Util.print3_error
            "Detailed error report follows for %s\nTaking %s seconds per proof obligation (%s proofs in total)\n"
            uu____927 uu____929 uu____930 in
        let print_result uu____942 =
          match uu____942 with
          | ((uu____948,msg,r),success) ->
              if success
              then
                let uu____955 = FStar_Range.string_of_range r in
                FStar_Util.print1_error
                  "OK: proof obligation at %s was proven\n" uu____955
              else FStar_Errors.err r msg in
        let elim labs =
          FStar_All.pipe_right labs
            (FStar_List.map
               (fun uu____986  ->
                  match uu____986 with
                  | (l,uu____993,uu____994) ->
                      let a =
                        let uu____1000 =
                          let uu____1001 =
                            let uu____1004 = FStar_SMTEncoding_Util.mkFreeV l in
                            (uu____1004, FStar_SMTEncoding_Util.mkTrue) in
                          FStar_SMTEncoding_Util.mkEq uu____1001 in
                        {
                          FStar_SMTEncoding_Term.assumption_term = uu____1000;
                          FStar_SMTEncoding_Term.assumption_caption =
                            (Some "Disabling label");
                          FStar_SMTEncoding_Term.assumption_name =
                            (Prims.strcat "disable_label_" (Prims.fst l));
                          FStar_SMTEncoding_Term.assumption_fact_ids = []
                        } in
                      FStar_SMTEncoding_Term.Assume a)) in
        let rec linear_check eliminated errors active =
          match active with
          | [] ->
              let results =
                let uu____1037 =
                  FStar_List.map (fun x  -> (x, true)) eliminated in
                let uu____1044 = FStar_List.map (fun x  -> (x, false)) errors in
                FStar_List.append uu____1037 uu____1044 in
              sort_labels results
          | hd1::tl1 ->
              ((let uu____1057 =
                  FStar_Util.string_of_int (FStar_List.length active) in
                FStar_Util.print1 "%s, " uu____1057);
               FStar_SMTEncoding_Z3.refresh ();
               (let uu____1062 =
                  let uu____1070 =
                    FStar_All.pipe_left elim
                      (FStar_List.append eliminated
                         (FStar_List.append errors tl1)) in
                  askZ3 uu____1070 in
                match uu____1062 with
                | (result,uu____1085,uu____1086) ->
                    let uu____1095 = FStar_Util.is_left result in
                    if uu____1095
                    then linear_check (hd1 :: eliminated) errors tl1
                    else linear_check eliminated (hd1 :: errors) tl1)) in
        print_banner ();
        FStar_Options.set_option "z3rlimit"
          (FStar_Options.Int (Prims.parse_int "5"));
        (let res = linear_check [] [] all_labels in
         FStar_Util.print_string "\n";
         FStar_All.pipe_right res (FStar_List.iter print_result);
         [])