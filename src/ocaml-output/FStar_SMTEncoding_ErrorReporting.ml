open Prims
exception Not_a_wp_implication of Prims.string 
let uu___is_Not_a_wp_implication : Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Not_a_wp_implication uu____6 -> true
    | uu____7 -> false
  
let __proj__Not_a_wp_implication__item__uu___ : Prims.exn -> Prims.string =
  fun projectee  ->
    match projectee with | Not_a_wp_implication uu____14 -> uu____14
  
type label = FStar_SMTEncoding_Term.error_label
type labels = FStar_SMTEncoding_Term.error_labels
let sort_labels :
  (FStar_SMTEncoding_Term.error_label * Prims.bool) Prims.list ->
    ((FStar_SMTEncoding_Term.fv * Prims.string * FStar_Range.range) *
      Prims.bool) Prims.list
  =
  fun l  ->
    FStar_List.sortWith
      (fun uu____35  ->
         fun uu____36  ->
           match (uu____35, uu____36) with
           | (((uu____57,uu____58,r1),uu____60),((uu____61,uu____62,r2),uu____64))
               -> FStar_Range.compare r1 r2) l
  
let remove_dups :
  labels ->
    (FStar_SMTEncoding_Term.fv * Prims.string * FStar_Range.range) Prims.list
  =
  fun l  ->
    FStar_Util.remove_dups
      (fun uu____91  ->
         fun uu____92  ->
           match (uu____91, uu____92) with
           | ((uu____105,m1,r1),(uu____108,m2,r2)) -> (r1 = r2) && (m1 = m2))
      l
  
type msg = (Prims.string * FStar_Range.range)
type ranges = (Prims.string Prims.option * FStar_Range.range) Prims.list
let fresh_label :
  Prims.string ->
    FStar_Range.range ->
      FStar_SMTEncoding_Term.term ->
        (((Prims.string * FStar_SMTEncoding_Term.sort) * Prims.string *
          FStar_Range.range) * FStar_SMTEncoding_Term.term)
  =
  let ctr = FStar_Util.mk_ref (Prims.parse_int "0")  in
  fun message  ->
    fun range  ->
      fun t  ->
        let l =
          FStar_Util.incr ctr;
          (let _0_449 = FStar_Util.string_of_int (FStar_ST.read ctr)  in
           FStar_Util.format1 "label_%s" _0_449)
           in
        let lvar = (l, FStar_SMTEncoding_Term.Bool_sort)  in
        let label = (lvar, message, range)  in
        let lterm = FStar_SMTEncoding_Util.mkFreeV lvar  in
        let lt = FStar_SMTEncoding_Term.mkOr (lterm, t) range  in (label, lt)
  
let label_goals :
  (Prims.unit -> Prims.string) Prims.option ->
    FStar_Range.range ->
      FStar_SMTEncoding_Term.term -> (labels * FStar_SMTEncoding_Term.term)
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
              (FStar_SMTEncoding_Term.Var "ApplyTT",tm::_)) ->
              is_a_post_condition post_name_opt tm
          | uu____206 -> false  in
        let conjuncts t =
          match t.FStar_SMTEncoding_Term.tm with
          | FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And ,cs) -> cs
          | uu____219 -> [t]  in
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
          | uu____251 -> false  in
        let is_a_named_continuation lhs =
          FStar_All.pipe_right (conjuncts lhs)
            (FStar_Util.for_some is_guard_free)
           in
        let uu____257 =
          match use_env_msg with
          | None  -> (false, "")
          | Some f -> let _0_450 = f ()  in (true, _0_450)  in
        match uu____257 with
        | (flag,msg_prefix) ->
            let fresh_label msg ropt rng t =
              let msg =
                match flag with
                | true  ->
                    Prims.strcat "Failed to verify implicit argument: " msg
                | uu____291 -> msg  in
              let rng =
                match ropt with
                | None  -> rng
                | Some r ->
                    let uu___99_294 = r  in
                    {
                      FStar_Range.def_range = (rng.FStar_Range.def_range);
                      FStar_Range.use_range =
                        (uu___99_294.FStar_Range.use_range)
                    }
                 in
              fresh_label msg rng t  in
            let rec aux default_msg ropt post_name_opt labels q =
              match q.FStar_SMTEncoding_Term.tm with
              | FStar_SMTEncoding_Term.BoundV _
                |FStar_SMTEncoding_Term.Integer _ -> (labels, q1)
              | FStar_SMTEncoding_Term.LblPos uu____329 ->
                  failwith "Impossible"
              | FStar_SMTEncoding_Term.Labeled
                  (arg,"could not prove post-condition",uu____336) ->
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
                                                     = uu____360;
                                                   FStar_SMTEncoding_Term.rng
                                                     = rng;_})
                         ->
                         let post_name =
                           let _0_452 =
                             let _0_451 = FStar_Syntax_Syntax.next_id ()  in
                             FStar_All.pipe_left FStar_Util.string_of_int
                               _0_451
                              in
                           Prims.strcat "^^post_condition_" _0_452  in
                         let names =
                           let uu____382 =
                             FStar_List.mapi
                               (fun i  ->
                                  fun s  ->
                                    let _0_454 =
                                      let _0_453 = FStar_Util.string_of_int i
                                         in
                                      Prims.strcat "^^" _0_453  in
                                    (_0_454, s)) sorts
                              in
                           (post_name, post) :: _0_455  in
                         let instantiation =
                           FStar_List.map FStar_SMTEncoding_Util.mkFreeV
                             names
                            in
                         let uu____387 =
                           let _0_457 =
                             FStar_SMTEncoding_Term.inst instantiation lhs
                              in
                           let _0_456 =
                             FStar_SMTEncoding_Term.inst instantiation rhs
                              in
                           (_0_457, _0_456)  in
                         (match uu____387 with
                          | (lhs,rhs) ->
                              let uu____395 =
                                match lhs.FStar_SMTEncoding_Term.tm with
                                | FStar_SMTEncoding_Term.App
                                    (FStar_SMTEncoding_Term.And ,clauses_lhs)
                                    ->
                                    let uu____405 =
                                      FStar_Util.prefix clauses_lhs  in
                                    (match uu____405 with
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
                                                  labels ensures_conjuncts
                                                 in
                                              (match uu____439 with
                                               | (labels,ensures_conjuncts)
                                                   ->
                                                   let pats_ens1 =
                                                     match pats_ens with
                                                     | []|[]::[] -> [[post]]
                                                     | uu____460 -> pats_ens
                                                      in
                                                   let ens =
                                                     let _0_459 =
                                                       FStar_SMTEncoding_Term.Quant
                                                         (let _0_458 =
                                                            FStar_SMTEncoding_Term.mk
                                                              (FStar_SMTEncoding_Term.App
                                                                 (FStar_SMTEncoding_Term.Imp,
                                                                   [ensures_conjuncts;
                                                                   post]))
                                                              rng_ens
                                                             in
                                                          (FStar_SMTEncoding_Term.Forall,
                                                            pats_ens,
                                                            iopt_ens,
                                                            sorts_ens,
                                                            _0_458))
                                                        in
                                                     FStar_SMTEncoding_Term.mk
                                                       _0_459
                                                       ens.FStar_SMTEncoding_Term.rng
                                                      in
                                                   let lhs =
                                                     FStar_SMTEncoding_Term.mk
                                                       (FStar_SMTEncoding_Term.App
                                                          (FStar_SMTEncoding_Term.And,
                                                            (FStar_List.append
                                                               req [ens])))
                                                       lhs.FStar_SMTEncoding_Term.rng
                                                      in
                                                   let _0_460 =
                                                     FStar_SMTEncoding_Term.abstr
                                                       names lhs
                                                      in
                                                   (labels, _0_460))
                                          | uu____472 ->
                                              Prims.raise
                                                (Not_a_wp_implication
                                                   (let _0_463 =
                                                      let _0_462 =
                                                        let _0_461 =
                                                          FStar_SMTEncoding_Term.print_smt_term
                                                            ens
                                                           in
                                                        Prims.strcat "  ... "
                                                          _0_461
                                                         in
                                                      Prims.strcat post_name
                                                        _0_462
                                                       in
                                                    Prims.strcat
                                                      "Ensures clause doesn't match post name:  "
                                                      _0_463))))
                                | uu____476 ->
                                    Prims.raise
                                      (Not_a_wp_implication
                                         (let _0_464 =
                                            FStar_SMTEncoding_Term.print_smt_term
                                              lhs
                                             in
                                          Prims.strcat "LHS not a conjunct: "
                                            _0_464))
                                 in
                              (match uu____395 with
                               | (labels,lhs) ->
                                   let uu____487 =
                                     let uu____491 =
                                       aux default_msg None (Some post_name)
                                         labels rhs
                                        in
                                     match uu____491 with
                                     | (labels,rhs) ->
                                         let _0_465 =
                                           FStar_SMTEncoding_Term.abstr names
                                             rhs
                                            in
                                         (labels, _0_465)
                                      in
                                   (match uu____487 with
                                    | (labels,rhs) ->
                                        let body =
                                          FStar_SMTEncoding_Term.mkImp
                                            (lhs, rhs) rng
                                           in
                                        let _0_466 =
                                          FStar_SMTEncoding_Term.mk
                                            (FStar_SMTEncoding_Term.Quant
                                               (FStar_SMTEncoding_Term.Forall,
                                                 pats, iopt, (post :: sorts),
                                                 body))
                                            q.FStar_SMTEncoding_Term.rng
                                           in
                                        (labels, _0_466))))
                     | uu____516 ->
                         fallback
                           (let _0_467 =
                              FStar_SMTEncoding_Term.print_smt_term arg  in
                            Prims.strcat "arg not a quant: " _0_467)
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
                    let _0_469 =
                      let _0_468 = FStar_Syntax_Syntax.next_id ()  in
                      FStar_All.pipe_left FStar_Util.string_of_int _0_468  in
                    Prims.strcat "^^post_condition_" _0_469  in
                  let names = (post_name, post)  in
                  let instantiation =
                    let _0_470 = FStar_SMTEncoding_Util.mkFreeV names  in
                    [_0_470]  in
                  let uu____546 =
                    let _0_472 =
                      FStar_SMTEncoding_Term.inst instantiation lhs  in
                    let _0_471 =
                      FStar_SMTEncoding_Term.inst instantiation rhs  in
                    (_0_472, _0_471)  in
                  (match uu____546 with
                   | (lhs,rhs) ->
                       let uu____554 =
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
                                        labels r
                                       in
                                    (match uu____593 with
                                     | (labels,r) ->
                                         let _0_475 =
                                           let _0_474 =
                                             FStar_SMTEncoding_Term.Quant
                                               (let _0_473 =
                                                  FStar_SMTEncoding_Util.norng
                                                    FStar_SMTEncoding_Term.mk
                                                    (FStar_SMTEncoding_Term.App
                                                       (FStar_SMTEncoding_Term.Iff,
                                                         [l; r]))
                                                   in
                                                (FStar_SMTEncoding_Term.Forall,
                                                  [[p]],
                                                  (Some (Prims.parse_int "0")),
                                                  sorts, _0_473))
                                              in
                                           FStar_SMTEncoding_Term.mk _0_474
                                             q.FStar_SMTEncoding_Term.rng
                                            in
                                         (labels, _0_475))
                                | uu____612 -> (labels, tm)) labels
                           (conjuncts lhs)
                          in
                       (match uu____554 with
                        | (labels,lhs_conjs) ->
                            let uu____623 =
                              aux default_msg None (Some post_name) labels
                                rhs
                               in
                            (match uu____623 with
                             | (labels,rhs) ->
                                 let body =
                                   let uu____691 =
                                     let uu____692 =
                                       let uu____695 =
                                         FStar_SMTEncoding_Term.mk_and_l
                                           lhs_conjs
                                           lhs.FStar_SMTEncoding_Term.rng
                                          in
                                       (_0_476, rhs)  in
                                     FStar_SMTEncoding_Term.mkImp _0_477 rng
                                      in
                                   FStar_All.pipe_right _0_478
                                     (FStar_SMTEncoding_Term.abstr [names])
                                    in
                                 let q =
                                   FStar_SMTEncoding_Term.mk
                                     (FStar_SMTEncoding_Term.Quant
                                        (FStar_SMTEncoding_Term.Forall, [],
                                          None, [post], body))
                                     q.FStar_SMTEncoding_Term.rng
                                    in
                                 (labels, q))))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Imp ,lhs::rhs::[]) ->
                  let uu____649 =
                    aux default_msg ropt post_name_opt labels rhs  in
                  (match uu____649 with
                   | (labels,rhs) ->
                       let _0_479 = FStar_SMTEncoding_Util.mkImp (lhs, rhs)
                          in
                       (labels, _0_479))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.And ,conjuncts1) ->
                  let uu____726 =
                    FStar_Util.fold_map (aux default_msg ropt post_name_opt)
                      labels conjuncts
                     in
                  (match uu____664 with
                   | (labels,conjuncts) ->
                       let _0_480 =
                         FStar_SMTEncoding_Term.mk_and_l conjuncts
                           q.FStar_SMTEncoding_Term.rng
                          in
                       (labels, _0_480))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.ITE ,hd::q1::q2::[]) ->
                  let uu____684 =
                    aux default_msg ropt post_name_opt labels q1  in
                  (match uu____684 with
                   | (labels,q1) ->
                       let uu____695 =
                         aux default_msg ropt post_name_opt labels q2  in
                       (match uu____695 with
                        | (labels,q2) ->
                            let _0_481 =
                              FStar_SMTEncoding_Term.mkITE (hd, q1, q2)
                                q.FStar_SMTEncoding_Term.rng
                               in
                            (labels, _0_481)))
              | FStar_SMTEncoding_Term.Quant
                (FStar_SMTEncoding_Term.Exists ,_,_,_,_)
                |FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Iff ,_)
                 |FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Or ,_)
                  ->
                  let uu____719 =
                    fresh_label default_msg ropt q.FStar_SMTEncoding_Term.rng
                      q
                     in
                  (match uu____719 with | (lab,q) -> ((lab :: labels), q))
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
                  let uu____753 =
                    fresh_label default_msg ropt q.FStar_SMTEncoding_Term.rng
                      q
                     in
                  (match uu____753 with | (lab,q) -> ((lab :: labels), q))
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
                  let uu____796 =
                    aux default_msg ropt post_name_opt labels body  in
                  (match uu____796 with
                   | (labels,body) ->
                       let _0_482 =
                         FStar_SMTEncoding_Term.mk
                           (FStar_SMTEncoding_Term.Quant
                              (FStar_SMTEncoding_Term.Forall, pats, iopt,
                                sorts, body)) q.FStar_SMTEncoding_Term.rng
                          in
                       (labels, _0_482))
               in
            aux "assertion failed" None None [] q
  
let detail_errors :
  FStar_TypeChecker_Env.env ->
    labels ->
      (FStar_SMTEncoding_Term.decls_t ->
         ((FStar_SMTEncoding_Z3.unsat_core,(FStar_SMTEncoding_Term.error_labels
                                             *
                                             FStar_SMTEncoding_Z3.error_kind))
           FStar_Util.either * Prims.int))
        -> FStar_SMTEncoding_Term.error_label Prims.list
  =
  fun env  ->
    fun all_labels  ->
      fun askZ3  ->
        let print_banner uu____841 =
          let _0_485 =
            FStar_Range.string_of_range (FStar_TypeChecker_Env.get_range env)
             in
          let _0_484 = FStar_Util.string_of_int (Prims.parse_int "5")  in
          let _0_483 =
            FStar_Util.string_of_int (FStar_List.length all_labels)  in
          FStar_Util.print3_error
            "Detailed error report follows for %s\nTaking %s seconds per proof obligation (%s proofs in total)\n"
            _0_485 _0_484 _0_483
           in
        let print_result uu____853 =
          match uu____853 with
          | ((uu____859,msg,r),success) ->
              (match success with
               | true  ->
                   let _0_486 = FStar_Range.string_of_range r  in
                   FStar_Util.print1_error
                     "OK: proof obligation at %s was proven\n" _0_486
               | uu____866 -> FStar_Errors.report r msg)
           in
        let elim labs =
          FStar_All.pipe_right labs
            (FStar_List.map
               (fun uu____896  ->
                  match uu____896 with
                  | (l,uu____903,uu____904) ->
                      FStar_SMTEncoding_Term.Assume
                        (let _0_488 =
                           FStar_SMTEncoding_Util.mkEq
                             (let _0_487 = FStar_SMTEncoding_Util.mkFreeV l
                                 in
                              (_0_487, FStar_SMTEncoding_Util.mkTrue))
                            in
                         (_0_488, (Some "Disabling label"),
                           (Some
                              (Prims.strcat "disable_label_" (Prims.fst l)))))))
           in
        let rec linear_check eliminated errors active =
          match active with
          | [] ->
              let results =
                let _0_490 = FStar_List.map (fun x  -> (x, true)) eliminated
                   in
                let _0_489 = FStar_List.map (fun x  -> (x, false)) errors  in
                FStar_List.append _0_490 _0_489  in
              sort_labels results
          | hd::tl ->
              ((let _0_491 =
                  FStar_Util.string_of_int (FStar_List.length active)  in
                FStar_Util.print1 "%s, " _0_491);
               FStar_SMTEncoding_Z3.refresh ();
               (let uu____959 =
                  askZ3
                    (FStar_All.pipe_left elim
                       (FStar_List.append eliminated
                          (FStar_List.append errors tl)))
                   in
                match uu____959 with
                | (result,uu____980) ->
                    let uu____989 = FStar_Util.is_left result  in
                    (match uu____989 with
                     | true  -> linear_check (hd :: eliminated) errors tl
                     | uu____998 -> linear_check eliminated (hd :: errors) tl)))
           in
        print_banner ();
        FStar_Options.set_option "z3rlimit"
          (FStar_Options.Int (Prims.parse_int "5"));
        (let res = linear_check [] [] all_labels  in
         FStar_Util.print_string "\n";
         FStar_All.pipe_right res (FStar_List.iter print_result);
         [])
  