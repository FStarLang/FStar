open Prims
let rec get_next_n_ite :
  Prims.int ->
    FStar_SMTEncoding_Term.term ->
      FStar_SMTEncoding_Term.term ->
        (FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term) ->
          (Prims.bool * FStar_SMTEncoding_Term.term *
            FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.term)
  =
  fun n  ->
    fun t  ->
      fun negs  ->
        fun f  ->
          if n <= (Prims.parse_int "0")
          then
            let _0_506 = f FStar_SMTEncoding_Util.mkTrue  in
            (true, _0_506, negs, t)
          else
            (match t.FStar_SMTEncoding_Term.tm with
             | FStar_SMTEncoding_Term.App
                 (FStar_SMTEncoding_Term.ITE ,g::t::e::uu____38) ->
                 let _0_508 =
                   FStar_SMTEncoding_Util.mkAnd
                     (let _0_507 = FStar_SMTEncoding_Util.mkNot g  in
                      (negs, _0_507))
                    in
                 get_next_n_ite (n - (Prims.parse_int "1")) e _0_508
                   (fun x  -> f (FStar_SMTEncoding_Util.mkITE (g, t, x)))
             | FStar_SMTEncoding_Term.FreeV uu____42 ->
                 let _0_509 = f FStar_SMTEncoding_Util.mkTrue  in
                 (true, _0_509, negs, t)
             | uu____45 ->
                 (false, FStar_SMTEncoding_Util.mkFalse,
                   FStar_SMTEncoding_Util.mkFalse,
                   FStar_SMTEncoding_Util.mkFalse))
  
let rec is_ite_all_the_way :
  Prims.int ->
    FStar_SMTEncoding_Term.term ->
      FStar_SMTEncoding_Term.term ->
        FStar_SMTEncoding_Term.term Prims.list ->
          (Prims.bool * FStar_SMTEncoding_Term.term Prims.list *
            FStar_SMTEncoding_Term.term)
  =
  fun n  ->
    fun t  ->
      fun negs  ->
        fun l  ->
          if n <= (Prims.parse_int "0")
          then Prims.raise FStar_Util.Impos
          else
            (match t.FStar_SMTEncoding_Term.tm with
             | FStar_SMTEncoding_Term.FreeV uu____81 ->
                 let _0_511 =
                   FStar_SMTEncoding_Util.mkAnd
                     (let _0_510 = FStar_SMTEncoding_Util.mkNot t  in
                      (negs, _0_510))
                    in
                 (true, l, _0_511)
             | uu____85 ->
                 let uu____86 = get_next_n_ite n t negs (fun x  -> x)  in
                 (match uu____86 with
                  | (b,t,negs',rest) ->
                      if b
                      then
                        let _0_513 =
                          let _0_512 = FStar_SMTEncoding_Util.mkImp (negs, t)
                             in
                          _0_512 :: l  in
                        is_ite_all_the_way n rest negs' _0_513
                      else (false, [], FStar_SMTEncoding_Util.mkFalse)))
  
let rec parse_query_for_split_cases :
  Prims.int ->
    FStar_SMTEncoding_Term.term ->
      (FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term) ->
        (Prims.bool *
          ((FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term) *
          FStar_SMTEncoding_Term.term Prims.list *
          FStar_SMTEncoding_Term.term))
  =
  fun n  ->
    fun t  ->
      fun f  ->
        match t.FStar_SMTEncoding_Term.tm with
        | FStar_SMTEncoding_Term.Quant
            (FStar_SMTEncoding_Term.Forall ,l,opt,l',t) ->
            parse_query_for_split_cases n t
              (fun x  ->
                 f (FStar_SMTEncoding_Util.mkForall'' (l, opt, l', x)))
        | FStar_SMTEncoding_Term.App
            (FStar_SMTEncoding_Term.Imp ,t1::t2::uu____163) ->
            let r =
              match t2.FStar_SMTEncoding_Term.tm with
              | FStar_SMTEncoding_Term.Quant
                  (FStar_SMTEncoding_Term.Forall
                   ,uu____183,uu____184,uu____185,uu____186)
                  ->
                  parse_query_for_split_cases n t2
                    (fun x  -> f (FStar_SMTEncoding_Util.mkImp (t1, x)))
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.ITE ,uu____196) ->
                  let uu____199 =
                    is_ite_all_the_way n t2 FStar_SMTEncoding_Util.mkTrue []
                     in
                  (match uu____199 with
                   | (b,l,negs) ->
                       (b,
                         (((fun x  ->
                              f (FStar_SMTEncoding_Util.mkImp (t1, x)))), l,
                           negs)))
              | uu____227 ->
                  (false,
                    (((fun uu____237  -> FStar_SMTEncoding_Util.mkFalse)),
                      [], FStar_SMTEncoding_Util.mkFalse))
               in
            r
        | FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE ,uu____238)
            ->
            let uu____241 =
              is_ite_all_the_way n t FStar_SMTEncoding_Util.mkTrue []  in
            (match uu____241 with | (b,l,negs) -> (b, (f, l, negs)))
        | uu____268 ->
            (false,
              (((fun uu____278  -> FStar_SMTEncoding_Util.mkFalse)), [],
                FStar_SMTEncoding_Util.mkFalse))
  
let strip_not : FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term =
  fun t  ->
    match t.FStar_SMTEncoding_Term.tm with
    | FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Not ,hd::uu____283)
        -> hd
    | uu____286 -> t
  
let rec check_split_cases :
  (FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term) ->
    FStar_SMTEncoding_Term.term Prims.list ->
      (FStar_SMTEncoding_Term.decl -> Prims.unit) -> Prims.unit
  =
  fun f  ->
    fun l  ->
      fun check  ->
        FStar_List.iter
          (fun t  ->
             check
               (FStar_SMTEncoding_Term.Assume
                  (let _0_514 = FStar_SMTEncoding_Util.mkNot (f t)  in
                   (_0_514, None, None)))) (FStar_List.rev l)
  
let check_exhaustiveness :
  (FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term) ->
    FStar_SMTEncoding_Term.term ->
      (FStar_SMTEncoding_Term.decl -> Prims.unit) -> Prims.unit
  =
  fun f  ->
    fun negs  ->
      fun check  ->
        check
          (FStar_SMTEncoding_Term.Assume
             (let _0_515 =
                FStar_SMTEncoding_Util.mkNot
                  (f (FStar_SMTEncoding_Util.mkNot negs))
                 in
              (_0_515, None, None)))
  
let can_handle_query :
  Prims.int ->
    FStar_SMTEncoding_Term.decl ->
      (Prims.bool *
        ((FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term) *
        FStar_SMTEncoding_Term.term Prims.list *
        FStar_SMTEncoding_Term.term))
  =
  fun n  ->
    fun q  ->
      match q with
      | FStar_SMTEncoding_Term.Assume (q',uu____363,uu____364) ->
          let _0_516 = strip_not q'  in
          parse_query_for_split_cases n _0_516 (fun x  -> x)
      | uu____368 ->
          (false, (((fun x  -> x)), [], FStar_SMTEncoding_Util.mkFalse))
  
let handle_query :
  ((FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term) *
    FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.term) ->
    (FStar_SMTEncoding_Term.decl -> Prims.unit) -> Prims.unit
  =
  fun uu____393  ->
    fun check  ->
      match uu____393 with
      | (f,l,negs) ->
          (check_split_cases f l check; check_exhaustiveness f negs check)
  