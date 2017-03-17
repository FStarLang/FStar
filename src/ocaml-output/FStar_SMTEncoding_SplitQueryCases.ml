open Prims
let rec get_next_n_ite :
  Prims.int ->
    FStar_SMTEncoding_Term.term ->
      FStar_SMTEncoding_Term.term ->
        (FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term) ->
          (Prims.bool * FStar_SMTEncoding_Term.term *
            FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.term)
  =
  fun n1  ->
    fun t  ->
      fun negs  ->
        fun f  ->
          match n <= (Prims.parse_int "0") with
          | true  ->
              let _0_354 = f FStar_SMTEncoding_Util.mkTrue  in
              (true, _0_354, negs, t)
          | uu____30 ->
              (match t.FStar_SMTEncoding_Term.tm with
               | FStar_SMTEncoding_Term.App
                   (FStar_SMTEncoding_Term.ITE ,g::t::e::uu____38) ->
                   let _0_356 =
                     FStar_SMTEncoding_Util.mkAnd
                       (let _0_355 = FStar_SMTEncoding_Util.mkNot g  in
                        (negs, _0_355))
                      in
                   get_next_n_ite (n - (Prims.parse_int "1")) e _0_356
                     (fun x  -> f (FStar_SMTEncoding_Util.mkITE (g, t, x)))
               | FStar_SMTEncoding_Term.FreeV uu____42 ->
                   let _0_357 = f FStar_SMTEncoding_Util.mkTrue  in
                   (true, _0_357, negs, t)
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
  fun n1  ->
    fun t  ->
      fun negs  ->
        fun l  ->
          match n <= (Prims.parse_int "0") with
          | true  -> Prims.raise FStar_Util.Impos
          | uu____76 ->
              (match t.FStar_SMTEncoding_Term.tm with
               | FStar_SMTEncoding_Term.FreeV uu____81 ->
                   let _0_359 =
                     FStar_SMTEncoding_Util.mkAnd
                       (let _0_358 = FStar_SMTEncoding_Util.mkNot t  in
                        (negs, _0_358))
                      in
                   (true, l, _0_359)
               | uu____85 ->
                   let uu____86 = get_next_n_ite n t negs (fun x  -> x)  in
                   (match uu____86 with
                    | (b,t,negs',rest) ->
                        (match b with
                         | true  ->
                             let _0_361 =
                               let _0_360 =
                                 FStar_SMTEncoding_Util.mkImp (negs, t)  in
                               _0_360 :: l  in
                             is_ite_all_the_way n rest negs' _0_361
                         | uu____104 ->
                             (false, [], FStar_SMTEncoding_Util.mkFalse))))
  
let rec parse_query_for_split_cases :
  Prims.int ->
    FStar_SMTEncoding_Term.term ->
      (FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term) ->
        (Prims.bool *
          ((FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term) *
          FStar_SMTEncoding_Term.term Prims.list *
          FStar_SMTEncoding_Term.term))
  =
  fun n1  ->
    fun t  ->
      fun f  ->
        match t.FStar_SMTEncoding_Term.tm with
        | FStar_SMTEncoding_Term.Quant
            (FStar_SMTEncoding_Term.Forall ,l,opt,l',t1) ->
            parse_query_for_split_cases n1 t1
              (fun x  ->
                 let uu____173 =
                   FStar_SMTEncoding_Util.mkForall'' (l, opt, l', x) in
                 f uu____173)
        | FStar_SMTEncoding_Term.App
            (FStar_SMTEncoding_Term.Imp ,t1::t2::uu____180) ->
            let r =
              match t2.FStar_SMTEncoding_Term.tm with
              | FStar_SMTEncoding_Term.Quant
                  (FStar_SMTEncoding_Term.Forall
                   ,uu____200,uu____201,uu____202,uu____203)
                  ->
                  parse_query_for_split_cases n1 t2
                    (fun x  ->
                       let uu____213 = FStar_SMTEncoding_Util.mkImp (t1, x) in
                       f uu____213)
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.ITE ,uu____196) ->
                  let uu____199 =
                    is_ite_all_the_way n t2 FStar_SMTEncoding_Util.mkTrue []
                     in
                  (match uu____199 with
                   | (b,l,negs) ->
                       (b,
                         (((fun x  ->
                              let uu____245 =
                                FStar_SMTEncoding_Util.mkImp (t1, x) in
                              f uu____245)), l, negs)))
              | uu____246 ->
                  (false,
                    (((fun uu____237  -> FStar_SMTEncoding_Util.mkFalse)),
                      [], FStar_SMTEncoding_Util.mkFalse))
               in
            r
        | FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE ,uu____257)
            ->
            let uu____241 =
              is_ite_all_the_way n t FStar_SMTEncoding_Util.mkTrue []  in
            (match uu____241 with | (b,l,negs) -> (b, (f, l, negs)))
        | uu____268 ->
            (false,
              (((fun uu____297  -> FStar_SMTEncoding_Util.mkFalse)), [],
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
                  (let _0_362 = FStar_SMTEncoding_Util.mkNot (f t)  in
                   (_0_362, None, None)))) (FStar_List.rev l)
  
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
             (let _0_363 =
                FStar_SMTEncoding_Util.mkNot
                  (f (FStar_SMTEncoding_Util.mkNot negs))
                 in
              (_0_363, None, None)))
  
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
          let _0_364 = strip_not q'  in
          parse_query_for_split_cases n _0_364 (fun x  -> x)
      | uu____368 ->
          (false, (((fun x  -> x)), [], FStar_SMTEncoding_Util.mkFalse))
  
let handle_query :
  ((FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term) *
    FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.term) ->
    (FStar_SMTEncoding_Term.decl -> Prims.unit) -> Prims.unit
  =
  fun uu____320  ->
    fun check  ->
      match uu____393 with
      | (f,l,negs) ->
          (check_split_cases f l check; check_exhaustiveness f negs check)
  