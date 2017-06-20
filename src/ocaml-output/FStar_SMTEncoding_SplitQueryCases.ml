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
          if n1 <= (Prims.parse_int "0")
          then
            let uu____34 = f FStar_SMTEncoding_Util.mkTrue  in
            (true, uu____34, negs, t)
          else
            (match t.FStar_SMTEncoding_Term.tm with
             | FStar_SMTEncoding_Term.App
                 (FStar_SMTEncoding_Term.ITE ,g::t1::e::uu____43) ->
                 let uu____46 =
                   let uu____47 =
                     let uu____50 = FStar_SMTEncoding_Util.mkNot g  in
                     (negs, uu____50)  in
                   FStar_SMTEncoding_Util.mkAnd uu____47  in
                 get_next_n_ite (n1 - (Prims.parse_int "1")) e uu____46
                   (fun x  ->
                      let uu____52 = FStar_SMTEncoding_Util.mkITE (g, t1, x)
                         in
                      f uu____52)
             | FStar_SMTEncoding_Term.FreeV uu____53 ->
                 let uu____56 = f FStar_SMTEncoding_Util.mkTrue  in
                 (true, uu____56, negs, t)
             | uu____57 ->
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
          if n1 <= (Prims.parse_int "0")
          then raise FStar_Util.Impos
          else
            (match t.FStar_SMTEncoding_Term.tm with
             | FStar_SMTEncoding_Term.FreeV uu____97 ->
                 let uu____100 =
                   let uu____101 =
                     let uu____104 = FStar_SMTEncoding_Util.mkNot t  in
                     (negs, uu____104)  in
                   FStar_SMTEncoding_Util.mkAnd uu____101  in
                 (true, l, uu____100)
             | uu____106 ->
                 let uu____107 = get_next_n_ite n1 t negs (fun x  -> x)  in
                 (match uu____107 with
                  | (b,t1,negs',rest) ->
                      if b
                      then
                        let uu____125 =
                          let uu____127 =
                            FStar_SMTEncoding_Util.mkImp (negs, t1)  in
                          uu____127 :: l  in
                        is_ite_all_the_way n1 rest negs' uu____125
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
  fun n1  ->
    fun t  ->
      fun f  ->
        match t.FStar_SMTEncoding_Term.tm with
        | FStar_SMTEncoding_Term.Quant
            (FStar_SMTEncoding_Term.Forall ,l,opt,l',t1) ->
            parse_query_for_split_cases n1 t1
              (fun x  ->
                 let uu____184 =
                   FStar_SMTEncoding_Util.mkForall'' (l, opt, l', x)  in
                 f uu____184)
        | FStar_SMTEncoding_Term.App
            (FStar_SMTEncoding_Term.Imp ,t1::t2::uu____191) ->
            let r =
              match t2.FStar_SMTEncoding_Term.tm with
              | FStar_SMTEncoding_Term.Quant
                  (FStar_SMTEncoding_Term.Forall
                   ,uu____211,uu____212,uu____213,uu____214)
                  ->
                  parse_query_for_split_cases n1 t2
                    (fun x  ->
                       let uu____224 = FStar_SMTEncoding_Util.mkImp (t1, x)
                          in
                       f uu____224)
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.ITE ,uu____225) ->
                  let uu____228 =
                    is_ite_all_the_way n1 t2 FStar_SMTEncoding_Util.mkTrue []
                     in
                  (match uu____228 with
                   | (b,l,negs) ->
                       (b,
                         (((fun x  ->
                              let uu____256 =
                                FStar_SMTEncoding_Util.mkImp (t1, x)  in
                              f uu____256)), l, negs)))
              | uu____257 ->
                  (false,
                    (((fun uu____267  -> FStar_SMTEncoding_Util.mkFalse)),
                      [], FStar_SMTEncoding_Util.mkFalse))
               in
            r
        | FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE ,uu____268)
            ->
            let uu____271 =
              is_ite_all_the_way n1 t FStar_SMTEncoding_Util.mkTrue []  in
            (match uu____271 with | (b,l,negs) -> (b, (f, l, negs)))
        | uu____298 ->
            (false,
              (((fun uu____308  -> FStar_SMTEncoding_Util.mkFalse)), [],
                FStar_SMTEncoding_Util.mkFalse))
  
let strip_not : FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term =
  fun t  ->
    match t.FStar_SMTEncoding_Term.tm with
    | FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Not ,hd1::uu____314)
        -> hd1
    | uu____317 -> t
  
let handle_query :
  ((FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term) *
    FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.term) ->
    (FStar_SMTEncoding_Term.decl -> Prims.unit) -> Prims.unit
  =
  fun uu____334  ->
    fun check  ->
      match uu____334 with
      | (f,l,negs) -> failwith "SplitQueryCases is not currently supported"
  