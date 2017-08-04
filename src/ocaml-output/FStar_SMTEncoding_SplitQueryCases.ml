open Prims
let rec get_next_n_ite :
  Prims.int ->
    FStar_SMTEncoding_Term.term ->
      FStar_SMTEncoding_Term.term ->
        (FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term) ->
          (Prims.bool,FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.term,
            FStar_SMTEncoding_Term.term) FStar_Pervasives_Native.tuple4
  =
  fun n1  ->
    fun t  ->
      fun negs  ->
        fun f  ->
          if n1 <= (Prims.parse_int "0")
          then
            let uu____38 = f FStar_SMTEncoding_Util.mkTrue  in
            (true, uu____38, negs, t)
          else
            (match t.FStar_SMTEncoding_Term.tm with
             | FStar_SMTEncoding_Term.App
                 (FStar_SMTEncoding_Term.ITE ,g::t1::e::uu____51) ->
                 let uu____56 =
                   let uu____57 =
                     let uu____62 = FStar_SMTEncoding_Util.mkNot g  in
                     (negs, uu____62)  in
                   FStar_SMTEncoding_Util.mkAnd uu____57  in
                 get_next_n_ite (n1 - (Prims.parse_int "1")) e uu____56
                   (fun x  ->
                      let uu____66 = FStar_SMTEncoding_Util.mkITE (g, t1, x)
                         in
                      f uu____66)
             | FStar_SMTEncoding_Term.FreeV uu____67 ->
                 let uu____72 = f FStar_SMTEncoding_Util.mkTrue  in
                 (true, uu____72, negs, t)
             | uu____73 ->
                 (false, FStar_SMTEncoding_Util.mkFalse,
                   FStar_SMTEncoding_Util.mkFalse,
                   FStar_SMTEncoding_Util.mkFalse))
  
let rec is_ite_all_the_way :
  Prims.int ->
    FStar_SMTEncoding_Term.term ->
      FStar_SMTEncoding_Term.term ->
        FStar_SMTEncoding_Term.term Prims.list ->
          (Prims.bool,FStar_SMTEncoding_Term.term Prims.list,FStar_SMTEncoding_Term.term)
            FStar_Pervasives_Native.tuple3
  =
  fun n1  ->
    fun t  ->
      fun negs  ->
        fun l  ->
          if n1 <= (Prims.parse_int "0")
          then FStar_Exn.raise FStar_Util.Impos
          else
            (match t.FStar_SMTEncoding_Term.tm with
             | FStar_SMTEncoding_Term.FreeV uu____127 ->
                 let uu____132 =
                   let uu____133 =
                     let uu____138 = FStar_SMTEncoding_Util.mkNot t  in
                     (negs, uu____138)  in
                   FStar_SMTEncoding_Util.mkAnd uu____133  in
                 (true, l, uu____132)
             | uu____141 ->
                 let uu____142 = get_next_n_ite n1 t negs (fun x  -> x)  in
                 (match uu____142 with
                  | (b,t1,negs',rest) ->
                      if b
                      then
                        let uu____173 =
                          let uu____176 =
                            FStar_SMTEncoding_Util.mkImp (negs, t1)  in
                          uu____176 :: l  in
                        is_ite_all_the_way n1 rest negs' uu____173
                      else (false, [], FStar_SMTEncoding_Util.mkFalse)))
  
let rec parse_query_for_split_cases :
  Prims.int ->
    FStar_SMTEncoding_Term.term ->
      (FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term) ->
        (Prims.bool,(FStar_SMTEncoding_Term.term ->
                       FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.term
                                                     Prims.list,FStar_SMTEncoding_Term.term)
                      FStar_Pervasives_Native.tuple3)
          FStar_Pervasives_Native.tuple2
  =
  fun n1  ->
    fun t  ->
      fun f  ->
        match t.FStar_SMTEncoding_Term.tm with
        | FStar_SMTEncoding_Term.Quant
            (FStar_SMTEncoding_Term.Forall ,l,opt,l',t1) ->
            parse_query_for_split_cases n1 t1
              (fun x  ->
                 let uu____248 =
                   FStar_SMTEncoding_Util.mkForall'' (l, opt, l', x)  in
                 f uu____248)
        | FStar_SMTEncoding_Term.App
            (FStar_SMTEncoding_Term.Imp ,t1::t2::uu____259) ->
            let r =
              match t2.FStar_SMTEncoding_Term.tm with
              | FStar_SMTEncoding_Term.Quant
                  (FStar_SMTEncoding_Term.Forall
                   ,uu____293,uu____294,uu____295,uu____296)
                  ->
                  parse_query_for_split_cases n1 t2
                    (fun x  ->
                       let uu____316 = FStar_SMTEncoding_Util.mkImp (t1, x)
                          in
                       f uu____316)
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.ITE ,uu____317) ->
                  let uu____322 =
                    is_ite_all_the_way n1 t2 FStar_SMTEncoding_Util.mkTrue []
                     in
                  (match uu____322 with
                   | (b,l,negs) ->
                       (b,
                         (((fun x  ->
                              let uu____369 =
                                FStar_SMTEncoding_Util.mkImp (t1, x)  in
                              f uu____369)), l, negs)))
              | uu____370 ->
                  (false,
                    (((fun uu____386  ->
                         FStar_Util.return_all FStar_SMTEncoding_Util.mkFalse)),
                      [], FStar_SMTEncoding_Util.mkFalse))
               in
            r
        | FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE ,uu____387)
            ->
            let uu____392 =
              is_ite_all_the_way n1 t FStar_SMTEncoding_Util.mkTrue []  in
            (match uu____392 with | (b,l,negs) -> (b, (f, l, negs)))
        | uu____436 ->
            (false,
              (((fun uu____452  ->
                   FStar_Util.return_all FStar_SMTEncoding_Util.mkFalse)),
                [], FStar_SMTEncoding_Util.mkFalse))
  
let strip_not : FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term =
  fun t  ->
    match t.FStar_SMTEncoding_Term.tm with
    | FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Not ,hd1::uu____458)
        -> hd1
    | uu____463 -> t
  
let handle_query :
  (FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.term
                                                                Prims.list,
    FStar_SMTEncoding_Term.term) FStar_Pervasives_Native.tuple3 ->
    (FStar_SMTEncoding_Term.decl -> Prims.unit) -> Prims.unit
  =
  fun uu____484  ->
    fun check  ->
      match uu____484 with
      | (f,l,negs) -> failwith "SplitQueryCases is not currently supported"
  