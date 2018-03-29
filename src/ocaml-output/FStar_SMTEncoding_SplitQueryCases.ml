open Prims
let rec (get_next_n_ite :
  Prims.int ->
    FStar_SMTEncoding_Term.term ->
      FStar_SMTEncoding_Term.term ->
        (FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term) ->
          (Prims.bool,FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.term,
            FStar_SMTEncoding_Term.term) FStar_Pervasives_Native.tuple4)
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
                 (FStar_SMTEncoding_Term.ITE ,g::t1::e::uu____47) ->
                 let uu____52 =
                   let uu____53 =
                     let uu____58 = FStar_SMTEncoding_Util.mkNot g  in
                     (negs, uu____58)  in
                   FStar_SMTEncoding_Util.mkAnd uu____53  in
                 get_next_n_ite (n1 - (Prims.parse_int "1")) e uu____52
                   (fun x  ->
                      let uu____62 = FStar_SMTEncoding_Util.mkITE (g, t1, x)
                         in
                      f uu____62)
             | FStar_SMTEncoding_Term.FreeV uu____63 ->
                 let uu____68 = f FStar_SMTEncoding_Util.mkTrue  in
                 (true, uu____68, negs, t)
             | uu____69 ->
                 (false, FStar_SMTEncoding_Util.mkFalse,
                   FStar_SMTEncoding_Util.mkFalse,
                   FStar_SMTEncoding_Util.mkFalse))
  
let rec (is_ite_all_the_way :
  Prims.int ->
    FStar_SMTEncoding_Term.term ->
      FStar_SMTEncoding_Term.term ->
        FStar_SMTEncoding_Term.term Prims.list ->
          (Prims.bool,FStar_SMTEncoding_Term.term Prims.list,FStar_SMTEncoding_Term.term)
            FStar_Pervasives_Native.tuple3)
  =
  fun n1  ->
    fun t  ->
      fun negs  ->
        fun l  ->
          if n1 <= (Prims.parse_int "0")
          then FStar_Exn.raise FStar_Util.Impos
          else
            (match t.FStar_SMTEncoding_Term.tm with
             | FStar_SMTEncoding_Term.FreeV uu____119 ->
                 let uu____124 =
                   let uu____125 =
                     let uu____130 = FStar_SMTEncoding_Util.mkNot t  in
                     (negs, uu____130)  in
                   FStar_SMTEncoding_Util.mkAnd uu____125  in
                 (true, l, uu____124)
             | uu____133 ->
                 let uu____134 = get_next_n_ite n1 t negs (fun x  -> x)  in
                 (match uu____134 with
                  | (b,t1,negs',rest) ->
                      if b
                      then
                        let uu____165 =
                          let uu____168 =
                            FStar_SMTEncoding_Util.mkImp (negs, t1)  in
                          uu____168 :: l  in
                        is_ite_all_the_way n1 rest negs' uu____165
                      else (false, [], FStar_SMTEncoding_Util.mkFalse)))
  
let rec (parse_query_for_split_cases :
  Prims.int ->
    FStar_SMTEncoding_Term.term ->
      (FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term) ->
        (Prims.bool,(FStar_SMTEncoding_Term.term ->
                       FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.term
                                                     Prims.list,FStar_SMTEncoding_Term.term)
                      FStar_Pervasives_Native.tuple3)
          FStar_Pervasives_Native.tuple2)
  =
  fun n1  ->
    fun t  ->
      fun f  ->
        match t.FStar_SMTEncoding_Term.tm with
        | FStar_SMTEncoding_Term.Quant
            (FStar_SMTEncoding_Term.Forall ,l,opt,l',t1) ->
            parse_query_for_split_cases n1 t1
              (fun x  ->
                 let uu____237 =
                   FStar_SMTEncoding_Util.mkForall'' (l, opt, l', x)  in
                 f uu____237)
        | FStar_SMTEncoding_Term.App
            (FStar_SMTEncoding_Term.Imp ,t1::t2::uu____248) ->
            let r =
              match t2.FStar_SMTEncoding_Term.tm with
              | FStar_SMTEncoding_Term.Quant
                  (FStar_SMTEncoding_Term.Forall
                   ,uu____282,uu____283,uu____284,uu____285)
                  ->
                  parse_query_for_split_cases n1 t2
                    (fun x  ->
                       let uu____305 = FStar_SMTEncoding_Util.mkImp (t1, x)
                          in
                       f uu____305)
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.ITE ,uu____306) ->
                  let uu____311 =
                    is_ite_all_the_way n1 t2 FStar_SMTEncoding_Util.mkTrue []
                     in
                  (match uu____311 with
                   | (b,l,negs) ->
                       (b,
                         (((fun x  ->
                              let uu____358 =
                                FStar_SMTEncoding_Util.mkImp (t1, x)  in
                              f uu____358)), l, negs)))
              | uu____359 ->
                  (false,
                    (((fun uu____375  ->
                         FStar_Util.return_all FStar_SMTEncoding_Util.mkFalse)),
                      [], FStar_SMTEncoding_Util.mkFalse))
               in
            r
        | FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE ,uu____376)
            ->
            let uu____381 =
              is_ite_all_the_way n1 t FStar_SMTEncoding_Util.mkTrue []  in
            (match uu____381 with | (b,l,negs) -> (b, (f, l, negs)))
        | uu____425 ->
            (false,
              (((fun uu____441  ->
                   FStar_Util.return_all FStar_SMTEncoding_Util.mkFalse)),
                [], FStar_SMTEncoding_Util.mkFalse))
  
let (strip_not : FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term)
  =
  fun t  ->
    match t.FStar_SMTEncoding_Term.tm with
    | FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Not ,hd1::uu____446)
        -> hd1
    | uu____451 -> t
  
let (handle_query :
  (FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.term
                                                                Prims.list,
    FStar_SMTEncoding_Term.term) FStar_Pervasives_Native.tuple3 ->
    (FStar_SMTEncoding_Term.decl -> Prims.unit) -> Prims.unit)
  =
  fun uu____470  ->
    fun check1  ->
      match uu____470 with
      | (f,l,negs) -> failwith "SplitQueryCases is not currently supported"
  