open Prims
let rec get_next_n_ite:
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
            let uu____30 = f FStar_SMTEncoding_Util.mkTrue in
            (true, uu____30, negs, t)
          else
            (match t.FStar_SMTEncoding_Term.tm with
             | FStar_SMTEncoding_Term.App
                 (FStar_SMTEncoding_Term.ITE ,g::t1::e::uu____39) ->
                 let uu____42 =
                   let uu____43 =
                     let uu____46 = FStar_SMTEncoding_Util.mkNot g in
                     (negs, uu____46) in
                   FStar_SMTEncoding_Util.mkAnd uu____43 in
                 get_next_n_ite (n1 - (Prims.parse_int "1")) e uu____42
                   (fun x  ->
                      let uu____50 = FStar_SMTEncoding_Util.mkITE (g, t1, x) in
                      f uu____50)
             | FStar_SMTEncoding_Term.FreeV uu____51 ->
                 let uu____54 = f FStar_SMTEncoding_Util.mkTrue in
                 (true, uu____54, negs, t)
             | uu____55 ->
                 (false, FStar_SMTEncoding_Util.mkFalse,
                   FStar_SMTEncoding_Util.mkFalse,
                   FStar_SMTEncoding_Util.mkFalse))
let rec is_ite_all_the_way:
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
          then raise FStar_Util.Impos
          else
            (match t.FStar_SMTEncoding_Term.tm with
             | FStar_SMTEncoding_Term.FreeV uu____91 ->
                 let uu____94 =
                   let uu____95 =
                     let uu____98 = FStar_SMTEncoding_Util.mkNot t in
                     (negs, uu____98) in
                   FStar_SMTEncoding_Util.mkAnd uu____95 in
                 (true, l, uu____94)
             | uu____100 ->
                 let uu____101 = get_next_n_ite n1 t negs (fun x  -> x) in
                 (match uu____101 with
                  | (b,t1,negs',rest) ->
                      if b
                      then
                        let uu____120 =
                          let uu____122 =
                            FStar_SMTEncoding_Util.mkImp (negs, t1) in
                          uu____122 :: l in
                        is_ite_all_the_way n1 rest negs' uu____120
                      else (false, [], FStar_SMTEncoding_Util.mkFalse)))
let rec parse_query_for_split_cases:
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
                       let uu____215 = FStar_SMTEncoding_Util.mkImp (t1, x) in
                       f uu____215)
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.ITE ,uu____216) ->
                  let uu____219 =
                    is_ite_all_the_way n1 t2 FStar_SMTEncoding_Util.mkTrue [] in
                  (match uu____219 with
                   | (b,l,negs) ->
                       (b,
                         (((fun x  ->
                              let uu____249 =
                                FStar_SMTEncoding_Util.mkImp (t1, x) in
                              f uu____249)), l, negs)))
              | uu____250 ->
                  (false,
                    (((fun uu____261  -> FStar_SMTEncoding_Util.mkFalse)),
                      [], FStar_SMTEncoding_Util.mkFalse)) in
            r
        | FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE ,uu____262)
            ->
            let uu____265 =
              is_ite_all_the_way n1 t FStar_SMTEncoding_Util.mkTrue [] in
            (match uu____265 with | (b,l,negs) -> (b, (f, l, negs)))
        | uu____292 ->
            (false,
              (((fun uu____303  -> FStar_SMTEncoding_Util.mkFalse)), [],
                FStar_SMTEncoding_Util.mkFalse))
let strip_not: FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term =
  fun t  ->
    match t.FStar_SMTEncoding_Term.tm with
    | FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Not ,hd1::uu____309)
        -> hd1
    | uu____312 -> t
let handle_query:
  (FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.term
                                                                Prims.list,
    FStar_SMTEncoding_Term.term) FStar_Pervasives_Native.tuple3 ->
    (FStar_SMTEncoding_Term.decl -> Prims.unit) -> Prims.unit
  =
  fun uu____329  ->
    fun check  ->
      match uu____329 with
      | (f,l,negs) -> failwith "SplitQueryCases is not currently supported"