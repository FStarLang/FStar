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
            let uu____42 = f FStar_SMTEncoding_Util.mkTrue in
            (true, uu____42, negs, t)
          else
            (match t.FStar_SMTEncoding_Term.tm with
             | FStar_SMTEncoding_Term.App
                 (FStar_SMTEncoding_Term.ITE ,g::t1::e::uu____55) ->
                 let uu____60 =
                   let uu____61 =
                     let uu____66 = FStar_SMTEncoding_Util.mkNot g in
                     (negs, uu____66) in
                   FStar_SMTEncoding_Util.mkAnd uu____61 in
                 get_next_n_ite (n1 - (Prims.parse_int "1")) e uu____60
                   (fun x  ->
                      let uu____68 = FStar_SMTEncoding_Util.mkITE (g, t1, x) in
                      f uu____68)
             | FStar_SMTEncoding_Term.FreeV uu____69 ->
                 let uu____74 = f FStar_SMTEncoding_Util.mkTrue in
                 (true, uu____74, negs, t)
             | uu____75 ->
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
             | FStar_SMTEncoding_Term.FreeV uu____133 ->
                 let uu____138 =
                   let uu____139 =
                     let uu____144 = FStar_SMTEncoding_Util.mkNot t in
                     (negs, uu____144) in
                   FStar_SMTEncoding_Util.mkAnd uu____139 in
                 (true, l, uu____138)
             | uu____147 ->
                 let uu____148 = get_next_n_ite n1 t negs (fun x  -> x) in
                 (match uu____148 with
                  | (b,t1,negs',rest) ->
                      if b
                      then
                        let uu____178 =
                          let uu____181 =
                            FStar_SMTEncoding_Util.mkImp (negs, t1) in
                          uu____181 :: l in
                        is_ite_all_the_way n1 rest negs' uu____178
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
                 let uu____262 =
                   FStar_SMTEncoding_Util.mkForall'' (l, opt, l', x) in
                 f uu____262)
        | FStar_SMTEncoding_Term.App
            (FStar_SMTEncoding_Term.Imp ,t1::t2::uu____273) ->
            let r =
              match t2.FStar_SMTEncoding_Term.tm with
              | FStar_SMTEncoding_Term.Quant
                  (FStar_SMTEncoding_Term.Forall
                   ,uu____307,uu____308,uu____309,uu____310)
                  ->
                  parse_query_for_split_cases n1 t2
                    (fun x  ->
                       let uu____328 = FStar_SMTEncoding_Util.mkImp (t1, x) in
                       f uu____328)
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.ITE ,uu____329) ->
                  let uu____334 =
                    is_ite_all_the_way n1 t2 FStar_SMTEncoding_Util.mkTrue [] in
                  (match uu____334 with
                   | (b,l,negs) ->
                       (b,
                         (((fun x  ->
                              let uu____379 =
                                FStar_SMTEncoding_Util.mkImp (t1, x) in
                              f uu____379)), l, negs)))
              | uu____380 ->
                  (false,
                    (((fun uu____395  -> FStar_SMTEncoding_Util.mkFalse)),
                      [], FStar_SMTEncoding_Util.mkFalse)) in
            r
        | FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE ,uu____396)
            ->
            let uu____401 =
              is_ite_all_the_way n1 t FStar_SMTEncoding_Util.mkTrue [] in
            (match uu____401 with | (b,l,negs) -> (b, (f, l, negs)))
        | uu____445 ->
            (false,
              (((fun uu____460  -> FStar_SMTEncoding_Util.mkFalse)), [],
                FStar_SMTEncoding_Util.mkFalse))
let strip_not: FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term =
  fun t  ->
    match t.FStar_SMTEncoding_Term.tm with
    | FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Not ,hd1::uu____465)
        -> hd1
    | uu____470 -> t
let handle_query:
  (FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.term
                                                                Prims.list,
    FStar_SMTEncoding_Term.term) FStar_Pervasives_Native.tuple3 ->
    (FStar_SMTEncoding_Term.decl -> Prims.unit) -> Prims.unit
  =
  fun uu____489  ->
    fun check  ->
      match uu____489 with
      | (f,l,negs) -> failwith "SplitQueryCases is not currently supported"