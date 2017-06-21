open Prims
let rec get_next_n_ite:
  Prims.int ->
    FStar_SMTEncoding_Term.term ->
      FStar_SMTEncoding_Term.term ->
        (FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term) ->
          (Prims.bool* FStar_SMTEncoding_Term.term*
            FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.term)
  =
  fun n1  ->
    fun t  ->
      fun negs  ->
        fun f  ->
          if n1 <= (Prims.parse_int "0")
          then
<<<<<<< HEAD
            let uu____26 = f FStar_SMTEncoding_Util.mkTrue in
            (true, uu____26, negs, t)
          else
            (match t.FStar_SMTEncoding_Term.tm with
             | FStar_SMTEncoding_Term.App
                 (FStar_SMTEncoding_Term.ITE ,g::t1::e::uu____35) ->
                 let uu____38 =
                   let uu____39 =
                     let uu____42 = FStar_SMTEncoding_Util.mkNot g in
                     (negs, uu____42) in
                   FStar_SMTEncoding_Util.mkAnd uu____39 in
                 get_next_n_ite (n1 - (Prims.parse_int "1")) e uu____38
                   (fun x  ->
                      let uu____46 = FStar_SMTEncoding_Util.mkITE (g, t1, x) in
                      f uu____46)
             | FStar_SMTEncoding_Term.FreeV uu____47 ->
                 let uu____50 = f FStar_SMTEncoding_Util.mkTrue in
                 (true, uu____50, negs, t)
             | uu____51 ->
=======
            let uu____34 = f FStar_SMTEncoding_Util.mkTrue in
            (true, uu____34, negs, t)
          else
            (match t.FStar_SMTEncoding_Term.tm with
             | FStar_SMTEncoding_Term.App
                 (FStar_SMTEncoding_Term.ITE ,g::t1::e::uu____43) ->
                 let uu____46 =
                   let uu____47 =
                     let uu____50 = FStar_SMTEncoding_Util.mkNot g in
                     (negs, uu____50) in
                   FStar_SMTEncoding_Util.mkAnd uu____47 in
                 get_next_n_ite (n1 - (Prims.parse_int "1")) e uu____46
                   (fun x  ->
                      let uu____52 = FStar_SMTEncoding_Util.mkITE (g, t1, x) in
                      f uu____52)
             | FStar_SMTEncoding_Term.FreeV uu____53 ->
                 let uu____56 = f FStar_SMTEncoding_Util.mkTrue in
                 (true, uu____56, negs, t)
             | uu____57 ->
>>>>>>> origin/guido_tactics
                 (false, FStar_SMTEncoding_Util.mkFalse,
                   FStar_SMTEncoding_Util.mkFalse,
                   FStar_SMTEncoding_Util.mkFalse))
let rec is_ite_all_the_way:
  Prims.int ->
    FStar_SMTEncoding_Term.term ->
      FStar_SMTEncoding_Term.term ->
        FStar_SMTEncoding_Term.term Prims.list ->
          (Prims.bool* FStar_SMTEncoding_Term.term Prims.list*
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
<<<<<<< HEAD
             | FStar_SMTEncoding_Term.FreeV uu____83 ->
                 let uu____86 =
                   let uu____87 =
                     let uu____90 = FStar_SMTEncoding_Util.mkNot t in
                     (negs, uu____90) in
                   FStar_SMTEncoding_Util.mkAnd uu____87 in
                 (true, l, uu____86)
             | uu____92 ->
                 let uu____93 = get_next_n_ite n1 t negs (fun x  -> x) in
                 (match uu____93 with
                  | (b,t1,negs',rest) ->
                      if b
                      then
                        let uu____112 =
                          let uu____114 =
                            FStar_SMTEncoding_Util.mkImp (negs, t1) in
                          uu____114 :: l in
                        is_ite_all_the_way n1 rest negs' uu____112
=======
             | FStar_SMTEncoding_Term.FreeV uu____97 ->
                 let uu____100 =
                   let uu____101 =
                     let uu____104 = FStar_SMTEncoding_Util.mkNot t in
                     (negs, uu____104) in
                   FStar_SMTEncoding_Util.mkAnd uu____101 in
                 (true, l, uu____100)
             | uu____106 ->
                 let uu____107 = get_next_n_ite n1 t negs (fun x  -> x) in
                 (match uu____107 with
                  | (b,t1,negs',rest) ->
                      if b
                      then
                        let uu____125 =
                          let uu____127 =
                            FStar_SMTEncoding_Util.mkImp (negs, t1) in
                          uu____127 :: l in
                        is_ite_all_the_way n1 rest negs' uu____125
>>>>>>> origin/guido_tactics
                      else (false, [], FStar_SMTEncoding_Util.mkFalse)))
let rec parse_query_for_split_cases:
  Prims.int ->
    FStar_SMTEncoding_Term.term ->
      (FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term) ->
        (Prims.bool*
          ((FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term)*
          FStar_SMTEncoding_Term.term Prims.list*
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
<<<<<<< HEAD
                 let uu____162 =
                   FStar_SMTEncoding_Util.mkForall'' (l, opt, l', x) in
                 f uu____162)
        | FStar_SMTEncoding_Term.App
            (FStar_SMTEncoding_Term.Imp ,t1::t2::uu____169) ->
=======
                 let uu____184 =
                   FStar_SMTEncoding_Util.mkForall'' (l, opt, l', x) in
                 f uu____184)
        | FStar_SMTEncoding_Term.App
            (FStar_SMTEncoding_Term.Imp ,t1::t2::uu____191) ->
>>>>>>> origin/guido_tactics
            let r =
              match t2.FStar_SMTEncoding_Term.tm with
              | FStar_SMTEncoding_Term.Quant
                  (FStar_SMTEncoding_Term.Forall
<<<<<<< HEAD
                   ,uu____189,uu____190,uu____191,uu____192)
                  ->
                  parse_query_for_split_cases n1 t2
                    (fun x  ->
                       let uu____204 = FStar_SMTEncoding_Util.mkImp (t1, x) in
                       f uu____204)
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.ITE ,uu____205) ->
                  let uu____208 =
                    is_ite_all_the_way n1 t2 FStar_SMTEncoding_Util.mkTrue [] in
                  (match uu____208 with
                   | (b,l,negs) ->
                       (b,
                         (((fun x  ->
                              let uu____238 =
                                FStar_SMTEncoding_Util.mkImp (t1, x) in
                              f uu____238)), l, negs)))
              | uu____239 ->
                  (false,
                    (((fun uu____250  -> FStar_SMTEncoding_Util.mkFalse)),
                      [], FStar_SMTEncoding_Util.mkFalse)) in
            r
        | FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE ,uu____251)
            ->
            let uu____254 =
              is_ite_all_the_way n1 t FStar_SMTEncoding_Util.mkTrue [] in
            (match uu____254 with | (b,l,negs) -> (b, (f, l, negs)))
        | uu____281 ->
            (false,
              (((fun uu____292  -> FStar_SMTEncoding_Util.mkFalse)), [],
=======
                   ,uu____211,uu____212,uu____213,uu____214)
                  ->
                  parse_query_for_split_cases n1 t2
                    (fun x  ->
                       let uu____224 = FStar_SMTEncoding_Util.mkImp (t1, x) in
                       f uu____224)
              | FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.ITE ,uu____225) ->
                  let uu____228 =
                    is_ite_all_the_way n1 t2 FStar_SMTEncoding_Util.mkTrue [] in
                  (match uu____228 with
                   | (b,l,negs) ->
                       (b,
                         (((fun x  ->
                              let uu____256 =
                                FStar_SMTEncoding_Util.mkImp (t1, x) in
                              f uu____256)), l, negs)))
              | uu____257 ->
                  (false,
                    (((fun uu____267  -> FStar_SMTEncoding_Util.mkFalse)),
                      [], FStar_SMTEncoding_Util.mkFalse)) in
            r
        | FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE ,uu____268)
            ->
            let uu____271 =
              is_ite_all_the_way n1 t FStar_SMTEncoding_Util.mkTrue [] in
            (match uu____271 with | (b,l,negs) -> (b, (f, l, negs)))
        | uu____298 ->
            (false,
              (((fun uu____308  -> FStar_SMTEncoding_Util.mkFalse)), [],
>>>>>>> origin/guido_tactics
                FStar_SMTEncoding_Util.mkFalse))
let strip_not: FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term =
  fun t  ->
    match t.FStar_SMTEncoding_Term.tm with
<<<<<<< HEAD
    | FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Not ,hd1::uu____297)
        -> hd1
    | uu____300 -> t
=======
    | FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Not ,hd1::uu____314)
        -> hd1
    | uu____317 -> t
>>>>>>> origin/guido_tactics
let handle_query:
  ((FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term)*
    FStar_SMTEncoding_Term.term Prims.list* FStar_SMTEncoding_Term.term) ->
    (FStar_SMTEncoding_Term.decl -> Prims.unit) -> Prims.unit
  =
<<<<<<< HEAD
  fun uu____315  ->
    fun check  ->
      match uu____315 with
=======
  fun uu____334  ->
    fun check  ->
      match uu____334 with
>>>>>>> origin/guido_tactics
      | (f,l,negs) -> failwith "SplitQueryCases is not currently supported"