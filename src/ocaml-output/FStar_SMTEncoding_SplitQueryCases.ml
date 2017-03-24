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
                      let uu____48 = FStar_SMTEncoding_Util.mkITE (g, t1, x) in
                      f uu____48)
             | FStar_SMTEncoding_Term.FreeV uu____49 ->
                 let uu____52 = f FStar_SMTEncoding_Util.mkTrue in
                 (true, uu____52, negs, t)
             | uu____53 ->
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
          then Prims.raise FStar_Util.Impos
          else
            (match t.FStar_SMTEncoding_Term.tm with
             | FStar_SMTEncoding_Term.FreeV uu____89 ->
                 let uu____92 =
                   let uu____93 =
                     let uu____96 = FStar_SMTEncoding_Util.mkNot t in
                     (negs, uu____96) in
                   FStar_SMTEncoding_Util.mkAnd uu____93 in
                 (true, l, uu____92)
             | uu____98 ->
                 let uu____99 = get_next_n_ite n1 t negs (fun x  -> x) in
                 (match uu____99 with
                  | (b,t1,negs',rest) ->
                      if b
                      then
                        let uu____117 =
                          let uu____119 =
                            FStar_SMTEncoding_Util.mkImp (negs, t1) in
                          uu____119 :: l in
                        is_ite_all_the_way n1 rest negs' uu____117
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
                  (FStar_SMTEncoding_Term.ITE ,uu____214) ->
                  let uu____217 =
                    is_ite_all_the_way n1 t2 FStar_SMTEncoding_Util.mkTrue [] in
                  (match uu____217 with
                   | (b,l,negs) ->
                       (b,
                         (((fun x  ->
                              let uu____245 =
                                FStar_SMTEncoding_Util.mkImp (t1, x) in
                              f uu____245)), l, negs)))
              | uu____246 ->
                  (false,
                    (((fun uu____256  -> FStar_SMTEncoding_Util.mkFalse)),
                      [], FStar_SMTEncoding_Util.mkFalse)) in
            r
        | FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE ,uu____257)
            ->
            let uu____260 =
              is_ite_all_the_way n1 t FStar_SMTEncoding_Util.mkTrue [] in
            (match uu____260 with | (b,l,negs) -> (b, (f, l, negs)))
        | uu____287 ->
            (false,
              (((fun uu____297  -> FStar_SMTEncoding_Util.mkFalse)), [],
                FStar_SMTEncoding_Util.mkFalse))
let strip_not: FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term =
  fun t  ->
    match t.FStar_SMTEncoding_Term.tm with
    | FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Not ,hd1::uu____302)
        -> hd1
    | uu____305 -> t
let rec check_split_cases:
  (FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term) ->
    FStar_SMTEncoding_Term.term Prims.list ->
      (FStar_SMTEncoding_Term.decl -> Prims.unit) -> Prims.unit
  =
  fun f  ->
    fun l  ->
      fun check  ->
        FStar_List.iter
          (fun t  ->
             let uu____328 =
               let uu____329 =
                 let uu____334 =
                   let uu____335 = f t in
                   FStar_SMTEncoding_Util.mkNot uu____335 in
                 (uu____334, None, None) in
               FStar_SMTEncoding_Term.Assume uu____329 in
             check uu____328) (FStar_List.rev l)
let check_exhaustiveness:
  (FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term) ->
    FStar_SMTEncoding_Term.term ->
      (FStar_SMTEncoding_Term.decl -> Prims.unit) -> Prims.unit
  =
  fun f  ->
    fun negs  ->
      fun check  ->
        let uu____357 =
          let uu____358 =
            let uu____363 =
              let uu____364 =
                let uu____365 = FStar_SMTEncoding_Util.mkNot negs in
                f uu____365 in
              FStar_SMTEncoding_Util.mkNot uu____364 in
            (uu____363, None, None) in
          FStar_SMTEncoding_Term.Assume uu____358 in
        check uu____357
let can_handle_query:
  Prims.int ->
    FStar_SMTEncoding_Term.decl ->
      (Prims.bool*
        ((FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term)*
        FStar_SMTEncoding_Term.term Prims.list* FStar_SMTEncoding_Term.term))
  =
  fun n1  ->
    fun q  ->
      match q with
      | FStar_SMTEncoding_Term.Assume (q',uu____399,uu____400) ->
          let uu____403 = strip_not q' in
          parse_query_for_split_cases n1 uu____403 (fun x  -> x)
      | uu____405 ->
          (false, (((fun x  -> x)), [], FStar_SMTEncoding_Util.mkFalse))
let handle_query:
  ((FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term)*
    FStar_SMTEncoding_Term.term Prims.list* FStar_SMTEncoding_Term.term) ->
    (FStar_SMTEncoding_Term.decl -> Prims.unit) -> Prims.unit
  =
  fun uu____430  ->
    fun check  ->
      match uu____430 with
      | (f,l,negs) ->
          (check_split_cases f l check; check_exhaustiveness f negs check)