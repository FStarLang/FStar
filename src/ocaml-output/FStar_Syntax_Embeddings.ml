open Prims
type norm_cb =
  (FStar_Ident.lid,FStar_Syntax_Syntax.term) FStar_Util.either ->
    FStar_Syntax_Syntax.term
let (id_norm_cb : norm_cb) =
  fun uu___0_16  ->
    match uu___0_16 with
    | FStar_Util.Inr x -> x
    | FStar_Util.Inl l ->
        let uu____23 =
          FStar_Syntax_Syntax.lid_as_fv l
            FStar_Syntax_Syntax.delta_equational FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.fv_to_tm uu____23
  
exception Embedding_failure 
let (uu___is_Embedding_failure : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Embedding_failure  -> true | uu____33 -> false
  
exception Unembedding_failure 
let (uu___is_Unembedding_failure : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unembedding_failure  -> true | uu____44 -> false
  
type shadow_term =
  FStar_Syntax_Syntax.term FStar_Thunk.t FStar_Pervasives_Native.option
let (map_shadow :
  shadow_term ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> shadow_term)
  = fun s  -> fun f  -> FStar_Util.map_opt s (FStar_Thunk.map f) 
let (force_shadow :
  shadow_term -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option) =
  fun s  -> FStar_Util.map_opt s FStar_Thunk.force 
type embed_t =
  FStar_Range.range -> shadow_term -> norm_cb -> FStar_Syntax_Syntax.term
type 'a unembed_t =
  Prims.bool -> norm_cb -> 'a FStar_Pervasives_Native.option
type 'a raw_embedder = 'a -> embed_t
type 'a raw_unembedder = FStar_Syntax_Syntax.term -> 'a unembed_t
type 'a printer = 'a -> Prims.string
type 'a embedding =
  {
  em: 'a -> embed_t ;
  un: FStar_Syntax_Syntax.term -> 'a unembed_t ;
  typ: FStar_Syntax_Syntax.typ ;
  print: 'a printer ;
  emb_typ: FStar_Syntax_Syntax.emb_typ }
let __proj__Mkembedding__item__em : 'a . 'a embedding -> 'a -> embed_t =
  fun projectee  ->
    match projectee with | { em; un; typ; print = print7; emb_typ;_} -> em
  
let __proj__Mkembedding__item__un :
  'a . 'a embedding -> FStar_Syntax_Syntax.term -> 'a unembed_t =
  fun projectee  ->
    match projectee with | { em; un; typ; print = print7; emb_typ;_} -> un
  
let __proj__Mkembedding__item__typ :
  'a . 'a embedding -> FStar_Syntax_Syntax.typ =
  fun projectee  ->
    match projectee with | { em; un; typ; print = print7; emb_typ;_} -> typ
  
let __proj__Mkembedding__item__print : 'a . 'a embedding -> 'a printer =
  fun projectee  ->
    match projectee with
    | { em; un; typ; print = print7; emb_typ;_} -> print7
  
let __proj__Mkembedding__item__emb_typ :
  'a . 'a embedding -> FStar_Syntax_Syntax.emb_typ =
  fun projectee  ->
    match projectee with
    | { em; un; typ; print = print7; emb_typ;_} -> emb_typ
  
let emb_typ_of : 'a . 'a embedding -> FStar_Syntax_Syntax.emb_typ =
  fun e  -> e.emb_typ 
let unknown_printer :
  'Auu____457 . FStar_Syntax_Syntax.term -> 'Auu____457 -> Prims.string =
  fun typ  ->
    fun uu____468  ->
      let uu____469 = FStar_Syntax_Print.term_to_string typ  in
      FStar_Util.format1 "unknown %s" uu____469
  
let (term_as_fv : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.fv) =
  fun t  ->
    let uu____478 =
      let uu____479 = FStar_Syntax_Subst.compress t  in
      uu____479.FStar_Syntax_Syntax.n  in
    match uu____478 with
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv
    | uu____483 ->
        let uu____484 =
          let uu____486 = FStar_Syntax_Print.term_to_string t  in
          FStar_Util.format1 "Embeddings not defined for type %s" uu____486
           in
        failwith uu____484
  
let mk_emb :
  'a .
    'a raw_embedder ->
      'a raw_unembedder -> FStar_Syntax_Syntax.fv -> 'a embedding
  =
  fun em  ->
    fun un  ->
      fun fv  ->
        let typ = FStar_Syntax_Syntax.fv_to_tm fv  in
        let uu____529 =
          let uu____530 =
            let uu____538 =
              let uu____540 = FStar_Syntax_Syntax.lid_of_fv fv  in
              FStar_All.pipe_right uu____540 FStar_Ident.string_of_lid  in
            (uu____538, [])  in
          FStar_Syntax_Syntax.ET_app uu____530  in
        { em; un; typ; print = (unknown_printer typ); emb_typ = uu____529 }
  
let mk_emb_full :
  'a .
    'a raw_embedder ->
      'a raw_unembedder ->
        FStar_Syntax_Syntax.typ ->
          ('a -> Prims.string) -> FStar_Syntax_Syntax.emb_typ -> 'a embedding
  =
  fun em  ->
    fun un  ->
      fun typ  ->
        fun printer  ->
          fun emb_typ  -> { em; un; typ; print = printer; emb_typ }
  
let embed : 'a . 'a embedding -> 'a -> embed_t = fun e  -> fun x  -> e.em x 
let unembed : 'a . 'a embedding -> FStar_Syntax_Syntax.term -> 'a unembed_t =
  fun e  -> fun t  -> e.un t 
let warn_unembed :
  'a .
    'a embedding ->
      FStar_Syntax_Syntax.term ->
        norm_cb -> 'a FStar_Pervasives_Native.option
  =
  fun e  ->
    fun t  -> fun n1  -> let uu____689 = unembed e t  in uu____689 true n1
  
let try_unembed :
  'a .
    'a embedding ->
      FStar_Syntax_Syntax.term ->
        norm_cb -> 'a FStar_Pervasives_Native.option
  =
  fun e  ->
    fun t  -> fun n1  -> let uu____730 = unembed e t  in uu____730 false n1
  
let type_of : 'a . 'a embedding -> FStar_Syntax_Syntax.typ = fun e  -> e.typ 
let set_type : 'a . FStar_Syntax_Syntax.typ -> 'a embedding -> 'a embedding =
  fun ty  ->
    fun e  ->
      let uu___77_777 = e  in
      {
        em = (uu___77_777.em);
        un = (uu___77_777.un);
        typ = ty;
        print = (uu___77_777.print);
        emb_typ = (uu___77_777.emb_typ)
      }
  
let lazy_embed :
  'a .
    'a printer ->
      FStar_Syntax_Syntax.emb_typ ->
        FStar_Range.range ->
          FStar_Syntax_Syntax.term ->
            'a ->
              (unit -> FStar_Syntax_Syntax.term) ->
                FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun pa  ->
    fun et  ->
      fun rng  ->
        fun ta  ->
          fun x  ->
            fun f  ->
              (let uu____840 = FStar_ST.op_Bang FStar_Options.debug_embedding
                  in
               if uu____840
               then
                 let uu____864 = FStar_Syntax_Print.term_to_string ta  in
                 let uu____866 = FStar_Syntax_Print.emb_typ_to_string et  in
                 let uu____868 = pa x  in
                 FStar_Util.print3
                   "Embedding a %s\n\temb_typ=%s\n\tvalue is %s\n" uu____864
                   uu____866 uu____868
               else ());
              (let uu____873 = FStar_ST.op_Bang FStar_Options.eager_embedding
                  in
               if uu____873
               then f ()
               else
                 (let thunk1 = FStar_Thunk.mk f  in
                  let uu____908 =
                    let uu____915 =
                      let uu____916 =
                        let uu____917 = FStar_Dyn.mkdyn x  in
                        {
                          FStar_Syntax_Syntax.blob = uu____917;
                          FStar_Syntax_Syntax.lkind =
                            (FStar_Syntax_Syntax.Lazy_embedding (et, thunk1));
                          FStar_Syntax_Syntax.ltyp = FStar_Syntax_Syntax.tun;
                          FStar_Syntax_Syntax.rng = rng
                        }  in
                      FStar_Syntax_Syntax.Tm_lazy uu____916  in
                    FStar_Syntax_Syntax.mk uu____915  in
                  uu____908 FStar_Pervasives_Native.None rng))
  
let lazy_unembed :
  'a .
    'a printer ->
      FStar_Syntax_Syntax.emb_typ ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.term ->
            (FStar_Syntax_Syntax.term -> 'a FStar_Pervasives_Native.option)
              -> 'a FStar_Pervasives_Native.option
  =
  fun pa  ->
    fun et  ->
      fun x  ->
        fun ta  ->
          fun f  ->
            let x1 = FStar_Syntax_Subst.compress x  in
            match x1.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_lazy
                { FStar_Syntax_Syntax.blob = b;
                  FStar_Syntax_Syntax.lkind =
                    FStar_Syntax_Syntax.Lazy_embedding (et',t);
                  FStar_Syntax_Syntax.ltyp = uu____984;
                  FStar_Syntax_Syntax.rng = uu____985;_}
                ->
                let uu____996 =
                  (et <> et') ||
                    (FStar_ST.op_Bang FStar_Options.eager_embedding)
                   in
                if uu____996
                then
                  let res =
                    let uu____1025 = FStar_Thunk.force t  in f uu____1025  in
                  ((let uu____1029 =
                      FStar_ST.op_Bang FStar_Options.debug_embedding  in
                    if uu____1029
                    then
                      let uu____1053 =
                        FStar_Syntax_Print.emb_typ_to_string et  in
                      let uu____1055 =
                        FStar_Syntax_Print.emb_typ_to_string et'  in
                      let uu____1057 =
                        match res with
                        | FStar_Pervasives_Native.None  -> "None"
                        | FStar_Pervasives_Native.Some x2 ->
                            let uu____1062 = pa x2  in
                            Prims.op_Hat "Some " uu____1062
                         in
                      FStar_Util.print3
                        "Unembed cancellation failed\n\t%s <> %s\nvalue is %s\n"
                        uu____1053 uu____1055 uu____1057
                    else ());
                   res)
                else
                  (let a = FStar_Dyn.undyn b  in
                   (let uu____1072 =
                      FStar_ST.op_Bang FStar_Options.debug_embedding  in
                    if uu____1072
                    then
                      let uu____1096 =
                        FStar_Syntax_Print.emb_typ_to_string et  in
                      let uu____1098 = pa a  in
                      FStar_Util.print2
                        "Unembed cancelled for %s\n\tvalue is %s\n"
                        uu____1096 uu____1098
                    else ());
                   FStar_Pervasives_Native.Some a)
            | uu____1103 ->
                let aopt = f x1  in
                ((let uu____1108 =
                    FStar_ST.op_Bang FStar_Options.debug_embedding  in
                  if uu____1108
                  then
                    let uu____1132 = FStar_Syntax_Print.emb_typ_to_string et
                       in
                    let uu____1134 = FStar_Syntax_Print.term_to_string x1  in
                    let uu____1136 =
                      match aopt with
                      | FStar_Pervasives_Native.None  -> "None"
                      | FStar_Pervasives_Native.Some a ->
                          let uu____1141 = pa a  in
                          Prims.op_Hat "Some " uu____1141
                       in
                    FStar_Util.print3
                      "Unembedding:\n\temb_typ=%s\n\tterm is %s\n\tvalue is %s\n"
                      uu____1132 uu____1134 uu____1136
                  else ());
                 aopt)
  
let (mk_any_emb :
  FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term embedding) =
  fun typ  ->
    let em t _r _topt _norm =
      (let uu____1179 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
       if uu____1179
       then
         let uu____1203 = unknown_printer typ t  in
         FStar_Util.print1 "Embedding abstract: %s\n" uu____1203
       else ());
      t  in
    let un t _w _n =
      (let uu____1231 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
       if uu____1231
       then
         let uu____1255 = unknown_printer typ t  in
         FStar_Util.print1 "Unembedding abstract: %s\n" uu____1255
       else ());
      FStar_Pervasives_Native.Some t  in
    mk_emb_full em un typ (unknown_printer typ)
      FStar_Syntax_Syntax.ET_abstract
  
let (e_any : FStar_Syntax_Syntax.term embedding) =
  let em t _r _topt _norm = t  in
  let un t _w _n = FStar_Pervasives_Native.Some t  in
  let uu____1308 =
    let uu____1309 =
      let uu____1317 =
        FStar_All.pipe_right FStar_Parser_Const.term_lid
          FStar_Ident.string_of_lid
         in
      (uu____1317, [])  in
    FStar_Syntax_Syntax.ET_app uu____1309  in
  mk_emb_full em un FStar_Syntax_Syntax.t_term
    FStar_Syntax_Print.term_to_string uu____1308
  
let (e_unit : unit embedding) =
  let em u rng _topt _norm =
    let uu___151_1349 = FStar_Syntax_Util.exp_unit  in
    {
      FStar_Syntax_Syntax.n = (uu___151_1349.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___151_1349.FStar_Syntax_Syntax.vars)
    }  in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unascribe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit ) ->
        FStar_Pervasives_Native.Some ()
    | uu____1377 ->
        (if w
         then
           (let uu____1380 =
              let uu____1386 =
                let uu____1388 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded unit: %s" uu____1388  in
              (FStar_Errors.Warning_NotEmbedded, uu____1386)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____1380)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____1394 =
    let uu____1395 =
      let uu____1403 =
        FStar_All.pipe_right FStar_Parser_Const.unit_lid
          FStar_Ident.string_of_lid
         in
      (uu____1403, [])  in
    FStar_Syntax_Syntax.ET_app uu____1395  in
  mk_emb_full em un FStar_Syntax_Syntax.t_unit (fun uu____1410  -> "()")
    uu____1394
  
let (e_bool : Prims.bool embedding) =
  let em b rng _topt _norm =
    let t =
      if b
      then FStar_Syntax_Util.exp_true_bool
      else FStar_Syntax_Util.exp_false_bool  in
    let uu___171_1449 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___171_1449.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___171_1449.FStar_Syntax_Syntax.vars)
    }  in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) ->
        FStar_Pervasives_Native.Some b
    | uu____1485 ->
        (if w
         then
           (let uu____1488 =
              let uu____1494 =
                let uu____1496 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded bool: %s" uu____1496  in
              (FStar_Errors.Warning_NotEmbedded, uu____1494)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____1488)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____1503 =
    let uu____1504 =
      let uu____1512 =
        FStar_All.pipe_right FStar_Parser_Const.bool_lid
          FStar_Ident.string_of_lid
         in
      (uu____1512, [])  in
    FStar_Syntax_Syntax.ET_app uu____1504  in
  mk_emb_full em un FStar_Syntax_Syntax.t_bool FStar_Util.string_of_bool
    uu____1503
  
let (e_char : FStar_Char.char embedding) =
  let em c rng _topt _norm =
    let t = FStar_Syntax_Util.exp_char c  in
    let uu___190_1549 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___190_1549.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___190_1549.FStar_Syntax_Syntax.vars)
    }  in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c) ->
        FStar_Pervasives_Native.Some c
    | uu____1583 ->
        (if w
         then
           (let uu____1586 =
              let uu____1592 =
                let uu____1594 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded char: %s" uu____1594  in
              (FStar_Errors.Warning_NotEmbedded, uu____1592)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____1586)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____1601 =
    let uu____1602 =
      let uu____1610 =
        FStar_All.pipe_right FStar_Parser_Const.char_lid
          FStar_Ident.string_of_lid
         in
      (uu____1610, [])  in
    FStar_Syntax_Syntax.ET_app uu____1602  in
  mk_emb_full em un FStar_Syntax_Syntax.t_char FStar_Util.string_of_char
    uu____1601
  
let (e_int : FStar_BigInt.t embedding) =
  let t_int1 = FStar_Syntax_Util.fvar_const FStar_Parser_Const.int_lid  in
  let emb_t_int =
    let uu____1622 =
      let uu____1630 =
        FStar_All.pipe_right FStar_Parser_Const.int_lid
          FStar_Ident.string_of_lid
         in
      (uu____1630, [])  in
    FStar_Syntax_Syntax.ET_app uu____1622  in
  let em i rng _topt _norm =
    lazy_embed FStar_BigInt.string_of_big_int emb_t_int rng t_int1 i
      (fun uu____1661  ->
         let uu____1662 = FStar_BigInt.string_of_big_int i  in
         FStar_Syntax_Util.exp_int uu____1662)
     in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    lazy_unembed FStar_BigInt.string_of_big_int emb_t_int t t_int1
      (fun t1  ->
         match t1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
             (s,uu____1697)) ->
             let uu____1712 = FStar_BigInt.big_int_of_string s  in
             FStar_Pervasives_Native.Some uu____1712
         | uu____1713 ->
             (if w
              then
                (let uu____1716 =
                   let uu____1722 =
                     let uu____1724 = FStar_Syntax_Print.term_to_string t0
                        in
                     FStar_Util.format1 "Not an embedded int: %s" uu____1724
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____1722)  in
                 FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____1716)
              else ();
              FStar_Pervasives_Native.None))
     in
  mk_emb_full em un FStar_Syntax_Syntax.t_int FStar_BigInt.string_of_big_int
    emb_t_int
  
let (e_string : Prims.string embedding) =
  let emb_t_string =
    let uu____1735 =
      let uu____1743 =
        FStar_All.pipe_right FStar_Parser_Const.string_lid
          FStar_Ident.string_of_lid
         in
      (uu____1743, [])  in
    FStar_Syntax_Syntax.ET_app uu____1735  in
  let em s rng _topt _norm =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, rng)))
      FStar_Pervasives_Native.None rng
     in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
        (s,uu____1806)) -> FStar_Pervasives_Native.Some s
    | uu____1810 ->
        (if w
         then
           (let uu____1813 =
              let uu____1819 =
                let uu____1821 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded string: %s" uu____1821
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____1819)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____1813)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb_full em un FStar_Syntax_Syntax.t_string
    (fun x  -> Prims.op_Hat "\"" (Prims.op_Hat x "\"")) emb_t_string
  
let e_option :
  'a . 'a embedding -> 'a FStar_Pervasives_Native.option embedding =
  fun ea  ->
    let t_option_a =
      let t_opt = FStar_Syntax_Util.fvar_const FStar_Parser_Const.option_lid
         in
      let uu____1857 =
        let uu____1862 =
          let uu____1863 = FStar_Syntax_Syntax.as_arg ea.typ  in [uu____1863]
           in
        FStar_Syntax_Syntax.mk_Tm_app t_opt uu____1862  in
      uu____1857 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
    let emb_t_option_a =
      let uu____1889 =
        let uu____1897 =
          FStar_All.pipe_right FStar_Parser_Const.option_lid
            FStar_Ident.string_of_lid
           in
        (uu____1897, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____1889  in
    let printer uu___1_1911 =
      match uu___1_1911 with
      | FStar_Pervasives_Native.None  -> "None"
      | FStar_Pervasives_Native.Some x ->
          let uu____1917 =
            let uu____1919 = ea.print x  in Prims.op_Hat uu____1919 ")"  in
          Prims.op_Hat "(Some " uu____1917
       in
    let em o rng topt norm1 =
      lazy_embed printer emb_t_option_a rng t_option_a o
        (fun uu____1954  ->
           match o with
           | FStar_Pervasives_Native.None  ->
               let uu____1955 =
                 let uu____1960 =
                   let uu____1961 =
                     FStar_Syntax_Syntax.tdataconstr
                       FStar_Parser_Const.none_lid
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____1961
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 let uu____1962 =
                   let uu____1963 =
                     let uu____1972 = type_of ea  in
                     FStar_Syntax_Syntax.iarg uu____1972  in
                   [uu____1963]  in
                 FStar_Syntax_Syntax.mk_Tm_app uu____1960 uu____1962  in
               uu____1955 FStar_Pervasives_Native.None rng
           | FStar_Pervasives_Native.Some a ->
               let shadow_a =
                 map_shadow topt
                   (fun t  ->
                      let v1 = FStar_Ident.mk_ident ("v", rng)  in
                      let some_v =
                        FStar_Syntax_Util.mk_field_projector_name_from_ident
                          FStar_Parser_Const.some_lid v1
                         in
                      let some_v_tm =
                        let uu____2002 =
                          FStar_Syntax_Syntax.lid_as_fv some_v
                            FStar_Syntax_Syntax.delta_equational
                            FStar_Pervasives_Native.None
                           in
                        FStar_Syntax_Syntax.fv_to_tm uu____2002  in
                      let uu____2003 =
                        let uu____2008 =
                          FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm
                            [FStar_Syntax_Syntax.U_zero]
                           in
                        let uu____2009 =
                          let uu____2010 =
                            let uu____2019 = type_of ea  in
                            FStar_Syntax_Syntax.iarg uu____2019  in
                          let uu____2020 =
                            let uu____2031 = FStar_Syntax_Syntax.as_arg t  in
                            [uu____2031]  in
                          uu____2010 :: uu____2020  in
                        FStar_Syntax_Syntax.mk_Tm_app uu____2008 uu____2009
                         in
                      uu____2003 FStar_Pervasives_Native.None rng)
                  in
               let uu____2064 =
                 let uu____2069 =
                   let uu____2070 =
                     FStar_Syntax_Syntax.tdataconstr
                       FStar_Parser_Const.some_lid
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____2070
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 let uu____2071 =
                   let uu____2072 =
                     let uu____2081 = type_of ea  in
                     FStar_Syntax_Syntax.iarg uu____2081  in
                   let uu____2082 =
                     let uu____2093 =
                       let uu____2102 =
                         let uu____2103 = embed ea a  in
                         uu____2103 rng shadow_a norm1  in
                       FStar_Syntax_Syntax.as_arg uu____2102  in
                     [uu____2093]  in
                   uu____2072 :: uu____2082  in
                 FStar_Syntax_Syntax.mk_Tm_app uu____2069 uu____2071  in
               uu____2064 FStar_Pervasives_Native.None rng)
       in
    let un t0 w norm1 =
      let t = FStar_Syntax_Util.unmeta_safe t0  in
      lazy_unembed printer emb_t_option_a t t_option_a
        (fun t1  ->
           let uu____2173 = FStar_Syntax_Util.head_and_args' t1  in
           match uu____2173 with
           | (hd1,args) ->
               let uu____2214 =
                 let uu____2229 =
                   let uu____2230 = FStar_Syntax_Util.un_uinst hd1  in
                   uu____2230.FStar_Syntax_Syntax.n  in
                 (uu____2229, args)  in
               (match uu____2214 with
                | (FStar_Syntax_Syntax.Tm_fvar fv,uu____2248) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.none_lid
                    ->
                    FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,uu____2272::(a,uu____2274)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.some_lid
                    ->
                    let uu____2325 =
                      let uu____2328 = unembed ea a  in uu____2328 w norm1
                       in
                    FStar_Util.bind_opt uu____2325
                      (fun a1  ->
                         FStar_Pervasives_Native.Some
                           (FStar_Pervasives_Native.Some a1))
                | uu____2341 ->
                    (if w
                     then
                       (let uu____2358 =
                          let uu____2364 =
                            let uu____2366 =
                              FStar_Syntax_Print.term_to_string t0  in
                            FStar_Util.format1 "Not an embedded option: %s"
                              uu____2366
                             in
                          (FStar_Errors.Warning_NotEmbedded, uu____2364)  in
                        FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                          uu____2358)
                     else ();
                     FStar_Pervasives_Native.None)))
       in
    let uu____2374 =
      let uu____2375 = type_of ea  in
      FStar_Syntax_Syntax.t_option_of uu____2375  in
    mk_emb_full em un uu____2374 printer emb_t_option_a
  
let e_tuple2 : 'a 'b . 'a embedding -> 'b embedding -> ('a * 'b) embedding =
  fun ea  ->
    fun eb  ->
      let t_pair_a_b =
        let t_tup2 =
          FStar_Syntax_Util.fvar_const FStar_Parser_Const.lid_tuple2  in
        let uu____2417 =
          let uu____2422 =
            let uu____2423 = FStar_Syntax_Syntax.as_arg ea.typ  in
            let uu____2432 =
              let uu____2443 = FStar_Syntax_Syntax.as_arg eb.typ  in
              [uu____2443]  in
            uu____2423 :: uu____2432  in
          FStar_Syntax_Syntax.mk_Tm_app t_tup2 uu____2422  in
        uu____2417 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
      let emb_t_pair_a_b =
        let uu____2477 =
          let uu____2485 =
            FStar_All.pipe_right FStar_Parser_Const.lid_tuple2
              FStar_Ident.string_of_lid
             in
          (uu____2485, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____2477  in
      let printer uu____2501 =
        match uu____2501 with
        | (x,y) ->
            let uu____2509 = ea.print x  in
            let uu____2511 = eb.print y  in
            FStar_Util.format2 "(%s, %s)" uu____2509 uu____2511
         in
      let em x rng topt norm1 =
        lazy_embed printer emb_t_pair_a_b rng t_pair_a_b x
          (fun uu____2554  ->
             let proj i ab =
               let proj_1 =
                 let uu____2571 =
                   FStar_Parser_Const.mk_tuple_data_lid (Prims.of_int (2))
                     rng
                    in
                 let uu____2573 =
                   FStar_Syntax_Syntax.null_bv FStar_Syntax_Syntax.tun  in
                 FStar_Syntax_Util.mk_field_projector_name uu____2571
                   uu____2573 i
                  in
               let proj_1_tm =
                 let uu____2575 =
                   FStar_Syntax_Syntax.lid_as_fv proj_1
                     FStar_Syntax_Syntax.delta_equational
                     FStar_Pervasives_Native.None
                    in
                 FStar_Syntax_Syntax.fv_to_tm uu____2575  in
               let uu____2576 =
                 let uu____2581 =
                   FStar_Syntax_Syntax.mk_Tm_uinst proj_1_tm
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 let uu____2582 =
                   let uu____2583 =
                     let uu____2592 = type_of ea  in
                     FStar_Syntax_Syntax.iarg uu____2592  in
                   let uu____2593 =
                     let uu____2604 =
                       let uu____2613 = type_of eb  in
                       FStar_Syntax_Syntax.iarg uu____2613  in
                     let uu____2614 =
                       let uu____2625 = FStar_Syntax_Syntax.as_arg ab  in
                       [uu____2625]  in
                     uu____2604 :: uu____2614  in
                   uu____2583 :: uu____2593  in
                 FStar_Syntax_Syntax.mk_Tm_app uu____2581 uu____2582  in
               uu____2576 FStar_Pervasives_Native.None rng  in
             let shadow_a = map_shadow topt (proj Prims.int_one)  in
             let shadow_b = map_shadow topt (proj (Prims.of_int (2)))  in
             let uu____2670 =
               let uu____2675 =
                 let uu____2676 =
                   FStar_Syntax_Syntax.tdataconstr
                     FStar_Parser_Const.lid_Mktuple2
                    in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu____2676
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                  in
               let uu____2677 =
                 let uu____2678 =
                   let uu____2687 = type_of ea  in
                   FStar_Syntax_Syntax.iarg uu____2687  in
                 let uu____2688 =
                   let uu____2699 =
                     let uu____2708 = type_of eb  in
                     FStar_Syntax_Syntax.iarg uu____2708  in
                   let uu____2709 =
                     let uu____2720 =
                       let uu____2729 =
                         let uu____2730 =
                           embed ea (FStar_Pervasives_Native.fst x)  in
                         uu____2730 rng shadow_a norm1  in
                       FStar_Syntax_Syntax.as_arg uu____2729  in
                     let uu____2737 =
                       let uu____2748 =
                         let uu____2757 =
                           let uu____2758 =
                             embed eb (FStar_Pervasives_Native.snd x)  in
                           uu____2758 rng shadow_b norm1  in
                         FStar_Syntax_Syntax.as_arg uu____2757  in
                       [uu____2748]  in
                     uu____2720 :: uu____2737  in
                   uu____2699 :: uu____2709  in
                 uu____2678 :: uu____2688  in
               FStar_Syntax_Syntax.mk_Tm_app uu____2675 uu____2677  in
             uu____2670 FStar_Pervasives_Native.None rng)
         in
      let un t0 w norm1 =
        let t = FStar_Syntax_Util.unmeta_safe t0  in
        lazy_unembed printer emb_t_pair_a_b t t_pair_a_b
          (fun t1  ->
             let uu____2856 = FStar_Syntax_Util.head_and_args' t1  in
             match uu____2856 with
             | (hd1,args) ->
                 let uu____2899 =
                   let uu____2912 =
                     let uu____2913 = FStar_Syntax_Util.un_uinst hd1  in
                     uu____2913.FStar_Syntax_Syntax.n  in
                   (uu____2912, args)  in
                 (match uu____2899 with
                  | (FStar_Syntax_Syntax.Tm_fvar
                     fv,uu____2931::uu____2932::(a,uu____2934)::(b,uu____2936)::[])
                      when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.lid_Mktuple2
                      ->
                      let uu____2995 =
                        let uu____2998 = unembed ea a  in uu____2998 w norm1
                         in
                      FStar_Util.bind_opt uu____2995
                        (fun a1  ->
                           let uu____3012 =
                             let uu____3015 = unembed eb b  in
                             uu____3015 w norm1  in
                           FStar_Util.bind_opt uu____3012
                             (fun b1  ->
                                FStar_Pervasives_Native.Some (a1, b1)))
                  | uu____3032 ->
                      (if w
                       then
                         (let uu____3047 =
                            let uu____3053 =
                              let uu____3055 =
                                FStar_Syntax_Print.term_to_string t0  in
                              FStar_Util.format1 "Not an embedded pair: %s"
                                uu____3055
                               in
                            (FStar_Errors.Warning_NotEmbedded, uu____3053)
                             in
                          FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                            uu____3047)
                       else ();
                       FStar_Pervasives_Native.None)))
         in
      let uu____3065 =
        let uu____3066 = type_of ea  in
        let uu____3067 = type_of eb  in
        FStar_Syntax_Syntax.t_tuple2_of uu____3066 uu____3067  in
      mk_emb_full em un uu____3065 printer emb_t_pair_a_b
  
let e_either :
  'a 'b . 'a embedding -> 'b embedding -> ('a,'b) FStar_Util.either embedding
  =
  fun ea  ->
    fun eb  ->
      let t_sum_a_b =
        let t_either =
          FStar_Syntax_Util.fvar_const FStar_Parser_Const.either_lid  in
        let uu____3111 =
          let uu____3116 =
            let uu____3117 = FStar_Syntax_Syntax.as_arg ea.typ  in
            let uu____3126 =
              let uu____3137 = FStar_Syntax_Syntax.as_arg eb.typ  in
              [uu____3137]  in
            uu____3117 :: uu____3126  in
          FStar_Syntax_Syntax.mk_Tm_app t_either uu____3116  in
        uu____3111 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
      let emb_t_sum_a_b =
        let uu____3171 =
          let uu____3179 =
            FStar_All.pipe_right FStar_Parser_Const.either_lid
              FStar_Ident.string_of_lid
             in
          (uu____3179, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____3171  in
      let printer s =
        match s with
        | FStar_Util.Inl a ->
            let uu____3202 = ea.print a  in
            FStar_Util.format1 "Inl %s" uu____3202
        | FStar_Util.Inr b ->
            let uu____3206 = eb.print b  in
            FStar_Util.format1 "Inr %s" uu____3206
         in
      let em s rng topt norm1 =
        lazy_embed printer emb_t_sum_a_b rng t_sum_a_b s
          (match s with
           | FStar_Util.Inl a ->
               (fun uu____3252  ->
                  let shadow_a =
                    map_shadow topt
                      (fun t  ->
                         let v1 = FStar_Ident.mk_ident ("v", rng)  in
                         let some_v =
                           FStar_Syntax_Util.mk_field_projector_name_from_ident
                             FStar_Parser_Const.inl_lid v1
                            in
                         let some_v_tm =
                           let uu____3265 =
                             FStar_Syntax_Syntax.lid_as_fv some_v
                               FStar_Syntax_Syntax.delta_equational
                               FStar_Pervasives_Native.None
                              in
                           FStar_Syntax_Syntax.fv_to_tm uu____3265  in
                         let uu____3266 =
                           let uu____3271 =
                             FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm
                               [FStar_Syntax_Syntax.U_zero]
                              in
                           let uu____3272 =
                             let uu____3273 =
                               let uu____3282 = type_of ea  in
                               FStar_Syntax_Syntax.iarg uu____3282  in
                             let uu____3283 =
                               let uu____3294 =
                                 let uu____3303 = type_of eb  in
                                 FStar_Syntax_Syntax.iarg uu____3303  in
                               let uu____3304 =
                                 let uu____3315 =
                                   FStar_Syntax_Syntax.as_arg t  in
                                 [uu____3315]  in
                               uu____3294 :: uu____3304  in
                             uu____3273 :: uu____3283  in
                           FStar_Syntax_Syntax.mk_Tm_app uu____3271
                             uu____3272
                            in
                         uu____3266 FStar_Pervasives_Native.None rng)
                     in
                  let uu____3356 =
                    let uu____3361 =
                      let uu____3362 =
                        FStar_Syntax_Syntax.tdataconstr
                          FStar_Parser_Const.inl_lid
                         in
                      FStar_Syntax_Syntax.mk_Tm_uinst uu____3362
                        [FStar_Syntax_Syntax.U_zero;
                        FStar_Syntax_Syntax.U_zero]
                       in
                    let uu____3363 =
                      let uu____3364 =
                        let uu____3373 = type_of ea  in
                        FStar_Syntax_Syntax.iarg uu____3373  in
                      let uu____3374 =
                        let uu____3385 =
                          let uu____3394 = type_of eb  in
                          FStar_Syntax_Syntax.iarg uu____3394  in
                        let uu____3395 =
                          let uu____3406 =
                            let uu____3415 =
                              let uu____3416 = embed ea a  in
                              uu____3416 rng shadow_a norm1  in
                            FStar_Syntax_Syntax.as_arg uu____3415  in
                          [uu____3406]  in
                        uu____3385 :: uu____3395  in
                      uu____3364 :: uu____3374  in
                    FStar_Syntax_Syntax.mk_Tm_app uu____3361 uu____3363  in
                  uu____3356 FStar_Pervasives_Native.None rng)
           | FStar_Util.Inr b ->
               (fun uu____3456  ->
                  let shadow_b =
                    map_shadow topt
                      (fun t  ->
                         let v1 = FStar_Ident.mk_ident ("v", rng)  in
                         let some_v =
                           FStar_Syntax_Util.mk_field_projector_name_from_ident
                             FStar_Parser_Const.inr_lid v1
                            in
                         let some_v_tm =
                           let uu____3469 =
                             FStar_Syntax_Syntax.lid_as_fv some_v
                               FStar_Syntax_Syntax.delta_equational
                               FStar_Pervasives_Native.None
                              in
                           FStar_Syntax_Syntax.fv_to_tm uu____3469  in
                         let uu____3470 =
                           let uu____3475 =
                             FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm
                               [FStar_Syntax_Syntax.U_zero]
                              in
                           let uu____3476 =
                             let uu____3477 =
                               let uu____3486 = type_of ea  in
                               FStar_Syntax_Syntax.iarg uu____3486  in
                             let uu____3487 =
                               let uu____3498 =
                                 let uu____3507 = type_of eb  in
                                 FStar_Syntax_Syntax.iarg uu____3507  in
                               let uu____3508 =
                                 let uu____3519 =
                                   FStar_Syntax_Syntax.as_arg t  in
                                 [uu____3519]  in
                               uu____3498 :: uu____3508  in
                             uu____3477 :: uu____3487  in
                           FStar_Syntax_Syntax.mk_Tm_app uu____3475
                             uu____3476
                            in
                         uu____3470 FStar_Pervasives_Native.None rng)
                     in
                  let uu____3560 =
                    let uu____3565 =
                      let uu____3566 =
                        FStar_Syntax_Syntax.tdataconstr
                          FStar_Parser_Const.inr_lid
                         in
                      FStar_Syntax_Syntax.mk_Tm_uinst uu____3566
                        [FStar_Syntax_Syntax.U_zero;
                        FStar_Syntax_Syntax.U_zero]
                       in
                    let uu____3567 =
                      let uu____3568 =
                        let uu____3577 = type_of ea  in
                        FStar_Syntax_Syntax.iarg uu____3577  in
                      let uu____3578 =
                        let uu____3589 =
                          let uu____3598 = type_of eb  in
                          FStar_Syntax_Syntax.iarg uu____3598  in
                        let uu____3599 =
                          let uu____3610 =
                            let uu____3619 =
                              let uu____3620 = embed eb b  in
                              uu____3620 rng shadow_b norm1  in
                            FStar_Syntax_Syntax.as_arg uu____3619  in
                          [uu____3610]  in
                        uu____3589 :: uu____3599  in
                      uu____3568 :: uu____3578  in
                    FStar_Syntax_Syntax.mk_Tm_app uu____3565 uu____3567  in
                  uu____3560 FStar_Pervasives_Native.None rng))
         in
      let un t0 w norm1 =
        let t = FStar_Syntax_Util.unmeta_safe t0  in
        lazy_unembed printer emb_t_sum_a_b t t_sum_a_b
          (fun t1  ->
             let uu____3708 = FStar_Syntax_Util.head_and_args' t1  in
             match uu____3708 with
             | (hd1,args) ->
                 let uu____3751 =
                   let uu____3766 =
                     let uu____3767 = FStar_Syntax_Util.un_uinst hd1  in
                     uu____3767.FStar_Syntax_Syntax.n  in
                   (uu____3766, args)  in
                 (match uu____3751 with
                  | (FStar_Syntax_Syntax.Tm_fvar
                     fv,uu____3787::uu____3788::(a,uu____3790)::[]) when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.inl_lid
                      ->
                      let uu____3857 =
                        let uu____3860 = unembed ea a  in uu____3860 w norm1
                         in
                      FStar_Util.bind_opt uu____3857
                        (fun a1  ->
                           FStar_Pervasives_Native.Some (FStar_Util.Inl a1))
                  | (FStar_Syntax_Syntax.Tm_fvar
                     fv,uu____3878::uu____3879::(b,uu____3881)::[]) when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.inr_lid
                      ->
                      let uu____3948 =
                        let uu____3951 = unembed eb b  in uu____3951 w norm1
                         in
                      FStar_Util.bind_opt uu____3948
                        (fun b1  ->
                           FStar_Pervasives_Native.Some (FStar_Util.Inr b1))
                  | uu____3968 ->
                      (if w
                       then
                         (let uu____3985 =
                            let uu____3991 =
                              let uu____3993 =
                                FStar_Syntax_Print.term_to_string t0  in
                              FStar_Util.format1 "Not an embedded sum: %s"
                                uu____3993
                               in
                            (FStar_Errors.Warning_NotEmbedded, uu____3991)
                             in
                          FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                            uu____3985)
                       else ();
                       FStar_Pervasives_Native.None)))
         in
      let uu____4003 =
        let uu____4004 = type_of ea  in
        let uu____4005 = type_of eb  in
        FStar_Syntax_Syntax.t_either_of uu____4004 uu____4005  in
      mk_emb_full em un uu____4003 printer emb_t_sum_a_b
  
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea  ->
    let t_list_a =
      let t_list = FStar_Syntax_Util.fvar_const FStar_Parser_Const.list_lid
         in
      let uu____4033 =
        let uu____4038 =
          let uu____4039 = FStar_Syntax_Syntax.as_arg ea.typ  in [uu____4039]
           in
        FStar_Syntax_Syntax.mk_Tm_app t_list uu____4038  in
      uu____4033 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
    let emb_t_list_a =
      let uu____4065 =
        let uu____4073 =
          FStar_All.pipe_right FStar_Parser_Const.list_lid
            FStar_Ident.string_of_lid
           in
        (uu____4073, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____4065  in
    let printer l =
      let uu____4090 =
        let uu____4092 =
          let uu____4094 = FStar_List.map ea.print l  in
          FStar_All.pipe_right uu____4094 (FStar_String.concat "; ")  in
        Prims.op_Hat uu____4092 "]"  in
      Prims.op_Hat "[" uu____4090  in
    let rec em l rng shadow_l norm1 =
      lazy_embed printer emb_t_list_a rng t_list_a l
        (fun uu____4138  ->
           let t =
             let uu____4140 = type_of ea  in
             FStar_Syntax_Syntax.iarg uu____4140  in
           match l with
           | [] ->
               let uu____4141 =
                 let uu____4146 =
                   let uu____4147 =
                     FStar_Syntax_Syntax.tdataconstr
                       FStar_Parser_Const.nil_lid
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____4147
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 FStar_Syntax_Syntax.mk_Tm_app uu____4146 [t]  in
               uu____4141 FStar_Pervasives_Native.None rng
           | hd1::tl1 ->
               let cons1 =
                 let uu____4169 =
                   FStar_Syntax_Syntax.tdataconstr
                     FStar_Parser_Const.cons_lid
                    in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu____4169
                   [FStar_Syntax_Syntax.U_zero]
                  in
               let proj f cons_tm =
                 let fid = FStar_Ident.mk_ident (f, rng)  in
                 let proj =
                   FStar_Syntax_Util.mk_field_projector_name_from_ident
                     FStar_Parser_Const.cons_lid fid
                    in
                 let proj_tm =
                   let uu____4189 =
                     FStar_Syntax_Syntax.lid_as_fv proj
                       FStar_Syntax_Syntax.delta_equational
                       FStar_Pervasives_Native.None
                      in
                   FStar_Syntax_Syntax.fv_to_tm uu____4189  in
                 let uu____4190 =
                   let uu____4195 =
                     FStar_Syntax_Syntax.mk_Tm_uinst proj_tm
                       [FStar_Syntax_Syntax.U_zero]
                      in
                   let uu____4196 =
                     let uu____4197 =
                       let uu____4206 = type_of ea  in
                       FStar_Syntax_Syntax.iarg uu____4206  in
                     let uu____4207 =
                       let uu____4218 = FStar_Syntax_Syntax.as_arg cons_tm
                          in
                       [uu____4218]  in
                     uu____4197 :: uu____4207  in
                   FStar_Syntax_Syntax.mk_Tm_app uu____4195 uu____4196  in
                 uu____4190 FStar_Pervasives_Native.None rng  in
               let shadow_hd = map_shadow shadow_l (proj "hd")  in
               let shadow_tl = map_shadow shadow_l (proj "tl")  in
               let uu____4255 =
                 let uu____4260 =
                   let uu____4261 =
                     let uu____4272 =
                       let uu____4281 =
                         let uu____4282 = embed ea hd1  in
                         uu____4282 rng shadow_hd norm1  in
                       FStar_Syntax_Syntax.as_arg uu____4281  in
                     let uu____4289 =
                       let uu____4300 =
                         let uu____4309 = em tl1 rng shadow_tl norm1  in
                         FStar_Syntax_Syntax.as_arg uu____4309  in
                       [uu____4300]  in
                     uu____4272 :: uu____4289  in
                   t :: uu____4261  in
                 FStar_Syntax_Syntax.mk_Tm_app cons1 uu____4260  in
               uu____4255 FStar_Pervasives_Native.None rng)
       in
    let rec un t0 w norm1 =
      let t = FStar_Syntax_Util.unmeta_safe t0  in
      lazy_unembed printer emb_t_list_a t t_list_a
        (fun t1  ->
           let uu____4381 = FStar_Syntax_Util.head_and_args' t1  in
           match uu____4381 with
           | (hd1,args) ->
               let uu____4422 =
                 let uu____4435 =
                   let uu____4436 = FStar_Syntax_Util.un_uinst hd1  in
                   uu____4436.FStar_Syntax_Syntax.n  in
                 (uu____4435, args)  in
               (match uu____4422 with
                | (FStar_Syntax_Syntax.Tm_fvar fv,uu____4452) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.nil_lid
                    -> FStar_Pervasives_Native.Some []
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(uu____4472,FStar_Pervasives_Native.Some
                       (FStar_Syntax_Syntax.Implicit uu____4473))::(hd2,FStar_Pervasives_Native.None
                                                                    )::
                   (tl1,FStar_Pervasives_Native.None )::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.cons_lid
                    ->
                    let uu____4515 =
                      let uu____4518 = unembed ea hd2  in uu____4518 w norm1
                       in
                    FStar_Util.bind_opt uu____4515
                      (fun hd3  ->
                         let uu____4530 = un tl1 w norm1  in
                         FStar_Util.bind_opt uu____4530
                           (fun tl2  ->
                              FStar_Pervasives_Native.Some (hd3 :: tl2)))
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(hd2,FStar_Pervasives_Native.None )::(tl1,FStar_Pervasives_Native.None
                                                            )::[])
                    when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.cons_lid
                    ->
                    let uu____4578 =
                      let uu____4581 = unembed ea hd2  in uu____4581 w norm1
                       in
                    FStar_Util.bind_opt uu____4578
                      (fun hd3  ->
                         let uu____4593 = un tl1 w norm1  in
                         FStar_Util.bind_opt uu____4593
                           (fun tl2  ->
                              FStar_Pervasives_Native.Some (hd3 :: tl2)))
                | uu____4608 ->
                    (if w
                     then
                       (let uu____4623 =
                          let uu____4629 =
                            let uu____4631 =
                              FStar_Syntax_Print.term_to_string t0  in
                            FStar_Util.format1 "Not an embedded list: %s"
                              uu____4631
                             in
                          (FStar_Errors.Warning_NotEmbedded, uu____4629)  in
                        FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                          uu____4623)
                     else ();
                     FStar_Pervasives_Native.None)))
       in
    let uu____4639 =
      let uu____4640 = type_of ea  in
      FStar_Syntax_Syntax.t_list_of uu____4640  in
    mk_emb_full em un uu____4639 printer emb_t_list_a
  
let (e_string_list : Prims.string Prims.list embedding) = e_list e_string 
type norm_step =
  | Simpl 
  | Weak 
  | HNF 
  | Primops 
  | Delta 
  | Zeta 
  | Iota 
  | Reify 
  | UnfoldOnly of Prims.string Prims.list 
  | UnfoldFully of Prims.string Prims.list 
  | UnfoldAttr of Prims.string Prims.list 
  | NBE 
let (uu___is_Simpl : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Simpl  -> true | uu____4683 -> false
  
let (uu___is_Weak : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Weak  -> true | uu____4694 -> false
  
let (uu___is_HNF : norm_step -> Prims.bool) =
  fun projectee  -> match projectee with | HNF  -> true | uu____4705 -> false 
let (uu___is_Primops : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____4716 -> false
  
let (uu___is_Delta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Delta  -> true | uu____4727 -> false
  
let (uu___is_Zeta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Zeta  -> true | uu____4738 -> false
  
let (uu___is_Iota : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Iota  -> true | uu____4749 -> false
  
let (uu___is_Reify : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____4760 -> false
  
let (uu___is_UnfoldOnly : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____4775 -> false
  
let (__proj__UnfoldOnly__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldFully : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldFully _0 -> true | uu____4806 -> false
  
let (__proj__UnfoldFully__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldFully _0 -> _0 
let (uu___is_UnfoldAttr : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____4837 -> false
  
let (__proj__UnfoldAttr__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_NBE : norm_step -> Prims.bool) =
  fun projectee  -> match projectee with | NBE  -> true | uu____4864 -> false 
let (steps_Simpl : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.steps_simpl 
let (steps_Weak : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.steps_weak 
let (steps_HNF : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.steps_hnf 
let (steps_Primops : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.steps_primops 
let (steps_Delta : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.steps_delta 
let (steps_Zeta : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.steps_zeta 
let (steps_Iota : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.steps_iota 
let (steps_Reify : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.steps_reify 
let (steps_UnfoldOnly : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.steps_unfoldonly 
let (steps_UnfoldFully : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.steps_unfoldonly 
let (steps_UnfoldAttr : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.steps_unfoldattr 
let (steps_NBE : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.steps_nbe 
let (e_norm_step : norm_step embedding) =
  let t_norm_step1 =
    let uu____4882 =
      FStar_Ident.lid_of_str "FStar.Syntax.Embeddings.norm_step"  in
    FStar_Syntax_Util.fvar_const uu____4882  in
  let emb_t_norm_step =
    let uu____4885 =
      let uu____4893 =
        FStar_All.pipe_right FStar_Parser_Const.norm_step_lid
          FStar_Ident.string_of_lid
         in
      (uu____4893, [])  in
    FStar_Syntax_Syntax.ET_app uu____4885  in
  let printer uu____4905 = "norm_step"  in
  let em n1 rng _topt norm1 =
    lazy_embed printer emb_t_norm_step rng t_norm_step1 n1
      (fun uu____4931  ->
         match n1 with
         | Simpl  -> steps_Simpl
         | Weak  -> steps_Weak
         | HNF  -> steps_HNF
         | Primops  -> steps_Primops
         | Delta  -> steps_Delta
         | Zeta  -> steps_Zeta
         | Iota  -> steps_Iota
         | NBE  -> steps_NBE
         | Reify  -> steps_Reify
         | UnfoldOnly l ->
             let uu____4936 =
               let uu____4941 =
                 let uu____4942 =
                   let uu____4951 =
                     let uu____4952 =
                       let uu____4959 = e_list e_string  in
                       embed uu____4959 l  in
                     uu____4952 rng FStar_Pervasives_Native.None norm1  in
                   FStar_Syntax_Syntax.as_arg uu____4951  in
                 [uu____4942]  in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldOnly uu____4941  in
             uu____4936 FStar_Pervasives_Native.None rng
         | UnfoldFully l ->
             let uu____4991 =
               let uu____4996 =
                 let uu____4997 =
                   let uu____5006 =
                     let uu____5007 =
                       let uu____5014 = e_list e_string  in
                       embed uu____5014 l  in
                     uu____5007 rng FStar_Pervasives_Native.None norm1  in
                   FStar_Syntax_Syntax.as_arg uu____5006  in
                 [uu____4997]  in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldFully uu____4996  in
             uu____4991 FStar_Pervasives_Native.None rng
         | UnfoldAttr l ->
             let uu____5046 =
               let uu____5051 =
                 let uu____5052 =
                   let uu____5061 =
                     let uu____5062 =
                       let uu____5069 = e_list e_string  in
                       embed uu____5069 l  in
                     uu____5062 rng FStar_Pervasives_Native.None norm1  in
                   FStar_Syntax_Syntax.as_arg uu____5061  in
                 [uu____5052]  in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldAttr uu____5051  in
             uu____5046 FStar_Pervasives_Native.None rng)
     in
  let un t0 w norm1 =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    lazy_unembed printer emb_t_norm_step t t_norm_step1
      (fun t1  ->
         let uu____5129 = FStar_Syntax_Util.head_and_args t1  in
         match uu____5129 with
         | (hd1,args) ->
             let uu____5174 =
               let uu____5189 =
                 let uu____5190 = FStar_Syntax_Util.un_uinst hd1  in
                 uu____5190.FStar_Syntax_Syntax.n  in
               (uu____5189, args)  in
             (match uu____5174 with
              | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_simpl
                  -> FStar_Pervasives_Native.Some Simpl
              | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_weak
                  -> FStar_Pervasives_Native.Some Weak
              | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_hnf
                  -> FStar_Pervasives_Native.Some HNF
              | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_primops
                  -> FStar_Pervasives_Native.Some Primops
              | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_delta
                  -> FStar_Pervasives_Native.Some Delta
              | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_zeta
                  -> FStar_Pervasives_Native.Some Zeta
              | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_iota
                  -> FStar_Pervasives_Native.Some Iota
              | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_nbe
                  -> FStar_Pervasives_Native.Some NBE
              | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_reify
                  -> FStar_Pervasives_Native.Some Reify
              | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____5378)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldonly
                  ->
                  let uu____5413 =
                    let uu____5419 =
                      let uu____5429 = e_list e_string  in
                      unembed uu____5429 l  in
                    uu____5419 w norm1  in
                  FStar_Util.bind_opt uu____5413
                    (fun ss  ->
                       FStar_All.pipe_left
                         (fun _5449  -> FStar_Pervasives_Native.Some _5449)
                         (UnfoldOnly ss))
              | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____5452)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldfully
                  ->
                  let uu____5487 =
                    let uu____5493 =
                      let uu____5503 = e_list e_string  in
                      unembed uu____5503 l  in
                    uu____5493 w norm1  in
                  FStar_Util.bind_opt uu____5487
                    (fun ss  ->
                       FStar_All.pipe_left
                         (fun _5523  -> FStar_Pervasives_Native.Some _5523)
                         (UnfoldFully ss))
              | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____5526)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldattr
                  ->
                  let uu____5561 =
                    let uu____5567 =
                      let uu____5577 = e_list e_string  in
                      unembed uu____5577 l  in
                    uu____5567 w norm1  in
                  FStar_Util.bind_opt uu____5561
                    (fun ss  ->
                       FStar_All.pipe_left
                         (fun _5597  -> FStar_Pervasives_Native.Some _5597)
                         (UnfoldAttr ss))
              | uu____5598 ->
                  (if w
                   then
                     (let uu____5615 =
                        let uu____5621 =
                          let uu____5623 =
                            FStar_Syntax_Print.term_to_string t0  in
                          FStar_Util.format1 "Not an embedded norm_step: %s"
                            uu____5623
                           in
                        (FStar_Errors.Warning_NotEmbedded, uu____5621)  in
                      FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                        uu____5615)
                   else ();
                   FStar_Pervasives_Native.None)))
     in
  mk_emb_full em un FStar_Syntax_Syntax.t_norm_step printer emb_t_norm_step 
let (e_range : FStar_Range.range embedding) =
  let em r rng _shadow _norm =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range r))
      FStar_Pervasives_Native.None rng
     in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range r) ->
        FStar_Pervasives_Native.Some r
    | uu____5683 ->
        (if w
         then
           (let uu____5686 =
              let uu____5692 =
                let uu____5694 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded range: %s" uu____5694  in
              (FStar_Errors.Warning_NotEmbedded, uu____5692)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____5686)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____5700 =
    let uu____5701 =
      let uu____5709 =
        FStar_All.pipe_right FStar_Parser_Const.range_lid
          FStar_Ident.string_of_lid
         in
      (uu____5709, [])  in
    FStar_Syntax_Syntax.ET_app uu____5701  in
  mk_emb_full em un FStar_Syntax_Syntax.t_range FStar_Range.string_of_range
    uu____5700
  
let or_else : 'a . 'a FStar_Pervasives_Native.option -> (unit -> 'a) -> 'a =
  fun f  ->
    fun g  ->
      match f with
      | FStar_Pervasives_Native.Some x -> x
      | FStar_Pervasives_Native.None  -> g ()
  
let e_arrow : 'a 'b . 'a embedding -> 'b embedding -> ('a -> 'b) embedding =
  fun ea  ->
    fun eb  ->
      let t_arrow =
        let uu____5780 =
          let uu____5787 =
            let uu____5788 =
              let uu____5803 =
                let uu____5812 =
                  let uu____5819 = FStar_Syntax_Syntax.null_bv ea.typ  in
                  (uu____5819, FStar_Pervasives_Native.None)  in
                [uu____5812]  in
              let uu____5834 = FStar_Syntax_Syntax.mk_Total eb.typ  in
              (uu____5803, uu____5834)  in
            FStar_Syntax_Syntax.Tm_arrow uu____5788  in
          FStar_Syntax_Syntax.mk uu____5787  in
        uu____5780 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
      let emb_t_arr_a_b =
        FStar_Syntax_Syntax.ET_fun ((ea.emb_typ), (eb.emb_typ))  in
      let printer f = "<fun>"  in
      let em f rng shadow_f norm1 =
        lazy_embed (fun uu____5906  -> "<fun>") emb_t_arr_a_b rng t_arrow f
          (fun uu____5912  ->
             let uu____5913 = force_shadow shadow_f  in
             match uu____5913 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Exn.raise Embedding_failure
             | FStar_Pervasives_Native.Some repr_f ->
                 ((let uu____5918 =
                     FStar_ST.op_Bang FStar_Options.debug_embedding  in
                   if uu____5918
                   then
                     let uu____5942 =
                       FStar_Syntax_Print.term_to_string repr_f  in
                     let uu____5944 = FStar_Util.stack_dump ()  in
                     FStar_Util.print2
                       "e_arrow forced back to term using shadow %s; repr=%s\n"
                       uu____5942 uu____5944
                   else ());
                  (let res = norm1 (FStar_Util.Inr repr_f)  in
                   (let uu____5951 =
                      FStar_ST.op_Bang FStar_Options.debug_embedding  in
                    if uu____5951
                    then
                      let uu____5975 =
                        FStar_Syntax_Print.term_to_string repr_f  in
                      let uu____5977 = FStar_Syntax_Print.term_to_string res
                         in
                      let uu____5979 = FStar_Util.stack_dump ()  in
                      FStar_Util.print3
                        "e_arrow forced back to term using shadow %s; repr=%s\n\t%s\n"
                        uu____5975 uu____5977 uu____5979
                    else ());
                   res)))
         in
      let un f w norm1 =
        lazy_unembed printer emb_t_arr_a_b f t_arrow
          (fun f1  ->
             let f_wrapped a =
               (let uu____6038 =
                  FStar_ST.op_Bang FStar_Options.debug_embedding  in
                if uu____6038
                then
                  let uu____6062 = FStar_Syntax_Print.term_to_string f1  in
                  let uu____6064 = FStar_Util.stack_dump ()  in
                  FStar_Util.print2
                    "Calling back into normalizer for %s\n%s\n" uu____6062
                    uu____6064
                else ());
               (let a_tm =
                  let uu____6070 = embed ea a  in
                  uu____6070 f1.FStar_Syntax_Syntax.pos
                    FStar_Pervasives_Native.None norm1
                   in
                let b_tm =
                  let uu____6080 =
                    let uu____6085 =
                      let uu____6086 =
                        let uu____6091 =
                          let uu____6092 = FStar_Syntax_Syntax.as_arg a_tm
                             in
                          [uu____6092]  in
                        FStar_Syntax_Syntax.mk_Tm_app f1 uu____6091  in
                      uu____6086 FStar_Pervasives_Native.None
                        f1.FStar_Syntax_Syntax.pos
                       in
                    FStar_Util.Inr uu____6085  in
                  norm1 uu____6080  in
                let uu____6117 =
                  let uu____6120 = unembed eb b_tm  in uu____6120 w norm1  in
                match uu____6117 with
                | FStar_Pervasives_Native.None  ->
                    FStar_Exn.raise Unembedding_failure
                | FStar_Pervasives_Native.Some b -> b)
                in
             FStar_Pervasives_Native.Some f_wrapped)
         in
      mk_emb_full em un t_arrow printer emb_t_arr_a_b
  
let arrow_as_prim_step_1 :
  'a 'b .
    'a embedding ->
      'b embedding ->
        ('a -> 'b) ->
          Prims.int ->
            FStar_Ident.lid ->
              norm_cb ->
                FStar_Syntax_Syntax.args ->
                  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun ea  ->
    fun eb  ->
      fun f  ->
        fun n_tvars  ->
          fun fv_lid1  ->
            fun norm1  ->
              let rng = FStar_Ident.range_of_lid fv_lid1  in
              let f_wrapped args =
                let uu____6214 = FStar_List.splitAt n_tvars args  in
                match uu____6214 with
                | (_tvar_args,rest_args) ->
                    let uu____6291 = FStar_List.hd rest_args  in
                    (match uu____6291 with
                     | (x,uu____6311) ->
                         let shadow_app =
                           let uu____6325 =
                             FStar_Thunk.mk
                               (fun uu____6332  ->
                                  let uu____6333 =
                                    let uu____6338 =
                                      norm1 (FStar_Util.Inl fv_lid1)  in
                                    FStar_Syntax_Syntax.mk_Tm_app uu____6338
                                      args
                                     in
                                  uu____6333 FStar_Pervasives_Native.None rng)
                              in
                           FStar_Pervasives_Native.Some uu____6325  in
                         let uu____6341 =
                           let uu____6344 =
                             let uu____6347 = unembed ea x  in
                             uu____6347 true norm1  in
                           FStar_Util.map_opt uu____6344
                             (fun x1  ->
                                let uu____6358 =
                                  let uu____6365 = f x1  in
                                  embed eb uu____6365  in
                                uu____6358 rng shadow_app norm1)
                            in
                         (match uu____6341 with
                          | FStar_Pervasives_Native.Some x1 ->
                              FStar_Pervasives_Native.Some x1
                          | FStar_Pervasives_Native.None  ->
                              force_shadow shadow_app))
                 in
              f_wrapped
  
let arrow_as_prim_step_2 :
  'a 'b 'c .
    'a embedding ->
      'b embedding ->
        'c embedding ->
          ('a -> 'b -> 'c) ->
            Prims.int ->
              FStar_Ident.lid ->
                norm_cb ->
                  FStar_Syntax_Syntax.args ->
                    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun ea  ->
    fun eb  ->
      fun ec  ->
        fun f  ->
          fun n_tvars  ->
            fun fv_lid1  ->
              fun norm1  ->
                let rng = FStar_Ident.range_of_lid fv_lid1  in
                let f_wrapped args =
                  let uu____6468 = FStar_List.splitAt n_tvars args  in
                  match uu____6468 with
                  | (_tvar_args,rest_args) ->
                      let uu____6531 = FStar_List.hd rest_args  in
                      (match uu____6531 with
                       | (x,uu____6547) ->
                           let uu____6552 =
                             let uu____6559 = FStar_List.tl rest_args  in
                             FStar_List.hd uu____6559  in
                           (match uu____6552 with
                            | (y,uu____6583) ->
                                let shadow_app =
                                  let uu____6593 =
                                    FStar_Thunk.mk
                                      (fun uu____6600  ->
                                         let uu____6601 =
                                           let uu____6606 =
                                             norm1 (FStar_Util.Inl fv_lid1)
                                              in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____6606 args
                                            in
                                         uu____6601
                                           FStar_Pervasives_Native.None rng)
                                     in
                                  FStar_Pervasives_Native.Some uu____6593  in
                                let uu____6609 =
                                  let uu____6612 =
                                    let uu____6615 = unembed ea x  in
                                    uu____6615 true norm1  in
                                  FStar_Util.bind_opt uu____6612
                                    (fun x1  ->
                                       let uu____6626 =
                                         let uu____6629 = unembed eb y  in
                                         uu____6629 true norm1  in
                                       FStar_Util.bind_opt uu____6626
                                         (fun y1  ->
                                            let uu____6640 =
                                              let uu____6641 =
                                                let uu____6648 = f x1 y1  in
                                                embed ec uu____6648  in
                                              uu____6641 rng shadow_app norm1
                                               in
                                            FStar_Pervasives_Native.Some
                                              uu____6640))
                                   in
                                (match uu____6609 with
                                 | FStar_Pervasives_Native.Some x1 ->
                                     FStar_Pervasives_Native.Some x1
                                 | FStar_Pervasives_Native.None  ->
                                     force_shadow shadow_app)))
                   in
                f_wrapped
  
let arrow_as_prim_step_3 :
  'a 'b 'c 'd .
    'a embedding ->
      'b embedding ->
        'c embedding ->
          'd embedding ->
            ('a -> 'b -> 'c -> 'd) ->
              Prims.int ->
                FStar_Ident.lid ->
                  norm_cb ->
                    FStar_Syntax_Syntax.args ->
                      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun ea  ->
    fun eb  ->
      fun ec  ->
        fun ed  ->
          fun f  ->
            fun n_tvars  ->
              fun fv_lid1  ->
                fun norm1  ->
                  let rng = FStar_Ident.range_of_lid fv_lid1  in
                  let f_wrapped args =
                    let uu____6770 = FStar_List.splitAt n_tvars args  in
                    match uu____6770 with
                    | (_tvar_args,rest_args) ->
                        let uu____6833 = FStar_List.hd rest_args  in
                        (match uu____6833 with
                         | (x,uu____6849) ->
                             let uu____6854 =
                               let uu____6861 = FStar_List.tl rest_args  in
                               FStar_List.hd uu____6861  in
                             (match uu____6854 with
                              | (y,uu____6885) ->
                                  let uu____6890 =
                                    let uu____6897 =
                                      let uu____6906 =
                                        FStar_List.tl rest_args  in
                                      FStar_List.tl uu____6906  in
                                    FStar_List.hd uu____6897  in
                                  (match uu____6890 with
                                   | (z,uu____6936) ->
                                       let shadow_app =
                                         let uu____6946 =
                                           FStar_Thunk.mk
                                             (fun uu____6953  ->
                                                let uu____6954 =
                                                  let uu____6959 =
                                                    norm1
                                                      (FStar_Util.Inl fv_lid1)
                                                     in
                                                  FStar_Syntax_Syntax.mk_Tm_app
                                                    uu____6959 args
                                                   in
                                                uu____6954
                                                  FStar_Pervasives_Native.None
                                                  rng)
                                            in
                                         FStar_Pervasives_Native.Some
                                           uu____6946
                                          in
                                       let uu____6962 =
                                         let uu____6965 =
                                           let uu____6968 = unembed ea x  in
                                           uu____6968 true norm1  in
                                         FStar_Util.bind_opt uu____6965
                                           (fun x1  ->
                                              let uu____6979 =
                                                let uu____6982 = unembed eb y
                                                   in
                                                uu____6982 true norm1  in
                                              FStar_Util.bind_opt uu____6979
                                                (fun y1  ->
                                                   let uu____6993 =
                                                     let uu____6996 =
                                                       unembed ec z  in
                                                     uu____6996 true norm1
                                                      in
                                                   FStar_Util.bind_opt
                                                     uu____6993
                                                     (fun z1  ->
                                                        let uu____7007 =
                                                          let uu____7008 =
                                                            let uu____7015 =
                                                              f x1 y1 z1  in
                                                            embed ed
                                                              uu____7015
                                                             in
                                                          uu____7008 rng
                                                            shadow_app norm1
                                                           in
                                                        FStar_Pervasives_Native.Some
                                                          uu____7007)))
                                          in
                                       (match uu____6962 with
                                        | FStar_Pervasives_Native.Some x1 ->
                                            FStar_Pervasives_Native.Some x1
                                        | FStar_Pervasives_Native.None  ->
                                            force_shadow shadow_app))))
                     in
                  f_wrapped
  
let debug_wrap : 'a . Prims.string -> (unit -> 'a) -> 'a =
  fun s  ->
    fun f  ->
      (let uu____7045 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
       if uu____7045 then FStar_Util.print1 "++++starting %s\n" s else ());
      (let res = f ()  in
       (let uu____7074 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
        if uu____7074 then FStar_Util.print1 "------ending %s\n" s else ());
       res)
  