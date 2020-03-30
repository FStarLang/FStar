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
               let uu____2570 =
                 let uu____2575 =
                   FStar_Parser_Const.mk_tuple_data_lid (Prims.of_int (2))
                     rng
                    in
                 let uu____2577 =
                   FStar_Syntax_Syntax.null_bv FStar_Syntax_Syntax.tun  in
                 FStar_Syntax_Util.mk_field_projector_name uu____2575
                   uu____2577 i
                  in
               match uu____2570 with
               | (proj_1,uu____2581) ->
                   let proj_1_tm =
                     let uu____2583 =
                       FStar_Syntax_Syntax.lid_as_fv proj_1
                         FStar_Syntax_Syntax.delta_equational
                         FStar_Pervasives_Native.None
                        in
                     FStar_Syntax_Syntax.fv_to_tm uu____2583  in
                   let uu____2584 =
                     let uu____2589 =
                       FStar_Syntax_Syntax.mk_Tm_uinst proj_1_tm
                         [FStar_Syntax_Syntax.U_zero]
                        in
                     let uu____2590 =
                       let uu____2591 =
                         let uu____2600 = type_of ea  in
                         FStar_Syntax_Syntax.iarg uu____2600  in
                       let uu____2601 =
                         let uu____2612 =
                           let uu____2621 = type_of eb  in
                           FStar_Syntax_Syntax.iarg uu____2621  in
                         let uu____2622 =
                           let uu____2633 = FStar_Syntax_Syntax.as_arg ab  in
                           [uu____2633]  in
                         uu____2612 :: uu____2622  in
                       uu____2591 :: uu____2601  in
                     FStar_Syntax_Syntax.mk_Tm_app uu____2589 uu____2590  in
                   uu____2584 FStar_Pervasives_Native.None rng
                in
             let shadow_a = map_shadow topt (proj Prims.int_one)  in
             let shadow_b = map_shadow topt (proj (Prims.of_int (2)))  in
             let uu____2678 =
               let uu____2683 =
                 let uu____2684 =
                   FStar_Syntax_Syntax.tdataconstr
                     FStar_Parser_Const.lid_Mktuple2
                    in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu____2684
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                  in
               let uu____2685 =
                 let uu____2686 =
                   let uu____2695 = type_of ea  in
                   FStar_Syntax_Syntax.iarg uu____2695  in
                 let uu____2696 =
                   let uu____2707 =
                     let uu____2716 = type_of eb  in
                     FStar_Syntax_Syntax.iarg uu____2716  in
                   let uu____2717 =
                     let uu____2728 =
                       let uu____2737 =
                         let uu____2738 =
                           embed ea (FStar_Pervasives_Native.fst x)  in
                         uu____2738 rng shadow_a norm1  in
                       FStar_Syntax_Syntax.as_arg uu____2737  in
                     let uu____2745 =
                       let uu____2756 =
                         let uu____2765 =
                           let uu____2766 =
                             embed eb (FStar_Pervasives_Native.snd x)  in
                           uu____2766 rng shadow_b norm1  in
                         FStar_Syntax_Syntax.as_arg uu____2765  in
                       [uu____2756]  in
                     uu____2728 :: uu____2745  in
                   uu____2707 :: uu____2717  in
                 uu____2686 :: uu____2696  in
               FStar_Syntax_Syntax.mk_Tm_app uu____2683 uu____2685  in
             uu____2678 FStar_Pervasives_Native.None rng)
         in
      let un t0 w norm1 =
        let t = FStar_Syntax_Util.unmeta_safe t0  in
        lazy_unembed printer emb_t_pair_a_b t t_pair_a_b
          (fun t1  ->
             let uu____2864 = FStar_Syntax_Util.head_and_args' t1  in
             match uu____2864 with
             | (hd1,args) ->
                 let uu____2907 =
                   let uu____2920 =
                     let uu____2921 = FStar_Syntax_Util.un_uinst hd1  in
                     uu____2921.FStar_Syntax_Syntax.n  in
                   (uu____2920, args)  in
                 (match uu____2907 with
                  | (FStar_Syntax_Syntax.Tm_fvar
                     fv,uu____2939::uu____2940::(a,uu____2942)::(b,uu____2944)::[])
                      when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.lid_Mktuple2
                      ->
                      let uu____3003 =
                        let uu____3006 = unembed ea a  in uu____3006 w norm1
                         in
                      FStar_Util.bind_opt uu____3003
                        (fun a1  ->
                           let uu____3020 =
                             let uu____3023 = unembed eb b  in
                             uu____3023 w norm1  in
                           FStar_Util.bind_opt uu____3020
                             (fun b1  ->
                                FStar_Pervasives_Native.Some (a1, b1)))
                  | uu____3040 ->
                      (if w
                       then
                         (let uu____3055 =
                            let uu____3061 =
                              let uu____3063 =
                                FStar_Syntax_Print.term_to_string t0  in
                              FStar_Util.format1 "Not an embedded pair: %s"
                                uu____3063
                               in
                            (FStar_Errors.Warning_NotEmbedded, uu____3061)
                             in
                          FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                            uu____3055)
                       else ();
                       FStar_Pervasives_Native.None)))
         in
      let uu____3073 =
        let uu____3074 = type_of ea  in
        let uu____3075 = type_of eb  in
        FStar_Syntax_Syntax.t_tuple2_of uu____3074 uu____3075  in
      mk_emb_full em un uu____3073 printer emb_t_pair_a_b
  
let e_either :
  'a 'b . 'a embedding -> 'b embedding -> ('a,'b) FStar_Util.either embedding
  =
  fun ea  ->
    fun eb  ->
      let t_sum_a_b =
        let t_either =
          FStar_Syntax_Util.fvar_const FStar_Parser_Const.either_lid  in
        let uu____3119 =
          let uu____3124 =
            let uu____3125 = FStar_Syntax_Syntax.as_arg ea.typ  in
            let uu____3134 =
              let uu____3145 = FStar_Syntax_Syntax.as_arg eb.typ  in
              [uu____3145]  in
            uu____3125 :: uu____3134  in
          FStar_Syntax_Syntax.mk_Tm_app t_either uu____3124  in
        uu____3119 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
      let emb_t_sum_a_b =
        let uu____3179 =
          let uu____3187 =
            FStar_All.pipe_right FStar_Parser_Const.either_lid
              FStar_Ident.string_of_lid
             in
          (uu____3187, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____3179  in
      let printer s =
        match s with
        | FStar_Util.Inl a ->
            let uu____3210 = ea.print a  in
            FStar_Util.format1 "Inl %s" uu____3210
        | FStar_Util.Inr b ->
            let uu____3214 = eb.print b  in
            FStar_Util.format1 "Inr %s" uu____3214
         in
      let em s rng topt norm1 =
        lazy_embed printer emb_t_sum_a_b rng t_sum_a_b s
          (match s with
           | FStar_Util.Inl a ->
               (fun uu____3260  ->
                  let shadow_a =
                    map_shadow topt
                      (fun t  ->
                         let v1 = FStar_Ident.mk_ident ("v", rng)  in
                         let some_v =
                           FStar_Syntax_Util.mk_field_projector_name_from_ident
                             FStar_Parser_Const.inl_lid v1
                            in
                         let some_v_tm =
                           let uu____3273 =
                             FStar_Syntax_Syntax.lid_as_fv some_v
                               FStar_Syntax_Syntax.delta_equational
                               FStar_Pervasives_Native.None
                              in
                           FStar_Syntax_Syntax.fv_to_tm uu____3273  in
                         let uu____3274 =
                           let uu____3279 =
                             FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm
                               [FStar_Syntax_Syntax.U_zero]
                              in
                           let uu____3280 =
                             let uu____3281 =
                               let uu____3290 = type_of ea  in
                               FStar_Syntax_Syntax.iarg uu____3290  in
                             let uu____3291 =
                               let uu____3302 =
                                 let uu____3311 = type_of eb  in
                                 FStar_Syntax_Syntax.iarg uu____3311  in
                               let uu____3312 =
                                 let uu____3323 =
                                   FStar_Syntax_Syntax.as_arg t  in
                                 [uu____3323]  in
                               uu____3302 :: uu____3312  in
                             uu____3281 :: uu____3291  in
                           FStar_Syntax_Syntax.mk_Tm_app uu____3279
                             uu____3280
                            in
                         uu____3274 FStar_Pervasives_Native.None rng)
                     in
                  let uu____3364 =
                    let uu____3369 =
                      let uu____3370 =
                        FStar_Syntax_Syntax.tdataconstr
                          FStar_Parser_Const.inl_lid
                         in
                      FStar_Syntax_Syntax.mk_Tm_uinst uu____3370
                        [FStar_Syntax_Syntax.U_zero;
                        FStar_Syntax_Syntax.U_zero]
                       in
                    let uu____3371 =
                      let uu____3372 =
                        let uu____3381 = type_of ea  in
                        FStar_Syntax_Syntax.iarg uu____3381  in
                      let uu____3382 =
                        let uu____3393 =
                          let uu____3402 = type_of eb  in
                          FStar_Syntax_Syntax.iarg uu____3402  in
                        let uu____3403 =
                          let uu____3414 =
                            let uu____3423 =
                              let uu____3424 = embed ea a  in
                              uu____3424 rng shadow_a norm1  in
                            FStar_Syntax_Syntax.as_arg uu____3423  in
                          [uu____3414]  in
                        uu____3393 :: uu____3403  in
                      uu____3372 :: uu____3382  in
                    FStar_Syntax_Syntax.mk_Tm_app uu____3369 uu____3371  in
                  uu____3364 FStar_Pervasives_Native.None rng)
           | FStar_Util.Inr b ->
               (fun uu____3464  ->
                  let shadow_b =
                    map_shadow topt
                      (fun t  ->
                         let v1 = FStar_Ident.mk_ident ("v", rng)  in
                         let some_v =
                           FStar_Syntax_Util.mk_field_projector_name_from_ident
                             FStar_Parser_Const.inr_lid v1
                            in
                         let some_v_tm =
                           let uu____3477 =
                             FStar_Syntax_Syntax.lid_as_fv some_v
                               FStar_Syntax_Syntax.delta_equational
                               FStar_Pervasives_Native.None
                              in
                           FStar_Syntax_Syntax.fv_to_tm uu____3477  in
                         let uu____3478 =
                           let uu____3483 =
                             FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm
                               [FStar_Syntax_Syntax.U_zero]
                              in
                           let uu____3484 =
                             let uu____3485 =
                               let uu____3494 = type_of ea  in
                               FStar_Syntax_Syntax.iarg uu____3494  in
                             let uu____3495 =
                               let uu____3506 =
                                 let uu____3515 = type_of eb  in
                                 FStar_Syntax_Syntax.iarg uu____3515  in
                               let uu____3516 =
                                 let uu____3527 =
                                   FStar_Syntax_Syntax.as_arg t  in
                                 [uu____3527]  in
                               uu____3506 :: uu____3516  in
                             uu____3485 :: uu____3495  in
                           FStar_Syntax_Syntax.mk_Tm_app uu____3483
                             uu____3484
                            in
                         uu____3478 FStar_Pervasives_Native.None rng)
                     in
                  let uu____3568 =
                    let uu____3573 =
                      let uu____3574 =
                        FStar_Syntax_Syntax.tdataconstr
                          FStar_Parser_Const.inr_lid
                         in
                      FStar_Syntax_Syntax.mk_Tm_uinst uu____3574
                        [FStar_Syntax_Syntax.U_zero;
                        FStar_Syntax_Syntax.U_zero]
                       in
                    let uu____3575 =
                      let uu____3576 =
                        let uu____3585 = type_of ea  in
                        FStar_Syntax_Syntax.iarg uu____3585  in
                      let uu____3586 =
                        let uu____3597 =
                          let uu____3606 = type_of eb  in
                          FStar_Syntax_Syntax.iarg uu____3606  in
                        let uu____3607 =
                          let uu____3618 =
                            let uu____3627 =
                              let uu____3628 = embed eb b  in
                              uu____3628 rng shadow_b norm1  in
                            FStar_Syntax_Syntax.as_arg uu____3627  in
                          [uu____3618]  in
                        uu____3597 :: uu____3607  in
                      uu____3576 :: uu____3586  in
                    FStar_Syntax_Syntax.mk_Tm_app uu____3573 uu____3575  in
                  uu____3568 FStar_Pervasives_Native.None rng))
         in
      let un t0 w norm1 =
        let t = FStar_Syntax_Util.unmeta_safe t0  in
        lazy_unembed printer emb_t_sum_a_b t t_sum_a_b
          (fun t1  ->
             let uu____3716 = FStar_Syntax_Util.head_and_args' t1  in
             match uu____3716 with
             | (hd1,args) ->
                 let uu____3759 =
                   let uu____3774 =
                     let uu____3775 = FStar_Syntax_Util.un_uinst hd1  in
                     uu____3775.FStar_Syntax_Syntax.n  in
                   (uu____3774, args)  in
                 (match uu____3759 with
                  | (FStar_Syntax_Syntax.Tm_fvar
                     fv,uu____3795::uu____3796::(a,uu____3798)::[]) when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.inl_lid
                      ->
                      let uu____3865 =
                        let uu____3868 = unembed ea a  in uu____3868 w norm1
                         in
                      FStar_Util.bind_opt uu____3865
                        (fun a1  ->
                           FStar_Pervasives_Native.Some (FStar_Util.Inl a1))
                  | (FStar_Syntax_Syntax.Tm_fvar
                     fv,uu____3886::uu____3887::(b,uu____3889)::[]) when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.inr_lid
                      ->
                      let uu____3956 =
                        let uu____3959 = unembed eb b  in uu____3959 w norm1
                         in
                      FStar_Util.bind_opt uu____3956
                        (fun b1  ->
                           FStar_Pervasives_Native.Some (FStar_Util.Inr b1))
                  | uu____3976 ->
                      (if w
                       then
                         (let uu____3993 =
                            let uu____3999 =
                              let uu____4001 =
                                FStar_Syntax_Print.term_to_string t0  in
                              FStar_Util.format1 "Not an embedded sum: %s"
                                uu____4001
                               in
                            (FStar_Errors.Warning_NotEmbedded, uu____3999)
                             in
                          FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                            uu____3993)
                       else ();
                       FStar_Pervasives_Native.None)))
         in
      let uu____4011 =
        let uu____4012 = type_of ea  in
        let uu____4013 = type_of eb  in
        FStar_Syntax_Syntax.t_either_of uu____4012 uu____4013  in
      mk_emb_full em un uu____4011 printer emb_t_sum_a_b
  
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea  ->
    let t_list_a =
      let t_list = FStar_Syntax_Util.fvar_const FStar_Parser_Const.list_lid
         in
      let uu____4041 =
        let uu____4046 =
          let uu____4047 = FStar_Syntax_Syntax.as_arg ea.typ  in [uu____4047]
           in
        FStar_Syntax_Syntax.mk_Tm_app t_list uu____4046  in
      uu____4041 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
    let emb_t_list_a =
      let uu____4073 =
        let uu____4081 =
          FStar_All.pipe_right FStar_Parser_Const.list_lid
            FStar_Ident.string_of_lid
           in
        (uu____4081, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____4073  in
    let printer l =
      let uu____4098 =
        let uu____4100 =
          let uu____4102 = FStar_List.map ea.print l  in
          FStar_All.pipe_right uu____4102 (FStar_String.concat "; ")  in
        Prims.op_Hat uu____4100 "]"  in
      Prims.op_Hat "[" uu____4098  in
    let rec em l rng shadow_l norm1 =
      lazy_embed printer emb_t_list_a rng t_list_a l
        (fun uu____4146  ->
           let t =
             let uu____4148 = type_of ea  in
             FStar_Syntax_Syntax.iarg uu____4148  in
           match l with
           | [] ->
               let uu____4149 =
                 let uu____4154 =
                   let uu____4155 =
                     FStar_Syntax_Syntax.tdataconstr
                       FStar_Parser_Const.nil_lid
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____4155
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 FStar_Syntax_Syntax.mk_Tm_app uu____4154 [t]  in
               uu____4149 FStar_Pervasives_Native.None rng
           | hd1::tl1 ->
               let cons1 =
                 let uu____4177 =
                   FStar_Syntax_Syntax.tdataconstr
                     FStar_Parser_Const.cons_lid
                    in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu____4177
                   [FStar_Syntax_Syntax.U_zero]
                  in
               let proj f cons_tm =
                 let fid = FStar_Ident.mk_ident (f, rng)  in
                 let proj =
                   FStar_Syntax_Util.mk_field_projector_name_from_ident
                     FStar_Parser_Const.cons_lid fid
                    in
                 let proj_tm =
                   let uu____4197 =
                     FStar_Syntax_Syntax.lid_as_fv proj
                       FStar_Syntax_Syntax.delta_equational
                       FStar_Pervasives_Native.None
                      in
                   FStar_Syntax_Syntax.fv_to_tm uu____4197  in
                 let uu____4198 =
                   let uu____4203 =
                     FStar_Syntax_Syntax.mk_Tm_uinst proj_tm
                       [FStar_Syntax_Syntax.U_zero]
                      in
                   let uu____4204 =
                     let uu____4205 =
                       let uu____4214 = type_of ea  in
                       FStar_Syntax_Syntax.iarg uu____4214  in
                     let uu____4215 =
                       let uu____4226 = FStar_Syntax_Syntax.as_arg cons_tm
                          in
                       [uu____4226]  in
                     uu____4205 :: uu____4215  in
                   FStar_Syntax_Syntax.mk_Tm_app uu____4203 uu____4204  in
                 uu____4198 FStar_Pervasives_Native.None rng  in
               let shadow_hd = map_shadow shadow_l (proj "hd")  in
               let shadow_tl = map_shadow shadow_l (proj "tl")  in
               let uu____4263 =
                 let uu____4268 =
                   let uu____4269 =
                     let uu____4280 =
                       let uu____4289 =
                         let uu____4290 = embed ea hd1  in
                         uu____4290 rng shadow_hd norm1  in
                       FStar_Syntax_Syntax.as_arg uu____4289  in
                     let uu____4297 =
                       let uu____4308 =
                         let uu____4317 = em tl1 rng shadow_tl norm1  in
                         FStar_Syntax_Syntax.as_arg uu____4317  in
                       [uu____4308]  in
                     uu____4280 :: uu____4297  in
                   t :: uu____4269  in
                 FStar_Syntax_Syntax.mk_Tm_app cons1 uu____4268  in
               uu____4263 FStar_Pervasives_Native.None rng)
       in
    let rec un t0 w norm1 =
      let t = FStar_Syntax_Util.unmeta_safe t0  in
      lazy_unembed printer emb_t_list_a t t_list_a
        (fun t1  ->
           let uu____4389 = FStar_Syntax_Util.head_and_args' t1  in
           match uu____4389 with
           | (hd1,args) ->
               let uu____4430 =
                 let uu____4443 =
                   let uu____4444 = FStar_Syntax_Util.un_uinst hd1  in
                   uu____4444.FStar_Syntax_Syntax.n  in
                 (uu____4443, args)  in
               (match uu____4430 with
                | (FStar_Syntax_Syntax.Tm_fvar fv,uu____4460) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.nil_lid
                    -> FStar_Pervasives_Native.Some []
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(uu____4480,FStar_Pervasives_Native.Some
                       (FStar_Syntax_Syntax.Implicit uu____4481))::(hd2,FStar_Pervasives_Native.None
                                                                    )::
                   (tl1,FStar_Pervasives_Native.None )::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.cons_lid
                    ->
                    let uu____4523 =
                      let uu____4526 = unembed ea hd2  in uu____4526 w norm1
                       in
                    FStar_Util.bind_opt uu____4523
                      (fun hd3  ->
                         let uu____4538 = un tl1 w norm1  in
                         FStar_Util.bind_opt uu____4538
                           (fun tl2  ->
                              FStar_Pervasives_Native.Some (hd3 :: tl2)))
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(hd2,FStar_Pervasives_Native.None )::(tl1,FStar_Pervasives_Native.None
                                                            )::[])
                    when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.cons_lid
                    ->
                    let uu____4586 =
                      let uu____4589 = unembed ea hd2  in uu____4589 w norm1
                       in
                    FStar_Util.bind_opt uu____4586
                      (fun hd3  ->
                         let uu____4601 = un tl1 w norm1  in
                         FStar_Util.bind_opt uu____4601
                           (fun tl2  ->
                              FStar_Pervasives_Native.Some (hd3 :: tl2)))
                | uu____4616 ->
                    (if w
                     then
                       (let uu____4631 =
                          let uu____4637 =
                            let uu____4639 =
                              FStar_Syntax_Print.term_to_string t0  in
                            FStar_Util.format1 "Not an embedded list: %s"
                              uu____4639
                             in
                          (FStar_Errors.Warning_NotEmbedded, uu____4637)  in
                        FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                          uu____4631)
                     else ();
                     FStar_Pervasives_Native.None)))
       in
    let uu____4647 =
      let uu____4648 = type_of ea  in
      FStar_Syntax_Syntax.t_list_of uu____4648  in
    mk_emb_full em un uu____4647 printer emb_t_list_a
  
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
    match projectee with | Simpl  -> true | uu____4691 -> false
  
let (uu___is_Weak : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Weak  -> true | uu____4702 -> false
  
let (uu___is_HNF : norm_step -> Prims.bool) =
  fun projectee  -> match projectee with | HNF  -> true | uu____4713 -> false 
let (uu___is_Primops : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____4724 -> false
  
let (uu___is_Delta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Delta  -> true | uu____4735 -> false
  
let (uu___is_Zeta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Zeta  -> true | uu____4746 -> false
  
let (uu___is_Iota : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Iota  -> true | uu____4757 -> false
  
let (uu___is_Reify : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____4768 -> false
  
let (uu___is_UnfoldOnly : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____4783 -> false
  
let (__proj__UnfoldOnly__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldFully : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldFully _0 -> true | uu____4814 -> false
  
let (__proj__UnfoldFully__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldFully _0 -> _0 
let (uu___is_UnfoldAttr : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____4845 -> false
  
let (__proj__UnfoldAttr__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_NBE : norm_step -> Prims.bool) =
  fun projectee  -> match projectee with | NBE  -> true | uu____4872 -> false 
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
    let uu____4890 =
      FStar_Ident.lid_of_str "FStar.Syntax.Embeddings.norm_step"  in
    FStar_Syntax_Util.fvar_const uu____4890  in
  let emb_t_norm_step =
    let uu____4893 =
      let uu____4901 =
        FStar_All.pipe_right FStar_Parser_Const.norm_step_lid
          FStar_Ident.string_of_lid
         in
      (uu____4901, [])  in
    FStar_Syntax_Syntax.ET_app uu____4893  in
  let printer uu____4913 = "norm_step"  in
  let em n1 rng _topt norm1 =
    lazy_embed printer emb_t_norm_step rng t_norm_step1 n1
      (fun uu____4939  ->
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
             let uu____4944 =
               let uu____4949 =
                 let uu____4950 =
                   let uu____4959 =
                     let uu____4960 =
                       let uu____4967 = e_list e_string  in
                       embed uu____4967 l  in
                     uu____4960 rng FStar_Pervasives_Native.None norm1  in
                   FStar_Syntax_Syntax.as_arg uu____4959  in
                 [uu____4950]  in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldOnly uu____4949  in
             uu____4944 FStar_Pervasives_Native.None rng
         | UnfoldFully l ->
             let uu____4999 =
               let uu____5004 =
                 let uu____5005 =
                   let uu____5014 =
                     let uu____5015 =
                       let uu____5022 = e_list e_string  in
                       embed uu____5022 l  in
                     uu____5015 rng FStar_Pervasives_Native.None norm1  in
                   FStar_Syntax_Syntax.as_arg uu____5014  in
                 [uu____5005]  in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldFully uu____5004  in
             uu____4999 FStar_Pervasives_Native.None rng
         | UnfoldAttr l ->
             let uu____5054 =
               let uu____5059 =
                 let uu____5060 =
                   let uu____5069 =
                     let uu____5070 =
                       let uu____5077 = e_list e_string  in
                       embed uu____5077 l  in
                     uu____5070 rng FStar_Pervasives_Native.None norm1  in
                   FStar_Syntax_Syntax.as_arg uu____5069  in
                 [uu____5060]  in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldAttr uu____5059  in
             uu____5054 FStar_Pervasives_Native.None rng)
     in
  let un t0 w norm1 =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    lazy_unembed printer emb_t_norm_step t t_norm_step1
      (fun t1  ->
         let uu____5137 = FStar_Syntax_Util.head_and_args t1  in
         match uu____5137 with
         | (hd1,args) ->
             let uu____5182 =
               let uu____5197 =
                 let uu____5198 = FStar_Syntax_Util.un_uinst hd1  in
                 uu____5198.FStar_Syntax_Syntax.n  in
               (uu____5197, args)  in
             (match uu____5182 with
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
              | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____5386)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldonly
                  ->
                  let uu____5421 =
                    let uu____5427 =
                      let uu____5437 = e_list e_string  in
                      unembed uu____5437 l  in
                    uu____5427 w norm1  in
                  FStar_Util.bind_opt uu____5421
                    (fun ss  ->
                       FStar_All.pipe_left
                         (fun _5457  -> FStar_Pervasives_Native.Some _5457)
                         (UnfoldOnly ss))
              | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____5460)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldfully
                  ->
                  let uu____5495 =
                    let uu____5501 =
                      let uu____5511 = e_list e_string  in
                      unembed uu____5511 l  in
                    uu____5501 w norm1  in
                  FStar_Util.bind_opt uu____5495
                    (fun ss  ->
                       FStar_All.pipe_left
                         (fun _5531  -> FStar_Pervasives_Native.Some _5531)
                         (UnfoldFully ss))
              | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____5534)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldattr
                  ->
                  let uu____5569 =
                    let uu____5575 =
                      let uu____5585 = e_list e_string  in
                      unembed uu____5585 l  in
                    uu____5575 w norm1  in
                  FStar_Util.bind_opt uu____5569
                    (fun ss  ->
                       FStar_All.pipe_left
                         (fun _5605  -> FStar_Pervasives_Native.Some _5605)
                         (UnfoldAttr ss))
              | uu____5606 ->
                  (if w
                   then
                     (let uu____5623 =
                        let uu____5629 =
                          let uu____5631 =
                            FStar_Syntax_Print.term_to_string t0  in
                          FStar_Util.format1 "Not an embedded norm_step: %s"
                            uu____5631
                           in
                        (FStar_Errors.Warning_NotEmbedded, uu____5629)  in
                      FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                        uu____5623)
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
    | uu____5691 ->
        (if w
         then
           (let uu____5694 =
              let uu____5700 =
                let uu____5702 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded range: %s" uu____5702  in
              (FStar_Errors.Warning_NotEmbedded, uu____5700)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____5694)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____5708 =
    let uu____5709 =
      let uu____5717 =
        FStar_All.pipe_right FStar_Parser_Const.range_lid
          FStar_Ident.string_of_lid
         in
      (uu____5717, [])  in
    FStar_Syntax_Syntax.ET_app uu____5709  in
  mk_emb_full em un FStar_Syntax_Syntax.t_range FStar_Range.string_of_range
    uu____5708
  
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
        let uu____5788 =
          let uu____5795 =
            let uu____5796 =
              let uu____5811 =
                let uu____5820 =
                  let uu____5827 = FStar_Syntax_Syntax.null_bv ea.typ  in
                  (uu____5827, FStar_Pervasives_Native.None)  in
                [uu____5820]  in
              let uu____5842 = FStar_Syntax_Syntax.mk_Total eb.typ  in
              (uu____5811, uu____5842)  in
            FStar_Syntax_Syntax.Tm_arrow uu____5796  in
          FStar_Syntax_Syntax.mk uu____5795  in
        uu____5788 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
      let emb_t_arr_a_b =
        FStar_Syntax_Syntax.ET_fun ((ea.emb_typ), (eb.emb_typ))  in
      let printer f = "<fun>"  in
      let em f rng shadow_f norm1 =
        lazy_embed (fun uu____5914  -> "<fun>") emb_t_arr_a_b rng t_arrow f
          (fun uu____5920  ->
             let uu____5921 = force_shadow shadow_f  in
             match uu____5921 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Exn.raise Embedding_failure
             | FStar_Pervasives_Native.Some repr_f ->
                 ((let uu____5926 =
                     FStar_ST.op_Bang FStar_Options.debug_embedding  in
                   if uu____5926
                   then
                     let uu____5950 =
                       FStar_Syntax_Print.term_to_string repr_f  in
                     let uu____5952 = FStar_Util.stack_dump ()  in
                     FStar_Util.print2
                       "e_arrow forced back to term using shadow %s; repr=%s\n"
                       uu____5950 uu____5952
                   else ());
                  (let res = norm1 (FStar_Util.Inr repr_f)  in
                   (let uu____5959 =
                      FStar_ST.op_Bang FStar_Options.debug_embedding  in
                    if uu____5959
                    then
                      let uu____5983 =
                        FStar_Syntax_Print.term_to_string repr_f  in
                      let uu____5985 = FStar_Syntax_Print.term_to_string res
                         in
                      let uu____5987 = FStar_Util.stack_dump ()  in
                      FStar_Util.print3
                        "e_arrow forced back to term using shadow %s; repr=%s\n\t%s\n"
                        uu____5983 uu____5985 uu____5987
                    else ());
                   res)))
         in
      let un f w norm1 =
        lazy_unembed printer emb_t_arr_a_b f t_arrow
          (fun f1  ->
             let f_wrapped a =
               (let uu____6046 =
                  FStar_ST.op_Bang FStar_Options.debug_embedding  in
                if uu____6046
                then
                  let uu____6070 = FStar_Syntax_Print.term_to_string f1  in
                  let uu____6072 = FStar_Util.stack_dump ()  in
                  FStar_Util.print2
                    "Calling back into normalizer for %s\n%s\n" uu____6070
                    uu____6072
                else ());
               (let a_tm =
                  let uu____6078 = embed ea a  in
                  uu____6078 f1.FStar_Syntax_Syntax.pos
                    FStar_Pervasives_Native.None norm1
                   in
                let b_tm =
                  let uu____6088 =
                    let uu____6093 =
                      let uu____6094 =
                        let uu____6099 =
                          let uu____6100 = FStar_Syntax_Syntax.as_arg a_tm
                             in
                          [uu____6100]  in
                        FStar_Syntax_Syntax.mk_Tm_app f1 uu____6099  in
                      uu____6094 FStar_Pervasives_Native.None
                        f1.FStar_Syntax_Syntax.pos
                       in
                    FStar_Util.Inr uu____6093  in
                  norm1 uu____6088  in
                let uu____6125 =
                  let uu____6128 = unembed eb b_tm  in uu____6128 w norm1  in
                match uu____6125 with
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
                let uu____6222 = FStar_List.splitAt n_tvars args  in
                match uu____6222 with
                | (_tvar_args,rest_args) ->
                    let uu____6299 = FStar_List.hd rest_args  in
                    (match uu____6299 with
                     | (x,uu____6319) ->
                         let shadow_app =
                           let uu____6333 =
                             FStar_Thunk.mk
                               (fun uu____6340  ->
                                  let uu____6341 =
                                    let uu____6346 =
                                      norm1 (FStar_Util.Inl fv_lid1)  in
                                    FStar_Syntax_Syntax.mk_Tm_app uu____6346
                                      args
                                     in
                                  uu____6341 FStar_Pervasives_Native.None rng)
                              in
                           FStar_Pervasives_Native.Some uu____6333  in
                         let uu____6349 =
                           let uu____6352 =
                             let uu____6355 = unembed ea x  in
                             uu____6355 true norm1  in
                           FStar_Util.map_opt uu____6352
                             (fun x1  ->
                                let uu____6366 =
                                  let uu____6373 = f x1  in
                                  embed eb uu____6373  in
                                uu____6366 rng shadow_app norm1)
                            in
                         (match uu____6349 with
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
                  let uu____6476 = FStar_List.splitAt n_tvars args  in
                  match uu____6476 with
                  | (_tvar_args,rest_args) ->
                      let uu____6539 = FStar_List.hd rest_args  in
                      (match uu____6539 with
                       | (x,uu____6555) ->
                           let uu____6560 =
                             let uu____6567 = FStar_List.tl rest_args  in
                             FStar_List.hd uu____6567  in
                           (match uu____6560 with
                            | (y,uu____6591) ->
                                let shadow_app =
                                  let uu____6601 =
                                    FStar_Thunk.mk
                                      (fun uu____6608  ->
                                         let uu____6609 =
                                           let uu____6614 =
                                             norm1 (FStar_Util.Inl fv_lid1)
                                              in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____6614 args
                                            in
                                         uu____6609
                                           FStar_Pervasives_Native.None rng)
                                     in
                                  FStar_Pervasives_Native.Some uu____6601  in
                                let uu____6617 =
                                  let uu____6620 =
                                    let uu____6623 = unembed ea x  in
                                    uu____6623 true norm1  in
                                  FStar_Util.bind_opt uu____6620
                                    (fun x1  ->
                                       let uu____6634 =
                                         let uu____6637 = unembed eb y  in
                                         uu____6637 true norm1  in
                                       FStar_Util.bind_opt uu____6634
                                         (fun y1  ->
                                            let uu____6648 =
                                              let uu____6649 =
                                                let uu____6656 = f x1 y1  in
                                                embed ec uu____6656  in
                                              uu____6649 rng shadow_app norm1
                                               in
                                            FStar_Pervasives_Native.Some
                                              uu____6648))
                                   in
                                (match uu____6617 with
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
                    let uu____6778 = FStar_List.splitAt n_tvars args  in
                    match uu____6778 with
                    | (_tvar_args,rest_args) ->
                        let uu____6841 = FStar_List.hd rest_args  in
                        (match uu____6841 with
                         | (x,uu____6857) ->
                             let uu____6862 =
                               let uu____6869 = FStar_List.tl rest_args  in
                               FStar_List.hd uu____6869  in
                             (match uu____6862 with
                              | (y,uu____6893) ->
                                  let uu____6898 =
                                    let uu____6905 =
                                      let uu____6914 =
                                        FStar_List.tl rest_args  in
                                      FStar_List.tl uu____6914  in
                                    FStar_List.hd uu____6905  in
                                  (match uu____6898 with
                                   | (z,uu____6944) ->
                                       let shadow_app =
                                         let uu____6954 =
                                           FStar_Thunk.mk
                                             (fun uu____6961  ->
                                                let uu____6962 =
                                                  let uu____6967 =
                                                    norm1
                                                      (FStar_Util.Inl fv_lid1)
                                                     in
                                                  FStar_Syntax_Syntax.mk_Tm_app
                                                    uu____6967 args
                                                   in
                                                uu____6962
                                                  FStar_Pervasives_Native.None
                                                  rng)
                                            in
                                         FStar_Pervasives_Native.Some
                                           uu____6954
                                          in
                                       let uu____6970 =
                                         let uu____6973 =
                                           let uu____6976 = unembed ea x  in
                                           uu____6976 true norm1  in
                                         FStar_Util.bind_opt uu____6973
                                           (fun x1  ->
                                              let uu____6987 =
                                                let uu____6990 = unembed eb y
                                                   in
                                                uu____6990 true norm1  in
                                              FStar_Util.bind_opt uu____6987
                                                (fun y1  ->
                                                   let uu____7001 =
                                                     let uu____7004 =
                                                       unembed ec z  in
                                                     uu____7004 true norm1
                                                      in
                                                   FStar_Util.bind_opt
                                                     uu____7001
                                                     (fun z1  ->
                                                        let uu____7015 =
                                                          let uu____7016 =
                                                            let uu____7023 =
                                                              f x1 y1 z1  in
                                                            embed ed
                                                              uu____7023
                                                             in
                                                          uu____7016 rng
                                                            shadow_app norm1
                                                           in
                                                        FStar_Pervasives_Native.Some
                                                          uu____7015)))
                                          in
                                       (match uu____6970 with
                                        | FStar_Pervasives_Native.Some x1 ->
                                            FStar_Pervasives_Native.Some x1
                                        | FStar_Pervasives_Native.None  ->
                                            force_shadow shadow_app))))
                     in
                  f_wrapped
  
let debug_wrap : 'a . Prims.string -> (unit -> 'a) -> 'a =
  fun s  ->
    fun f  ->
      (let uu____7053 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
       if uu____7053 then FStar_Util.print1 "++++starting %s\n" s else ());
      (let res = f ()  in
       (let uu____7082 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
        if uu____7082 then FStar_Util.print1 "------ending %s\n" s else ());
       res)
  