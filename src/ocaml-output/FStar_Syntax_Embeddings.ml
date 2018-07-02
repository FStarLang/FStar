open Prims
type norm_cb =
  (FStar_Ident.lid,FStar_Syntax_Syntax.term) FStar_Util.either ->
    FStar_Syntax_Syntax.term
let (id_norm_cb : norm_cb) =
  fun uu___205_13  ->
    match uu___205_13 with
    | FStar_Util.Inr x -> x
    | FStar_Util.Inl l ->
        let uu____20 =
          FStar_Syntax_Syntax.lid_as_fv l
            FStar_Syntax_Syntax.delta_equational FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.fv_to_tm uu____20
  
exception Embedding_failure 
let (uu___is_Embedding_failure : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Embedding_failure  -> true | uu____26 -> false
  
exception Unembedding_failure 
let (uu___is_Unembedding_failure : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unembedding_failure  -> true | uu____32 -> false
  
type shadow_term =
  FStar_Syntax_Syntax.term FStar_Common.thunk FStar_Pervasives_Native.option
let (map_shadow :
  shadow_term ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> shadow_term)
  =
  fun s  ->
    fun f  ->
      FStar_Util.map_opt s
        (fun s1  ->
           FStar_Common.mk_thunk
             (fun uu____196  ->
                let uu____197 = FStar_Common.force_thunk s1  in f uu____197))
  
let (force_shadow :
  shadow_term -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option) =
  fun s  -> FStar_Util.map_opt s FStar_Common.force_thunk 
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
    match projectee with
    | { em = __fname__em; un = __fname__un; typ = __fname__typ;
        print = __fname__print; emb_typ = __fname__emb_typ;_} -> __fname__em
  
let __proj__Mkembedding__item__un :
  'a . 'a embedding -> FStar_Syntax_Syntax.term -> 'a unembed_t =
  fun projectee  ->
    match projectee with
    | { em = __fname__em; un = __fname__un; typ = __fname__typ;
        print = __fname__print; emb_typ = __fname__emb_typ;_} -> __fname__un
  
let __proj__Mkembedding__item__typ :
  'a . 'a embedding -> FStar_Syntax_Syntax.typ =
  fun projectee  ->
    match projectee with
    | { em = __fname__em; un = __fname__un; typ = __fname__typ;
        print = __fname__print; emb_typ = __fname__emb_typ;_} -> __fname__typ
  
let __proj__Mkembedding__item__print : 'a . 'a embedding -> 'a printer =
  fun projectee  ->
    match projectee with
    | { em = __fname__em; un = __fname__un; typ = __fname__typ;
        print = __fname__print; emb_typ = __fname__emb_typ;_} ->
        __fname__print
  
let __proj__Mkembedding__item__emb_typ :
  'a . 'a embedding -> FStar_Syntax_Syntax.emb_typ =
  fun projectee  ->
    match projectee with
    | { em = __fname__em; un = __fname__un; typ = __fname__typ;
        print = __fname__print; emb_typ = __fname__emb_typ;_} ->
        __fname__emb_typ
  
let emb_typ_of : 'a . 'a embedding -> FStar_Syntax_Syntax.emb_typ =
  fun e  -> e.emb_typ 
let unknown_printer :
  'Auu____821 . FStar_Syntax_Syntax.term -> 'Auu____821 -> Prims.string =
  fun typ  ->
    fun uu____831  ->
      let uu____832 = FStar_Syntax_Print.term_to_string typ  in
      FStar_Util.format1 "unknown %s" uu____832
  
let (term_as_fv : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.fv) =
  fun t  ->
    let uu____838 =
      let uu____839 = FStar_Syntax_Subst.compress t  in
      uu____839.FStar_Syntax_Syntax.n  in
    match uu____838 with
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv
    | uu____843 ->
        let uu____844 =
          let uu____845 = FStar_Syntax_Print.term_to_string t  in
          FStar_Util.format1 "Embeddings not defined for type %s" uu____845
           in
        failwith uu____844
  
let mk_emb :
  'a .
    'a raw_embedder ->
      'a raw_unembedder -> FStar_Syntax_Syntax.fv -> 'a embedding
  =
  fun em  ->
    fun un  ->
      fun fv  ->
        let typ = FStar_Syntax_Syntax.fv_to_tm fv  in
        let uu____970 =
          let uu____971 =
            let uu____978 =
              let uu____979 = FStar_Syntax_Syntax.lid_of_fv fv  in
              FStar_All.pipe_right uu____979 FStar_Ident.string_of_lid  in
            (uu____978, [])  in
          FStar_Syntax_Syntax.ET_app uu____971  in
        { em; un; typ; print = (unknown_printer typ); emb_typ = uu____970 }
  
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
    fun t  -> fun n1  -> let uu____1381 = unembed e t  in uu____1381 true n1
  
let try_unembed :
  'a .
    'a embedding ->
      FStar_Syntax_Syntax.term ->
        norm_cb -> 'a FStar_Pervasives_Native.option
  =
  fun e  ->
    fun t  -> fun n1  -> let uu____1428 = unembed e t  in uu____1428 false n1
  
let type_of : 'a . 'a embedding -> FStar_Syntax_Syntax.typ = fun e  -> e.typ 
let set_type : 'a . FStar_Syntax_Syntax.typ -> 'a embedding -> 'a embedding =
  fun ty  ->
    fun e  ->
      let uu___208_1478 = e  in
      {
        em = (uu___208_1478.em);
        un = (uu___208_1478.un);
        typ = ty;
        print = (uu___208_1478.print);
        emb_typ = (uu___208_1478.emb_typ)
      }
  
let rec (emb_typ_to_string : FStar_Syntax_Syntax.emb_typ -> Prims.string) =
  fun uu___206_1485  ->
    match uu___206_1485 with
    | FStar_Syntax_Syntax.ET_abstract  -> "abstract"
    | FStar_Syntax_Syntax.ET_app (h,[]) -> h
    | FStar_Syntax_Syntax.ET_app (h,args) ->
        let uu____1495 =
          let uu____1496 =
            let uu____1497 =
              let uu____1498 =
                let uu____1499 = FStar_List.map emb_typ_to_string args  in
                FStar_All.pipe_right uu____1499 (FStar_String.concat " ")  in
              Prims.strcat uu____1498 ")"  in
            Prims.strcat " " uu____1497  in
          Prims.strcat h uu____1496  in
        Prims.strcat "(" uu____1495
    | FStar_Syntax_Syntax.ET_fun (a,b) ->
        let uu____1506 =
          let uu____1507 = emb_typ_to_string a  in
          let uu____1508 =
            let uu____1509 = emb_typ_to_string b  in
            Prims.strcat ") -> " uu____1509  in
          Prims.strcat uu____1507 uu____1508  in
        Prims.strcat "(" uu____1506
  
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
              (let uu____1575 =
                 FStar_ST.op_Bang FStar_Options.debug_embedding  in
               if uu____1575
               then
                 let uu____1595 = FStar_Syntax_Print.term_to_string ta  in
                 let uu____1596 = emb_typ_to_string et  in
                 let uu____1597 = pa x  in
                 FStar_Util.print3
                   "Embedding a %s\n\temb_typ=%s\n\tvalue is %s\n" uu____1595
                   uu____1596 uu____1597
               else ());
              (let uu____1601 = FStar_Options.eager_embedding ()  in
               if uu____1601
               then f ()
               else
                 (let thunk = FStar_Common.mk_thunk f  in
                  let uu____1612 =
                    let uu____1619 =
                      let uu____1620 =
                        let uu____1621 = FStar_Dyn.mkdyn x  in
                        {
                          FStar_Syntax_Syntax.blob = uu____1621;
                          FStar_Syntax_Syntax.lkind =
                            (FStar_Syntax_Syntax.Lazy_embedding (et, thunk));
                          FStar_Syntax_Syntax.ltyp = FStar_Syntax_Syntax.tun;
                          FStar_Syntax_Syntax.rng = rng
                        }  in
                      FStar_Syntax_Syntax.Tm_lazy uu____1620  in
                    FStar_Syntax_Syntax.mk uu____1619  in
                  uu____1612 FStar_Pervasives_Native.None rng))
  
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
                  FStar_Syntax_Syntax.ltyp = uu____1736;
                  FStar_Syntax_Syntax.rng = uu____1737;_}
                ->
                let uu____1748 =
                  (FStar_Options.eager_embedding ()) || (et <> et')  in
                if uu____1748
                then
                  ((let uu____1752 =
                      FStar_ST.op_Bang FStar_Options.debug_embedding  in
                    if uu____1752
                    then
                      let uu____1772 = emb_typ_to_string et  in
                      let uu____1773 = emb_typ_to_string et'  in
                      let uu____1774 =
                        let uu____1775 = FStar_Dyn.undyn b  in pa uu____1775
                         in
                      FStar_Util.print3
                        "Unembed cancellation failed\n\t%s <> %s\n\tvalue is %s\n"
                        uu____1772 uu____1773 uu____1774
                    else ());
                   (let aopt =
                      let uu____1782 = FStar_Common.force_thunk t  in
                      f uu____1782  in
                    let uu____1825 = FStar_Common.force_thunk t  in
                    f uu____1825))
                else
                  (let a = FStar_Dyn.undyn b  in
                   (let uu____1871 =
                      FStar_ST.op_Bang FStar_Options.debug_embedding  in
                    if uu____1871
                    then
                      let uu____1891 = emb_typ_to_string et  in
                      let uu____1892 = pa a  in
                      FStar_Util.print2
                        "Unembed cancelled for %s\n\tvalue is %s\n"
                        uu____1891 uu____1892
                    else ());
                   FStar_Pervasives_Native.Some a)
            | uu____1896 ->
                let aopt = f x1  in
                ((let uu____1901 =
                    FStar_ST.op_Bang FStar_Options.debug_embedding  in
                  if uu____1901
                  then
                    let uu____1921 = emb_typ_to_string et  in
                    let uu____1922 =
                      match aopt with
                      | FStar_Pervasives_Native.None  -> "None"
                      | FStar_Pervasives_Native.Some a ->
                          let uu____1924 = pa a  in
                          Prims.strcat "Some " uu____1924
                       in
                    FStar_Util.print2
                      "Unembedding:\n\temb_typ=%s\n\tvalue is %s\n"
                      uu____1921 uu____1922
                  else ());
                 aopt)
  
let (mk_any_emb :
  FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term embedding) =
  fun typ  ->
    let em t _r _topt _norm =
      (let uu____1999 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
       if uu____1999
       then
         let uu____2019 = unknown_printer typ t  in
         FStar_Util.print1 "Embedding abstract: %s\n" uu____2019
       else ());
      t  in
    let un t _w _n =
      (let uu____2044 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
       if uu____2044
       then
         let uu____2064 = unknown_printer typ t  in
         FStar_Util.print1 "Unembedding abstract: %s\n" uu____2064
       else ());
      FStar_Pervasives_Native.Some t  in
    mk_emb_full em un typ (unknown_printer typ)
      FStar_Syntax_Syntax.ET_abstract
  
let (e_any : FStar_Syntax_Syntax.term embedding) =
  let em t _r _topt _norm = t  in
  let un t _w _n = FStar_Pervasives_Native.Some t  in
  let uu____2153 =
    let uu____2154 =
      let uu____2161 =
        FStar_All.pipe_right FStar_Parser_Const.term_lid
          FStar_Ident.string_of_lid
         in
      (uu____2161, [])  in
    FStar_Syntax_Syntax.ET_app uu____2154  in
  mk_emb_full em un FStar_Syntax_Syntax.t_term
    FStar_Syntax_Print.term_to_string uu____2153
  
let (e_unit : unit embedding) =
  let em u rng _topt _norm =
    let uu___209_2229 = FStar_Syntax_Util.exp_unit  in
    {
      FStar_Syntax_Syntax.n = (uu___209_2229.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___209_2229.FStar_Syntax_Syntax.vars)
    }  in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unascribe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit ) ->
        FStar_Pervasives_Native.Some ()
    | uu____2257 ->
        (if w
         then
           (let uu____2259 =
              let uu____2264 =
                let uu____2265 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded unit: %s" uu____2265  in
              (FStar_Errors.Warning_NotEmbedded, uu____2264)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____2259)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____2267 =
    let uu____2268 =
      let uu____2275 =
        FStar_All.pipe_right FStar_Parser_Const.unit_lid
          FStar_Ident.string_of_lid
         in
      (uu____2275, [])  in
    FStar_Syntax_Syntax.ET_app uu____2268  in
  mk_emb_full em un FStar_Syntax_Syntax.t_unit (fun uu____2279  -> "()")
    uu____2267
  
let (e_bool : Prims.bool embedding) =
  let em b rng _topt _norm =
    let t =
      if b
      then FStar_Syntax_Util.exp_true_bool
      else FStar_Syntax_Util.exp_false_bool  in
    let uu___210_2351 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___210_2351.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___210_2351.FStar_Syntax_Syntax.vars)
    }  in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) ->
        FStar_Pervasives_Native.Some b
    | uu____2382 ->
        (if w
         then
           (let uu____2384 =
              let uu____2389 =
                let uu____2390 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded bool: %s" uu____2390  in
              (FStar_Errors.Warning_NotEmbedded, uu____2389)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____2384)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____2392 =
    let uu____2393 =
      let uu____2400 =
        FStar_All.pipe_right FStar_Parser_Const.bool_lid
          FStar_Ident.string_of_lid
         in
      (uu____2400, [])  in
    FStar_Syntax_Syntax.ET_app uu____2393  in
  mk_emb_full em un FStar_Syntax_Syntax.t_bool FStar_Util.string_of_bool
    uu____2392
  
let (e_char : FStar_Char.char embedding) =
  let em c rng _topt _norm =
    let t = FStar_Syntax_Util.exp_char c  in
    let uu___211_2472 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___211_2472.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___211_2472.FStar_Syntax_Syntax.vars)
    }  in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c) ->
        FStar_Pervasives_Native.Some c
    | uu____2506 ->
        (if w
         then
           (let uu____2508 =
              let uu____2513 =
                let uu____2514 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded char: %s" uu____2514  in
              (FStar_Errors.Warning_NotEmbedded, uu____2513)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____2508)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____2517 =
    let uu____2518 =
      let uu____2525 =
        FStar_All.pipe_right FStar_Parser_Const.char_lid
          FStar_Ident.string_of_lid
         in
      (uu____2525, [])  in
    FStar_Syntax_Syntax.ET_app uu____2518  in
  mk_emb_full em un FStar_Syntax_Syntax.t_char FStar_Util.string_of_char
    uu____2517
  
let (e_int : FStar_BigInt.t embedding) =
  let t_int1 = FStar_Syntax_Util.fvar_const FStar_Parser_Const.int_lid  in
  let emb_t_int =
    let uu____2533 =
      let uu____2540 =
        FStar_All.pipe_right FStar_Parser_Const.int_lid
          FStar_Ident.string_of_lid
         in
      (uu____2540, [])  in
    FStar_Syntax_Syntax.ET_app uu____2533  in
  let em i rng _topt _norm =
    lazy_embed FStar_BigInt.string_of_big_int emb_t_int rng t_int1 i
      (fun uu____2608  ->
         let uu____2609 = FStar_BigInt.string_of_big_int i  in
         FStar_Syntax_Util.exp_int uu____2609)
     in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    lazy_unembed FStar_BigInt.string_of_big_int emb_t_int t t_int1
      (fun t1  ->
         match t1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
             (s,uu____2643)) ->
             let uu____2656 = FStar_BigInt.big_int_of_string s  in
             FStar_Pervasives_Native.Some uu____2656
         | uu____2657 ->
             (if w
              then
                (let uu____2659 =
                   let uu____2664 =
                     let uu____2665 = FStar_Syntax_Print.term_to_string t0
                        in
                     FStar_Util.format1 "Not an embedded int: %s" uu____2665
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____2664)  in
                 FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____2659)
              else ();
              FStar_Pervasives_Native.None))
     in
  mk_emb_full em un FStar_Syntax_Syntax.t_int FStar_BigInt.string_of_big_int
    emb_t_int
  
let (e_string : Prims.string embedding) =
  let emb_t_string =
    let uu____2670 =
      let uu____2677 =
        FStar_All.pipe_right FStar_Parser_Const.string_lid
          FStar_Ident.string_of_lid
         in
      (uu____2677, [])  in
    FStar_Syntax_Syntax.ET_app uu____2670  in
  let em s rng _topt _norm =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, rng)))
      FStar_Pervasives_Native.None rng
     in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
        (s,uu____2771)) -> FStar_Pervasives_Native.Some s
    | uu____2772 ->
        (if w
         then
           (let uu____2774 =
              let uu____2779 =
                let uu____2780 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded string: %s" uu____2780
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____2779)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____2774)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb_full em un FStar_Syntax_Syntax.t_string
    (fun x  -> Prims.strcat "\"" (Prims.strcat x "\"")) emb_t_string
  
let e_option :
  'a . 'a embedding -> 'a FStar_Pervasives_Native.option embedding =
  fun ea  ->
    let t_option_a =
      let t_opt = FStar_Syntax_Util.fvar_const FStar_Parser_Const.option_lid
         in
      let uu____2806 =
        let uu____2811 =
          let uu____2812 = FStar_Syntax_Syntax.as_arg ea.typ  in [uu____2812]
           in
        FStar_Syntax_Syntax.mk_Tm_app t_opt uu____2811  in
      uu____2806 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
    let emb_t_option_a =
      let uu____2840 =
        let uu____2847 =
          FStar_All.pipe_right FStar_Parser_Const.option_lid
            FStar_Ident.string_of_lid
           in
        (uu____2847, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____2840  in
    let printer uu___207_2857 =
      match uu___207_2857 with
      | FStar_Pervasives_Native.None  -> "None"
      | FStar_Pervasives_Native.Some x ->
          let uu____2861 =
            let uu____2862 = ea.print x  in Prims.strcat uu____2862 ")"  in
          Prims.strcat "(Some " uu____2861
       in
    let em o rng topt norm1 =
      lazy_embed printer emb_t_option_a rng t_option_a o
        (fun uu____2936  ->
           match o with
           | FStar_Pervasives_Native.None  ->
               let uu____2937 =
                 let uu____2942 =
                   let uu____2943 =
                     FStar_Syntax_Syntax.tdataconstr
                       FStar_Parser_Const.none_lid
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____2943
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 let uu____2944 =
                   let uu____2945 =
                     let uu____2954 = type_of ea  in
                     FStar_Syntax_Syntax.iarg uu____2954  in
                   [uu____2945]  in
                 FStar_Syntax_Syntax.mk_Tm_app uu____2942 uu____2944  in
               uu____2937 FStar_Pervasives_Native.None rng
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
                        let uu____3043 =
                          FStar_Syntax_Syntax.lid_as_fv some_v
                            FStar_Syntax_Syntax.delta_equational
                            FStar_Pervasives_Native.None
                           in
                        FStar_Syntax_Syntax.fv_to_tm uu____3043  in
                      let uu____3044 =
                        let uu____3049 =
                          FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm
                            [FStar_Syntax_Syntax.U_zero]
                           in
                        let uu____3050 =
                          let uu____3051 =
                            let uu____3060 = type_of ea  in
                            FStar_Syntax_Syntax.iarg uu____3060  in
                          let uu____3061 =
                            let uu____3072 = FStar_Syntax_Syntax.as_arg t  in
                            [uu____3072]  in
                          uu____3051 :: uu____3061  in
                        FStar_Syntax_Syntax.mk_Tm_app uu____3049 uu____3050
                         in
                      uu____3044 FStar_Pervasives_Native.None rng)
                  in
               let uu____3107 =
                 let uu____3112 =
                   let uu____3113 =
                     FStar_Syntax_Syntax.tdataconstr
                       FStar_Parser_Const.some_lid
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____3113
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 let uu____3114 =
                   let uu____3115 =
                     let uu____3124 = type_of ea  in
                     FStar_Syntax_Syntax.iarg uu____3124  in
                   let uu____3125 =
                     let uu____3136 =
                       let uu____3145 =
                         let uu____3146 = embed ea a  in
                         uu____3146 rng shadow_a norm1  in
                       FStar_Syntax_Syntax.as_arg uu____3145  in
                     [uu____3136]  in
                   uu____3115 :: uu____3125  in
                 FStar_Syntax_Syntax.mk_Tm_app uu____3112 uu____3114  in
               uu____3107 FStar_Pervasives_Native.None rng)
       in
    let un t0 w norm1 =
      let t = FStar_Syntax_Util.unmeta_safe t0  in
      lazy_unembed printer emb_t_option_a t t_option_a
        (fun t1  ->
           let uu____3281 = FStar_Syntax_Util.head_and_args' t1  in
           match uu____3281 with
           | (hd1,args) ->
               let uu____3322 =
                 let uu____3337 =
                   let uu____3338 = FStar_Syntax_Util.un_uinst hd1  in
                   uu____3338.FStar_Syntax_Syntax.n  in
                 (uu____3337, args)  in
               (match uu____3322 with
                | (FStar_Syntax_Syntax.Tm_fvar fv,uu____3356) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.none_lid
                    ->
                    FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,uu____3380::(a,uu____3382)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.some_lid
                    ->
                    let uu____3433 =
                      let uu____3436 = unembed ea a  in uu____3436 w norm1
                       in
                    FStar_Util.bind_opt uu____3433
                      (fun a1  ->
                         FStar_Pervasives_Native.Some
                           (FStar_Pervasives_Native.Some a1))
                | uu____3455 ->
                    (if w
                     then
                       (let uu____3471 =
                          let uu____3476 =
                            let uu____3477 =
                              FStar_Syntax_Print.term_to_string t0  in
                            FStar_Util.format1 "Not an embedded option: %s"
                              uu____3477
                             in
                          (FStar_Errors.Warning_NotEmbedded, uu____3476)  in
                        FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                          uu____3471)
                     else ();
                     FStar_Pervasives_Native.None)))
       in
    let uu____3481 =
      let uu____3482 = type_of ea  in
      FStar_Syntax_Syntax.t_option_of uu____3482  in
    mk_emb_full em un uu____3481 printer emb_t_option_a
  
let e_tuple2 :
  'a 'b .
    'a embedding ->
      'b embedding -> ('a,'b) FStar_Pervasives_Native.tuple2 embedding
  =
  fun ea  ->
    fun eb  ->
      let t_pair_a_b =
        let t_tup2 =
          FStar_Syntax_Util.fvar_const FStar_Parser_Const.lid_tuple2  in
        let uu____3523 =
          let uu____3528 =
            let uu____3529 = FStar_Syntax_Syntax.as_arg ea.typ  in
            let uu____3538 =
              let uu____3549 = FStar_Syntax_Syntax.as_arg eb.typ  in
              [uu____3549]  in
            uu____3529 :: uu____3538  in
          FStar_Syntax_Syntax.mk_Tm_app t_tup2 uu____3528  in
        uu____3523 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
      let emb_t_pair_a_b =
        let uu____3585 =
          let uu____3592 =
            FStar_All.pipe_right FStar_Parser_Const.lid_tuple2
              FStar_Ident.string_of_lid
             in
          (uu____3592, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____3585  in
      let printer uu____3604 =
        match uu____3604 with
        | (x,y) ->
            let uu____3611 = ea.print x  in
            let uu____3612 = eb.print y  in
            FStar_Util.format2 "(%s, %s)" uu____3611 uu____3612
         in
      let em x rng topt norm1 =
        lazy_embed printer emb_t_pair_a_b rng t_pair_a_b x
          (fun uu____3695  ->
             let proj i ab =
               let uu____3709 =
                 let uu____3714 =
                   FStar_Parser_Const.mk_tuple_data_lid (Prims.parse_int "2")
                     rng
                    in
                 let uu____3715 =
                   FStar_Syntax_Syntax.null_bv FStar_Syntax_Syntax.tun  in
                 FStar_Syntax_Util.mk_field_projector_name uu____3714
                   uu____3715 i
                  in
               match uu____3709 with
               | (proj_1,uu____3719) ->
                   let proj_1_tm =
                     let uu____3721 =
                       FStar_Syntax_Syntax.lid_as_fv proj_1
                         FStar_Syntax_Syntax.delta_equational
                         FStar_Pervasives_Native.None
                        in
                     FStar_Syntax_Syntax.fv_to_tm uu____3721  in
                   let uu____3722 =
                     let uu____3727 =
                       FStar_Syntax_Syntax.mk_Tm_uinst proj_1_tm
                         [FStar_Syntax_Syntax.U_zero]
                        in
                     let uu____3728 =
                       let uu____3729 =
                         let uu____3738 = type_of ea  in
                         FStar_Syntax_Syntax.iarg uu____3738  in
                       let uu____3739 =
                         let uu____3750 =
                           let uu____3759 = type_of eb  in
                           FStar_Syntax_Syntax.iarg uu____3759  in
                         let uu____3760 =
                           let uu____3771 = FStar_Syntax_Syntax.as_arg ab  in
                           [uu____3771]  in
                         uu____3750 :: uu____3760  in
                       uu____3729 :: uu____3739  in
                     FStar_Syntax_Syntax.mk_Tm_app uu____3727 uu____3728  in
                   uu____3722 FStar_Pervasives_Native.None rng
                in
             let shadow_a = map_shadow topt (proj (Prims.parse_int "1"))  in
             let shadow_b = map_shadow topt (proj (Prims.parse_int "2"))  in
             let uu____3930 =
               let uu____3935 =
                 let uu____3936 =
                   FStar_Syntax_Syntax.tdataconstr
                     FStar_Parser_Const.lid_Mktuple2
                    in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu____3936
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                  in
               let uu____3937 =
                 let uu____3938 =
                   let uu____3947 = type_of ea  in
                   FStar_Syntax_Syntax.iarg uu____3947  in
                 let uu____3948 =
                   let uu____3959 =
                     let uu____3968 = type_of eb  in
                     FStar_Syntax_Syntax.iarg uu____3968  in
                   let uu____3969 =
                     let uu____3980 =
                       let uu____3989 =
                         let uu____3990 =
                           embed ea (FStar_Pervasives_Native.fst x)  in
                         uu____3990 rng shadow_a norm1  in
                       FStar_Syntax_Syntax.as_arg uu____3989  in
                     let uu____4060 =
                       let uu____4071 =
                         let uu____4080 =
                           let uu____4081 =
                             embed eb (FStar_Pervasives_Native.snd x)  in
                           uu____4081 rng shadow_b norm1  in
                         FStar_Syntax_Syntax.as_arg uu____4080  in
                       [uu____4071]  in
                     uu____3980 :: uu____4060  in
                   uu____3959 :: uu____3969  in
                 uu____3938 :: uu____3948  in
               FStar_Syntax_Syntax.mk_Tm_app uu____3935 uu____3937  in
             uu____3930 FStar_Pervasives_Native.None rng)
         in
      let un t0 w norm1 =
        let t = FStar_Syntax_Util.unmeta_safe t0  in
        lazy_unembed printer emb_t_pair_a_b t t_pair_a_b
          (fun t1  ->
             let uu____4244 = FStar_Syntax_Util.head_and_args' t1  in
             match uu____4244 with
             | (hd1,args) ->
                 let uu____4287 =
                   let uu____4300 =
                     let uu____4301 = FStar_Syntax_Util.un_uinst hd1  in
                     uu____4301.FStar_Syntax_Syntax.n  in
                   (uu____4300, args)  in
                 (match uu____4287 with
                  | (FStar_Syntax_Syntax.Tm_fvar
                     fv,uu____4319::uu____4320::(a,uu____4322)::(b,uu____4324)::[])
                      when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.lid_Mktuple2
                      ->
                      let uu____4383 =
                        let uu____4386 = unembed ea a  in uu____4386 w norm1
                         in
                      FStar_Util.bind_opt uu____4383
                        (fun a1  ->
                           let uu____4406 =
                             let uu____4409 = unembed eb b  in
                             uu____4409 w norm1  in
                           FStar_Util.bind_opt uu____4406
                             (fun b1  ->
                                FStar_Pervasives_Native.Some (a1, b1)))
                  | uu____4432 ->
                      (if w
                       then
                         (let uu____4446 =
                            let uu____4451 =
                              let uu____4452 =
                                FStar_Syntax_Print.term_to_string t0  in
                              FStar_Util.format1 "Not an embedded pair: %s"
                                uu____4452
                               in
                            (FStar_Errors.Warning_NotEmbedded, uu____4451)
                             in
                          FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                            uu____4446)
                       else ();
                       FStar_Pervasives_Native.None)))
         in
      let uu____4458 =
        let uu____4459 = type_of ea  in
        let uu____4460 = type_of eb  in
        FStar_Syntax_Syntax.t_tuple2_of uu____4459 uu____4460  in
      mk_emb_full em un uu____4458 printer emb_t_pair_a_b
  
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea  ->
    let t_list_a =
      let t_list = FStar_Syntax_Util.fvar_const FStar_Parser_Const.list_lid
         in
      let uu____4487 =
        let uu____4492 =
          let uu____4493 = FStar_Syntax_Syntax.as_arg ea.typ  in [uu____4493]
           in
        FStar_Syntax_Syntax.mk_Tm_app t_list uu____4492  in
      uu____4487 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
    let emb_t_list_a =
      let uu____4521 =
        let uu____4528 =
          FStar_All.pipe_right FStar_Parser_Const.list_lid
            FStar_Ident.string_of_lid
           in
        (uu____4528, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____4521  in
    let printer l =
      let uu____4541 =
        let uu____4542 =
          let uu____4543 = FStar_List.map ea.print l  in
          FStar_All.pipe_right uu____4543 (FStar_String.concat "; ")  in
        Prims.strcat uu____4542 "]"  in
      Prims.strcat "[" uu____4541  in
    let rec em l rng shadow_l norm1 =
      lazy_embed printer emb_t_list_a rng t_list_a l
        (fun uu____4622  ->
           let t =
             let uu____4624 = type_of ea  in
             FStar_Syntax_Syntax.iarg uu____4624  in
           match l with
           | [] ->
               let uu____4625 =
                 let uu____4630 =
                   let uu____4631 =
                     FStar_Syntax_Syntax.tdataconstr
                       FStar_Parser_Const.nil_lid
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____4631
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 FStar_Syntax_Syntax.mk_Tm_app uu____4630 [t]  in
               uu____4625 FStar_Pervasives_Native.None rng
           | hd1::tl1 ->
               let cons1 =
                 let uu____4655 =
                   FStar_Syntax_Syntax.tdataconstr
                     FStar_Parser_Const.cons_lid
                    in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu____4655
                   [FStar_Syntax_Syntax.U_zero]
                  in
               let proj f cons_tm =
                 let fid = FStar_Ident.mk_ident (f, rng)  in
                 let proj =
                   FStar_Syntax_Util.mk_field_projector_name_from_ident
                     FStar_Parser_Const.cons_lid fid
                    in
                 let proj_tm =
                   let uu____4672 =
                     FStar_Syntax_Syntax.lid_as_fv proj
                       FStar_Syntax_Syntax.delta_equational
                       FStar_Pervasives_Native.None
                      in
                   FStar_Syntax_Syntax.fv_to_tm uu____4672  in
                 let uu____4673 =
                   let uu____4678 =
                     FStar_Syntax_Syntax.mk_Tm_uinst proj_tm
                       [FStar_Syntax_Syntax.U_zero]
                      in
                   let uu____4679 =
                     let uu____4680 =
                       let uu____4689 = type_of ea  in
                       FStar_Syntax_Syntax.iarg uu____4689  in
                     let uu____4690 =
                       let uu____4701 = FStar_Syntax_Syntax.as_arg cons_tm
                          in
                       [uu____4701]  in
                     uu____4680 :: uu____4690  in
                   FStar_Syntax_Syntax.mk_Tm_app uu____4678 uu____4679  in
                 uu____4673 FStar_Pervasives_Native.None rng  in
               let shadow_hd = map_shadow shadow_l (proj "hd")  in
               let shadow_tl = map_shadow shadow_l (proj "tl")  in
               let uu____4852 =
                 let uu____4857 =
                   let uu____4858 =
                     let uu____4869 =
                       let uu____4878 =
                         let uu____4879 = embed ea hd1  in
                         uu____4879 rng shadow_hd norm1  in
                       FStar_Syntax_Syntax.as_arg uu____4878  in
                     let uu____4949 =
                       let uu____4960 =
                         let uu____4969 = em tl1 rng shadow_tl norm1  in
                         FStar_Syntax_Syntax.as_arg uu____4969  in
                       [uu____4960]  in
                     uu____4869 :: uu____4949  in
                   t :: uu____4858  in
                 FStar_Syntax_Syntax.mk_Tm_app cons1 uu____4857  in
               uu____4852 FStar_Pervasives_Native.None rng)
       in
    let rec un t0 w norm1 =
      let t = FStar_Syntax_Util.unmeta_safe t0  in
      lazy_unembed printer emb_t_list_a t t_list_a
        (fun t1  ->
           let uu____5083 = FStar_Syntax_Util.head_and_args' t1  in
           match uu____5083 with
           | (hd1,args) ->
               let uu____5124 =
                 let uu____5137 =
                   let uu____5138 = FStar_Syntax_Util.un_uinst hd1  in
                   uu____5138.FStar_Syntax_Syntax.n  in
                 (uu____5137, args)  in
               (match uu____5124 with
                | (FStar_Syntax_Syntax.Tm_fvar fv,uu____5154) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.nil_lid
                    -> FStar_Pervasives_Native.Some []
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(uu____5174,FStar_Pervasives_Native.Some
                       (FStar_Syntax_Syntax.Implicit uu____5175))::(hd2,FStar_Pervasives_Native.None
                                                                    )::
                   (tl1,FStar_Pervasives_Native.None )::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.cons_lid
                    ->
                    let uu____5216 =
                      let uu____5219 = unembed ea hd2  in uu____5219 w norm1
                       in
                    FStar_Util.bind_opt uu____5216
                      (fun hd3  ->
                         let uu____5237 = un tl1 w norm1  in
                         FStar_Util.bind_opt uu____5237
                           (fun tl2  ->
                              FStar_Pervasives_Native.Some (hd3 :: tl2)))
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(hd2,FStar_Pervasives_Native.None )::(tl1,FStar_Pervasives_Native.None
                                                            )::[])
                    when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.cons_lid
                    ->
                    let uu____5287 =
                      let uu____5290 = unembed ea hd2  in uu____5290 w norm1
                       in
                    FStar_Util.bind_opt uu____5287
                      (fun hd3  ->
                         let uu____5308 = un tl1 w norm1  in
                         FStar_Util.bind_opt uu____5308
                           (fun tl2  ->
                              FStar_Pervasives_Native.Some (hd3 :: tl2)))
                | uu____5325 ->
                    (if w
                     then
                       (let uu____5339 =
                          let uu____5344 =
                            let uu____5345 =
                              FStar_Syntax_Print.term_to_string t0  in
                            FStar_Util.format1 "Not an embedded list: %s"
                              uu____5345
                             in
                          (FStar_Errors.Warning_NotEmbedded, uu____5344)  in
                        FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                          uu____5339)
                     else ();
                     FStar_Pervasives_Native.None)))
       in
    let uu____5349 =
      let uu____5350 = type_of ea  in
      FStar_Syntax_Syntax.t_list_of uu____5350  in
    mk_emb_full em un uu____5349 printer emb_t_list_a
  
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
  | UnfoldAttr of FStar_Syntax_Syntax.attribute 
  | NBE 
let (uu___is_Simpl : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Simpl  -> true | uu____5381 -> false
  
let (uu___is_Weak : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Weak  -> true | uu____5387 -> false
  
let (uu___is_HNF : norm_step -> Prims.bool) =
  fun projectee  -> match projectee with | HNF  -> true | uu____5393 -> false 
let (uu___is_Primops : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____5399 -> false
  
let (uu___is_Delta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Delta  -> true | uu____5405 -> false
  
let (uu___is_Zeta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Zeta  -> true | uu____5411 -> false
  
let (uu___is_Iota : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Iota  -> true | uu____5417 -> false
  
let (uu___is_Reify : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____5423 -> false
  
let (uu___is_UnfoldOnly : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____5432 -> false
  
let (__proj__UnfoldOnly__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldFully : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldFully _0 -> true | uu____5454 -> false
  
let (__proj__UnfoldFully__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldFully _0 -> _0 
let (uu___is_UnfoldAttr : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____5474 -> false
  
let (__proj__UnfoldAttr__item___0 :
  norm_step -> FStar_Syntax_Syntax.attribute) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_NBE : norm_step -> Prims.bool) =
  fun projectee  -> match projectee with | NBE  -> true | uu____5487 -> false 
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
    let uu____5491 =
      FStar_Ident.lid_of_str "FStar.Syntax.Embeddings.norm_step"  in
    FStar_Syntax_Util.fvar_const uu____5491  in
  let emb_t_norm_step =
    let uu____5493 =
      let uu____5500 =
        FStar_All.pipe_right FStar_Parser_Const.norm_step_lid
          FStar_Ident.string_of_lid
         in
      (uu____5500, [])  in
    FStar_Syntax_Syntax.ET_app uu____5493  in
  let printer uu____5508 = "norm_step"  in
  let em n1 rng _topt norm1 =
    lazy_embed printer emb_t_norm_step rng t_norm_step1 n1
      (fun uu____5573  ->
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
             let uu____5577 =
               let uu____5582 =
                 let uu____5583 =
                   let uu____5592 =
                     let uu____5593 =
                       let uu____5600 = e_list e_string  in
                       embed uu____5600 l  in
                     uu____5593 rng FStar_Pervasives_Native.None norm1  in
                   FStar_Syntax_Syntax.as_arg uu____5592  in
                 [uu____5583]  in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldOnly uu____5582  in
             uu____5577 FStar_Pervasives_Native.None rng
         | UnfoldFully l ->
             let uu____5655 =
               let uu____5660 =
                 let uu____5661 =
                   let uu____5670 =
                     let uu____5671 =
                       let uu____5678 = e_list e_string  in
                       embed uu____5678 l  in
                     uu____5671 rng FStar_Pervasives_Native.None norm1  in
                   FStar_Syntax_Syntax.as_arg uu____5670  in
                 [uu____5661]  in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldFully uu____5660  in
             uu____5655 FStar_Pervasives_Native.None rng
         | UnfoldAttr a ->
             let uu____5731 =
               let uu____5736 =
                 let uu____5737 = FStar_Syntax_Syntax.as_arg a  in
                 [uu____5737]  in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldAttr uu____5736  in
             uu____5731 FStar_Pervasives_Native.None rng)
     in
  let un t0 w norm1 =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    lazy_unembed printer emb_t_norm_step t t_norm_step1
      (fun t1  ->
         let uu____5796 = FStar_Syntax_Util.head_and_args t1  in
         match uu____5796 with
         | (hd1,args) ->
             let uu____5841 =
               let uu____5856 =
                 let uu____5857 = FStar_Syntax_Util.un_uinst hd1  in
                 uu____5857.FStar_Syntax_Syntax.n  in
               (uu____5856, args)  in
             (match uu____5841 with
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
              | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____6045)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldonly
                  ->
                  let uu____6080 =
                    let uu____6085 =
                      let uu____6094 = e_list e_string  in
                      unembed uu____6094 l  in
                    uu____6085 w norm1  in
                  FStar_Util.bind_opt uu____6080
                    (fun ss  ->
                       FStar_All.pipe_left
                         (fun _0_16  -> FStar_Pervasives_Native.Some _0_16)
                         (UnfoldOnly ss))
              | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____6117)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldfully
                  ->
                  let uu____6152 =
                    let uu____6157 =
                      let uu____6166 = e_list e_string  in
                      unembed uu____6166 l  in
                    uu____6157 w norm1  in
                  FStar_Util.bind_opt uu____6152
                    (fun ss  ->
                       FStar_All.pipe_left
                         (fun _0_17  -> FStar_Pervasives_Native.Some _0_17)
                         (UnfoldFully ss))
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____6188::(a,uu____6190)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldattr
                  -> FStar_Pervasives_Native.Some (UnfoldAttr a)
              | uu____6241 ->
                  (if w
                   then
                     (let uu____6257 =
                        let uu____6262 =
                          let uu____6263 =
                            FStar_Syntax_Print.term_to_string t0  in
                          FStar_Util.format1 "Not an embedded norm_step: %s"
                            uu____6263
                           in
                        (FStar_Errors.Warning_NotEmbedded, uu____6262)  in
                      FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                        uu____6257)
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
    | uu____6358 ->
        (if w
         then
           (let uu____6360 =
              let uu____6365 =
                let uu____6366 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded range: %s" uu____6366  in
              (FStar_Errors.Warning_NotEmbedded, uu____6365)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____6360)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____6368 =
    let uu____6369 =
      let uu____6376 =
        FStar_All.pipe_right FStar_Parser_Const.range_lid
          FStar_Ident.string_of_lid
         in
      (uu____6376, [])  in
    FStar_Syntax_Syntax.ET_app uu____6369  in
  mk_emb_full em un FStar_Syntax_Syntax.t_range FStar_Range.string_of_range
    uu____6368
  
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
        let uu____6442 =
          let uu____6449 =
            let uu____6450 =
              let uu____6465 =
                let uu____6474 =
                  let uu____6481 = FStar_Syntax_Syntax.null_bv ea.typ  in
                  (uu____6481, FStar_Pervasives_Native.None)  in
                [uu____6474]  in
              let uu____6496 = FStar_Syntax_Syntax.mk_Total eb.typ  in
              (uu____6465, uu____6496)  in
            FStar_Syntax_Syntax.Tm_arrow uu____6450  in
          FStar_Syntax_Syntax.mk uu____6449  in
        uu____6442 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
      let emb_t_arr_a_b =
        FStar_Syntax_Syntax.ET_fun ((ea.emb_typ), (eb.emb_typ))  in
      let printer f = "<fun>"  in
      let em f rng shadow_f norm1 =
        let f_wrapped x =
          let shadow_app =
            map_shadow shadow_f
              (fun f1  ->
                 let uu____6663 =
                   let uu____6668 =
                     let uu____6669 = FStar_Syntax_Syntax.as_arg x  in
                     [uu____6669]  in
                   FStar_Syntax_Syntax.mk_Tm_app f1 uu____6668  in
                 uu____6663 FStar_Pervasives_Native.None rng)
             in
          let uu____6696 =
            let uu____6699 =
              let uu____6702 = unembed ea x  in uu____6702 true norm1  in
            FStar_Util.map_opt uu____6699
              (fun x1  ->
                 let uu____6741 =
                   let uu____6748 = f x1  in embed eb uu____6748  in
                 uu____6741 rng shadow_app norm1)
             in
          or_else uu____6696
            (fun uu____6814  ->
               let uu____6815 = force_shadow shadow_app  in
               match uu____6815 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Exn.raise Embedding_failure
               | FStar_Pervasives_Native.Some app ->
                   norm1 (FStar_Util.Inr app))
           in
        lazy_embed (fun uu____6881  -> "<fun>") emb_t_arr_a_b rng t_arrow
          f_wrapped
          (fun uu____6886  ->
             let uu____6887 = force_shadow shadow_f  in
             match uu____6887 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Exn.raise Embedding_failure
             | FStar_Pervasives_Native.Some repr_f ->
                 norm1 (FStar_Util.Inr repr_f))
         in
      let un f w norm1 =
        lazy_unembed printer emb_t_arr_a_b f t_arrow
          (fun f1  ->
             let f_wrapped a =
               let a_tm =
                 let uu____7001 = embed ea a  in
                 uu____7001 f1.FStar_Syntax_Syntax.pos
                   FStar_Pervasives_Native.None norm1
                  in
               let b_tm =
                 let uu____7034 =
                   let uu____7039 =
                     let uu____7040 =
                       let uu____7045 =
                         let uu____7046 = FStar_Syntax_Syntax.as_arg a_tm  in
                         [uu____7046]  in
                       FStar_Syntax_Syntax.mk_Tm_app f1 uu____7045  in
                     uu____7040 FStar_Pervasives_Native.None
                       f1.FStar_Syntax_Syntax.pos
                      in
                   FStar_Util.Inr uu____7039  in
                 norm1 uu____7034  in
               let uu____7073 =
                 let uu____7076 = unembed eb b_tm  in uu____7076 w norm1  in
               match uu____7073 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Exn.raise Unembedding_failure
               | FStar_Pervasives_Native.Some b -> b  in
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
                let uu____7173 = FStar_List.splitAt n_tvars args  in
                match uu____7173 with
                | (_tvar_args,rest_args) ->
                    let uu____7250 = FStar_List.hd rest_args  in
                    (match uu____7250 with
                     | (x,uu____7270) ->
                         let shadow_app =
                           let uu____7284 =
                             FStar_Common.mk_thunk
                               (fun uu____7293  ->
                                  let uu____7294 =
                                    let uu____7299 =
                                      norm1 (FStar_Util.Inl fv_lid1)  in
                                    FStar_Syntax_Syntax.mk_Tm_app uu____7299
                                      args
                                     in
                                  uu____7294 FStar_Pervasives_Native.None rng)
                              in
                           FStar_Pervasives_Native.Some uu____7284  in
                         let uu____7345 =
                           let uu____7348 =
                             let uu____7351 = unembed ea x  in
                             uu____7351 true norm1  in
                           FStar_Util.map_opt uu____7348
                             (fun x1  ->
                                let uu____7390 =
                                  let uu____7397 = f x1  in
                                  embed eb uu____7397  in
                                uu____7390 rng shadow_app norm1)
                            in
                         (match uu____7345 with
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
                  let uu____7524 = FStar_List.splitAt n_tvars args  in
                  match uu____7524 with
                  | (_tvar_args,rest_args) ->
                      let uu____7587 = FStar_List.hd rest_args  in
                      (match uu____7587 with
                       | (x,uu____7603) ->
                           let uu____7608 =
                             let uu____7615 = FStar_List.tl rest_args  in
                             FStar_List.hd uu____7615  in
                           (match uu____7608 with
                            | (y,uu____7639) ->
                                let shadow_app =
                                  let uu____7649 =
                                    FStar_Common.mk_thunk
                                      (fun uu____7658  ->
                                         let uu____7659 =
                                           let uu____7664 =
                                             norm1 (FStar_Util.Inl fv_lid1)
                                              in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____7664 args
                                            in
                                         uu____7659
                                           FStar_Pervasives_Native.None rng)
                                     in
                                  FStar_Pervasives_Native.Some uu____7649  in
                                let uu____7710 =
                                  let uu____7713 =
                                    let uu____7716 = unembed ea x  in
                                    uu____7716 true norm1  in
                                  FStar_Util.bind_opt uu____7713
                                    (fun x1  ->
                                       let uu____7732 =
                                         let uu____7735 = unembed eb y  in
                                         uu____7735 true norm1  in
                                       FStar_Util.bind_opt uu____7732
                                         (fun y1  ->
                                            let uu____7751 =
                                              let uu____7752 =
                                                let uu____7759 = f x1 y1  in
                                                embed ec uu____7759  in
                                              uu____7752 rng shadow_app norm1
                                               in
                                            FStar_Pervasives_Native.Some
                                              uu____7751))
                                   in
                                (match uu____7710 with
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
                    let uu____7905 = FStar_List.splitAt n_tvars args  in
                    match uu____7905 with
                    | (_tvar_args,rest_args) ->
                        let uu____7968 = FStar_List.hd rest_args  in
                        (match uu____7968 with
                         | (x,uu____7984) ->
                             let uu____7989 =
                               let uu____7996 = FStar_List.tl rest_args  in
                               FStar_List.hd uu____7996  in
                             (match uu____7989 with
                              | (y,uu____8020) ->
                                  let uu____8025 =
                                    let uu____8032 =
                                      let uu____8041 =
                                        FStar_List.tl rest_args  in
                                      FStar_List.tl uu____8041  in
                                    FStar_List.hd uu____8032  in
                                  (match uu____8025 with
                                   | (z,uu____8071) ->
                                       let shadow_app =
                                         let uu____8081 =
                                           FStar_Common.mk_thunk
                                             (fun uu____8090  ->
                                                let uu____8091 =
                                                  let uu____8096 =
                                                    norm1
                                                      (FStar_Util.Inl fv_lid1)
                                                     in
                                                  FStar_Syntax_Syntax.mk_Tm_app
                                                    uu____8096 args
                                                   in
                                                uu____8091
                                                  FStar_Pervasives_Native.None
                                                  rng)
                                            in
                                         FStar_Pervasives_Native.Some
                                           uu____8081
                                          in
                                       let uu____8142 =
                                         let uu____8145 =
                                           let uu____8148 = unembed ea x  in
                                           uu____8148 true norm1  in
                                         FStar_Util.bind_opt uu____8145
                                           (fun x1  ->
                                              let uu____8164 =
                                                let uu____8167 = unembed eb y
                                                   in
                                                uu____8167 true norm1  in
                                              FStar_Util.bind_opt uu____8164
                                                (fun y1  ->
                                                   let uu____8183 =
                                                     let uu____8186 =
                                                       unembed ec z  in
                                                     uu____8186 true norm1
                                                      in
                                                   FStar_Util.bind_opt
                                                     uu____8183
                                                     (fun z1  ->
                                                        let uu____8202 =
                                                          let uu____8203 =
                                                            let uu____8210 =
                                                              f x1 y1 z1  in
                                                            embed ed
                                                              uu____8210
                                                             in
                                                          uu____8203 rng
                                                            shadow_app norm1
                                                           in
                                                        FStar_Pervasives_Native.Some
                                                          uu____8202)))
                                          in
                                       (match uu____8142 with
                                        | FStar_Pervasives_Native.Some x1 ->
                                            FStar_Pervasives_Native.Some x1
                                        | FStar_Pervasives_Native.None  ->
                                            force_shadow shadow_app))))
                     in
                  f_wrapped
  
let debug_wrap : 'a . Prims.string -> (unit -> 'a) -> 'a =
  fun s  ->
    fun f  ->
      (let uu____8262 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
       if uu____8262 then FStar_Util.print1 "++++starting %s\n" s else ());
      (let res = f ()  in
       (let uu____8285 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
        if uu____8285 then FStar_Util.print1 "------ending %s\n" s else ());
       res)
  