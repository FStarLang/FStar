open Prims
type norm_cb =
  (FStar_Ident.lid,FStar_Syntax_Syntax.term) FStar_Util.either ->
    FStar_Syntax_Syntax.term
let (id_norm_cb : norm_cb) =
  fun uu___208_13  ->
    match uu___208_13 with
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
  'Auu____824 . FStar_Syntax_Syntax.term -> 'Auu____824 -> Prims.string =
  fun typ  ->
    fun uu____834  ->
      let uu____835 = FStar_Syntax_Print.term_to_string typ  in
      FStar_Util.format1 "unknown %s" uu____835
  
let (term_as_fv : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.fv) =
  fun t  ->
    let uu____841 =
      let uu____842 = FStar_Syntax_Subst.compress t  in
      uu____842.FStar_Syntax_Syntax.n  in
    match uu____841 with
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv
    | uu____846 ->
        let uu____847 =
          let uu____848 = FStar_Syntax_Print.term_to_string t  in
          FStar_Util.format1 "Embeddings not defined for type %s" uu____848
           in
        failwith uu____847
  
let mk_emb :
  'a .
    'a raw_embedder ->
      'a raw_unembedder -> FStar_Syntax_Syntax.fv -> 'a embedding
  =
  fun em  ->
    fun un  ->
      fun fv  ->
        let typ = FStar_Syntax_Syntax.fv_to_tm fv  in
        let uu____973 =
          let uu____974 =
            let uu____981 =
              let uu____982 = FStar_Syntax_Syntax.lid_of_fv fv  in
              FStar_All.pipe_right uu____982 FStar_Ident.string_of_lid  in
            (uu____981, [])  in
          FStar_Syntax_Syntax.ET_app uu____974  in
        { em; un; typ; print = (unknown_printer typ); emb_typ = uu____973 }
  
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
    fun t  -> fun n1  -> let uu____1384 = unembed e t  in uu____1384 true n1
  
let try_unembed :
  'a .
    'a embedding ->
      FStar_Syntax_Syntax.term ->
        norm_cb -> 'a FStar_Pervasives_Native.option
  =
  fun e  ->
    fun t  -> fun n1  -> let uu____1431 = unembed e t  in uu____1431 false n1
  
let type_of : 'a . 'a embedding -> FStar_Syntax_Syntax.typ = fun e  -> e.typ 
let set_type : 'a . FStar_Syntax_Syntax.typ -> 'a embedding -> 'a embedding =
  fun ty  ->
    fun e  ->
      let uu___210_1481 = e  in
      {
        em = (uu___210_1481.em);
        un = (uu___210_1481.un);
        typ = ty;
        print = (uu___210_1481.print);
        emb_typ = (uu___210_1481.emb_typ)
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
              (let uu____1549 =
                 FStar_ST.op_Bang FStar_Options.debug_embedding  in
               if uu____1549
               then
                 let uu____1569 = FStar_Syntax_Print.term_to_string ta  in
                 let uu____1570 = FStar_Syntax_Print.emb_typ_to_string et  in
                 let uu____1571 = pa x  in
                 FStar_Util.print3
                   "Embedding a %s\n\temb_typ=%s\n\tvalue is %s\n" uu____1569
                   uu____1570 uu____1571
               else ());
              (let uu____1575 =
                 FStar_ST.op_Bang FStar_Options.eager_embedding  in
               if uu____1575
               then f ()
               else
                 (let thunk = FStar_Common.mk_thunk f  in
                  let uu____1605 =
                    let uu____1612 =
                      let uu____1613 =
                        let uu____1614 = FStar_Dyn.mkdyn x  in
                        {
                          FStar_Syntax_Syntax.blob = uu____1614;
                          FStar_Syntax_Syntax.lkind =
                            (FStar_Syntax_Syntax.Lazy_embedding (et, thunk));
                          FStar_Syntax_Syntax.ltyp = FStar_Syntax_Syntax.tun;
                          FStar_Syntax_Syntax.rng = rng
                        }  in
                      FStar_Syntax_Syntax.Tm_lazy uu____1613  in
                    FStar_Syntax_Syntax.mk uu____1612  in
                  uu____1605 FStar_Pervasives_Native.None rng))
  
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
                  FStar_Syntax_Syntax.ltyp = uu____1729;
                  FStar_Syntax_Syntax.rng = uu____1730;_}
                ->
                let uu____1741 =
                  (et <> et') ||
                    (FStar_ST.op_Bang FStar_Options.eager_embedding)
                   in
                if uu____1741
                then
                  let res =
                    let uu____1766 = FStar_Common.force_thunk t  in
                    f uu____1766  in
                  ((let uu____1810 =
                      FStar_ST.op_Bang FStar_Options.debug_embedding  in
                    if uu____1810
                    then
                      let uu____1830 =
                        FStar_Syntax_Print.emb_typ_to_string et  in
                      let uu____1831 =
                        FStar_Syntax_Print.emb_typ_to_string et'  in
                      let uu____1832 =
                        match res with
                        | FStar_Pervasives_Native.None  -> "None"
                        | FStar_Pervasives_Native.Some x2 ->
                            let uu____1834 = pa x2  in
                            Prims.strcat "Some " uu____1834
                         in
                      FStar_Util.print3
                        "Unembed cancellation failed\n\t%s <> %s\nvalue is %s\n"
                        uu____1830 uu____1831 uu____1832
                    else ());
                   res)
                else
                  (let a = FStar_Dyn.undyn b  in
                   (let uu____1841 =
                      FStar_ST.op_Bang FStar_Options.debug_embedding  in
                    if uu____1841
                    then
                      let uu____1861 =
                        FStar_Syntax_Print.emb_typ_to_string et  in
                      let uu____1862 = pa a  in
                      FStar_Util.print2
                        "Unembed cancelled for %s\n\tvalue is %s\n"
                        uu____1861 uu____1862
                    else ());
                   FStar_Pervasives_Native.Some a)
            | uu____1866 ->
                let aopt = f x1  in
                ((let uu____1871 =
                    FStar_ST.op_Bang FStar_Options.debug_embedding  in
                  if uu____1871
                  then
                    let uu____1891 = FStar_Syntax_Print.emb_typ_to_string et
                       in
                    let uu____1892 = FStar_Syntax_Print.term_to_string x1  in
                    let uu____1893 =
                      match aopt with
                      | FStar_Pervasives_Native.None  -> "None"
                      | FStar_Pervasives_Native.Some a ->
                          let uu____1895 = pa a  in
                          Prims.strcat "Some " uu____1895
                       in
                    FStar_Util.print3
                      "Unembedding:\n\temb_typ=%s\n\tterm is %s\n\tvalue is %s\n"
                      uu____1891 uu____1892 uu____1893
                  else ());
                 aopt)
  
let (mk_any_emb :
  FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term embedding) =
  fun typ  ->
    let em t _r _topt _norm =
      (let uu____1970 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
       if uu____1970
       then
         let uu____1990 = unknown_printer typ t  in
         FStar_Util.print1 "Embedding abstract: %s\n" uu____1990
       else ());
      t  in
    let un t _w _n =
      (let uu____2015 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
       if uu____2015
       then
         let uu____2035 = unknown_printer typ t  in
         FStar_Util.print1 "Unembedding abstract: %s\n" uu____2035
       else ());
      FStar_Pervasives_Native.Some t  in
    mk_emb_full em un typ (unknown_printer typ)
      FStar_Syntax_Syntax.ET_abstract
  
let (e_any : FStar_Syntax_Syntax.term embedding) =
  let em t _r _topt _norm = t  in
  let un t _w _n = FStar_Pervasives_Native.Some t  in
  let uu____2124 =
    let uu____2125 =
      let uu____2132 =
        FStar_All.pipe_right FStar_Parser_Const.term_lid
          FStar_Ident.string_of_lid
         in
      (uu____2132, [])  in
    FStar_Syntax_Syntax.ET_app uu____2125  in
  mk_emb_full em un FStar_Syntax_Syntax.t_term
    FStar_Syntax_Print.term_to_string uu____2124
  
let (e_unit : unit embedding) =
  let em u rng _topt _norm =
    let uu___211_2200 = FStar_Syntax_Util.exp_unit  in
    {
      FStar_Syntax_Syntax.n = (uu___211_2200.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___211_2200.FStar_Syntax_Syntax.vars)
    }  in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unascribe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit ) ->
        FStar_Pervasives_Native.Some ()
    | uu____2228 ->
        (if w
         then
           (let uu____2230 =
              let uu____2235 =
                let uu____2236 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded unit: %s" uu____2236  in
              (FStar_Errors.Warning_NotEmbedded, uu____2235)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____2230)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____2238 =
    let uu____2239 =
      let uu____2246 =
        FStar_All.pipe_right FStar_Parser_Const.unit_lid
          FStar_Ident.string_of_lid
         in
      (uu____2246, [])  in
    FStar_Syntax_Syntax.ET_app uu____2239  in
  mk_emb_full em un FStar_Syntax_Syntax.t_unit (fun uu____2250  -> "()")
    uu____2238
  
let (e_bool : Prims.bool embedding) =
  let em b rng _topt _norm =
    let t =
      if b
      then FStar_Syntax_Util.exp_true_bool
      else FStar_Syntax_Util.exp_false_bool  in
    let uu___212_2322 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___212_2322.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___212_2322.FStar_Syntax_Syntax.vars)
    }  in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) ->
        FStar_Pervasives_Native.Some b
    | uu____2353 ->
        (if w
         then
           (let uu____2355 =
              let uu____2360 =
                let uu____2361 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded bool: %s" uu____2361  in
              (FStar_Errors.Warning_NotEmbedded, uu____2360)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____2355)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____2363 =
    let uu____2364 =
      let uu____2371 =
        FStar_All.pipe_right FStar_Parser_Const.bool_lid
          FStar_Ident.string_of_lid
         in
      (uu____2371, [])  in
    FStar_Syntax_Syntax.ET_app uu____2364  in
  mk_emb_full em un FStar_Syntax_Syntax.t_bool FStar_Util.string_of_bool
    uu____2363
  
let (e_char : FStar_Char.char embedding) =
  let em c rng _topt _norm =
    let t = FStar_Syntax_Util.exp_char c  in
    let uu___213_2443 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___213_2443.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___213_2443.FStar_Syntax_Syntax.vars)
    }  in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c) ->
        FStar_Pervasives_Native.Some c
    | uu____2477 ->
        (if w
         then
           (let uu____2479 =
              let uu____2484 =
                let uu____2485 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded char: %s" uu____2485  in
              (FStar_Errors.Warning_NotEmbedded, uu____2484)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____2479)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____2488 =
    let uu____2489 =
      let uu____2496 =
        FStar_All.pipe_right FStar_Parser_Const.char_lid
          FStar_Ident.string_of_lid
         in
      (uu____2496, [])  in
    FStar_Syntax_Syntax.ET_app uu____2489  in
  mk_emb_full em un FStar_Syntax_Syntax.t_char FStar_Util.string_of_char
    uu____2488
  
let (e_int : FStar_BigInt.t embedding) =
  let t_int1 = FStar_Syntax_Util.fvar_const FStar_Parser_Const.int_lid  in
  let emb_t_int =
    let uu____2504 =
      let uu____2511 =
        FStar_All.pipe_right FStar_Parser_Const.int_lid
          FStar_Ident.string_of_lid
         in
      (uu____2511, [])  in
    FStar_Syntax_Syntax.ET_app uu____2504  in
  let em i rng _topt _norm =
    lazy_embed FStar_BigInt.string_of_big_int emb_t_int rng t_int1 i
      (fun uu____2579  ->
         let uu____2580 = FStar_BigInt.string_of_big_int i  in
         FStar_Syntax_Util.exp_int uu____2580)
     in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    lazy_unembed FStar_BigInt.string_of_big_int emb_t_int t t_int1
      (fun t1  ->
         match t1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
             (s,uu____2614)) ->
             let uu____2627 = FStar_BigInt.big_int_of_string s  in
             FStar_Pervasives_Native.Some uu____2627
         | uu____2628 ->
             (if w
              then
                (let uu____2630 =
                   let uu____2635 =
                     let uu____2636 = FStar_Syntax_Print.term_to_string t0
                        in
                     FStar_Util.format1 "Not an embedded int: %s" uu____2636
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____2635)  in
                 FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____2630)
              else ();
              FStar_Pervasives_Native.None))
     in
  mk_emb_full em un FStar_Syntax_Syntax.t_int FStar_BigInt.string_of_big_int
    emb_t_int
  
let (e_string : Prims.string embedding) =
  let emb_t_string =
    let uu____2641 =
      let uu____2648 =
        FStar_All.pipe_right FStar_Parser_Const.string_lid
          FStar_Ident.string_of_lid
         in
      (uu____2648, [])  in
    FStar_Syntax_Syntax.ET_app uu____2641  in
  let em s rng _topt _norm =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, rng)))
      FStar_Pervasives_Native.None rng
     in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
        (s,uu____2742)) -> FStar_Pervasives_Native.Some s
    | uu____2743 ->
        (if w
         then
           (let uu____2745 =
              let uu____2750 =
                let uu____2751 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded string: %s" uu____2751
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____2750)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____2745)
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
      let uu____2777 =
        let uu____2782 =
          let uu____2783 = FStar_Syntax_Syntax.as_arg ea.typ  in [uu____2783]
           in
        FStar_Syntax_Syntax.mk_Tm_app t_opt uu____2782  in
      uu____2777 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
    let emb_t_option_a =
      let uu____2811 =
        let uu____2818 =
          FStar_All.pipe_right FStar_Parser_Const.option_lid
            FStar_Ident.string_of_lid
           in
        (uu____2818, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____2811  in
    let printer uu___209_2828 =
      match uu___209_2828 with
      | FStar_Pervasives_Native.None  -> "None"
      | FStar_Pervasives_Native.Some x ->
          let uu____2832 =
            let uu____2833 = ea.print x  in Prims.strcat uu____2833 ")"  in
          Prims.strcat "(Some " uu____2832
       in
    let em o rng topt norm1 =
      lazy_embed printer emb_t_option_a rng t_option_a o
        (fun uu____2907  ->
           match o with
           | FStar_Pervasives_Native.None  ->
               let uu____2908 =
                 let uu____2913 =
                   let uu____2914 =
                     FStar_Syntax_Syntax.tdataconstr
                       FStar_Parser_Const.none_lid
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____2914
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 let uu____2915 =
                   let uu____2916 =
                     let uu____2925 = type_of ea  in
                     FStar_Syntax_Syntax.iarg uu____2925  in
                   [uu____2916]  in
                 FStar_Syntax_Syntax.mk_Tm_app uu____2913 uu____2915  in
               uu____2908 FStar_Pervasives_Native.None rng
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
                        let uu____3014 =
                          FStar_Syntax_Syntax.lid_as_fv some_v
                            FStar_Syntax_Syntax.delta_equational
                            FStar_Pervasives_Native.None
                           in
                        FStar_Syntax_Syntax.fv_to_tm uu____3014  in
                      let uu____3015 =
                        let uu____3020 =
                          FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm
                            [FStar_Syntax_Syntax.U_zero]
                           in
                        let uu____3021 =
                          let uu____3022 =
                            let uu____3031 = type_of ea  in
                            FStar_Syntax_Syntax.iarg uu____3031  in
                          let uu____3032 =
                            let uu____3043 = FStar_Syntax_Syntax.as_arg t  in
                            [uu____3043]  in
                          uu____3022 :: uu____3032  in
                        FStar_Syntax_Syntax.mk_Tm_app uu____3020 uu____3021
                         in
                      uu____3015 FStar_Pervasives_Native.None rng)
                  in
               let uu____3078 =
                 let uu____3083 =
                   let uu____3084 =
                     FStar_Syntax_Syntax.tdataconstr
                       FStar_Parser_Const.some_lid
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____3084
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 let uu____3085 =
                   let uu____3086 =
                     let uu____3095 = type_of ea  in
                     FStar_Syntax_Syntax.iarg uu____3095  in
                   let uu____3096 =
                     let uu____3107 =
                       let uu____3116 =
                         let uu____3117 = embed ea a  in
                         uu____3117 rng shadow_a norm1  in
                       FStar_Syntax_Syntax.as_arg uu____3116  in
                     [uu____3107]  in
                   uu____3086 :: uu____3096  in
                 FStar_Syntax_Syntax.mk_Tm_app uu____3083 uu____3085  in
               uu____3078 FStar_Pervasives_Native.None rng)
       in
    let un t0 w norm1 =
      let t = FStar_Syntax_Util.unmeta_safe t0  in
      lazy_unembed printer emb_t_option_a t t_option_a
        (fun t1  ->
           let uu____3252 = FStar_Syntax_Util.head_and_args' t1  in
           match uu____3252 with
           | (hd1,args) ->
               let uu____3293 =
                 let uu____3308 =
                   let uu____3309 = FStar_Syntax_Util.un_uinst hd1  in
                   uu____3309.FStar_Syntax_Syntax.n  in
                 (uu____3308, args)  in
               (match uu____3293 with
                | (FStar_Syntax_Syntax.Tm_fvar fv,uu____3327) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.none_lid
                    ->
                    FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,uu____3351::(a,uu____3353)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.some_lid
                    ->
                    let uu____3404 =
                      let uu____3407 = unembed ea a  in uu____3407 w norm1
                       in
                    FStar_Util.bind_opt uu____3404
                      (fun a1  ->
                         FStar_Pervasives_Native.Some
                           (FStar_Pervasives_Native.Some a1))
                | uu____3426 ->
                    (if w
                     then
                       (let uu____3442 =
                          let uu____3447 =
                            let uu____3448 =
                              FStar_Syntax_Print.term_to_string t0  in
                            FStar_Util.format1 "Not an embedded option: %s"
                              uu____3448
                             in
                          (FStar_Errors.Warning_NotEmbedded, uu____3447)  in
                        FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                          uu____3442)
                     else ();
                     FStar_Pervasives_Native.None)))
       in
    let uu____3452 =
      let uu____3453 = type_of ea  in
      FStar_Syntax_Syntax.t_option_of uu____3453  in
    mk_emb_full em un uu____3452 printer emb_t_option_a
  
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
        let uu____3494 =
          let uu____3499 =
            let uu____3500 = FStar_Syntax_Syntax.as_arg ea.typ  in
            let uu____3509 =
              let uu____3520 = FStar_Syntax_Syntax.as_arg eb.typ  in
              [uu____3520]  in
            uu____3500 :: uu____3509  in
          FStar_Syntax_Syntax.mk_Tm_app t_tup2 uu____3499  in
        uu____3494 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
      let emb_t_pair_a_b =
        let uu____3556 =
          let uu____3563 =
            FStar_All.pipe_right FStar_Parser_Const.lid_tuple2
              FStar_Ident.string_of_lid
             in
          (uu____3563, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____3556  in
      let printer uu____3575 =
        match uu____3575 with
        | (x,y) ->
            let uu____3582 = ea.print x  in
            let uu____3583 = eb.print y  in
            FStar_Util.format2 "(%s, %s)" uu____3582 uu____3583
         in
      let em x rng topt norm1 =
        lazy_embed printer emb_t_pair_a_b rng t_pair_a_b x
          (fun uu____3666  ->
             let proj i ab =
               let uu____3680 =
                 let uu____3685 =
                   FStar_Parser_Const.mk_tuple_data_lid (Prims.parse_int "2")
                     rng
                    in
                 let uu____3686 =
                   FStar_Syntax_Syntax.null_bv FStar_Syntax_Syntax.tun  in
                 FStar_Syntax_Util.mk_field_projector_name uu____3685
                   uu____3686 i
                  in
               match uu____3680 with
               | (proj_1,uu____3690) ->
                   let proj_1_tm =
                     let uu____3692 =
                       FStar_Syntax_Syntax.lid_as_fv proj_1
                         FStar_Syntax_Syntax.delta_equational
                         FStar_Pervasives_Native.None
                        in
                     FStar_Syntax_Syntax.fv_to_tm uu____3692  in
                   let uu____3693 =
                     let uu____3698 =
                       FStar_Syntax_Syntax.mk_Tm_uinst proj_1_tm
                         [FStar_Syntax_Syntax.U_zero]
                        in
                     let uu____3699 =
                       let uu____3700 =
                         let uu____3709 = type_of ea  in
                         FStar_Syntax_Syntax.iarg uu____3709  in
                       let uu____3710 =
                         let uu____3721 =
                           let uu____3730 = type_of eb  in
                           FStar_Syntax_Syntax.iarg uu____3730  in
                         let uu____3731 =
                           let uu____3742 = FStar_Syntax_Syntax.as_arg ab  in
                           [uu____3742]  in
                         uu____3721 :: uu____3731  in
                       uu____3700 :: uu____3710  in
                     FStar_Syntax_Syntax.mk_Tm_app uu____3698 uu____3699  in
                   uu____3693 FStar_Pervasives_Native.None rng
                in
             let shadow_a = map_shadow topt (proj (Prims.parse_int "1"))  in
             let shadow_b = map_shadow topt (proj (Prims.parse_int "2"))  in
             let uu____3901 =
               let uu____3906 =
                 let uu____3907 =
                   FStar_Syntax_Syntax.tdataconstr
                     FStar_Parser_Const.lid_Mktuple2
                    in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu____3907
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                  in
               let uu____3908 =
                 let uu____3909 =
                   let uu____3918 = type_of ea  in
                   FStar_Syntax_Syntax.iarg uu____3918  in
                 let uu____3919 =
                   let uu____3930 =
                     let uu____3939 = type_of eb  in
                     FStar_Syntax_Syntax.iarg uu____3939  in
                   let uu____3940 =
                     let uu____3951 =
                       let uu____3960 =
                         let uu____3961 =
                           embed ea (FStar_Pervasives_Native.fst x)  in
                         uu____3961 rng shadow_a norm1  in
                       FStar_Syntax_Syntax.as_arg uu____3960  in
                     let uu____4031 =
                       let uu____4042 =
                         let uu____4051 =
                           let uu____4052 =
                             embed eb (FStar_Pervasives_Native.snd x)  in
                           uu____4052 rng shadow_b norm1  in
                         FStar_Syntax_Syntax.as_arg uu____4051  in
                       [uu____4042]  in
                     uu____3951 :: uu____4031  in
                   uu____3930 :: uu____3940  in
                 uu____3909 :: uu____3919  in
               FStar_Syntax_Syntax.mk_Tm_app uu____3906 uu____3908  in
             uu____3901 FStar_Pervasives_Native.None rng)
         in
      let un t0 w norm1 =
        let t = FStar_Syntax_Util.unmeta_safe t0  in
        lazy_unembed printer emb_t_pair_a_b t t_pair_a_b
          (fun t1  ->
             let uu____4215 = FStar_Syntax_Util.head_and_args' t1  in
             match uu____4215 with
             | (hd1,args) ->
                 let uu____4258 =
                   let uu____4271 =
                     let uu____4272 = FStar_Syntax_Util.un_uinst hd1  in
                     uu____4272.FStar_Syntax_Syntax.n  in
                   (uu____4271, args)  in
                 (match uu____4258 with
                  | (FStar_Syntax_Syntax.Tm_fvar
                     fv,uu____4290::uu____4291::(a,uu____4293)::(b,uu____4295)::[])
                      when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.lid_Mktuple2
                      ->
                      let uu____4354 =
                        let uu____4357 = unembed ea a  in uu____4357 w norm1
                         in
                      FStar_Util.bind_opt uu____4354
                        (fun a1  ->
                           let uu____4377 =
                             let uu____4380 = unembed eb b  in
                             uu____4380 w norm1  in
                           FStar_Util.bind_opt uu____4377
                             (fun b1  ->
                                FStar_Pervasives_Native.Some (a1, b1)))
                  | uu____4403 ->
                      (if w
                       then
                         (let uu____4417 =
                            let uu____4422 =
                              let uu____4423 =
                                FStar_Syntax_Print.term_to_string t0  in
                              FStar_Util.format1 "Not an embedded pair: %s"
                                uu____4423
                               in
                            (FStar_Errors.Warning_NotEmbedded, uu____4422)
                             in
                          FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                            uu____4417)
                       else ();
                       FStar_Pervasives_Native.None)))
         in
      let uu____4429 =
        let uu____4430 = type_of ea  in
        let uu____4431 = type_of eb  in
        FStar_Syntax_Syntax.t_tuple2_of uu____4430 uu____4431  in
      mk_emb_full em un uu____4429 printer emb_t_pair_a_b
  
let e_either :
  'a 'b . 'a embedding -> 'b embedding -> ('a,'b) FStar_Util.either embedding
  =
  fun ea  ->
    fun eb  ->
      let t_sum_a_b =
        let t_either =
          FStar_Syntax_Util.fvar_const FStar_Parser_Const.either_lid  in
        let uu____4474 =
          let uu____4479 =
            let uu____4480 = FStar_Syntax_Syntax.as_arg ea.typ  in
            let uu____4489 =
              let uu____4500 = FStar_Syntax_Syntax.as_arg eb.typ  in
              [uu____4500]  in
            uu____4480 :: uu____4489  in
          FStar_Syntax_Syntax.mk_Tm_app t_either uu____4479  in
        uu____4474 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
      let emb_t_sum_a_b =
        let uu____4536 =
          let uu____4543 =
            FStar_All.pipe_right FStar_Parser_Const.either_lid
              FStar_Ident.string_of_lid
             in
          (uu____4543, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____4536  in
      let printer s =
        match s with
        | FStar_Util.Inl a ->
            let uu____4561 = ea.print a  in
            FStar_Util.format1 "Inl %s" uu____4561
        | FStar_Util.Inr b ->
            let uu____4563 = eb.print b  in
            FStar_Util.format1 "Inr %s" uu____4563
         in
      let em s rng topt norm1 =
        lazy_embed printer emb_t_sum_a_b rng t_sum_a_b s
          (match s with
           | FStar_Util.Inl a ->
               (fun uu____4649  ->
                  let shadow_a =
                    map_shadow topt
                      (fun t  ->
                         let v1 = FStar_Ident.mk_ident ("v", rng)  in
                         let some_v =
                           FStar_Syntax_Util.mk_field_projector_name_from_ident
                             FStar_Parser_Const.inl_lid v1
                            in
                         let some_v_tm =
                           let uu____4719 =
                             FStar_Syntax_Syntax.lid_as_fv some_v
                               FStar_Syntax_Syntax.delta_equational
                               FStar_Pervasives_Native.None
                              in
                           FStar_Syntax_Syntax.fv_to_tm uu____4719  in
                         let uu____4720 =
                           let uu____4725 =
                             FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm
                               [FStar_Syntax_Syntax.U_zero]
                              in
                           let uu____4726 =
                             let uu____4727 =
                               let uu____4736 = type_of ea  in
                               FStar_Syntax_Syntax.iarg uu____4736  in
                             let uu____4737 =
                               let uu____4748 =
                                 let uu____4757 = type_of eb  in
                                 FStar_Syntax_Syntax.iarg uu____4757  in
                               let uu____4758 =
                                 let uu____4769 =
                                   FStar_Syntax_Syntax.as_arg t  in
                                 [uu____4769]  in
                               uu____4748 :: uu____4758  in
                             uu____4727 :: uu____4737  in
                           FStar_Syntax_Syntax.mk_Tm_app uu____4725
                             uu____4726
                            in
                         uu____4720 FStar_Pervasives_Native.None rng)
                     in
                  let uu____4812 =
                    let uu____4817 =
                      let uu____4818 =
                        FStar_Syntax_Syntax.tdataconstr
                          FStar_Parser_Const.inl_lid
                         in
                      FStar_Syntax_Syntax.mk_Tm_uinst uu____4818
                        [FStar_Syntax_Syntax.U_zero;
                        FStar_Syntax_Syntax.U_zero]
                       in
                    let uu____4819 =
                      let uu____4820 =
                        let uu____4829 = type_of ea  in
                        FStar_Syntax_Syntax.iarg uu____4829  in
                      let uu____4830 =
                        let uu____4841 =
                          let uu____4850 = type_of eb  in
                          FStar_Syntax_Syntax.iarg uu____4850  in
                        let uu____4851 =
                          let uu____4862 =
                            let uu____4871 =
                              let uu____4872 = embed ea a  in
                              uu____4872 rng shadow_a norm1  in
                            FStar_Syntax_Syntax.as_arg uu____4871  in
                          [uu____4862]  in
                        uu____4841 :: uu____4851  in
                      uu____4820 :: uu____4830  in
                    FStar_Syntax_Syntax.mk_Tm_app uu____4817 uu____4819  in
                  uu____4812 FStar_Pervasives_Native.None rng)
           | FStar_Util.Inr b ->
               (fun uu____4977  ->
                  let shadow_b =
                    map_shadow topt
                      (fun t  ->
                         let v1 = FStar_Ident.mk_ident ("v", rng)  in
                         let some_v =
                           FStar_Syntax_Util.mk_field_projector_name_from_ident
                             FStar_Parser_Const.inr_lid v1
                            in
                         let some_v_tm =
                           let uu____5047 =
                             FStar_Syntax_Syntax.lid_as_fv some_v
                               FStar_Syntax_Syntax.delta_equational
                               FStar_Pervasives_Native.None
                              in
                           FStar_Syntax_Syntax.fv_to_tm uu____5047  in
                         let uu____5048 =
                           let uu____5053 =
                             FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm
                               [FStar_Syntax_Syntax.U_zero]
                              in
                           let uu____5054 =
                             let uu____5055 =
                               let uu____5064 = type_of ea  in
                               FStar_Syntax_Syntax.iarg uu____5064  in
                             let uu____5065 =
                               let uu____5076 =
                                 let uu____5085 = type_of eb  in
                                 FStar_Syntax_Syntax.iarg uu____5085  in
                               let uu____5086 =
                                 let uu____5097 =
                                   FStar_Syntax_Syntax.as_arg t  in
                                 [uu____5097]  in
                               uu____5076 :: uu____5086  in
                             uu____5055 :: uu____5065  in
                           FStar_Syntax_Syntax.mk_Tm_app uu____5053
                             uu____5054
                            in
                         uu____5048 FStar_Pervasives_Native.None rng)
                     in
                  let uu____5140 =
                    let uu____5145 =
                      let uu____5146 =
                        FStar_Syntax_Syntax.tdataconstr
                          FStar_Parser_Const.inr_lid
                         in
                      FStar_Syntax_Syntax.mk_Tm_uinst uu____5146
                        [FStar_Syntax_Syntax.U_zero;
                        FStar_Syntax_Syntax.U_zero]
                       in
                    let uu____5147 =
                      let uu____5148 =
                        let uu____5157 = type_of ea  in
                        FStar_Syntax_Syntax.iarg uu____5157  in
                      let uu____5158 =
                        let uu____5169 =
                          let uu____5178 = type_of eb  in
                          FStar_Syntax_Syntax.iarg uu____5178  in
                        let uu____5179 =
                          let uu____5190 =
                            let uu____5199 =
                              let uu____5200 = embed eb b  in
                              uu____5200 rng shadow_b norm1  in
                            FStar_Syntax_Syntax.as_arg uu____5199  in
                          [uu____5190]  in
                        uu____5169 :: uu____5179  in
                      uu____5148 :: uu____5158  in
                    FStar_Syntax_Syntax.mk_Tm_app uu____5145 uu____5147  in
                  uu____5140 FStar_Pervasives_Native.None rng))
         in
      let un t0 w norm1 =
        let t = FStar_Syntax_Util.unmeta_safe t0  in
        lazy_unembed printer emb_t_sum_a_b t t_sum_a_b
          (fun t1  ->
             let uu____5353 = FStar_Syntax_Util.head_and_args' t1  in
             match uu____5353 with
             | (hd1,args) ->
                 let uu____5396 =
                   let uu____5411 =
                     let uu____5412 = FStar_Syntax_Util.un_uinst hd1  in
                     uu____5412.FStar_Syntax_Syntax.n  in
                   (uu____5411, args)  in
                 (match uu____5396 with
                  | (FStar_Syntax_Syntax.Tm_fvar
                     fv,uu____5432::uu____5433::(a,uu____5435)::[]) when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.inl_lid
                      ->
                      let uu____5502 =
                        let uu____5505 = unembed ea a  in uu____5505 w norm1
                         in
                      FStar_Util.bind_opt uu____5502
                        (fun a1  ->
                           FStar_Pervasives_Native.Some (FStar_Util.Inl a1))
                  | (FStar_Syntax_Syntax.Tm_fvar
                     fv,uu____5529::uu____5530::(b,uu____5532)::[]) when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.inr_lid
                      ->
                      let uu____5599 =
                        let uu____5602 = unembed eb b  in uu____5602 w norm1
                         in
                      FStar_Util.bind_opt uu____5599
                        (fun b1  ->
                           FStar_Pervasives_Native.Some (FStar_Util.Inr b1))
                  | uu____5625 ->
                      (if w
                       then
                         (let uu____5641 =
                            let uu____5646 =
                              let uu____5647 =
                                FStar_Syntax_Print.term_to_string t0  in
                              FStar_Util.format1 "Not an embedded sum: %s"
                                uu____5647
                               in
                            (FStar_Errors.Warning_NotEmbedded, uu____5646)
                             in
                          FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                            uu____5641)
                       else ();
                       FStar_Pervasives_Native.None)))
         in
      let uu____5653 =
        let uu____5654 = type_of ea  in
        let uu____5655 = type_of eb  in
        FStar_Syntax_Syntax.t_either_of uu____5654 uu____5655  in
      mk_emb_full em un uu____5653 printer emb_t_sum_a_b
  
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea  ->
    let t_list_a =
      let t_list = FStar_Syntax_Util.fvar_const FStar_Parser_Const.list_lid
         in
      let uu____5682 =
        let uu____5687 =
          let uu____5688 = FStar_Syntax_Syntax.as_arg ea.typ  in [uu____5688]
           in
        FStar_Syntax_Syntax.mk_Tm_app t_list uu____5687  in
      uu____5682 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
    let emb_t_list_a =
      let uu____5716 =
        let uu____5723 =
          FStar_All.pipe_right FStar_Parser_Const.list_lid
            FStar_Ident.string_of_lid
           in
        (uu____5723, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____5716  in
    let printer l =
      let uu____5736 =
        let uu____5737 =
          let uu____5738 = FStar_List.map ea.print l  in
          FStar_All.pipe_right uu____5738 (FStar_String.concat "; ")  in
        Prims.strcat uu____5737 "]"  in
      Prims.strcat "[" uu____5736  in
    let rec em l rng shadow_l norm1 =
      lazy_embed printer emb_t_list_a rng t_list_a l
        (fun uu____5817  ->
           let t =
             let uu____5819 = type_of ea  in
             FStar_Syntax_Syntax.iarg uu____5819  in
           match l with
           | [] ->
               let uu____5820 =
                 let uu____5825 =
                   let uu____5826 =
                     FStar_Syntax_Syntax.tdataconstr
                       FStar_Parser_Const.nil_lid
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____5826
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 FStar_Syntax_Syntax.mk_Tm_app uu____5825 [t]  in
               uu____5820 FStar_Pervasives_Native.None rng
           | hd1::tl1 ->
               let cons1 =
                 let uu____5850 =
                   FStar_Syntax_Syntax.tdataconstr
                     FStar_Parser_Const.cons_lid
                    in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu____5850
                   [FStar_Syntax_Syntax.U_zero]
                  in
               let proj f cons_tm =
                 let fid = FStar_Ident.mk_ident (f, rng)  in
                 let proj =
                   FStar_Syntax_Util.mk_field_projector_name_from_ident
                     FStar_Parser_Const.cons_lid fid
                    in
                 let proj_tm =
                   let uu____5867 =
                     FStar_Syntax_Syntax.lid_as_fv proj
                       FStar_Syntax_Syntax.delta_equational
                       FStar_Pervasives_Native.None
                      in
                   FStar_Syntax_Syntax.fv_to_tm uu____5867  in
                 let uu____5868 =
                   let uu____5873 =
                     FStar_Syntax_Syntax.mk_Tm_uinst proj_tm
                       [FStar_Syntax_Syntax.U_zero]
                      in
                   let uu____5874 =
                     let uu____5875 =
                       let uu____5884 = type_of ea  in
                       FStar_Syntax_Syntax.iarg uu____5884  in
                     let uu____5885 =
                       let uu____5896 = FStar_Syntax_Syntax.as_arg cons_tm
                          in
                       [uu____5896]  in
                     uu____5875 :: uu____5885  in
                   FStar_Syntax_Syntax.mk_Tm_app uu____5873 uu____5874  in
                 uu____5868 FStar_Pervasives_Native.None rng  in
               let shadow_hd = map_shadow shadow_l (proj "hd")  in
               let shadow_tl = map_shadow shadow_l (proj "tl")  in
               let uu____6047 =
                 let uu____6052 =
                   let uu____6053 =
                     let uu____6064 =
                       let uu____6073 =
                         let uu____6074 = embed ea hd1  in
                         uu____6074 rng shadow_hd norm1  in
                       FStar_Syntax_Syntax.as_arg uu____6073  in
                     let uu____6144 =
                       let uu____6155 =
                         let uu____6164 = em tl1 rng shadow_tl norm1  in
                         FStar_Syntax_Syntax.as_arg uu____6164  in
                       [uu____6155]  in
                     uu____6064 :: uu____6144  in
                   t :: uu____6053  in
                 FStar_Syntax_Syntax.mk_Tm_app cons1 uu____6052  in
               uu____6047 FStar_Pervasives_Native.None rng)
       in
    let rec un t0 w norm1 =
      let t = FStar_Syntax_Util.unmeta_safe t0  in
      lazy_unembed printer emb_t_list_a t t_list_a
        (fun t1  ->
           let uu____6278 = FStar_Syntax_Util.head_and_args' t1  in
           match uu____6278 with
           | (hd1,args) ->
               let uu____6319 =
                 let uu____6332 =
                   let uu____6333 = FStar_Syntax_Util.un_uinst hd1  in
                   uu____6333.FStar_Syntax_Syntax.n  in
                 (uu____6332, args)  in
               (match uu____6319 with
                | (FStar_Syntax_Syntax.Tm_fvar fv,uu____6349) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.nil_lid
                    -> FStar_Pervasives_Native.Some []
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(uu____6369,FStar_Pervasives_Native.Some
                       (FStar_Syntax_Syntax.Implicit uu____6370))::(hd2,FStar_Pervasives_Native.None
                                                                    )::
                   (tl1,FStar_Pervasives_Native.None )::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.cons_lid
                    ->
                    let uu____6411 =
                      let uu____6414 = unembed ea hd2  in uu____6414 w norm1
                       in
                    FStar_Util.bind_opt uu____6411
                      (fun hd3  ->
                         let uu____6432 = un tl1 w norm1  in
                         FStar_Util.bind_opt uu____6432
                           (fun tl2  ->
                              FStar_Pervasives_Native.Some (hd3 :: tl2)))
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(hd2,FStar_Pervasives_Native.None )::(tl1,FStar_Pervasives_Native.None
                                                            )::[])
                    when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.cons_lid
                    ->
                    let uu____6482 =
                      let uu____6485 = unembed ea hd2  in uu____6485 w norm1
                       in
                    FStar_Util.bind_opt uu____6482
                      (fun hd3  ->
                         let uu____6503 = un tl1 w norm1  in
                         FStar_Util.bind_opt uu____6503
                           (fun tl2  ->
                              FStar_Pervasives_Native.Some (hd3 :: tl2)))
                | uu____6520 ->
                    (if w
                     then
                       (let uu____6534 =
                          let uu____6539 =
                            let uu____6540 =
                              FStar_Syntax_Print.term_to_string t0  in
                            FStar_Util.format1 "Not an embedded list: %s"
                              uu____6540
                             in
                          (FStar_Errors.Warning_NotEmbedded, uu____6539)  in
                        FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                          uu____6534)
                     else ();
                     FStar_Pervasives_Native.None)))
       in
    let uu____6544 =
      let uu____6545 = type_of ea  in
      FStar_Syntax_Syntax.t_list_of uu____6545  in
    mk_emb_full em un uu____6544 printer emb_t_list_a
  
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
    match projectee with | Simpl  -> true | uu____6578 -> false
  
let (uu___is_Weak : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Weak  -> true | uu____6584 -> false
  
let (uu___is_HNF : norm_step -> Prims.bool) =
  fun projectee  -> match projectee with | HNF  -> true | uu____6590 -> false 
let (uu___is_Primops : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____6596 -> false
  
let (uu___is_Delta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Delta  -> true | uu____6602 -> false
  
let (uu___is_Zeta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Zeta  -> true | uu____6608 -> false
  
let (uu___is_Iota : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Iota  -> true | uu____6614 -> false
  
let (uu___is_Reify : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____6620 -> false
  
let (uu___is_UnfoldOnly : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____6629 -> false
  
let (__proj__UnfoldOnly__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldFully : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldFully _0 -> true | uu____6651 -> false
  
let (__proj__UnfoldFully__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldFully _0 -> _0 
let (uu___is_UnfoldAttr : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____6673 -> false
  
let (__proj__UnfoldAttr__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_NBE : norm_step -> Prims.bool) =
  fun projectee  -> match projectee with | NBE  -> true | uu____6692 -> false 
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
    let uu____6696 =
      FStar_Ident.lid_of_str "FStar.Syntax.Embeddings.norm_step"  in
    FStar_Syntax_Util.fvar_const uu____6696  in
  let emb_t_norm_step =
    let uu____6698 =
      let uu____6705 =
        FStar_All.pipe_right FStar_Parser_Const.norm_step_lid
          FStar_Ident.string_of_lid
         in
      (uu____6705, [])  in
    FStar_Syntax_Syntax.ET_app uu____6698  in
  let printer uu____6713 = "norm_step"  in
  let em n1 rng _topt norm1 =
    lazy_embed printer emb_t_norm_step rng t_norm_step1 n1
      (fun uu____6778  ->
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
             let uu____6782 =
               let uu____6787 =
                 let uu____6788 =
                   let uu____6797 =
                     let uu____6798 =
                       let uu____6805 = e_list e_string  in
                       embed uu____6805 l  in
                     uu____6798 rng FStar_Pervasives_Native.None norm1  in
                   FStar_Syntax_Syntax.as_arg uu____6797  in
                 [uu____6788]  in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldOnly uu____6787  in
             uu____6782 FStar_Pervasives_Native.None rng
         | UnfoldFully l ->
             let uu____6860 =
               let uu____6865 =
                 let uu____6866 =
                   let uu____6875 =
                     let uu____6876 =
                       let uu____6883 = e_list e_string  in
                       embed uu____6883 l  in
                     uu____6876 rng FStar_Pervasives_Native.None norm1  in
                   FStar_Syntax_Syntax.as_arg uu____6875  in
                 [uu____6866]  in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldFully uu____6865  in
             uu____6860 FStar_Pervasives_Native.None rng
         | UnfoldAttr l ->
             let uu____6938 =
               let uu____6943 =
                 let uu____6944 =
                   let uu____6953 =
                     let uu____6954 =
                       let uu____6961 = e_list e_string  in
                       embed uu____6961 l  in
                     uu____6954 rng FStar_Pervasives_Native.None norm1  in
                   FStar_Syntax_Syntax.as_arg uu____6953  in
                 [uu____6944]  in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldAttr uu____6943  in
             uu____6938 FStar_Pervasives_Native.None rng)
     in
  let un t0 w norm1 =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    lazy_unembed printer emb_t_norm_step t t_norm_step1
      (fun t1  ->
         let uu____7045 = FStar_Syntax_Util.head_and_args t1  in
         match uu____7045 with
         | (hd1,args) ->
             let uu____7090 =
               let uu____7105 =
                 let uu____7106 = FStar_Syntax_Util.un_uinst hd1  in
                 uu____7106.FStar_Syntax_Syntax.n  in
               (uu____7105, args)  in
             (match uu____7090 with
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
              | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____7294)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldonly
                  ->
                  let uu____7329 =
                    let uu____7334 =
                      let uu____7343 = e_list e_string  in
                      unembed uu____7343 l  in
                    uu____7334 w norm1  in
                  FStar_Util.bind_opt uu____7329
                    (fun ss  ->
                       FStar_All.pipe_left
                         (fun _0_16  -> FStar_Pervasives_Native.Some _0_16)
                         (UnfoldOnly ss))
              | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____7366)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldfully
                  ->
                  let uu____7401 =
                    let uu____7406 =
                      let uu____7415 = e_list e_string  in
                      unembed uu____7415 l  in
                    uu____7406 w norm1  in
                  FStar_Util.bind_opt uu____7401
                    (fun ss  ->
                       FStar_All.pipe_left
                         (fun _0_17  -> FStar_Pervasives_Native.Some _0_17)
                         (UnfoldFully ss))
              | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____7438)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldattr
                  ->
                  let uu____7473 =
                    let uu____7478 =
                      let uu____7487 = e_list e_string  in
                      unembed uu____7487 l  in
                    uu____7478 w norm1  in
                  FStar_Util.bind_opt uu____7473
                    (fun ss  ->
                       FStar_All.pipe_left
                         (fun _0_18  -> FStar_Pervasives_Native.Some _0_18)
                         (UnfoldAttr ss))
              | uu____7508 ->
                  (if w
                   then
                     (let uu____7524 =
                        let uu____7529 =
                          let uu____7530 =
                            FStar_Syntax_Print.term_to_string t0  in
                          FStar_Util.format1 "Not an embedded norm_step: %s"
                            uu____7530
                           in
                        (FStar_Errors.Warning_NotEmbedded, uu____7529)  in
                      FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                        uu____7524)
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
    | uu____7625 ->
        (if w
         then
           (let uu____7627 =
              let uu____7632 =
                let uu____7633 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded range: %s" uu____7633  in
              (FStar_Errors.Warning_NotEmbedded, uu____7632)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____7627)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____7635 =
    let uu____7636 =
      let uu____7643 =
        FStar_All.pipe_right FStar_Parser_Const.range_lid
          FStar_Ident.string_of_lid
         in
      (uu____7643, [])  in
    FStar_Syntax_Syntax.ET_app uu____7636  in
  mk_emb_full em un FStar_Syntax_Syntax.t_range FStar_Range.string_of_range
    uu____7635
  
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
        let uu____7709 =
          let uu____7716 =
            let uu____7717 =
              let uu____7732 =
                let uu____7741 =
                  let uu____7748 = FStar_Syntax_Syntax.null_bv ea.typ  in
                  (uu____7748, FStar_Pervasives_Native.None)  in
                [uu____7741]  in
              let uu____7763 = FStar_Syntax_Syntax.mk_Total eb.typ  in
              (uu____7732, uu____7763)  in
            FStar_Syntax_Syntax.Tm_arrow uu____7717  in
          FStar_Syntax_Syntax.mk uu____7716  in
        uu____7709 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
      let emb_t_arr_a_b =
        FStar_Syntax_Syntax.ET_fun ((ea.emb_typ), (eb.emb_typ))  in
      let printer f = "<fun>"  in
      let em f rng shadow_f norm1 =
        lazy_embed (fun uu____7874  -> "<fun>") emb_t_arr_a_b rng t_arrow f
          (fun uu____7879  ->
             let uu____7880 = force_shadow shadow_f  in
             match uu____7880 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Exn.raise Embedding_failure
             | FStar_Pervasives_Native.Some repr_f ->
                 ((let uu____7942 =
                     FStar_ST.op_Bang FStar_Options.debug_embedding  in
                   if uu____7942
                   then
                     let uu____7962 =
                       FStar_Syntax_Print.term_to_string repr_f  in
                     let uu____7963 = FStar_Util.stack_dump ()  in
                     FStar_Util.print2
                       "e_arrow forced back to term using shadow %s; repr=%s\n"
                       uu____7962 uu____7963
                   else ());
                  (let res = norm1 (FStar_Util.Inr repr_f)  in
                   (let uu____7967 =
                      FStar_ST.op_Bang FStar_Options.debug_embedding  in
                    if uu____7967
                    then
                      let uu____7987 =
                        FStar_Syntax_Print.term_to_string repr_f  in
                      let uu____7988 = FStar_Syntax_Print.term_to_string res
                         in
                      let uu____7989 = FStar_Util.stack_dump ()  in
                      FStar_Util.print3
                        "e_arrow forced back to term using shadow %s; repr=%s\n\t%s\n"
                        uu____7987 uu____7988 uu____7989
                    else ());
                   res)))
         in
      let un f w norm1 =
        lazy_unembed printer emb_t_arr_a_b f t_arrow
          (fun f1  ->
             let f_wrapped a =
               (let uu____8043 =
                  FStar_ST.op_Bang FStar_Options.debug_embedding  in
                if uu____8043
                then
                  let uu____8063 = FStar_Syntax_Print.term_to_string f1  in
                  let uu____8064 = FStar_Util.stack_dump ()  in
                  FStar_Util.print2
                    "Calling back into normalizer for %s\n%s\n" uu____8063
                    uu____8064
                else ());
               (let a_tm =
                  let uu____8067 = embed ea a  in
                  uu____8067 f1.FStar_Syntax_Syntax.pos
                    FStar_Pervasives_Native.None norm1
                   in
                let b_tm =
                  let uu____8100 =
                    let uu____8105 =
                      let uu____8106 =
                        let uu____8111 =
                          let uu____8112 = FStar_Syntax_Syntax.as_arg a_tm
                             in
                          [uu____8112]  in
                        FStar_Syntax_Syntax.mk_Tm_app f1 uu____8111  in
                      uu____8106 FStar_Pervasives_Native.None
                        f1.FStar_Syntax_Syntax.pos
                       in
                    FStar_Util.Inr uu____8105  in
                  norm1 uu____8100  in
                let uu____8139 =
                  let uu____8142 = unembed eb b_tm  in uu____8142 w norm1  in
                match uu____8139 with
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
                let uu____8239 = FStar_List.splitAt n_tvars args  in
                match uu____8239 with
                | (_tvar_args,rest_args) ->
                    let uu____8316 = FStar_List.hd rest_args  in
                    (match uu____8316 with
                     | (x,uu____8336) ->
                         let shadow_app =
                           let uu____8350 =
                             FStar_Common.mk_thunk
                               (fun uu____8359  ->
                                  let uu____8360 =
                                    let uu____8365 =
                                      norm1 (FStar_Util.Inl fv_lid1)  in
                                    FStar_Syntax_Syntax.mk_Tm_app uu____8365
                                      args
                                     in
                                  uu____8360 FStar_Pervasives_Native.None rng)
                              in
                           FStar_Pervasives_Native.Some uu____8350  in
                         let uu____8411 =
                           let uu____8414 =
                             let uu____8417 = unembed ea x  in
                             uu____8417 true norm1  in
                           FStar_Util.map_opt uu____8414
                             (fun x1  ->
                                let uu____8456 =
                                  let uu____8463 = f x1  in
                                  embed eb uu____8463  in
                                uu____8456 rng shadow_app norm1)
                            in
                         (match uu____8411 with
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
                  let uu____8590 = FStar_List.splitAt n_tvars args  in
                  match uu____8590 with
                  | (_tvar_args,rest_args) ->
                      let uu____8653 = FStar_List.hd rest_args  in
                      (match uu____8653 with
                       | (x,uu____8669) ->
                           let uu____8674 =
                             let uu____8681 = FStar_List.tl rest_args  in
                             FStar_List.hd uu____8681  in
                           (match uu____8674 with
                            | (y,uu____8705) ->
                                let shadow_app =
                                  let uu____8715 =
                                    FStar_Common.mk_thunk
                                      (fun uu____8724  ->
                                         let uu____8725 =
                                           let uu____8730 =
                                             norm1 (FStar_Util.Inl fv_lid1)
                                              in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____8730 args
                                            in
                                         uu____8725
                                           FStar_Pervasives_Native.None rng)
                                     in
                                  FStar_Pervasives_Native.Some uu____8715  in
                                let uu____8776 =
                                  let uu____8779 =
                                    let uu____8782 = unembed ea x  in
                                    uu____8782 true norm1  in
                                  FStar_Util.bind_opt uu____8779
                                    (fun x1  ->
                                       let uu____8798 =
                                         let uu____8801 = unembed eb y  in
                                         uu____8801 true norm1  in
                                       FStar_Util.bind_opt uu____8798
                                         (fun y1  ->
                                            let uu____8817 =
                                              let uu____8818 =
                                                let uu____8825 = f x1 y1  in
                                                embed ec uu____8825  in
                                              uu____8818 rng shadow_app norm1
                                               in
                                            FStar_Pervasives_Native.Some
                                              uu____8817))
                                   in
                                (match uu____8776 with
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
                    let uu____8971 = FStar_List.splitAt n_tvars args  in
                    match uu____8971 with
                    | (_tvar_args,rest_args) ->
                        let uu____9034 = FStar_List.hd rest_args  in
                        (match uu____9034 with
                         | (x,uu____9050) ->
                             let uu____9055 =
                               let uu____9062 = FStar_List.tl rest_args  in
                               FStar_List.hd uu____9062  in
                             (match uu____9055 with
                              | (y,uu____9086) ->
                                  let uu____9091 =
                                    let uu____9098 =
                                      let uu____9107 =
                                        FStar_List.tl rest_args  in
                                      FStar_List.tl uu____9107  in
                                    FStar_List.hd uu____9098  in
                                  (match uu____9091 with
                                   | (z,uu____9137) ->
                                       let shadow_app =
                                         let uu____9147 =
                                           FStar_Common.mk_thunk
                                             (fun uu____9156  ->
                                                let uu____9157 =
                                                  let uu____9162 =
                                                    norm1
                                                      (FStar_Util.Inl fv_lid1)
                                                     in
                                                  FStar_Syntax_Syntax.mk_Tm_app
                                                    uu____9162 args
                                                   in
                                                uu____9157
                                                  FStar_Pervasives_Native.None
                                                  rng)
                                            in
                                         FStar_Pervasives_Native.Some
                                           uu____9147
                                          in
                                       let uu____9208 =
                                         let uu____9211 =
                                           let uu____9214 = unembed ea x  in
                                           uu____9214 true norm1  in
                                         FStar_Util.bind_opt uu____9211
                                           (fun x1  ->
                                              let uu____9230 =
                                                let uu____9233 = unembed eb y
                                                   in
                                                uu____9233 true norm1  in
                                              FStar_Util.bind_opt uu____9230
                                                (fun y1  ->
                                                   let uu____9249 =
                                                     let uu____9252 =
                                                       unembed ec z  in
                                                     uu____9252 true norm1
                                                      in
                                                   FStar_Util.bind_opt
                                                     uu____9249
                                                     (fun z1  ->
                                                        let uu____9268 =
                                                          let uu____9269 =
                                                            let uu____9276 =
                                                              f x1 y1 z1  in
                                                            embed ed
                                                              uu____9276
                                                             in
                                                          uu____9269 rng
                                                            shadow_app norm1
                                                           in
                                                        FStar_Pervasives_Native.Some
                                                          uu____9268)))
                                          in
                                       (match uu____9208 with
                                        | FStar_Pervasives_Native.Some x1 ->
                                            FStar_Pervasives_Native.Some x1
                                        | FStar_Pervasives_Native.None  ->
                                            force_shadow shadow_app))))
                     in
                  f_wrapped
  
let debug_wrap : 'a . Prims.string -> (unit -> 'a) -> 'a =
  fun s  ->
    fun f  ->
      (let uu____9328 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
       if uu____9328 then FStar_Util.print1 "++++starting %s\n" s else ());
      (let res = f ()  in
       (let uu____9351 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
        if uu____9351 then FStar_Util.print1 "------ending %s\n" s else ());
       res)
  