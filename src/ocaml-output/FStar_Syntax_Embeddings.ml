open Prims
type norm_cb =
  (FStar_Ident.lid,FStar_Syntax_Syntax.term) FStar_Util.either ->
    FStar_Syntax_Syntax.term
let (id_norm_cb : norm_cb) =
  fun uu___216_13  ->
    match uu___216_13 with
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
    match projectee with | Embedding_failure  -> true | uu____30 -> false
  
exception Unembedding_failure 
let (uu___is_Unembedding_failure : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unembedding_failure  -> true | uu____41 -> false
  
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
             (fun uu____207  ->
                let uu____208 = FStar_Common.force_thunk s1  in f uu____208))
  
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
  'Auu____842 . FStar_Syntax_Syntax.term -> 'Auu____842 -> Prims.string =
  fun typ  ->
    fun uu____853  ->
      let uu____854 = FStar_Syntax_Print.term_to_string typ  in
      FStar_Util.format1 "unknown %s" uu____854
  
let (term_as_fv : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.fv) =
  fun t  ->
    let uu____863 =
      let uu____864 = FStar_Syntax_Subst.compress t  in
      uu____864.FStar_Syntax_Syntax.n  in
    match uu____863 with
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv
    | uu____868 ->
        let uu____869 =
          let uu____871 = FStar_Syntax_Print.term_to_string t  in
          FStar_Util.format1 "Embeddings not defined for type %s" uu____871
           in
        failwith uu____869
  
let mk_emb :
  'a .
    'a raw_embedder ->
      'a raw_unembedder -> FStar_Syntax_Syntax.fv -> 'a embedding
  =
  fun em  ->
    fun un  ->
      fun fv  ->
        let typ = FStar_Syntax_Syntax.fv_to_tm fv  in
        let uu____999 =
          let uu____1000 =
            let uu____1008 =
              let uu____1010 = FStar_Syntax_Syntax.lid_of_fv fv  in
              FStar_All.pipe_right uu____1010 FStar_Ident.string_of_lid  in
            (uu____1008, [])  in
          FStar_Syntax_Syntax.ET_app uu____1000  in
        { em; un; typ; print = (unknown_printer typ); emb_typ = uu____999 }
  
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
    fun t  -> fun n1  -> let uu____1420 = unembed e t  in uu____1420 true n1
  
let try_unembed :
  'a .
    'a embedding ->
      FStar_Syntax_Syntax.term ->
        norm_cb -> 'a FStar_Pervasives_Native.option
  =
  fun e  ->
    fun t  -> fun n1  -> let uu____1469 = unembed e t  in uu____1469 false n1
  
let type_of : 'a . 'a embedding -> FStar_Syntax_Syntax.typ = fun e  -> e.typ 
let set_type : 'a . FStar_Syntax_Syntax.typ -> 'a embedding -> 'a embedding =
  fun ty  ->
    fun e  ->
      let uu___218_1522 = e  in
      {
        em = (uu___218_1522.em);
        un = (uu___218_1522.un);
        typ = ty;
        print = (uu___218_1522.print);
        emb_typ = (uu___218_1522.emb_typ)
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
              (let uu____1591 =
                 FStar_ST.op_Bang FStar_Options.debug_embedding  in
               if uu____1591
               then
                 let uu____1615 = FStar_Syntax_Print.term_to_string ta  in
                 let uu____1617 = FStar_Syntax_Print.emb_typ_to_string et  in
                 let uu____1619 = pa x  in
                 FStar_Util.print3
                   "Embedding a %s\n\temb_typ=%s\n\tvalue is %s\n" uu____1615
                   uu____1617 uu____1619
               else ());
              (let uu____1626 =
                 FStar_ST.op_Bang FStar_Options.eager_embedding  in
               if uu____1626
               then f ()
               else
                 (let thunk1 = FStar_Common.mk_thunk f  in
                  let uu____1661 =
                    let uu____1668 =
                      let uu____1669 =
                        let uu____1670 = FStar_Dyn.mkdyn x  in
                        {
                          FStar_Syntax_Syntax.blob = uu____1670;
                          FStar_Syntax_Syntax.lkind =
                            (FStar_Syntax_Syntax.Lazy_embedding (et, thunk1));
                          FStar_Syntax_Syntax.ltyp = FStar_Syntax_Syntax.tun;
                          FStar_Syntax_Syntax.rng = rng
                        }  in
                      FStar_Syntax_Syntax.Tm_lazy uu____1669  in
                    FStar_Syntax_Syntax.mk uu____1668  in
                  uu____1661 FStar_Pervasives_Native.None rng))
  
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
                  FStar_Syntax_Syntax.ltyp = uu____1786;
                  FStar_Syntax_Syntax.rng = uu____1787;_}
                ->
                let uu____1798 =
                  (et <> et') ||
                    (FStar_ST.op_Bang FStar_Options.eager_embedding)
                   in
                if uu____1798
                then
                  let res =
                    let uu____1827 = FStar_Common.force_thunk t  in
                    f uu____1827  in
                  ((let uu____1871 =
                      FStar_ST.op_Bang FStar_Options.debug_embedding  in
                    if uu____1871
                    then
                      let uu____1895 =
                        FStar_Syntax_Print.emb_typ_to_string et  in
                      let uu____1897 =
                        FStar_Syntax_Print.emb_typ_to_string et'  in
                      let uu____1899 =
                        match res with
                        | FStar_Pervasives_Native.None  -> "None"
                        | FStar_Pervasives_Native.Some x2 ->
                            let uu____1904 = pa x2  in
                            Prims.strcat "Some " uu____1904
                         in
                      FStar_Util.print3
                        "Unembed cancellation failed\n\t%s <> %s\nvalue is %s\n"
                        uu____1895 uu____1897 uu____1899
                    else ());
                   res)
                else
                  (let a = FStar_Dyn.undyn b  in
                   (let uu____1916 =
                      FStar_ST.op_Bang FStar_Options.debug_embedding  in
                    if uu____1916
                    then
                      let uu____1940 =
                        FStar_Syntax_Print.emb_typ_to_string et  in
                      let uu____1942 = pa a  in
                      FStar_Util.print2
                        "Unembed cancelled for %s\n\tvalue is %s\n"
                        uu____1940 uu____1942
                    else ());
                   FStar_Pervasives_Native.Some a)
            | uu____1949 ->
                let aopt = f x1  in
                ((let uu____1954 =
                    FStar_ST.op_Bang FStar_Options.debug_embedding  in
                  if uu____1954
                  then
                    let uu____1978 = FStar_Syntax_Print.emb_typ_to_string et
                       in
                    let uu____1980 = FStar_Syntax_Print.term_to_string x1  in
                    let uu____1982 =
                      match aopt with
                      | FStar_Pervasives_Native.None  -> "None"
                      | FStar_Pervasives_Native.Some a ->
                          let uu____1987 = pa a  in
                          Prims.strcat "Some " uu____1987
                       in
                    FStar_Util.print3
                      "Unembedding:\n\temb_typ=%s\n\tterm is %s\n\tvalue is %s\n"
                      uu____1978 uu____1980 uu____1982
                  else ());
                 aopt)
  
let (mk_any_emb :
  FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term embedding) =
  fun typ  ->
    let em t _r _topt _norm =
      (let uu____2067 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
       if uu____2067
       then
         let uu____2091 = unknown_printer typ t  in
         FStar_Util.print1 "Embedding abstract: %s\n" uu____2091
       else ());
      t  in
    let un t _w _n =
      (let uu____2121 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
       if uu____2121
       then
         let uu____2145 = unknown_printer typ t  in
         FStar_Util.print1 "Unembedding abstract: %s\n" uu____2145
       else ());
      FStar_Pervasives_Native.Some t  in
    mk_emb_full em un typ (unknown_printer typ)
      FStar_Syntax_Syntax.ET_abstract
  
let (e_any : FStar_Syntax_Syntax.term embedding) =
  let em t _r _topt _norm = t  in
  let un t _w _n = FStar_Pervasives_Native.Some t  in
  let uu____2240 =
    let uu____2241 =
      let uu____2249 =
        FStar_All.pipe_right FStar_Parser_Const.term_lid
          FStar_Ident.string_of_lid
         in
      (uu____2249, [])  in
    FStar_Syntax_Syntax.ET_app uu____2241  in
  mk_emb_full em un FStar_Syntax_Syntax.t_term
    FStar_Syntax_Print.term_to_string uu____2240
  
let (e_unit : unit embedding) =
  let em u rng _topt _norm =
    let uu___219_2321 = FStar_Syntax_Util.exp_unit  in
    {
      FStar_Syntax_Syntax.n = (uu___219_2321.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___219_2321.FStar_Syntax_Syntax.vars)
    }  in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unascribe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit ) ->
        FStar_Pervasives_Native.Some ()
    | uu____2351 ->
        (if w
         then
           (let uu____2354 =
              let uu____2360 =
                let uu____2362 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded unit: %s" uu____2362  in
              (FStar_Errors.Warning_NotEmbedded, uu____2360)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____2354)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____2368 =
    let uu____2369 =
      let uu____2377 =
        FStar_All.pipe_right FStar_Parser_Const.unit_lid
          FStar_Ident.string_of_lid
         in
      (uu____2377, [])  in
    FStar_Syntax_Syntax.ET_app uu____2369  in
  mk_emb_full em un FStar_Syntax_Syntax.t_unit (fun uu____2384  -> "()")
    uu____2368
  
let (e_bool : Prims.bool embedding) =
  let em b rng _topt _norm =
    let t =
      if b
      then FStar_Syntax_Util.exp_true_bool
      else FStar_Syntax_Util.exp_false_bool  in
    let uu___220_2463 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___220_2463.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___220_2463.FStar_Syntax_Syntax.vars)
    }  in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) ->
        FStar_Pervasives_Native.Some b
    | uu____2501 ->
        (if w
         then
           (let uu____2504 =
              let uu____2510 =
                let uu____2512 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded bool: %s" uu____2512  in
              (FStar_Errors.Warning_NotEmbedded, uu____2510)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____2504)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____2519 =
    let uu____2520 =
      let uu____2528 =
        FStar_All.pipe_right FStar_Parser_Const.bool_lid
          FStar_Ident.string_of_lid
         in
      (uu____2528, [])  in
    FStar_Syntax_Syntax.ET_app uu____2520  in
  mk_emb_full em un FStar_Syntax_Syntax.t_bool FStar_Util.string_of_bool
    uu____2519
  
let (e_char : FStar_Char.char embedding) =
  let em c rng _topt _norm =
    let t = FStar_Syntax_Util.exp_char c  in
    let uu___221_2605 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___221_2605.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___221_2605.FStar_Syntax_Syntax.vars)
    }  in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c) ->
        FStar_Pervasives_Native.Some c
    | uu____2641 ->
        (if w
         then
           (let uu____2644 =
              let uu____2650 =
                let uu____2652 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded char: %s" uu____2652  in
              (FStar_Errors.Warning_NotEmbedded, uu____2650)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____2644)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____2659 =
    let uu____2660 =
      let uu____2668 =
        FStar_All.pipe_right FStar_Parser_Const.char_lid
          FStar_Ident.string_of_lid
         in
      (uu____2668, [])  in
    FStar_Syntax_Syntax.ET_app uu____2660  in
  mk_emb_full em un FStar_Syntax_Syntax.t_char FStar_Util.string_of_char
    uu____2659
  
let (e_int : FStar_BigInt.t embedding) =
  let t_int1 = FStar_Syntax_Util.fvar_const FStar_Parser_Const.int_lid  in
  let emb_t_int =
    let uu____2680 =
      let uu____2688 =
        FStar_All.pipe_right FStar_Parser_Const.int_lid
          FStar_Ident.string_of_lid
         in
      (uu____2688, [])  in
    FStar_Syntax_Syntax.ET_app uu____2680  in
  let em i rng _topt _norm =
    lazy_embed FStar_BigInt.string_of_big_int emb_t_int rng t_int1 i
      (fun uu____2759  ->
         let uu____2760 = FStar_BigInt.string_of_big_int i  in
         FStar_Syntax_Util.exp_int uu____2760)
     in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    lazy_unembed FStar_BigInt.string_of_big_int emb_t_int t t_int1
      (fun t1  ->
         match t1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
             (s,uu____2797)) ->
             let uu____2812 = FStar_BigInt.big_int_of_string s  in
             FStar_Pervasives_Native.Some uu____2812
         | uu____2813 ->
             (if w
              then
                (let uu____2816 =
                   let uu____2822 =
                     let uu____2824 = FStar_Syntax_Print.term_to_string t0
                        in
                     FStar_Util.format1 "Not an embedded int: %s" uu____2824
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____2822)  in
                 FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____2816)
              else ();
              FStar_Pervasives_Native.None))
     in
  mk_emb_full em un FStar_Syntax_Syntax.t_int FStar_BigInt.string_of_big_int
    emb_t_int
  
let (e_string : Prims.string embedding) =
  let emb_t_string =
    let uu____2835 =
      let uu____2843 =
        FStar_All.pipe_right FStar_Parser_Const.string_lid
          FStar_Ident.string_of_lid
         in
      (uu____2843, [])  in
    FStar_Syntax_Syntax.ET_app uu____2835  in
  let em s rng _topt _norm =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, rng)))
      FStar_Pervasives_Native.None rng
     in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
        (s,uu____2948)) -> FStar_Pervasives_Native.Some s
    | uu____2952 ->
        (if w
         then
           (let uu____2955 =
              let uu____2961 =
                let uu____2963 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded string: %s" uu____2963
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____2961)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____2955)
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
      let uu____2999 =
        let uu____3004 =
          let uu____3005 = FStar_Syntax_Syntax.as_arg ea.typ  in [uu____3005]
           in
        FStar_Syntax_Syntax.mk_Tm_app t_opt uu____3004  in
      uu____2999 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
    let emb_t_option_a =
      let uu____3033 =
        let uu____3041 =
          FStar_All.pipe_right FStar_Parser_Const.option_lid
            FStar_Ident.string_of_lid
           in
        (uu____3041, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____3033  in
    let printer uu___217_3055 =
      match uu___217_3055 with
      | FStar_Pervasives_Native.None  -> "None"
      | FStar_Pervasives_Native.Some x ->
          let uu____3061 =
            let uu____3063 = ea.print x  in Prims.strcat uu____3063 ")"  in
          Prims.strcat "(Some " uu____3061
       in
    let em o rng topt norm1 =
      lazy_embed printer emb_t_option_a rng t_option_a o
        (fun uu____3140  ->
           match o with
           | FStar_Pervasives_Native.None  ->
               let uu____3141 =
                 let uu____3146 =
                   let uu____3147 =
                     FStar_Syntax_Syntax.tdataconstr
                       FStar_Parser_Const.none_lid
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____3147
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 let uu____3148 =
                   let uu____3149 =
                     let uu____3158 = type_of ea  in
                     FStar_Syntax_Syntax.iarg uu____3158  in
                   [uu____3149]  in
                 FStar_Syntax_Syntax.mk_Tm_app uu____3146 uu____3148  in
               uu____3141 FStar_Pervasives_Native.None rng
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
                        let uu____3249 =
                          FStar_Syntax_Syntax.lid_as_fv some_v
                            FStar_Syntax_Syntax.delta_equational
                            FStar_Pervasives_Native.None
                           in
                        FStar_Syntax_Syntax.fv_to_tm uu____3249  in
                      let uu____3250 =
                        let uu____3255 =
                          FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm
                            [FStar_Syntax_Syntax.U_zero]
                           in
                        let uu____3256 =
                          let uu____3257 =
                            let uu____3266 = type_of ea  in
                            FStar_Syntax_Syntax.iarg uu____3266  in
                          let uu____3267 =
                            let uu____3278 = FStar_Syntax_Syntax.as_arg t  in
                            [uu____3278]  in
                          uu____3257 :: uu____3267  in
                        FStar_Syntax_Syntax.mk_Tm_app uu____3255 uu____3256
                         in
                      uu____3250 FStar_Pervasives_Native.None rng)
                  in
               let uu____3313 =
                 let uu____3318 =
                   let uu____3319 =
                     FStar_Syntax_Syntax.tdataconstr
                       FStar_Parser_Const.some_lid
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____3319
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 let uu____3320 =
                   let uu____3321 =
                     let uu____3330 = type_of ea  in
                     FStar_Syntax_Syntax.iarg uu____3330  in
                   let uu____3331 =
                     let uu____3342 =
                       let uu____3351 =
                         let uu____3352 = embed ea a  in
                         uu____3352 rng shadow_a norm1  in
                       FStar_Syntax_Syntax.as_arg uu____3351  in
                     [uu____3342]  in
                   uu____3321 :: uu____3331  in
                 FStar_Syntax_Syntax.mk_Tm_app uu____3318 uu____3320  in
               uu____3313 FStar_Pervasives_Native.None rng)
       in
    let un t0 w norm1 =
      let t = FStar_Syntax_Util.unmeta_safe t0  in
      lazy_unembed printer emb_t_option_a t t_option_a
        (fun t1  ->
           let uu____3489 = FStar_Syntax_Util.head_and_args' t1  in
           match uu____3489 with
           | (hd1,args) ->
               let uu____3530 =
                 let uu____3545 =
                   let uu____3546 = FStar_Syntax_Util.un_uinst hd1  in
                   uu____3546.FStar_Syntax_Syntax.n  in
                 (uu____3545, args)  in
               (match uu____3530 with
                | (FStar_Syntax_Syntax.Tm_fvar fv,uu____3564) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.none_lid
                    ->
                    FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,uu____3588::(a,uu____3590)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.some_lid
                    ->
                    let uu____3641 =
                      let uu____3644 = unembed ea a  in uu____3644 w norm1
                       in
                    FStar_Util.bind_opt uu____3641
                      (fun a1  ->
                         FStar_Pervasives_Native.Some
                           (FStar_Pervasives_Native.Some a1))
                | uu____3663 ->
                    (if w
                     then
                       (let uu____3680 =
                          let uu____3686 =
                            let uu____3688 =
                              FStar_Syntax_Print.term_to_string t0  in
                            FStar_Util.format1 "Not an embedded option: %s"
                              uu____3688
                             in
                          (FStar_Errors.Warning_NotEmbedded, uu____3686)  in
                        FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                          uu____3680)
                     else ();
                     FStar_Pervasives_Native.None)))
       in
    let uu____3696 =
      let uu____3697 = type_of ea  in
      FStar_Syntax_Syntax.t_option_of uu____3697  in
    mk_emb_full em un uu____3696 printer emb_t_option_a
  
let e_tuple2 : 'a 'b . 'a embedding -> 'b embedding -> ('a * 'b) embedding =
  fun ea  ->
    fun eb  ->
      let t_pair_a_b =
        let t_tup2 =
          FStar_Syntax_Util.fvar_const FStar_Parser_Const.lid_tuple2  in
        let uu____3739 =
          let uu____3744 =
            let uu____3745 = FStar_Syntax_Syntax.as_arg ea.typ  in
            let uu____3754 =
              let uu____3765 = FStar_Syntax_Syntax.as_arg eb.typ  in
              [uu____3765]  in
            uu____3745 :: uu____3754  in
          FStar_Syntax_Syntax.mk_Tm_app t_tup2 uu____3744  in
        uu____3739 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
      let emb_t_pair_a_b =
        let uu____3801 =
          let uu____3809 =
            FStar_All.pipe_right FStar_Parser_Const.lid_tuple2
              FStar_Ident.string_of_lid
             in
          (uu____3809, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____3801  in
      let printer uu____3825 =
        match uu____3825 with
        | (x,y) ->
            let uu____3833 = ea.print x  in
            let uu____3835 = eb.print y  in
            FStar_Util.format2 "(%s, %s)" uu____3833 uu____3835
         in
      let em x rng topt norm1 =
        lazy_embed printer emb_t_pair_a_b rng t_pair_a_b x
          (fun uu____3920  ->
             let proj i ab =
               let uu____3936 =
                 let uu____3941 =
                   FStar_Parser_Const.mk_tuple_data_lid (Prims.parse_int "2")
                     rng
                    in
                 let uu____3943 =
                   FStar_Syntax_Syntax.null_bv FStar_Syntax_Syntax.tun  in
                 FStar_Syntax_Util.mk_field_projector_name uu____3941
                   uu____3943 i
                  in
               match uu____3936 with
               | (proj_1,uu____3947) ->
                   let proj_1_tm =
                     let uu____3949 =
                       FStar_Syntax_Syntax.lid_as_fv proj_1
                         FStar_Syntax_Syntax.delta_equational
                         FStar_Pervasives_Native.None
                        in
                     FStar_Syntax_Syntax.fv_to_tm uu____3949  in
                   let uu____3950 =
                     let uu____3955 =
                       FStar_Syntax_Syntax.mk_Tm_uinst proj_1_tm
                         [FStar_Syntax_Syntax.U_zero]
                        in
                     let uu____3956 =
                       let uu____3957 =
                         let uu____3966 = type_of ea  in
                         FStar_Syntax_Syntax.iarg uu____3966  in
                       let uu____3967 =
                         let uu____3978 =
                           let uu____3987 = type_of eb  in
                           FStar_Syntax_Syntax.iarg uu____3987  in
                         let uu____3988 =
                           let uu____3999 = FStar_Syntax_Syntax.as_arg ab  in
                           [uu____3999]  in
                         uu____3978 :: uu____3988  in
                       uu____3957 :: uu____3967  in
                     FStar_Syntax_Syntax.mk_Tm_app uu____3955 uu____3956  in
                   uu____3950 FStar_Pervasives_Native.None rng
                in
             let shadow_a = map_shadow topt (proj (Prims.parse_int "1"))  in
             let shadow_b = map_shadow topt (proj (Prims.parse_int "2"))  in
             let uu____4160 =
               let uu____4165 =
                 let uu____4166 =
                   FStar_Syntax_Syntax.tdataconstr
                     FStar_Parser_Const.lid_Mktuple2
                    in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu____4166
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                  in
               let uu____4167 =
                 let uu____4168 =
                   let uu____4177 = type_of ea  in
                   FStar_Syntax_Syntax.iarg uu____4177  in
                 let uu____4178 =
                   let uu____4189 =
                     let uu____4198 = type_of eb  in
                     FStar_Syntax_Syntax.iarg uu____4198  in
                   let uu____4199 =
                     let uu____4210 =
                       let uu____4219 =
                         let uu____4220 =
                           embed ea (FStar_Pervasives_Native.fst x)  in
                         uu____4220 rng shadow_a norm1  in
                       FStar_Syntax_Syntax.as_arg uu____4219  in
                     let uu____4290 =
                       let uu____4301 =
                         let uu____4310 =
                           let uu____4311 =
                             embed eb (FStar_Pervasives_Native.snd x)  in
                           uu____4311 rng shadow_b norm1  in
                         FStar_Syntax_Syntax.as_arg uu____4310  in
                       [uu____4301]  in
                     uu____4210 :: uu____4290  in
                   uu____4189 :: uu____4199  in
                 uu____4168 :: uu____4178  in
               FStar_Syntax_Syntax.mk_Tm_app uu____4165 uu____4167  in
             uu____4160 FStar_Pervasives_Native.None rng)
         in
      let un t0 w norm1 =
        let t = FStar_Syntax_Util.unmeta_safe t0  in
        lazy_unembed printer emb_t_pair_a_b t t_pair_a_b
          (fun t1  ->
             let uu____4476 = FStar_Syntax_Util.head_and_args' t1  in
             match uu____4476 with
             | (hd1,args) ->
                 let uu____4519 =
                   let uu____4532 =
                     let uu____4533 = FStar_Syntax_Util.un_uinst hd1  in
                     uu____4533.FStar_Syntax_Syntax.n  in
                   (uu____4532, args)  in
                 (match uu____4519 with
                  | (FStar_Syntax_Syntax.Tm_fvar
                     fv,uu____4551::uu____4552::(a,uu____4554)::(b,uu____4556)::[])
                      when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.lid_Mktuple2
                      ->
                      let uu____4615 =
                        let uu____4618 = unembed ea a  in uu____4618 w norm1
                         in
                      FStar_Util.bind_opt uu____4615
                        (fun a1  ->
                           let uu____4638 =
                             let uu____4641 = unembed eb b  in
                             uu____4641 w norm1  in
                           FStar_Util.bind_opt uu____4638
                             (fun b1  ->
                                FStar_Pervasives_Native.Some (a1, b1)))
                  | uu____4664 ->
                      (if w
                       then
                         (let uu____4679 =
                            let uu____4685 =
                              let uu____4687 =
                                FStar_Syntax_Print.term_to_string t0  in
                              FStar_Util.format1 "Not an embedded pair: %s"
                                uu____4687
                               in
                            (FStar_Errors.Warning_NotEmbedded, uu____4685)
                             in
                          FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                            uu____4679)
                       else ();
                       FStar_Pervasives_Native.None)))
         in
      let uu____4697 =
        let uu____4698 = type_of ea  in
        let uu____4699 = type_of eb  in
        FStar_Syntax_Syntax.t_tuple2_of uu____4698 uu____4699  in
      mk_emb_full em un uu____4697 printer emb_t_pair_a_b
  
let e_either :
  'a 'b . 'a embedding -> 'b embedding -> ('a,'b) FStar_Util.either embedding
  =
  fun ea  ->
    fun eb  ->
      let t_sum_a_b =
        let t_either =
          FStar_Syntax_Util.fvar_const FStar_Parser_Const.either_lid  in
        let uu____4743 =
          let uu____4748 =
            let uu____4749 = FStar_Syntax_Syntax.as_arg ea.typ  in
            let uu____4758 =
              let uu____4769 = FStar_Syntax_Syntax.as_arg eb.typ  in
              [uu____4769]  in
            uu____4749 :: uu____4758  in
          FStar_Syntax_Syntax.mk_Tm_app t_either uu____4748  in
        uu____4743 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
      let emb_t_sum_a_b =
        let uu____4805 =
          let uu____4813 =
            FStar_All.pipe_right FStar_Parser_Const.either_lid
              FStar_Ident.string_of_lid
             in
          (uu____4813, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____4805  in
      let printer s =
        match s with
        | FStar_Util.Inl a ->
            let uu____4836 = ea.print a  in
            FStar_Util.format1 "Inl %s" uu____4836
        | FStar_Util.Inr b ->
            let uu____4840 = eb.print b  in
            FStar_Util.format1 "Inr %s" uu____4840
         in
      let em s rng topt norm1 =
        lazy_embed printer emb_t_sum_a_b rng t_sum_a_b s
          (match s with
           | FStar_Util.Inl a ->
               (fun uu____4928  ->
                  let shadow_a =
                    map_shadow topt
                      (fun t  ->
                         let v1 = FStar_Ident.mk_ident ("v", rng)  in
                         let some_v =
                           FStar_Syntax_Util.mk_field_projector_name_from_ident
                             FStar_Parser_Const.inl_lid v1
                            in
                         let some_v_tm =
                           let uu____5000 =
                             FStar_Syntax_Syntax.lid_as_fv some_v
                               FStar_Syntax_Syntax.delta_equational
                               FStar_Pervasives_Native.None
                              in
                           FStar_Syntax_Syntax.fv_to_tm uu____5000  in
                         let uu____5001 =
                           let uu____5006 =
                             FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm
                               [FStar_Syntax_Syntax.U_zero]
                              in
                           let uu____5007 =
                             let uu____5008 =
                               let uu____5017 = type_of ea  in
                               FStar_Syntax_Syntax.iarg uu____5017  in
                             let uu____5018 =
                               let uu____5029 =
                                 let uu____5038 = type_of eb  in
                                 FStar_Syntax_Syntax.iarg uu____5038  in
                               let uu____5039 =
                                 let uu____5050 =
                                   FStar_Syntax_Syntax.as_arg t  in
                                 [uu____5050]  in
                               uu____5029 :: uu____5039  in
                             uu____5008 :: uu____5018  in
                           FStar_Syntax_Syntax.mk_Tm_app uu____5006
                             uu____5007
                            in
                         uu____5001 FStar_Pervasives_Native.None rng)
                     in
                  let uu____5093 =
                    let uu____5098 =
                      let uu____5099 =
                        FStar_Syntax_Syntax.tdataconstr
                          FStar_Parser_Const.inl_lid
                         in
                      FStar_Syntax_Syntax.mk_Tm_uinst uu____5099
                        [FStar_Syntax_Syntax.U_zero;
                        FStar_Syntax_Syntax.U_zero]
                       in
                    let uu____5100 =
                      let uu____5101 =
                        let uu____5110 = type_of ea  in
                        FStar_Syntax_Syntax.iarg uu____5110  in
                      let uu____5111 =
                        let uu____5122 =
                          let uu____5131 = type_of eb  in
                          FStar_Syntax_Syntax.iarg uu____5131  in
                        let uu____5132 =
                          let uu____5143 =
                            let uu____5152 =
                              let uu____5153 = embed ea a  in
                              uu____5153 rng shadow_a norm1  in
                            FStar_Syntax_Syntax.as_arg uu____5152  in
                          [uu____5143]  in
                        uu____5122 :: uu____5132  in
                      uu____5101 :: uu____5111  in
                    FStar_Syntax_Syntax.mk_Tm_app uu____5098 uu____5100  in
                  uu____5093 FStar_Pervasives_Native.None rng)
           | FStar_Util.Inr b ->
               (fun uu____5258  ->
                  let shadow_b =
                    map_shadow topt
                      (fun t  ->
                         let v1 = FStar_Ident.mk_ident ("v", rng)  in
                         let some_v =
                           FStar_Syntax_Util.mk_field_projector_name_from_ident
                             FStar_Parser_Const.inr_lid v1
                            in
                         let some_v_tm =
                           let uu____5330 =
                             FStar_Syntax_Syntax.lid_as_fv some_v
                               FStar_Syntax_Syntax.delta_equational
                               FStar_Pervasives_Native.None
                              in
                           FStar_Syntax_Syntax.fv_to_tm uu____5330  in
                         let uu____5331 =
                           let uu____5336 =
                             FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm
                               [FStar_Syntax_Syntax.U_zero]
                              in
                           let uu____5337 =
                             let uu____5338 =
                               let uu____5347 = type_of ea  in
                               FStar_Syntax_Syntax.iarg uu____5347  in
                             let uu____5348 =
                               let uu____5359 =
                                 let uu____5368 = type_of eb  in
                                 FStar_Syntax_Syntax.iarg uu____5368  in
                               let uu____5369 =
                                 let uu____5380 =
                                   FStar_Syntax_Syntax.as_arg t  in
                                 [uu____5380]  in
                               uu____5359 :: uu____5369  in
                             uu____5338 :: uu____5348  in
                           FStar_Syntax_Syntax.mk_Tm_app uu____5336
                             uu____5337
                            in
                         uu____5331 FStar_Pervasives_Native.None rng)
                     in
                  let uu____5423 =
                    let uu____5428 =
                      let uu____5429 =
                        FStar_Syntax_Syntax.tdataconstr
                          FStar_Parser_Const.inr_lid
                         in
                      FStar_Syntax_Syntax.mk_Tm_uinst uu____5429
                        [FStar_Syntax_Syntax.U_zero;
                        FStar_Syntax_Syntax.U_zero]
                       in
                    let uu____5430 =
                      let uu____5431 =
                        let uu____5440 = type_of ea  in
                        FStar_Syntax_Syntax.iarg uu____5440  in
                      let uu____5441 =
                        let uu____5452 =
                          let uu____5461 = type_of eb  in
                          FStar_Syntax_Syntax.iarg uu____5461  in
                        let uu____5462 =
                          let uu____5473 =
                            let uu____5482 =
                              let uu____5483 = embed eb b  in
                              uu____5483 rng shadow_b norm1  in
                            FStar_Syntax_Syntax.as_arg uu____5482  in
                          [uu____5473]  in
                        uu____5452 :: uu____5462  in
                      uu____5431 :: uu____5441  in
                    FStar_Syntax_Syntax.mk_Tm_app uu____5428 uu____5430  in
                  uu____5423 FStar_Pervasives_Native.None rng))
         in
      let un t0 w norm1 =
        let t = FStar_Syntax_Util.unmeta_safe t0  in
        lazy_unembed printer emb_t_sum_a_b t t_sum_a_b
          (fun t1  ->
             let uu____5638 = FStar_Syntax_Util.head_and_args' t1  in
             match uu____5638 with
             | (hd1,args) ->
                 let uu____5681 =
                   let uu____5696 =
                     let uu____5697 = FStar_Syntax_Util.un_uinst hd1  in
                     uu____5697.FStar_Syntax_Syntax.n  in
                   (uu____5696, args)  in
                 (match uu____5681 with
                  | (FStar_Syntax_Syntax.Tm_fvar
                     fv,uu____5717::uu____5718::(a,uu____5720)::[]) when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.inl_lid
                      ->
                      let uu____5787 =
                        let uu____5790 = unembed ea a  in uu____5790 w norm1
                         in
                      FStar_Util.bind_opt uu____5787
                        (fun a1  ->
                           FStar_Pervasives_Native.Some (FStar_Util.Inl a1))
                  | (FStar_Syntax_Syntax.Tm_fvar
                     fv,uu____5814::uu____5815::(b,uu____5817)::[]) when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.inr_lid
                      ->
                      let uu____5884 =
                        let uu____5887 = unembed eb b  in uu____5887 w norm1
                         in
                      FStar_Util.bind_opt uu____5884
                        (fun b1  ->
                           FStar_Pervasives_Native.Some (FStar_Util.Inr b1))
                  | uu____5910 ->
                      (if w
                       then
                         (let uu____5927 =
                            let uu____5933 =
                              let uu____5935 =
                                FStar_Syntax_Print.term_to_string t0  in
                              FStar_Util.format1 "Not an embedded sum: %s"
                                uu____5935
                               in
                            (FStar_Errors.Warning_NotEmbedded, uu____5933)
                             in
                          FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                            uu____5927)
                       else ();
                       FStar_Pervasives_Native.None)))
         in
      let uu____5945 =
        let uu____5946 = type_of ea  in
        let uu____5947 = type_of eb  in
        FStar_Syntax_Syntax.t_either_of uu____5946 uu____5947  in
      mk_emb_full em un uu____5945 printer emb_t_sum_a_b
  
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea  ->
    let t_list_a =
      let t_list = FStar_Syntax_Util.fvar_const FStar_Parser_Const.list_lid
         in
      let uu____5975 =
        let uu____5980 =
          let uu____5981 = FStar_Syntax_Syntax.as_arg ea.typ  in [uu____5981]
           in
        FStar_Syntax_Syntax.mk_Tm_app t_list uu____5980  in
      uu____5975 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
    let emb_t_list_a =
      let uu____6009 =
        let uu____6017 =
          FStar_All.pipe_right FStar_Parser_Const.list_lid
            FStar_Ident.string_of_lid
           in
        (uu____6017, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____6009  in
    let printer l =
      let uu____6034 =
        let uu____6036 =
          let uu____6038 = FStar_List.map ea.print l  in
          FStar_All.pipe_right uu____6038 (FStar_String.concat "; ")  in
        Prims.strcat uu____6036 "]"  in
      Prims.strcat "[" uu____6034  in
    let rec em l rng shadow_l norm1 =
      lazy_embed printer emb_t_list_a rng t_list_a l
        (fun uu____6124  ->
           let t =
             let uu____6126 = type_of ea  in
             FStar_Syntax_Syntax.iarg uu____6126  in
           match l with
           | [] ->
               let uu____6127 =
                 let uu____6132 =
                   let uu____6133 =
                     FStar_Syntax_Syntax.tdataconstr
                       FStar_Parser_Const.nil_lid
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____6133
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 FStar_Syntax_Syntax.mk_Tm_app uu____6132 [t]  in
               uu____6127 FStar_Pervasives_Native.None rng
           | hd1::tl1 ->
               let cons1 =
                 let uu____6157 =
                   FStar_Syntax_Syntax.tdataconstr
                     FStar_Parser_Const.cons_lid
                    in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu____6157
                   [FStar_Syntax_Syntax.U_zero]
                  in
               let proj f cons_tm =
                 let fid = FStar_Ident.mk_ident (f, rng)  in
                 let proj =
                   FStar_Syntax_Util.mk_field_projector_name_from_ident
                     FStar_Parser_Const.cons_lid fid
                    in
                 let proj_tm =
                   let uu____6177 =
                     FStar_Syntax_Syntax.lid_as_fv proj
                       FStar_Syntax_Syntax.delta_equational
                       FStar_Pervasives_Native.None
                      in
                   FStar_Syntax_Syntax.fv_to_tm uu____6177  in
                 let uu____6178 =
                   let uu____6183 =
                     FStar_Syntax_Syntax.mk_Tm_uinst proj_tm
                       [FStar_Syntax_Syntax.U_zero]
                      in
                   let uu____6184 =
                     let uu____6185 =
                       let uu____6194 = type_of ea  in
                       FStar_Syntax_Syntax.iarg uu____6194  in
                     let uu____6195 =
                       let uu____6206 = FStar_Syntax_Syntax.as_arg cons_tm
                          in
                       [uu____6206]  in
                     uu____6185 :: uu____6195  in
                   FStar_Syntax_Syntax.mk_Tm_app uu____6183 uu____6184  in
                 uu____6178 FStar_Pervasives_Native.None rng  in
               let shadow_hd = map_shadow shadow_l (proj "hd")  in
               let shadow_tl = map_shadow shadow_l (proj "tl")  in
               let uu____6359 =
                 let uu____6364 =
                   let uu____6365 =
                     let uu____6376 =
                       let uu____6385 =
                         let uu____6386 = embed ea hd1  in
                         uu____6386 rng shadow_hd norm1  in
                       FStar_Syntax_Syntax.as_arg uu____6385  in
                     let uu____6456 =
                       let uu____6467 =
                         let uu____6476 = em tl1 rng shadow_tl norm1  in
                         FStar_Syntax_Syntax.as_arg uu____6476  in
                       [uu____6467]  in
                     uu____6376 :: uu____6456  in
                   t :: uu____6365  in
                 FStar_Syntax_Syntax.mk_Tm_app cons1 uu____6364  in
               uu____6359 FStar_Pervasives_Native.None rng)
       in
    let rec un t0 w norm1 =
      let t = FStar_Syntax_Util.unmeta_safe t0  in
      lazy_unembed printer emb_t_list_a t t_list_a
        (fun t1  ->
           let uu____6592 = FStar_Syntax_Util.head_and_args' t1  in
           match uu____6592 with
           | (hd1,args) ->
               let uu____6633 =
                 let uu____6646 =
                   let uu____6647 = FStar_Syntax_Util.un_uinst hd1  in
                   uu____6647.FStar_Syntax_Syntax.n  in
                 (uu____6646, args)  in
               (match uu____6633 with
                | (FStar_Syntax_Syntax.Tm_fvar fv,uu____6663) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.nil_lid
                    -> FStar_Pervasives_Native.Some []
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(uu____6683,FStar_Pervasives_Native.Some
                       (FStar_Syntax_Syntax.Implicit uu____6684))::(hd2,FStar_Pervasives_Native.None
                                                                    )::
                   (tl1,FStar_Pervasives_Native.None )::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.cons_lid
                    ->
                    let uu____6726 =
                      let uu____6729 = unembed ea hd2  in uu____6729 w norm1
                       in
                    FStar_Util.bind_opt uu____6726
                      (fun hd3  ->
                         let uu____6747 = un tl1 w norm1  in
                         FStar_Util.bind_opt uu____6747
                           (fun tl2  ->
                              FStar_Pervasives_Native.Some (hd3 :: tl2)))
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(hd2,FStar_Pervasives_Native.None )::(tl1,FStar_Pervasives_Native.None
                                                            )::[])
                    when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.cons_lid
                    ->
                    let uu____6797 =
                      let uu____6800 = unembed ea hd2  in uu____6800 w norm1
                       in
                    FStar_Util.bind_opt uu____6797
                      (fun hd3  ->
                         let uu____6818 = un tl1 w norm1  in
                         FStar_Util.bind_opt uu____6818
                           (fun tl2  ->
                              FStar_Pervasives_Native.Some (hd3 :: tl2)))
                | uu____6835 ->
                    (if w
                     then
                       (let uu____6850 =
                          let uu____6856 =
                            let uu____6858 =
                              FStar_Syntax_Print.term_to_string t0  in
                            FStar_Util.format1 "Not an embedded list: %s"
                              uu____6858
                             in
                          (FStar_Errors.Warning_NotEmbedded, uu____6856)  in
                        FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                          uu____6850)
                     else ();
                     FStar_Pervasives_Native.None)))
       in
    let uu____6866 =
      let uu____6867 = type_of ea  in
      FStar_Syntax_Syntax.t_list_of uu____6867  in
    mk_emb_full em un uu____6866 printer emb_t_list_a
  
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
    match projectee with | Simpl  -> true | uu____6910 -> false
  
let (uu___is_Weak : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Weak  -> true | uu____6921 -> false
  
let (uu___is_HNF : norm_step -> Prims.bool) =
  fun projectee  -> match projectee with | HNF  -> true | uu____6932 -> false 
let (uu___is_Primops : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____6943 -> false
  
let (uu___is_Delta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Delta  -> true | uu____6954 -> false
  
let (uu___is_Zeta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Zeta  -> true | uu____6965 -> false
  
let (uu___is_Iota : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Iota  -> true | uu____6976 -> false
  
let (uu___is_Reify : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____6987 -> false
  
let (uu___is_UnfoldOnly : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____7002 -> false
  
let (__proj__UnfoldOnly__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldFully : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldFully _0 -> true | uu____7034 -> false
  
let (__proj__UnfoldFully__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldFully _0 -> _0 
let (uu___is_UnfoldAttr : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____7066 -> false
  
let (__proj__UnfoldAttr__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_NBE : norm_step -> Prims.bool) =
  fun projectee  -> match projectee with | NBE  -> true | uu____7094 -> false 
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
    let uu____7112 =
      FStar_Ident.lid_of_str "FStar.Syntax.Embeddings.norm_step"  in
    FStar_Syntax_Util.fvar_const uu____7112  in
  let emb_t_norm_step =
    let uu____7115 =
      let uu____7123 =
        FStar_All.pipe_right FStar_Parser_Const.norm_step_lid
          FStar_Ident.string_of_lid
         in
      (uu____7123, [])  in
    FStar_Syntax_Syntax.ET_app uu____7115  in
  let printer uu____7135 = "norm_step"  in
  let em n1 rng _topt norm1 =
    lazy_embed printer emb_t_norm_step rng t_norm_step1 n1
      (fun uu____7201  ->
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
             let uu____7206 =
               let uu____7211 =
                 let uu____7212 =
                   let uu____7221 =
                     let uu____7222 =
                       let uu____7229 = e_list e_string  in
                       embed uu____7229 l  in
                     uu____7222 rng FStar_Pervasives_Native.None norm1  in
                   FStar_Syntax_Syntax.as_arg uu____7221  in
                 [uu____7212]  in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldOnly uu____7211  in
             uu____7206 FStar_Pervasives_Native.None rng
         | UnfoldFully l ->
             let uu____7288 =
               let uu____7293 =
                 let uu____7294 =
                   let uu____7303 =
                     let uu____7304 =
                       let uu____7311 = e_list e_string  in
                       embed uu____7311 l  in
                     uu____7304 rng FStar_Pervasives_Native.None norm1  in
                   FStar_Syntax_Syntax.as_arg uu____7303  in
                 [uu____7294]  in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldFully uu____7293  in
             uu____7288 FStar_Pervasives_Native.None rng
         | UnfoldAttr l ->
             let uu____7370 =
               let uu____7375 =
                 let uu____7376 =
                   let uu____7385 =
                     let uu____7386 =
                       let uu____7393 = e_list e_string  in
                       embed uu____7393 l  in
                     uu____7386 rng FStar_Pervasives_Native.None norm1  in
                   FStar_Syntax_Syntax.as_arg uu____7385  in
                 [uu____7376]  in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldAttr uu____7375  in
             uu____7370 FStar_Pervasives_Native.None rng)
     in
  let un t0 w norm1 =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    lazy_unembed printer emb_t_norm_step t t_norm_step1
      (fun t1  ->
         let uu____7482 = FStar_Syntax_Util.head_and_args t1  in
         match uu____7482 with
         | (hd1,args) ->
             let uu____7527 =
               let uu____7542 =
                 let uu____7543 = FStar_Syntax_Util.un_uinst hd1  in
                 uu____7543.FStar_Syntax_Syntax.n  in
               (uu____7542, args)  in
             (match uu____7527 with
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
              | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____7731)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldonly
                  ->
                  let uu____7766 =
                    let uu____7772 =
                      let uu____7782 = e_list e_string  in
                      unembed uu____7782 l  in
                    uu____7772 w norm1  in
                  FStar_Util.bind_opt uu____7766
                    (fun ss  ->
                       FStar_All.pipe_left
                         (fun _0_1  -> FStar_Pervasives_Native.Some _0_1)
                         (UnfoldOnly ss))
              | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____7810)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldfully
                  ->
                  let uu____7845 =
                    let uu____7851 =
                      let uu____7861 = e_list e_string  in
                      unembed uu____7861 l  in
                    uu____7851 w norm1  in
                  FStar_Util.bind_opt uu____7845
                    (fun ss  ->
                       FStar_All.pipe_left
                         (fun _0_2  -> FStar_Pervasives_Native.Some _0_2)
                         (UnfoldFully ss))
              | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____7889)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldattr
                  ->
                  let uu____7924 =
                    let uu____7930 =
                      let uu____7940 = e_list e_string  in
                      unembed uu____7940 l  in
                    uu____7930 w norm1  in
                  FStar_Util.bind_opt uu____7924
                    (fun ss  ->
                       FStar_All.pipe_left
                         (fun _0_3  -> FStar_Pervasives_Native.Some _0_3)
                         (UnfoldAttr ss))
              | uu____7966 ->
                  (if w
                   then
                     (let uu____7983 =
                        let uu____7989 =
                          let uu____7991 =
                            FStar_Syntax_Print.term_to_string t0  in
                          FStar_Util.format1 "Not an embedded norm_step: %s"
                            uu____7991
                           in
                        (FStar_Errors.Warning_NotEmbedded, uu____7989)  in
                      FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                        uu____7983)
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
    | uu____8093 ->
        (if w
         then
           (let uu____8096 =
              let uu____8102 =
                let uu____8104 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded range: %s" uu____8104  in
              (FStar_Errors.Warning_NotEmbedded, uu____8102)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____8096)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____8110 =
    let uu____8111 =
      let uu____8119 =
        FStar_All.pipe_right FStar_Parser_Const.range_lid
          FStar_Ident.string_of_lid
         in
      (uu____8119, [])  in
    FStar_Syntax_Syntax.ET_app uu____8111  in
  mk_emb_full em un FStar_Syntax_Syntax.t_range FStar_Range.string_of_range
    uu____8110
  
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
        let uu____8190 =
          let uu____8197 =
            let uu____8198 =
              let uu____8213 =
                let uu____8222 =
                  let uu____8229 = FStar_Syntax_Syntax.null_bv ea.typ  in
                  (uu____8229, FStar_Pervasives_Native.None)  in
                [uu____8222]  in
              let uu____8244 = FStar_Syntax_Syntax.mk_Total eb.typ  in
              (uu____8213, uu____8244)  in
            FStar_Syntax_Syntax.Tm_arrow uu____8198  in
          FStar_Syntax_Syntax.mk uu____8197  in
        uu____8190 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
      let emb_t_arr_a_b =
        FStar_Syntax_Syntax.ET_fun ((ea.emb_typ), (eb.emb_typ))  in
      let printer f = "<fun>"  in
      let em f rng shadow_f norm1 =
        lazy_embed (fun uu____8357  -> "<fun>") emb_t_arr_a_b rng t_arrow f
          (fun uu____8363  ->
             let uu____8364 = force_shadow shadow_f  in
             match uu____8364 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Exn.raise Embedding_failure
             | FStar_Pervasives_Native.Some repr_f ->
                 ((let uu____8426 =
                     FStar_ST.op_Bang FStar_Options.debug_embedding  in
                   if uu____8426
                   then
                     let uu____8450 =
                       FStar_Syntax_Print.term_to_string repr_f  in
                     let uu____8452 = FStar_Util.stack_dump ()  in
                     FStar_Util.print2
                       "e_arrow forced back to term using shadow %s; repr=%s\n"
                       uu____8450 uu____8452
                   else ());
                  (let res = norm1 (FStar_Util.Inr repr_f)  in
                   (let uu____8459 =
                      FStar_ST.op_Bang FStar_Options.debug_embedding  in
                    if uu____8459
                    then
                      let uu____8483 =
                        FStar_Syntax_Print.term_to_string repr_f  in
                      let uu____8485 = FStar_Syntax_Print.term_to_string res
                         in
                      let uu____8487 = FStar_Util.stack_dump ()  in
                      FStar_Util.print3
                        "e_arrow forced back to term using shadow %s; repr=%s\n\t%s\n"
                        uu____8483 uu____8485 uu____8487
                    else ());
                   res)))
         in
      let un f w norm1 =
        lazy_unembed printer emb_t_arr_a_b f t_arrow
          (fun f1  ->
             let f_wrapped a =
               (let uu____8546 =
                  FStar_ST.op_Bang FStar_Options.debug_embedding  in
                if uu____8546
                then
                  let uu____8570 = FStar_Syntax_Print.term_to_string f1  in
                  let uu____8572 = FStar_Util.stack_dump ()  in
                  FStar_Util.print2
                    "Calling back into normalizer for %s\n%s\n" uu____8570
                    uu____8572
                else ());
               (let a_tm =
                  let uu____8578 = embed ea a  in
                  uu____8578 f1.FStar_Syntax_Syntax.pos
                    FStar_Pervasives_Native.None norm1
                   in
                let b_tm =
                  let uu____8611 =
                    let uu____8616 =
                      let uu____8617 =
                        let uu____8622 =
                          let uu____8623 = FStar_Syntax_Syntax.as_arg a_tm
                             in
                          [uu____8623]  in
                        FStar_Syntax_Syntax.mk_Tm_app f1 uu____8622  in
                      uu____8617 FStar_Pervasives_Native.None
                        f1.FStar_Syntax_Syntax.pos
                       in
                    FStar_Util.Inr uu____8616  in
                  norm1 uu____8611  in
                let uu____8650 =
                  let uu____8653 = unembed eb b_tm  in uu____8653 w norm1  in
                match uu____8650 with
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
                let uu____8753 = FStar_List.splitAt n_tvars args  in
                match uu____8753 with
                | (_tvar_args,rest_args) ->
                    let uu____8830 = FStar_List.hd rest_args  in
                    (match uu____8830 with
                     | (x,uu____8850) ->
                         let shadow_app =
                           let uu____8864 =
                             FStar_Common.mk_thunk
                               (fun uu____8873  ->
                                  let uu____8874 =
                                    let uu____8879 =
                                      norm1 (FStar_Util.Inl fv_lid1)  in
                                    FStar_Syntax_Syntax.mk_Tm_app uu____8879
                                      args
                                     in
                                  uu____8874 FStar_Pervasives_Native.None rng)
                              in
                           FStar_Pervasives_Native.Some uu____8864  in
                         let uu____8925 =
                           let uu____8928 =
                             let uu____8931 = unembed ea x  in
                             uu____8931 true norm1  in
                           FStar_Util.map_opt uu____8928
                             (fun x1  ->
                                let uu____8971 =
                                  let uu____8978 = f x1  in
                                  embed eb uu____8978  in
                                uu____8971 rng shadow_app norm1)
                            in
                         (match uu____8925 with
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
                  let uu____9108 = FStar_List.splitAt n_tvars args  in
                  match uu____9108 with
                  | (_tvar_args,rest_args) ->
                      let uu____9171 = FStar_List.hd rest_args  in
                      (match uu____9171 with
                       | (x,uu____9187) ->
                           let uu____9192 =
                             let uu____9199 = FStar_List.tl rest_args  in
                             FStar_List.hd uu____9199  in
                           (match uu____9192 with
                            | (y,uu____9223) ->
                                let shadow_app =
                                  let uu____9233 =
                                    FStar_Common.mk_thunk
                                      (fun uu____9242  ->
                                         let uu____9243 =
                                           let uu____9248 =
                                             norm1 (FStar_Util.Inl fv_lid1)
                                              in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____9248 args
                                            in
                                         uu____9243
                                           FStar_Pervasives_Native.None rng)
                                     in
                                  FStar_Pervasives_Native.Some uu____9233  in
                                let uu____9294 =
                                  let uu____9297 =
                                    let uu____9300 = unembed ea x  in
                                    uu____9300 true norm1  in
                                  FStar_Util.bind_opt uu____9297
                                    (fun x1  ->
                                       let uu____9317 =
                                         let uu____9320 = unembed eb y  in
                                         uu____9320 true norm1  in
                                       FStar_Util.bind_opt uu____9317
                                         (fun y1  ->
                                            let uu____9337 =
                                              let uu____9338 =
                                                let uu____9345 = f x1 y1  in
                                                embed ec uu____9345  in
                                              uu____9338 rng shadow_app norm1
                                               in
                                            FStar_Pervasives_Native.Some
                                              uu____9337))
                                   in
                                (match uu____9294 with
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
                    let uu____9494 = FStar_List.splitAt n_tvars args  in
                    match uu____9494 with
                    | (_tvar_args,rest_args) ->
                        let uu____9557 = FStar_List.hd rest_args  in
                        (match uu____9557 with
                         | (x,uu____9573) ->
                             let uu____9578 =
                               let uu____9585 = FStar_List.tl rest_args  in
                               FStar_List.hd uu____9585  in
                             (match uu____9578 with
                              | (y,uu____9609) ->
                                  let uu____9614 =
                                    let uu____9621 =
                                      let uu____9630 =
                                        FStar_List.tl rest_args  in
                                      FStar_List.tl uu____9630  in
                                    FStar_List.hd uu____9621  in
                                  (match uu____9614 with
                                   | (z,uu____9660) ->
                                       let shadow_app =
                                         let uu____9670 =
                                           FStar_Common.mk_thunk
                                             (fun uu____9679  ->
                                                let uu____9680 =
                                                  let uu____9685 =
                                                    norm1
                                                      (FStar_Util.Inl fv_lid1)
                                                     in
                                                  FStar_Syntax_Syntax.mk_Tm_app
                                                    uu____9685 args
                                                   in
                                                uu____9680
                                                  FStar_Pervasives_Native.None
                                                  rng)
                                            in
                                         FStar_Pervasives_Native.Some
                                           uu____9670
                                          in
                                       let uu____9731 =
                                         let uu____9734 =
                                           let uu____9737 = unembed ea x  in
                                           uu____9737 true norm1  in
                                         FStar_Util.bind_opt uu____9734
                                           (fun x1  ->
                                              let uu____9754 =
                                                let uu____9757 = unembed eb y
                                                   in
                                                uu____9757 true norm1  in
                                              FStar_Util.bind_opt uu____9754
                                                (fun y1  ->
                                                   let uu____9774 =
                                                     let uu____9777 =
                                                       unembed ec z  in
                                                     uu____9777 true norm1
                                                      in
                                                   FStar_Util.bind_opt
                                                     uu____9774
                                                     (fun z1  ->
                                                        let uu____9794 =
                                                          let uu____9795 =
                                                            let uu____9802 =
                                                              f x1 y1 z1  in
                                                            embed ed
                                                              uu____9802
                                                             in
                                                          uu____9795 rng
                                                            shadow_app norm1
                                                           in
                                                        FStar_Pervasives_Native.Some
                                                          uu____9794)))
                                          in
                                       (match uu____9731 with
                                        | FStar_Pervasives_Native.Some x1 ->
                                            FStar_Pervasives_Native.Some x1
                                        | FStar_Pervasives_Native.None  ->
                                            force_shadow shadow_app))))
                     in
                  f_wrapped
  
let debug_wrap : 'a . Prims.string -> (unit -> 'a) -> 'a =
  fun s  ->
    fun f  ->
      (let uu____9857 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
       if uu____9857 then FStar_Util.print1 "++++starting %s\n" s else ());
      (let res = f ()  in
       (let uu____9886 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
        if uu____9886 then FStar_Util.print1 "------ending %s\n" s else ());
       res)
  