open Prims
type norm_cb =
  (FStar_Ident.lid,FStar_Syntax_Syntax.term) FStar_Util.either ->
    FStar_Syntax_Syntax.term
let (id_norm_cb : norm_cb) =
  fun uu___203_13  ->
    match uu___203_13 with
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
  print: 'a printer }
let __proj__Mkembedding__item__em : 'a . 'a embedding -> 'a -> embed_t =
  fun projectee  ->
    match projectee with
    | { em = __fname__em; un = __fname__un; typ = __fname__typ;
        print = __fname__print;_} -> __fname__em
  
let __proj__Mkembedding__item__un :
  'a . 'a embedding -> FStar_Syntax_Syntax.term -> 'a unembed_t =
  fun projectee  ->
    match projectee with
    | { em = __fname__em; un = __fname__un; typ = __fname__typ;
        print = __fname__print;_} -> __fname__un
  
let __proj__Mkembedding__item__typ :
  'a . 'a embedding -> FStar_Syntax_Syntax.typ =
  fun projectee  ->
    match projectee with
    | { em = __fname__em; un = __fname__un; typ = __fname__typ;
        print = __fname__print;_} -> __fname__typ
  
let __proj__Mkembedding__item__print : 'a . 'a embedding -> 'a printer =
  fun projectee  ->
    match projectee with
    | { em = __fname__em; un = __fname__un; typ = __fname__typ;
        print = __fname__print;_} -> __fname__print
  
let unknown_printer :
  'Auu____763 . FStar_Syntax_Syntax.term -> 'Auu____763 -> Prims.string =
  fun typ  ->
    fun uu____773  ->
      let uu____774 = FStar_Syntax_Print.term_to_string typ  in
      FStar_Util.format1 "unknown %s" uu____774
  
let mk_emb :
  'a .
    'a raw_embedder ->
      'a raw_unembedder -> FStar_Syntax_Syntax.typ -> 'a embedding
  =
  fun em  ->
    fun un  -> fun typ  -> { em; un; typ; print = (unknown_printer typ) }
  
let mk_emb_with_printer :
  'Auu____991 .
    ('Auu____991 -> embed_t) ->
      (FStar_Syntax_Syntax.term -> 'Auu____991 unembed_t) ->
        FStar_Syntax_Syntax.typ ->
          'Auu____991 printer -> 'Auu____991 embedding
  =
  fun em  ->
    fun un  -> fun typ  -> fun printer  -> { em; un; typ; print = printer }
  
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
    fun t  -> fun n1  -> let uu____1297 = unembed e t  in uu____1297 true n1
  
let try_unembed :
  'a .
    'a embedding ->
      FStar_Syntax_Syntax.term ->
        norm_cb -> 'a FStar_Pervasives_Native.option
  =
  fun e  ->
    fun t  -> fun n1  -> let uu____1344 = unembed e t  in uu____1344 false n1
  
let type_of : 'a . 'a embedding -> FStar_Syntax_Syntax.typ = fun e  -> e.typ 
let lazy_embed :
  'a .
    'a printer ->
      FStar_Range.range ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          'a ->
            (unit -> FStar_Syntax_Syntax.term) ->
              FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun pa  ->
    fun rng  ->
      fun ta  ->
        fun x  ->
          fun f  ->
            (let uu____1433 = FStar_Syntax_Print.term_to_string ta  in
             let uu____1434 = pa x  in
             let uu____1437 =
               let uu____1438 = f ()  in
               FStar_Syntax_Print.term_to_string uu____1438  in
             FStar_Util.print3
               "Embedding a %s\n\tvalue is %s\nthunked as a %s\n" uu____1433
               uu____1434 uu____1437);
            (let uu____1439 = FStar_Options.eager_embedding ()  in
             if uu____1439
             then f ()
             else
               (let thunk = FStar_Common.mk_thunk f  in
                let uu____1450 =
                  let uu____1457 =
                    let uu____1458 =
                      let uu____1459 = FStar_Dyn.mkdyn x  in
                      {
                        FStar_Syntax_Syntax.blob = uu____1459;
                        FStar_Syntax_Syntax.lkind =
                          (FStar_Syntax_Syntax.Lazy_embedding (ta, thunk));
                        FStar_Syntax_Syntax.ltyp = FStar_Syntax_Syntax.tun;
                        FStar_Syntax_Syntax.rng = rng
                      }  in
                    FStar_Syntax_Syntax.Tm_lazy uu____1458  in
                  FStar_Syntax_Syntax.mk uu____1457  in
                uu____1450 FStar_Pervasives_Native.None rng))
  
let lazy_unembed :
  'a .
    'a printer ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.term -> 'a FStar_Pervasives_Native.option) ->
            'a FStar_Pervasives_Native.option
  =
  fun pa  ->
    fun x  ->
      fun ta  ->
        fun f  ->
          let x1 = FStar_Syntax_Subst.compress x  in
          match x1.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Tm_lazy
              { FStar_Syntax_Syntax.blob = b;
                FStar_Syntax_Syntax.lkind =
                  FStar_Syntax_Syntax.Lazy_embedding (tb,t);
                FStar_Syntax_Syntax.ltyp = uu____1569;
                FStar_Syntax_Syntax.rng = uu____1570;_}
              ->
              let uu____1585 = FStar_Options.eager_embedding ()  in
              if uu____1585
              then
                let uu____1588 = FStar_Common.force_thunk t  in f uu____1588
              else
                (let a = FStar_Dyn.undyn b  in
                 (let uu____1634 = FStar_Syntax_Print.term_to_string tb  in
                  let uu____1635 = FStar_Syntax_Print.term_to_string ta  in
                  let uu____1636 = pa a  in
                  let uu____1639 =
                    let uu____1640 = FStar_Common.force_thunk t  in
                    FStar_Syntax_Print.term_to_string uu____1640  in
                  FStar_Util.print4
                    "Unembedding a %s as a %s\n undyn a %s\n unthunked a %s\n"
                    uu____1634 uu____1635 uu____1636 uu____1639);
                 FStar_Pervasives_Native.Some a)
          | uu____1683 -> f x1
  
let (e_any : FStar_Syntax_Syntax.term embedding) =
  let em t _r _topt _norm = t  in
  let un t _w _n = FStar_Pervasives_Native.Some t  in
  let typ = FStar_Syntax_Syntax.t_term  in mk_emb em un typ 
let (mk_any_emb :
  FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term embedding) =
  fun typ  ->
    { em = (e_any.em); un = (e_any.un); typ; print = (unknown_printer typ) }
  
let (e_unit : unit embedding) =
  let em u rng _topt _norm =
    let uu___205_1844 = FStar_Syntax_Util.exp_unit  in
    {
      FStar_Syntax_Syntax.n = (uu___205_1844.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___205_1844.FStar_Syntax_Syntax.vars)
    }  in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unascribe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit ) ->
        FStar_Pervasives_Native.Some ()
    | uu____1872 ->
        (if w
         then
           (let uu____1874 =
              let uu____1879 =
                let uu____1880 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded unit: %s" uu____1880  in
              (FStar_Errors.Warning_NotEmbedded, uu____1879)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____1874)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb_with_printer em un FStar_Syntax_Syntax.t_unit
    (fun uu____1883  -> "()")
  
let (e_bool : Prims.bool embedding) =
  let em b rng _topt _norm =
    let t =
      if b
      then FStar_Syntax_Util.exp_true_bool
      else FStar_Syntax_Util.exp_false_bool  in
    let uu___206_1955 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___206_1955.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___206_1955.FStar_Syntax_Syntax.vars)
    }  in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) ->
        FStar_Pervasives_Native.Some b
    | uu____1986 ->
        (if w
         then
           (let uu____1988 =
              let uu____1993 =
                let uu____1994 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded bool: %s" uu____1994  in
              (FStar_Errors.Warning_NotEmbedded, uu____1993)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____1988)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb_with_printer em un FStar_Syntax_Syntax.t_bool
    FStar_Util.string_of_bool
  
let (e_char : FStar_Char.char embedding) =
  let em c rng _topt _norm =
    let t = FStar_Syntax_Util.exp_char c  in
    let uu___207_2065 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___207_2065.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___207_2065.FStar_Syntax_Syntax.vars)
    }  in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c) ->
        FStar_Pervasives_Native.Some c
    | uu____2099 ->
        (if w
         then
           (let uu____2101 =
              let uu____2106 =
                let uu____2107 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded char: %s" uu____2107  in
              (FStar_Errors.Warning_NotEmbedded, uu____2106)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____2101)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb_with_printer em un FStar_Syntax_Syntax.t_char
    FStar_Util.string_of_char
  
let (e_int : FStar_BigInt.t embedding) =
  let t_int1 = FStar_Syntax_Util.fvar_const FStar_Parser_Const.int_lid  in
  let em i rng _topt _norm =
    lazy_embed FStar_BigInt.string_of_big_int rng t_int1 i
      (fun uu____2179  ->
         let uu____2180 = FStar_BigInt.string_of_big_int i  in
         FStar_Syntax_Util.exp_int uu____2180)
     in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    lazy_unembed FStar_BigInt.string_of_big_int t t_int1
      (fun t1  ->
         match t1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
             (s,uu____2214)) ->
             let uu____2227 = FStar_BigInt.big_int_of_string s  in
             FStar_Pervasives_Native.Some uu____2227
         | uu____2228 ->
             (if w
              then
                (let uu____2230 =
                   let uu____2235 =
                     let uu____2236 = FStar_Syntax_Print.term_to_string t0
                        in
                     FStar_Util.format1 "Not an embedded int: %s" uu____2236
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____2235)  in
                 FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____2230)
              else ();
              FStar_Pervasives_Native.None))
     in
  mk_emb_with_printer em un FStar_Syntax_Syntax.t_int
    FStar_BigInt.string_of_big_int
  
let (e_string : Prims.string embedding) =
  let em s rng _topt _norm =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, rng)))
      FStar_Pervasives_Native.None rng
     in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
        (s,uu____2331)) -> FStar_Pervasives_Native.Some s
    | uu____2332 ->
        (if w
         then
           (let uu____2334 =
              let uu____2339 =
                let uu____2340 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded string: %s" uu____2340
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____2339)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____2334)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb_with_printer em un FStar_Syntax_Syntax.t_string
    (fun x  -> Prims.strcat "\"" (Prims.strcat x "\""))
  
let e_option :
  'a . 'a embedding -> 'a FStar_Pervasives_Native.option embedding =
  fun ea  ->
    let t_option_a =
      let t_opt = FStar_Syntax_Util.fvar_const FStar_Parser_Const.option_lid
         in
      let uu____2366 =
        let uu____2371 =
          let uu____2372 = FStar_Syntax_Syntax.as_arg ea.typ  in [uu____2372]
           in
        FStar_Syntax_Syntax.mk_Tm_app t_opt uu____2371  in
      uu____2366 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
    let printer uu___204_2406 =
      match uu___204_2406 with
      | FStar_Pervasives_Native.None  -> "None"
      | FStar_Pervasives_Native.Some x ->
          let uu____2410 =
            let uu____2411 = ea.print x  in Prims.strcat uu____2411 ")"  in
          Prims.strcat "(Some " uu____2410
       in
    let em o rng topt norm1 =
      lazy_embed printer rng t_option_a o
        (fun uu____2485  ->
           match o with
           | FStar_Pervasives_Native.None  ->
               let uu____2486 =
                 let uu____2491 =
                   let uu____2492 =
                     FStar_Syntax_Syntax.tdataconstr
                       FStar_Parser_Const.none_lid
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____2492
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 let uu____2493 =
                   let uu____2494 =
                     let uu____2503 = type_of ea  in
                     FStar_Syntax_Syntax.iarg uu____2503  in
                   [uu____2494]  in
                 FStar_Syntax_Syntax.mk_Tm_app uu____2491 uu____2493  in
               uu____2486 FStar_Pervasives_Native.None rng
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
                        let uu____2592 =
                          FStar_Syntax_Syntax.lid_as_fv some_v
                            FStar_Syntax_Syntax.delta_equational
                            FStar_Pervasives_Native.None
                           in
                        FStar_Syntax_Syntax.fv_to_tm uu____2592  in
                      let uu____2593 =
                        let uu____2598 =
                          FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm
                            [FStar_Syntax_Syntax.U_zero]
                           in
                        let uu____2599 =
                          let uu____2600 =
                            let uu____2609 = type_of ea  in
                            FStar_Syntax_Syntax.iarg uu____2609  in
                          let uu____2610 =
                            let uu____2621 = FStar_Syntax_Syntax.as_arg t  in
                            [uu____2621]  in
                          uu____2600 :: uu____2610  in
                        FStar_Syntax_Syntax.mk_Tm_app uu____2598 uu____2599
                         in
                      uu____2593 FStar_Pervasives_Native.None rng)
                  in
               let uu____2656 =
                 let uu____2661 =
                   let uu____2662 =
                     FStar_Syntax_Syntax.tdataconstr
                       FStar_Parser_Const.some_lid
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____2662
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 let uu____2663 =
                   let uu____2664 =
                     let uu____2673 = type_of ea  in
                     FStar_Syntax_Syntax.iarg uu____2673  in
                   let uu____2674 =
                     let uu____2685 =
                       let uu____2694 =
                         let uu____2695 = embed ea a  in
                         uu____2695 rng shadow_a norm1  in
                       FStar_Syntax_Syntax.as_arg uu____2694  in
                     [uu____2685]  in
                   uu____2664 :: uu____2674  in
                 FStar_Syntax_Syntax.mk_Tm_app uu____2661 uu____2663  in
               uu____2656 FStar_Pervasives_Native.None rng)
       in
    let un t0 w norm1 =
      let t = FStar_Syntax_Util.unmeta_safe t0  in
      lazy_unembed printer t t_option_a
        (fun t1  ->
           let uu____2830 = FStar_Syntax_Util.head_and_args t1  in
           match uu____2830 with
           | (hd1,args) ->
               let uu____2877 =
                 let uu____2892 =
                   let uu____2893 = FStar_Syntax_Util.un_uinst hd1  in
                   uu____2893.FStar_Syntax_Syntax.n  in
                 (uu____2892, args)  in
               (match uu____2877 with
                | (FStar_Syntax_Syntax.Tm_fvar fv,uu____2911) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.none_lid
                    ->
                    FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,uu____2935::(a,uu____2937)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.some_lid
                    ->
                    let uu____2988 =
                      let uu____2991 = unembed ea a  in uu____2991 w norm1
                       in
                    FStar_Util.bind_opt uu____2988
                      (fun a1  ->
                         FStar_Pervasives_Native.Some
                           (FStar_Pervasives_Native.Some a1))
                | uu____3010 ->
                    (if w
                     then
                       (let uu____3026 =
                          let uu____3031 =
                            let uu____3032 =
                              FStar_Syntax_Print.term_to_string t0  in
                            FStar_Util.format1 "Not an embedded option: %s"
                              uu____3032
                             in
                          (FStar_Errors.Warning_NotEmbedded, uu____3031)  in
                        FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                          uu____3026)
                     else ();
                     FStar_Pervasives_Native.None)))
       in
    let uu____3036 =
      let uu____3037 = type_of ea  in
      FStar_Syntax_Syntax.t_option_of uu____3037  in
    mk_emb_with_printer em un uu____3036 printer
  
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
        let uu____3078 =
          let uu____3083 =
            let uu____3084 = FStar_Syntax_Syntax.as_arg ea.typ  in
            let uu____3093 =
              let uu____3104 = FStar_Syntax_Syntax.as_arg eb.typ  in
              [uu____3104]  in
            uu____3084 :: uu____3093  in
          FStar_Syntax_Syntax.mk_Tm_app t_tup2 uu____3083  in
        uu____3078 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
      let printer uu____3148 =
        match uu____3148 with
        | (x,y) ->
            let uu____3155 = ea.print x  in
            let uu____3156 = eb.print y  in
            FStar_Util.format2 "(%s, %s)" uu____3155 uu____3156
         in
      let em x rng topt norm1 =
        lazy_embed printer rng t_pair_a_b x
          (fun uu____3239  ->
             let proj i ab =
               let uu____3253 =
                 let uu____3258 =
                   FStar_Parser_Const.mk_tuple_data_lid (Prims.parse_int "2")
                     rng
                    in
                 let uu____3259 =
                   FStar_Syntax_Syntax.null_bv FStar_Syntax_Syntax.tun  in
                 FStar_Syntax_Util.mk_field_projector_name uu____3258
                   uu____3259 i
                  in
               match uu____3253 with
               | (proj_1,uu____3263) ->
                   let proj_1_tm =
                     let uu____3265 =
                       FStar_Syntax_Syntax.lid_as_fv proj_1
                         FStar_Syntax_Syntax.delta_equational
                         FStar_Pervasives_Native.None
                        in
                     FStar_Syntax_Syntax.fv_to_tm uu____3265  in
                   let uu____3266 =
                     let uu____3271 =
                       FStar_Syntax_Syntax.mk_Tm_uinst proj_1_tm
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
                           let uu____3315 = FStar_Syntax_Syntax.as_arg ab  in
                           [uu____3315]  in
                         uu____3294 :: uu____3304  in
                       uu____3273 :: uu____3283  in
                     FStar_Syntax_Syntax.mk_Tm_app uu____3271 uu____3272  in
                   uu____3266 FStar_Pervasives_Native.None rng
                in
             let shadow_a = map_shadow topt (proj (Prims.parse_int "1"))  in
             let shadow_b = map_shadow topt (proj (Prims.parse_int "2"))  in
             let uu____3474 =
               let uu____3479 =
                 let uu____3480 =
                   FStar_Syntax_Syntax.tdataconstr
                     FStar_Parser_Const.lid_Mktuple2
                    in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu____3480
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                  in
               let uu____3481 =
                 let uu____3482 =
                   let uu____3491 = type_of ea  in
                   FStar_Syntax_Syntax.iarg uu____3491  in
                 let uu____3492 =
                   let uu____3503 =
                     let uu____3512 = type_of eb  in
                     FStar_Syntax_Syntax.iarg uu____3512  in
                   let uu____3513 =
                     let uu____3524 =
                       let uu____3533 =
                         let uu____3534 =
                           embed ea (FStar_Pervasives_Native.fst x)  in
                         uu____3534 rng shadow_a norm1  in
                       FStar_Syntax_Syntax.as_arg uu____3533  in
                     let uu____3604 =
                       let uu____3615 =
                         let uu____3624 =
                           let uu____3625 =
                             embed eb (FStar_Pervasives_Native.snd x)  in
                           uu____3625 rng shadow_b norm1  in
                         FStar_Syntax_Syntax.as_arg uu____3624  in
                       [uu____3615]  in
                     uu____3524 :: uu____3604  in
                   uu____3503 :: uu____3513  in
                 uu____3482 :: uu____3492  in
               FStar_Syntax_Syntax.mk_Tm_app uu____3479 uu____3481  in
             uu____3474 FStar_Pervasives_Native.None rng)
         in
      let un t0 w norm1 =
        let t = FStar_Syntax_Util.unmeta_safe t0  in
        lazy_unembed printer t t_pair_a_b
          (fun t1  ->
             let uu____3788 = FStar_Syntax_Util.head_and_args t1  in
             match uu____3788 with
             | (hd1,args) ->
                 let uu____3837 =
                   let uu____3850 =
                     let uu____3851 = FStar_Syntax_Util.un_uinst hd1  in
                     uu____3851.FStar_Syntax_Syntax.n  in
                   (uu____3850, args)  in
                 (match uu____3837 with
                  | (FStar_Syntax_Syntax.Tm_fvar
                     fv,uu____3869::uu____3870::(a,uu____3872)::(b,uu____3874)::[])
                      when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.lid_Mktuple2
                      ->
                      let uu____3933 =
                        let uu____3936 = unembed ea a  in uu____3936 w norm1
                         in
                      FStar_Util.bind_opt uu____3933
                        (fun a1  ->
                           let uu____3956 =
                             let uu____3959 = unembed eb b  in
                             uu____3959 w norm1  in
                           FStar_Util.bind_opt uu____3956
                             (fun b1  ->
                                FStar_Pervasives_Native.Some (a1, b1)))
                  | uu____3982 ->
                      (if w
                       then
                         (let uu____3996 =
                            let uu____4001 =
                              let uu____4002 =
                                FStar_Syntax_Print.term_to_string t0  in
                              FStar_Util.format1 "Not an embedded pair: %s"
                                uu____4002
                               in
                            (FStar_Errors.Warning_NotEmbedded, uu____4001)
                             in
                          FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                            uu____3996)
                       else ();
                       FStar_Pervasives_Native.None)))
         in
      let uu____4008 =
        let uu____4009 = type_of ea  in
        let uu____4010 = type_of eb  in
        FStar_Syntax_Syntax.t_tuple2_of uu____4009 uu____4010  in
      mk_emb_with_printer em un uu____4008 printer
  
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea  ->
    let t_list_a =
      let t_list = FStar_Syntax_Util.fvar_const FStar_Parser_Const.list_lid
         in
      let uu____4037 =
        let uu____4042 =
          let uu____4043 = FStar_Syntax_Syntax.as_arg ea.typ  in [uu____4043]
           in
        FStar_Syntax_Syntax.mk_Tm_app t_list uu____4042  in
      uu____4037 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
    let printer l =
      let uu____4080 =
        let uu____4081 =
          let uu____4082 = FStar_List.map ea.print l  in
          FStar_All.pipe_right uu____4082 (FStar_String.concat "; ")  in
        Prims.strcat uu____4081 "]"  in
      Prims.strcat "[" uu____4080  in
    let rec em l rng shadow_l norm1 =
      lazy_embed printer rng t_list_a l
        (fun uu____4161  ->
           let t =
             let uu____4163 = type_of ea  in
             FStar_Syntax_Syntax.iarg uu____4163  in
           match l with
           | [] ->
               let uu____4164 =
                 let uu____4169 =
                   let uu____4170 =
                     FStar_Syntax_Syntax.tdataconstr
                       FStar_Parser_Const.nil_lid
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____4170
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 FStar_Syntax_Syntax.mk_Tm_app uu____4169 [t]  in
               uu____4164 FStar_Pervasives_Native.None rng
           | hd1::tl1 ->
               let cons1 =
                 let uu____4194 =
                   FStar_Syntax_Syntax.tdataconstr
                     FStar_Parser_Const.cons_lid
                    in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu____4194
                   [FStar_Syntax_Syntax.U_zero]
                  in
               let proj f cons_tm =
                 let fid = FStar_Ident.mk_ident (f, rng)  in
                 let proj =
                   FStar_Syntax_Util.mk_field_projector_name_from_ident
                     FStar_Parser_Const.cons_lid fid
                    in
                 let proj_tm =
                   let uu____4211 =
                     FStar_Syntax_Syntax.lid_as_fv proj
                       FStar_Syntax_Syntax.delta_equational
                       FStar_Pervasives_Native.None
                      in
                   FStar_Syntax_Syntax.fv_to_tm uu____4211  in
                 let uu____4212 =
                   let uu____4217 =
                     FStar_Syntax_Syntax.mk_Tm_uinst proj_tm
                       [FStar_Syntax_Syntax.U_zero]
                      in
                   let uu____4218 =
                     let uu____4219 =
                       let uu____4228 = type_of ea  in
                       FStar_Syntax_Syntax.iarg uu____4228  in
                     let uu____4229 =
                       let uu____4240 = FStar_Syntax_Syntax.as_arg cons_tm
                          in
                       [uu____4240]  in
                     uu____4219 :: uu____4229  in
                   FStar_Syntax_Syntax.mk_Tm_app uu____4217 uu____4218  in
                 uu____4212 FStar_Pervasives_Native.None rng  in
               let shadow_hd = map_shadow shadow_l (proj "hd")  in
               let shadow_tl = map_shadow shadow_l (proj "tl")  in
               let uu____4391 =
                 let uu____4396 =
                   let uu____4397 =
                     let uu____4408 =
                       let uu____4417 =
                         let uu____4418 = embed ea hd1  in
                         uu____4418 rng shadow_hd norm1  in
                       FStar_Syntax_Syntax.as_arg uu____4417  in
                     let uu____4488 =
                       let uu____4499 =
                         let uu____4508 = em tl1 rng shadow_tl norm1  in
                         FStar_Syntax_Syntax.as_arg uu____4508  in
                       [uu____4499]  in
                     uu____4408 :: uu____4488  in
                   t :: uu____4397  in
                 FStar_Syntax_Syntax.mk_Tm_app cons1 uu____4396  in
               uu____4391 FStar_Pervasives_Native.None rng)
       in
    let rec un t0 w norm1 =
      let t = FStar_Syntax_Util.unmeta_safe t0  in
      lazy_unembed printer t t_list_a
        (fun t1  ->
           let uu____4622 = FStar_Syntax_Util.head_and_args t1  in
           match uu____4622 with
           | (hd1,args) ->
               let uu____4669 =
                 let uu____4682 =
                   let uu____4683 = FStar_Syntax_Util.un_uinst hd1  in
                   uu____4683.FStar_Syntax_Syntax.n  in
                 (uu____4682, args)  in
               (match uu____4669 with
                | (FStar_Syntax_Syntax.Tm_fvar fv,uu____4699) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.nil_lid
                    -> FStar_Pervasives_Native.Some []
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(uu____4719,FStar_Pervasives_Native.Some
                       (FStar_Syntax_Syntax.Implicit uu____4720))::(hd2,FStar_Pervasives_Native.None
                                                                    )::
                   (tl1,FStar_Pervasives_Native.None )::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.cons_lid
                    ->
                    let uu____4761 =
                      let uu____4764 = unembed ea hd2  in uu____4764 w norm1
                       in
                    FStar_Util.bind_opt uu____4761
                      (fun hd3  ->
                         let uu____4782 = un tl1 w norm1  in
                         FStar_Util.bind_opt uu____4782
                           (fun tl2  ->
                              FStar_Pervasives_Native.Some (hd3 :: tl2)))
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(hd2,FStar_Pervasives_Native.None )::(tl1,FStar_Pervasives_Native.None
                                                            )::[])
                    when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.cons_lid
                    ->
                    let uu____4832 =
                      let uu____4835 = unembed ea hd2  in uu____4835 w norm1
                       in
                    FStar_Util.bind_opt uu____4832
                      (fun hd3  ->
                         let uu____4853 = un tl1 w norm1  in
                         FStar_Util.bind_opt uu____4853
                           (fun tl2  ->
                              FStar_Pervasives_Native.Some (hd3 :: tl2)))
                | uu____4870 ->
                    (if w
                     then
                       (let uu____4884 =
                          let uu____4889 =
                            let uu____4890 =
                              FStar_Syntax_Print.term_to_string t0  in
                            FStar_Util.format1 "Not an embedded list: %s"
                              uu____4890
                             in
                          (FStar_Errors.Warning_NotEmbedded, uu____4889)  in
                        FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                          uu____4884)
                     else ();
                     FStar_Pervasives_Native.None)))
       in
    let uu____4894 =
      let uu____4895 = type_of ea  in
      FStar_Syntax_Syntax.t_list_of uu____4895  in
    mk_emb_with_printer em un uu____4894 printer
  
let (e_string_list : Prims.string Prims.list embedding) = e_list e_string 
type norm_step =
  | Simpl 
  | Weak 
  | HNF 
  | Primops 
  | Delta 
  | Zeta 
  | Iota 
  | UnfoldOnly of Prims.string Prims.list 
  | UnfoldFully of Prims.string Prims.list 
  | UnfoldAttr of FStar_Syntax_Syntax.attribute 
let (uu___is_Simpl : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Simpl  -> true | uu____4926 -> false
  
let (uu___is_Weak : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Weak  -> true | uu____4932 -> false
  
let (uu___is_HNF : norm_step -> Prims.bool) =
  fun projectee  -> match projectee with | HNF  -> true | uu____4938 -> false 
let (uu___is_Primops : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____4944 -> false
  
let (uu___is_Delta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Delta  -> true | uu____4950 -> false
  
let (uu___is_Zeta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Zeta  -> true | uu____4956 -> false
  
let (uu___is_Iota : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Iota  -> true | uu____4962 -> false
  
let (uu___is_UnfoldOnly : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____4971 -> false
  
let (__proj__UnfoldOnly__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldFully : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldFully _0 -> true | uu____4993 -> false
  
let (__proj__UnfoldFully__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldFully _0 -> _0 
let (uu___is_UnfoldAttr : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____5013 -> false
  
let (__proj__UnfoldAttr__item___0 :
  norm_step -> FStar_Syntax_Syntax.attribute) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
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
let (steps_UnfoldOnly : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.steps_unfoldonly 
let (steps_UnfoldFully : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.steps_unfoldonly 
let (steps_UnfoldAttr : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.steps_unfoldattr 
let (e_norm_step : norm_step embedding) =
  let t_norm_step1 =
    let uu____5024 =
      FStar_Ident.lid_of_str "FStar.Syntax.Embeddings.norm_step"  in
    FStar_Syntax_Util.fvar_const uu____5024  in
  let printer uu____5030 = "norm_step"  in
  let em n1 rng _topt norm1 =
    lazy_embed printer rng t_norm_step1 n1
      (fun uu____5095  ->
         match n1 with
         | Simpl  -> steps_Simpl
         | Weak  -> steps_Weak
         | HNF  -> steps_HNF
         | Primops  -> steps_Primops
         | Delta  -> steps_Delta
         | Zeta  -> steps_Zeta
         | Iota  -> steps_Iota
         | UnfoldOnly l ->
             let uu____5099 =
               let uu____5104 =
                 let uu____5105 =
                   let uu____5114 =
                     let uu____5115 =
                       let uu____5122 = e_list e_string  in
                       embed uu____5122 l  in
                     uu____5115 rng FStar_Pervasives_Native.None norm1  in
                   FStar_Syntax_Syntax.as_arg uu____5114  in
                 [uu____5105]  in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldOnly uu____5104  in
             uu____5099 FStar_Pervasives_Native.None rng
         | UnfoldFully l ->
             let uu____5177 =
               let uu____5182 =
                 let uu____5183 =
                   let uu____5192 =
                     let uu____5193 =
                       let uu____5200 = e_list e_string  in
                       embed uu____5200 l  in
                     uu____5193 rng FStar_Pervasives_Native.None norm1  in
                   FStar_Syntax_Syntax.as_arg uu____5192  in
                 [uu____5183]  in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldFully uu____5182  in
             uu____5177 FStar_Pervasives_Native.None rng
         | UnfoldAttr a ->
             let uu____5253 =
               let uu____5258 =
                 let uu____5259 = FStar_Syntax_Syntax.as_arg a  in
                 [uu____5259]  in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldAttr uu____5258  in
             uu____5253 FStar_Pervasives_Native.None rng)
     in
  let un t0 w norm1 =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    lazy_unembed printer t t_norm_step1
      (fun t1  ->
         let uu____5318 = FStar_Syntax_Util.head_and_args t1  in
         match uu____5318 with
         | (hd1,args) ->
             let uu____5363 =
               let uu____5378 =
                 let uu____5379 = FStar_Syntax_Util.un_uinst hd1  in
                 uu____5379.FStar_Syntax_Syntax.n  in
               (uu____5378, args)  in
             (match uu____5363 with
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
              | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____5529)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldonly
                  ->
                  let uu____5564 =
                    let uu____5569 =
                      let uu____5578 = e_list e_string  in
                      unembed uu____5578 l  in
                    uu____5569 w norm1  in
                  FStar_Util.bind_opt uu____5564
                    (fun ss  ->
                       FStar_All.pipe_left
                         (fun _0_16  -> FStar_Pervasives_Native.Some _0_16)
                         (UnfoldOnly ss))
              | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____5601)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldfully
                  ->
                  let uu____5636 =
                    let uu____5641 =
                      let uu____5650 = e_list e_string  in
                      unembed uu____5650 l  in
                    uu____5641 w norm1  in
                  FStar_Util.bind_opt uu____5636
                    (fun ss  ->
                       FStar_All.pipe_left
                         (fun _0_17  -> FStar_Pervasives_Native.Some _0_17)
                         (UnfoldFully ss))
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____5672::(a,uu____5674)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldattr
                  -> FStar_Pervasives_Native.Some (UnfoldAttr a)
              | uu____5725 ->
                  (if w
                   then
                     (let uu____5741 =
                        let uu____5746 =
                          let uu____5747 =
                            FStar_Syntax_Print.term_to_string t0  in
                          FStar_Util.format1 "Not an embedded norm_step: %s"
                            uu____5747
                           in
                        (FStar_Errors.Warning_NotEmbedded, uu____5746)  in
                      FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                        uu____5741)
                   else ();
                   FStar_Pervasives_Native.None)))
     in
  mk_emb_with_printer em un FStar_Syntax_Syntax.t_norm_step printer 
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
    | uu____5842 ->
        (if w
         then
           (let uu____5844 =
              let uu____5849 =
                let uu____5850 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded range: %s" uu____5850  in
              (FStar_Errors.Warning_NotEmbedded, uu____5849)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____5844)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb_with_printer em un FStar_Syntax_Syntax.t_range
    FStar_Range.string_of_range
  
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
        let uu____5915 =
          let uu____5922 =
            let uu____5923 =
              let uu____5938 =
                let uu____5947 =
                  let uu____5954 = FStar_Syntax_Syntax.null_bv ea.typ  in
                  (uu____5954, FStar_Pervasives_Native.None)  in
                [uu____5947]  in
              let uu____5969 = FStar_Syntax_Syntax.mk_Total eb.typ  in
              (uu____5938, uu____5969)  in
            FStar_Syntax_Syntax.Tm_arrow uu____5923  in
          FStar_Syntax_Syntax.mk uu____5922  in
        uu____5915 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
      let printer f = "<fun>"  in
      let em f rng shadow_f norm1 =
        let f_wrapped x =
          let shadow_app =
            map_shadow shadow_f
              (fun f1  ->
                 let uu____6135 =
                   let uu____6140 =
                     let uu____6141 = FStar_Syntax_Syntax.as_arg x  in
                     [uu____6141]  in
                   FStar_Syntax_Syntax.mk_Tm_app f1 uu____6140  in
                 uu____6135 FStar_Pervasives_Native.None rng)
             in
          let uu____6168 =
            let uu____6171 =
              let uu____6174 = unembed ea x  in uu____6174 true norm1  in
            FStar_Util.map_opt uu____6171
              (fun x1  ->
                 let uu____6213 =
                   let uu____6220 = f x1  in embed eb uu____6220  in
                 uu____6213 rng shadow_app norm1)
             in
          or_else uu____6168
            (fun uu____6286  ->
               let uu____6287 = force_shadow shadow_app  in
               match uu____6287 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Exn.raise Embedding_failure
               | FStar_Pervasives_Native.Some app ->
                   norm1 (FStar_Util.Inr app))
           in
        lazy_embed (fun uu____6353  -> "<fun>") rng t_arrow f_wrapped
          (fun uu____6358  ->
             let uu____6359 = force_shadow shadow_f  in
             match uu____6359 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Exn.raise Embedding_failure
             | FStar_Pervasives_Native.Some repr_f ->
                 norm1 (FStar_Util.Inr repr_f))
         in
      let un f w norm1 =
        lazy_unembed printer f t_arrow
          (fun f1  ->
             let f_wrapped a =
               let a_tm =
                 let uu____6473 = embed ea a  in
                 uu____6473 f1.FStar_Syntax_Syntax.pos
                   FStar_Pervasives_Native.None norm1
                  in
               let b_tm =
                 let uu____6506 =
                   let uu____6511 =
                     let uu____6512 =
                       let uu____6517 =
                         let uu____6518 = FStar_Syntax_Syntax.as_arg a_tm  in
                         [uu____6518]  in
                       FStar_Syntax_Syntax.mk_Tm_app f1 uu____6517  in
                     uu____6512 FStar_Pervasives_Native.None
                       f1.FStar_Syntax_Syntax.pos
                      in
                   FStar_Util.Inr uu____6511  in
                 norm1 uu____6506  in
               let uu____6545 =
                 let uu____6548 = unembed eb b_tm  in uu____6548 w norm1  in
               match uu____6545 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Exn.raise Unembedding_failure
               | FStar_Pervasives_Native.Some b -> b  in
             FStar_Pervasives_Native.Some f_wrapped)
         in
      let tarr =
        let uu____6566 =
          let uu____6573 =
            let uu____6574 =
              let uu____6589 =
                let uu____6598 =
                  let uu____6605 =
                    let uu____6606 = type_of ea  in
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      uu____6606
                     in
                  FStar_Syntax_Syntax.mk_binder uu____6605  in
                [uu____6598]  in
              let uu____6619 =
                let uu____6622 = type_of eb  in
                FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total uu____6622
                 in
              (uu____6589, uu____6619)  in
            FStar_Syntax_Syntax.Tm_arrow uu____6574  in
          FStar_Syntax_Syntax.mk uu____6573  in
        uu____6566 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
      mk_emb em un tarr
  
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
                let uu____6720 = FStar_List.splitAt n_tvars args  in
                match uu____6720 with
                | (_tvar_args,rest_args) ->
                    let uu____6797 = FStar_List.hd rest_args  in
                    (match uu____6797 with
                     | (x,uu____6817) ->
                         let shadow_app =
                           let uu____6831 =
                             FStar_Common.mk_thunk
                               (fun uu____6840  ->
                                  let uu____6841 =
                                    let uu____6846 =
                                      norm1 (FStar_Util.Inl fv_lid1)  in
                                    FStar_Syntax_Syntax.mk_Tm_app uu____6846
                                      args
                                     in
                                  uu____6841 FStar_Pervasives_Native.None rng)
                              in
                           FStar_Pervasives_Native.Some uu____6831  in
                         let uu____6892 =
                           let uu____6895 =
                             let uu____6898 = unembed ea x  in
                             uu____6898 true norm1  in
                           FStar_Util.map_opt uu____6895
                             (fun x1  ->
                                let uu____6937 =
                                  let uu____6944 = f x1  in
                                  embed eb uu____6944  in
                                uu____6937 rng shadow_app norm1)
                            in
                         (match uu____6892 with
                          | FStar_Pervasives_Native.Some x1 ->
                              FStar_Pervasives_Native.Some x1
                          | FStar_Pervasives_Native.None  ->
                              let uu____6973 = force_shadow shadow_app  in
                              (match uu____6973 with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some app ->
                                   let uu____6979 =
                                     norm1 (FStar_Util.Inr app)  in
                                   FStar_Pervasives_Native.Some uu____6979)))
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
                  let uu____7079 = FStar_List.splitAt n_tvars args  in
                  match uu____7079 with
                  | (_tvar_args,rest_args) ->
                      let uu____7142 = FStar_List.hd rest_args  in
                      (match uu____7142 with
                       | (x,uu____7158) ->
                           let uu____7163 =
                             let uu____7170 = FStar_List.tl rest_args  in
                             FStar_List.hd uu____7170  in
                           (match uu____7163 with
                            | (y,uu____7194) ->
                                let shadow_app =
                                  let uu____7204 =
                                    FStar_Common.mk_thunk
                                      (fun uu____7213  ->
                                         let uu____7214 =
                                           let uu____7219 =
                                             norm1 (FStar_Util.Inl fv_lid1)
                                              in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____7219 args
                                            in
                                         uu____7214
                                           FStar_Pervasives_Native.None rng)
                                     in
                                  FStar_Pervasives_Native.Some uu____7204  in
                                let uu____7265 =
                                  let uu____7268 =
                                    let uu____7271 = unembed ea x  in
                                    uu____7271 true norm1  in
                                  FStar_Util.bind_opt uu____7268
                                    (fun x1  ->
                                       let uu____7287 =
                                         let uu____7290 = unembed eb y  in
                                         uu____7290 true norm1  in
                                       FStar_Util.bind_opt uu____7287
                                         (fun y1  ->
                                            let uu____7306 =
                                              let uu____7307 =
                                                let uu____7314 = f x1 y1  in
                                                embed ec uu____7314  in
                                              uu____7307 rng shadow_app norm1
                                               in
                                            FStar_Pervasives_Native.Some
                                              uu____7306))
                                   in
                                (match uu____7265 with
                                 | FStar_Pervasives_Native.Some x1 ->
                                     FStar_Pervasives_Native.Some x1
                                 | FStar_Pervasives_Native.None  ->
                                     let uu____7343 = force_shadow shadow_app
                                        in
                                     (match uu____7343 with
                                      | FStar_Pervasives_Native.None  ->
                                          FStar_Pervasives_Native.None
                                      | FStar_Pervasives_Native.Some app ->
                                          let uu____7349 =
                                            norm1 (FStar_Util.Inr app)  in
                                          FStar_Pervasives_Native.Some
                                            uu____7349))))
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
                    let uu____7468 = FStar_List.splitAt n_tvars args  in
                    match uu____7468 with
                    | (_tvar_args,rest_args) ->
                        let uu____7531 = FStar_List.hd rest_args  in
                        (match uu____7531 with
                         | (x,uu____7547) ->
                             let uu____7552 =
                               let uu____7559 = FStar_List.tl rest_args  in
                               FStar_List.hd uu____7559  in
                             (match uu____7552 with
                              | (y,uu____7583) ->
                                  let uu____7588 =
                                    let uu____7595 =
                                      let uu____7604 =
                                        FStar_List.tl rest_args  in
                                      FStar_List.tl uu____7604  in
                                    FStar_List.hd uu____7595  in
                                  (match uu____7588 with
                                   | (z,uu____7634) ->
                                       let shadow_app =
                                         let uu____7644 =
                                           FStar_Common.mk_thunk
                                             (fun uu____7653  ->
                                                let uu____7654 =
                                                  let uu____7659 =
                                                    norm1
                                                      (FStar_Util.Inl fv_lid1)
                                                     in
                                                  FStar_Syntax_Syntax.mk_Tm_app
                                                    uu____7659 args
                                                   in
                                                uu____7654
                                                  FStar_Pervasives_Native.None
                                                  rng)
                                            in
                                         FStar_Pervasives_Native.Some
                                           uu____7644
                                          in
                                       let uu____7705 =
                                         let uu____7708 =
                                           let uu____7711 = unembed ea x  in
                                           uu____7711 true norm1  in
                                         FStar_Util.bind_opt uu____7708
                                           (fun x1  ->
                                              let uu____7727 =
                                                let uu____7730 = unembed eb y
                                                   in
                                                uu____7730 true norm1  in
                                              FStar_Util.bind_opt uu____7727
                                                (fun y1  ->
                                                   let uu____7746 =
                                                     let uu____7749 =
                                                       unembed ec z  in
                                                     uu____7749 true norm1
                                                      in
                                                   FStar_Util.bind_opt
                                                     uu____7746
                                                     (fun z1  ->
                                                        let uu____7765 =
                                                          let uu____7766 =
                                                            let uu____7773 =
                                                              f x1 y1 z1  in
                                                            embed ed
                                                              uu____7773
                                                             in
                                                          uu____7766 rng
                                                            shadow_app norm1
                                                           in
                                                        FStar_Pervasives_Native.Some
                                                          uu____7765)))
                                          in
                                       (match uu____7705 with
                                        | FStar_Pervasives_Native.Some x1 ->
                                            FStar_Pervasives_Native.Some x1
                                        | FStar_Pervasives_Native.None  ->
                                            let uu____7802 =
                                              force_shadow shadow_app  in
                                            (match uu____7802 with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some
                                                 app ->
                                                 let uu____7808 =
                                                   norm1 (FStar_Util.Inr app)
                                                    in
                                                 FStar_Pervasives_Native.Some
                                                   uu____7808)))))
                     in
                  f_wrapped
  