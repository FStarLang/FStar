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
            let thunk = FStar_Common.mk_thunk f  in
            let tm = FStar_Common.force_thunk thunk  in
            (let uu____1485 = FStar_Syntax_Print.term_to_string ta  in
             let uu____1486 = pa x  in
             let uu____1489 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print3
               "Embedding a %s\n\tvalue is %s\nthunked as a %s\n" uu____1485
               uu____1486 uu____1489);
            (let uu____1490 =
               let uu____1497 =
                 let uu____1498 =
                   let uu____1499 = FStar_Dyn.mkdyn x  in
                   {
                     FStar_Syntax_Syntax.blob = uu____1499;
                     FStar_Syntax_Syntax.lkind =
                       (FStar_Syntax_Syntax.Lazy_embedding (ta, thunk));
                     FStar_Syntax_Syntax.ltyp = FStar_Syntax_Syntax.tun;
                     FStar_Syntax_Syntax.rng = rng
                   }  in
                 FStar_Syntax_Syntax.Tm_lazy uu____1498  in
               FStar_Syntax_Syntax.mk uu____1497  in
             uu____1490 FStar_Pervasives_Native.None rng)
  
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
                FStar_Syntax_Syntax.ltyp = uu____1609;
                FStar_Syntax_Syntax.rng = uu____1610;_}
              ->
              let a = FStar_Dyn.undyn b  in
              let tm = FStar_Common.force_thunk t  in
              ((let uu____1672 = FStar_Syntax_Print.term_to_string tb  in
                let uu____1673 = FStar_Syntax_Print.term_to_string ta  in
                let uu____1674 = FStar_Syntax_Print.term_to_string tm  in
                FStar_Util.print3
                  "Unembedding a %s as a %s\n unthunked a %s\n" uu____1672
                  uu____1673 uu____1674);
               (let uu____1676 = f tm  in
                match uu____1676 with
                | FStar_Pervasives_Native.None  -> ()
                | FStar_Pervasives_Native.Some a' ->
                    FStar_Util.print_string "Successful unembedding\n");
               FStar_Pervasives_Native.Some a)
          | uu____1680 -> f x1
  
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
    let uu___205_1841 = FStar_Syntax_Util.exp_unit  in
    {
      FStar_Syntax_Syntax.n = (uu___205_1841.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___205_1841.FStar_Syntax_Syntax.vars)
    }  in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unascribe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit ) ->
        FStar_Pervasives_Native.Some ()
    | uu____1869 ->
        (if w
         then
           (let uu____1871 =
              let uu____1876 =
                let uu____1877 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded unit: %s" uu____1877  in
              (FStar_Errors.Warning_NotEmbedded, uu____1876)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____1871)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb_with_printer em un FStar_Syntax_Syntax.t_unit
    (fun uu____1880  -> "()")
  
let (e_bool : Prims.bool embedding) =
  let em b rng _topt _norm =
    let t =
      if b
      then FStar_Syntax_Util.exp_true_bool
      else FStar_Syntax_Util.exp_false_bool  in
    let uu___206_1952 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___206_1952.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___206_1952.FStar_Syntax_Syntax.vars)
    }  in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) ->
        FStar_Pervasives_Native.Some b
    | uu____1983 ->
        (if w
         then
           (let uu____1985 =
              let uu____1990 =
                let uu____1991 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded bool: %s" uu____1991  in
              (FStar_Errors.Warning_NotEmbedded, uu____1990)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____1985)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb_with_printer em un FStar_Syntax_Syntax.t_bool
    FStar_Util.string_of_bool
  
let (e_char : FStar_Char.char embedding) =
  let em c rng _topt _norm =
    let t = FStar_Syntax_Util.exp_char c  in
    let uu___207_2062 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___207_2062.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___207_2062.FStar_Syntax_Syntax.vars)
    }  in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c) ->
        FStar_Pervasives_Native.Some c
    | uu____2096 ->
        (if w
         then
           (let uu____2098 =
              let uu____2103 =
                let uu____2104 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded char: %s" uu____2104  in
              (FStar_Errors.Warning_NotEmbedded, uu____2103)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____2098)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb_with_printer em un FStar_Syntax_Syntax.t_char
    FStar_Util.string_of_char
  
let (e_int : FStar_BigInt.t embedding) =
  let t_int1 = FStar_Syntax_Util.fvar_const FStar_Parser_Const.int_lid  in
  let em i rng _topt _norm =
    lazy_embed FStar_BigInt.string_of_big_int rng t_int1 i
      (fun uu____2176  ->
         let uu____2177 = FStar_BigInt.string_of_big_int i  in
         FStar_Syntax_Util.exp_int uu____2177)
     in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    lazy_unembed FStar_BigInt.string_of_big_int t t_int1
      (fun t1  ->
         match t1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
             (s,uu____2211)) ->
             let uu____2224 = FStar_BigInt.big_int_of_string s  in
             FStar_Pervasives_Native.Some uu____2224
         | uu____2225 ->
             (if w
              then
                (let uu____2227 =
                   let uu____2232 =
                     let uu____2233 = FStar_Syntax_Print.term_to_string t0
                        in
                     FStar_Util.format1 "Not an embedded int: %s" uu____2233
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____2232)  in
                 FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____2227)
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
        (s,uu____2328)) -> FStar_Pervasives_Native.Some s
    | uu____2329 ->
        (if w
         then
           (let uu____2331 =
              let uu____2336 =
                let uu____2337 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded string: %s" uu____2337
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____2336)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____2331)
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
      let uu____2363 =
        let uu____2368 =
          let uu____2369 = FStar_Syntax_Syntax.as_arg ea.typ  in [uu____2369]
           in
        FStar_Syntax_Syntax.mk_Tm_app t_opt uu____2368  in
      uu____2363 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
    let printer uu___204_2403 =
      match uu___204_2403 with
      | FStar_Pervasives_Native.None  -> "None"
      | FStar_Pervasives_Native.Some x ->
          let uu____2407 =
            let uu____2408 = ea.print x  in Prims.strcat uu____2408 ")"  in
          Prims.strcat "(Some " uu____2407
       in
    let em o rng topt norm1 =
      lazy_embed printer rng t_option_a o
        (fun uu____2482  ->
           match o with
           | FStar_Pervasives_Native.None  ->
               let uu____2483 =
                 let uu____2488 =
                   let uu____2489 =
                     FStar_Syntax_Syntax.tdataconstr
                       FStar_Parser_Const.none_lid
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____2489
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 let uu____2490 =
                   let uu____2491 =
                     let uu____2500 = type_of ea  in
                     FStar_Syntax_Syntax.iarg uu____2500  in
                   [uu____2491]  in
                 FStar_Syntax_Syntax.mk_Tm_app uu____2488 uu____2490  in
               uu____2483 FStar_Pervasives_Native.None rng
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
                        let uu____2589 =
                          FStar_Syntax_Syntax.lid_as_fv some_v
                            FStar_Syntax_Syntax.delta_equational
                            FStar_Pervasives_Native.None
                           in
                        FStar_Syntax_Syntax.fv_to_tm uu____2589  in
                      let uu____2590 =
                        let uu____2595 =
                          FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm
                            [FStar_Syntax_Syntax.U_zero]
                           in
                        let uu____2596 =
                          let uu____2597 =
                            let uu____2606 = type_of ea  in
                            FStar_Syntax_Syntax.iarg uu____2606  in
                          let uu____2607 =
                            let uu____2618 = FStar_Syntax_Syntax.as_arg t  in
                            [uu____2618]  in
                          uu____2597 :: uu____2607  in
                        FStar_Syntax_Syntax.mk_Tm_app uu____2595 uu____2596
                         in
                      uu____2590 FStar_Pervasives_Native.None rng)
                  in
               let uu____2653 =
                 let uu____2658 =
                   let uu____2659 =
                     FStar_Syntax_Syntax.tdataconstr
                       FStar_Parser_Const.some_lid
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____2659
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 let uu____2660 =
                   let uu____2661 =
                     let uu____2670 = type_of ea  in
                     FStar_Syntax_Syntax.iarg uu____2670  in
                   let uu____2671 =
                     let uu____2682 =
                       let uu____2691 =
                         let uu____2692 = embed ea a  in
                         uu____2692 rng shadow_a norm1  in
                       FStar_Syntax_Syntax.as_arg uu____2691  in
                     [uu____2682]  in
                   uu____2661 :: uu____2671  in
                 FStar_Syntax_Syntax.mk_Tm_app uu____2658 uu____2660  in
               uu____2653 FStar_Pervasives_Native.None rng)
       in
    let un t0 w norm1 =
      let t = FStar_Syntax_Util.unmeta_safe t0  in
      lazy_unembed printer t t_option_a
        (fun t1  ->
           let uu____2827 = FStar_Syntax_Util.head_and_args t1  in
           match uu____2827 with
           | (hd1,args) ->
               let uu____2874 =
                 let uu____2889 =
                   let uu____2890 = FStar_Syntax_Util.un_uinst hd1  in
                   uu____2890.FStar_Syntax_Syntax.n  in
                 (uu____2889, args)  in
               (match uu____2874 with
                | (FStar_Syntax_Syntax.Tm_fvar fv,uu____2908) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.none_lid
                    ->
                    FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,uu____2932::(a,uu____2934)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.some_lid
                    ->
                    let uu____2985 =
                      let uu____2988 = unembed ea a  in uu____2988 w norm1
                       in
                    FStar_Util.bind_opt uu____2985
                      (fun a1  ->
                         FStar_Pervasives_Native.Some
                           (FStar_Pervasives_Native.Some a1))
                | uu____3007 ->
                    (if w
                     then
                       (let uu____3023 =
                          let uu____3028 =
                            let uu____3029 =
                              FStar_Syntax_Print.term_to_string t0  in
                            FStar_Util.format1 "Not an embedded option: %s"
                              uu____3029
                             in
                          (FStar_Errors.Warning_NotEmbedded, uu____3028)  in
                        FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                          uu____3023)
                     else ();
                     FStar_Pervasives_Native.None)))
       in
    let uu____3033 =
      let uu____3034 = type_of ea  in
      FStar_Syntax_Syntax.t_option_of uu____3034  in
    mk_emb_with_printer em un uu____3033 printer
  
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
        let uu____3075 =
          let uu____3080 =
            let uu____3081 = FStar_Syntax_Syntax.as_arg ea.typ  in
            let uu____3090 =
              let uu____3101 = FStar_Syntax_Syntax.as_arg eb.typ  in
              [uu____3101]  in
            uu____3081 :: uu____3090  in
          FStar_Syntax_Syntax.mk_Tm_app t_tup2 uu____3080  in
        uu____3075 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
      let printer uu____3145 =
        match uu____3145 with
        | (x,y) ->
            let uu____3152 = ea.print x  in
            let uu____3153 = eb.print y  in
            FStar_Util.format2 "(%s, %s)" uu____3152 uu____3153
         in
      let em x rng topt norm1 =
        lazy_embed printer rng t_pair_a_b x
          (fun uu____3236  ->
             let proj i ab =
               let uu____3250 =
                 let uu____3255 =
                   FStar_Parser_Const.mk_tuple_data_lid (Prims.parse_int "2")
                     rng
                    in
                 let uu____3256 =
                   FStar_Syntax_Syntax.null_bv FStar_Syntax_Syntax.tun  in
                 FStar_Syntax_Util.mk_field_projector_name uu____3255
                   uu____3256 i
                  in
               match uu____3250 with
               | (proj_1,uu____3260) ->
                   let proj_1_tm =
                     let uu____3262 =
                       FStar_Syntax_Syntax.lid_as_fv proj_1
                         FStar_Syntax_Syntax.delta_equational
                         FStar_Pervasives_Native.None
                        in
                     FStar_Syntax_Syntax.fv_to_tm uu____3262  in
                   let uu____3263 =
                     let uu____3268 =
                       FStar_Syntax_Syntax.mk_Tm_uinst proj_1_tm
                         [FStar_Syntax_Syntax.U_zero]
                        in
                     let uu____3269 =
                       let uu____3270 =
                         let uu____3279 = type_of ea  in
                         FStar_Syntax_Syntax.iarg uu____3279  in
                       let uu____3280 =
                         let uu____3291 =
                           let uu____3300 = type_of eb  in
                           FStar_Syntax_Syntax.iarg uu____3300  in
                         let uu____3301 =
                           let uu____3312 = FStar_Syntax_Syntax.as_arg ab  in
                           [uu____3312]  in
                         uu____3291 :: uu____3301  in
                       uu____3270 :: uu____3280  in
                     FStar_Syntax_Syntax.mk_Tm_app uu____3268 uu____3269  in
                   uu____3263 FStar_Pervasives_Native.None rng
                in
             let shadow_a = map_shadow topt (proj (Prims.parse_int "1"))  in
             let shadow_b = map_shadow topt (proj (Prims.parse_int "2"))  in
             let uu____3471 =
               let uu____3476 =
                 let uu____3477 =
                   FStar_Syntax_Syntax.tdataconstr
                     FStar_Parser_Const.lid_Mktuple2
                    in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu____3477
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                  in
               let uu____3478 =
                 let uu____3479 =
                   let uu____3488 = type_of ea  in
                   FStar_Syntax_Syntax.iarg uu____3488  in
                 let uu____3489 =
                   let uu____3500 =
                     let uu____3509 = type_of eb  in
                     FStar_Syntax_Syntax.iarg uu____3509  in
                   let uu____3510 =
                     let uu____3521 =
                       let uu____3530 =
                         let uu____3531 =
                           embed ea (FStar_Pervasives_Native.fst x)  in
                         uu____3531 rng shadow_a norm1  in
                       FStar_Syntax_Syntax.as_arg uu____3530  in
                     let uu____3601 =
                       let uu____3612 =
                         let uu____3621 =
                           let uu____3622 =
                             embed eb (FStar_Pervasives_Native.snd x)  in
                           uu____3622 rng shadow_b norm1  in
                         FStar_Syntax_Syntax.as_arg uu____3621  in
                       [uu____3612]  in
                     uu____3521 :: uu____3601  in
                   uu____3500 :: uu____3510  in
                 uu____3479 :: uu____3489  in
               FStar_Syntax_Syntax.mk_Tm_app uu____3476 uu____3478  in
             uu____3471 FStar_Pervasives_Native.None rng)
         in
      let un t0 w norm1 =
        let t = FStar_Syntax_Util.unmeta_safe t0  in
        lazy_unembed printer t t_pair_a_b
          (fun t1  ->
             let uu____3785 = FStar_Syntax_Util.head_and_args t1  in
             match uu____3785 with
             | (hd1,args) ->
                 let uu____3834 =
                   let uu____3847 =
                     let uu____3848 = FStar_Syntax_Util.un_uinst hd1  in
                     uu____3848.FStar_Syntax_Syntax.n  in
                   (uu____3847, args)  in
                 (match uu____3834 with
                  | (FStar_Syntax_Syntax.Tm_fvar
                     fv,uu____3866::uu____3867::(a,uu____3869)::(b,uu____3871)::[])
                      when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.lid_Mktuple2
                      ->
                      let uu____3930 =
                        let uu____3933 = unembed ea a  in uu____3933 w norm1
                         in
                      FStar_Util.bind_opt uu____3930
                        (fun a1  ->
                           let uu____3953 =
                             let uu____3956 = unembed eb b  in
                             uu____3956 w norm1  in
                           FStar_Util.bind_opt uu____3953
                             (fun b1  ->
                                FStar_Pervasives_Native.Some (a1, b1)))
                  | uu____3979 ->
                      (if w
                       then
                         (let uu____3993 =
                            let uu____3998 =
                              let uu____3999 =
                                FStar_Syntax_Print.term_to_string t0  in
                              FStar_Util.format1 "Not an embedded pair: %s"
                                uu____3999
                               in
                            (FStar_Errors.Warning_NotEmbedded, uu____3998)
                             in
                          FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                            uu____3993)
                       else ();
                       FStar_Pervasives_Native.None)))
         in
      let uu____4005 =
        let uu____4006 = type_of ea  in
        let uu____4007 = type_of eb  in
        FStar_Syntax_Syntax.t_tuple2_of uu____4006 uu____4007  in
      mk_emb_with_printer em un uu____4005 printer
  
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea  ->
    let t_list_a =
      let t_list = FStar_Syntax_Util.fvar_const FStar_Parser_Const.list_lid
         in
      let uu____4034 =
        let uu____4039 =
          let uu____4040 = FStar_Syntax_Syntax.as_arg ea.typ  in [uu____4040]
           in
        FStar_Syntax_Syntax.mk_Tm_app t_list uu____4039  in
      uu____4034 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
    let printer l =
      let uu____4077 =
        let uu____4078 =
          let uu____4079 = FStar_List.map ea.print l  in
          FStar_All.pipe_right uu____4079 (FStar_String.concat "; ")  in
        Prims.strcat uu____4078 "]"  in
      Prims.strcat "[" uu____4077  in
    let rec em l rng shadow_l norm1 =
      lazy_embed printer rng t_list_a l
        (fun uu____4158  ->
           let t =
             let uu____4160 = type_of ea  in
             FStar_Syntax_Syntax.iarg uu____4160  in
           match l with
           | [] ->
               let uu____4161 =
                 let uu____4166 =
                   let uu____4167 =
                     FStar_Syntax_Syntax.tdataconstr
                       FStar_Parser_Const.nil_lid
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____4167
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 FStar_Syntax_Syntax.mk_Tm_app uu____4166 [t]  in
               uu____4161 FStar_Pervasives_Native.None rng
           | hd1::tl1 ->
               let cons1 =
                 let uu____4191 =
                   FStar_Syntax_Syntax.tdataconstr
                     FStar_Parser_Const.cons_lid
                    in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu____4191
                   [FStar_Syntax_Syntax.U_zero]
                  in
               let proj f cons_tm =
                 let fid = FStar_Ident.mk_ident (f, rng)  in
                 let proj =
                   FStar_Syntax_Util.mk_field_projector_name_from_ident
                     FStar_Parser_Const.cons_lid fid
                    in
                 let proj_tm =
                   let uu____4208 =
                     FStar_Syntax_Syntax.lid_as_fv proj
                       FStar_Syntax_Syntax.delta_equational
                       FStar_Pervasives_Native.None
                      in
                   FStar_Syntax_Syntax.fv_to_tm uu____4208  in
                 let uu____4209 =
                   let uu____4214 =
                     FStar_Syntax_Syntax.mk_Tm_uinst proj_tm
                       [FStar_Syntax_Syntax.U_zero]
                      in
                   let uu____4215 =
                     let uu____4216 =
                       let uu____4225 = type_of ea  in
                       FStar_Syntax_Syntax.iarg uu____4225  in
                     let uu____4226 =
                       let uu____4237 = FStar_Syntax_Syntax.as_arg cons_tm
                          in
                       [uu____4237]  in
                     uu____4216 :: uu____4226  in
                   FStar_Syntax_Syntax.mk_Tm_app uu____4214 uu____4215  in
                 uu____4209 FStar_Pervasives_Native.None rng  in
               let shadow_hd = map_shadow shadow_l (proj "hd")  in
               let shadow_tl = map_shadow shadow_l (proj "tl")  in
               let uu____4388 =
                 let uu____4393 =
                   let uu____4394 =
                     let uu____4405 =
                       let uu____4414 =
                         let uu____4415 = embed ea hd1  in
                         uu____4415 rng shadow_hd norm1  in
                       FStar_Syntax_Syntax.as_arg uu____4414  in
                     let uu____4485 =
                       let uu____4496 =
                         let uu____4505 = em tl1 rng shadow_tl norm1  in
                         FStar_Syntax_Syntax.as_arg uu____4505  in
                       [uu____4496]  in
                     uu____4405 :: uu____4485  in
                   t :: uu____4394  in
                 FStar_Syntax_Syntax.mk_Tm_app cons1 uu____4393  in
               uu____4388 FStar_Pervasives_Native.None rng)
       in
    let rec un t0 w norm1 =
      let t = FStar_Syntax_Util.unmeta_safe t0  in
      lazy_unembed printer t t_list_a
        (fun t1  ->
           let uu____4619 = FStar_Syntax_Util.head_and_args t1  in
           match uu____4619 with
           | (hd1,args) ->
               let uu____4666 =
                 let uu____4679 =
                   let uu____4680 = FStar_Syntax_Util.un_uinst hd1  in
                   uu____4680.FStar_Syntax_Syntax.n  in
                 (uu____4679, args)  in
               (match uu____4666 with
                | (FStar_Syntax_Syntax.Tm_fvar fv,uu____4696) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.nil_lid
                    -> FStar_Pervasives_Native.Some []
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(uu____4716,FStar_Pervasives_Native.Some
                       (FStar_Syntax_Syntax.Implicit uu____4717))::(hd2,FStar_Pervasives_Native.None
                                                                    )::
                   (tl1,FStar_Pervasives_Native.None )::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.cons_lid
                    ->
                    let uu____4758 =
                      let uu____4761 = unembed ea hd2  in uu____4761 w norm1
                       in
                    FStar_Util.bind_opt uu____4758
                      (fun hd3  ->
                         let uu____4779 = un tl1 w norm1  in
                         FStar_Util.bind_opt uu____4779
                           (fun tl2  ->
                              FStar_Pervasives_Native.Some (hd3 :: tl2)))
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(hd2,FStar_Pervasives_Native.None )::(tl1,FStar_Pervasives_Native.None
                                                            )::[])
                    when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.cons_lid
                    ->
                    let uu____4829 =
                      let uu____4832 = unembed ea hd2  in uu____4832 w norm1
                       in
                    FStar_Util.bind_opt uu____4829
                      (fun hd3  ->
                         let uu____4850 = un tl1 w norm1  in
                         FStar_Util.bind_opt uu____4850
                           (fun tl2  ->
                              FStar_Pervasives_Native.Some (hd3 :: tl2)))
                | uu____4867 ->
                    (if w
                     then
                       (let uu____4881 =
                          let uu____4886 =
                            let uu____4887 =
                              FStar_Syntax_Print.term_to_string t0  in
                            FStar_Util.format1 "Not an embedded list: %s"
                              uu____4887
                             in
                          (FStar_Errors.Warning_NotEmbedded, uu____4886)  in
                        FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                          uu____4881)
                     else ();
                     FStar_Pervasives_Native.None)))
       in
    let uu____4891 =
      let uu____4892 = type_of ea  in
      FStar_Syntax_Syntax.t_list_of uu____4892  in
    mk_emb_with_printer em un uu____4891 printer
  
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
    match projectee with | Simpl  -> true | uu____4923 -> false
  
let (uu___is_Weak : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Weak  -> true | uu____4929 -> false
  
let (uu___is_HNF : norm_step -> Prims.bool) =
  fun projectee  -> match projectee with | HNF  -> true | uu____4935 -> false 
let (uu___is_Primops : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____4941 -> false
  
let (uu___is_Delta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Delta  -> true | uu____4947 -> false
  
let (uu___is_Zeta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Zeta  -> true | uu____4953 -> false
  
let (uu___is_Iota : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Iota  -> true | uu____4959 -> false
  
let (uu___is_UnfoldOnly : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____4968 -> false
  
let (__proj__UnfoldOnly__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldFully : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldFully _0 -> true | uu____4990 -> false
  
let (__proj__UnfoldFully__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldFully _0 -> _0 
let (uu___is_UnfoldAttr : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____5010 -> false
  
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
    let uu____5021 =
      FStar_Ident.lid_of_str "FStar.Syntax.Embeddings.norm_step"  in
    FStar_Syntax_Util.fvar_const uu____5021  in
  let printer uu____5027 = "norm_step"  in
  let em n1 rng _topt norm1 =
    lazy_embed printer rng t_norm_step1 n1
      (fun uu____5092  ->
         match n1 with
         | Simpl  -> steps_Simpl
         | Weak  -> steps_Weak
         | HNF  -> steps_HNF
         | Primops  -> steps_Primops
         | Delta  -> steps_Delta
         | Zeta  -> steps_Zeta
         | Iota  -> steps_Iota
         | UnfoldOnly l ->
             let uu____5096 =
               let uu____5101 =
                 let uu____5102 =
                   let uu____5111 =
                     let uu____5112 =
                       let uu____5119 = e_list e_string  in
                       embed uu____5119 l  in
                     uu____5112 rng FStar_Pervasives_Native.None norm1  in
                   FStar_Syntax_Syntax.as_arg uu____5111  in
                 [uu____5102]  in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldOnly uu____5101  in
             uu____5096 FStar_Pervasives_Native.None rng
         | UnfoldFully l ->
             let uu____5174 =
               let uu____5179 =
                 let uu____5180 =
                   let uu____5189 =
                     let uu____5190 =
                       let uu____5197 = e_list e_string  in
                       embed uu____5197 l  in
                     uu____5190 rng FStar_Pervasives_Native.None norm1  in
                   FStar_Syntax_Syntax.as_arg uu____5189  in
                 [uu____5180]  in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldFully uu____5179  in
             uu____5174 FStar_Pervasives_Native.None rng
         | UnfoldAttr a ->
             let uu____5250 =
               let uu____5255 =
                 let uu____5256 = FStar_Syntax_Syntax.as_arg a  in
                 [uu____5256]  in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldAttr uu____5255  in
             uu____5250 FStar_Pervasives_Native.None rng)
     in
  let un t0 w norm1 =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    lazy_unembed printer t t_norm_step1
      (fun t1  ->
         let uu____5315 = FStar_Syntax_Util.head_and_args t1  in
         match uu____5315 with
         | (hd1,args) ->
             let uu____5360 =
               let uu____5375 =
                 let uu____5376 = FStar_Syntax_Util.un_uinst hd1  in
                 uu____5376.FStar_Syntax_Syntax.n  in
               (uu____5375, args)  in
             (match uu____5360 with
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
              | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____5526)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldonly
                  ->
                  let uu____5561 =
                    let uu____5566 =
                      let uu____5575 = e_list e_string  in
                      unembed uu____5575 l  in
                    uu____5566 w norm1  in
                  FStar_Util.bind_opt uu____5561
                    (fun ss  ->
                       FStar_All.pipe_left
                         (fun _0_16  -> FStar_Pervasives_Native.Some _0_16)
                         (UnfoldOnly ss))
              | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____5598)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldfully
                  ->
                  let uu____5633 =
                    let uu____5638 =
                      let uu____5647 = e_list e_string  in
                      unembed uu____5647 l  in
                    uu____5638 w norm1  in
                  FStar_Util.bind_opt uu____5633
                    (fun ss  ->
                       FStar_All.pipe_left
                         (fun _0_17  -> FStar_Pervasives_Native.Some _0_17)
                         (UnfoldFully ss))
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____5669::(a,uu____5671)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldattr
                  -> FStar_Pervasives_Native.Some (UnfoldAttr a)
              | uu____5722 ->
                  (if w
                   then
                     (let uu____5738 =
                        let uu____5743 =
                          let uu____5744 =
                            FStar_Syntax_Print.term_to_string t0  in
                          FStar_Util.format1 "Not an embedded norm_step: %s"
                            uu____5744
                           in
                        (FStar_Errors.Warning_NotEmbedded, uu____5743)  in
                      FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                        uu____5738)
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
    | uu____5839 ->
        (if w
         then
           (let uu____5841 =
              let uu____5846 =
                let uu____5847 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded range: %s" uu____5847  in
              (FStar_Errors.Warning_NotEmbedded, uu____5846)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____5841)
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
        let uu____5912 =
          let uu____5919 =
            let uu____5920 =
              let uu____5935 =
                let uu____5944 =
                  let uu____5951 = FStar_Syntax_Syntax.null_bv ea.typ  in
                  (uu____5951, FStar_Pervasives_Native.None)  in
                [uu____5944]  in
              let uu____5966 = FStar_Syntax_Syntax.mk_Total eb.typ  in
              (uu____5935, uu____5966)  in
            FStar_Syntax_Syntax.Tm_arrow uu____5920  in
          FStar_Syntax_Syntax.mk uu____5919  in
        uu____5912 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
      let printer f = "<fun>"  in
      let em f rng shadow_f norm1 =
        let f_wrapped x =
          let shadow_app =
            map_shadow shadow_f
              (fun f1  ->
                 let uu____6132 =
                   let uu____6137 =
                     let uu____6138 = FStar_Syntax_Syntax.as_arg x  in
                     [uu____6138]  in
                   FStar_Syntax_Syntax.mk_Tm_app f1 uu____6137  in
                 uu____6132 FStar_Pervasives_Native.None rng)
             in
          let uu____6165 =
            let uu____6168 =
              let uu____6171 = unembed ea x  in uu____6171 true norm1  in
            FStar_Util.map_opt uu____6168
              (fun x1  ->
                 let uu____6210 =
                   let uu____6217 = f x1  in embed eb uu____6217  in
                 uu____6210 rng shadow_app norm1)
             in
          or_else uu____6165
            (fun uu____6283  ->
               let uu____6284 = force_shadow shadow_app  in
               match uu____6284 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Exn.raise Embedding_failure
               | FStar_Pervasives_Native.Some app ->
                   norm1 (FStar_Util.Inr app))
           in
        lazy_embed (fun uu____6350  -> "<fun>") rng t_arrow f_wrapped
          (fun uu____6355  ->
             let uu____6356 = force_shadow shadow_f  in
             match uu____6356 with
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
                 let uu____6470 = embed ea a  in
                 uu____6470 f1.FStar_Syntax_Syntax.pos
                   FStar_Pervasives_Native.None norm1
                  in
               let b_tm =
                 let uu____6503 =
                   let uu____6508 =
                     let uu____6509 =
                       let uu____6514 =
                         let uu____6515 = FStar_Syntax_Syntax.as_arg a_tm  in
                         [uu____6515]  in
                       FStar_Syntax_Syntax.mk_Tm_app f1 uu____6514  in
                     uu____6509 FStar_Pervasives_Native.None
                       f1.FStar_Syntax_Syntax.pos
                      in
                   FStar_Util.Inr uu____6508  in
                 norm1 uu____6503  in
               let uu____6542 =
                 let uu____6545 = unembed eb b_tm  in uu____6545 w norm1  in
               match uu____6542 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Exn.raise Unembedding_failure
               | FStar_Pervasives_Native.Some b -> b  in
             FStar_Pervasives_Native.Some f_wrapped)
         in
      let tarr =
        let uu____6563 =
          let uu____6570 =
            let uu____6571 =
              let uu____6586 =
                let uu____6595 =
                  let uu____6602 =
                    let uu____6603 = type_of ea  in
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      uu____6603
                     in
                  FStar_Syntax_Syntax.mk_binder uu____6602  in
                [uu____6595]  in
              let uu____6616 =
                let uu____6619 = type_of eb  in
                FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total uu____6619
                 in
              (uu____6586, uu____6616)  in
            FStar_Syntax_Syntax.Tm_arrow uu____6571  in
          FStar_Syntax_Syntax.mk uu____6570  in
        uu____6563 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
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
                let uu____6717 = FStar_List.splitAt n_tvars args  in
                match uu____6717 with
                | (_tvar_args,rest_args) ->
                    let uu____6794 = FStar_List.hd rest_args  in
                    (match uu____6794 with
                     | (x,uu____6814) ->
                         let shadow_app =
                           let uu____6828 =
                             FStar_Common.mk_thunk
                               (fun uu____6837  ->
                                  let uu____6838 =
                                    let uu____6843 =
                                      norm1 (FStar_Util.Inl fv_lid1)  in
                                    FStar_Syntax_Syntax.mk_Tm_app uu____6843
                                      args
                                     in
                                  uu____6838 FStar_Pervasives_Native.None rng)
                              in
                           FStar_Pervasives_Native.Some uu____6828  in
                         let uu____6889 =
                           let uu____6892 =
                             let uu____6895 = unembed ea x  in
                             uu____6895 true norm1  in
                           FStar_Util.map_opt uu____6892
                             (fun x1  ->
                                let uu____6934 =
                                  let uu____6941 = f x1  in
                                  embed eb uu____6941  in
                                uu____6934 rng shadow_app norm1)
                            in
                         (match uu____6889 with
                          | FStar_Pervasives_Native.Some x1 ->
                              FStar_Pervasives_Native.Some x1
                          | FStar_Pervasives_Native.None  ->
                              let uu____6970 = force_shadow shadow_app  in
                              (match uu____6970 with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some app ->
                                   let uu____6976 =
                                     norm1 (FStar_Util.Inr app)  in
                                   FStar_Pervasives_Native.Some uu____6976)))
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
                  let uu____7076 = FStar_List.splitAt n_tvars args  in
                  match uu____7076 with
                  | (_tvar_args,rest_args) ->
                      let uu____7139 = FStar_List.hd rest_args  in
                      (match uu____7139 with
                       | (x,uu____7155) ->
                           let uu____7160 =
                             let uu____7167 = FStar_List.tl rest_args  in
                             FStar_List.hd uu____7167  in
                           (match uu____7160 with
                            | (y,uu____7191) ->
                                let shadow_app =
                                  let uu____7201 =
                                    FStar_Common.mk_thunk
                                      (fun uu____7210  ->
                                         let uu____7211 =
                                           let uu____7216 =
                                             norm1 (FStar_Util.Inl fv_lid1)
                                              in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____7216 args
                                            in
                                         uu____7211
                                           FStar_Pervasives_Native.None rng)
                                     in
                                  FStar_Pervasives_Native.Some uu____7201  in
                                let uu____7262 =
                                  let uu____7265 =
                                    let uu____7268 = unembed ea x  in
                                    uu____7268 true norm1  in
                                  FStar_Util.bind_opt uu____7265
                                    (fun x1  ->
                                       let uu____7284 =
                                         let uu____7287 = unembed eb y  in
                                         uu____7287 true norm1  in
                                       FStar_Util.bind_opt uu____7284
                                         (fun y1  ->
                                            let uu____7303 =
                                              let uu____7304 =
                                                let uu____7311 = f x1 y1  in
                                                embed ec uu____7311  in
                                              uu____7304 rng shadow_app norm1
                                               in
                                            FStar_Pervasives_Native.Some
                                              uu____7303))
                                   in
                                (match uu____7262 with
                                 | FStar_Pervasives_Native.Some x1 ->
                                     FStar_Pervasives_Native.Some x1
                                 | FStar_Pervasives_Native.None  ->
                                     let uu____7340 = force_shadow shadow_app
                                        in
                                     (match uu____7340 with
                                      | FStar_Pervasives_Native.None  ->
                                          FStar_Pervasives_Native.None
                                      | FStar_Pervasives_Native.Some app ->
                                          let uu____7346 =
                                            norm1 (FStar_Util.Inr app)  in
                                          FStar_Pervasives_Native.Some
                                            uu____7346))))
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
                    let uu____7465 = FStar_List.splitAt n_tvars args  in
                    match uu____7465 with
                    | (_tvar_args,rest_args) ->
                        let uu____7528 = FStar_List.hd rest_args  in
                        (match uu____7528 with
                         | (x,uu____7544) ->
                             let uu____7549 =
                               let uu____7556 = FStar_List.tl rest_args  in
                               FStar_List.hd uu____7556  in
                             (match uu____7549 with
                              | (y,uu____7580) ->
                                  let uu____7585 =
                                    let uu____7592 =
                                      let uu____7601 =
                                        FStar_List.tl rest_args  in
                                      FStar_List.tl uu____7601  in
                                    FStar_List.hd uu____7592  in
                                  (match uu____7585 with
                                   | (z,uu____7631) ->
                                       let shadow_app =
                                         let uu____7641 =
                                           FStar_Common.mk_thunk
                                             (fun uu____7650  ->
                                                let uu____7651 =
                                                  let uu____7656 =
                                                    norm1
                                                      (FStar_Util.Inl fv_lid1)
                                                     in
                                                  FStar_Syntax_Syntax.mk_Tm_app
                                                    uu____7656 args
                                                   in
                                                uu____7651
                                                  FStar_Pervasives_Native.None
                                                  rng)
                                            in
                                         FStar_Pervasives_Native.Some
                                           uu____7641
                                          in
                                       let uu____7702 =
                                         let uu____7705 =
                                           let uu____7708 = unembed ea x  in
                                           uu____7708 true norm1  in
                                         FStar_Util.bind_opt uu____7705
                                           (fun x1  ->
                                              let uu____7724 =
                                                let uu____7727 = unembed eb y
                                                   in
                                                uu____7727 true norm1  in
                                              FStar_Util.bind_opt uu____7724
                                                (fun y1  ->
                                                   let uu____7743 =
                                                     let uu____7746 =
                                                       unembed ec z  in
                                                     uu____7746 true norm1
                                                      in
                                                   FStar_Util.bind_opt
                                                     uu____7743
                                                     (fun z1  ->
                                                        let uu____7762 =
                                                          let uu____7763 =
                                                            let uu____7770 =
                                                              f x1 y1 z1  in
                                                            embed ed
                                                              uu____7770
                                                             in
                                                          uu____7763 rng
                                                            shadow_app norm1
                                                           in
                                                        FStar_Pervasives_Native.Some
                                                          uu____7762)))
                                          in
                                       (match uu____7702 with
                                        | FStar_Pervasives_Native.Some x1 ->
                                            FStar_Pervasives_Native.Some x1
                                        | FStar_Pervasives_Native.None  ->
                                            let uu____7799 =
                                              force_shadow shadow_app  in
                                            (match uu____7799 with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some
                                                 app ->
                                                 let uu____7805 =
                                                   norm1 (FStar_Util.Inr app)
                                                    in
                                                 FStar_Pervasives_Native.Some
                                                   uu____7805)))))
                     in
                  f_wrapped
  