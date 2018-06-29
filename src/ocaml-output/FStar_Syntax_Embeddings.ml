open Prims
type norm_cb =
  (FStar_Ident.lid,FStar_Syntax_Syntax.term) FStar_Util.either ->
    FStar_Syntax_Syntax.term
let (id_norm_cb : norm_cb) =
  fun uu___202_13  ->
    match uu___202_13 with
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
type 'a embedding =
  {
  em: 'a -> embed_t ;
  un: FStar_Syntax_Syntax.term -> 'a unembed_t ;
  typ: FStar_Syntax_Syntax.typ }
let __proj__Mkembedding__item__em : 'a . 'a embedding -> 'a -> embed_t =
  fun projectee  ->
    match projectee with
    | { em = __fname__em; un = __fname__un; typ = __fname__typ;_} ->
        __fname__em
  
let __proj__Mkembedding__item__un :
  'a . 'a embedding -> FStar_Syntax_Syntax.term -> 'a unembed_t =
  fun projectee  ->
    match projectee with
    | { em = __fname__em; un = __fname__un; typ = __fname__typ;_} ->
        __fname__un
  
let __proj__Mkembedding__item__typ :
  'a . 'a embedding -> FStar_Syntax_Syntax.typ =
  fun projectee  ->
    match projectee with
    | { em = __fname__em; un = __fname__un; typ = __fname__typ;_} ->
        __fname__typ
  
let mk_emb :
  'a .
    'a raw_embedder ->
      'a raw_unembedder -> FStar_Syntax_Syntax.typ -> 'a embedding
  = fun em  -> fun un  -> fun typ  -> { em; un; typ } 
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
    fun t  -> fun n1  -> let uu____1002 = unembed e t  in uu____1002 true n1
  
let try_unembed :
  'a .
    'a embedding ->
      FStar_Syntax_Syntax.term ->
        norm_cb -> 'a FStar_Pervasives_Native.option
  =
  fun e  ->
    fun t  -> fun n1  -> let uu____1049 = unembed e t  in uu____1049 false n1
  
let type_of : 'a . 'a embedding -> FStar_Syntax_Syntax.typ = fun e  -> e.typ 
let lazy_embed :
  'a .
    FStar_Range.range ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        'a ->
          (unit -> FStar_Syntax_Syntax.term) ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun rng  ->
    fun ta  ->
      fun x  ->
        fun f  ->
          let uu____1118 =
            let uu____1125 =
              let uu____1126 =
                let uu____1127 = FStar_Dyn.mkdyn x  in
                let uu____1128 =
                  let uu____1129 =
                    let uu____1140 = FStar_Common.mk_thunk f  in
                    (ta, uu____1140)  in
                  FStar_Syntax_Syntax.Lazy_embedding uu____1129  in
                {
                  FStar_Syntax_Syntax.blob = uu____1127;
                  FStar_Syntax_Syntax.lkind = uu____1128;
                  FStar_Syntax_Syntax.ltyp = FStar_Syntax_Syntax.tun;
                  FStar_Syntax_Syntax.rng = rng
                }  in
              FStar_Syntax_Syntax.Tm_lazy uu____1126  in
            FStar_Syntax_Syntax.mk uu____1125  in
          uu____1118 FStar_Pervasives_Native.None rng
  
let lazy_unembed :
  'a .
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term -> 'a FStar_Pervasives_Native.option) ->
          'a FStar_Pervasives_Native.option
  =
  fun x  ->
    fun ta  ->
      fun f  ->
        let x1 = FStar_Syntax_Subst.compress x  in
        match x1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_lazy
            { FStar_Syntax_Syntax.blob = b;
              FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
                (tb,uu____1236);
              FStar_Syntax_Syntax.ltyp = uu____1237;
              FStar_Syntax_Syntax.rng = uu____1238;_}
            ->
            ((let uu____1254 = FStar_Syntax_Print.term_to_string tb  in
              let uu____1255 = FStar_Syntax_Print.term_to_string ta  in
              FStar_Util.print2 "Unembedding a %s as a %s\n" uu____1254
                uu____1255);
             (let uu____1256 = FStar_Dyn.undyn b  in
              FStar_Pervasives_Native.Some uu____1256))
        | uu____1257 -> f x1
  
let (e_any : FStar_Syntax_Syntax.term embedding) =
  let em t _r _topt _norm = t  in
  let un t _w _n = FStar_Pervasives_Native.Some t  in
  let typ = FStar_Syntax_Syntax.t_term  in mk_emb em un typ 
let (mk_any_emb :
  FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term embedding) =
  fun typ  -> { em = (e_any.em); un = (e_any.un); typ } 
let (e_unit : unit embedding) =
  let em u rng _topt _norm =
    let uu___203_1418 = FStar_Syntax_Util.exp_unit  in
    {
      FStar_Syntax_Syntax.n = (uu___203_1418.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___203_1418.FStar_Syntax_Syntax.vars)
    }  in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unascribe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit ) ->
        FStar_Pervasives_Native.Some ()
    | uu____1446 ->
        (if w
         then
           (let uu____1448 =
              let uu____1453 =
                let uu____1454 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded unit: %s" uu____1454  in
              (FStar_Errors.Warning_NotEmbedded, uu____1453)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____1448)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb em un FStar_Syntax_Syntax.t_unit 
let (e_bool : Prims.bool embedding) =
  let em b rng _topt _norm =
    let t =
      if b
      then FStar_Syntax_Util.exp_true_bool
      else FStar_Syntax_Util.exp_false_bool  in
    let uu___204_1527 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___204_1527.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___204_1527.FStar_Syntax_Syntax.vars)
    }  in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) ->
        FStar_Pervasives_Native.Some b
    | uu____1558 ->
        (if w
         then
           (let uu____1560 =
              let uu____1565 =
                let uu____1566 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded bool: %s" uu____1566  in
              (FStar_Errors.Warning_NotEmbedded, uu____1565)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____1560)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb em un FStar_Syntax_Syntax.t_bool 
let (e_char : FStar_Char.char embedding) =
  let em c rng _topt _norm =
    let t = FStar_Syntax_Util.exp_char c  in
    let uu___205_1637 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___205_1637.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___205_1637.FStar_Syntax_Syntax.vars)
    }  in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c) ->
        FStar_Pervasives_Native.Some c
    | uu____1671 ->
        (if w
         then
           (let uu____1673 =
              let uu____1678 =
                let uu____1679 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded char: %s" uu____1679  in
              (FStar_Errors.Warning_NotEmbedded, uu____1678)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____1673)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb em un FStar_Syntax_Syntax.t_char 
let (e_int : FStar_BigInt.t embedding) =
  let t_int1 = FStar_Syntax_Util.fvar_const FStar_Parser_Const.int_lid  in
  let em i rng _topt _norm =
    lazy_embed rng t_int1 i
      (fun uu____1751  ->
         let uu____1752 = FStar_BigInt.string_of_big_int i  in
         FStar_Syntax_Util.exp_int uu____1752)
     in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    lazy_unembed t t_int1
      (fun t1  ->
         match t1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
             (s,uu____1786)) ->
             let uu____1799 = FStar_BigInt.big_int_of_string s  in
             FStar_Pervasives_Native.Some uu____1799
         | uu____1800 ->
             (if w
              then
                (let uu____1802 =
                   let uu____1807 =
                     let uu____1808 = FStar_Syntax_Print.term_to_string t0
                        in
                     FStar_Util.format1 "Not an embedded int: %s" uu____1808
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____1807)  in
                 FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____1802)
              else ();
              FStar_Pervasives_Native.None))
     in
  mk_emb em un FStar_Syntax_Syntax.t_int 
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
        (s,uu____1903)) -> FStar_Pervasives_Native.Some s
    | uu____1904 ->
        (if w
         then
           (let uu____1906 =
              let uu____1911 =
                let uu____1912 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded string: %s" uu____1912
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____1911)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____1906)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb em un FStar_Syntax_Syntax.t_string 
let e_option :
  'a . 'a embedding -> 'a FStar_Pervasives_Native.option embedding =
  fun ea  ->
    let t_option_a =
      let t_opt = FStar_Syntax_Util.fvar_const FStar_Parser_Const.option_lid
         in
      let uu____1936 =
        let uu____1941 =
          let uu____1942 = FStar_Syntax_Syntax.as_arg ea.typ  in [uu____1942]
           in
        FStar_Syntax_Syntax.mk_Tm_app t_opt uu____1941  in
      uu____1936 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
    let em o rng topt norm1 =
      lazy_embed rng t_option_a o
        (fun uu____2042  ->
           match o with
           | FStar_Pervasives_Native.None  ->
               let uu____2043 =
                 let uu____2048 =
                   let uu____2049 =
                     FStar_Syntax_Syntax.tdataconstr
                       FStar_Parser_Const.none_lid
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____2049
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 let uu____2050 =
                   let uu____2051 =
                     let uu____2060 = type_of ea  in
                     FStar_Syntax_Syntax.iarg uu____2060  in
                   [uu____2051]  in
                 FStar_Syntax_Syntax.mk_Tm_app uu____2048 uu____2050  in
               uu____2043 FStar_Pervasives_Native.None rng
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
                        let uu____2149 =
                          FStar_Syntax_Syntax.lid_as_fv some_v
                            FStar_Syntax_Syntax.delta_equational
                            FStar_Pervasives_Native.None
                           in
                        FStar_Syntax_Syntax.fv_to_tm uu____2149  in
                      let uu____2150 =
                        let uu____2155 =
                          FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm
                            [FStar_Syntax_Syntax.U_zero]
                           in
                        let uu____2156 =
                          let uu____2157 =
                            let uu____2166 = type_of ea  in
                            FStar_Syntax_Syntax.iarg uu____2166  in
                          let uu____2167 =
                            let uu____2178 = FStar_Syntax_Syntax.as_arg t  in
                            [uu____2178]  in
                          uu____2157 :: uu____2167  in
                        FStar_Syntax_Syntax.mk_Tm_app uu____2155 uu____2156
                         in
                      uu____2150 FStar_Pervasives_Native.None rng)
                  in
               let uu____2213 =
                 let uu____2218 =
                   let uu____2219 =
                     FStar_Syntax_Syntax.tdataconstr
                       FStar_Parser_Const.some_lid
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____2219
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 let uu____2220 =
                   let uu____2221 =
                     let uu____2230 = type_of ea  in
                     FStar_Syntax_Syntax.iarg uu____2230  in
                   let uu____2231 =
                     let uu____2242 =
                       let uu____2251 =
                         let uu____2252 = embed ea a  in
                         uu____2252 rng shadow_a norm1  in
                       FStar_Syntax_Syntax.as_arg uu____2251  in
                     [uu____2242]  in
                   uu____2221 :: uu____2231  in
                 FStar_Syntax_Syntax.mk_Tm_app uu____2218 uu____2220  in
               uu____2213 FStar_Pervasives_Native.None rng)
       in
    let un t0 w norm1 =
      let t = FStar_Syntax_Util.unmeta_safe t0  in
      lazy_unembed t t_option_a
        (fun t1  ->
           let uu____2387 = FStar_Syntax_Util.head_and_args t1  in
           match uu____2387 with
           | (hd1,args) ->
               let uu____2434 =
                 let uu____2449 =
                   let uu____2450 = FStar_Syntax_Util.un_uinst hd1  in
                   uu____2450.FStar_Syntax_Syntax.n  in
                 (uu____2449, args)  in
               (match uu____2434 with
                | (FStar_Syntax_Syntax.Tm_fvar fv,uu____2468) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.none_lid
                    ->
                    FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,uu____2492::(a,uu____2494)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.some_lid
                    ->
                    let uu____2545 =
                      let uu____2548 = unembed ea a  in uu____2548 w norm1
                       in
                    FStar_Util.bind_opt uu____2545
                      (fun a1  ->
                         FStar_Pervasives_Native.Some
                           (FStar_Pervasives_Native.Some a1))
                | uu____2567 ->
                    (if w
                     then
                       (let uu____2583 =
                          let uu____2588 =
                            let uu____2589 =
                              FStar_Syntax_Print.term_to_string t0  in
                            FStar_Util.format1 "Not an embedded option: %s"
                              uu____2589
                             in
                          (FStar_Errors.Warning_NotEmbedded, uu____2588)  in
                        FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                          uu____2583)
                     else ();
                     FStar_Pervasives_Native.None)))
       in
    let uu____2593 =
      let uu____2594 = type_of ea  in
      FStar_Syntax_Syntax.t_option_of uu____2594  in
    mk_emb em un uu____2593
  
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
        let uu____2635 =
          let uu____2640 =
            let uu____2641 = FStar_Syntax_Syntax.as_arg ea.typ  in
            let uu____2650 =
              let uu____2661 = FStar_Syntax_Syntax.as_arg eb.typ  in
              [uu____2661]  in
            uu____2641 :: uu____2650  in
          FStar_Syntax_Syntax.mk_Tm_app t_tup2 uu____2640  in
        uu____2635 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
      let em x rng topt norm1 =
        lazy_embed rng t_pair_a_b x
          (fun uu____2778  ->
             let proj i ab =
               let uu____2792 =
                 let uu____2797 =
                   FStar_Parser_Const.mk_tuple_data_lid (Prims.parse_int "2")
                     rng
                    in
                 let uu____2798 =
                   FStar_Syntax_Syntax.null_bv FStar_Syntax_Syntax.tun  in
                 FStar_Syntax_Util.mk_field_projector_name uu____2797
                   uu____2798 i
                  in
               match uu____2792 with
               | (proj_1,uu____2802) ->
                   let proj_1_tm =
                     let uu____2804 =
                       FStar_Syntax_Syntax.lid_as_fv proj_1
                         FStar_Syntax_Syntax.delta_equational
                         FStar_Pervasives_Native.None
                        in
                     FStar_Syntax_Syntax.fv_to_tm uu____2804  in
                   let uu____2805 =
                     let uu____2810 =
                       FStar_Syntax_Syntax.mk_Tm_uinst proj_1_tm
                         [FStar_Syntax_Syntax.U_zero]
                        in
                     let uu____2811 =
                       let uu____2812 =
                         let uu____2821 = type_of ea  in
                         FStar_Syntax_Syntax.iarg uu____2821  in
                       let uu____2822 =
                         let uu____2833 =
                           let uu____2842 = type_of eb  in
                           FStar_Syntax_Syntax.iarg uu____2842  in
                         let uu____2843 =
                           let uu____2854 = FStar_Syntax_Syntax.as_arg ab  in
                           [uu____2854]  in
                         uu____2833 :: uu____2843  in
                       uu____2812 :: uu____2822  in
                     FStar_Syntax_Syntax.mk_Tm_app uu____2810 uu____2811  in
                   uu____2805 FStar_Pervasives_Native.None rng
                in
             let shadow_a = map_shadow topt (proj (Prims.parse_int "1"))  in
             let shadow_b = map_shadow topt (proj (Prims.parse_int "2"))  in
             let uu____3013 =
               let uu____3018 =
                 let uu____3019 =
                   FStar_Syntax_Syntax.tdataconstr
                     FStar_Parser_Const.lid_Mktuple2
                    in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu____3019
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                  in
               let uu____3020 =
                 let uu____3021 =
                   let uu____3030 = type_of ea  in
                   FStar_Syntax_Syntax.iarg uu____3030  in
                 let uu____3031 =
                   let uu____3042 =
                     let uu____3051 = type_of eb  in
                     FStar_Syntax_Syntax.iarg uu____3051  in
                   let uu____3052 =
                     let uu____3063 =
                       let uu____3072 =
                         let uu____3073 =
                           embed ea (FStar_Pervasives_Native.fst x)  in
                         uu____3073 rng shadow_a norm1  in
                       FStar_Syntax_Syntax.as_arg uu____3072  in
                     let uu____3143 =
                       let uu____3154 =
                         let uu____3163 =
                           let uu____3164 =
                             embed eb (FStar_Pervasives_Native.snd x)  in
                           uu____3164 rng shadow_b norm1  in
                         FStar_Syntax_Syntax.as_arg uu____3163  in
                       [uu____3154]  in
                     uu____3063 :: uu____3143  in
                   uu____3042 :: uu____3052  in
                 uu____3021 :: uu____3031  in
               FStar_Syntax_Syntax.mk_Tm_app uu____3018 uu____3020  in
             uu____3013 FStar_Pervasives_Native.None rng)
         in
      let un t0 w norm1 =
        let t = FStar_Syntax_Util.unmeta_safe t0  in
        lazy_unembed t t_pair_a_b
          (fun t1  ->
             let uu____3327 = FStar_Syntax_Util.head_and_args t1  in
             match uu____3327 with
             | (hd1,args) ->
                 let uu____3376 =
                   let uu____3389 =
                     let uu____3390 = FStar_Syntax_Util.un_uinst hd1  in
                     uu____3390.FStar_Syntax_Syntax.n  in
                   (uu____3389, args)  in
                 (match uu____3376 with
                  | (FStar_Syntax_Syntax.Tm_fvar
                     fv,uu____3408::uu____3409::(a,uu____3411)::(b,uu____3413)::[])
                      when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.lid_Mktuple2
                      ->
                      let uu____3472 =
                        let uu____3475 = unembed ea a  in uu____3475 w norm1
                         in
                      FStar_Util.bind_opt uu____3472
                        (fun a1  ->
                           let uu____3495 =
                             let uu____3498 = unembed eb b  in
                             uu____3498 w norm1  in
                           FStar_Util.bind_opt uu____3495
                             (fun b1  ->
                                FStar_Pervasives_Native.Some (a1, b1)))
                  | uu____3521 ->
                      (if w
                       then
                         (let uu____3535 =
                            let uu____3540 =
                              let uu____3541 =
                                FStar_Syntax_Print.term_to_string t0  in
                              FStar_Util.format1 "Not an embedded pair: %s"
                                uu____3541
                               in
                            (FStar_Errors.Warning_NotEmbedded, uu____3540)
                             in
                          FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                            uu____3535)
                       else ();
                       FStar_Pervasives_Native.None)))
         in
      let uu____3547 =
        let uu____3548 = type_of ea  in
        let uu____3549 = type_of eb  in
        FStar_Syntax_Syntax.t_tuple2_of uu____3548 uu____3549  in
      mk_emb em un uu____3547
  
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea  ->
    let t_list_a =
      let t_list = FStar_Syntax_Util.fvar_const FStar_Parser_Const.list_lid
         in
      let uu____3576 =
        let uu____3581 =
          let uu____3582 = FStar_Syntax_Syntax.as_arg ea.typ  in [uu____3582]
           in
        FStar_Syntax_Syntax.mk_Tm_app t_list uu____3581  in
      uu____3576 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
    let rec em l rng shadow_l norm1 =
      lazy_embed rng t_list_a l
        (fun uu____3683  ->
           let t =
             let uu____3685 = type_of ea  in
             FStar_Syntax_Syntax.iarg uu____3685  in
           match l with
           | [] ->
               let uu____3686 =
                 let uu____3691 =
                   let uu____3692 =
                     FStar_Syntax_Syntax.tdataconstr
                       FStar_Parser_Const.nil_lid
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____3692
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 FStar_Syntax_Syntax.mk_Tm_app uu____3691 [t]  in
               uu____3686 FStar_Pervasives_Native.None rng
           | hd1::tl1 ->
               let cons1 =
                 let uu____3716 =
                   FStar_Syntax_Syntax.tdataconstr
                     FStar_Parser_Const.cons_lid
                    in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu____3716
                   [FStar_Syntax_Syntax.U_zero]
                  in
               let proj f cons_tm =
                 let fid = FStar_Ident.mk_ident (f, rng)  in
                 let proj =
                   FStar_Syntax_Util.mk_field_projector_name_from_ident
                     FStar_Parser_Const.cons_lid fid
                    in
                 let proj_tm =
                   let uu____3733 =
                     FStar_Syntax_Syntax.lid_as_fv proj
                       FStar_Syntax_Syntax.delta_equational
                       FStar_Pervasives_Native.None
                      in
                   FStar_Syntax_Syntax.fv_to_tm uu____3733  in
                 let uu____3734 =
                   let uu____3739 =
                     FStar_Syntax_Syntax.mk_Tm_uinst proj_tm
                       [FStar_Syntax_Syntax.U_zero]
                      in
                   let uu____3740 =
                     let uu____3741 =
                       let uu____3750 = type_of ea  in
                       FStar_Syntax_Syntax.iarg uu____3750  in
                     let uu____3751 =
                       let uu____3762 = FStar_Syntax_Syntax.as_arg cons_tm
                          in
                       [uu____3762]  in
                     uu____3741 :: uu____3751  in
                   FStar_Syntax_Syntax.mk_Tm_app uu____3739 uu____3740  in
                 uu____3734 FStar_Pervasives_Native.None rng  in
               let shadow_hd = map_shadow shadow_l (proj "hd")  in
               let shadow_tl = map_shadow shadow_l (proj "tl")  in
               let uu____3913 =
                 let uu____3918 =
                   let uu____3919 =
                     let uu____3930 =
                       let uu____3939 =
                         let uu____3940 = embed ea hd1  in
                         uu____3940 rng shadow_hd norm1  in
                       FStar_Syntax_Syntax.as_arg uu____3939  in
                     let uu____4010 =
                       let uu____4021 =
                         let uu____4030 = em tl1 rng shadow_tl norm1  in
                         FStar_Syntax_Syntax.as_arg uu____4030  in
                       [uu____4021]  in
                     uu____3930 :: uu____4010  in
                   t :: uu____3919  in
                 FStar_Syntax_Syntax.mk_Tm_app cons1 uu____3918  in
               uu____3913 FStar_Pervasives_Native.None rng)
       in
    let rec un t0 w norm1 =
      let t = FStar_Syntax_Util.unmeta_safe t0  in
      lazy_unembed t t_list_a
        (fun t1  ->
           let uu____4144 = FStar_Syntax_Util.head_and_args t1  in
           match uu____4144 with
           | (hd1,args) ->
               let uu____4191 =
                 let uu____4204 =
                   let uu____4205 = FStar_Syntax_Util.un_uinst hd1  in
                   uu____4205.FStar_Syntax_Syntax.n  in
                 (uu____4204, args)  in
               (match uu____4191 with
                | (FStar_Syntax_Syntax.Tm_fvar fv,uu____4221) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.nil_lid
                    -> FStar_Pervasives_Native.Some []
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(uu____4241,FStar_Pervasives_Native.Some
                       (FStar_Syntax_Syntax.Implicit uu____4242))::(hd2,FStar_Pervasives_Native.None
                                                                    )::
                   (tl1,FStar_Pervasives_Native.None )::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.cons_lid
                    ->
                    let uu____4283 =
                      let uu____4286 = unembed ea hd2  in uu____4286 w norm1
                       in
                    FStar_Util.bind_opt uu____4283
                      (fun hd3  ->
                         let uu____4304 = un tl1 w norm1  in
                         FStar_Util.bind_opt uu____4304
                           (fun tl2  ->
                              FStar_Pervasives_Native.Some (hd3 :: tl2)))
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(hd2,FStar_Pervasives_Native.None )::(tl1,FStar_Pervasives_Native.None
                                                            )::[])
                    when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.cons_lid
                    ->
                    let uu____4354 =
                      let uu____4357 = unembed ea hd2  in uu____4357 w norm1
                       in
                    FStar_Util.bind_opt uu____4354
                      (fun hd3  ->
                         let uu____4375 = un tl1 w norm1  in
                         FStar_Util.bind_opt uu____4375
                           (fun tl2  ->
                              FStar_Pervasives_Native.Some (hd3 :: tl2)))
                | uu____4392 ->
                    (if w
                     then
                       (let uu____4406 =
                          let uu____4411 =
                            let uu____4412 =
                              FStar_Syntax_Print.term_to_string t0  in
                            FStar_Util.format1 "Not an embedded list: %s"
                              uu____4412
                             in
                          (FStar_Errors.Warning_NotEmbedded, uu____4411)  in
                        FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                          uu____4406)
                     else ();
                     FStar_Pervasives_Native.None)))
       in
    let uu____4416 =
      let uu____4417 = type_of ea  in
      FStar_Syntax_Syntax.t_list_of uu____4417  in
    mk_emb em un uu____4416
  
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
    match projectee with | Simpl  -> true | uu____4448 -> false
  
let (uu___is_Weak : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Weak  -> true | uu____4454 -> false
  
let (uu___is_HNF : norm_step -> Prims.bool) =
  fun projectee  -> match projectee with | HNF  -> true | uu____4460 -> false 
let (uu___is_Primops : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____4466 -> false
  
let (uu___is_Delta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Delta  -> true | uu____4472 -> false
  
let (uu___is_Zeta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Zeta  -> true | uu____4478 -> false
  
let (uu___is_Iota : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Iota  -> true | uu____4484 -> false
  
let (uu___is_UnfoldOnly : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____4493 -> false
  
let (__proj__UnfoldOnly__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldFully : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldFully _0 -> true | uu____4515 -> false
  
let (__proj__UnfoldFully__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldFully _0 -> _0 
let (uu___is_UnfoldAttr : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____4535 -> false
  
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
    let uu____4546 =
      FStar_Ident.lid_of_str "FStar.Syntax.Embeddings.norm_step"  in
    FStar_Syntax_Util.fvar_const uu____4546  in
  let em n1 rng _topt norm1 =
    lazy_embed rng t_norm_step1 n1
      (fun uu____4611  ->
         match n1 with
         | Simpl  -> steps_Simpl
         | Weak  -> steps_Weak
         | HNF  -> steps_HNF
         | Primops  -> steps_Primops
         | Delta  -> steps_Delta
         | Zeta  -> steps_Zeta
         | Iota  -> steps_Iota
         | UnfoldOnly l ->
             let uu____4615 =
               let uu____4620 =
                 let uu____4621 =
                   let uu____4630 =
                     let uu____4631 =
                       let uu____4638 = e_list e_string  in
                       embed uu____4638 l  in
                     uu____4631 rng FStar_Pervasives_Native.None norm1  in
                   FStar_Syntax_Syntax.as_arg uu____4630  in
                 [uu____4621]  in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldOnly uu____4620  in
             uu____4615 FStar_Pervasives_Native.None rng
         | UnfoldFully l ->
             let uu____4693 =
               let uu____4698 =
                 let uu____4699 =
                   let uu____4708 =
                     let uu____4709 =
                       let uu____4716 = e_list e_string  in
                       embed uu____4716 l  in
                     uu____4709 rng FStar_Pervasives_Native.None norm1  in
                   FStar_Syntax_Syntax.as_arg uu____4708  in
                 [uu____4699]  in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldFully uu____4698  in
             uu____4693 FStar_Pervasives_Native.None rng
         | UnfoldAttr a ->
             let uu____4769 =
               let uu____4774 =
                 let uu____4775 = FStar_Syntax_Syntax.as_arg a  in
                 [uu____4775]  in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldAttr uu____4774  in
             uu____4769 FStar_Pervasives_Native.None rng)
     in
  let un t0 w norm1 =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    lazy_unembed t t_norm_step1
      (fun t1  ->
         let uu____4834 = FStar_Syntax_Util.head_and_args t1  in
         match uu____4834 with
         | (hd1,args) ->
             let uu____4879 =
               let uu____4894 =
                 let uu____4895 = FStar_Syntax_Util.un_uinst hd1  in
                 uu____4895.FStar_Syntax_Syntax.n  in
               (uu____4894, args)  in
             (match uu____4879 with
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
              | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____5045)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldonly
                  ->
                  let uu____5080 =
                    let uu____5085 =
                      let uu____5094 = e_list e_string  in
                      unembed uu____5094 l  in
                    uu____5085 w norm1  in
                  FStar_Util.bind_opt uu____5080
                    (fun ss  ->
                       FStar_All.pipe_left
                         (fun _0_16  -> FStar_Pervasives_Native.Some _0_16)
                         (UnfoldOnly ss))
              | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____5117)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldfully
                  ->
                  let uu____5152 =
                    let uu____5157 =
                      let uu____5166 = e_list e_string  in
                      unembed uu____5166 l  in
                    uu____5157 w norm1  in
                  FStar_Util.bind_opt uu____5152
                    (fun ss  ->
                       FStar_All.pipe_left
                         (fun _0_17  -> FStar_Pervasives_Native.Some _0_17)
                         (UnfoldFully ss))
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____5188::(a,uu____5190)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldattr
                  -> FStar_Pervasives_Native.Some (UnfoldAttr a)
              | uu____5241 ->
                  (if w
                   then
                     (let uu____5257 =
                        let uu____5262 =
                          let uu____5263 =
                            FStar_Syntax_Print.term_to_string t0  in
                          FStar_Util.format1 "Not an embedded norm_step: %s"
                            uu____5263
                           in
                        (FStar_Errors.Warning_NotEmbedded, uu____5262)  in
                      FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                        uu____5257)
                   else ();
                   FStar_Pervasives_Native.None)))
     in
  mk_emb em un FStar_Syntax_Syntax.t_norm_step 
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
    | uu____5358 ->
        (if w
         then
           (let uu____5360 =
              let uu____5365 =
                let uu____5366 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded range: %s" uu____5366  in
              (FStar_Errors.Warning_NotEmbedded, uu____5365)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____5360)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb em un FStar_Syntax_Syntax.t_range 
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
        let uu____5431 =
          let uu____5438 =
            let uu____5439 =
              let uu____5454 =
                let uu____5463 =
                  let uu____5470 = FStar_Syntax_Syntax.null_bv ea.typ  in
                  (uu____5470, FStar_Pervasives_Native.None)  in
                [uu____5463]  in
              let uu____5485 = FStar_Syntax_Syntax.mk_Total eb.typ  in
              (uu____5454, uu____5485)  in
            FStar_Syntax_Syntax.Tm_arrow uu____5439  in
          FStar_Syntax_Syntax.mk uu____5438  in
        uu____5431 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
      let em f rng shadow_f norm1 =
        let f_wrapped x =
          let shadow_app =
            map_shadow shadow_f
              (fun f1  ->
                 let uu____5640 =
                   let uu____5645 =
                     let uu____5646 = FStar_Syntax_Syntax.as_arg x  in
                     [uu____5646]  in
                   FStar_Syntax_Syntax.mk_Tm_app f1 uu____5645  in
                 uu____5640 FStar_Pervasives_Native.None rng)
             in
          let uu____5673 =
            let uu____5676 =
              let uu____5679 = unembed ea x  in uu____5679 true norm1  in
            FStar_Util.map_opt uu____5676
              (fun x1  ->
                 let uu____5718 =
                   let uu____5725 = f x1  in embed eb uu____5725  in
                 uu____5718 rng shadow_app norm1)
             in
          or_else uu____5673
            (fun uu____5791  ->
               let uu____5792 = force_shadow shadow_app  in
               match uu____5792 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Exn.raise Embedding_failure
               | FStar_Pervasives_Native.Some app ->
                   norm1 (FStar_Util.Inr app))
           in
        lazy_embed rng t_arrow f_wrapped
          (fun uu____5859  ->
             let uu____5860 = force_shadow shadow_f  in
             match uu____5860 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Exn.raise Embedding_failure
             | FStar_Pervasives_Native.Some repr_f ->
                 norm1 (FStar_Util.Inr repr_f))
         in
      let un f w norm1 =
        lazy_unembed f t_arrow
          (fun f1  ->
             let f_wrapped a =
               let a_tm =
                 let uu____5974 = embed ea a  in
                 uu____5974 f1.FStar_Syntax_Syntax.pos
                   FStar_Pervasives_Native.None norm1
                  in
               let b_tm =
                 let uu____6007 =
                   let uu____6012 =
                     let uu____6013 =
                       let uu____6018 =
                         let uu____6019 = FStar_Syntax_Syntax.as_arg a_tm  in
                         [uu____6019]  in
                       FStar_Syntax_Syntax.mk_Tm_app f1 uu____6018  in
                     uu____6013 FStar_Pervasives_Native.None
                       f1.FStar_Syntax_Syntax.pos
                      in
                   FStar_Util.Inr uu____6012  in
                 norm1 uu____6007  in
               let uu____6046 =
                 let uu____6049 = unembed eb b_tm  in uu____6049 w norm1  in
               match uu____6046 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Exn.raise Unembedding_failure
               | FStar_Pervasives_Native.Some b -> b  in
             FStar_Pervasives_Native.Some f_wrapped)
         in
      let tarr =
        let uu____6067 =
          let uu____6074 =
            let uu____6075 =
              let uu____6090 =
                let uu____6099 =
                  let uu____6106 =
                    let uu____6107 = type_of ea  in
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      uu____6107
                     in
                  FStar_Syntax_Syntax.mk_binder uu____6106  in
                [uu____6099]  in
              let uu____6120 =
                let uu____6123 = type_of eb  in
                FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total uu____6123
                 in
              (uu____6090, uu____6120)  in
            FStar_Syntax_Syntax.Tm_arrow uu____6075  in
          FStar_Syntax_Syntax.mk uu____6074  in
        uu____6067 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
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
                let uu____6221 = FStar_List.splitAt n_tvars args  in
                match uu____6221 with
                | (_tvar_args,rest_args) ->
                    let uu____6298 = FStar_List.hd rest_args  in
                    (match uu____6298 with
                     | (x,uu____6318) ->
                         let shadow_app =
                           let uu____6332 =
                             FStar_Common.mk_thunk
                               (fun uu____6341  ->
                                  let uu____6342 =
                                    let uu____6347 =
                                      norm1 (FStar_Util.Inl fv_lid1)  in
                                    FStar_Syntax_Syntax.mk_Tm_app uu____6347
                                      args
                                     in
                                  uu____6342 FStar_Pervasives_Native.None rng)
                              in
                           FStar_Pervasives_Native.Some uu____6332  in
                         let uu____6393 =
                           let uu____6396 =
                             let uu____6399 = unembed ea x  in
                             uu____6399 true norm1  in
                           FStar_Util.map_opt uu____6396
                             (fun x1  ->
                                let uu____6438 =
                                  let uu____6445 = f x1  in
                                  embed eb uu____6445  in
                                uu____6438 rng shadow_app norm1)
                            in
                         (match uu____6393 with
                          | FStar_Pervasives_Native.Some x1 ->
                              FStar_Pervasives_Native.Some x1
                          | FStar_Pervasives_Native.None  ->
                              let uu____6474 = force_shadow shadow_app  in
                              (match uu____6474 with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some app ->
                                   let uu____6480 =
                                     norm1 (FStar_Util.Inr app)  in
                                   FStar_Pervasives_Native.Some uu____6480)))
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
                  let uu____6580 = FStar_List.splitAt n_tvars args  in
                  match uu____6580 with
                  | (_tvar_args,rest_args) ->
                      let uu____6643 = FStar_List.hd rest_args  in
                      (match uu____6643 with
                       | (x,uu____6659) ->
                           let uu____6664 =
                             let uu____6671 = FStar_List.tl rest_args  in
                             FStar_List.hd uu____6671  in
                           (match uu____6664 with
                            | (y,uu____6695) ->
                                let shadow_app =
                                  let uu____6705 =
                                    FStar_Common.mk_thunk
                                      (fun uu____6714  ->
                                         let uu____6715 =
                                           let uu____6720 =
                                             norm1 (FStar_Util.Inl fv_lid1)
                                              in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____6720 args
                                            in
                                         uu____6715
                                           FStar_Pervasives_Native.None rng)
                                     in
                                  FStar_Pervasives_Native.Some uu____6705  in
                                let uu____6766 =
                                  let uu____6769 =
                                    let uu____6772 = unembed ea x  in
                                    uu____6772 true norm1  in
                                  FStar_Util.bind_opt uu____6769
                                    (fun x1  ->
                                       let uu____6788 =
                                         let uu____6791 = unembed eb y  in
                                         uu____6791 true norm1  in
                                       FStar_Util.bind_opt uu____6788
                                         (fun y1  ->
                                            let uu____6807 =
                                              let uu____6808 =
                                                let uu____6815 = f x1 y1  in
                                                embed ec uu____6815  in
                                              uu____6808 rng shadow_app norm1
                                               in
                                            FStar_Pervasives_Native.Some
                                              uu____6807))
                                   in
                                (match uu____6766 with
                                 | FStar_Pervasives_Native.Some x1 ->
                                     FStar_Pervasives_Native.Some x1
                                 | FStar_Pervasives_Native.None  ->
                                     let uu____6844 = force_shadow shadow_app
                                        in
                                     (match uu____6844 with
                                      | FStar_Pervasives_Native.None  ->
                                          FStar_Pervasives_Native.None
                                      | FStar_Pervasives_Native.Some app ->
                                          let uu____6850 =
                                            norm1 (FStar_Util.Inr app)  in
                                          FStar_Pervasives_Native.Some
                                            uu____6850))))
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
                    let uu____6969 = FStar_List.splitAt n_tvars args  in
                    match uu____6969 with
                    | (_tvar_args,rest_args) ->
                        let uu____7032 = FStar_List.hd rest_args  in
                        (match uu____7032 with
                         | (x,uu____7048) ->
                             let uu____7053 =
                               let uu____7060 = FStar_List.tl rest_args  in
                               FStar_List.hd uu____7060  in
                             (match uu____7053 with
                              | (y,uu____7084) ->
                                  let uu____7089 =
                                    let uu____7096 =
                                      let uu____7105 =
                                        FStar_List.tl rest_args  in
                                      FStar_List.tl uu____7105  in
                                    FStar_List.hd uu____7096  in
                                  (match uu____7089 with
                                   | (z,uu____7135) ->
                                       let shadow_app =
                                         let uu____7145 =
                                           FStar_Common.mk_thunk
                                             (fun uu____7154  ->
                                                let uu____7155 =
                                                  let uu____7160 =
                                                    norm1
                                                      (FStar_Util.Inl fv_lid1)
                                                     in
                                                  FStar_Syntax_Syntax.mk_Tm_app
                                                    uu____7160 args
                                                   in
                                                uu____7155
                                                  FStar_Pervasives_Native.None
                                                  rng)
                                            in
                                         FStar_Pervasives_Native.Some
                                           uu____7145
                                          in
                                       let uu____7206 =
                                         let uu____7209 =
                                           let uu____7212 = unembed ea x  in
                                           uu____7212 true norm1  in
                                         FStar_Util.bind_opt uu____7209
                                           (fun x1  ->
                                              let uu____7228 =
                                                let uu____7231 = unembed eb y
                                                   in
                                                uu____7231 true norm1  in
                                              FStar_Util.bind_opt uu____7228
                                                (fun y1  ->
                                                   let uu____7247 =
                                                     let uu____7250 =
                                                       unembed ec z  in
                                                     uu____7250 true norm1
                                                      in
                                                   FStar_Util.bind_opt
                                                     uu____7247
                                                     (fun z1  ->
                                                        let uu____7266 =
                                                          let uu____7267 =
                                                            let uu____7274 =
                                                              f x1 y1 z1  in
                                                            embed ed
                                                              uu____7274
                                                             in
                                                          uu____7267 rng
                                                            shadow_app norm1
                                                           in
                                                        FStar_Pervasives_Native.Some
                                                          uu____7266)))
                                          in
                                       (match uu____7206 with
                                        | FStar_Pervasives_Native.Some x1 ->
                                            FStar_Pervasives_Native.Some x1
                                        | FStar_Pervasives_Native.None  ->
                                            let uu____7303 =
                                              force_shadow shadow_app  in
                                            (match uu____7303 with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some
                                                 app ->
                                                 let uu____7309 =
                                                   norm1 (FStar_Util.Inr app)
                                                    in
                                                 FStar_Pervasives_Native.Some
                                                   uu____7309)))))
                     in
                  f_wrapped
  