open Prims
type norm_cb =
  (FStar_Ident.lid,FStar_Syntax_Syntax.term) FStar_Util.either ->
    FStar_Syntax_Syntax.term
let (id_norm_cb : norm_cb) =
  fun uu___0_28  ->
    match uu___0_28 with
    | FStar_Util.Inr x -> x
    | FStar_Util.Inl l ->
        let uu____71 =
          FStar_Syntax_Syntax.lid_as_fv l
            FStar_Syntax_Syntax.delta_equational FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.fv_to_tm uu____71
  
exception Embedding_failure 
let (uu___is_Embedding_failure : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Embedding_failure  -> true | uu____87 -> false
  
exception Unembedding_failure 
let (uu___is_Unembedding_failure : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unembedding_failure  -> true | uu____98 -> false
  
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
             (fun uu____166  ->
                let uu____167 = FStar_Common.force_thunk s1  in f uu____167))
  
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
  'Auu____692 . FStar_Syntax_Syntax.term -> 'Auu____692 -> Prims.string =
  fun typ  ->
    fun uu____707  ->
      let uu____712 = FStar_Syntax_Print.term_to_string typ  in
      FStar_Util.format1 "unknown %s" uu____712
  
let (term_as_fv : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.fv) =
  fun t  ->
    let uu____732 =
      let uu____733 = FStar_Syntax_Subst.compress t  in
      uu____733.FStar_Syntax_Syntax.n  in
    match uu____732 with
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv
    | uu____751 ->
        let uu____752 =
          let uu____754 = FStar_Syntax_Print.term_to_string t  in
          FStar_Util.format1 "Embeddings not defined for type %s" uu____754
           in
        failwith uu____752
  
let mk_emb :
  'a .
    'a raw_embedder ->
      'a raw_unembedder -> FStar_Syntax_Syntax.fv -> 'a embedding
  =
  fun em  ->
    fun un  ->
      fun fv  ->
        let typ = FStar_Syntax_Syntax.fv_to_tm fv  in
        let uu____821 =
          let uu____822 =
            let uu____830 =
              let uu____832 = FStar_Syntax_Syntax.lid_of_fv fv  in
              FStar_All.pipe_right uu____832 FStar_Ident.string_of_lid  in
            (uu____830, [])  in
          FStar_Syntax_Syntax.ET_app uu____822  in
        { em; un; typ; print = (unknown_printer typ); emb_typ = uu____821 }
  
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
    fun t  -> fun n1  -> let uu____1045 = unembed e t  in uu____1045 true n1
  
let try_unembed :
  'a .
    'a embedding ->
      FStar_Syntax_Syntax.term ->
        norm_cb -> 'a FStar_Pervasives_Native.option
  =
  fun e  ->
    fun t  -> fun n1  -> let uu____1101 = unembed e t  in uu____1101 false n1
  
let type_of : 'a . 'a embedding -> FStar_Syntax_Syntax.typ = fun e  -> e.typ 
let set_type : 'a . FStar_Syntax_Syntax.typ -> 'a embedding -> 'a embedding =
  fun ty  ->
    fun e  ->
      let uu___79_1181 = e  in
      {
        em = (uu___79_1181.em);
        un = (uu___79_1181.un);
        typ = ty;
        print = (uu___79_1181.print);
        emb_typ = (uu___79_1181.emb_typ)
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
              (let uu____1271 =
                 FStar_ST.op_Bang FStar_Options.debug_embedding  in
               if uu____1271
               then
                 let uu____1295 = FStar_Syntax_Print.term_to_string ta  in
                 let uu____1297 = FStar_Syntax_Print.emb_typ_to_string et  in
                 let uu____1299 = pa x  in
                 FStar_Util.print3
                   "Embedding a %s\n\temb_typ=%s\n\tvalue is %s\n" uu____1295
                   uu____1297 uu____1299
               else ());
              (let uu____1304 =
                 FStar_ST.op_Bang FStar_Options.eager_embedding  in
               if uu____1304
               then f ()
               else
                 (let thunk1 = FStar_Common.mk_thunk f  in
                  let uu____1351 =
                    let uu____1358 =
                      let uu____1359 =
                        let uu____1368 = FStar_Dyn.mkdyn x  in
                        {
                          FStar_Syntax_Syntax.blob = uu____1368;
                          FStar_Syntax_Syntax.lkind =
                            (FStar_Syntax_Syntax.Lazy_embedding (et, thunk1));
                          FStar_Syntax_Syntax.ltyp = FStar_Syntax_Syntax.tun;
                          FStar_Syntax_Syntax.rng = rng
                        }  in
                      FStar_Syntax_Syntax.Tm_lazy uu____1359  in
                    FStar_Syntax_Syntax.mk uu____1358  in
                  uu____1351 FStar_Pervasives_Native.None rng))
  
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
                  FStar_Syntax_Syntax.ltyp = uu____1471;
                  FStar_Syntax_Syntax.rng = uu____1472;_}
                ->
                let uu____1495 =
                  (et <> et') ||
                    (FStar_ST.op_Bang FStar_Options.eager_embedding)
                   in
                if uu____1495
                then
                  let res =
                    let uu____1524 = FStar_Common.force_thunk t  in
                    f uu____1524  in
                  ((let uu____1540 =
                      FStar_ST.op_Bang FStar_Options.debug_embedding  in
                    if uu____1540
                    then
                      let uu____1564 =
                        FStar_Syntax_Print.emb_typ_to_string et  in
                      let uu____1566 =
                        FStar_Syntax_Print.emb_typ_to_string et'  in
                      let uu____1568 =
                        match res with
                        | FStar_Pervasives_Native.None  -> "None"
                        | FStar_Pervasives_Native.Some x2 ->
                            let uu____1573 = pa x2  in
                            Prims.op_Hat "Some " uu____1573
                         in
                      FStar_Util.print3
                        "Unembed cancellation failed\n\t%s <> %s\nvalue is %s\n"
                        uu____1564 uu____1566 uu____1568
                    else ());
                   res)
                else
                  (let a = FStar_Dyn.undyn b  in
                   (let uu____1583 =
                      FStar_ST.op_Bang FStar_Options.debug_embedding  in
                    if uu____1583
                    then
                      let uu____1607 =
                        FStar_Syntax_Print.emb_typ_to_string et  in
                      let uu____1609 = pa a  in
                      FStar_Util.print2
                        "Unembed cancelled for %s\n\tvalue is %s\n"
                        uu____1607 uu____1609
                    else ());
                   FStar_Pervasives_Native.Some a)
            | uu____1614 ->
                let aopt = f x1  in
                ((let uu____1619 =
                    FStar_ST.op_Bang FStar_Options.debug_embedding  in
                  if uu____1619
                  then
                    let uu____1643 = FStar_Syntax_Print.emb_typ_to_string et
                       in
                    let uu____1645 = FStar_Syntax_Print.term_to_string x1  in
                    let uu____1647 =
                      match aopt with
                      | FStar_Pervasives_Native.None  -> "None"
                      | FStar_Pervasives_Native.Some a ->
                          let uu____1652 = pa a  in
                          Prims.op_Hat "Some " uu____1652
                       in
                    FStar_Util.print3
                      "Unembedding:\n\temb_typ=%s\n\tterm is %s\n\tvalue is %s\n"
                      uu____1643 uu____1645 uu____1647
                  else ());
                 aopt)
  
let (mk_any_emb :
  FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term embedding) =
  fun typ  ->
    let em t _r _topt _norm =
      (let uu____1721 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
       if uu____1721
       then
         let uu____1745 = unknown_printer typ t  in
         FStar_Util.print1 "Embedding abstract: %s\n" uu____1745
       else ());
      t  in
    let un t _w _n =
      (let uu____1789 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
       if uu____1789
       then
         let uu____1813 = unknown_printer typ t  in
         FStar_Util.print1 "Unembedding abstract: %s\n" uu____1813
       else ());
      FStar_Pervasives_Native.Some t  in
    mk_emb_full em un typ (unknown_printer typ)
      FStar_Syntax_Syntax.ET_abstract
  
let (e_any : FStar_Syntax_Syntax.term embedding) =
  let em t _r _topt _norm = t  in
  let un t _w _n = FStar_Pervasives_Native.Some t  in
  let uu____1929 =
    let uu____1930 =
      let uu____1938 =
        FStar_All.pipe_right FStar_Parser_Const.term_lid
          FStar_Ident.string_of_lid
         in
      (uu____1938, [])  in
    FStar_Syntax_Syntax.ET_app uu____1930  in
  mk_emb_full em un FStar_Syntax_Syntax.t_term
    FStar_Syntax_Print.term_to_string uu____1929
  
let (e_unit : unit embedding) =
  let em u rng _topt _norm =
    let uu___153_1993 = FStar_Syntax_Util.exp_unit  in
    {
      FStar_Syntax_Syntax.n = (uu___153_1993.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___153_1993.FStar_Syntax_Syntax.vars)
    }  in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unascribe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit ) ->
        FStar_Pervasives_Native.Some ()
    | uu____2045 ->
        (if w
         then
           (let uu____2048 =
              let uu____2054 =
                let uu____2056 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded unit: %s" uu____2056  in
              (FStar_Errors.Warning_NotEmbedded, uu____2054)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____2048)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____2062 =
    let uu____2063 =
      let uu____2071 =
        FStar_All.pipe_right FStar_Parser_Const.unit_lid
          FStar_Ident.string_of_lid
         in
      (uu____2071, [])  in
    FStar_Syntax_Syntax.ET_app uu____2063  in
  mk_emb_full em un FStar_Syntax_Syntax.t_unit (fun uu____2082  -> "()")
    uu____2062
  
let (e_bool : Prims.bool embedding) =
  let em b rng _topt _norm =
    let t =
      if b
      then FStar_Syntax_Util.exp_true_bool
      else FStar_Syntax_Util.exp_false_bool  in
    let uu___173_2148 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___173_2148.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___173_2148.FStar_Syntax_Syntax.vars)
    }  in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) ->
        FStar_Pervasives_Native.Some b
    | uu____2208 ->
        (if w
         then
           (let uu____2211 =
              let uu____2217 =
                let uu____2219 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded bool: %s" uu____2219  in
              (FStar_Errors.Warning_NotEmbedded, uu____2217)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____2211)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____2226 =
    let uu____2227 =
      let uu____2235 =
        FStar_All.pipe_right FStar_Parser_Const.bool_lid
          FStar_Ident.string_of_lid
         in
      (uu____2235, [])  in
    FStar_Syntax_Syntax.ET_app uu____2227  in
  mk_emb_full em un FStar_Syntax_Syntax.t_bool FStar_Util.string_of_bool
    uu____2226
  
let (e_char : FStar_Char.char embedding) =
  let em c rng _topt _norm =
    let t = FStar_Syntax_Util.exp_char c  in
    let uu___192_2299 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___192_2299.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___192_2299.FStar_Syntax_Syntax.vars)
    }  in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c) ->
        FStar_Pervasives_Native.Some c
    | uu____2357 ->
        (if w
         then
           (let uu____2360 =
              let uu____2366 =
                let uu____2368 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded char: %s" uu____2368  in
              (FStar_Errors.Warning_NotEmbedded, uu____2366)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____2360)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____2375 =
    let uu____2376 =
      let uu____2384 =
        FStar_All.pipe_right FStar_Parser_Const.char_lid
          FStar_Ident.string_of_lid
         in
      (uu____2384, [])  in
    FStar_Syntax_Syntax.ET_app uu____2376  in
  mk_emb_full em un FStar_Syntax_Syntax.t_char FStar_Util.string_of_char
    uu____2375
  
let (e_int : FStar_BigInt.t embedding) =
  let t_int1 = FStar_Syntax_Util.fvar_const FStar_Parser_Const.int_lid  in
  let emb_t_int =
    let uu____2415 =
      let uu____2423 =
        FStar_All.pipe_right FStar_Parser_Const.int_lid
          FStar_Ident.string_of_lid
         in
      (uu____2423, [])  in
    FStar_Syntax_Syntax.ET_app uu____2415  in
  let em i rng _topt _norm =
    lazy_embed FStar_BigInt.string_of_big_int emb_t_int rng t_int1 i
      (fun uu____2466  ->
         let uu____2467 = FStar_BigInt.string_of_big_int i  in
         FStar_Syntax_Util.exp_int uu____2467)
     in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    lazy_unembed FStar_BigInt.string_of_big_int emb_t_int t t_int1
      (fun t1  ->
         match t1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
             (s,uu____2522)) ->
             let uu____2537 = FStar_BigInt.big_int_of_string s  in
             FStar_Pervasives_Native.Some uu____2537
         | uu____2538 ->
             (if w
              then
                (let uu____2541 =
                   let uu____2547 =
                     let uu____2549 = FStar_Syntax_Print.term_to_string t0
                        in
                     FStar_Util.format1 "Not an embedded int: %s" uu____2549
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____2547)  in
                 FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____2541)
              else ();
              FStar_Pervasives_Native.None))
     in
  mk_emb_full em un FStar_Syntax_Syntax.t_int FStar_BigInt.string_of_big_int
    emb_t_int
  
let (e_string : Prims.string embedding) =
  let emb_t_string =
    let uu____2567 =
      let uu____2575 =
        FStar_All.pipe_right FStar_Parser_Const.string_lid
          FStar_Ident.string_of_lid
         in
      (uu____2575, [])  in
    FStar_Syntax_Syntax.ET_app uu____2567  in
  let em s rng _topt _norm =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, rng)))
      FStar_Pervasives_Native.None rng
     in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
        (s,uu____2666)) -> FStar_Pervasives_Native.Some s
    | uu____2670 ->
        (if w
         then
           (let uu____2673 =
              let uu____2679 =
                let uu____2681 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded string: %s" uu____2681
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____2679)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____2673)
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
      let uu____2747 =
        let uu____2752 =
          let uu____2753 = FStar_Syntax_Syntax.as_arg ea.typ  in [uu____2753]
           in
        FStar_Syntax_Syntax.mk_Tm_app t_opt uu____2752  in
      uu____2747 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
    let emb_t_option_a =
      let uu____2791 =
        let uu____2799 =
          FStar_All.pipe_right FStar_Parser_Const.option_lid
            FStar_Ident.string_of_lid
           in
        (uu____2799, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____2791  in
    let printer uu___1_2817 =
      match uu___1_2817 with
      | FStar_Pervasives_Native.None  -> "None"
      | FStar_Pervasives_Native.Some x ->
          let uu____2823 =
            let uu____2825 = ea.print x  in Prims.op_Hat uu____2825 ")"  in
          Prims.op_Hat "(Some " uu____2823
       in
    let em o rng topt norm1 =
      lazy_embed printer emb_t_option_a rng t_option_a o
        (fun uu____2868  ->
           match o with
           | FStar_Pervasives_Native.None  ->
               let uu____2873 =
                 let uu____2878 =
                   let uu____2887 =
                     FStar_Syntax_Syntax.tdataconstr
                       FStar_Parser_Const.none_lid
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____2887
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 let uu____2896 =
                   let uu____2897 =
                     let uu____2910 = type_of ea  in
                     FStar_Syntax_Syntax.iarg uu____2910  in
                   [uu____2897]  in
                 FStar_Syntax_Syntax.mk_Tm_app uu____2878 uu____2896  in
               uu____2873 FStar_Pervasives_Native.None rng
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
                        let uu____2980 =
                          FStar_Syntax_Syntax.lid_as_fv some_v
                            FStar_Syntax_Syntax.delta_equational
                            FStar_Pervasives_Native.None
                           in
                        FStar_Syntax_Syntax.fv_to_tm uu____2980  in
                      let uu____2987 =
                        let uu____2992 =
                          FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm
                            [FStar_Syntax_Syntax.U_zero]
                           in
                        let uu____3001 =
                          let uu____3002 =
                            let uu____3015 = type_of ea  in
                            FStar_Syntax_Syntax.iarg uu____3015  in
                          let uu____3024 =
                            let uu____3039 = FStar_Syntax_Syntax.as_arg t  in
                            [uu____3039]  in
                          uu____3002 :: uu____3024  in
                        FStar_Syntax_Syntax.mk_Tm_app uu____2992 uu____3001
                         in
                      uu____2987 FStar_Pervasives_Native.None rng)
                  in
               let uu____3088 =
                 let uu____3093 =
                   let uu____3102 =
                     FStar_Syntax_Syntax.tdataconstr
                       FStar_Parser_Const.some_lid
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____3102
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 let uu____3111 =
                   let uu____3112 =
                     let uu____3125 = type_of ea  in
                     FStar_Syntax_Syntax.iarg uu____3125  in
                   let uu____3134 =
                     let uu____3149 =
                       let uu____3162 =
                         let uu____3171 = embed ea a  in
                         uu____3171 rng shadow_a norm1  in
                       FStar_Syntax_Syntax.as_arg uu____3162  in
                     [uu____3149]  in
                   uu____3112 :: uu____3134  in
                 FStar_Syntax_Syntax.mk_Tm_app uu____3093 uu____3111  in
               uu____3088 FStar_Pervasives_Native.None rng)
       in
    let un t0 w norm1 =
      let t = FStar_Syntax_Util.unmeta_safe t0  in
      lazy_unembed printer emb_t_option_a t t_option_a
        (fun t1  ->
           let uu____3273 = FStar_Syntax_Util.head_and_args' t1  in
           match uu____3273 with
           | (hd1,args) ->
               let uu____3338 =
                 let uu____3357 =
                   let uu____3358 = FStar_Syntax_Util.un_uinst hd1  in
                   uu____3358.FStar_Syntax_Syntax.n  in
                 (uu____3357, args)  in
               (match uu____3338 with
                | (FStar_Syntax_Syntax.Tm_fvar fv,uu____3388) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.none_lid
                    ->
                    FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,uu____3423::(a,uu____3425)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.some_lid
                    ->
                    let uu____3507 =
                      let uu____3510 = unembed ea a  in uu____3510 w norm1
                       in
                    FStar_Util.bind_opt uu____3507
                      (fun a1  ->
                         FStar_Pervasives_Native.Some
                           (FStar_Pervasives_Native.Some a1))
                | uu____3523 ->
                    (if w
                     then
                       (let uu____3544 =
                          let uu____3550 =
                            let uu____3552 =
                              FStar_Syntax_Print.term_to_string t0  in
                            FStar_Util.format1 "Not an embedded option: %s"
                              uu____3552
                             in
                          (FStar_Errors.Warning_NotEmbedded, uu____3550)  in
                        FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                          uu____3544)
                     else ();
                     FStar_Pervasives_Native.None)))
       in
    let uu____3560 =
      let uu____3569 = type_of ea  in
      FStar_Syntax_Syntax.t_option_of uu____3569  in
    mk_emb_full em un uu____3560 printer emb_t_option_a
  
let e_tuple2 : 'a 'b . 'a embedding -> 'b embedding -> ('a * 'b) embedding =
  fun ea  ->
    fun eb  ->
      let t_pair_a_b =
        let t_tup2 =
          FStar_Syntax_Util.fvar_const FStar_Parser_Const.lid_tuple2  in
        let uu____3656 =
          let uu____3661 =
            let uu____3662 = FStar_Syntax_Syntax.as_arg ea.typ  in
            let uu____3675 =
              let uu____3690 = FStar_Syntax_Syntax.as_arg eb.typ  in
              [uu____3690]  in
            uu____3662 :: uu____3675  in
          FStar_Syntax_Syntax.mk_Tm_app t_tup2 uu____3661  in
        uu____3656 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
      let emb_t_pair_a_b =
        let uu____3740 =
          let uu____3748 =
            FStar_All.pipe_right FStar_Parser_Const.lid_tuple2
              FStar_Ident.string_of_lid
             in
          (uu____3748, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____3740  in
      let printer uu____3768 =
        match uu____3768 with
        | (x,y) ->
            let uu____3776 = ea.print x  in
            let uu____3778 = eb.print y  in
            FStar_Util.format2 "(%s, %s)" uu____3776 uu____3778
         in
      let em x rng topt norm1 =
        lazy_embed printer emb_t_pair_a_b rng t_pair_a_b x
          (fun uu____3829  ->
             let proj i ab =
               let uu____3857 =
                 let uu____3871 =
                   FStar_Parser_Const.mk_tuple_data_lid (Prims.parse_int "2")
                     rng
                    in
                 let uu____3881 =
                   FStar_Syntax_Syntax.null_bv FStar_Syntax_Syntax.tun  in
                 FStar_Syntax_Util.mk_field_projector_name uu____3871
                   uu____3881 i
                  in
               match uu____3857 with
               | (proj_1,uu____3899) ->
                   let proj_1_tm =
                     let uu____3927 =
                       FStar_Syntax_Syntax.lid_as_fv proj_1
                         FStar_Syntax_Syntax.delta_equational
                         FStar_Pervasives_Native.None
                        in
                     FStar_Syntax_Syntax.fv_to_tm uu____3927  in
                   let uu____3934 =
                     let uu____3939 =
                       FStar_Syntax_Syntax.mk_Tm_uinst proj_1_tm
                         [FStar_Syntax_Syntax.U_zero]
                        in
                     let uu____3948 =
                       let uu____3949 =
                         let uu____3962 = type_of ea  in
                         FStar_Syntax_Syntax.iarg uu____3962  in
                       let uu____3971 =
                         let uu____3986 =
                           let uu____3999 = type_of eb  in
                           FStar_Syntax_Syntax.iarg uu____3999  in
                         let uu____4008 =
                           let uu____4023 = FStar_Syntax_Syntax.as_arg ab  in
                           [uu____4023]  in
                         uu____3986 :: uu____4008  in
                       uu____3949 :: uu____3971  in
                     FStar_Syntax_Syntax.mk_Tm_app uu____3939 uu____3948  in
                   uu____3934 FStar_Pervasives_Native.None rng
                in
             let shadow_a = map_shadow topt (proj (Prims.parse_int "1"))  in
             let shadow_b = map_shadow topt (proj (Prims.parse_int "2"))  in
             let uu____4088 =
               let uu____4093 =
                 let uu____4102 =
                   FStar_Syntax_Syntax.tdataconstr
                     FStar_Parser_Const.lid_Mktuple2
                    in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu____4102
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                  in
               let uu____4111 =
                 let uu____4112 =
                   let uu____4125 = type_of ea  in
                   FStar_Syntax_Syntax.iarg uu____4125  in
                 let uu____4134 =
                   let uu____4149 =
                     let uu____4162 = type_of eb  in
                     FStar_Syntax_Syntax.iarg uu____4162  in
                   let uu____4171 =
                     let uu____4186 =
                       let uu____4199 =
                         let uu____4208 =
                           embed ea (FStar_Pervasives_Native.fst x)  in
                         uu____4208 rng shadow_a norm1  in
                       FStar_Syntax_Syntax.as_arg uu____4199  in
                     let uu____4215 =
                       let uu____4230 =
                         let uu____4243 =
                           let uu____4252 =
                             embed eb (FStar_Pervasives_Native.snd x)  in
                           uu____4252 rng shadow_b norm1  in
                         FStar_Syntax_Syntax.as_arg uu____4243  in
                       [uu____4230]  in
                     uu____4186 :: uu____4215  in
                   uu____4149 :: uu____4171  in
                 uu____4112 :: uu____4134  in
               FStar_Syntax_Syntax.mk_Tm_app uu____4093 uu____4111  in
             uu____4088 FStar_Pervasives_Native.None rng)
         in
      let un t0 w norm1 =
        let t = FStar_Syntax_Util.unmeta_safe t0  in
        lazy_unembed printer emb_t_pair_a_b t t_pair_a_b
          (fun t1  ->
             let uu____4390 = FStar_Syntax_Util.head_and_args' t1  in
             match uu____4390 with
             | (hd1,args) ->
                 let uu____4457 =
                   let uu____4474 =
                     let uu____4475 = FStar_Syntax_Util.un_uinst hd1  in
                     uu____4475.FStar_Syntax_Syntax.n  in
                   (uu____4474, args)  in
                 (match uu____4457 with
                  | (FStar_Syntax_Syntax.Tm_fvar
                     fv,uu____4505::uu____4506::(a,uu____4508)::(b,uu____4510)::[])
                      when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.lid_Mktuple2
                      ->
                      let uu____4620 =
                        let uu____4623 = unembed ea a  in uu____4623 w norm1
                         in
                      FStar_Util.bind_opt uu____4620
                        (fun a1  ->
                           let uu____4637 =
                             let uu____4640 = unembed eb b  in
                             uu____4640 w norm1  in
                           FStar_Util.bind_opt uu____4637
                             (fun b1  ->
                                FStar_Pervasives_Native.Some (a1, b1)))
                  | uu____4657 ->
                      (if w
                       then
                         (let uu____4676 =
                            let uu____4682 =
                              let uu____4684 =
                                FStar_Syntax_Print.term_to_string t0  in
                              FStar_Util.format1 "Not an embedded pair: %s"
                                uu____4684
                               in
                            (FStar_Errors.Warning_NotEmbedded, uu____4682)
                             in
                          FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                            uu____4676)
                       else ();
                       FStar_Pervasives_Native.None)))
         in
      let uu____4694 =
        let uu____4703 = type_of ea  in
        let uu____4712 = type_of eb  in
        FStar_Syntax_Syntax.t_tuple2_of uu____4703 uu____4712  in
      mk_emb_full em un uu____4694 printer emb_t_pair_a_b
  
let e_either :
  'a 'b . 'a embedding -> 'b embedding -> ('a,'b) FStar_Util.either embedding
  =
  fun ea  ->
    fun eb  ->
      let t_sum_a_b =
        let t_either =
          FStar_Syntax_Util.fvar_const FStar_Parser_Const.either_lid  in
        let uu____4801 =
          let uu____4806 =
            let uu____4807 = FStar_Syntax_Syntax.as_arg ea.typ  in
            let uu____4820 =
              let uu____4835 = FStar_Syntax_Syntax.as_arg eb.typ  in
              [uu____4835]  in
            uu____4807 :: uu____4820  in
          FStar_Syntax_Syntax.mk_Tm_app t_either uu____4806  in
        uu____4801 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
      let emb_t_sum_a_b =
        let uu____4885 =
          let uu____4893 =
            FStar_All.pipe_right FStar_Parser_Const.either_lid
              FStar_Ident.string_of_lid
             in
          (uu____4893, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____4885  in
      let printer s =
        match s with
        | FStar_Util.Inl a ->
            let uu____4920 = ea.print a  in
            FStar_Util.format1 "Inl %s" uu____4920
        | FStar_Util.Inr b ->
            let uu____4924 = eb.print b  in
            FStar_Util.format1 "Inr %s" uu____4924
         in
      let em s rng topt norm1 =
        lazy_embed printer emb_t_sum_a_b rng t_sum_a_b s
          (match s with
           | FStar_Util.Inl a ->
               (fun uu____4982  ->
                  let shadow_a =
                    map_shadow topt
                      (fun t  ->
                         let v1 = FStar_Ident.mk_ident ("v", rng)  in
                         let some_v =
                           FStar_Syntax_Util.mk_field_projector_name_from_ident
                             FStar_Parser_Const.inl_lid v1
                            in
                         let some_v_tm =
                           let uu____5019 =
                             FStar_Syntax_Syntax.lid_as_fv some_v
                               FStar_Syntax_Syntax.delta_equational
                               FStar_Pervasives_Native.None
                              in
                           FStar_Syntax_Syntax.fv_to_tm uu____5019  in
                         let uu____5026 =
                           let uu____5031 =
                             FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm
                               [FStar_Syntax_Syntax.U_zero]
                              in
                           let uu____5040 =
                             let uu____5041 =
                               let uu____5054 = type_of ea  in
                               FStar_Syntax_Syntax.iarg uu____5054  in
                             let uu____5063 =
                               let uu____5078 =
                                 let uu____5091 = type_of eb  in
                                 FStar_Syntax_Syntax.iarg uu____5091  in
                               let uu____5100 =
                                 let uu____5115 =
                                   FStar_Syntax_Syntax.as_arg t  in
                                 [uu____5115]  in
                               uu____5078 :: uu____5100  in
                             uu____5041 :: uu____5063  in
                           FStar_Syntax_Syntax.mk_Tm_app uu____5031
                             uu____5040
                            in
                         uu____5026 FStar_Pervasives_Native.None rng)
                     in
                  let uu____5176 =
                    let uu____5181 =
                      let uu____5190 =
                        FStar_Syntax_Syntax.tdataconstr
                          FStar_Parser_Const.inl_lid
                         in
                      FStar_Syntax_Syntax.mk_Tm_uinst uu____5190
                        [FStar_Syntax_Syntax.U_zero;
                        FStar_Syntax_Syntax.U_zero]
                       in
                    let uu____5199 =
                      let uu____5200 =
                        let uu____5213 = type_of ea  in
                        FStar_Syntax_Syntax.iarg uu____5213  in
                      let uu____5222 =
                        let uu____5237 =
                          let uu____5250 = type_of eb  in
                          FStar_Syntax_Syntax.iarg uu____5250  in
                        let uu____5259 =
                          let uu____5274 =
                            let uu____5287 =
                              let uu____5296 = embed ea a  in
                              uu____5296 rng shadow_a norm1  in
                            FStar_Syntax_Syntax.as_arg uu____5287  in
                          [uu____5274]  in
                        uu____5237 :: uu____5259  in
                      uu____5200 :: uu____5222  in
                    FStar_Syntax_Syntax.mk_Tm_app uu____5181 uu____5199  in
                  uu____5176 FStar_Pervasives_Native.None rng)
           | FStar_Util.Inr b ->
               (fun uu____5352  ->
                  let shadow_b =
                    map_shadow topt
                      (fun t  ->
                         let v1 = FStar_Ident.mk_ident ("v", rng)  in
                         let some_v =
                           FStar_Syntax_Util.mk_field_projector_name_from_ident
                             FStar_Parser_Const.inr_lid v1
                            in
                         let some_v_tm =
                           let uu____5389 =
                             FStar_Syntax_Syntax.lid_as_fv some_v
                               FStar_Syntax_Syntax.delta_equational
                               FStar_Pervasives_Native.None
                              in
                           FStar_Syntax_Syntax.fv_to_tm uu____5389  in
                         let uu____5396 =
                           let uu____5401 =
                             FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm
                               [FStar_Syntax_Syntax.U_zero]
                              in
                           let uu____5410 =
                             let uu____5411 =
                               let uu____5424 = type_of ea  in
                               FStar_Syntax_Syntax.iarg uu____5424  in
                             let uu____5433 =
                               let uu____5448 =
                                 let uu____5461 = type_of eb  in
                                 FStar_Syntax_Syntax.iarg uu____5461  in
                               let uu____5470 =
                                 let uu____5485 =
                                   FStar_Syntax_Syntax.as_arg t  in
                                 [uu____5485]  in
                               uu____5448 :: uu____5470  in
                             uu____5411 :: uu____5433  in
                           FStar_Syntax_Syntax.mk_Tm_app uu____5401
                             uu____5410
                            in
                         uu____5396 FStar_Pervasives_Native.None rng)
                     in
                  let uu____5546 =
                    let uu____5551 =
                      let uu____5560 =
                        FStar_Syntax_Syntax.tdataconstr
                          FStar_Parser_Const.inr_lid
                         in
                      FStar_Syntax_Syntax.mk_Tm_uinst uu____5560
                        [FStar_Syntax_Syntax.U_zero;
                        FStar_Syntax_Syntax.U_zero]
                       in
                    let uu____5569 =
                      let uu____5570 =
                        let uu____5583 = type_of ea  in
                        FStar_Syntax_Syntax.iarg uu____5583  in
                      let uu____5592 =
                        let uu____5607 =
                          let uu____5620 = type_of eb  in
                          FStar_Syntax_Syntax.iarg uu____5620  in
                        let uu____5629 =
                          let uu____5644 =
                            let uu____5657 =
                              let uu____5666 = embed eb b  in
                              uu____5666 rng shadow_b norm1  in
                            FStar_Syntax_Syntax.as_arg uu____5657  in
                          [uu____5644]  in
                        uu____5607 :: uu____5629  in
                      uu____5570 :: uu____5592  in
                    FStar_Syntax_Syntax.mk_Tm_app uu____5551 uu____5569  in
                  uu____5546 FStar_Pervasives_Native.None rng))
         in
      let un t0 w norm1 =
        let t = FStar_Syntax_Util.unmeta_safe t0  in
        lazy_unembed printer emb_t_sum_a_b t t_sum_a_b
          (fun t1  ->
             let uu____5790 = FStar_Syntax_Util.head_and_args' t1  in
             match uu____5790 with
             | (hd1,args) ->
                 let uu____5857 =
                   let uu____5876 =
                     let uu____5877 = FStar_Syntax_Util.un_uinst hd1  in
                     uu____5877.FStar_Syntax_Syntax.n  in
                   (uu____5876, args)  in
                 (match uu____5857 with
                  | (FStar_Syntax_Syntax.Tm_fvar
                     fv,uu____5909::uu____5910::(a,uu____5912)::[]) when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.inl_lid
                      ->
                      let uu____6018 =
                        let uu____6021 = unembed ea a  in uu____6021 w norm1
                         in
                      FStar_Util.bind_opt uu____6018
                        (fun a1  ->
                           FStar_Pervasives_Native.Some (FStar_Util.Inl a1))
                  | (FStar_Syntax_Syntax.Tm_fvar
                     fv,uu____6039::uu____6040::(b,uu____6042)::[]) when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.inr_lid
                      ->
                      let uu____6148 =
                        let uu____6151 = unembed eb b  in uu____6151 w norm1
                         in
                      FStar_Util.bind_opt uu____6148
                        (fun b1  ->
                           FStar_Pervasives_Native.Some (FStar_Util.Inr b1))
                  | uu____6168 ->
                      (if w
                       then
                         (let uu____6189 =
                            let uu____6195 =
                              let uu____6197 =
                                FStar_Syntax_Print.term_to_string t0  in
                              FStar_Util.format1 "Not an embedded sum: %s"
                                uu____6197
                               in
                            (FStar_Errors.Warning_NotEmbedded, uu____6195)
                             in
                          FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                            uu____6189)
                       else ();
                       FStar_Pervasives_Native.None)))
         in
      let uu____6207 =
        let uu____6216 = type_of ea  in
        let uu____6225 = type_of eb  in
        FStar_Syntax_Syntax.t_either_of uu____6216 uu____6225  in
      mk_emb_full em un uu____6207 printer emb_t_sum_a_b
  
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea  ->
    let t_list_a =
      let t_list = FStar_Syntax_Util.fvar_const FStar_Parser_Const.list_lid
         in
      let uu____6291 =
        let uu____6296 =
          let uu____6297 = FStar_Syntax_Syntax.as_arg ea.typ  in [uu____6297]
           in
        FStar_Syntax_Syntax.mk_Tm_app t_list uu____6296  in
      uu____6291 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
    let emb_t_list_a =
      let uu____6335 =
        let uu____6343 =
          FStar_All.pipe_right FStar_Parser_Const.list_lid
            FStar_Ident.string_of_lid
           in
        (uu____6343, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____6335  in
    let printer l =
      let uu____6364 =
        let uu____6366 =
          let uu____6368 = FStar_List.map ea.print l  in
          FStar_All.pipe_right uu____6368 (FStar_String.concat "; ")  in
        Prims.op_Hat uu____6366 "]"  in
      Prims.op_Hat "[" uu____6364  in
    let rec em l rng shadow_l norm1 =
      lazy_embed printer emb_t_list_a rng t_list_a l
        (fun uu____6420  ->
           let t =
             let uu____6422 = type_of ea  in
             FStar_Syntax_Syntax.iarg uu____6422  in
           match l with
           | [] ->
               let uu____6435 =
                 let uu____6440 =
                   let uu____6449 =
                     FStar_Syntax_Syntax.tdataconstr
                       FStar_Parser_Const.nil_lid
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____6449
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 FStar_Syntax_Syntax.mk_Tm_app uu____6440 [t]  in
               uu____6435 FStar_Pervasives_Native.None rng
           | hd1::tl1 ->
               let cons1 =
                 let uu____6495 =
                   FStar_Syntax_Syntax.tdataconstr
                     FStar_Parser_Const.cons_lid
                    in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu____6495
                   [FStar_Syntax_Syntax.U_zero]
                  in
               let proj f cons_tm =
                 let fid = FStar_Ident.mk_ident (f, rng)  in
                 let proj =
                   FStar_Syntax_Util.mk_field_projector_name_from_ident
                     FStar_Parser_Const.cons_lid fid
                    in
                 let proj_tm =
                   let uu____6555 =
                     FStar_Syntax_Syntax.lid_as_fv proj
                       FStar_Syntax_Syntax.delta_equational
                       FStar_Pervasives_Native.None
                      in
                   FStar_Syntax_Syntax.fv_to_tm uu____6555  in
                 let uu____6562 =
                   let uu____6567 =
                     FStar_Syntax_Syntax.mk_Tm_uinst proj_tm
                       [FStar_Syntax_Syntax.U_zero]
                      in
                   let uu____6576 =
                     let uu____6577 =
                       let uu____6590 = type_of ea  in
                       FStar_Syntax_Syntax.iarg uu____6590  in
                     let uu____6599 =
                       let uu____6614 = FStar_Syntax_Syntax.as_arg cons_tm
                          in
                       [uu____6614]  in
                     uu____6577 :: uu____6599  in
                   FStar_Syntax_Syntax.mk_Tm_app uu____6567 uu____6576  in
                 uu____6562 FStar_Pervasives_Native.None rng  in
               let shadow_hd = map_shadow shadow_l (proj "hd")  in
               let shadow_tl = map_shadow shadow_l (proj "tl")  in
               let uu____6667 =
                 let uu____6672 =
                   let uu____6673 =
                     let uu____6688 =
                       let uu____6701 =
                         let uu____6710 = embed ea hd1  in
                         uu____6710 rng shadow_hd norm1  in
                       FStar_Syntax_Syntax.as_arg uu____6701  in
                     let uu____6717 =
                       let uu____6732 =
                         let uu____6745 = em tl1 rng shadow_tl norm1  in
                         FStar_Syntax_Syntax.as_arg uu____6745  in
                       [uu____6732]  in
                     uu____6688 :: uu____6717  in
                   t :: uu____6673  in
                 FStar_Syntax_Syntax.mk_Tm_app cons1 uu____6672  in
               uu____6667 FStar_Pervasives_Native.None rng)
       in
    let rec un t0 w norm1 =
      let t = FStar_Syntax_Util.unmeta_safe t0  in
      lazy_unembed printer emb_t_list_a t t_list_a
        (fun t1  ->
           let uu____6861 = FStar_Syntax_Util.head_and_args' t1  in
           match uu____6861 with
           | (hd1,args) ->
               let uu____6926 =
                 let uu____6943 =
                   let uu____6944 = FStar_Syntax_Util.un_uinst hd1  in
                   uu____6944.FStar_Syntax_Syntax.n  in
                 (uu____6943, args)  in
               (match uu____6926 with
                | (FStar_Syntax_Syntax.Tm_fvar fv,uu____6972) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.nil_lid
                    -> FStar_Pervasives_Native.Some []
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(uu____7003,FStar_Pervasives_Native.Some
                       (FStar_Syntax_Syntax.Implicit uu____7004))::(hd2,FStar_Pervasives_Native.None
                                                                    )::
                   (tl1,FStar_Pervasives_Native.None )::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.cons_lid
                    ->
                    let uu____7093 =
                      let uu____7096 = unembed ea hd2  in uu____7096 w norm1
                       in
                    FStar_Util.bind_opt uu____7093
                      (fun hd3  ->
                         let uu____7108 = un tl1 w norm1  in
                         FStar_Util.bind_opt uu____7108
                           (fun tl2  ->
                              FStar_Pervasives_Native.Some (hd3 :: tl2)))
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(hd2,FStar_Pervasives_Native.None )::(tl1,FStar_Pervasives_Native.None
                                                            )::[])
                    when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.cons_lid
                    ->
                    let uu____7191 =
                      let uu____7194 = unembed ea hd2  in uu____7194 w norm1
                       in
                    FStar_Util.bind_opt uu____7191
                      (fun hd3  ->
                         let uu____7206 = un tl1 w norm1  in
                         FStar_Util.bind_opt uu____7206
                           (fun tl2  ->
                              FStar_Pervasives_Native.Some (hd3 :: tl2)))
                | uu____7221 ->
                    (if w
                     then
                       (let uu____7240 =
                          let uu____7246 =
                            let uu____7248 =
                              FStar_Syntax_Print.term_to_string t0  in
                            FStar_Util.format1 "Not an embedded list: %s"
                              uu____7248
                             in
                          (FStar_Errors.Warning_NotEmbedded, uu____7246)  in
                        FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                          uu____7240)
                     else ();
                     FStar_Pervasives_Native.None)))
       in
    let uu____7256 =
      let uu____7265 = type_of ea  in
      FStar_Syntax_Syntax.t_list_of uu____7265  in
    mk_emb_full em un uu____7256 printer emb_t_list_a
  
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
    match projectee with | Simpl  -> true | uu____7323 -> false
  
let (uu___is_Weak : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Weak  -> true | uu____7334 -> false
  
let (uu___is_HNF : norm_step -> Prims.bool) =
  fun projectee  -> match projectee with | HNF  -> true | uu____7345 -> false 
let (uu___is_Primops : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____7356 -> false
  
let (uu___is_Delta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Delta  -> true | uu____7367 -> false
  
let (uu___is_Zeta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Zeta  -> true | uu____7378 -> false
  
let (uu___is_Iota : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Iota  -> true | uu____7389 -> false
  
let (uu___is_Reify : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____7400 -> false
  
let (uu___is_UnfoldOnly : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____7415 -> false
  
let (__proj__UnfoldOnly__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldFully : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldFully _0 -> true | uu____7446 -> false
  
let (__proj__UnfoldFully__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldFully _0 -> _0 
let (uu___is_UnfoldAttr : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____7477 -> false
  
let (__proj__UnfoldAttr__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_NBE : norm_step -> Prims.bool) =
  fun projectee  -> match projectee with | NBE  -> true | uu____7504 -> false 
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
    let uu____7633 =
      FStar_Ident.lid_of_str "FStar.Syntax.Embeddings.norm_step"  in
    FStar_Syntax_Util.fvar_const uu____7633  in
  let emb_t_norm_step =
    let uu____7644 =
      let uu____7652 =
        FStar_All.pipe_right FStar_Parser_Const.norm_step_lid
          FStar_Ident.string_of_lid
         in
      (uu____7652, [])  in
    FStar_Syntax_Syntax.ET_app uu____7644  in
  let printer uu____7668 = "norm_step"  in
  let em n1 rng _topt norm1 =
    lazy_embed printer emb_t_norm_step rng t_norm_step1 n1
      (fun uu____7702  ->
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
             let uu____7711 =
               let uu____7716 =
                 let uu____7717 =
                   let uu____7730 =
                     let uu____7739 =
                       let uu____7746 = e_list e_string  in
                       embed uu____7746 l  in
                     uu____7739 rng FStar_Pervasives_Native.None norm1  in
                   FStar_Syntax_Syntax.as_arg uu____7730  in
                 [uu____7717]  in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldOnly uu____7716  in
             uu____7711 FStar_Pervasives_Native.None rng
         | UnfoldFully l ->
             let uu____7797 =
               let uu____7802 =
                 let uu____7803 =
                   let uu____7816 =
                     let uu____7825 =
                       let uu____7832 = e_list e_string  in
                       embed uu____7832 l  in
                     uu____7825 rng FStar_Pervasives_Native.None norm1  in
                   FStar_Syntax_Syntax.as_arg uu____7816  in
                 [uu____7803]  in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldFully uu____7802  in
             uu____7797 FStar_Pervasives_Native.None rng
         | UnfoldAttr l ->
             let uu____7883 =
               let uu____7888 =
                 let uu____7889 =
                   let uu____7902 =
                     let uu____7911 =
                       let uu____7918 = e_list e_string  in
                       embed uu____7918 l  in
                     uu____7911 rng FStar_Pervasives_Native.None norm1  in
                   FStar_Syntax_Syntax.as_arg uu____7902  in
                 [uu____7889]  in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldAttr uu____7888  in
             uu____7883 FStar_Pervasives_Native.None rng)
     in
  let un t0 w norm1 =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    lazy_unembed printer emb_t_norm_step t t_norm_step1
      (fun t1  ->
         let uu____8017 = FStar_Syntax_Util.head_and_args t1  in
         match uu____8017 with
         | (hd1,args) ->
             let uu____8086 =
               let uu____8105 =
                 let uu____8106 = FStar_Syntax_Util.un_uinst hd1  in
                 uu____8106.FStar_Syntax_Syntax.n  in
               (uu____8105, args)  in
             (match uu____8086 with
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
              | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____8405)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldonly
                  ->
                  let uu____8463 =
                    let uu____8469 =
                      let uu____8479 = e_list e_string  in
                      unembed uu____8479 l  in
                    uu____8469 w norm1  in
                  FStar_Util.bind_opt uu____8463
                    (fun ss  ->
                       FStar_All.pipe_left
                         (fun _8506  -> FStar_Pervasives_Native.Some _8506)
                         (UnfoldOnly ss))
              | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____8509)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldfully
                  ->
                  let uu____8567 =
                    let uu____8573 =
                      let uu____8583 = e_list e_string  in
                      unembed uu____8583 l  in
                    uu____8573 w norm1  in
                  FStar_Util.bind_opt uu____8567
                    (fun ss  ->
                       FStar_All.pipe_left
                         (fun _8610  -> FStar_Pervasives_Native.Some _8610)
                         (UnfoldFully ss))
              | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____8613)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldattr
                  ->
                  let uu____8671 =
                    let uu____8677 =
                      let uu____8687 = e_list e_string  in
                      unembed uu____8687 l  in
                    uu____8677 w norm1  in
                  FStar_Util.bind_opt uu____8671
                    (fun ss  ->
                       FStar_All.pipe_left
                         (fun _8714  -> FStar_Pervasives_Native.Some _8714)
                         (UnfoldAttr ss))
              | uu____8715 ->
                  (if w
                   then
                     (let uu____8736 =
                        let uu____8742 =
                          let uu____8744 =
                            FStar_Syntax_Print.term_to_string t0  in
                          FStar_Util.format1 "Not an embedded norm_step: %s"
                            uu____8744
                           in
                        (FStar_Errors.Warning_NotEmbedded, uu____8742)  in
                      FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                        uu____8736)
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
    | uu____8835 ->
        (if w
         then
           (let uu____8838 =
              let uu____8844 =
                let uu____8846 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded range: %s" uu____8846  in
              (FStar_Errors.Warning_NotEmbedded, uu____8844)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____8838)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____8852 =
    let uu____8853 =
      let uu____8861 =
        FStar_All.pipe_right FStar_Parser_Const.range_lid
          FStar_Ident.string_of_lid
         in
      (uu____8861, [])  in
    FStar_Syntax_Syntax.ET_app uu____8853  in
  mk_emb_full em un FStar_Syntax_Syntax.t_range FStar_Range.string_of_range
    uu____8852
  
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
        let uu____8965 =
          let uu____8972 =
            let uu____8973 =
              let uu____8997 =
                let uu____9011 =
                  let uu____9023 = FStar_Syntax_Syntax.null_bv ea.typ  in
                  (uu____9023, FStar_Pervasives_Native.None)  in
                [uu____9011]  in
              let uu____9063 = FStar_Syntax_Syntax.mk_Total eb.typ  in
              (uu____8997, uu____9063)  in
            FStar_Syntax_Syntax.Tm_arrow uu____8973  in
          FStar_Syntax_Syntax.mk uu____8972  in
        uu____8965 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
      let emb_t_arr_a_b =
        FStar_Syntax_Syntax.ET_fun ((ea.emb_typ), (eb.emb_typ))  in
      let printer f = "<fun>"  in
      let em f rng shadow_f norm1 =
        lazy_embed (fun uu____9180  -> "<fun>") emb_t_arr_a_b rng t_arrow f
          (fun uu____9186  ->
             let uu____9187 = force_shadow shadow_f  in
             match uu____9187 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Exn.raise Embedding_failure
             | FStar_Pervasives_Native.Some repr_f ->
                 ((let uu____9216 =
                     FStar_ST.op_Bang FStar_Options.debug_embedding  in
                   if uu____9216
                   then
                     let uu____9240 =
                       FStar_Syntax_Print.term_to_string repr_f  in
                     let uu____9242 = FStar_Util.stack_dump ()  in
                     FStar_Util.print2
                       "e_arrow forced back to term using shadow %s; repr=%s\n"
                       uu____9240 uu____9242
                   else ());
                  (let res = norm1 (FStar_Util.Inr repr_f)  in
                   (let uu____9265 =
                      FStar_ST.op_Bang FStar_Options.debug_embedding  in
                    if uu____9265
                    then
                      let uu____9289 =
                        FStar_Syntax_Print.term_to_string repr_f  in
                      let uu____9291 = FStar_Syntax_Print.term_to_string res
                         in
                      let uu____9293 = FStar_Util.stack_dump ()  in
                      FStar_Util.print3
                        "e_arrow forced back to term using shadow %s; repr=%s\n\t%s\n"
                        uu____9289 uu____9291 uu____9293
                    else ());
                   res)))
         in
      let un f w norm1 =
        lazy_unembed printer emb_t_arr_a_b f t_arrow
          (fun f1  ->
             let f_wrapped a =
               (let uu____9388 =
                  FStar_ST.op_Bang FStar_Options.debug_embedding  in
                if uu____9388
                then
                  let uu____9412 = FStar_Syntax_Print.term_to_string f1  in
                  let uu____9414 = FStar_Util.stack_dump ()  in
                  FStar_Util.print2
                    "Calling back into normalizer for %s\n%s\n" uu____9412
                    uu____9414
                else ());
               (let a_tm =
                  let uu____9428 = embed ea a  in
                  uu____9428 f1.FStar_Syntax_Syntax.pos
                    FStar_Pervasives_Native.None norm1
                   in
                let b_tm =
                  let uu____9450 =
                    let uu____9463 =
                      let uu____9472 =
                        let uu____9477 =
                          let uu____9478 = FStar_Syntax_Syntax.as_arg a_tm
                             in
                          [uu____9478]  in
                        FStar_Syntax_Syntax.mk_Tm_app f1 uu____9477  in
                      uu____9472 FStar_Pervasives_Native.None
                        f1.FStar_Syntax_Syntax.pos
                       in
                    FStar_Util.Inr uu____9463  in
                  norm1 uu____9450  in
                let uu____9523 =
                  let uu____9526 = unembed eb b_tm  in uu____9526 w norm1  in
                match uu____9523 with
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
                let uu____9650 = FStar_List.splitAt n_tvars args  in
                match uu____9650 with
                | (_tvar_args,rest_args) ->
                    let uu____9759 = FStar_List.hd rest_args  in
                    (match uu____9759 with
                     | (x,uu____9791) ->
                         let shadow_app =
                           let uu____9817 =
                             FStar_Common.mk_thunk
                               (fun uu____9832  ->
                                  let uu____9833 =
                                    let uu____9838 =
                                      norm1 (FStar_Util.Inl fv_lid1)  in
                                    FStar_Syntax_Syntax.mk_Tm_app uu____9838
                                      args
                                     in
                                  uu____9833 FStar_Pervasives_Native.None rng)
                              in
                           FStar_Pervasives_Native.Some uu____9817  in
                         let uu____9861 =
                           let uu____9868 =
                             let uu____9871 = unembed ea x  in
                             uu____9871 true norm1  in
                           FStar_Util.map_opt uu____9868
                             (fun x1  ->
                                let uu____9886 =
                                  let uu____9893 = f x1  in
                                  embed eb uu____9893  in
                                uu____9886 rng shadow_app norm1)
                            in
                         (match uu____9861 with
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
                  let uu____10053 = FStar_List.splitAt n_tvars args  in
                  match uu____10053 with
                  | (_tvar_args,rest_args) ->
                      let uu____10148 = FStar_List.hd rest_args  in
                      (match uu____10148 with
                       | (x,uu____10176) ->
                           let uu____10189 =
                             let uu____10200 = FStar_List.tl rest_args  in
                             FStar_List.hd uu____10200  in
                           (match uu____10189 with
                            | (y,uu____10240) ->
                                let shadow_app =
                                  let uu____10262 =
                                    FStar_Common.mk_thunk
                                      (fun uu____10277  ->
                                         let uu____10278 =
                                           let uu____10283 =
                                             norm1 (FStar_Util.Inl fv_lid1)
                                              in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____10283 args
                                            in
                                         uu____10278
                                           FStar_Pervasives_Native.None rng)
                                     in
                                  FStar_Pervasives_Native.Some uu____10262
                                   in
                                let uu____10306 =
                                  let uu____10313 =
                                    let uu____10316 = unembed ea x  in
                                    uu____10316 true norm1  in
                                  FStar_Util.bind_opt uu____10313
                                    (fun x1  ->
                                       let uu____10331 =
                                         let uu____10334 = unembed eb y  in
                                         uu____10334 true norm1  in
                                       FStar_Util.bind_opt uu____10331
                                         (fun y1  ->
                                            let uu____10349 =
                                              let uu____10358 =
                                                let uu____10365 = f x1 y1  in
                                                embed ec uu____10365  in
                                              uu____10358 rng shadow_app
                                                norm1
                                               in
                                            FStar_Pervasives_Native.Some
                                              uu____10349))
                                   in
                                (match uu____10306 with
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
                    let uu____10555 = FStar_List.splitAt n_tvars args  in
                    match uu____10555 with
                    | (_tvar_args,rest_args) ->
                        let uu____10650 = FStar_List.hd rest_args  in
                        (match uu____10650 with
                         | (x,uu____10678) ->
                             let uu____10691 =
                               let uu____10702 = FStar_List.tl rest_args  in
                               FStar_List.hd uu____10702  in
                             (match uu____10691 with
                              | (y,uu____10742) ->
                                  let uu____10755 =
                                    let uu____10766 =
                                      let uu____10779 =
                                        FStar_List.tl rest_args  in
                                      FStar_List.tl uu____10779  in
                                    FStar_List.hd uu____10766  in
                                  (match uu____10755 with
                                   | (z,uu____10829) ->
                                       let shadow_app =
                                         let uu____10851 =
                                           FStar_Common.mk_thunk
                                             (fun uu____10866  ->
                                                let uu____10867 =
                                                  let uu____10872 =
                                                    norm1
                                                      (FStar_Util.Inl fv_lid1)
                                                     in
                                                  FStar_Syntax_Syntax.mk_Tm_app
                                                    uu____10872 args
                                                   in
                                                uu____10867
                                                  FStar_Pervasives_Native.None
                                                  rng)
                                            in
                                         FStar_Pervasives_Native.Some
                                           uu____10851
                                          in
                                       let uu____10895 =
                                         let uu____10902 =
                                           let uu____10905 = unembed ea x  in
                                           uu____10905 true norm1  in
                                         FStar_Util.bind_opt uu____10902
                                           (fun x1  ->
                                              let uu____10920 =
                                                let uu____10923 =
                                                  unembed eb y  in
                                                uu____10923 true norm1  in
                                              FStar_Util.bind_opt uu____10920
                                                (fun y1  ->
                                                   let uu____10938 =
                                                     let uu____10941 =
                                                       unembed ec z  in
                                                     uu____10941 true norm1
                                                      in
                                                   FStar_Util.bind_opt
                                                     uu____10938
                                                     (fun z1  ->
                                                        let uu____10956 =
                                                          let uu____10965 =
                                                            let uu____10972 =
                                                              f x1 y1 z1  in
                                                            embed ed
                                                              uu____10972
                                                             in
                                                          uu____10965 rng
                                                            shadow_app norm1
                                                           in
                                                        FStar_Pervasives_Native.Some
                                                          uu____10956)))
                                          in
                                       (match uu____10895 with
                                        | FStar_Pervasives_Native.Some x1 ->
                                            FStar_Pervasives_Native.Some x1
                                        | FStar_Pervasives_Native.None  ->
                                            force_shadow shadow_app))))
                     in
                  f_wrapped
  
let debug_wrap : 'a . Prims.string -> (unit -> 'a) -> 'a =
  fun s  ->
    fun f  ->
      (let uu____11026 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
       if uu____11026 then FStar_Util.print1 "++++starting %s\n" s else ());
      (let res = f ()  in
       (let uu____11055 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
        if uu____11055 then FStar_Util.print1 "------ending %s\n" s else ());
       res)
  