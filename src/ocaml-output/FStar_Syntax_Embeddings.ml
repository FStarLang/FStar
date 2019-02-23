open Prims
type norm_cb =
  (FStar_Ident.lid,FStar_Syntax_Syntax.term) FStar_Util.either ->
    FStar_Syntax_Syntax.term
let (id_norm_cb : norm_cb) =
  fun uu___429_55234  ->
    match uu___429_55234 with
    | FStar_Util.Inr x -> x
    | FStar_Util.Inl l ->
        let uu____55241 =
          FStar_Syntax_Syntax.lid_as_fv l
            FStar_Syntax_Syntax.delta_equational FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.fv_to_tm uu____55241
  
exception Embedding_failure 
let (uu___is_Embedding_failure : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Embedding_failure  -> true | uu____55251 -> false
  
exception Unembedding_failure 
let (uu___is_Unembedding_failure : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Unembedding_failure  -> true
    | uu____55262 -> false
  
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
             (fun uu____55428  ->
                let uu____55429 = FStar_Common.force_thunk s1  in
                f uu____55429))
  
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
  'Auu____56063 . FStar_Syntax_Syntax.term -> 'Auu____56063 -> Prims.string =
  fun typ  ->
    fun uu____56074  ->
      let uu____56075 = FStar_Syntax_Print.term_to_string typ  in
      FStar_Util.format1 "unknown %s" uu____56075
  
let (term_as_fv : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.fv) =
  fun t  ->
    let uu____56084 =
      let uu____56085 = FStar_Syntax_Subst.compress t  in
      uu____56085.FStar_Syntax_Syntax.n  in
    match uu____56084 with
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv
    | uu____56089 ->
        let uu____56090 =
          let uu____56092 = FStar_Syntax_Print.term_to_string t  in
          FStar_Util.format1 "Embeddings not defined for type %s" uu____56092
           in
        failwith uu____56090
  
let mk_emb :
  'a .
    'a raw_embedder ->
      'a raw_unembedder -> FStar_Syntax_Syntax.fv -> 'a embedding
  =
  fun em  ->
    fun un  ->
      fun fv  ->
        let typ = FStar_Syntax_Syntax.fv_to_tm fv  in
        let uu____56220 =
          let uu____56221 =
            let uu____56229 =
              let uu____56231 = FStar_Syntax_Syntax.lid_of_fv fv  in
              FStar_All.pipe_right uu____56231 FStar_Ident.string_of_lid  in
            (uu____56229, [])  in
          FStar_Syntax_Syntax.ET_app uu____56221  in
        { em; un; typ; print = (unknown_printer typ); emb_typ = uu____56220 }
  
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
    fun t  ->
      fun n1  -> let uu____56641 = unembed e t  in uu____56641 true n1
  
let try_unembed :
  'a .
    'a embedding ->
      FStar_Syntax_Syntax.term ->
        norm_cb -> 'a FStar_Pervasives_Native.option
  =
  fun e  ->
    fun t  ->
      fun n1  -> let uu____56690 = unembed e t  in uu____56690 false n1
  
let type_of : 'a . 'a embedding -> FStar_Syntax_Syntax.typ = fun e  -> e.typ 
let set_type : 'a . FStar_Syntax_Syntax.typ -> 'a embedding -> 'a embedding =
  fun ty  ->
    fun e  ->
      let uu___508_56743 = e  in
      {
        em = (uu___508_56743.em);
        un = (uu___508_56743.un);
        typ = ty;
        print = (uu___508_56743.print);
        emb_typ = (uu___508_56743.emb_typ)
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
              (let uu____56812 =
                 FStar_ST.op_Bang FStar_Options.debug_embedding  in
               if uu____56812
               then
                 let uu____56836 = FStar_Syntax_Print.term_to_string ta  in
                 let uu____56838 = FStar_Syntax_Print.emb_typ_to_string et
                    in
                 let uu____56840 = pa x  in
                 FStar_Util.print3
                   "Embedding a %s\n\temb_typ=%s\n\tvalue is %s\n"
                   uu____56836 uu____56838 uu____56840
               else ());
              (let uu____56847 =
                 FStar_ST.op_Bang FStar_Options.eager_embedding  in
               if uu____56847
               then f ()
               else
                 (let thunk1 = FStar_Common.mk_thunk f  in
                  let uu____56882 =
                    let uu____56889 =
                      let uu____56890 =
                        let uu____56891 = FStar_Dyn.mkdyn x  in
                        {
                          FStar_Syntax_Syntax.blob = uu____56891;
                          FStar_Syntax_Syntax.lkind =
                            (FStar_Syntax_Syntax.Lazy_embedding (et, thunk1));
                          FStar_Syntax_Syntax.ltyp = FStar_Syntax_Syntax.tun;
                          FStar_Syntax_Syntax.rng = rng
                        }  in
                      FStar_Syntax_Syntax.Tm_lazy uu____56890  in
                    FStar_Syntax_Syntax.mk uu____56889  in
                  uu____56882 FStar_Pervasives_Native.None rng))
  
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
                  FStar_Syntax_Syntax.ltyp = uu____57007;
                  FStar_Syntax_Syntax.rng = uu____57008;_}
                ->
                let uu____57019 =
                  (et <> et') ||
                    (FStar_ST.op_Bang FStar_Options.eager_embedding)
                   in
                if uu____57019
                then
                  let res =
                    let uu____57048 = FStar_Common.force_thunk t  in
                    f uu____57048  in
                  ((let uu____57092 =
                      FStar_ST.op_Bang FStar_Options.debug_embedding  in
                    if uu____57092
                    then
                      let uu____57116 =
                        FStar_Syntax_Print.emb_typ_to_string et  in
                      let uu____57118 =
                        FStar_Syntax_Print.emb_typ_to_string et'  in
                      let uu____57120 =
                        match res with
                        | FStar_Pervasives_Native.None  -> "None"
                        | FStar_Pervasives_Native.Some x2 ->
                            let uu____57125 = pa x2  in
                            Prims.op_Hat "Some " uu____57125
                         in
                      FStar_Util.print3
                        "Unembed cancellation failed\n\t%s <> %s\nvalue is %s\n"
                        uu____57116 uu____57118 uu____57120
                    else ());
                   res)
                else
                  (let a = FStar_Dyn.undyn b  in
                   (let uu____57137 =
                      FStar_ST.op_Bang FStar_Options.debug_embedding  in
                    if uu____57137
                    then
                      let uu____57161 =
                        FStar_Syntax_Print.emb_typ_to_string et  in
                      let uu____57163 = pa a  in
                      FStar_Util.print2
                        "Unembed cancelled for %s\n\tvalue is %s\n"
                        uu____57161 uu____57163
                    else ());
                   FStar_Pervasives_Native.Some a)
            | uu____57170 ->
                let aopt = f x1  in
                ((let uu____57175 =
                    FStar_ST.op_Bang FStar_Options.debug_embedding  in
                  if uu____57175
                  then
                    let uu____57199 = FStar_Syntax_Print.emb_typ_to_string et
                       in
                    let uu____57201 = FStar_Syntax_Print.term_to_string x1
                       in
                    let uu____57203 =
                      match aopt with
                      | FStar_Pervasives_Native.None  -> "None"
                      | FStar_Pervasives_Native.Some a ->
                          let uu____57208 = pa a  in
                          Prims.op_Hat "Some " uu____57208
                       in
                    FStar_Util.print3
                      "Unembedding:\n\temb_typ=%s\n\tterm is %s\n\tvalue is %s\n"
                      uu____57199 uu____57201 uu____57203
                  else ());
                 aopt)
  
let (mk_any_emb :
  FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term embedding) =
  fun typ  ->
    let em t _r _topt _norm =
      (let uu____57288 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
       if uu____57288
       then
         let uu____57312 = unknown_printer typ t  in
         FStar_Util.print1 "Embedding abstract: %s\n" uu____57312
       else ());
      t  in
    let un t _w _n =
      (let uu____57342 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
       if uu____57342
       then
         let uu____57366 = unknown_printer typ t  in
         FStar_Util.print1 "Unembedding abstract: %s\n" uu____57366
       else ());
      FStar_Pervasives_Native.Some t  in
    mk_emb_full em un typ (unknown_printer typ)
      FStar_Syntax_Syntax.ET_abstract
  
let (e_any : FStar_Syntax_Syntax.term embedding) =
  let em t _r _topt _norm = t  in
  let un t _w _n = FStar_Pervasives_Native.Some t  in
  let uu____57461 =
    let uu____57462 =
      let uu____57470 =
        FStar_All.pipe_right FStar_Parser_Const.term_lid
          FStar_Ident.string_of_lid
         in
      (uu____57470, [])  in
    FStar_Syntax_Syntax.ET_app uu____57462  in
  mk_emb_full em un FStar_Syntax_Syntax.t_term
    FStar_Syntax_Print.term_to_string uu____57461
  
let (e_unit : unit embedding) =
  let em u rng _topt _norm =
    let uu___582_57542 = FStar_Syntax_Util.exp_unit  in
    {
      FStar_Syntax_Syntax.n = (uu___582_57542.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___582_57542.FStar_Syntax_Syntax.vars)
    }  in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unascribe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit ) ->
        FStar_Pervasives_Native.Some ()
    | uu____57572 ->
        (if w
         then
           (let uu____57575 =
              let uu____57581 =
                let uu____57583 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded unit: %s" uu____57583  in
              (FStar_Errors.Warning_NotEmbedded, uu____57581)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____57575)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____57589 =
    let uu____57590 =
      let uu____57598 =
        FStar_All.pipe_right FStar_Parser_Const.unit_lid
          FStar_Ident.string_of_lid
         in
      (uu____57598, [])  in
    FStar_Syntax_Syntax.ET_app uu____57590  in
  mk_emb_full em un FStar_Syntax_Syntax.t_unit (fun uu____57605  -> "()")
    uu____57589
  
let (e_bool : Prims.bool embedding) =
  let em b rng _topt _norm =
    let t =
      if b
      then FStar_Syntax_Util.exp_true_bool
      else FStar_Syntax_Util.exp_false_bool  in
    let uu___602_57684 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___602_57684.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___602_57684.FStar_Syntax_Syntax.vars)
    }  in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) ->
        FStar_Pervasives_Native.Some b
    | uu____57722 ->
        (if w
         then
           (let uu____57725 =
              let uu____57731 =
                let uu____57733 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded bool: %s" uu____57733  in
              (FStar_Errors.Warning_NotEmbedded, uu____57731)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____57725)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____57740 =
    let uu____57741 =
      let uu____57749 =
        FStar_All.pipe_right FStar_Parser_Const.bool_lid
          FStar_Ident.string_of_lid
         in
      (uu____57749, [])  in
    FStar_Syntax_Syntax.ET_app uu____57741  in
  mk_emb_full em un FStar_Syntax_Syntax.t_bool FStar_Util.string_of_bool
    uu____57740
  
let (e_char : FStar_Char.char embedding) =
  let em c rng _topt _norm =
    let t = FStar_Syntax_Util.exp_char c  in
    let uu___621_57826 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___621_57826.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___621_57826.FStar_Syntax_Syntax.vars)
    }  in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c) ->
        FStar_Pervasives_Native.Some c
    | uu____57862 ->
        (if w
         then
           (let uu____57865 =
              let uu____57871 =
                let uu____57873 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded char: %s" uu____57873  in
              (FStar_Errors.Warning_NotEmbedded, uu____57871)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____57865)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____57880 =
    let uu____57881 =
      let uu____57889 =
        FStar_All.pipe_right FStar_Parser_Const.char_lid
          FStar_Ident.string_of_lid
         in
      (uu____57889, [])  in
    FStar_Syntax_Syntax.ET_app uu____57881  in
  mk_emb_full em un FStar_Syntax_Syntax.t_char FStar_Util.string_of_char
    uu____57880
  
let (e_int : FStar_BigInt.t embedding) =
  let t_int1 = FStar_Syntax_Util.fvar_const FStar_Parser_Const.int_lid  in
  let emb_t_int =
    let uu____57901 =
      let uu____57909 =
        FStar_All.pipe_right FStar_Parser_Const.int_lid
          FStar_Ident.string_of_lid
         in
      (uu____57909, [])  in
    FStar_Syntax_Syntax.ET_app uu____57901  in
  let em i rng _topt _norm =
    lazy_embed FStar_BigInt.string_of_big_int emb_t_int rng t_int1 i
      (fun uu____57980  ->
         let uu____57981 = FStar_BigInt.string_of_big_int i  in
         FStar_Syntax_Util.exp_int uu____57981)
     in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    lazy_unembed FStar_BigInt.string_of_big_int emb_t_int t t_int1
      (fun t1  ->
         match t1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
             (s,uu____58018)) ->
             let uu____58033 = FStar_BigInt.big_int_of_string s  in
             FStar_Pervasives_Native.Some uu____58033
         | uu____58034 ->
             (if w
              then
                (let uu____58037 =
                   let uu____58043 =
                     let uu____58045 = FStar_Syntax_Print.term_to_string t0
                        in
                     FStar_Util.format1 "Not an embedded int: %s" uu____58045
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____58043)  in
                 FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                   uu____58037)
              else ();
              FStar_Pervasives_Native.None))
     in
  mk_emb_full em un FStar_Syntax_Syntax.t_int FStar_BigInt.string_of_big_int
    emb_t_int
  
let (e_string : Prims.string embedding) =
  let emb_t_string =
    let uu____58056 =
      let uu____58064 =
        FStar_All.pipe_right FStar_Parser_Const.string_lid
          FStar_Ident.string_of_lid
         in
      (uu____58064, [])  in
    FStar_Syntax_Syntax.ET_app uu____58056  in
  let em s rng _topt _norm =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, rng)))
      FStar_Pervasives_Native.None rng
     in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
        (s,uu____58169)) -> FStar_Pervasives_Native.Some s
    | uu____58173 ->
        (if w
         then
           (let uu____58176 =
              let uu____58182 =
                let uu____58184 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded string: %s" uu____58184
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____58182)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____58176)
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
      let uu____58220 =
        let uu____58225 =
          let uu____58226 = FStar_Syntax_Syntax.as_arg ea.typ  in
          [uu____58226]  in
        FStar_Syntax_Syntax.mk_Tm_app t_opt uu____58225  in
      uu____58220 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
    let emb_t_option_a =
      let uu____58254 =
        let uu____58262 =
          FStar_All.pipe_right FStar_Parser_Const.option_lid
            FStar_Ident.string_of_lid
           in
        (uu____58262, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____58254  in
    let printer uu___430_58276 =
      match uu___430_58276 with
      | FStar_Pervasives_Native.None  -> "None"
      | FStar_Pervasives_Native.Some x ->
          let uu____58282 =
            let uu____58284 = ea.print x  in Prims.op_Hat uu____58284 ")"  in
          Prims.op_Hat "(Some " uu____58282
       in
    let em o rng topt norm1 =
      lazy_embed printer emb_t_option_a rng t_option_a o
        (fun uu____58361  ->
           match o with
           | FStar_Pervasives_Native.None  ->
               let uu____58362 =
                 let uu____58367 =
                   let uu____58368 =
                     FStar_Syntax_Syntax.tdataconstr
                       FStar_Parser_Const.none_lid
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____58368
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 let uu____58369 =
                   let uu____58370 =
                     let uu____58379 = type_of ea  in
                     FStar_Syntax_Syntax.iarg uu____58379  in
                   [uu____58370]  in
                 FStar_Syntax_Syntax.mk_Tm_app uu____58367 uu____58369  in
               uu____58362 FStar_Pervasives_Native.None rng
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
                        let uu____58470 =
                          FStar_Syntax_Syntax.lid_as_fv some_v
                            FStar_Syntax_Syntax.delta_equational
                            FStar_Pervasives_Native.None
                           in
                        FStar_Syntax_Syntax.fv_to_tm uu____58470  in
                      let uu____58471 =
                        let uu____58476 =
                          FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm
                            [FStar_Syntax_Syntax.U_zero]
                           in
                        let uu____58477 =
                          let uu____58478 =
                            let uu____58487 = type_of ea  in
                            FStar_Syntax_Syntax.iarg uu____58487  in
                          let uu____58488 =
                            let uu____58499 = FStar_Syntax_Syntax.as_arg t
                               in
                            [uu____58499]  in
                          uu____58478 :: uu____58488  in
                        FStar_Syntax_Syntax.mk_Tm_app uu____58476 uu____58477
                         in
                      uu____58471 FStar_Pervasives_Native.None rng)
                  in
               let uu____58534 =
                 let uu____58539 =
                   let uu____58540 =
                     FStar_Syntax_Syntax.tdataconstr
                       FStar_Parser_Const.some_lid
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____58540
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 let uu____58541 =
                   let uu____58542 =
                     let uu____58551 = type_of ea  in
                     FStar_Syntax_Syntax.iarg uu____58551  in
                   let uu____58552 =
                     let uu____58563 =
                       let uu____58572 =
                         let uu____58573 = embed ea a  in
                         uu____58573 rng shadow_a norm1  in
                       FStar_Syntax_Syntax.as_arg uu____58572  in
                     [uu____58563]  in
                   uu____58542 :: uu____58552  in
                 FStar_Syntax_Syntax.mk_Tm_app uu____58539 uu____58541  in
               uu____58534 FStar_Pervasives_Native.None rng)
       in
    let un t0 w norm1 =
      let t = FStar_Syntax_Util.unmeta_safe t0  in
      lazy_unembed printer emb_t_option_a t t_option_a
        (fun t1  ->
           let uu____58710 = FStar_Syntax_Util.head_and_args' t1  in
           match uu____58710 with
           | (hd1,args) ->
               let uu____58751 =
                 let uu____58766 =
                   let uu____58767 = FStar_Syntax_Util.un_uinst hd1  in
                   uu____58767.FStar_Syntax_Syntax.n  in
                 (uu____58766, args)  in
               (match uu____58751 with
                | (FStar_Syntax_Syntax.Tm_fvar fv,uu____58785) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.none_lid
                    ->
                    FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,uu____58809::(a,uu____58811)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.some_lid
                    ->
                    let uu____58862 =
                      let uu____58865 = unembed ea a  in uu____58865 w norm1
                       in
                    FStar_Util.bind_opt uu____58862
                      (fun a1  ->
                         FStar_Pervasives_Native.Some
                           (FStar_Pervasives_Native.Some a1))
                | uu____58884 ->
                    (if w
                     then
                       (let uu____58901 =
                          let uu____58907 =
                            let uu____58909 =
                              FStar_Syntax_Print.term_to_string t0  in
                            FStar_Util.format1 "Not an embedded option: %s"
                              uu____58909
                             in
                          (FStar_Errors.Warning_NotEmbedded, uu____58907)  in
                        FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                          uu____58901)
                     else ();
                     FStar_Pervasives_Native.None)))
       in
    let uu____58917 =
      let uu____58918 = type_of ea  in
      FStar_Syntax_Syntax.t_option_of uu____58918  in
    mk_emb_full em un uu____58917 printer emb_t_option_a
  
let e_tuple2 : 'a 'b . 'a embedding -> 'b embedding -> ('a * 'b) embedding =
  fun ea  ->
    fun eb  ->
      let t_pair_a_b =
        let t_tup2 =
          FStar_Syntax_Util.fvar_const FStar_Parser_Const.lid_tuple2  in
        let uu____58960 =
          let uu____58965 =
            let uu____58966 = FStar_Syntax_Syntax.as_arg ea.typ  in
            let uu____58975 =
              let uu____58986 = FStar_Syntax_Syntax.as_arg eb.typ  in
              [uu____58986]  in
            uu____58966 :: uu____58975  in
          FStar_Syntax_Syntax.mk_Tm_app t_tup2 uu____58965  in
        uu____58960 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
      let emb_t_pair_a_b =
        let uu____59022 =
          let uu____59030 =
            FStar_All.pipe_right FStar_Parser_Const.lid_tuple2
              FStar_Ident.string_of_lid
             in
          (uu____59030, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____59022  in
      let printer uu____59046 =
        match uu____59046 with
        | (x,y) ->
            let uu____59054 = ea.print x  in
            let uu____59056 = eb.print y  in
            FStar_Util.format2 "(%s, %s)" uu____59054 uu____59056
         in
      let em x rng topt norm1 =
        lazy_embed printer emb_t_pair_a_b rng t_pair_a_b x
          (fun uu____59141  ->
             let proj i ab =
               let uu____59157 =
                 let uu____59162 =
                   FStar_Parser_Const.mk_tuple_data_lid (Prims.parse_int "2")
                     rng
                    in
                 let uu____59164 =
                   FStar_Syntax_Syntax.null_bv FStar_Syntax_Syntax.tun  in
                 FStar_Syntax_Util.mk_field_projector_name uu____59162
                   uu____59164 i
                  in
               match uu____59157 with
               | (proj_1,uu____59168) ->
                   let proj_1_tm =
                     let uu____59170 =
                       FStar_Syntax_Syntax.lid_as_fv proj_1
                         FStar_Syntax_Syntax.delta_equational
                         FStar_Pervasives_Native.None
                        in
                     FStar_Syntax_Syntax.fv_to_tm uu____59170  in
                   let uu____59171 =
                     let uu____59176 =
                       FStar_Syntax_Syntax.mk_Tm_uinst proj_1_tm
                         [FStar_Syntax_Syntax.U_zero]
                        in
                     let uu____59177 =
                       let uu____59178 =
                         let uu____59187 = type_of ea  in
                         FStar_Syntax_Syntax.iarg uu____59187  in
                       let uu____59188 =
                         let uu____59199 =
                           let uu____59208 = type_of eb  in
                           FStar_Syntax_Syntax.iarg uu____59208  in
                         let uu____59209 =
                           let uu____59220 = FStar_Syntax_Syntax.as_arg ab
                              in
                           [uu____59220]  in
                         uu____59199 :: uu____59209  in
                       uu____59178 :: uu____59188  in
                     FStar_Syntax_Syntax.mk_Tm_app uu____59176 uu____59177
                      in
                   uu____59171 FStar_Pervasives_Native.None rng
                in
             let shadow_a = map_shadow topt (proj (Prims.parse_int "1"))  in
             let shadow_b = map_shadow topt (proj (Prims.parse_int "2"))  in
             let uu____59381 =
               let uu____59386 =
                 let uu____59387 =
                   FStar_Syntax_Syntax.tdataconstr
                     FStar_Parser_Const.lid_Mktuple2
                    in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu____59387
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                  in
               let uu____59388 =
                 let uu____59389 =
                   let uu____59398 = type_of ea  in
                   FStar_Syntax_Syntax.iarg uu____59398  in
                 let uu____59399 =
                   let uu____59410 =
                     let uu____59419 = type_of eb  in
                     FStar_Syntax_Syntax.iarg uu____59419  in
                   let uu____59420 =
                     let uu____59431 =
                       let uu____59440 =
                         let uu____59441 =
                           embed ea (FStar_Pervasives_Native.fst x)  in
                         uu____59441 rng shadow_a norm1  in
                       FStar_Syntax_Syntax.as_arg uu____59440  in
                     let uu____59511 =
                       let uu____59522 =
                         let uu____59531 =
                           let uu____59532 =
                             embed eb (FStar_Pervasives_Native.snd x)  in
                           uu____59532 rng shadow_b norm1  in
                         FStar_Syntax_Syntax.as_arg uu____59531  in
                       [uu____59522]  in
                     uu____59431 :: uu____59511  in
                   uu____59410 :: uu____59420  in
                 uu____59389 :: uu____59399  in
               FStar_Syntax_Syntax.mk_Tm_app uu____59386 uu____59388  in
             uu____59381 FStar_Pervasives_Native.None rng)
         in
      let un t0 w norm1 =
        let t = FStar_Syntax_Util.unmeta_safe t0  in
        lazy_unembed printer emb_t_pair_a_b t t_pair_a_b
          (fun t1  ->
             let uu____59697 = FStar_Syntax_Util.head_and_args' t1  in
             match uu____59697 with
             | (hd1,args) ->
                 let uu____59740 =
                   let uu____59753 =
                     let uu____59754 = FStar_Syntax_Util.un_uinst hd1  in
                     uu____59754.FStar_Syntax_Syntax.n  in
                   (uu____59753, args)  in
                 (match uu____59740 with
                  | (FStar_Syntax_Syntax.Tm_fvar
                     fv,uu____59772::uu____59773::(a,uu____59775)::(b,uu____59777)::[])
                      when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.lid_Mktuple2
                      ->
                      let uu____59836 =
                        let uu____59839 = unembed ea a  in
                        uu____59839 w norm1  in
                      FStar_Util.bind_opt uu____59836
                        (fun a1  ->
                           let uu____59859 =
                             let uu____59862 = unembed eb b  in
                             uu____59862 w norm1  in
                           FStar_Util.bind_opt uu____59859
                             (fun b1  ->
                                FStar_Pervasives_Native.Some (a1, b1)))
                  | uu____59885 ->
                      (if w
                       then
                         (let uu____59900 =
                            let uu____59906 =
                              let uu____59908 =
                                FStar_Syntax_Print.term_to_string t0  in
                              FStar_Util.format1 "Not an embedded pair: %s"
                                uu____59908
                               in
                            (FStar_Errors.Warning_NotEmbedded, uu____59906)
                             in
                          FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                            uu____59900)
                       else ();
                       FStar_Pervasives_Native.None)))
         in
      let uu____59918 =
        let uu____59919 = type_of ea  in
        let uu____59920 = type_of eb  in
        FStar_Syntax_Syntax.t_tuple2_of uu____59919 uu____59920  in
      mk_emb_full em un uu____59918 printer emb_t_pair_a_b
  
let e_either :
  'a 'b . 'a embedding -> 'b embedding -> ('a,'b) FStar_Util.either embedding
  =
  fun ea  ->
    fun eb  ->
      let t_sum_a_b =
        let t_either =
          FStar_Syntax_Util.fvar_const FStar_Parser_Const.either_lid  in
        let uu____59964 =
          let uu____59969 =
            let uu____59970 = FStar_Syntax_Syntax.as_arg ea.typ  in
            let uu____59979 =
              let uu____59990 = FStar_Syntax_Syntax.as_arg eb.typ  in
              [uu____59990]  in
            uu____59970 :: uu____59979  in
          FStar_Syntax_Syntax.mk_Tm_app t_either uu____59969  in
        uu____59964 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
      let emb_t_sum_a_b =
        let uu____60026 =
          let uu____60034 =
            FStar_All.pipe_right FStar_Parser_Const.either_lid
              FStar_Ident.string_of_lid
             in
          (uu____60034, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____60026  in
      let printer s =
        match s with
        | FStar_Util.Inl a ->
            let uu____60057 = ea.print a  in
            FStar_Util.format1 "Inl %s" uu____60057
        | FStar_Util.Inr b ->
            let uu____60061 = eb.print b  in
            FStar_Util.format1 "Inr %s" uu____60061
         in
      let em s rng topt norm1 =
        lazy_embed printer emb_t_sum_a_b rng t_sum_a_b s
          (match s with
           | FStar_Util.Inl a ->
               (fun uu____60149  ->
                  let shadow_a =
                    map_shadow topt
                      (fun t  ->
                         let v1 = FStar_Ident.mk_ident ("v", rng)  in
                         let some_v =
                           FStar_Syntax_Util.mk_field_projector_name_from_ident
                             FStar_Parser_Const.inl_lid v1
                            in
                         let some_v_tm =
                           let uu____60221 =
                             FStar_Syntax_Syntax.lid_as_fv some_v
                               FStar_Syntax_Syntax.delta_equational
                               FStar_Pervasives_Native.None
                              in
                           FStar_Syntax_Syntax.fv_to_tm uu____60221  in
                         let uu____60222 =
                           let uu____60227 =
                             FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm
                               [FStar_Syntax_Syntax.U_zero]
                              in
                           let uu____60228 =
                             let uu____60229 =
                               let uu____60238 = type_of ea  in
                               FStar_Syntax_Syntax.iarg uu____60238  in
                             let uu____60239 =
                               let uu____60250 =
                                 let uu____60259 = type_of eb  in
                                 FStar_Syntax_Syntax.iarg uu____60259  in
                               let uu____60260 =
                                 let uu____60271 =
                                   FStar_Syntax_Syntax.as_arg t  in
                                 [uu____60271]  in
                               uu____60250 :: uu____60260  in
                             uu____60229 :: uu____60239  in
                           FStar_Syntax_Syntax.mk_Tm_app uu____60227
                             uu____60228
                            in
                         uu____60222 FStar_Pervasives_Native.None rng)
                     in
                  let uu____60314 =
                    let uu____60319 =
                      let uu____60320 =
                        FStar_Syntax_Syntax.tdataconstr
                          FStar_Parser_Const.inl_lid
                         in
                      FStar_Syntax_Syntax.mk_Tm_uinst uu____60320
                        [FStar_Syntax_Syntax.U_zero;
                        FStar_Syntax_Syntax.U_zero]
                       in
                    let uu____60321 =
                      let uu____60322 =
                        let uu____60331 = type_of ea  in
                        FStar_Syntax_Syntax.iarg uu____60331  in
                      let uu____60332 =
                        let uu____60343 =
                          let uu____60352 = type_of eb  in
                          FStar_Syntax_Syntax.iarg uu____60352  in
                        let uu____60353 =
                          let uu____60364 =
                            let uu____60373 =
                              let uu____60374 = embed ea a  in
                              uu____60374 rng shadow_a norm1  in
                            FStar_Syntax_Syntax.as_arg uu____60373  in
                          [uu____60364]  in
                        uu____60343 :: uu____60353  in
                      uu____60322 :: uu____60332  in
                    FStar_Syntax_Syntax.mk_Tm_app uu____60319 uu____60321  in
                  uu____60314 FStar_Pervasives_Native.None rng)
           | FStar_Util.Inr b ->
               (fun uu____60479  ->
                  let shadow_b =
                    map_shadow topt
                      (fun t  ->
                         let v1 = FStar_Ident.mk_ident ("v", rng)  in
                         let some_v =
                           FStar_Syntax_Util.mk_field_projector_name_from_ident
                             FStar_Parser_Const.inr_lid v1
                            in
                         let some_v_tm =
                           let uu____60551 =
                             FStar_Syntax_Syntax.lid_as_fv some_v
                               FStar_Syntax_Syntax.delta_equational
                               FStar_Pervasives_Native.None
                              in
                           FStar_Syntax_Syntax.fv_to_tm uu____60551  in
                         let uu____60552 =
                           let uu____60557 =
                             FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm
                               [FStar_Syntax_Syntax.U_zero]
                              in
                           let uu____60558 =
                             let uu____60559 =
                               let uu____60568 = type_of ea  in
                               FStar_Syntax_Syntax.iarg uu____60568  in
                             let uu____60569 =
                               let uu____60580 =
                                 let uu____60589 = type_of eb  in
                                 FStar_Syntax_Syntax.iarg uu____60589  in
                               let uu____60590 =
                                 let uu____60601 =
                                   FStar_Syntax_Syntax.as_arg t  in
                                 [uu____60601]  in
                               uu____60580 :: uu____60590  in
                             uu____60559 :: uu____60569  in
                           FStar_Syntax_Syntax.mk_Tm_app uu____60557
                             uu____60558
                            in
                         uu____60552 FStar_Pervasives_Native.None rng)
                     in
                  let uu____60644 =
                    let uu____60649 =
                      let uu____60650 =
                        FStar_Syntax_Syntax.tdataconstr
                          FStar_Parser_Const.inr_lid
                         in
                      FStar_Syntax_Syntax.mk_Tm_uinst uu____60650
                        [FStar_Syntax_Syntax.U_zero;
                        FStar_Syntax_Syntax.U_zero]
                       in
                    let uu____60651 =
                      let uu____60652 =
                        let uu____60661 = type_of ea  in
                        FStar_Syntax_Syntax.iarg uu____60661  in
                      let uu____60662 =
                        let uu____60673 =
                          let uu____60682 = type_of eb  in
                          FStar_Syntax_Syntax.iarg uu____60682  in
                        let uu____60683 =
                          let uu____60694 =
                            let uu____60703 =
                              let uu____60704 = embed eb b  in
                              uu____60704 rng shadow_b norm1  in
                            FStar_Syntax_Syntax.as_arg uu____60703  in
                          [uu____60694]  in
                        uu____60673 :: uu____60683  in
                      uu____60652 :: uu____60662  in
                    FStar_Syntax_Syntax.mk_Tm_app uu____60649 uu____60651  in
                  uu____60644 FStar_Pervasives_Native.None rng))
         in
      let un t0 w norm1 =
        let t = FStar_Syntax_Util.unmeta_safe t0  in
        lazy_unembed printer emb_t_sum_a_b t t_sum_a_b
          (fun t1  ->
             let uu____60859 = FStar_Syntax_Util.head_and_args' t1  in
             match uu____60859 with
             | (hd1,args) ->
                 let uu____60902 =
                   let uu____60917 =
                     let uu____60918 = FStar_Syntax_Util.un_uinst hd1  in
                     uu____60918.FStar_Syntax_Syntax.n  in
                   (uu____60917, args)  in
                 (match uu____60902 with
                  | (FStar_Syntax_Syntax.Tm_fvar
                     fv,uu____60938::uu____60939::(a,uu____60941)::[]) when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.inl_lid
                      ->
                      let uu____61008 =
                        let uu____61011 = unembed ea a  in
                        uu____61011 w norm1  in
                      FStar_Util.bind_opt uu____61008
                        (fun a1  ->
                           FStar_Pervasives_Native.Some (FStar_Util.Inl a1))
                  | (FStar_Syntax_Syntax.Tm_fvar
                     fv,uu____61035::uu____61036::(b,uu____61038)::[]) when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.inr_lid
                      ->
                      let uu____61105 =
                        let uu____61108 = unembed eb b  in
                        uu____61108 w norm1  in
                      FStar_Util.bind_opt uu____61105
                        (fun b1  ->
                           FStar_Pervasives_Native.Some (FStar_Util.Inr b1))
                  | uu____61131 ->
                      (if w
                       then
                         (let uu____61148 =
                            let uu____61154 =
                              let uu____61156 =
                                FStar_Syntax_Print.term_to_string t0  in
                              FStar_Util.format1 "Not an embedded sum: %s"
                                uu____61156
                               in
                            (FStar_Errors.Warning_NotEmbedded, uu____61154)
                             in
                          FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                            uu____61148)
                       else ();
                       FStar_Pervasives_Native.None)))
         in
      let uu____61166 =
        let uu____61167 = type_of ea  in
        let uu____61168 = type_of eb  in
        FStar_Syntax_Syntax.t_either_of uu____61167 uu____61168  in
      mk_emb_full em un uu____61166 printer emb_t_sum_a_b
  
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea  ->
    let t_list_a =
      let t_list = FStar_Syntax_Util.fvar_const FStar_Parser_Const.list_lid
         in
      let uu____61196 =
        let uu____61201 =
          let uu____61202 = FStar_Syntax_Syntax.as_arg ea.typ  in
          [uu____61202]  in
        FStar_Syntax_Syntax.mk_Tm_app t_list uu____61201  in
      uu____61196 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
    let emb_t_list_a =
      let uu____61230 =
        let uu____61238 =
          FStar_All.pipe_right FStar_Parser_Const.list_lid
            FStar_Ident.string_of_lid
           in
        (uu____61238, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____61230  in
    let printer l =
      let uu____61255 =
        let uu____61257 =
          let uu____61259 = FStar_List.map ea.print l  in
          FStar_All.pipe_right uu____61259 (FStar_String.concat "; ")  in
        Prims.op_Hat uu____61257 "]"  in
      Prims.op_Hat "[" uu____61255  in
    let rec em l rng shadow_l norm1 =
      lazy_embed printer emb_t_list_a rng t_list_a l
        (fun uu____61345  ->
           let t =
             let uu____61347 = type_of ea  in
             FStar_Syntax_Syntax.iarg uu____61347  in
           match l with
           | [] ->
               let uu____61348 =
                 let uu____61353 =
                   let uu____61354 =
                     FStar_Syntax_Syntax.tdataconstr
                       FStar_Parser_Const.nil_lid
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____61354
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 FStar_Syntax_Syntax.mk_Tm_app uu____61353 [t]  in
               uu____61348 FStar_Pervasives_Native.None rng
           | hd1::tl1 ->
               let cons1 =
                 let uu____61378 =
                   FStar_Syntax_Syntax.tdataconstr
                     FStar_Parser_Const.cons_lid
                    in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu____61378
                   [FStar_Syntax_Syntax.U_zero]
                  in
               let proj f cons_tm =
                 let fid = FStar_Ident.mk_ident (f, rng)  in
                 let proj =
                   FStar_Syntax_Util.mk_field_projector_name_from_ident
                     FStar_Parser_Const.cons_lid fid
                    in
                 let proj_tm =
                   let uu____61398 =
                     FStar_Syntax_Syntax.lid_as_fv proj
                       FStar_Syntax_Syntax.delta_equational
                       FStar_Pervasives_Native.None
                      in
                   FStar_Syntax_Syntax.fv_to_tm uu____61398  in
                 let uu____61399 =
                   let uu____61404 =
                     FStar_Syntax_Syntax.mk_Tm_uinst proj_tm
                       [FStar_Syntax_Syntax.U_zero]
                      in
                   let uu____61405 =
                     let uu____61406 =
                       let uu____61415 = type_of ea  in
                       FStar_Syntax_Syntax.iarg uu____61415  in
                     let uu____61416 =
                       let uu____61427 = FStar_Syntax_Syntax.as_arg cons_tm
                          in
                       [uu____61427]  in
                     uu____61406 :: uu____61416  in
                   FStar_Syntax_Syntax.mk_Tm_app uu____61404 uu____61405  in
                 uu____61399 FStar_Pervasives_Native.None rng  in
               let shadow_hd = map_shadow shadow_l (proj "hd")  in
               let shadow_tl = map_shadow shadow_l (proj "tl")  in
               let uu____61580 =
                 let uu____61585 =
                   let uu____61586 =
                     let uu____61597 =
                       let uu____61606 =
                         let uu____61607 = embed ea hd1  in
                         uu____61607 rng shadow_hd norm1  in
                       FStar_Syntax_Syntax.as_arg uu____61606  in
                     let uu____61677 =
                       let uu____61688 =
                         let uu____61697 = em tl1 rng shadow_tl norm1  in
                         FStar_Syntax_Syntax.as_arg uu____61697  in
                       [uu____61688]  in
                     uu____61597 :: uu____61677  in
                   t :: uu____61586  in
                 FStar_Syntax_Syntax.mk_Tm_app cons1 uu____61585  in
               uu____61580 FStar_Pervasives_Native.None rng)
       in
    let rec un t0 w norm1 =
      let t = FStar_Syntax_Util.unmeta_safe t0  in
      lazy_unembed printer emb_t_list_a t t_list_a
        (fun t1  ->
           let uu____61813 = FStar_Syntax_Util.head_and_args' t1  in
           match uu____61813 with
           | (hd1,args) ->
               let uu____61854 =
                 let uu____61867 =
                   let uu____61868 = FStar_Syntax_Util.un_uinst hd1  in
                   uu____61868.FStar_Syntax_Syntax.n  in
                 (uu____61867, args)  in
               (match uu____61854 with
                | (FStar_Syntax_Syntax.Tm_fvar fv,uu____61884) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.nil_lid
                    -> FStar_Pervasives_Native.Some []
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(uu____61904,FStar_Pervasives_Native.Some
                       (FStar_Syntax_Syntax.Implicit uu____61905))::(hd2,FStar_Pervasives_Native.None
                                                                    )::
                   (tl1,FStar_Pervasives_Native.None )::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.cons_lid
                    ->
                    let uu____61947 =
                      let uu____61950 = unembed ea hd2  in
                      uu____61950 w norm1  in
                    FStar_Util.bind_opt uu____61947
                      (fun hd3  ->
                         let uu____61968 = un tl1 w norm1  in
                         FStar_Util.bind_opt uu____61968
                           (fun tl2  ->
                              FStar_Pervasives_Native.Some (hd3 :: tl2)))
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(hd2,FStar_Pervasives_Native.None )::(tl1,FStar_Pervasives_Native.None
                                                            )::[])
                    when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.cons_lid
                    ->
                    let uu____62018 =
                      let uu____62021 = unembed ea hd2  in
                      uu____62021 w norm1  in
                    FStar_Util.bind_opt uu____62018
                      (fun hd3  ->
                         let uu____62039 = un tl1 w norm1  in
                         FStar_Util.bind_opt uu____62039
                           (fun tl2  ->
                              FStar_Pervasives_Native.Some (hd3 :: tl2)))
                | uu____62056 ->
                    (if w
                     then
                       (let uu____62071 =
                          let uu____62077 =
                            let uu____62079 =
                              FStar_Syntax_Print.term_to_string t0  in
                            FStar_Util.format1 "Not an embedded list: %s"
                              uu____62079
                             in
                          (FStar_Errors.Warning_NotEmbedded, uu____62077)  in
                        FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                          uu____62071)
                     else ();
                     FStar_Pervasives_Native.None)))
       in
    let uu____62087 =
      let uu____62088 = type_of ea  in
      FStar_Syntax_Syntax.t_list_of uu____62088  in
    mk_emb_full em un uu____62087 printer emb_t_list_a
  
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
    match projectee with | Simpl  -> true | uu____62131 -> false
  
let (uu___is_Weak : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Weak  -> true | uu____62142 -> false
  
let (uu___is_HNF : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | HNF  -> true | uu____62153 -> false
  
let (uu___is_Primops : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____62164 -> false
  
let (uu___is_Delta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Delta  -> true | uu____62175 -> false
  
let (uu___is_Zeta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Zeta  -> true | uu____62186 -> false
  
let (uu___is_Iota : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Iota  -> true | uu____62197 -> false
  
let (uu___is_Reify : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____62208 -> false
  
let (uu___is_UnfoldOnly : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____62223 -> false
  
let (__proj__UnfoldOnly__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldFully : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldFully _0 -> true | uu____62255 -> false
  
let (__proj__UnfoldFully__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldFully _0 -> _0 
let (uu___is_UnfoldAttr : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____62287 -> false
  
let (__proj__UnfoldAttr__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_NBE : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | NBE  -> true | uu____62315 -> false
  
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
    let uu____62333 =
      FStar_Ident.lid_of_str "FStar.Syntax.Embeddings.norm_step"  in
    FStar_Syntax_Util.fvar_const uu____62333  in
  let emb_t_norm_step =
    let uu____62336 =
      let uu____62344 =
        FStar_All.pipe_right FStar_Parser_Const.norm_step_lid
          FStar_Ident.string_of_lid
         in
      (uu____62344, [])  in
    FStar_Syntax_Syntax.ET_app uu____62336  in
  let printer uu____62356 = "norm_step"  in
  let em n1 rng _topt norm1 =
    lazy_embed printer emb_t_norm_step rng t_norm_step1 n1
      (fun uu____62422  ->
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
             let uu____62427 =
               let uu____62432 =
                 let uu____62433 =
                   let uu____62442 =
                     let uu____62443 =
                       let uu____62450 = e_list e_string  in
                       embed uu____62450 l  in
                     uu____62443 rng FStar_Pervasives_Native.None norm1  in
                   FStar_Syntax_Syntax.as_arg uu____62442  in
                 [uu____62433]  in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldOnly uu____62432  in
             uu____62427 FStar_Pervasives_Native.None rng
         | UnfoldFully l ->
             let uu____62509 =
               let uu____62514 =
                 let uu____62515 =
                   let uu____62524 =
                     let uu____62525 =
                       let uu____62532 = e_list e_string  in
                       embed uu____62532 l  in
                     uu____62525 rng FStar_Pervasives_Native.None norm1  in
                   FStar_Syntax_Syntax.as_arg uu____62524  in
                 [uu____62515]  in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldFully uu____62514
                in
             uu____62509 FStar_Pervasives_Native.None rng
         | UnfoldAttr l ->
             let uu____62591 =
               let uu____62596 =
                 let uu____62597 =
                   let uu____62606 =
                     let uu____62607 =
                       let uu____62614 = e_list e_string  in
                       embed uu____62614 l  in
                     uu____62607 rng FStar_Pervasives_Native.None norm1  in
                   FStar_Syntax_Syntax.as_arg uu____62606  in
                 [uu____62597]  in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldAttr uu____62596  in
             uu____62591 FStar_Pervasives_Native.None rng)
     in
  let un t0 w norm1 =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    lazy_unembed printer emb_t_norm_step t t_norm_step1
      (fun t1  ->
         let uu____62703 = FStar_Syntax_Util.head_and_args t1  in
         match uu____62703 with
         | (hd1,args) ->
             let uu____62748 =
               let uu____62763 =
                 let uu____62764 = FStar_Syntax_Util.un_uinst hd1  in
                 uu____62764.FStar_Syntax_Syntax.n  in
               (uu____62763, args)  in
             (match uu____62748 with
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
              | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____62952)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldonly
                  ->
                  let uu____62987 =
                    let uu____62993 =
                      let uu____63003 = e_list e_string  in
                      unembed uu____63003 l  in
                    uu____62993 w norm1  in
                  FStar_Util.bind_opt uu____62987
                    (fun ss  ->
                       FStar_All.pipe_left
                         (fun _63029  -> FStar_Pervasives_Native.Some _63029)
                         (UnfoldOnly ss))
              | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____63032)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldfully
                  ->
                  let uu____63067 =
                    let uu____63073 =
                      let uu____63083 = e_list e_string  in
                      unembed uu____63083 l  in
                    uu____63073 w norm1  in
                  FStar_Util.bind_opt uu____63067
                    (fun ss  ->
                       FStar_All.pipe_left
                         (fun _63109  -> FStar_Pervasives_Native.Some _63109)
                         (UnfoldFully ss))
              | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____63112)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldattr
                  ->
                  let uu____63147 =
                    let uu____63153 =
                      let uu____63163 = e_list e_string  in
                      unembed uu____63163 l  in
                    uu____63153 w norm1  in
                  FStar_Util.bind_opt uu____63147
                    (fun ss  ->
                       FStar_All.pipe_left
                         (fun _63189  -> FStar_Pervasives_Native.Some _63189)
                         (UnfoldAttr ss))
              | uu____63190 ->
                  (if w
                   then
                     (let uu____63207 =
                        let uu____63213 =
                          let uu____63215 =
                            FStar_Syntax_Print.term_to_string t0  in
                          FStar_Util.format1 "Not an embedded norm_step: %s"
                            uu____63215
                           in
                        (FStar_Errors.Warning_NotEmbedded, uu____63213)  in
                      FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                        uu____63207)
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
    | uu____63317 ->
        (if w
         then
           (let uu____63320 =
              let uu____63326 =
                let uu____63328 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded range: %s" uu____63328
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____63326)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____63320)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____63334 =
    let uu____63335 =
      let uu____63343 =
        FStar_All.pipe_right FStar_Parser_Const.range_lid
          FStar_Ident.string_of_lid
         in
      (uu____63343, [])  in
    FStar_Syntax_Syntax.ET_app uu____63335  in
  mk_emb_full em un FStar_Syntax_Syntax.t_range FStar_Range.string_of_range
    uu____63334
  
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
        let uu____63414 =
          let uu____63421 =
            let uu____63422 =
              let uu____63437 =
                let uu____63446 =
                  let uu____63453 = FStar_Syntax_Syntax.null_bv ea.typ  in
                  (uu____63453, FStar_Pervasives_Native.None)  in
                [uu____63446]  in
              let uu____63468 = FStar_Syntax_Syntax.mk_Total eb.typ  in
              (uu____63437, uu____63468)  in
            FStar_Syntax_Syntax.Tm_arrow uu____63422  in
          FStar_Syntax_Syntax.mk uu____63421  in
        uu____63414 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
      let emb_t_arr_a_b =
        FStar_Syntax_Syntax.ET_fun ((ea.emb_typ), (eb.emb_typ))  in
      let printer f = "<fun>"  in
      let em f rng shadow_f norm1 =
        lazy_embed (fun uu____63581  -> "<fun>") emb_t_arr_a_b rng t_arrow f
          (fun uu____63587  ->
             let uu____63588 = force_shadow shadow_f  in
             match uu____63588 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Exn.raise Embedding_failure
             | FStar_Pervasives_Native.Some repr_f ->
                 ((let uu____63650 =
                     FStar_ST.op_Bang FStar_Options.debug_embedding  in
                   if uu____63650
                   then
                     let uu____63674 =
                       FStar_Syntax_Print.term_to_string repr_f  in
                     let uu____63676 = FStar_Util.stack_dump ()  in
                     FStar_Util.print2
                       "e_arrow forced back to term using shadow %s; repr=%s\n"
                       uu____63674 uu____63676
                   else ());
                  (let res = norm1 (FStar_Util.Inr repr_f)  in
                   (let uu____63683 =
                      FStar_ST.op_Bang FStar_Options.debug_embedding  in
                    if uu____63683
                    then
                      let uu____63707 =
                        FStar_Syntax_Print.term_to_string repr_f  in
                      let uu____63709 = FStar_Syntax_Print.term_to_string res
                         in
                      let uu____63711 = FStar_Util.stack_dump ()  in
                      FStar_Util.print3
                        "e_arrow forced back to term using shadow %s; repr=%s\n\t%s\n"
                        uu____63707 uu____63709 uu____63711
                    else ());
                   res)))
         in
      let un f w norm1 =
        lazy_unembed printer emb_t_arr_a_b f t_arrow
          (fun f1  ->
             let f_wrapped a =
               (let uu____63770 =
                  FStar_ST.op_Bang FStar_Options.debug_embedding  in
                if uu____63770
                then
                  let uu____63794 = FStar_Syntax_Print.term_to_string f1  in
                  let uu____63796 = FStar_Util.stack_dump ()  in
                  FStar_Util.print2
                    "Calling back into normalizer for %s\n%s\n" uu____63794
                    uu____63796
                else ());
               (let a_tm =
                  let uu____63802 = embed ea a  in
                  uu____63802 f1.FStar_Syntax_Syntax.pos
                    FStar_Pervasives_Native.None norm1
                   in
                let b_tm =
                  let uu____63835 =
                    let uu____63840 =
                      let uu____63841 =
                        let uu____63846 =
                          let uu____63847 = FStar_Syntax_Syntax.as_arg a_tm
                             in
                          [uu____63847]  in
                        FStar_Syntax_Syntax.mk_Tm_app f1 uu____63846  in
                      uu____63841 FStar_Pervasives_Native.None
                        f1.FStar_Syntax_Syntax.pos
                       in
                    FStar_Util.Inr uu____63840  in
                  norm1 uu____63835  in
                let uu____63874 =
                  let uu____63877 = unembed eb b_tm  in uu____63877 w norm1
                   in
                match uu____63874 with
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
                let uu____63977 = FStar_List.splitAt n_tvars args  in
                match uu____63977 with
                | (_tvar_args,rest_args) ->
                    let uu____64054 = FStar_List.hd rest_args  in
                    (match uu____64054 with
                     | (x,uu____64074) ->
                         let shadow_app =
                           let uu____64088 =
                             FStar_Common.mk_thunk
                               (fun uu____64097  ->
                                  let uu____64098 =
                                    let uu____64103 =
                                      norm1 (FStar_Util.Inl fv_lid1)  in
                                    FStar_Syntax_Syntax.mk_Tm_app uu____64103
                                      args
                                     in
                                  uu____64098 FStar_Pervasives_Native.None
                                    rng)
                              in
                           FStar_Pervasives_Native.Some uu____64088  in
                         let uu____64149 =
                           let uu____64152 =
                             let uu____64155 = unembed ea x  in
                             uu____64155 true norm1  in
                           FStar_Util.map_opt uu____64152
                             (fun x1  ->
                                let uu____64195 =
                                  let uu____64202 = f x1  in
                                  embed eb uu____64202  in
                                uu____64195 rng shadow_app norm1)
                            in
                         (match uu____64149 with
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
                  let uu____64332 = FStar_List.splitAt n_tvars args  in
                  match uu____64332 with
                  | (_tvar_args,rest_args) ->
                      let uu____64395 = FStar_List.hd rest_args  in
                      (match uu____64395 with
                       | (x,uu____64411) ->
                           let uu____64416 =
                             let uu____64423 = FStar_List.tl rest_args  in
                             FStar_List.hd uu____64423  in
                           (match uu____64416 with
                            | (y,uu____64447) ->
                                let shadow_app =
                                  let uu____64457 =
                                    FStar_Common.mk_thunk
                                      (fun uu____64466  ->
                                         let uu____64467 =
                                           let uu____64472 =
                                             norm1 (FStar_Util.Inl fv_lid1)
                                              in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____64472 args
                                            in
                                         uu____64467
                                           FStar_Pervasives_Native.None rng)
                                     in
                                  FStar_Pervasives_Native.Some uu____64457
                                   in
                                let uu____64518 =
                                  let uu____64521 =
                                    let uu____64524 = unembed ea x  in
                                    uu____64524 true norm1  in
                                  FStar_Util.bind_opt uu____64521
                                    (fun x1  ->
                                       let uu____64541 =
                                         let uu____64544 = unembed eb y  in
                                         uu____64544 true norm1  in
                                       FStar_Util.bind_opt uu____64541
                                         (fun y1  ->
                                            let uu____64561 =
                                              let uu____64562 =
                                                let uu____64569 = f x1 y1  in
                                                embed ec uu____64569  in
                                              uu____64562 rng shadow_app
                                                norm1
                                               in
                                            FStar_Pervasives_Native.Some
                                              uu____64561))
                                   in
                                (match uu____64518 with
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
                    let uu____64718 = FStar_List.splitAt n_tvars args  in
                    match uu____64718 with
                    | (_tvar_args,rest_args) ->
                        let uu____64781 = FStar_List.hd rest_args  in
                        (match uu____64781 with
                         | (x,uu____64797) ->
                             let uu____64802 =
                               let uu____64809 = FStar_List.tl rest_args  in
                               FStar_List.hd uu____64809  in
                             (match uu____64802 with
                              | (y,uu____64833) ->
                                  let uu____64838 =
                                    let uu____64845 =
                                      let uu____64854 =
                                        FStar_List.tl rest_args  in
                                      FStar_List.tl uu____64854  in
                                    FStar_List.hd uu____64845  in
                                  (match uu____64838 with
                                   | (z,uu____64884) ->
                                       let shadow_app =
                                         let uu____64894 =
                                           FStar_Common.mk_thunk
                                             (fun uu____64903  ->
                                                let uu____64904 =
                                                  let uu____64909 =
                                                    norm1
                                                      (FStar_Util.Inl fv_lid1)
                                                     in
                                                  FStar_Syntax_Syntax.mk_Tm_app
                                                    uu____64909 args
                                                   in
                                                uu____64904
                                                  FStar_Pervasives_Native.None
                                                  rng)
                                            in
                                         FStar_Pervasives_Native.Some
                                           uu____64894
                                          in
                                       let uu____64955 =
                                         let uu____64958 =
                                           let uu____64961 = unembed ea x  in
                                           uu____64961 true norm1  in
                                         FStar_Util.bind_opt uu____64958
                                           (fun x1  ->
                                              let uu____64978 =
                                                let uu____64981 =
                                                  unembed eb y  in
                                                uu____64981 true norm1  in
                                              FStar_Util.bind_opt uu____64978
                                                (fun y1  ->
                                                   let uu____64998 =
                                                     let uu____65001 =
                                                       unembed ec z  in
                                                     uu____65001 true norm1
                                                      in
                                                   FStar_Util.bind_opt
                                                     uu____64998
                                                     (fun z1  ->
                                                        let uu____65018 =
                                                          let uu____65019 =
                                                            let uu____65026 =
                                                              f x1 y1 z1  in
                                                            embed ed
                                                              uu____65026
                                                             in
                                                          uu____65019 rng
                                                            shadow_app norm1
                                                           in
                                                        FStar_Pervasives_Native.Some
                                                          uu____65018)))
                                          in
                                       (match uu____64955 with
                                        | FStar_Pervasives_Native.Some x1 ->
                                            FStar_Pervasives_Native.Some x1
                                        | FStar_Pervasives_Native.None  ->
                                            force_shadow shadow_app))))
                     in
                  f_wrapped
  
let debug_wrap : 'a . Prims.string -> (unit -> 'a) -> 'a =
  fun s  ->
    fun f  ->
      (let uu____65081 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
       if uu____65081 then FStar_Util.print1 "++++starting %s\n" s else ());
      (let res = f ()  in
       (let uu____65110 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
        if uu____65110 then FStar_Util.print1 "------ending %s\n" s else ());
       res)
  