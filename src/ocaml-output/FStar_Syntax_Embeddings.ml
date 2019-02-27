open Prims
type norm_cb =
  (FStar_Ident.lid,FStar_Syntax_Syntax.term) FStar_Util.either ->
    FStar_Syntax_Syntax.term
let (id_norm_cb : norm_cb) =
  fun uu___429_55239  ->
    match uu___429_55239 with
    | FStar_Util.Inr x -> x
    | FStar_Util.Inl l ->
        let uu____55246 =
          FStar_Syntax_Syntax.lid_as_fv l
            FStar_Syntax_Syntax.delta_equational FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.fv_to_tm uu____55246
  
exception Embedding_failure 
let (uu___is_Embedding_failure : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Embedding_failure  -> true | uu____55256 -> false
  
exception Unembedding_failure 
let (uu___is_Unembedding_failure : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Unembedding_failure  -> true
    | uu____55267 -> false
  
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
             (fun uu____55433  ->
                let uu____55434 = FStar_Common.force_thunk s1  in
                f uu____55434))
  
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
  'Auu____56068 . FStar_Syntax_Syntax.term -> 'Auu____56068 -> Prims.string =
  fun typ  ->
    fun uu____56079  ->
      let uu____56080 = FStar_Syntax_Print.term_to_string typ  in
      FStar_Util.format1 "unknown %s" uu____56080
  
let (term_as_fv : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.fv) =
  fun t  ->
    let uu____56089 =
      let uu____56090 = FStar_Syntax_Subst.compress t  in
      uu____56090.FStar_Syntax_Syntax.n  in
    match uu____56089 with
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv
    | uu____56094 ->
        let uu____56095 =
          let uu____56097 = FStar_Syntax_Print.term_to_string t  in
          FStar_Util.format1 "Embeddings not defined for type %s" uu____56097
           in
        failwith uu____56095
  
let mk_emb :
  'a .
    'a raw_embedder ->
      'a raw_unembedder -> FStar_Syntax_Syntax.fv -> 'a embedding
  =
  fun em  ->
    fun un  ->
      fun fv  ->
        let typ = FStar_Syntax_Syntax.fv_to_tm fv  in
        let uu____56225 =
          let uu____56226 =
            let uu____56234 =
              let uu____56236 = FStar_Syntax_Syntax.lid_of_fv fv  in
              FStar_All.pipe_right uu____56236 FStar_Ident.string_of_lid  in
            (uu____56234, [])  in
          FStar_Syntax_Syntax.ET_app uu____56226  in
        { em; un; typ; print = (unknown_printer typ); emb_typ = uu____56225 }
  
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
      fun n1  -> let uu____56646 = unembed e t  in uu____56646 true n1
  
let try_unembed :
  'a .
    'a embedding ->
      FStar_Syntax_Syntax.term ->
        norm_cb -> 'a FStar_Pervasives_Native.option
  =
  fun e  ->
    fun t  ->
      fun n1  -> let uu____56695 = unembed e t  in uu____56695 false n1
  
let type_of : 'a . 'a embedding -> FStar_Syntax_Syntax.typ = fun e  -> e.typ 
let set_type : 'a . FStar_Syntax_Syntax.typ -> 'a embedding -> 'a embedding =
  fun ty  ->
    fun e  ->
      let uu___508_56748 = e  in
      {
        em = (uu___508_56748.em);
        un = (uu___508_56748.un);
        typ = ty;
        print = (uu___508_56748.print);
        emb_typ = (uu___508_56748.emb_typ)
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
              (let uu____56817 =
                 FStar_ST.op_Bang FStar_Options.debug_embedding  in
               if uu____56817
               then
                 let uu____56841 = FStar_Syntax_Print.term_to_string ta  in
                 let uu____56843 = FStar_Syntax_Print.emb_typ_to_string et
                    in
                 let uu____56845 = pa x  in
                 FStar_Util.print3
                   "Embedding a %s\n\temb_typ=%s\n\tvalue is %s\n"
                   uu____56841 uu____56843 uu____56845
               else ());
              (let uu____56852 =
                 FStar_ST.op_Bang FStar_Options.eager_embedding  in
               if uu____56852
               then f ()
               else
                 (let thunk1 = FStar_Common.mk_thunk f  in
                  let uu____56887 =
                    let uu____56894 =
                      let uu____56895 =
                        let uu____56896 = FStar_Dyn.mkdyn x  in
                        {
                          FStar_Syntax_Syntax.blob = uu____56896;
                          FStar_Syntax_Syntax.lkind =
                            (FStar_Syntax_Syntax.Lazy_embedding (et, thunk1));
                          FStar_Syntax_Syntax.ltyp = FStar_Syntax_Syntax.tun;
                          FStar_Syntax_Syntax.rng = rng
                        }  in
                      FStar_Syntax_Syntax.Tm_lazy uu____56895  in
                    FStar_Syntax_Syntax.mk uu____56894  in
                  uu____56887 FStar_Pervasives_Native.None rng))
  
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
                  FStar_Syntax_Syntax.ltyp = uu____57012;
                  FStar_Syntax_Syntax.rng = uu____57013;_}
                ->
                let uu____57024 =
                  (et <> et') ||
                    (FStar_ST.op_Bang FStar_Options.eager_embedding)
                   in
                if uu____57024
                then
                  let res =
                    let uu____57053 = FStar_Common.force_thunk t  in
                    f uu____57053  in
                  ((let uu____57097 =
                      FStar_ST.op_Bang FStar_Options.debug_embedding  in
                    if uu____57097
                    then
                      let uu____57121 =
                        FStar_Syntax_Print.emb_typ_to_string et  in
                      let uu____57123 =
                        FStar_Syntax_Print.emb_typ_to_string et'  in
                      let uu____57125 =
                        match res with
                        | FStar_Pervasives_Native.None  -> "None"
                        | FStar_Pervasives_Native.Some x2 ->
                            let uu____57130 = pa x2  in
                            Prims.op_Hat "Some " uu____57130
                         in
                      FStar_Util.print3
                        "Unembed cancellation failed\n\t%s <> %s\nvalue is %s\n"
                        uu____57121 uu____57123 uu____57125
                    else ());
                   res)
                else
                  (let a = FStar_Dyn.undyn b  in
                   (let uu____57142 =
                      FStar_ST.op_Bang FStar_Options.debug_embedding  in
                    if uu____57142
                    then
                      let uu____57166 =
                        FStar_Syntax_Print.emb_typ_to_string et  in
                      let uu____57168 = pa a  in
                      FStar_Util.print2
                        "Unembed cancelled for %s\n\tvalue is %s\n"
                        uu____57166 uu____57168
                    else ());
                   FStar_Pervasives_Native.Some a)
            | uu____57175 ->
                let aopt = f x1  in
                ((let uu____57180 =
                    FStar_ST.op_Bang FStar_Options.debug_embedding  in
                  if uu____57180
                  then
                    let uu____57204 = FStar_Syntax_Print.emb_typ_to_string et
                       in
                    let uu____57206 = FStar_Syntax_Print.term_to_string x1
                       in
                    let uu____57208 =
                      match aopt with
                      | FStar_Pervasives_Native.None  -> "None"
                      | FStar_Pervasives_Native.Some a ->
                          let uu____57213 = pa a  in
                          Prims.op_Hat "Some " uu____57213
                       in
                    FStar_Util.print3
                      "Unembedding:\n\temb_typ=%s\n\tterm is %s\n\tvalue is %s\n"
                      uu____57204 uu____57206 uu____57208
                  else ());
                 aopt)
  
let (mk_any_emb :
  FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term embedding) =
  fun typ  ->
    let em t _r _topt _norm =
      (let uu____57293 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
       if uu____57293
       then
         let uu____57317 = unknown_printer typ t  in
         FStar_Util.print1 "Embedding abstract: %s\n" uu____57317
       else ());
      t  in
    let un t _w _n =
      (let uu____57347 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
       if uu____57347
       then
         let uu____57371 = unknown_printer typ t  in
         FStar_Util.print1 "Unembedding abstract: %s\n" uu____57371
       else ());
      FStar_Pervasives_Native.Some t  in
    mk_emb_full em un typ (unknown_printer typ)
      FStar_Syntax_Syntax.ET_abstract
  
let (e_any : FStar_Syntax_Syntax.term embedding) =
  let em t _r _topt _norm = t  in
  let un t _w _n = FStar_Pervasives_Native.Some t  in
  let uu____57466 =
    let uu____57467 =
      let uu____57475 =
        FStar_All.pipe_right FStar_Parser_Const.term_lid
          FStar_Ident.string_of_lid
         in
      (uu____57475, [])  in
    FStar_Syntax_Syntax.ET_app uu____57467  in
  mk_emb_full em un FStar_Syntax_Syntax.t_term
    FStar_Syntax_Print.term_to_string uu____57466
  
let (e_unit : unit embedding) =
  let em u rng _topt _norm =
    let uu___582_57547 = FStar_Syntax_Util.exp_unit  in
    {
      FStar_Syntax_Syntax.n = (uu___582_57547.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___582_57547.FStar_Syntax_Syntax.vars)
    }  in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unascribe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit ) ->
        FStar_Pervasives_Native.Some ()
    | uu____57577 ->
        (if w
         then
           (let uu____57580 =
              let uu____57586 =
                let uu____57588 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded unit: %s" uu____57588  in
              (FStar_Errors.Warning_NotEmbedded, uu____57586)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____57580)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____57594 =
    let uu____57595 =
      let uu____57603 =
        FStar_All.pipe_right FStar_Parser_Const.unit_lid
          FStar_Ident.string_of_lid
         in
      (uu____57603, [])  in
    FStar_Syntax_Syntax.ET_app uu____57595  in
  mk_emb_full em un FStar_Syntax_Syntax.t_unit (fun uu____57610  -> "()")
    uu____57594
  
let (e_bool : Prims.bool embedding) =
  let em b rng _topt _norm =
    let t =
      if b
      then FStar_Syntax_Util.exp_true_bool
      else FStar_Syntax_Util.exp_false_bool  in
    let uu___602_57689 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___602_57689.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___602_57689.FStar_Syntax_Syntax.vars)
    }  in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) ->
        FStar_Pervasives_Native.Some b
    | uu____57727 ->
        (if w
         then
           (let uu____57730 =
              let uu____57736 =
                let uu____57738 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded bool: %s" uu____57738  in
              (FStar_Errors.Warning_NotEmbedded, uu____57736)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____57730)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____57745 =
    let uu____57746 =
      let uu____57754 =
        FStar_All.pipe_right FStar_Parser_Const.bool_lid
          FStar_Ident.string_of_lid
         in
      (uu____57754, [])  in
    FStar_Syntax_Syntax.ET_app uu____57746  in
  mk_emb_full em un FStar_Syntax_Syntax.t_bool FStar_Util.string_of_bool
    uu____57745
  
let (e_char : FStar_Char.char embedding) =
  let em c rng _topt _norm =
    let t = FStar_Syntax_Util.exp_char c  in
    let uu___621_57831 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___621_57831.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___621_57831.FStar_Syntax_Syntax.vars)
    }  in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c) ->
        FStar_Pervasives_Native.Some c
    | uu____57867 ->
        (if w
         then
           (let uu____57870 =
              let uu____57876 =
                let uu____57878 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded char: %s" uu____57878  in
              (FStar_Errors.Warning_NotEmbedded, uu____57876)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____57870)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____57885 =
    let uu____57886 =
      let uu____57894 =
        FStar_All.pipe_right FStar_Parser_Const.char_lid
          FStar_Ident.string_of_lid
         in
      (uu____57894, [])  in
    FStar_Syntax_Syntax.ET_app uu____57886  in
  mk_emb_full em un FStar_Syntax_Syntax.t_char FStar_Util.string_of_char
    uu____57885
  
let (e_int : FStar_BigInt.t embedding) =
  let t_int1 = FStar_Syntax_Util.fvar_const FStar_Parser_Const.int_lid  in
  let emb_t_int =
    let uu____57906 =
      let uu____57914 =
        FStar_All.pipe_right FStar_Parser_Const.int_lid
          FStar_Ident.string_of_lid
         in
      (uu____57914, [])  in
    FStar_Syntax_Syntax.ET_app uu____57906  in
  let em i rng _topt _norm =
    lazy_embed FStar_BigInt.string_of_big_int emb_t_int rng t_int1 i
      (fun uu____57985  ->
         let uu____57986 = FStar_BigInt.string_of_big_int i  in
         FStar_Syntax_Util.exp_int uu____57986)
     in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    lazy_unembed FStar_BigInt.string_of_big_int emb_t_int t t_int1
      (fun t1  ->
         match t1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
             (s,uu____58023)) ->
             let uu____58038 = FStar_BigInt.big_int_of_string s  in
             FStar_Pervasives_Native.Some uu____58038
         | uu____58039 ->
             (if w
              then
                (let uu____58042 =
                   let uu____58048 =
                     let uu____58050 = FStar_Syntax_Print.term_to_string t0
                        in
                     FStar_Util.format1 "Not an embedded int: %s" uu____58050
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____58048)  in
                 FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                   uu____58042)
              else ();
              FStar_Pervasives_Native.None))
     in
  mk_emb_full em un FStar_Syntax_Syntax.t_int FStar_BigInt.string_of_big_int
    emb_t_int
  
let (e_string : Prims.string embedding) =
  let emb_t_string =
    let uu____58061 =
      let uu____58069 =
        FStar_All.pipe_right FStar_Parser_Const.string_lid
          FStar_Ident.string_of_lid
         in
      (uu____58069, [])  in
    FStar_Syntax_Syntax.ET_app uu____58061  in
  let em s rng _topt _norm =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, rng)))
      FStar_Pervasives_Native.None rng
     in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
        (s,uu____58174)) -> FStar_Pervasives_Native.Some s
    | uu____58178 ->
        (if w
         then
           (let uu____58181 =
              let uu____58187 =
                let uu____58189 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded string: %s" uu____58189
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____58187)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____58181)
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
      let uu____58225 =
        let uu____58230 =
          let uu____58231 = FStar_Syntax_Syntax.as_arg ea.typ  in
          [uu____58231]  in
        FStar_Syntax_Syntax.mk_Tm_app t_opt uu____58230  in
      uu____58225 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
    let emb_t_option_a =
      let uu____58259 =
        let uu____58267 =
          FStar_All.pipe_right FStar_Parser_Const.option_lid
            FStar_Ident.string_of_lid
           in
        (uu____58267, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____58259  in
    let printer uu___430_58281 =
      match uu___430_58281 with
      | FStar_Pervasives_Native.None  -> "None"
      | FStar_Pervasives_Native.Some x ->
          let uu____58287 =
            let uu____58289 = ea.print x  in Prims.op_Hat uu____58289 ")"  in
          Prims.op_Hat "(Some " uu____58287
       in
    let em o rng topt norm1 =
      lazy_embed printer emb_t_option_a rng t_option_a o
        (fun uu____58366  ->
           match o with
           | FStar_Pervasives_Native.None  ->
               let uu____58367 =
                 let uu____58372 =
                   let uu____58373 =
                     FStar_Syntax_Syntax.tdataconstr
                       FStar_Parser_Const.none_lid
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____58373
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 let uu____58374 =
                   let uu____58375 =
                     let uu____58384 = type_of ea  in
                     FStar_Syntax_Syntax.iarg uu____58384  in
                   [uu____58375]  in
                 FStar_Syntax_Syntax.mk_Tm_app uu____58372 uu____58374  in
               uu____58367 FStar_Pervasives_Native.None rng
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
                        let uu____58475 =
                          FStar_Syntax_Syntax.lid_as_fv some_v
                            FStar_Syntax_Syntax.delta_equational
                            FStar_Pervasives_Native.None
                           in
                        FStar_Syntax_Syntax.fv_to_tm uu____58475  in
                      let uu____58476 =
                        let uu____58481 =
                          FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm
                            [FStar_Syntax_Syntax.U_zero]
                           in
                        let uu____58482 =
                          let uu____58483 =
                            let uu____58492 = type_of ea  in
                            FStar_Syntax_Syntax.iarg uu____58492  in
                          let uu____58493 =
                            let uu____58504 = FStar_Syntax_Syntax.as_arg t
                               in
                            [uu____58504]  in
                          uu____58483 :: uu____58493  in
                        FStar_Syntax_Syntax.mk_Tm_app uu____58481 uu____58482
                         in
                      uu____58476 FStar_Pervasives_Native.None rng)
                  in
               let uu____58539 =
                 let uu____58544 =
                   let uu____58545 =
                     FStar_Syntax_Syntax.tdataconstr
                       FStar_Parser_Const.some_lid
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____58545
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 let uu____58546 =
                   let uu____58547 =
                     let uu____58556 = type_of ea  in
                     FStar_Syntax_Syntax.iarg uu____58556  in
                   let uu____58557 =
                     let uu____58568 =
                       let uu____58577 =
                         let uu____58578 = embed ea a  in
                         uu____58578 rng shadow_a norm1  in
                       FStar_Syntax_Syntax.as_arg uu____58577  in
                     [uu____58568]  in
                   uu____58547 :: uu____58557  in
                 FStar_Syntax_Syntax.mk_Tm_app uu____58544 uu____58546  in
               uu____58539 FStar_Pervasives_Native.None rng)
       in
    let un t0 w norm1 =
      let t = FStar_Syntax_Util.unmeta_safe t0  in
      lazy_unembed printer emb_t_option_a t t_option_a
        (fun t1  ->
           let uu____58715 = FStar_Syntax_Util.head_and_args' t1  in
           match uu____58715 with
           | (hd1,args) ->
               let uu____58756 =
                 let uu____58771 =
                   let uu____58772 = FStar_Syntax_Util.un_uinst hd1  in
                   uu____58772.FStar_Syntax_Syntax.n  in
                 (uu____58771, args)  in
               (match uu____58756 with
                | (FStar_Syntax_Syntax.Tm_fvar fv,uu____58790) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.none_lid
                    ->
                    FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,uu____58814::(a,uu____58816)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.some_lid
                    ->
                    let uu____58867 =
                      let uu____58870 = unembed ea a  in uu____58870 w norm1
                       in
                    FStar_Util.bind_opt uu____58867
                      (fun a1  ->
                         FStar_Pervasives_Native.Some
                           (FStar_Pervasives_Native.Some a1))
                | uu____58889 ->
                    (if w
                     then
                       (let uu____58906 =
                          let uu____58912 =
                            let uu____58914 =
                              FStar_Syntax_Print.term_to_string t0  in
                            FStar_Util.format1 "Not an embedded option: %s"
                              uu____58914
                             in
                          (FStar_Errors.Warning_NotEmbedded, uu____58912)  in
                        FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                          uu____58906)
                     else ();
                     FStar_Pervasives_Native.None)))
       in
    let uu____58922 =
      let uu____58923 = type_of ea  in
      FStar_Syntax_Syntax.t_option_of uu____58923  in
    mk_emb_full em un uu____58922 printer emb_t_option_a
  
let e_tuple2 : 'a 'b . 'a embedding -> 'b embedding -> ('a * 'b) embedding =
  fun ea  ->
    fun eb  ->
      let t_pair_a_b =
        let t_tup2 =
          FStar_Syntax_Util.fvar_const FStar_Parser_Const.lid_tuple2  in
        let uu____58965 =
          let uu____58970 =
            let uu____58971 = FStar_Syntax_Syntax.as_arg ea.typ  in
            let uu____58980 =
              let uu____58991 = FStar_Syntax_Syntax.as_arg eb.typ  in
              [uu____58991]  in
            uu____58971 :: uu____58980  in
          FStar_Syntax_Syntax.mk_Tm_app t_tup2 uu____58970  in
        uu____58965 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
      let emb_t_pair_a_b =
        let uu____59027 =
          let uu____59035 =
            FStar_All.pipe_right FStar_Parser_Const.lid_tuple2
              FStar_Ident.string_of_lid
             in
          (uu____59035, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____59027  in
      let printer uu____59051 =
        match uu____59051 with
        | (x,y) ->
            let uu____59059 = ea.print x  in
            let uu____59061 = eb.print y  in
            FStar_Util.format2 "(%s, %s)" uu____59059 uu____59061
         in
      let em x rng topt norm1 =
        lazy_embed printer emb_t_pair_a_b rng t_pair_a_b x
          (fun uu____59146  ->
             let proj i ab =
               let uu____59162 =
                 let uu____59167 =
                   FStar_Parser_Const.mk_tuple_data_lid (Prims.parse_int "2")
                     rng
                    in
                 let uu____59169 =
                   FStar_Syntax_Syntax.null_bv FStar_Syntax_Syntax.tun  in
                 FStar_Syntax_Util.mk_field_projector_name uu____59167
                   uu____59169 i
                  in
               match uu____59162 with
               | (proj_1,uu____59173) ->
                   let proj_1_tm =
                     let uu____59175 =
                       FStar_Syntax_Syntax.lid_as_fv proj_1
                         FStar_Syntax_Syntax.delta_equational
                         FStar_Pervasives_Native.None
                        in
                     FStar_Syntax_Syntax.fv_to_tm uu____59175  in
                   let uu____59176 =
                     let uu____59181 =
                       FStar_Syntax_Syntax.mk_Tm_uinst proj_1_tm
                         [FStar_Syntax_Syntax.U_zero]
                        in
                     let uu____59182 =
                       let uu____59183 =
                         let uu____59192 = type_of ea  in
                         FStar_Syntax_Syntax.iarg uu____59192  in
                       let uu____59193 =
                         let uu____59204 =
                           let uu____59213 = type_of eb  in
                           FStar_Syntax_Syntax.iarg uu____59213  in
                         let uu____59214 =
                           let uu____59225 = FStar_Syntax_Syntax.as_arg ab
                              in
                           [uu____59225]  in
                         uu____59204 :: uu____59214  in
                       uu____59183 :: uu____59193  in
                     FStar_Syntax_Syntax.mk_Tm_app uu____59181 uu____59182
                      in
                   uu____59176 FStar_Pervasives_Native.None rng
                in
             let shadow_a = map_shadow topt (proj (Prims.parse_int "1"))  in
             let shadow_b = map_shadow topt (proj (Prims.parse_int "2"))  in
             let uu____59386 =
               let uu____59391 =
                 let uu____59392 =
                   FStar_Syntax_Syntax.tdataconstr
                     FStar_Parser_Const.lid_Mktuple2
                    in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu____59392
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                  in
               let uu____59393 =
                 let uu____59394 =
                   let uu____59403 = type_of ea  in
                   FStar_Syntax_Syntax.iarg uu____59403  in
                 let uu____59404 =
                   let uu____59415 =
                     let uu____59424 = type_of eb  in
                     FStar_Syntax_Syntax.iarg uu____59424  in
                   let uu____59425 =
                     let uu____59436 =
                       let uu____59445 =
                         let uu____59446 =
                           embed ea (FStar_Pervasives_Native.fst x)  in
                         uu____59446 rng shadow_a norm1  in
                       FStar_Syntax_Syntax.as_arg uu____59445  in
                     let uu____59516 =
                       let uu____59527 =
                         let uu____59536 =
                           let uu____59537 =
                             embed eb (FStar_Pervasives_Native.snd x)  in
                           uu____59537 rng shadow_b norm1  in
                         FStar_Syntax_Syntax.as_arg uu____59536  in
                       [uu____59527]  in
                     uu____59436 :: uu____59516  in
                   uu____59415 :: uu____59425  in
                 uu____59394 :: uu____59404  in
               FStar_Syntax_Syntax.mk_Tm_app uu____59391 uu____59393  in
             uu____59386 FStar_Pervasives_Native.None rng)
         in
      let un t0 w norm1 =
        let t = FStar_Syntax_Util.unmeta_safe t0  in
        lazy_unembed printer emb_t_pair_a_b t t_pair_a_b
          (fun t1  ->
             let uu____59702 = FStar_Syntax_Util.head_and_args' t1  in
             match uu____59702 with
             | (hd1,args) ->
                 let uu____59745 =
                   let uu____59758 =
                     let uu____59759 = FStar_Syntax_Util.un_uinst hd1  in
                     uu____59759.FStar_Syntax_Syntax.n  in
                   (uu____59758, args)  in
                 (match uu____59745 with
                  | (FStar_Syntax_Syntax.Tm_fvar
                     fv,uu____59777::uu____59778::(a,uu____59780)::(b,uu____59782)::[])
                      when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.lid_Mktuple2
                      ->
                      let uu____59841 =
                        let uu____59844 = unembed ea a  in
                        uu____59844 w norm1  in
                      FStar_Util.bind_opt uu____59841
                        (fun a1  ->
                           let uu____59864 =
                             let uu____59867 = unembed eb b  in
                             uu____59867 w norm1  in
                           FStar_Util.bind_opt uu____59864
                             (fun b1  ->
                                FStar_Pervasives_Native.Some (a1, b1)))
                  | uu____59890 ->
                      (if w
                       then
                         (let uu____59905 =
                            let uu____59911 =
                              let uu____59913 =
                                FStar_Syntax_Print.term_to_string t0  in
                              FStar_Util.format1 "Not an embedded pair: %s"
                                uu____59913
                               in
                            (FStar_Errors.Warning_NotEmbedded, uu____59911)
                             in
                          FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                            uu____59905)
                       else ();
                       FStar_Pervasives_Native.None)))
         in
      let uu____59923 =
        let uu____59924 = type_of ea  in
        let uu____59925 = type_of eb  in
        FStar_Syntax_Syntax.t_tuple2_of uu____59924 uu____59925  in
      mk_emb_full em un uu____59923 printer emb_t_pair_a_b
  
let e_either :
  'a 'b . 'a embedding -> 'b embedding -> ('a,'b) FStar_Util.either embedding
  =
  fun ea  ->
    fun eb  ->
      let t_sum_a_b =
        let t_either =
          FStar_Syntax_Util.fvar_const FStar_Parser_Const.either_lid  in
        let uu____59969 =
          let uu____59974 =
            let uu____59975 = FStar_Syntax_Syntax.as_arg ea.typ  in
            let uu____59984 =
              let uu____59995 = FStar_Syntax_Syntax.as_arg eb.typ  in
              [uu____59995]  in
            uu____59975 :: uu____59984  in
          FStar_Syntax_Syntax.mk_Tm_app t_either uu____59974  in
        uu____59969 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
      let emb_t_sum_a_b =
        let uu____60031 =
          let uu____60039 =
            FStar_All.pipe_right FStar_Parser_Const.either_lid
              FStar_Ident.string_of_lid
             in
          (uu____60039, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____60031  in
      let printer s =
        match s with
        | FStar_Util.Inl a ->
            let uu____60062 = ea.print a  in
            FStar_Util.format1 "Inl %s" uu____60062
        | FStar_Util.Inr b ->
            let uu____60066 = eb.print b  in
            FStar_Util.format1 "Inr %s" uu____60066
         in
      let em s rng topt norm1 =
        lazy_embed printer emb_t_sum_a_b rng t_sum_a_b s
          (match s with
           | FStar_Util.Inl a ->
               (fun uu____60154  ->
                  let shadow_a =
                    map_shadow topt
                      (fun t  ->
                         let v1 = FStar_Ident.mk_ident ("v", rng)  in
                         let some_v =
                           FStar_Syntax_Util.mk_field_projector_name_from_ident
                             FStar_Parser_Const.inl_lid v1
                            in
                         let some_v_tm =
                           let uu____60226 =
                             FStar_Syntax_Syntax.lid_as_fv some_v
                               FStar_Syntax_Syntax.delta_equational
                               FStar_Pervasives_Native.None
                              in
                           FStar_Syntax_Syntax.fv_to_tm uu____60226  in
                         let uu____60227 =
                           let uu____60232 =
                             FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm
                               [FStar_Syntax_Syntax.U_zero]
                              in
                           let uu____60233 =
                             let uu____60234 =
                               let uu____60243 = type_of ea  in
                               FStar_Syntax_Syntax.iarg uu____60243  in
                             let uu____60244 =
                               let uu____60255 =
                                 let uu____60264 = type_of eb  in
                                 FStar_Syntax_Syntax.iarg uu____60264  in
                               let uu____60265 =
                                 let uu____60276 =
                                   FStar_Syntax_Syntax.as_arg t  in
                                 [uu____60276]  in
                               uu____60255 :: uu____60265  in
                             uu____60234 :: uu____60244  in
                           FStar_Syntax_Syntax.mk_Tm_app uu____60232
                             uu____60233
                            in
                         uu____60227 FStar_Pervasives_Native.None rng)
                     in
                  let uu____60319 =
                    let uu____60324 =
                      let uu____60325 =
                        FStar_Syntax_Syntax.tdataconstr
                          FStar_Parser_Const.inl_lid
                         in
                      FStar_Syntax_Syntax.mk_Tm_uinst uu____60325
                        [FStar_Syntax_Syntax.U_zero;
                        FStar_Syntax_Syntax.U_zero]
                       in
                    let uu____60326 =
                      let uu____60327 =
                        let uu____60336 = type_of ea  in
                        FStar_Syntax_Syntax.iarg uu____60336  in
                      let uu____60337 =
                        let uu____60348 =
                          let uu____60357 = type_of eb  in
                          FStar_Syntax_Syntax.iarg uu____60357  in
                        let uu____60358 =
                          let uu____60369 =
                            let uu____60378 =
                              let uu____60379 = embed ea a  in
                              uu____60379 rng shadow_a norm1  in
                            FStar_Syntax_Syntax.as_arg uu____60378  in
                          [uu____60369]  in
                        uu____60348 :: uu____60358  in
                      uu____60327 :: uu____60337  in
                    FStar_Syntax_Syntax.mk_Tm_app uu____60324 uu____60326  in
                  uu____60319 FStar_Pervasives_Native.None rng)
           | FStar_Util.Inr b ->
               (fun uu____60484  ->
                  let shadow_b =
                    map_shadow topt
                      (fun t  ->
                         let v1 = FStar_Ident.mk_ident ("v", rng)  in
                         let some_v =
                           FStar_Syntax_Util.mk_field_projector_name_from_ident
                             FStar_Parser_Const.inr_lid v1
                            in
                         let some_v_tm =
                           let uu____60556 =
                             FStar_Syntax_Syntax.lid_as_fv some_v
                               FStar_Syntax_Syntax.delta_equational
                               FStar_Pervasives_Native.None
                              in
                           FStar_Syntax_Syntax.fv_to_tm uu____60556  in
                         let uu____60557 =
                           let uu____60562 =
                             FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm
                               [FStar_Syntax_Syntax.U_zero]
                              in
                           let uu____60563 =
                             let uu____60564 =
                               let uu____60573 = type_of ea  in
                               FStar_Syntax_Syntax.iarg uu____60573  in
                             let uu____60574 =
                               let uu____60585 =
                                 let uu____60594 = type_of eb  in
                                 FStar_Syntax_Syntax.iarg uu____60594  in
                               let uu____60595 =
                                 let uu____60606 =
                                   FStar_Syntax_Syntax.as_arg t  in
                                 [uu____60606]  in
                               uu____60585 :: uu____60595  in
                             uu____60564 :: uu____60574  in
                           FStar_Syntax_Syntax.mk_Tm_app uu____60562
                             uu____60563
                            in
                         uu____60557 FStar_Pervasives_Native.None rng)
                     in
                  let uu____60649 =
                    let uu____60654 =
                      let uu____60655 =
                        FStar_Syntax_Syntax.tdataconstr
                          FStar_Parser_Const.inr_lid
                         in
                      FStar_Syntax_Syntax.mk_Tm_uinst uu____60655
                        [FStar_Syntax_Syntax.U_zero;
                        FStar_Syntax_Syntax.U_zero]
                       in
                    let uu____60656 =
                      let uu____60657 =
                        let uu____60666 = type_of ea  in
                        FStar_Syntax_Syntax.iarg uu____60666  in
                      let uu____60667 =
                        let uu____60678 =
                          let uu____60687 = type_of eb  in
                          FStar_Syntax_Syntax.iarg uu____60687  in
                        let uu____60688 =
                          let uu____60699 =
                            let uu____60708 =
                              let uu____60709 = embed eb b  in
                              uu____60709 rng shadow_b norm1  in
                            FStar_Syntax_Syntax.as_arg uu____60708  in
                          [uu____60699]  in
                        uu____60678 :: uu____60688  in
                      uu____60657 :: uu____60667  in
                    FStar_Syntax_Syntax.mk_Tm_app uu____60654 uu____60656  in
                  uu____60649 FStar_Pervasives_Native.None rng))
         in
      let un t0 w norm1 =
        let t = FStar_Syntax_Util.unmeta_safe t0  in
        lazy_unembed printer emb_t_sum_a_b t t_sum_a_b
          (fun t1  ->
             let uu____60864 = FStar_Syntax_Util.head_and_args' t1  in
             match uu____60864 with
             | (hd1,args) ->
                 let uu____60907 =
                   let uu____60922 =
                     let uu____60923 = FStar_Syntax_Util.un_uinst hd1  in
                     uu____60923.FStar_Syntax_Syntax.n  in
                   (uu____60922, args)  in
                 (match uu____60907 with
                  | (FStar_Syntax_Syntax.Tm_fvar
                     fv,uu____60943::uu____60944::(a,uu____60946)::[]) when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.inl_lid
                      ->
                      let uu____61013 =
                        let uu____61016 = unembed ea a  in
                        uu____61016 w norm1  in
                      FStar_Util.bind_opt uu____61013
                        (fun a1  ->
                           FStar_Pervasives_Native.Some (FStar_Util.Inl a1))
                  | (FStar_Syntax_Syntax.Tm_fvar
                     fv,uu____61040::uu____61041::(b,uu____61043)::[]) when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.inr_lid
                      ->
                      let uu____61110 =
                        let uu____61113 = unembed eb b  in
                        uu____61113 w norm1  in
                      FStar_Util.bind_opt uu____61110
                        (fun b1  ->
                           FStar_Pervasives_Native.Some (FStar_Util.Inr b1))
                  | uu____61136 ->
                      (if w
                       then
                         (let uu____61153 =
                            let uu____61159 =
                              let uu____61161 =
                                FStar_Syntax_Print.term_to_string t0  in
                              FStar_Util.format1 "Not an embedded sum: %s"
                                uu____61161
                               in
                            (FStar_Errors.Warning_NotEmbedded, uu____61159)
                             in
                          FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                            uu____61153)
                       else ();
                       FStar_Pervasives_Native.None)))
         in
      let uu____61171 =
        let uu____61172 = type_of ea  in
        let uu____61173 = type_of eb  in
        FStar_Syntax_Syntax.t_either_of uu____61172 uu____61173  in
      mk_emb_full em un uu____61171 printer emb_t_sum_a_b
  
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea  ->
    let t_list_a =
      let t_list = FStar_Syntax_Util.fvar_const FStar_Parser_Const.list_lid
         in
      let uu____61201 =
        let uu____61206 =
          let uu____61207 = FStar_Syntax_Syntax.as_arg ea.typ  in
          [uu____61207]  in
        FStar_Syntax_Syntax.mk_Tm_app t_list uu____61206  in
      uu____61201 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
    let emb_t_list_a =
      let uu____61235 =
        let uu____61243 =
          FStar_All.pipe_right FStar_Parser_Const.list_lid
            FStar_Ident.string_of_lid
           in
        (uu____61243, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____61235  in
    let printer l =
      let uu____61260 =
        let uu____61262 =
          let uu____61264 = FStar_List.map ea.print l  in
          FStar_All.pipe_right uu____61264 (FStar_String.concat "; ")  in
        Prims.op_Hat uu____61262 "]"  in
      Prims.op_Hat "[" uu____61260  in
    let rec em l rng shadow_l norm1 =
      lazy_embed printer emb_t_list_a rng t_list_a l
        (fun uu____61350  ->
           let t =
             let uu____61352 = type_of ea  in
             FStar_Syntax_Syntax.iarg uu____61352  in
           match l with
           | [] ->
               let uu____61353 =
                 let uu____61358 =
                   let uu____61359 =
                     FStar_Syntax_Syntax.tdataconstr
                       FStar_Parser_Const.nil_lid
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____61359
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 FStar_Syntax_Syntax.mk_Tm_app uu____61358 [t]  in
               uu____61353 FStar_Pervasives_Native.None rng
           | hd1::tl1 ->
               let cons1 =
                 let uu____61383 =
                   FStar_Syntax_Syntax.tdataconstr
                     FStar_Parser_Const.cons_lid
                    in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu____61383
                   [FStar_Syntax_Syntax.U_zero]
                  in
               let proj f cons_tm =
                 let fid = FStar_Ident.mk_ident (f, rng)  in
                 let proj =
                   FStar_Syntax_Util.mk_field_projector_name_from_ident
                     FStar_Parser_Const.cons_lid fid
                    in
                 let proj_tm =
                   let uu____61403 =
                     FStar_Syntax_Syntax.lid_as_fv proj
                       FStar_Syntax_Syntax.delta_equational
                       FStar_Pervasives_Native.None
                      in
                   FStar_Syntax_Syntax.fv_to_tm uu____61403  in
                 let uu____61404 =
                   let uu____61409 =
                     FStar_Syntax_Syntax.mk_Tm_uinst proj_tm
                       [FStar_Syntax_Syntax.U_zero]
                      in
                   let uu____61410 =
                     let uu____61411 =
                       let uu____61420 = type_of ea  in
                       FStar_Syntax_Syntax.iarg uu____61420  in
                     let uu____61421 =
                       let uu____61432 = FStar_Syntax_Syntax.as_arg cons_tm
                          in
                       [uu____61432]  in
                     uu____61411 :: uu____61421  in
                   FStar_Syntax_Syntax.mk_Tm_app uu____61409 uu____61410  in
                 uu____61404 FStar_Pervasives_Native.None rng  in
               let shadow_hd = map_shadow shadow_l (proj "hd")  in
               let shadow_tl = map_shadow shadow_l (proj "tl")  in
               let uu____61585 =
                 let uu____61590 =
                   let uu____61591 =
                     let uu____61602 =
                       let uu____61611 =
                         let uu____61612 = embed ea hd1  in
                         uu____61612 rng shadow_hd norm1  in
                       FStar_Syntax_Syntax.as_arg uu____61611  in
                     let uu____61682 =
                       let uu____61693 =
                         let uu____61702 = em tl1 rng shadow_tl norm1  in
                         FStar_Syntax_Syntax.as_arg uu____61702  in
                       [uu____61693]  in
                     uu____61602 :: uu____61682  in
                   t :: uu____61591  in
                 FStar_Syntax_Syntax.mk_Tm_app cons1 uu____61590  in
               uu____61585 FStar_Pervasives_Native.None rng)
       in
    let rec un t0 w norm1 =
      let t = FStar_Syntax_Util.unmeta_safe t0  in
      lazy_unembed printer emb_t_list_a t t_list_a
        (fun t1  ->
           let uu____61818 = FStar_Syntax_Util.head_and_args' t1  in
           match uu____61818 with
           | (hd1,args) ->
               let uu____61859 =
                 let uu____61872 =
                   let uu____61873 = FStar_Syntax_Util.un_uinst hd1  in
                   uu____61873.FStar_Syntax_Syntax.n  in
                 (uu____61872, args)  in
               (match uu____61859 with
                | (FStar_Syntax_Syntax.Tm_fvar fv,uu____61889) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.nil_lid
                    -> FStar_Pervasives_Native.Some []
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(uu____61909,FStar_Pervasives_Native.Some
                       (FStar_Syntax_Syntax.Implicit uu____61910))::(hd2,FStar_Pervasives_Native.None
                                                                    )::
                   (tl1,FStar_Pervasives_Native.None )::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.cons_lid
                    ->
                    let uu____61952 =
                      let uu____61955 = unembed ea hd2  in
                      uu____61955 w norm1  in
                    FStar_Util.bind_opt uu____61952
                      (fun hd3  ->
                         let uu____61973 = un tl1 w norm1  in
                         FStar_Util.bind_opt uu____61973
                           (fun tl2  ->
                              FStar_Pervasives_Native.Some (hd3 :: tl2)))
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(hd2,FStar_Pervasives_Native.None )::(tl1,FStar_Pervasives_Native.None
                                                            )::[])
                    when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.cons_lid
                    ->
                    let uu____62023 =
                      let uu____62026 = unembed ea hd2  in
                      uu____62026 w norm1  in
                    FStar_Util.bind_opt uu____62023
                      (fun hd3  ->
                         let uu____62044 = un tl1 w norm1  in
                         FStar_Util.bind_opt uu____62044
                           (fun tl2  ->
                              FStar_Pervasives_Native.Some (hd3 :: tl2)))
                | uu____62061 ->
                    (if w
                     then
                       (let uu____62076 =
                          let uu____62082 =
                            let uu____62084 =
                              FStar_Syntax_Print.term_to_string t0  in
                            FStar_Util.format1 "Not an embedded list: %s"
                              uu____62084
                             in
                          (FStar_Errors.Warning_NotEmbedded, uu____62082)  in
                        FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                          uu____62076)
                     else ();
                     FStar_Pervasives_Native.None)))
       in
    let uu____62092 =
      let uu____62093 = type_of ea  in
      FStar_Syntax_Syntax.t_list_of uu____62093  in
    mk_emb_full em un uu____62092 printer emb_t_list_a
  
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
    match projectee with | Simpl  -> true | uu____62136 -> false
  
let (uu___is_Weak : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Weak  -> true | uu____62147 -> false
  
let (uu___is_HNF : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | HNF  -> true | uu____62158 -> false
  
let (uu___is_Primops : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____62169 -> false
  
let (uu___is_Delta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Delta  -> true | uu____62180 -> false
  
let (uu___is_Zeta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Zeta  -> true | uu____62191 -> false
  
let (uu___is_Iota : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Iota  -> true | uu____62202 -> false
  
let (uu___is_Reify : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____62213 -> false
  
let (uu___is_UnfoldOnly : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____62228 -> false
  
let (__proj__UnfoldOnly__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldFully : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldFully _0 -> true | uu____62260 -> false
  
let (__proj__UnfoldFully__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldFully _0 -> _0 
let (uu___is_UnfoldAttr : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____62292 -> false
  
let (__proj__UnfoldAttr__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_NBE : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | NBE  -> true | uu____62320 -> false
  
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
    let uu____62338 =
      FStar_Ident.lid_of_str "FStar.Syntax.Embeddings.norm_step"  in
    FStar_Syntax_Util.fvar_const uu____62338  in
  let emb_t_norm_step =
    let uu____62341 =
      let uu____62349 =
        FStar_All.pipe_right FStar_Parser_Const.norm_step_lid
          FStar_Ident.string_of_lid
         in
      (uu____62349, [])  in
    FStar_Syntax_Syntax.ET_app uu____62341  in
  let printer uu____62361 = "norm_step"  in
  let em n1 rng _topt norm1 =
    lazy_embed printer emb_t_norm_step rng t_norm_step1 n1
      (fun uu____62427  ->
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
             let uu____62432 =
               let uu____62437 =
                 let uu____62438 =
                   let uu____62447 =
                     let uu____62448 =
                       let uu____62455 = e_list e_string  in
                       embed uu____62455 l  in
                     uu____62448 rng FStar_Pervasives_Native.None norm1  in
                   FStar_Syntax_Syntax.as_arg uu____62447  in
                 [uu____62438]  in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldOnly uu____62437  in
             uu____62432 FStar_Pervasives_Native.None rng
         | UnfoldFully l ->
             let uu____62514 =
               let uu____62519 =
                 let uu____62520 =
                   let uu____62529 =
                     let uu____62530 =
                       let uu____62537 = e_list e_string  in
                       embed uu____62537 l  in
                     uu____62530 rng FStar_Pervasives_Native.None norm1  in
                   FStar_Syntax_Syntax.as_arg uu____62529  in
                 [uu____62520]  in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldFully uu____62519
                in
             uu____62514 FStar_Pervasives_Native.None rng
         | UnfoldAttr l ->
             let uu____62596 =
               let uu____62601 =
                 let uu____62602 =
                   let uu____62611 =
                     let uu____62612 =
                       let uu____62619 = e_list e_string  in
                       embed uu____62619 l  in
                     uu____62612 rng FStar_Pervasives_Native.None norm1  in
                   FStar_Syntax_Syntax.as_arg uu____62611  in
                 [uu____62602]  in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldAttr uu____62601  in
             uu____62596 FStar_Pervasives_Native.None rng)
     in
  let un t0 w norm1 =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    lazy_unembed printer emb_t_norm_step t t_norm_step1
      (fun t1  ->
         let uu____62708 = FStar_Syntax_Util.head_and_args t1  in
         match uu____62708 with
         | (hd1,args) ->
             let uu____62753 =
               let uu____62768 =
                 let uu____62769 = FStar_Syntax_Util.un_uinst hd1  in
                 uu____62769.FStar_Syntax_Syntax.n  in
               (uu____62768, args)  in
             (match uu____62753 with
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
              | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____62957)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldonly
                  ->
                  let uu____62992 =
                    let uu____62998 =
                      let uu____63008 = e_list e_string  in
                      unembed uu____63008 l  in
                    uu____62998 w norm1  in
                  FStar_Util.bind_opt uu____62992
                    (fun ss  ->
                       FStar_All.pipe_left
                         (fun _63034  -> FStar_Pervasives_Native.Some _63034)
                         (UnfoldOnly ss))
              | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____63037)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldfully
                  ->
                  let uu____63072 =
                    let uu____63078 =
                      let uu____63088 = e_list e_string  in
                      unembed uu____63088 l  in
                    uu____63078 w norm1  in
                  FStar_Util.bind_opt uu____63072
                    (fun ss  ->
                       FStar_All.pipe_left
                         (fun _63114  -> FStar_Pervasives_Native.Some _63114)
                         (UnfoldFully ss))
              | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____63117)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldattr
                  ->
                  let uu____63152 =
                    let uu____63158 =
                      let uu____63168 = e_list e_string  in
                      unembed uu____63168 l  in
                    uu____63158 w norm1  in
                  FStar_Util.bind_opt uu____63152
                    (fun ss  ->
                       FStar_All.pipe_left
                         (fun _63194  -> FStar_Pervasives_Native.Some _63194)
                         (UnfoldAttr ss))
              | uu____63195 ->
                  (if w
                   then
                     (let uu____63212 =
                        let uu____63218 =
                          let uu____63220 =
                            FStar_Syntax_Print.term_to_string t0  in
                          FStar_Util.format1 "Not an embedded norm_step: %s"
                            uu____63220
                           in
                        (FStar_Errors.Warning_NotEmbedded, uu____63218)  in
                      FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                        uu____63212)
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
    | uu____63322 ->
        (if w
         then
           (let uu____63325 =
              let uu____63331 =
                let uu____63333 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded range: %s" uu____63333
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____63331)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____63325)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____63339 =
    let uu____63340 =
      let uu____63348 =
        FStar_All.pipe_right FStar_Parser_Const.range_lid
          FStar_Ident.string_of_lid
         in
      (uu____63348, [])  in
    FStar_Syntax_Syntax.ET_app uu____63340  in
  mk_emb_full em un FStar_Syntax_Syntax.t_range FStar_Range.string_of_range
    uu____63339
  
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
        let uu____63419 =
          let uu____63426 =
            let uu____63427 =
              let uu____63442 =
                let uu____63451 =
                  let uu____63458 = FStar_Syntax_Syntax.null_bv ea.typ  in
                  (uu____63458, FStar_Pervasives_Native.None)  in
                [uu____63451]  in
              let uu____63473 = FStar_Syntax_Syntax.mk_Total eb.typ  in
              (uu____63442, uu____63473)  in
            FStar_Syntax_Syntax.Tm_arrow uu____63427  in
          FStar_Syntax_Syntax.mk uu____63426  in
        uu____63419 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
      let emb_t_arr_a_b =
        FStar_Syntax_Syntax.ET_fun ((ea.emb_typ), (eb.emb_typ))  in
      let printer f = "<fun>"  in
      let em f rng shadow_f norm1 =
        lazy_embed (fun uu____63586  -> "<fun>") emb_t_arr_a_b rng t_arrow f
          (fun uu____63592  ->
             let uu____63593 = force_shadow shadow_f  in
             match uu____63593 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Exn.raise Embedding_failure
             | FStar_Pervasives_Native.Some repr_f ->
                 ((let uu____63655 =
                     FStar_ST.op_Bang FStar_Options.debug_embedding  in
                   if uu____63655
                   then
                     let uu____63679 =
                       FStar_Syntax_Print.term_to_string repr_f  in
                     let uu____63681 = FStar_Util.stack_dump ()  in
                     FStar_Util.print2
                       "e_arrow forced back to term using shadow %s; repr=%s\n"
                       uu____63679 uu____63681
                   else ());
                  (let res = norm1 (FStar_Util.Inr repr_f)  in
                   (let uu____63688 =
                      FStar_ST.op_Bang FStar_Options.debug_embedding  in
                    if uu____63688
                    then
                      let uu____63712 =
                        FStar_Syntax_Print.term_to_string repr_f  in
                      let uu____63714 = FStar_Syntax_Print.term_to_string res
                         in
                      let uu____63716 = FStar_Util.stack_dump ()  in
                      FStar_Util.print3
                        "e_arrow forced back to term using shadow %s; repr=%s\n\t%s\n"
                        uu____63712 uu____63714 uu____63716
                    else ());
                   res)))
         in
      let un f w norm1 =
        lazy_unembed printer emb_t_arr_a_b f t_arrow
          (fun f1  ->
             let f_wrapped a =
               (let uu____63775 =
                  FStar_ST.op_Bang FStar_Options.debug_embedding  in
                if uu____63775
                then
                  let uu____63799 = FStar_Syntax_Print.term_to_string f1  in
                  let uu____63801 = FStar_Util.stack_dump ()  in
                  FStar_Util.print2
                    "Calling back into normalizer for %s\n%s\n" uu____63799
                    uu____63801
                else ());
               (let a_tm =
                  let uu____63807 = embed ea a  in
                  uu____63807 f1.FStar_Syntax_Syntax.pos
                    FStar_Pervasives_Native.None norm1
                   in
                let b_tm =
                  let uu____63840 =
                    let uu____63845 =
                      let uu____63846 =
                        let uu____63851 =
                          let uu____63852 = FStar_Syntax_Syntax.as_arg a_tm
                             in
                          [uu____63852]  in
                        FStar_Syntax_Syntax.mk_Tm_app f1 uu____63851  in
                      uu____63846 FStar_Pervasives_Native.None
                        f1.FStar_Syntax_Syntax.pos
                       in
                    FStar_Util.Inr uu____63845  in
                  norm1 uu____63840  in
                let uu____63879 =
                  let uu____63882 = unembed eb b_tm  in uu____63882 w norm1
                   in
                match uu____63879 with
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
                let uu____63982 = FStar_List.splitAt n_tvars args  in
                match uu____63982 with
                | (_tvar_args,rest_args) ->
                    let uu____64059 = FStar_List.hd rest_args  in
                    (match uu____64059 with
                     | (x,uu____64079) ->
                         let shadow_app =
                           let uu____64093 =
                             FStar_Common.mk_thunk
                               (fun uu____64102  ->
                                  let uu____64103 =
                                    let uu____64108 =
                                      norm1 (FStar_Util.Inl fv_lid1)  in
                                    FStar_Syntax_Syntax.mk_Tm_app uu____64108
                                      args
                                     in
                                  uu____64103 FStar_Pervasives_Native.None
                                    rng)
                              in
                           FStar_Pervasives_Native.Some uu____64093  in
                         let uu____64154 =
                           let uu____64157 =
                             let uu____64160 = unembed ea x  in
                             uu____64160 true norm1  in
                           FStar_Util.map_opt uu____64157
                             (fun x1  ->
                                let uu____64200 =
                                  let uu____64207 = f x1  in
                                  embed eb uu____64207  in
                                uu____64200 rng shadow_app norm1)
                            in
                         (match uu____64154 with
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
                  let uu____64337 = FStar_List.splitAt n_tvars args  in
                  match uu____64337 with
                  | (_tvar_args,rest_args) ->
                      let uu____64400 = FStar_List.hd rest_args  in
                      (match uu____64400 with
                       | (x,uu____64416) ->
                           let uu____64421 =
                             let uu____64428 = FStar_List.tl rest_args  in
                             FStar_List.hd uu____64428  in
                           (match uu____64421 with
                            | (y,uu____64452) ->
                                let shadow_app =
                                  let uu____64462 =
                                    FStar_Common.mk_thunk
                                      (fun uu____64471  ->
                                         let uu____64472 =
                                           let uu____64477 =
                                             norm1 (FStar_Util.Inl fv_lid1)
                                              in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____64477 args
                                            in
                                         uu____64472
                                           FStar_Pervasives_Native.None rng)
                                     in
                                  FStar_Pervasives_Native.Some uu____64462
                                   in
                                let uu____64523 =
                                  let uu____64526 =
                                    let uu____64529 = unembed ea x  in
                                    uu____64529 true norm1  in
                                  FStar_Util.bind_opt uu____64526
                                    (fun x1  ->
                                       let uu____64546 =
                                         let uu____64549 = unembed eb y  in
                                         uu____64549 true norm1  in
                                       FStar_Util.bind_opt uu____64546
                                         (fun y1  ->
                                            let uu____64566 =
                                              let uu____64567 =
                                                let uu____64574 = f x1 y1  in
                                                embed ec uu____64574  in
                                              uu____64567 rng shadow_app
                                                norm1
                                               in
                                            FStar_Pervasives_Native.Some
                                              uu____64566))
                                   in
                                (match uu____64523 with
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
                    let uu____64723 = FStar_List.splitAt n_tvars args  in
                    match uu____64723 with
                    | (_tvar_args,rest_args) ->
                        let uu____64786 = FStar_List.hd rest_args  in
                        (match uu____64786 with
                         | (x,uu____64802) ->
                             let uu____64807 =
                               let uu____64814 = FStar_List.tl rest_args  in
                               FStar_List.hd uu____64814  in
                             (match uu____64807 with
                              | (y,uu____64838) ->
                                  let uu____64843 =
                                    let uu____64850 =
                                      let uu____64859 =
                                        FStar_List.tl rest_args  in
                                      FStar_List.tl uu____64859  in
                                    FStar_List.hd uu____64850  in
                                  (match uu____64843 with
                                   | (z,uu____64889) ->
                                       let shadow_app =
                                         let uu____64899 =
                                           FStar_Common.mk_thunk
                                             (fun uu____64908  ->
                                                let uu____64909 =
                                                  let uu____64914 =
                                                    norm1
                                                      (FStar_Util.Inl fv_lid1)
                                                     in
                                                  FStar_Syntax_Syntax.mk_Tm_app
                                                    uu____64914 args
                                                   in
                                                uu____64909
                                                  FStar_Pervasives_Native.None
                                                  rng)
                                            in
                                         FStar_Pervasives_Native.Some
                                           uu____64899
                                          in
                                       let uu____64960 =
                                         let uu____64963 =
                                           let uu____64966 = unembed ea x  in
                                           uu____64966 true norm1  in
                                         FStar_Util.bind_opt uu____64963
                                           (fun x1  ->
                                              let uu____64983 =
                                                let uu____64986 =
                                                  unembed eb y  in
                                                uu____64986 true norm1  in
                                              FStar_Util.bind_opt uu____64983
                                                (fun y1  ->
                                                   let uu____65003 =
                                                     let uu____65006 =
                                                       unembed ec z  in
                                                     uu____65006 true norm1
                                                      in
                                                   FStar_Util.bind_opt
                                                     uu____65003
                                                     (fun z1  ->
                                                        let uu____65023 =
                                                          let uu____65024 =
                                                            let uu____65031 =
                                                              f x1 y1 z1  in
                                                            embed ed
                                                              uu____65031
                                                             in
                                                          uu____65024 rng
                                                            shadow_app norm1
                                                           in
                                                        FStar_Pervasives_Native.Some
                                                          uu____65023)))
                                          in
                                       (match uu____64960 with
                                        | FStar_Pervasives_Native.Some x1 ->
                                            FStar_Pervasives_Native.Some x1
                                        | FStar_Pervasives_Native.None  ->
                                            force_shadow shadow_app))))
                     in
                  f_wrapped
  
let debug_wrap : 'a . Prims.string -> (unit -> 'a) -> 'a =
  fun s  ->
    fun f  ->
      (let uu____65086 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
       if uu____65086 then FStar_Util.print1 "++++starting %s\n" s else ());
      (let res = f ()  in
       (let uu____65115 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
        if uu____65115 then FStar_Util.print1 "------ending %s\n" s else ());
       res)
  