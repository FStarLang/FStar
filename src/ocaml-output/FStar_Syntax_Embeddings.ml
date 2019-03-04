open Prims
type norm_cb =
  (FStar_Ident.lid,FStar_Syntax_Syntax.term) FStar_Util.either ->
    FStar_Syntax_Syntax.term
let (id_norm_cb : norm_cb) =
  fun uu___429_55317  ->
    match uu___429_55317 with
    | FStar_Util.Inr x -> x
    | FStar_Util.Inl l ->
        let uu____55324 =
          FStar_Syntax_Syntax.lid_as_fv l
            FStar_Syntax_Syntax.delta_equational FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.fv_to_tm uu____55324
  
exception Embedding_failure 
let (uu___is_Embedding_failure : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Embedding_failure  -> true | uu____55334 -> false
  
exception Unembedding_failure 
let (uu___is_Unembedding_failure : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Unembedding_failure  -> true
    | uu____55345 -> false
  
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
             (fun uu____55511  ->
                let uu____55512 = FStar_Common.force_thunk s1  in
                f uu____55512))
  
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
  'Auu____56146 . FStar_Syntax_Syntax.term -> 'Auu____56146 -> Prims.string =
  fun typ  ->
    fun uu____56157  ->
      let uu____56158 = FStar_Syntax_Print.term_to_string typ  in
      FStar_Util.format1 "unknown %s" uu____56158
  
let (term_as_fv : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.fv) =
  fun t  ->
    let uu____56167 =
      let uu____56168 = FStar_Syntax_Subst.compress t  in
      uu____56168.FStar_Syntax_Syntax.n  in
    match uu____56167 with
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv
    | uu____56172 ->
        let uu____56173 =
          let uu____56175 = FStar_Syntax_Print.term_to_string t  in
          FStar_Util.format1 "Embeddings not defined for type %s" uu____56175
           in
        failwith uu____56173
  
let mk_emb :
  'a .
    'a raw_embedder ->
      'a raw_unembedder -> FStar_Syntax_Syntax.fv -> 'a embedding
  =
  fun em  ->
    fun un  ->
      fun fv  ->
        let typ = FStar_Syntax_Syntax.fv_to_tm fv  in
        let uu____56303 =
          let uu____56304 =
            let uu____56312 =
              let uu____56314 = FStar_Syntax_Syntax.lid_of_fv fv  in
              FStar_All.pipe_right uu____56314 FStar_Ident.string_of_lid  in
            (uu____56312, [])  in
          FStar_Syntax_Syntax.ET_app uu____56304  in
        { em; un; typ; print = (unknown_printer typ); emb_typ = uu____56303 }
  
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
      fun n1  -> let uu____56724 = unembed e t  in uu____56724 true n1
  
let try_unembed :
  'a .
    'a embedding ->
      FStar_Syntax_Syntax.term ->
        norm_cb -> 'a FStar_Pervasives_Native.option
  =
  fun e  ->
    fun t  ->
      fun n1  -> let uu____56773 = unembed e t  in uu____56773 false n1
  
let type_of : 'a . 'a embedding -> FStar_Syntax_Syntax.typ = fun e  -> e.typ 
let set_type : 'a . FStar_Syntax_Syntax.typ -> 'a embedding -> 'a embedding =
  fun ty  ->
    fun e  ->
      let uu___508_56826 = e  in
      {
        em = (uu___508_56826.em);
        un = (uu___508_56826.un);
        typ = ty;
        print = (uu___508_56826.print);
        emb_typ = (uu___508_56826.emb_typ)
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
              (let uu____56895 =
                 FStar_ST.op_Bang FStar_Options.debug_embedding  in
               if uu____56895
               then
                 let uu____56919 = FStar_Syntax_Print.term_to_string ta  in
                 let uu____56921 = FStar_Syntax_Print.emb_typ_to_string et
                    in
                 let uu____56923 = pa x  in
                 FStar_Util.print3
                   "Embedding a %s\n\temb_typ=%s\n\tvalue is %s\n"
                   uu____56919 uu____56921 uu____56923
               else ());
              (let uu____56930 =
                 FStar_ST.op_Bang FStar_Options.eager_embedding  in
               if uu____56930
               then f ()
               else
                 (let thunk1 = FStar_Common.mk_thunk f  in
                  let uu____56965 =
                    let uu____56972 =
                      let uu____56973 =
                        let uu____56974 = FStar_Dyn.mkdyn x  in
                        {
                          FStar_Syntax_Syntax.blob = uu____56974;
                          FStar_Syntax_Syntax.lkind =
                            (FStar_Syntax_Syntax.Lazy_embedding (et, thunk1));
                          FStar_Syntax_Syntax.ltyp = FStar_Syntax_Syntax.tun;
                          FStar_Syntax_Syntax.rng = rng
                        }  in
                      FStar_Syntax_Syntax.Tm_lazy uu____56973  in
                    FStar_Syntax_Syntax.mk uu____56972  in
                  uu____56965 FStar_Pervasives_Native.None rng))
  
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
                  FStar_Syntax_Syntax.ltyp = uu____57090;
                  FStar_Syntax_Syntax.rng = uu____57091;_}
                ->
                let uu____57102 =
                  (et <> et') ||
                    (FStar_ST.op_Bang FStar_Options.eager_embedding)
                   in
                if uu____57102
                then
                  let res =
                    let uu____57131 = FStar_Common.force_thunk t  in
                    f uu____57131  in
                  ((let uu____57175 =
                      FStar_ST.op_Bang FStar_Options.debug_embedding  in
                    if uu____57175
                    then
                      let uu____57199 =
                        FStar_Syntax_Print.emb_typ_to_string et  in
                      let uu____57201 =
                        FStar_Syntax_Print.emb_typ_to_string et'  in
                      let uu____57203 =
                        match res with
                        | FStar_Pervasives_Native.None  -> "None"
                        | FStar_Pervasives_Native.Some x2 ->
                            let uu____57208 = pa x2  in
                            Prims.op_Hat "Some " uu____57208
                         in
                      FStar_Util.print3
                        "Unembed cancellation failed\n\t%s <> %s\nvalue is %s\n"
                        uu____57199 uu____57201 uu____57203
                    else ());
                   res)
                else
                  (let a = FStar_Dyn.undyn b  in
                   (let uu____57220 =
                      FStar_ST.op_Bang FStar_Options.debug_embedding  in
                    if uu____57220
                    then
                      let uu____57244 =
                        FStar_Syntax_Print.emb_typ_to_string et  in
                      let uu____57246 = pa a  in
                      FStar_Util.print2
                        "Unembed cancelled for %s\n\tvalue is %s\n"
                        uu____57244 uu____57246
                    else ());
                   FStar_Pervasives_Native.Some a)
            | uu____57253 ->
                let aopt = f x1  in
                ((let uu____57258 =
                    FStar_ST.op_Bang FStar_Options.debug_embedding  in
                  if uu____57258
                  then
                    let uu____57282 = FStar_Syntax_Print.emb_typ_to_string et
                       in
                    let uu____57284 = FStar_Syntax_Print.term_to_string x1
                       in
                    let uu____57286 =
                      match aopt with
                      | FStar_Pervasives_Native.None  -> "None"
                      | FStar_Pervasives_Native.Some a ->
                          let uu____57291 = pa a  in
                          Prims.op_Hat "Some " uu____57291
                       in
                    FStar_Util.print3
                      "Unembedding:\n\temb_typ=%s\n\tterm is %s\n\tvalue is %s\n"
                      uu____57282 uu____57284 uu____57286
                  else ());
                 aopt)
  
let (mk_any_emb :
  FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term embedding) =
  fun typ  ->
    let em t _r _topt _norm =
      (let uu____57371 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
       if uu____57371
       then
         let uu____57395 = unknown_printer typ t  in
         FStar_Util.print1 "Embedding abstract: %s\n" uu____57395
       else ());
      t  in
    let un t _w _n =
      (let uu____57425 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
       if uu____57425
       then
         let uu____57449 = unknown_printer typ t  in
         FStar_Util.print1 "Unembedding abstract: %s\n" uu____57449
       else ());
      FStar_Pervasives_Native.Some t  in
    mk_emb_full em un typ (unknown_printer typ)
      FStar_Syntax_Syntax.ET_abstract
  
let (e_any : FStar_Syntax_Syntax.term embedding) =
  let em t _r _topt _norm = t  in
  let un t _w _n = FStar_Pervasives_Native.Some t  in
  let uu____57544 =
    let uu____57545 =
      let uu____57553 =
        FStar_All.pipe_right FStar_Parser_Const.term_lid
          FStar_Ident.string_of_lid
         in
      (uu____57553, [])  in
    FStar_Syntax_Syntax.ET_app uu____57545  in
  mk_emb_full em un FStar_Syntax_Syntax.t_term
    FStar_Syntax_Print.term_to_string uu____57544
  
let (e_unit : unit embedding) =
  let em u rng _topt _norm =
    let uu___582_57625 = FStar_Syntax_Util.exp_unit  in
    {
      FStar_Syntax_Syntax.n = (uu___582_57625.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___582_57625.FStar_Syntax_Syntax.vars)
    }  in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unascribe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit ) ->
        FStar_Pervasives_Native.Some ()
    | uu____57655 ->
        (if w
         then
           (let uu____57658 =
              let uu____57664 =
                let uu____57666 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded unit: %s" uu____57666  in
              (FStar_Errors.Warning_NotEmbedded, uu____57664)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____57658)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____57672 =
    let uu____57673 =
      let uu____57681 =
        FStar_All.pipe_right FStar_Parser_Const.unit_lid
          FStar_Ident.string_of_lid
         in
      (uu____57681, [])  in
    FStar_Syntax_Syntax.ET_app uu____57673  in
  mk_emb_full em un FStar_Syntax_Syntax.t_unit (fun uu____57688  -> "()")
    uu____57672
  
let (e_bool : Prims.bool embedding) =
  let em b rng _topt _norm =
    let t =
      if b
      then FStar_Syntax_Util.exp_true_bool
      else FStar_Syntax_Util.exp_false_bool  in
    let uu___602_57767 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___602_57767.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___602_57767.FStar_Syntax_Syntax.vars)
    }  in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) ->
        FStar_Pervasives_Native.Some b
    | uu____57805 ->
        (if w
         then
           (let uu____57808 =
              let uu____57814 =
                let uu____57816 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded bool: %s" uu____57816  in
              (FStar_Errors.Warning_NotEmbedded, uu____57814)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____57808)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____57823 =
    let uu____57824 =
      let uu____57832 =
        FStar_All.pipe_right FStar_Parser_Const.bool_lid
          FStar_Ident.string_of_lid
         in
      (uu____57832, [])  in
    FStar_Syntax_Syntax.ET_app uu____57824  in
  mk_emb_full em un FStar_Syntax_Syntax.t_bool FStar_Util.string_of_bool
    uu____57823
  
let (e_char : FStar_Char.char embedding) =
  let em c rng _topt _norm =
    let t = FStar_Syntax_Util.exp_char c  in
    let uu___621_57909 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___621_57909.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___621_57909.FStar_Syntax_Syntax.vars)
    }  in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c) ->
        FStar_Pervasives_Native.Some c
    | uu____57945 ->
        (if w
         then
           (let uu____57948 =
              let uu____57954 =
                let uu____57956 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded char: %s" uu____57956  in
              (FStar_Errors.Warning_NotEmbedded, uu____57954)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____57948)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____57963 =
    let uu____57964 =
      let uu____57972 =
        FStar_All.pipe_right FStar_Parser_Const.char_lid
          FStar_Ident.string_of_lid
         in
      (uu____57972, [])  in
    FStar_Syntax_Syntax.ET_app uu____57964  in
  mk_emb_full em un FStar_Syntax_Syntax.t_char FStar_Util.string_of_char
    uu____57963
  
let (e_int : FStar_BigInt.t embedding) =
  let t_int1 = FStar_Syntax_Util.fvar_const FStar_Parser_Const.int_lid  in
  let emb_t_int =
    let uu____57984 =
      let uu____57992 =
        FStar_All.pipe_right FStar_Parser_Const.int_lid
          FStar_Ident.string_of_lid
         in
      (uu____57992, [])  in
    FStar_Syntax_Syntax.ET_app uu____57984  in
  let em i rng _topt _norm =
    lazy_embed FStar_BigInt.string_of_big_int emb_t_int rng t_int1 i
      (fun uu____58063  ->
         let uu____58064 = FStar_BigInt.string_of_big_int i  in
         FStar_Syntax_Util.exp_int uu____58064)
     in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    lazy_unembed FStar_BigInt.string_of_big_int emb_t_int t t_int1
      (fun t1  ->
         match t1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
             (s,uu____58101)) ->
             let uu____58116 = FStar_BigInt.big_int_of_string s  in
             FStar_Pervasives_Native.Some uu____58116
         | uu____58117 ->
             (if w
              then
                (let uu____58120 =
                   let uu____58126 =
                     let uu____58128 = FStar_Syntax_Print.term_to_string t0
                        in
                     FStar_Util.format1 "Not an embedded int: %s" uu____58128
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____58126)  in
                 FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                   uu____58120)
              else ();
              FStar_Pervasives_Native.None))
     in
  mk_emb_full em un FStar_Syntax_Syntax.t_int FStar_BigInt.string_of_big_int
    emb_t_int
  
let (e_string : Prims.string embedding) =
  let emb_t_string =
    let uu____58139 =
      let uu____58147 =
        FStar_All.pipe_right FStar_Parser_Const.string_lid
          FStar_Ident.string_of_lid
         in
      (uu____58147, [])  in
    FStar_Syntax_Syntax.ET_app uu____58139  in
  let em s rng _topt _norm =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, rng)))
      FStar_Pervasives_Native.None rng
     in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
        (s,uu____58252)) -> FStar_Pervasives_Native.Some s
    | uu____58256 ->
        (if w
         then
           (let uu____58259 =
              let uu____58265 =
                let uu____58267 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded string: %s" uu____58267
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____58265)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____58259)
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
      let uu____58303 =
        let uu____58308 =
          let uu____58309 = FStar_Syntax_Syntax.as_arg ea.typ  in
          [uu____58309]  in
        FStar_Syntax_Syntax.mk_Tm_app t_opt uu____58308  in
      uu____58303 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
    let emb_t_option_a =
      let uu____58337 =
        let uu____58345 =
          FStar_All.pipe_right FStar_Parser_Const.option_lid
            FStar_Ident.string_of_lid
           in
        (uu____58345, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____58337  in
    let printer uu___430_58359 =
      match uu___430_58359 with
      | FStar_Pervasives_Native.None  -> "None"
      | FStar_Pervasives_Native.Some x ->
          let uu____58365 =
            let uu____58367 = ea.print x  in Prims.op_Hat uu____58367 ")"  in
          Prims.op_Hat "(Some " uu____58365
       in
    let em o rng topt norm1 =
      lazy_embed printer emb_t_option_a rng t_option_a o
        (fun uu____58444  ->
           match o with
           | FStar_Pervasives_Native.None  ->
               let uu____58445 =
                 let uu____58450 =
                   let uu____58451 =
                     FStar_Syntax_Syntax.tdataconstr
                       FStar_Parser_Const.none_lid
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____58451
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 let uu____58452 =
                   let uu____58453 =
                     let uu____58462 = type_of ea  in
                     FStar_Syntax_Syntax.iarg uu____58462  in
                   [uu____58453]  in
                 FStar_Syntax_Syntax.mk_Tm_app uu____58450 uu____58452  in
               uu____58445 FStar_Pervasives_Native.None rng
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
                        let uu____58553 =
                          FStar_Syntax_Syntax.lid_as_fv some_v
                            FStar_Syntax_Syntax.delta_equational
                            FStar_Pervasives_Native.None
                           in
                        FStar_Syntax_Syntax.fv_to_tm uu____58553  in
                      let uu____58554 =
                        let uu____58559 =
                          FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm
                            [FStar_Syntax_Syntax.U_zero]
                           in
                        let uu____58560 =
                          let uu____58561 =
                            let uu____58570 = type_of ea  in
                            FStar_Syntax_Syntax.iarg uu____58570  in
                          let uu____58571 =
                            let uu____58582 = FStar_Syntax_Syntax.as_arg t
                               in
                            [uu____58582]  in
                          uu____58561 :: uu____58571  in
                        FStar_Syntax_Syntax.mk_Tm_app uu____58559 uu____58560
                         in
                      uu____58554 FStar_Pervasives_Native.None rng)
                  in
               let uu____58617 =
                 let uu____58622 =
                   let uu____58623 =
                     FStar_Syntax_Syntax.tdataconstr
                       FStar_Parser_Const.some_lid
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____58623
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 let uu____58624 =
                   let uu____58625 =
                     let uu____58634 = type_of ea  in
                     FStar_Syntax_Syntax.iarg uu____58634  in
                   let uu____58635 =
                     let uu____58646 =
                       let uu____58655 =
                         let uu____58656 = embed ea a  in
                         uu____58656 rng shadow_a norm1  in
                       FStar_Syntax_Syntax.as_arg uu____58655  in
                     [uu____58646]  in
                   uu____58625 :: uu____58635  in
                 FStar_Syntax_Syntax.mk_Tm_app uu____58622 uu____58624  in
               uu____58617 FStar_Pervasives_Native.None rng)
       in
    let un t0 w norm1 =
      let t = FStar_Syntax_Util.unmeta_safe t0  in
      lazy_unembed printer emb_t_option_a t t_option_a
        (fun t1  ->
           let uu____58793 = FStar_Syntax_Util.head_and_args' t1  in
           match uu____58793 with
           | (hd1,args) ->
               let uu____58834 =
                 let uu____58849 =
                   let uu____58850 = FStar_Syntax_Util.un_uinst hd1  in
                   uu____58850.FStar_Syntax_Syntax.n  in
                 (uu____58849, args)  in
               (match uu____58834 with
                | (FStar_Syntax_Syntax.Tm_fvar fv,uu____58868) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.none_lid
                    ->
                    FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,uu____58892::(a,uu____58894)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.some_lid
                    ->
                    let uu____58945 =
                      let uu____58948 = unembed ea a  in uu____58948 w norm1
                       in
                    FStar_Util.bind_opt uu____58945
                      (fun a1  ->
                         FStar_Pervasives_Native.Some
                           (FStar_Pervasives_Native.Some a1))
                | uu____58967 ->
                    (if w
                     then
                       (let uu____58984 =
                          let uu____58990 =
                            let uu____58992 =
                              FStar_Syntax_Print.term_to_string t0  in
                            FStar_Util.format1 "Not an embedded option: %s"
                              uu____58992
                             in
                          (FStar_Errors.Warning_NotEmbedded, uu____58990)  in
                        FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                          uu____58984)
                     else ();
                     FStar_Pervasives_Native.None)))
       in
    let uu____59000 =
      let uu____59001 = type_of ea  in
      FStar_Syntax_Syntax.t_option_of uu____59001  in
    mk_emb_full em un uu____59000 printer emb_t_option_a
  
let e_tuple2 : 'a 'b . 'a embedding -> 'b embedding -> ('a * 'b) embedding =
  fun ea  ->
    fun eb  ->
      let t_pair_a_b =
        let t_tup2 =
          FStar_Syntax_Util.fvar_const FStar_Parser_Const.lid_tuple2  in
        let uu____59043 =
          let uu____59048 =
            let uu____59049 = FStar_Syntax_Syntax.as_arg ea.typ  in
            let uu____59058 =
              let uu____59069 = FStar_Syntax_Syntax.as_arg eb.typ  in
              [uu____59069]  in
            uu____59049 :: uu____59058  in
          FStar_Syntax_Syntax.mk_Tm_app t_tup2 uu____59048  in
        uu____59043 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
      let emb_t_pair_a_b =
        let uu____59105 =
          let uu____59113 =
            FStar_All.pipe_right FStar_Parser_Const.lid_tuple2
              FStar_Ident.string_of_lid
             in
          (uu____59113, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____59105  in
      let printer uu____59129 =
        match uu____59129 with
        | (x,y) ->
            let uu____59137 = ea.print x  in
            let uu____59139 = eb.print y  in
            FStar_Util.format2 "(%s, %s)" uu____59137 uu____59139
         in
      let em x rng topt norm1 =
        lazy_embed printer emb_t_pair_a_b rng t_pair_a_b x
          (fun uu____59224  ->
             let proj i ab =
               let uu____59240 =
                 let uu____59245 =
                   FStar_Parser_Const.mk_tuple_data_lid (Prims.parse_int "2")
                     rng
                    in
                 let uu____59247 =
                   FStar_Syntax_Syntax.null_bv FStar_Syntax_Syntax.tun  in
                 FStar_Syntax_Util.mk_field_projector_name uu____59245
                   uu____59247 i
                  in
               match uu____59240 with
               | (proj_1,uu____59251) ->
                   let proj_1_tm =
                     let uu____59253 =
                       FStar_Syntax_Syntax.lid_as_fv proj_1
                         FStar_Syntax_Syntax.delta_equational
                         FStar_Pervasives_Native.None
                        in
                     FStar_Syntax_Syntax.fv_to_tm uu____59253  in
                   let uu____59254 =
                     let uu____59259 =
                       FStar_Syntax_Syntax.mk_Tm_uinst proj_1_tm
                         [FStar_Syntax_Syntax.U_zero]
                        in
                     let uu____59260 =
                       let uu____59261 =
                         let uu____59270 = type_of ea  in
                         FStar_Syntax_Syntax.iarg uu____59270  in
                       let uu____59271 =
                         let uu____59282 =
                           let uu____59291 = type_of eb  in
                           FStar_Syntax_Syntax.iarg uu____59291  in
                         let uu____59292 =
                           let uu____59303 = FStar_Syntax_Syntax.as_arg ab
                              in
                           [uu____59303]  in
                         uu____59282 :: uu____59292  in
                       uu____59261 :: uu____59271  in
                     FStar_Syntax_Syntax.mk_Tm_app uu____59259 uu____59260
                      in
                   uu____59254 FStar_Pervasives_Native.None rng
                in
             let shadow_a = map_shadow topt (proj (Prims.parse_int "1"))  in
             let shadow_b = map_shadow topt (proj (Prims.parse_int "2"))  in
             let uu____59464 =
               let uu____59469 =
                 let uu____59470 =
                   FStar_Syntax_Syntax.tdataconstr
                     FStar_Parser_Const.lid_Mktuple2
                    in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu____59470
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                  in
               let uu____59471 =
                 let uu____59472 =
                   let uu____59481 = type_of ea  in
                   FStar_Syntax_Syntax.iarg uu____59481  in
                 let uu____59482 =
                   let uu____59493 =
                     let uu____59502 = type_of eb  in
                     FStar_Syntax_Syntax.iarg uu____59502  in
                   let uu____59503 =
                     let uu____59514 =
                       let uu____59523 =
                         let uu____59524 =
                           embed ea (FStar_Pervasives_Native.fst x)  in
                         uu____59524 rng shadow_a norm1  in
                       FStar_Syntax_Syntax.as_arg uu____59523  in
                     let uu____59594 =
                       let uu____59605 =
                         let uu____59614 =
                           let uu____59615 =
                             embed eb (FStar_Pervasives_Native.snd x)  in
                           uu____59615 rng shadow_b norm1  in
                         FStar_Syntax_Syntax.as_arg uu____59614  in
                       [uu____59605]  in
                     uu____59514 :: uu____59594  in
                   uu____59493 :: uu____59503  in
                 uu____59472 :: uu____59482  in
               FStar_Syntax_Syntax.mk_Tm_app uu____59469 uu____59471  in
             uu____59464 FStar_Pervasives_Native.None rng)
         in
      let un t0 w norm1 =
        let t = FStar_Syntax_Util.unmeta_safe t0  in
        lazy_unembed printer emb_t_pair_a_b t t_pair_a_b
          (fun t1  ->
             let uu____59780 = FStar_Syntax_Util.head_and_args' t1  in
             match uu____59780 with
             | (hd1,args) ->
                 let uu____59823 =
                   let uu____59836 =
                     let uu____59837 = FStar_Syntax_Util.un_uinst hd1  in
                     uu____59837.FStar_Syntax_Syntax.n  in
                   (uu____59836, args)  in
                 (match uu____59823 with
                  | (FStar_Syntax_Syntax.Tm_fvar
                     fv,uu____59855::uu____59856::(a,uu____59858)::(b,uu____59860)::[])
                      when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.lid_Mktuple2
                      ->
                      let uu____59919 =
                        let uu____59922 = unembed ea a  in
                        uu____59922 w norm1  in
                      FStar_Util.bind_opt uu____59919
                        (fun a1  ->
                           let uu____59942 =
                             let uu____59945 = unembed eb b  in
                             uu____59945 w norm1  in
                           FStar_Util.bind_opt uu____59942
                             (fun b1  ->
                                FStar_Pervasives_Native.Some (a1, b1)))
                  | uu____59968 ->
                      (if w
                       then
                         (let uu____59983 =
                            let uu____59989 =
                              let uu____59991 =
                                FStar_Syntax_Print.term_to_string t0  in
                              FStar_Util.format1 "Not an embedded pair: %s"
                                uu____59991
                               in
                            (FStar_Errors.Warning_NotEmbedded, uu____59989)
                             in
                          FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                            uu____59983)
                       else ();
                       FStar_Pervasives_Native.None)))
         in
      let uu____60001 =
        let uu____60002 = type_of ea  in
        let uu____60003 = type_of eb  in
        FStar_Syntax_Syntax.t_tuple2_of uu____60002 uu____60003  in
      mk_emb_full em un uu____60001 printer emb_t_pair_a_b
  
let e_either :
  'a 'b . 'a embedding -> 'b embedding -> ('a,'b) FStar_Util.either embedding
  =
  fun ea  ->
    fun eb  ->
      let t_sum_a_b =
        let t_either =
          FStar_Syntax_Util.fvar_const FStar_Parser_Const.either_lid  in
        let uu____60047 =
          let uu____60052 =
            let uu____60053 = FStar_Syntax_Syntax.as_arg ea.typ  in
            let uu____60062 =
              let uu____60073 = FStar_Syntax_Syntax.as_arg eb.typ  in
              [uu____60073]  in
            uu____60053 :: uu____60062  in
          FStar_Syntax_Syntax.mk_Tm_app t_either uu____60052  in
        uu____60047 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
      let emb_t_sum_a_b =
        let uu____60109 =
          let uu____60117 =
            FStar_All.pipe_right FStar_Parser_Const.either_lid
              FStar_Ident.string_of_lid
             in
          (uu____60117, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____60109  in
      let printer s =
        match s with
        | FStar_Util.Inl a ->
            let uu____60140 = ea.print a  in
            FStar_Util.format1 "Inl %s" uu____60140
        | FStar_Util.Inr b ->
            let uu____60144 = eb.print b  in
            FStar_Util.format1 "Inr %s" uu____60144
         in
      let em s rng topt norm1 =
        lazy_embed printer emb_t_sum_a_b rng t_sum_a_b s
          (match s with
           | FStar_Util.Inl a ->
               (fun uu____60232  ->
                  let shadow_a =
                    map_shadow topt
                      (fun t  ->
                         let v1 = FStar_Ident.mk_ident ("v", rng)  in
                         let some_v =
                           FStar_Syntax_Util.mk_field_projector_name_from_ident
                             FStar_Parser_Const.inl_lid v1
                            in
                         let some_v_tm =
                           let uu____60304 =
                             FStar_Syntax_Syntax.lid_as_fv some_v
                               FStar_Syntax_Syntax.delta_equational
                               FStar_Pervasives_Native.None
                              in
                           FStar_Syntax_Syntax.fv_to_tm uu____60304  in
                         let uu____60305 =
                           let uu____60310 =
                             FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm
                               [FStar_Syntax_Syntax.U_zero]
                              in
                           let uu____60311 =
                             let uu____60312 =
                               let uu____60321 = type_of ea  in
                               FStar_Syntax_Syntax.iarg uu____60321  in
                             let uu____60322 =
                               let uu____60333 =
                                 let uu____60342 = type_of eb  in
                                 FStar_Syntax_Syntax.iarg uu____60342  in
                               let uu____60343 =
                                 let uu____60354 =
                                   FStar_Syntax_Syntax.as_arg t  in
                                 [uu____60354]  in
                               uu____60333 :: uu____60343  in
                             uu____60312 :: uu____60322  in
                           FStar_Syntax_Syntax.mk_Tm_app uu____60310
                             uu____60311
                            in
                         uu____60305 FStar_Pervasives_Native.None rng)
                     in
                  let uu____60397 =
                    let uu____60402 =
                      let uu____60403 =
                        FStar_Syntax_Syntax.tdataconstr
                          FStar_Parser_Const.inl_lid
                         in
                      FStar_Syntax_Syntax.mk_Tm_uinst uu____60403
                        [FStar_Syntax_Syntax.U_zero;
                        FStar_Syntax_Syntax.U_zero]
                       in
                    let uu____60404 =
                      let uu____60405 =
                        let uu____60414 = type_of ea  in
                        FStar_Syntax_Syntax.iarg uu____60414  in
                      let uu____60415 =
                        let uu____60426 =
                          let uu____60435 = type_of eb  in
                          FStar_Syntax_Syntax.iarg uu____60435  in
                        let uu____60436 =
                          let uu____60447 =
                            let uu____60456 =
                              let uu____60457 = embed ea a  in
                              uu____60457 rng shadow_a norm1  in
                            FStar_Syntax_Syntax.as_arg uu____60456  in
                          [uu____60447]  in
                        uu____60426 :: uu____60436  in
                      uu____60405 :: uu____60415  in
                    FStar_Syntax_Syntax.mk_Tm_app uu____60402 uu____60404  in
                  uu____60397 FStar_Pervasives_Native.None rng)
           | FStar_Util.Inr b ->
               (fun uu____60562  ->
                  let shadow_b =
                    map_shadow topt
                      (fun t  ->
                         let v1 = FStar_Ident.mk_ident ("v", rng)  in
                         let some_v =
                           FStar_Syntax_Util.mk_field_projector_name_from_ident
                             FStar_Parser_Const.inr_lid v1
                            in
                         let some_v_tm =
                           let uu____60634 =
                             FStar_Syntax_Syntax.lid_as_fv some_v
                               FStar_Syntax_Syntax.delta_equational
                               FStar_Pervasives_Native.None
                              in
                           FStar_Syntax_Syntax.fv_to_tm uu____60634  in
                         let uu____60635 =
                           let uu____60640 =
                             FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm
                               [FStar_Syntax_Syntax.U_zero]
                              in
                           let uu____60641 =
                             let uu____60642 =
                               let uu____60651 = type_of ea  in
                               FStar_Syntax_Syntax.iarg uu____60651  in
                             let uu____60652 =
                               let uu____60663 =
                                 let uu____60672 = type_of eb  in
                                 FStar_Syntax_Syntax.iarg uu____60672  in
                               let uu____60673 =
                                 let uu____60684 =
                                   FStar_Syntax_Syntax.as_arg t  in
                                 [uu____60684]  in
                               uu____60663 :: uu____60673  in
                             uu____60642 :: uu____60652  in
                           FStar_Syntax_Syntax.mk_Tm_app uu____60640
                             uu____60641
                            in
                         uu____60635 FStar_Pervasives_Native.None rng)
                     in
                  let uu____60727 =
                    let uu____60732 =
                      let uu____60733 =
                        FStar_Syntax_Syntax.tdataconstr
                          FStar_Parser_Const.inr_lid
                         in
                      FStar_Syntax_Syntax.mk_Tm_uinst uu____60733
                        [FStar_Syntax_Syntax.U_zero;
                        FStar_Syntax_Syntax.U_zero]
                       in
                    let uu____60734 =
                      let uu____60735 =
                        let uu____60744 = type_of ea  in
                        FStar_Syntax_Syntax.iarg uu____60744  in
                      let uu____60745 =
                        let uu____60756 =
                          let uu____60765 = type_of eb  in
                          FStar_Syntax_Syntax.iarg uu____60765  in
                        let uu____60766 =
                          let uu____60777 =
                            let uu____60786 =
                              let uu____60787 = embed eb b  in
                              uu____60787 rng shadow_b norm1  in
                            FStar_Syntax_Syntax.as_arg uu____60786  in
                          [uu____60777]  in
                        uu____60756 :: uu____60766  in
                      uu____60735 :: uu____60745  in
                    FStar_Syntax_Syntax.mk_Tm_app uu____60732 uu____60734  in
                  uu____60727 FStar_Pervasives_Native.None rng))
         in
      let un t0 w norm1 =
        let t = FStar_Syntax_Util.unmeta_safe t0  in
        lazy_unembed printer emb_t_sum_a_b t t_sum_a_b
          (fun t1  ->
             let uu____60942 = FStar_Syntax_Util.head_and_args' t1  in
             match uu____60942 with
             | (hd1,args) ->
                 let uu____60985 =
                   let uu____61000 =
                     let uu____61001 = FStar_Syntax_Util.un_uinst hd1  in
                     uu____61001.FStar_Syntax_Syntax.n  in
                   (uu____61000, args)  in
                 (match uu____60985 with
                  | (FStar_Syntax_Syntax.Tm_fvar
                     fv,uu____61021::uu____61022::(a,uu____61024)::[]) when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.inl_lid
                      ->
                      let uu____61091 =
                        let uu____61094 = unembed ea a  in
                        uu____61094 w norm1  in
                      FStar_Util.bind_opt uu____61091
                        (fun a1  ->
                           FStar_Pervasives_Native.Some (FStar_Util.Inl a1))
                  | (FStar_Syntax_Syntax.Tm_fvar
                     fv,uu____61118::uu____61119::(b,uu____61121)::[]) when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.inr_lid
                      ->
                      let uu____61188 =
                        let uu____61191 = unembed eb b  in
                        uu____61191 w norm1  in
                      FStar_Util.bind_opt uu____61188
                        (fun b1  ->
                           FStar_Pervasives_Native.Some (FStar_Util.Inr b1))
                  | uu____61214 ->
                      (if w
                       then
                         (let uu____61231 =
                            let uu____61237 =
                              let uu____61239 =
                                FStar_Syntax_Print.term_to_string t0  in
                              FStar_Util.format1 "Not an embedded sum: %s"
                                uu____61239
                               in
                            (FStar_Errors.Warning_NotEmbedded, uu____61237)
                             in
                          FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                            uu____61231)
                       else ();
                       FStar_Pervasives_Native.None)))
         in
      let uu____61249 =
        let uu____61250 = type_of ea  in
        let uu____61251 = type_of eb  in
        FStar_Syntax_Syntax.t_either_of uu____61250 uu____61251  in
      mk_emb_full em un uu____61249 printer emb_t_sum_a_b
  
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea  ->
    let t_list_a =
      let t_list = FStar_Syntax_Util.fvar_const FStar_Parser_Const.list_lid
         in
      let uu____61279 =
        let uu____61284 =
          let uu____61285 = FStar_Syntax_Syntax.as_arg ea.typ  in
          [uu____61285]  in
        FStar_Syntax_Syntax.mk_Tm_app t_list uu____61284  in
      uu____61279 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
    let emb_t_list_a =
      let uu____61313 =
        let uu____61321 =
          FStar_All.pipe_right FStar_Parser_Const.list_lid
            FStar_Ident.string_of_lid
           in
        (uu____61321, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____61313  in
    let printer l =
      let uu____61338 =
        let uu____61340 =
          let uu____61342 = FStar_List.map ea.print l  in
          FStar_All.pipe_right uu____61342 (FStar_String.concat "; ")  in
        Prims.op_Hat uu____61340 "]"  in
      Prims.op_Hat "[" uu____61338  in
    let rec em l rng shadow_l norm1 =
      lazy_embed printer emb_t_list_a rng t_list_a l
        (fun uu____61428  ->
           let t =
             let uu____61430 = type_of ea  in
             FStar_Syntax_Syntax.iarg uu____61430  in
           match l with
           | [] ->
               let uu____61431 =
                 let uu____61436 =
                   let uu____61437 =
                     FStar_Syntax_Syntax.tdataconstr
                       FStar_Parser_Const.nil_lid
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____61437
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 FStar_Syntax_Syntax.mk_Tm_app uu____61436 [t]  in
               uu____61431 FStar_Pervasives_Native.None rng
           | hd1::tl1 ->
               let cons1 =
                 let uu____61461 =
                   FStar_Syntax_Syntax.tdataconstr
                     FStar_Parser_Const.cons_lid
                    in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu____61461
                   [FStar_Syntax_Syntax.U_zero]
                  in
               let proj f cons_tm =
                 let fid = FStar_Ident.mk_ident (f, rng)  in
                 let proj =
                   FStar_Syntax_Util.mk_field_projector_name_from_ident
                     FStar_Parser_Const.cons_lid fid
                    in
                 let proj_tm =
                   let uu____61481 =
                     FStar_Syntax_Syntax.lid_as_fv proj
                       FStar_Syntax_Syntax.delta_equational
                       FStar_Pervasives_Native.None
                      in
                   FStar_Syntax_Syntax.fv_to_tm uu____61481  in
                 let uu____61482 =
                   let uu____61487 =
                     FStar_Syntax_Syntax.mk_Tm_uinst proj_tm
                       [FStar_Syntax_Syntax.U_zero]
                      in
                   let uu____61488 =
                     let uu____61489 =
                       let uu____61498 = type_of ea  in
                       FStar_Syntax_Syntax.iarg uu____61498  in
                     let uu____61499 =
                       let uu____61510 = FStar_Syntax_Syntax.as_arg cons_tm
                          in
                       [uu____61510]  in
                     uu____61489 :: uu____61499  in
                   FStar_Syntax_Syntax.mk_Tm_app uu____61487 uu____61488  in
                 uu____61482 FStar_Pervasives_Native.None rng  in
               let shadow_hd = map_shadow shadow_l (proj "hd")  in
               let shadow_tl = map_shadow shadow_l (proj "tl")  in
               let uu____61663 =
                 let uu____61668 =
                   let uu____61669 =
                     let uu____61680 =
                       let uu____61689 =
                         let uu____61690 = embed ea hd1  in
                         uu____61690 rng shadow_hd norm1  in
                       FStar_Syntax_Syntax.as_arg uu____61689  in
                     let uu____61760 =
                       let uu____61771 =
                         let uu____61780 = em tl1 rng shadow_tl norm1  in
                         FStar_Syntax_Syntax.as_arg uu____61780  in
                       [uu____61771]  in
                     uu____61680 :: uu____61760  in
                   t :: uu____61669  in
                 FStar_Syntax_Syntax.mk_Tm_app cons1 uu____61668  in
               uu____61663 FStar_Pervasives_Native.None rng)
       in
    let rec un t0 w norm1 =
      let t = FStar_Syntax_Util.unmeta_safe t0  in
      lazy_unembed printer emb_t_list_a t t_list_a
        (fun t1  ->
           let uu____61896 = FStar_Syntax_Util.head_and_args' t1  in
           match uu____61896 with
           | (hd1,args) ->
               let uu____61937 =
                 let uu____61950 =
                   let uu____61951 = FStar_Syntax_Util.un_uinst hd1  in
                   uu____61951.FStar_Syntax_Syntax.n  in
                 (uu____61950, args)  in
               (match uu____61937 with
                | (FStar_Syntax_Syntax.Tm_fvar fv,uu____61967) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.nil_lid
                    -> FStar_Pervasives_Native.Some []
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(uu____61987,FStar_Pervasives_Native.Some
                       (FStar_Syntax_Syntax.Implicit uu____61988))::(hd2,FStar_Pervasives_Native.None
                                                                    )::
                   (tl1,FStar_Pervasives_Native.None )::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.cons_lid
                    ->
                    let uu____62030 =
                      let uu____62033 = unembed ea hd2  in
                      uu____62033 w norm1  in
                    FStar_Util.bind_opt uu____62030
                      (fun hd3  ->
                         let uu____62051 = un tl1 w norm1  in
                         FStar_Util.bind_opt uu____62051
                           (fun tl2  ->
                              FStar_Pervasives_Native.Some (hd3 :: tl2)))
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(hd2,FStar_Pervasives_Native.None )::(tl1,FStar_Pervasives_Native.None
                                                            )::[])
                    when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.cons_lid
                    ->
                    let uu____62101 =
                      let uu____62104 = unembed ea hd2  in
                      uu____62104 w norm1  in
                    FStar_Util.bind_opt uu____62101
                      (fun hd3  ->
                         let uu____62122 = un tl1 w norm1  in
                         FStar_Util.bind_opt uu____62122
                           (fun tl2  ->
                              FStar_Pervasives_Native.Some (hd3 :: tl2)))
                | uu____62139 ->
                    (if w
                     then
                       (let uu____62154 =
                          let uu____62160 =
                            let uu____62162 =
                              FStar_Syntax_Print.term_to_string t0  in
                            FStar_Util.format1 "Not an embedded list: %s"
                              uu____62162
                             in
                          (FStar_Errors.Warning_NotEmbedded, uu____62160)  in
                        FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                          uu____62154)
                     else ();
                     FStar_Pervasives_Native.None)))
       in
    let uu____62170 =
      let uu____62171 = type_of ea  in
      FStar_Syntax_Syntax.t_list_of uu____62171  in
    mk_emb_full em un uu____62170 printer emb_t_list_a
  
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
    match projectee with | Simpl  -> true | uu____62214 -> false
  
let (uu___is_Weak : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Weak  -> true | uu____62225 -> false
  
let (uu___is_HNF : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | HNF  -> true | uu____62236 -> false
  
let (uu___is_Primops : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____62247 -> false
  
let (uu___is_Delta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Delta  -> true | uu____62258 -> false
  
let (uu___is_Zeta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Zeta  -> true | uu____62269 -> false
  
let (uu___is_Iota : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Iota  -> true | uu____62280 -> false
  
let (uu___is_Reify : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____62291 -> false
  
let (uu___is_UnfoldOnly : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____62306 -> false
  
let (__proj__UnfoldOnly__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldFully : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldFully _0 -> true | uu____62338 -> false
  
let (__proj__UnfoldFully__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldFully _0 -> _0 
let (uu___is_UnfoldAttr : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____62370 -> false
  
let (__proj__UnfoldAttr__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_NBE : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | NBE  -> true | uu____62398 -> false
  
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
    let uu____62416 =
      FStar_Ident.lid_of_str "FStar.Syntax.Embeddings.norm_step"  in
    FStar_Syntax_Util.fvar_const uu____62416  in
  let emb_t_norm_step =
    let uu____62419 =
      let uu____62427 =
        FStar_All.pipe_right FStar_Parser_Const.norm_step_lid
          FStar_Ident.string_of_lid
         in
      (uu____62427, [])  in
    FStar_Syntax_Syntax.ET_app uu____62419  in
  let printer uu____62439 = "norm_step"  in
  let em n1 rng _topt norm1 =
    lazy_embed printer emb_t_norm_step rng t_norm_step1 n1
      (fun uu____62505  ->
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
             let uu____62510 =
               let uu____62515 =
                 let uu____62516 =
                   let uu____62525 =
                     let uu____62526 =
                       let uu____62533 = e_list e_string  in
                       embed uu____62533 l  in
                     uu____62526 rng FStar_Pervasives_Native.None norm1  in
                   FStar_Syntax_Syntax.as_arg uu____62525  in
                 [uu____62516]  in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldOnly uu____62515  in
             uu____62510 FStar_Pervasives_Native.None rng
         | UnfoldFully l ->
             let uu____62592 =
               let uu____62597 =
                 let uu____62598 =
                   let uu____62607 =
                     let uu____62608 =
                       let uu____62615 = e_list e_string  in
                       embed uu____62615 l  in
                     uu____62608 rng FStar_Pervasives_Native.None norm1  in
                   FStar_Syntax_Syntax.as_arg uu____62607  in
                 [uu____62598]  in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldFully uu____62597
                in
             uu____62592 FStar_Pervasives_Native.None rng
         | UnfoldAttr l ->
             let uu____62674 =
               let uu____62679 =
                 let uu____62680 =
                   let uu____62689 =
                     let uu____62690 =
                       let uu____62697 = e_list e_string  in
                       embed uu____62697 l  in
                     uu____62690 rng FStar_Pervasives_Native.None norm1  in
                   FStar_Syntax_Syntax.as_arg uu____62689  in
                 [uu____62680]  in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldAttr uu____62679  in
             uu____62674 FStar_Pervasives_Native.None rng)
     in
  let un t0 w norm1 =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    lazy_unembed printer emb_t_norm_step t t_norm_step1
      (fun t1  ->
         let uu____62786 = FStar_Syntax_Util.head_and_args t1  in
         match uu____62786 with
         | (hd1,args) ->
             let uu____62831 =
               let uu____62846 =
                 let uu____62847 = FStar_Syntax_Util.un_uinst hd1  in
                 uu____62847.FStar_Syntax_Syntax.n  in
               (uu____62846, args)  in
             (match uu____62831 with
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
              | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____63035)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldonly
                  ->
                  let uu____63070 =
                    let uu____63076 =
                      let uu____63086 = e_list e_string  in
                      unembed uu____63086 l  in
                    uu____63076 w norm1  in
                  FStar_Util.bind_opt uu____63070
                    (fun ss  ->
                       FStar_All.pipe_left
                         (fun _63112  -> FStar_Pervasives_Native.Some _63112)
                         (UnfoldOnly ss))
              | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____63115)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldfully
                  ->
                  let uu____63150 =
                    let uu____63156 =
                      let uu____63166 = e_list e_string  in
                      unembed uu____63166 l  in
                    uu____63156 w norm1  in
                  FStar_Util.bind_opt uu____63150
                    (fun ss  ->
                       FStar_All.pipe_left
                         (fun _63192  -> FStar_Pervasives_Native.Some _63192)
                         (UnfoldFully ss))
              | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____63195)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldattr
                  ->
                  let uu____63230 =
                    let uu____63236 =
                      let uu____63246 = e_list e_string  in
                      unembed uu____63246 l  in
                    uu____63236 w norm1  in
                  FStar_Util.bind_opt uu____63230
                    (fun ss  ->
                       FStar_All.pipe_left
                         (fun _63272  -> FStar_Pervasives_Native.Some _63272)
                         (UnfoldAttr ss))
              | uu____63273 ->
                  (if w
                   then
                     (let uu____63290 =
                        let uu____63296 =
                          let uu____63298 =
                            FStar_Syntax_Print.term_to_string t0  in
                          FStar_Util.format1 "Not an embedded norm_step: %s"
                            uu____63298
                           in
                        (FStar_Errors.Warning_NotEmbedded, uu____63296)  in
                      FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                        uu____63290)
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
    | uu____63400 ->
        (if w
         then
           (let uu____63403 =
              let uu____63409 =
                let uu____63411 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded range: %s" uu____63411
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____63409)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____63403)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____63417 =
    let uu____63418 =
      let uu____63426 =
        FStar_All.pipe_right FStar_Parser_Const.range_lid
          FStar_Ident.string_of_lid
         in
      (uu____63426, [])  in
    FStar_Syntax_Syntax.ET_app uu____63418  in
  mk_emb_full em un FStar_Syntax_Syntax.t_range FStar_Range.string_of_range
    uu____63417
  
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
        let uu____63497 =
          let uu____63504 =
            let uu____63505 =
              let uu____63520 =
                let uu____63529 =
                  let uu____63536 = FStar_Syntax_Syntax.null_bv ea.typ  in
                  (uu____63536, FStar_Pervasives_Native.None)  in
                [uu____63529]  in
              let uu____63551 = FStar_Syntax_Syntax.mk_Total eb.typ  in
              (uu____63520, uu____63551)  in
            FStar_Syntax_Syntax.Tm_arrow uu____63505  in
          FStar_Syntax_Syntax.mk uu____63504  in
        uu____63497 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
      let emb_t_arr_a_b =
        FStar_Syntax_Syntax.ET_fun ((ea.emb_typ), (eb.emb_typ))  in
      let printer f = "<fun>"  in
      let em f rng shadow_f norm1 =
        lazy_embed (fun uu____63664  -> "<fun>") emb_t_arr_a_b rng t_arrow f
          (fun uu____63670  ->
             let uu____63671 = force_shadow shadow_f  in
             match uu____63671 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Exn.raise Embedding_failure
             | FStar_Pervasives_Native.Some repr_f ->
                 ((let uu____63733 =
                     FStar_ST.op_Bang FStar_Options.debug_embedding  in
                   if uu____63733
                   then
                     let uu____63757 =
                       FStar_Syntax_Print.term_to_string repr_f  in
                     let uu____63759 = FStar_Util.stack_dump ()  in
                     FStar_Util.print2
                       "e_arrow forced back to term using shadow %s; repr=%s\n"
                       uu____63757 uu____63759
                   else ());
                  (let res = norm1 (FStar_Util.Inr repr_f)  in
                   (let uu____63766 =
                      FStar_ST.op_Bang FStar_Options.debug_embedding  in
                    if uu____63766
                    then
                      let uu____63790 =
                        FStar_Syntax_Print.term_to_string repr_f  in
                      let uu____63792 = FStar_Syntax_Print.term_to_string res
                         in
                      let uu____63794 = FStar_Util.stack_dump ()  in
                      FStar_Util.print3
                        "e_arrow forced back to term using shadow %s; repr=%s\n\t%s\n"
                        uu____63790 uu____63792 uu____63794
                    else ());
                   res)))
         in
      let un f w norm1 =
        lazy_unembed printer emb_t_arr_a_b f t_arrow
          (fun f1  ->
             let f_wrapped a =
               (let uu____63853 =
                  FStar_ST.op_Bang FStar_Options.debug_embedding  in
                if uu____63853
                then
                  let uu____63877 = FStar_Syntax_Print.term_to_string f1  in
                  let uu____63879 = FStar_Util.stack_dump ()  in
                  FStar_Util.print2
                    "Calling back into normalizer for %s\n%s\n" uu____63877
                    uu____63879
                else ());
               (let a_tm =
                  let uu____63885 = embed ea a  in
                  uu____63885 f1.FStar_Syntax_Syntax.pos
                    FStar_Pervasives_Native.None norm1
                   in
                let b_tm =
                  let uu____63918 =
                    let uu____63923 =
                      let uu____63924 =
                        let uu____63929 =
                          let uu____63930 = FStar_Syntax_Syntax.as_arg a_tm
                             in
                          [uu____63930]  in
                        FStar_Syntax_Syntax.mk_Tm_app f1 uu____63929  in
                      uu____63924 FStar_Pervasives_Native.None
                        f1.FStar_Syntax_Syntax.pos
                       in
                    FStar_Util.Inr uu____63923  in
                  norm1 uu____63918  in
                let uu____63957 =
                  let uu____63960 = unembed eb b_tm  in uu____63960 w norm1
                   in
                match uu____63957 with
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
                let uu____64060 = FStar_List.splitAt n_tvars args  in
                match uu____64060 with
                | (_tvar_args,rest_args) ->
                    let uu____64137 = FStar_List.hd rest_args  in
                    (match uu____64137 with
                     | (x,uu____64157) ->
                         let shadow_app =
                           let uu____64171 =
                             FStar_Common.mk_thunk
                               (fun uu____64180  ->
                                  let uu____64181 =
                                    let uu____64186 =
                                      norm1 (FStar_Util.Inl fv_lid1)  in
                                    FStar_Syntax_Syntax.mk_Tm_app uu____64186
                                      args
                                     in
                                  uu____64181 FStar_Pervasives_Native.None
                                    rng)
                              in
                           FStar_Pervasives_Native.Some uu____64171  in
                         let uu____64232 =
                           let uu____64235 =
                             let uu____64238 = unembed ea x  in
                             uu____64238 true norm1  in
                           FStar_Util.map_opt uu____64235
                             (fun x1  ->
                                let uu____64278 =
                                  let uu____64285 = f x1  in
                                  embed eb uu____64285  in
                                uu____64278 rng shadow_app norm1)
                            in
                         (match uu____64232 with
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
                  let uu____64415 = FStar_List.splitAt n_tvars args  in
                  match uu____64415 with
                  | (_tvar_args,rest_args) ->
                      let uu____64478 = FStar_List.hd rest_args  in
                      (match uu____64478 with
                       | (x,uu____64494) ->
                           let uu____64499 =
                             let uu____64506 = FStar_List.tl rest_args  in
                             FStar_List.hd uu____64506  in
                           (match uu____64499 with
                            | (y,uu____64530) ->
                                let shadow_app =
                                  let uu____64540 =
                                    FStar_Common.mk_thunk
                                      (fun uu____64549  ->
                                         let uu____64550 =
                                           let uu____64555 =
                                             norm1 (FStar_Util.Inl fv_lid1)
                                              in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____64555 args
                                            in
                                         uu____64550
                                           FStar_Pervasives_Native.None rng)
                                     in
                                  FStar_Pervasives_Native.Some uu____64540
                                   in
                                let uu____64601 =
                                  let uu____64604 =
                                    let uu____64607 = unembed ea x  in
                                    uu____64607 true norm1  in
                                  FStar_Util.bind_opt uu____64604
                                    (fun x1  ->
                                       let uu____64624 =
                                         let uu____64627 = unembed eb y  in
                                         uu____64627 true norm1  in
                                       FStar_Util.bind_opt uu____64624
                                         (fun y1  ->
                                            let uu____64644 =
                                              let uu____64645 =
                                                let uu____64652 = f x1 y1  in
                                                embed ec uu____64652  in
                                              uu____64645 rng shadow_app
                                                norm1
                                               in
                                            FStar_Pervasives_Native.Some
                                              uu____64644))
                                   in
                                (match uu____64601 with
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
                    let uu____64801 = FStar_List.splitAt n_tvars args  in
                    match uu____64801 with
                    | (_tvar_args,rest_args) ->
                        let uu____64864 = FStar_List.hd rest_args  in
                        (match uu____64864 with
                         | (x,uu____64880) ->
                             let uu____64885 =
                               let uu____64892 = FStar_List.tl rest_args  in
                               FStar_List.hd uu____64892  in
                             (match uu____64885 with
                              | (y,uu____64916) ->
                                  let uu____64921 =
                                    let uu____64928 =
                                      let uu____64937 =
                                        FStar_List.tl rest_args  in
                                      FStar_List.tl uu____64937  in
                                    FStar_List.hd uu____64928  in
                                  (match uu____64921 with
                                   | (z,uu____64967) ->
                                       let shadow_app =
                                         let uu____64977 =
                                           FStar_Common.mk_thunk
                                             (fun uu____64986  ->
                                                let uu____64987 =
                                                  let uu____64992 =
                                                    norm1
                                                      (FStar_Util.Inl fv_lid1)
                                                     in
                                                  FStar_Syntax_Syntax.mk_Tm_app
                                                    uu____64992 args
                                                   in
                                                uu____64987
                                                  FStar_Pervasives_Native.None
                                                  rng)
                                            in
                                         FStar_Pervasives_Native.Some
                                           uu____64977
                                          in
                                       let uu____65038 =
                                         let uu____65041 =
                                           let uu____65044 = unembed ea x  in
                                           uu____65044 true norm1  in
                                         FStar_Util.bind_opt uu____65041
                                           (fun x1  ->
                                              let uu____65061 =
                                                let uu____65064 =
                                                  unembed eb y  in
                                                uu____65064 true norm1  in
                                              FStar_Util.bind_opt uu____65061
                                                (fun y1  ->
                                                   let uu____65081 =
                                                     let uu____65084 =
                                                       unembed ec z  in
                                                     uu____65084 true norm1
                                                      in
                                                   FStar_Util.bind_opt
                                                     uu____65081
                                                     (fun z1  ->
                                                        let uu____65101 =
                                                          let uu____65102 =
                                                            let uu____65109 =
                                                              f x1 y1 z1  in
                                                            embed ed
                                                              uu____65109
                                                             in
                                                          uu____65102 rng
                                                            shadow_app norm1
                                                           in
                                                        FStar_Pervasives_Native.Some
                                                          uu____65101)))
                                          in
                                       (match uu____65038 with
                                        | FStar_Pervasives_Native.Some x1 ->
                                            FStar_Pervasives_Native.Some x1
                                        | FStar_Pervasives_Native.None  ->
                                            force_shadow shadow_app))))
                     in
                  f_wrapped
  
let debug_wrap : 'a . Prims.string -> (unit -> 'a) -> 'a =
  fun s  ->
    fun f  ->
      (let uu____65164 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
       if uu____65164 then FStar_Util.print1 "++++starting %s\n" s else ());
      (let res = f ()  in
       (let uu____65193 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
        if uu____65193 then FStar_Util.print1 "------ending %s\n" s else ());
       res)
  