open Prims
type norm_cb =
  (FStar_Ident.lid,FStar_Syntax_Syntax.term) FStar_Util.either ->
    FStar_Syntax_Syntax.term
let (id_norm_cb : norm_cb) =
  fun uu___429_51406  ->
    match uu___429_51406 with
    | FStar_Util.Inr x -> x
    | FStar_Util.Inl l ->
        let uu____51413 =
          FStar_Syntax_Syntax.lid_as_fv l
            FStar_Syntax_Syntax.delta_equational FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.fv_to_tm uu____51413
  
exception Embedding_failure 
let (uu___is_Embedding_failure : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Embedding_failure  -> true | uu____51423 -> false
  
exception Unembedding_failure 
let (uu___is_Unembedding_failure : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Unembedding_failure  -> true
    | uu____51434 -> false
  
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
             (fun uu____51466  ->
                let uu____51467 = FStar_Common.force_thunk s1  in
                f uu____51467))
  
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
  'Auu____51829 . FStar_Syntax_Syntax.term -> 'Auu____51829 -> Prims.string =
  fun typ  ->
    fun uu____51840  ->
      let uu____51841 = FStar_Syntax_Print.term_to_string typ  in
      FStar_Util.format1 "unknown %s" uu____51841
  
let (term_as_fv : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.fv) =
  fun t  ->
    let uu____51850 =
      let uu____51851 = FStar_Syntax_Subst.compress t  in
      uu____51851.FStar_Syntax_Syntax.n  in
    match uu____51850 with
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv
    | uu____51855 ->
        let uu____51856 =
          let uu____51858 = FStar_Syntax_Print.term_to_string t  in
          FStar_Util.format1 "Embeddings not defined for type %s" uu____51858
           in
        failwith uu____51856
  
let mk_emb :
  'a .
    'a raw_embedder ->
      'a raw_unembedder -> FStar_Syntax_Syntax.fv -> 'a embedding
  =
  fun em  ->
    fun un  ->
      fun fv  ->
        let typ = FStar_Syntax_Syntax.fv_to_tm fv  in
        let uu____51901 =
          let uu____51902 =
            let uu____51910 =
              let uu____51912 = FStar_Syntax_Syntax.lid_of_fv fv  in
              FStar_All.pipe_right uu____51912 FStar_Ident.string_of_lid  in
            (uu____51910, [])  in
          FStar_Syntax_Syntax.ET_app uu____51902  in
        { em; un; typ; print = (unknown_printer typ); emb_typ = uu____51901 }
  
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
      fun n1  -> let uu____52061 = unembed e t  in uu____52061 true n1
  
let try_unembed :
  'a .
    'a embedding ->
      FStar_Syntax_Syntax.term ->
        norm_cb -> 'a FStar_Pervasives_Native.option
  =
  fun e  ->
    fun t  ->
      fun n1  -> let uu____52102 = unembed e t  in uu____52102 false n1
  
let type_of : 'a . 'a embedding -> FStar_Syntax_Syntax.typ = fun e  -> e.typ 
let set_type : 'a . FStar_Syntax_Syntax.typ -> 'a embedding -> 'a embedding =
  fun ty  ->
    fun e  ->
      let uu___508_52149 = e  in
      {
        em = (uu___508_52149.em);
        un = (uu___508_52149.un);
        typ = ty;
        print = (uu___508_52149.print);
        emb_typ = (uu___508_52149.emb_typ)
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
              (let uu____52212 =
                 FStar_ST.op_Bang FStar_Options.debug_embedding  in
               if uu____52212
               then
                 let uu____52236 = FStar_Syntax_Print.term_to_string ta  in
                 let uu____52238 = FStar_Syntax_Print.emb_typ_to_string et
                    in
                 let uu____52240 = pa x  in
                 FStar_Util.print3
                   "Embedding a %s\n\temb_typ=%s\n\tvalue is %s\n"
                   uu____52236 uu____52238 uu____52240
               else ());
              (let uu____52245 =
                 FStar_ST.op_Bang FStar_Options.eager_embedding  in
               if uu____52245
               then f ()
               else
                 (let thunk1 = FStar_Common.mk_thunk f  in
                  let uu____52280 =
                    let uu____52287 =
                      let uu____52288 =
                        let uu____52289 = FStar_Dyn.mkdyn x  in
                        {
                          FStar_Syntax_Syntax.blob = uu____52289;
                          FStar_Syntax_Syntax.lkind =
                            (FStar_Syntax_Syntax.Lazy_embedding (et, thunk1));
                          FStar_Syntax_Syntax.ltyp = FStar_Syntax_Syntax.tun;
                          FStar_Syntax_Syntax.rng = rng
                        }  in
                      FStar_Syntax_Syntax.Tm_lazy uu____52288  in
                    FStar_Syntax_Syntax.mk uu____52287  in
                  uu____52280 FStar_Pervasives_Native.None rng))
  
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
                  FStar_Syntax_Syntax.ltyp = uu____52356;
                  FStar_Syntax_Syntax.rng = uu____52357;_}
                ->
                let uu____52368 =
                  (et <> et') ||
                    (FStar_ST.op_Bang FStar_Options.eager_embedding)
                   in
                if uu____52368
                then
                  let res =
                    let uu____52397 = FStar_Common.force_thunk t  in
                    f uu____52397  in
                  ((let uu____52401 =
                      FStar_ST.op_Bang FStar_Options.debug_embedding  in
                    if uu____52401
                    then
                      let uu____52425 =
                        FStar_Syntax_Print.emb_typ_to_string et  in
                      let uu____52427 =
                        FStar_Syntax_Print.emb_typ_to_string et'  in
                      let uu____52429 =
                        match res with
                        | FStar_Pervasives_Native.None  -> "None"
                        | FStar_Pervasives_Native.Some x2 ->
                            let uu____52434 = pa x2  in
                            Prims.op_Hat "Some " uu____52434
                         in
                      FStar_Util.print3
                        "Unembed cancellation failed\n\t%s <> %s\nvalue is %s\n"
                        uu____52425 uu____52427 uu____52429
                    else ());
                   res)
                else
                  (let a = FStar_Dyn.undyn b  in
                   (let uu____52444 =
                      FStar_ST.op_Bang FStar_Options.debug_embedding  in
                    if uu____52444
                    then
                      let uu____52468 =
                        FStar_Syntax_Print.emb_typ_to_string et  in
                      let uu____52470 = pa a  in
                      FStar_Util.print2
                        "Unembed cancelled for %s\n\tvalue is %s\n"
                        uu____52468 uu____52470
                    else ());
                   FStar_Pervasives_Native.Some a)
            | uu____52475 ->
                let aopt = f x1  in
                ((let uu____52480 =
                    FStar_ST.op_Bang FStar_Options.debug_embedding  in
                  if uu____52480
                  then
                    let uu____52504 = FStar_Syntax_Print.emb_typ_to_string et
                       in
                    let uu____52506 = FStar_Syntax_Print.term_to_string x1
                       in
                    let uu____52508 =
                      match aopt with
                      | FStar_Pervasives_Native.None  -> "None"
                      | FStar_Pervasives_Native.Some a ->
                          let uu____52513 = pa a  in
                          Prims.op_Hat "Some " uu____52513
                       in
                    FStar_Util.print3
                      "Unembedding:\n\temb_typ=%s\n\tterm is %s\n\tvalue is %s\n"
                      uu____52504 uu____52506 uu____52508
                  else ());
                 aopt)
  
let (mk_any_emb :
  FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term embedding) =
  fun typ  ->
    let em t _r _topt _norm =
      (let uu____52551 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
       if uu____52551
       then
         let uu____52575 = unknown_printer typ t  in
         FStar_Util.print1 "Embedding abstract: %s\n" uu____52575
       else ());
      t  in
    let un t _w _n =
      (let uu____52603 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
       if uu____52603
       then
         let uu____52627 = unknown_printer typ t  in
         FStar_Util.print1 "Unembedding abstract: %s\n" uu____52627
       else ());
      FStar_Pervasives_Native.Some t  in
    mk_emb_full em un typ (unknown_printer typ)
      FStar_Syntax_Syntax.ET_abstract
  
let (e_any : FStar_Syntax_Syntax.term embedding) =
  let em t _r _topt _norm = t  in
  let un t _w _n = FStar_Pervasives_Native.Some t  in
  let uu____52680 =
    let uu____52681 =
      let uu____52689 =
        FStar_All.pipe_right FStar_Parser_Const.term_lid
          FStar_Ident.string_of_lid
         in
      (uu____52689, [])  in
    FStar_Syntax_Syntax.ET_app uu____52681  in
  mk_emb_full em un FStar_Syntax_Syntax.t_term
    FStar_Syntax_Print.term_to_string uu____52680
  
let (e_unit : unit embedding) =
  let em u rng _topt _norm =
    let uu___582_52721 = FStar_Syntax_Util.exp_unit  in
    {
      FStar_Syntax_Syntax.n = (uu___582_52721.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___582_52721.FStar_Syntax_Syntax.vars)
    }  in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unascribe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit ) ->
        FStar_Pervasives_Native.Some ()
    | uu____52749 ->
        (if w
         then
           (let uu____52752 =
              let uu____52758 =
                let uu____52760 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded unit: %s" uu____52760  in
              (FStar_Errors.Warning_NotEmbedded, uu____52758)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____52752)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____52766 =
    let uu____52767 =
      let uu____52775 =
        FStar_All.pipe_right FStar_Parser_Const.unit_lid
          FStar_Ident.string_of_lid
         in
      (uu____52775, [])  in
    FStar_Syntax_Syntax.ET_app uu____52767  in
  mk_emb_full em un FStar_Syntax_Syntax.t_unit (fun uu____52782  -> "()")
    uu____52766
  
let (e_bool : Prims.bool embedding) =
  let em b rng _topt _norm =
    let t =
      if b
      then FStar_Syntax_Util.exp_true_bool
      else FStar_Syntax_Util.exp_false_bool  in
    let uu___602_52821 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___602_52821.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___602_52821.FStar_Syntax_Syntax.vars)
    }  in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) ->
        FStar_Pervasives_Native.Some b
    | uu____52857 ->
        (if w
         then
           (let uu____52860 =
              let uu____52866 =
                let uu____52868 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded bool: %s" uu____52868  in
              (FStar_Errors.Warning_NotEmbedded, uu____52866)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____52860)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____52875 =
    let uu____52876 =
      let uu____52884 =
        FStar_All.pipe_right FStar_Parser_Const.bool_lid
          FStar_Ident.string_of_lid
         in
      (uu____52884, [])  in
    FStar_Syntax_Syntax.ET_app uu____52876  in
  mk_emb_full em un FStar_Syntax_Syntax.t_bool FStar_Util.string_of_bool
    uu____52875
  
let (e_char : FStar_Char.char embedding) =
  let em c rng _topt _norm =
    let t = FStar_Syntax_Util.exp_char c  in
    let uu___621_52921 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___621_52921.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___621_52921.FStar_Syntax_Syntax.vars)
    }  in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c) ->
        FStar_Pervasives_Native.Some c
    | uu____52955 ->
        (if w
         then
           (let uu____52958 =
              let uu____52964 =
                let uu____52966 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded char: %s" uu____52966  in
              (FStar_Errors.Warning_NotEmbedded, uu____52964)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____52958)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____52973 =
    let uu____52974 =
      let uu____52982 =
        FStar_All.pipe_right FStar_Parser_Const.char_lid
          FStar_Ident.string_of_lid
         in
      (uu____52982, [])  in
    FStar_Syntax_Syntax.ET_app uu____52974  in
  mk_emb_full em un FStar_Syntax_Syntax.t_char FStar_Util.string_of_char
    uu____52973
  
let (e_int : FStar_BigInt.t embedding) =
  let t_int1 = FStar_Syntax_Util.fvar_const FStar_Parser_Const.int_lid  in
  let emb_t_int =
    let uu____52994 =
      let uu____53002 =
        FStar_All.pipe_right FStar_Parser_Const.int_lid
          FStar_Ident.string_of_lid
         in
      (uu____53002, [])  in
    FStar_Syntax_Syntax.ET_app uu____52994  in
  let em i rng _topt _norm =
    lazy_embed FStar_BigInt.string_of_big_int emb_t_int rng t_int1 i
      (fun uu____53033  ->
         let uu____53034 = FStar_BigInt.string_of_big_int i  in
         FStar_Syntax_Util.exp_int uu____53034)
     in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    lazy_unembed FStar_BigInt.string_of_big_int emb_t_int t t_int1
      (fun t1  ->
         match t1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
             (s,uu____53069)) ->
             let uu____53084 = FStar_BigInt.big_int_of_string s  in
             FStar_Pervasives_Native.Some uu____53084
         | uu____53085 ->
             (if w
              then
                (let uu____53088 =
                   let uu____53094 =
                     let uu____53096 = FStar_Syntax_Print.term_to_string t0
                        in
                     FStar_Util.format1 "Not an embedded int: %s" uu____53096
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____53094)  in
                 FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                   uu____53088)
              else ();
              FStar_Pervasives_Native.None))
     in
  mk_emb_full em un FStar_Syntax_Syntax.t_int FStar_BigInt.string_of_big_int
    emb_t_int
  
let (e_string : Prims.string embedding) =
  let emb_t_string =
    let uu____53107 =
      let uu____53115 =
        FStar_All.pipe_right FStar_Parser_Const.string_lid
          FStar_Ident.string_of_lid
         in
      (uu____53115, [])  in
    FStar_Syntax_Syntax.ET_app uu____53107  in
  let em s rng _topt _norm =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, rng)))
      FStar_Pervasives_Native.None rng
     in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
        (s,uu____53178)) -> FStar_Pervasives_Native.Some s
    | uu____53182 ->
        (if w
         then
           (let uu____53185 =
              let uu____53191 =
                let uu____53193 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded string: %s" uu____53193
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____53191)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____53185)
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
      let uu____53229 =
        let uu____53234 =
          let uu____53235 = FStar_Syntax_Syntax.as_arg ea.typ  in
          [uu____53235]  in
        FStar_Syntax_Syntax.mk_Tm_app t_opt uu____53234  in
      uu____53229 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
    let emb_t_option_a =
      let uu____53261 =
        let uu____53269 =
          FStar_All.pipe_right FStar_Parser_Const.option_lid
            FStar_Ident.string_of_lid
           in
        (uu____53269, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____53261  in
    let printer uu___430_53283 =
      match uu___430_53283 with
      | FStar_Pervasives_Native.None  -> "None"
      | FStar_Pervasives_Native.Some x ->
          let uu____53289 =
            let uu____53291 = ea.print x  in Prims.op_Hat uu____53291 ")"  in
          Prims.op_Hat "(Some " uu____53289
       in
    let em o rng topt norm1 =
      lazy_embed printer emb_t_option_a rng t_option_a o
        (fun uu____53326  ->
           match o with
           | FStar_Pervasives_Native.None  ->
               let uu____53327 =
                 let uu____53332 =
                   let uu____53333 =
                     FStar_Syntax_Syntax.tdataconstr
                       FStar_Parser_Const.none_lid
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____53333
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 let uu____53334 =
                   let uu____53335 =
                     let uu____53344 = type_of ea  in
                     FStar_Syntax_Syntax.iarg uu____53344  in
                   [uu____53335]  in
                 FStar_Syntax_Syntax.mk_Tm_app uu____53332 uu____53334  in
               uu____53327 FStar_Pervasives_Native.None rng
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
                        let uu____53374 =
                          FStar_Syntax_Syntax.lid_as_fv some_v
                            FStar_Syntax_Syntax.delta_equational
                            FStar_Pervasives_Native.None
                           in
                        FStar_Syntax_Syntax.fv_to_tm uu____53374  in
                      let uu____53375 =
                        let uu____53380 =
                          FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm
                            [FStar_Syntax_Syntax.U_zero]
                           in
                        let uu____53381 =
                          let uu____53382 =
                            let uu____53391 = type_of ea  in
                            FStar_Syntax_Syntax.iarg uu____53391  in
                          let uu____53392 =
                            let uu____53403 = FStar_Syntax_Syntax.as_arg t
                               in
                            [uu____53403]  in
                          uu____53382 :: uu____53392  in
                        FStar_Syntax_Syntax.mk_Tm_app uu____53380 uu____53381
                         in
                      uu____53375 FStar_Pervasives_Native.None rng)
                  in
               let uu____53436 =
                 let uu____53441 =
                   let uu____53442 =
                     FStar_Syntax_Syntax.tdataconstr
                       FStar_Parser_Const.some_lid
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____53442
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 let uu____53443 =
                   let uu____53444 =
                     let uu____53453 = type_of ea  in
                     FStar_Syntax_Syntax.iarg uu____53453  in
                   let uu____53454 =
                     let uu____53465 =
                       let uu____53474 =
                         let uu____53475 = embed ea a  in
                         uu____53475 rng shadow_a norm1  in
                       FStar_Syntax_Syntax.as_arg uu____53474  in
                     [uu____53465]  in
                   uu____53444 :: uu____53454  in
                 FStar_Syntax_Syntax.mk_Tm_app uu____53441 uu____53443  in
               uu____53436 FStar_Pervasives_Native.None rng)
       in
    let un t0 w norm1 =
      let t = FStar_Syntax_Util.unmeta_safe t0  in
      lazy_unembed printer emb_t_option_a t t_option_a
        (fun t1  ->
           let uu____53545 = FStar_Syntax_Util.head_and_args' t1  in
           match uu____53545 with
           | (hd1,args) ->
               let uu____53586 =
                 let uu____53601 =
                   let uu____53602 = FStar_Syntax_Util.un_uinst hd1  in
                   uu____53602.FStar_Syntax_Syntax.n  in
                 (uu____53601, args)  in
               (match uu____53586 with
                | (FStar_Syntax_Syntax.Tm_fvar fv,uu____53620) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.none_lid
                    ->
                    FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,uu____53644::(a,uu____53646)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.some_lid
                    ->
                    let uu____53697 =
                      let uu____53700 = unembed ea a  in uu____53700 w norm1
                       in
                    FStar_Util.bind_opt uu____53697
                      (fun a1  ->
                         FStar_Pervasives_Native.Some
                           (FStar_Pervasives_Native.Some a1))
                | uu____53713 ->
                    (if w
                     then
                       (let uu____53730 =
                          let uu____53736 =
                            let uu____53738 =
                              FStar_Syntax_Print.term_to_string t0  in
                            FStar_Util.format1 "Not an embedded option: %s"
                              uu____53738
                             in
                          (FStar_Errors.Warning_NotEmbedded, uu____53736)  in
                        FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                          uu____53730)
                     else ();
                     FStar_Pervasives_Native.None)))
       in
    let uu____53746 =
      let uu____53747 = type_of ea  in
      FStar_Syntax_Syntax.t_option_of uu____53747  in
    mk_emb_full em un uu____53746 printer emb_t_option_a
  
let e_tuple2 : 'a 'b . 'a embedding -> 'b embedding -> ('a * 'b) embedding =
  fun ea  ->
    fun eb  ->
      let t_pair_a_b =
        let t_tup2 =
          FStar_Syntax_Util.fvar_const FStar_Parser_Const.lid_tuple2  in
        let uu____53789 =
          let uu____53794 =
            let uu____53795 = FStar_Syntax_Syntax.as_arg ea.typ  in
            let uu____53804 =
              let uu____53815 = FStar_Syntax_Syntax.as_arg eb.typ  in
              [uu____53815]  in
            uu____53795 :: uu____53804  in
          FStar_Syntax_Syntax.mk_Tm_app t_tup2 uu____53794  in
        uu____53789 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
      let emb_t_pair_a_b =
        let uu____53849 =
          let uu____53857 =
            FStar_All.pipe_right FStar_Parser_Const.lid_tuple2
              FStar_Ident.string_of_lid
             in
          (uu____53857, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____53849  in
      let printer uu____53873 =
        match uu____53873 with
        | (x,y) ->
            let uu____53881 = ea.print x  in
            let uu____53883 = eb.print y  in
            FStar_Util.format2 "(%s, %s)" uu____53881 uu____53883
         in
      let em x rng topt norm1 =
        lazy_embed printer emb_t_pair_a_b rng t_pair_a_b x
          (fun uu____53926  ->
             let proj i ab =
               let uu____53942 =
                 let uu____53947 =
                   FStar_Parser_Const.mk_tuple_data_lid (Prims.parse_int "2")
                     rng
                    in
                 let uu____53949 =
                   FStar_Syntax_Syntax.null_bv FStar_Syntax_Syntax.tun  in
                 FStar_Syntax_Util.mk_field_projector_name uu____53947
                   uu____53949 i
                  in
               match uu____53942 with
               | (proj_1,uu____53953) ->
                   let proj_1_tm =
                     let uu____53955 =
                       FStar_Syntax_Syntax.lid_as_fv proj_1
                         FStar_Syntax_Syntax.delta_equational
                         FStar_Pervasives_Native.None
                        in
                     FStar_Syntax_Syntax.fv_to_tm uu____53955  in
                   let uu____53956 =
                     let uu____53961 =
                       FStar_Syntax_Syntax.mk_Tm_uinst proj_1_tm
                         [FStar_Syntax_Syntax.U_zero]
                        in
                     let uu____53962 =
                       let uu____53963 =
                         let uu____53972 = type_of ea  in
                         FStar_Syntax_Syntax.iarg uu____53972  in
                       let uu____53973 =
                         let uu____53984 =
                           let uu____53993 = type_of eb  in
                           FStar_Syntax_Syntax.iarg uu____53993  in
                         let uu____53994 =
                           let uu____54005 = FStar_Syntax_Syntax.as_arg ab
                              in
                           [uu____54005]  in
                         uu____53984 :: uu____53994  in
                       uu____53963 :: uu____53973  in
                     FStar_Syntax_Syntax.mk_Tm_app uu____53961 uu____53962
                      in
                   uu____53956 FStar_Pervasives_Native.None rng
                in
             let shadow_a = map_shadow topt (proj (Prims.parse_int "1"))  in
             let shadow_b = map_shadow topt (proj (Prims.parse_int "2"))  in
             let uu____54050 =
               let uu____54055 =
                 let uu____54056 =
                   FStar_Syntax_Syntax.tdataconstr
                     FStar_Parser_Const.lid_Mktuple2
                    in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu____54056
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                  in
               let uu____54057 =
                 let uu____54058 =
                   let uu____54067 = type_of ea  in
                   FStar_Syntax_Syntax.iarg uu____54067  in
                 let uu____54068 =
                   let uu____54079 =
                     let uu____54088 = type_of eb  in
                     FStar_Syntax_Syntax.iarg uu____54088  in
                   let uu____54089 =
                     let uu____54100 =
                       let uu____54109 =
                         let uu____54110 =
                           embed ea (FStar_Pervasives_Native.fst x)  in
                         uu____54110 rng shadow_a norm1  in
                       FStar_Syntax_Syntax.as_arg uu____54109  in
                     let uu____54117 =
                       let uu____54128 =
                         let uu____54137 =
                           let uu____54138 =
                             embed eb (FStar_Pervasives_Native.snd x)  in
                           uu____54138 rng shadow_b norm1  in
                         FStar_Syntax_Syntax.as_arg uu____54137  in
                       [uu____54128]  in
                     uu____54100 :: uu____54117  in
                   uu____54079 :: uu____54089  in
                 uu____54058 :: uu____54068  in
               FStar_Syntax_Syntax.mk_Tm_app uu____54055 uu____54057  in
             uu____54050 FStar_Pervasives_Native.None rng)
         in
      let un t0 w norm1 =
        let t = FStar_Syntax_Util.unmeta_safe t0  in
        lazy_unembed printer emb_t_pair_a_b t t_pair_a_b
          (fun t1  ->
             let uu____54236 = FStar_Syntax_Util.head_and_args' t1  in
             match uu____54236 with
             | (hd1,args) ->
                 let uu____54279 =
                   let uu____54292 =
                     let uu____54293 = FStar_Syntax_Util.un_uinst hd1  in
                     uu____54293.FStar_Syntax_Syntax.n  in
                   (uu____54292, args)  in
                 (match uu____54279 with
                  | (FStar_Syntax_Syntax.Tm_fvar
                     fv,uu____54311::uu____54312::(a,uu____54314)::(b,uu____54316)::[])
                      when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.lid_Mktuple2
                      ->
                      let uu____54375 =
                        let uu____54378 = unembed ea a  in
                        uu____54378 w norm1  in
                      FStar_Util.bind_opt uu____54375
                        (fun a1  ->
                           let uu____54392 =
                             let uu____54395 = unembed eb b  in
                             uu____54395 w norm1  in
                           FStar_Util.bind_opt uu____54392
                             (fun b1  ->
                                FStar_Pervasives_Native.Some (a1, b1)))
                  | uu____54412 ->
                      (if w
                       then
                         (let uu____54427 =
                            let uu____54433 =
                              let uu____54435 =
                                FStar_Syntax_Print.term_to_string t0  in
                              FStar_Util.format1 "Not an embedded pair: %s"
                                uu____54435
                               in
                            (FStar_Errors.Warning_NotEmbedded, uu____54433)
                             in
                          FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                            uu____54427)
                       else ();
                       FStar_Pervasives_Native.None)))
         in
      let uu____54445 =
        let uu____54446 = type_of ea  in
        let uu____54447 = type_of eb  in
        FStar_Syntax_Syntax.t_tuple2_of uu____54446 uu____54447  in
      mk_emb_full em un uu____54445 printer emb_t_pair_a_b
  
let e_either :
  'a 'b . 'a embedding -> 'b embedding -> ('a,'b) FStar_Util.either embedding
  =
  fun ea  ->
    fun eb  ->
      let t_sum_a_b =
        let t_either =
          FStar_Syntax_Util.fvar_const FStar_Parser_Const.either_lid  in
        let uu____54491 =
          let uu____54496 =
            let uu____54497 = FStar_Syntax_Syntax.as_arg ea.typ  in
            let uu____54506 =
              let uu____54517 = FStar_Syntax_Syntax.as_arg eb.typ  in
              [uu____54517]  in
            uu____54497 :: uu____54506  in
          FStar_Syntax_Syntax.mk_Tm_app t_either uu____54496  in
        uu____54491 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
      let emb_t_sum_a_b =
        let uu____54551 =
          let uu____54559 =
            FStar_All.pipe_right FStar_Parser_Const.either_lid
              FStar_Ident.string_of_lid
             in
          (uu____54559, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____54551  in
      let printer s =
        match s with
        | FStar_Util.Inl a ->
            let uu____54582 = ea.print a  in
            FStar_Util.format1 "Inl %s" uu____54582
        | FStar_Util.Inr b ->
            let uu____54586 = eb.print b  in
            FStar_Util.format1 "Inr %s" uu____54586
         in
      let em s rng topt norm1 =
        lazy_embed printer emb_t_sum_a_b rng t_sum_a_b s
          (match s with
           | FStar_Util.Inl a ->
               (fun uu____54632  ->
                  let shadow_a =
                    map_shadow topt
                      (fun t  ->
                         let v1 = FStar_Ident.mk_ident ("v", rng)  in
                         let some_v =
                           FStar_Syntax_Util.mk_field_projector_name_from_ident
                             FStar_Parser_Const.inl_lid v1
                            in
                         let some_v_tm =
                           let uu____54645 =
                             FStar_Syntax_Syntax.lid_as_fv some_v
                               FStar_Syntax_Syntax.delta_equational
                               FStar_Pervasives_Native.None
                              in
                           FStar_Syntax_Syntax.fv_to_tm uu____54645  in
                         let uu____54646 =
                           let uu____54651 =
                             FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm
                               [FStar_Syntax_Syntax.U_zero]
                              in
                           let uu____54652 =
                             let uu____54653 =
                               let uu____54662 = type_of ea  in
                               FStar_Syntax_Syntax.iarg uu____54662  in
                             let uu____54663 =
                               let uu____54674 =
                                 let uu____54683 = type_of eb  in
                                 FStar_Syntax_Syntax.iarg uu____54683  in
                               let uu____54684 =
                                 let uu____54695 =
                                   FStar_Syntax_Syntax.as_arg t  in
                                 [uu____54695]  in
                               uu____54674 :: uu____54684  in
                             uu____54653 :: uu____54663  in
                           FStar_Syntax_Syntax.mk_Tm_app uu____54651
                             uu____54652
                            in
                         uu____54646 FStar_Pervasives_Native.None rng)
                     in
                  let uu____54736 =
                    let uu____54741 =
                      let uu____54742 =
                        FStar_Syntax_Syntax.tdataconstr
                          FStar_Parser_Const.inl_lid
                         in
                      FStar_Syntax_Syntax.mk_Tm_uinst uu____54742
                        [FStar_Syntax_Syntax.U_zero;
                        FStar_Syntax_Syntax.U_zero]
                       in
                    let uu____54743 =
                      let uu____54744 =
                        let uu____54753 = type_of ea  in
                        FStar_Syntax_Syntax.iarg uu____54753  in
                      let uu____54754 =
                        let uu____54765 =
                          let uu____54774 = type_of eb  in
                          FStar_Syntax_Syntax.iarg uu____54774  in
                        let uu____54775 =
                          let uu____54786 =
                            let uu____54795 =
                              let uu____54796 = embed ea a  in
                              uu____54796 rng shadow_a norm1  in
                            FStar_Syntax_Syntax.as_arg uu____54795  in
                          [uu____54786]  in
                        uu____54765 :: uu____54775  in
                      uu____54744 :: uu____54754  in
                    FStar_Syntax_Syntax.mk_Tm_app uu____54741 uu____54743  in
                  uu____54736 FStar_Pervasives_Native.None rng)
           | FStar_Util.Inr b ->
               (fun uu____54836  ->
                  let shadow_b =
                    map_shadow topt
                      (fun t  ->
                         let v1 = FStar_Ident.mk_ident ("v", rng)  in
                         let some_v =
                           FStar_Syntax_Util.mk_field_projector_name_from_ident
                             FStar_Parser_Const.inr_lid v1
                            in
                         let some_v_tm =
                           let uu____54849 =
                             FStar_Syntax_Syntax.lid_as_fv some_v
                               FStar_Syntax_Syntax.delta_equational
                               FStar_Pervasives_Native.None
                              in
                           FStar_Syntax_Syntax.fv_to_tm uu____54849  in
                         let uu____54850 =
                           let uu____54855 =
                             FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm
                               [FStar_Syntax_Syntax.U_zero]
                              in
                           let uu____54856 =
                             let uu____54857 =
                               let uu____54866 = type_of ea  in
                               FStar_Syntax_Syntax.iarg uu____54866  in
                             let uu____54867 =
                               let uu____54878 =
                                 let uu____54887 = type_of eb  in
                                 FStar_Syntax_Syntax.iarg uu____54887  in
                               let uu____54888 =
                                 let uu____54899 =
                                   FStar_Syntax_Syntax.as_arg t  in
                                 [uu____54899]  in
                               uu____54878 :: uu____54888  in
                             uu____54857 :: uu____54867  in
                           FStar_Syntax_Syntax.mk_Tm_app uu____54855
                             uu____54856
                            in
                         uu____54850 FStar_Pervasives_Native.None rng)
                     in
                  let uu____54940 =
                    let uu____54945 =
                      let uu____54946 =
                        FStar_Syntax_Syntax.tdataconstr
                          FStar_Parser_Const.inr_lid
                         in
                      FStar_Syntax_Syntax.mk_Tm_uinst uu____54946
                        [FStar_Syntax_Syntax.U_zero;
                        FStar_Syntax_Syntax.U_zero]
                       in
                    let uu____54947 =
                      let uu____54948 =
                        let uu____54957 = type_of ea  in
                        FStar_Syntax_Syntax.iarg uu____54957  in
                      let uu____54958 =
                        let uu____54969 =
                          let uu____54978 = type_of eb  in
                          FStar_Syntax_Syntax.iarg uu____54978  in
                        let uu____54979 =
                          let uu____54990 =
                            let uu____54999 =
                              let uu____55000 = embed eb b  in
                              uu____55000 rng shadow_b norm1  in
                            FStar_Syntax_Syntax.as_arg uu____54999  in
                          [uu____54990]  in
                        uu____54969 :: uu____54979  in
                      uu____54948 :: uu____54958  in
                    FStar_Syntax_Syntax.mk_Tm_app uu____54945 uu____54947  in
                  uu____54940 FStar_Pervasives_Native.None rng))
         in
      let un t0 w norm1 =
        let t = FStar_Syntax_Util.unmeta_safe t0  in
        lazy_unembed printer emb_t_sum_a_b t t_sum_a_b
          (fun t1  ->
             let uu____55088 = FStar_Syntax_Util.head_and_args' t1  in
             match uu____55088 with
             | (hd1,args) ->
                 let uu____55131 =
                   let uu____55146 =
                     let uu____55147 = FStar_Syntax_Util.un_uinst hd1  in
                     uu____55147.FStar_Syntax_Syntax.n  in
                   (uu____55146, args)  in
                 (match uu____55131 with
                  | (FStar_Syntax_Syntax.Tm_fvar
                     fv,uu____55167::uu____55168::(a,uu____55170)::[]) when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.inl_lid
                      ->
                      let uu____55237 =
                        let uu____55240 = unembed ea a  in
                        uu____55240 w norm1  in
                      FStar_Util.bind_opt uu____55237
                        (fun a1  ->
                           FStar_Pervasives_Native.Some (FStar_Util.Inl a1))
                  | (FStar_Syntax_Syntax.Tm_fvar
                     fv,uu____55258::uu____55259::(b,uu____55261)::[]) when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.inr_lid
                      ->
                      let uu____55328 =
                        let uu____55331 = unembed eb b  in
                        uu____55331 w norm1  in
                      FStar_Util.bind_opt uu____55328
                        (fun b1  ->
                           FStar_Pervasives_Native.Some (FStar_Util.Inr b1))
                  | uu____55348 ->
                      (if w
                       then
                         (let uu____55365 =
                            let uu____55371 =
                              let uu____55373 =
                                FStar_Syntax_Print.term_to_string t0  in
                              FStar_Util.format1 "Not an embedded sum: %s"
                                uu____55373
                               in
                            (FStar_Errors.Warning_NotEmbedded, uu____55371)
                             in
                          FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                            uu____55365)
                       else ();
                       FStar_Pervasives_Native.None)))
         in
      let uu____55383 =
        let uu____55384 = type_of ea  in
        let uu____55385 = type_of eb  in
        FStar_Syntax_Syntax.t_either_of uu____55384 uu____55385  in
      mk_emb_full em un uu____55383 printer emb_t_sum_a_b
  
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea  ->
    let t_list_a =
      let t_list = FStar_Syntax_Util.fvar_const FStar_Parser_Const.list_lid
         in
      let uu____55413 =
        let uu____55418 =
          let uu____55419 = FStar_Syntax_Syntax.as_arg ea.typ  in
          [uu____55419]  in
        FStar_Syntax_Syntax.mk_Tm_app t_list uu____55418  in
      uu____55413 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
    let emb_t_list_a =
      let uu____55445 =
        let uu____55453 =
          FStar_All.pipe_right FStar_Parser_Const.list_lid
            FStar_Ident.string_of_lid
           in
        (uu____55453, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____55445  in
    let printer l =
      let uu____55470 =
        let uu____55472 =
          let uu____55474 = FStar_List.map ea.print l  in
          FStar_All.pipe_right uu____55474 (FStar_String.concat "; ")  in
        Prims.op_Hat uu____55472 "]"  in
      Prims.op_Hat "[" uu____55470  in
    let rec em l rng shadow_l norm1 =
      lazy_embed printer emb_t_list_a rng t_list_a l
        (fun uu____55518  ->
           let t =
             let uu____55520 = type_of ea  in
             FStar_Syntax_Syntax.iarg uu____55520  in
           match l with
           | [] ->
               let uu____55521 =
                 let uu____55526 =
                   let uu____55527 =
                     FStar_Syntax_Syntax.tdataconstr
                       FStar_Parser_Const.nil_lid
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____55527
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 FStar_Syntax_Syntax.mk_Tm_app uu____55526 [t]  in
               uu____55521 FStar_Pervasives_Native.None rng
           | hd1::tl1 ->
               let cons1 =
                 let uu____55549 =
                   FStar_Syntax_Syntax.tdataconstr
                     FStar_Parser_Const.cons_lid
                    in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu____55549
                   [FStar_Syntax_Syntax.U_zero]
                  in
               let proj f cons_tm =
                 let fid = FStar_Ident.mk_ident (f, rng)  in
                 let proj =
                   FStar_Syntax_Util.mk_field_projector_name_from_ident
                     FStar_Parser_Const.cons_lid fid
                    in
                 let proj_tm =
                   let uu____55569 =
                     FStar_Syntax_Syntax.lid_as_fv proj
                       FStar_Syntax_Syntax.delta_equational
                       FStar_Pervasives_Native.None
                      in
                   FStar_Syntax_Syntax.fv_to_tm uu____55569  in
                 let uu____55570 =
                   let uu____55575 =
                     FStar_Syntax_Syntax.mk_Tm_uinst proj_tm
                       [FStar_Syntax_Syntax.U_zero]
                      in
                   let uu____55576 =
                     let uu____55577 =
                       let uu____55586 = type_of ea  in
                       FStar_Syntax_Syntax.iarg uu____55586  in
                     let uu____55587 =
                       let uu____55598 = FStar_Syntax_Syntax.as_arg cons_tm
                          in
                       [uu____55598]  in
                     uu____55577 :: uu____55587  in
                   FStar_Syntax_Syntax.mk_Tm_app uu____55575 uu____55576  in
                 uu____55570 FStar_Pervasives_Native.None rng  in
               let shadow_hd = map_shadow shadow_l (proj "hd")  in
               let shadow_tl = map_shadow shadow_l (proj "tl")  in
               let uu____55635 =
                 let uu____55640 =
                   let uu____55641 =
                     let uu____55652 =
                       let uu____55661 =
                         let uu____55662 = embed ea hd1  in
                         uu____55662 rng shadow_hd norm1  in
                       FStar_Syntax_Syntax.as_arg uu____55661  in
                     let uu____55669 =
                       let uu____55680 =
                         let uu____55689 = em tl1 rng shadow_tl norm1  in
                         FStar_Syntax_Syntax.as_arg uu____55689  in
                       [uu____55680]  in
                     uu____55652 :: uu____55669  in
                   t :: uu____55641  in
                 FStar_Syntax_Syntax.mk_Tm_app cons1 uu____55640  in
               uu____55635 FStar_Pervasives_Native.None rng)
       in
    let rec un t0 w norm1 =
      let t = FStar_Syntax_Util.unmeta_safe t0  in
      lazy_unembed printer emb_t_list_a t t_list_a
        (fun t1  ->
           let uu____55761 = FStar_Syntax_Util.head_and_args' t1  in
           match uu____55761 with
           | (hd1,args) ->
               let uu____55802 =
                 let uu____55815 =
                   let uu____55816 = FStar_Syntax_Util.un_uinst hd1  in
                   uu____55816.FStar_Syntax_Syntax.n  in
                 (uu____55815, args)  in
               (match uu____55802 with
                | (FStar_Syntax_Syntax.Tm_fvar fv,uu____55832) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.nil_lid
                    -> FStar_Pervasives_Native.Some []
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(uu____55852,FStar_Pervasives_Native.Some
                       (FStar_Syntax_Syntax.Implicit uu____55853))::(hd2,FStar_Pervasives_Native.None
                                                                    )::
                   (tl1,FStar_Pervasives_Native.None )::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.cons_lid
                    ->
                    let uu____55895 =
                      let uu____55898 = unembed ea hd2  in
                      uu____55898 w norm1  in
                    FStar_Util.bind_opt uu____55895
                      (fun hd3  ->
                         let uu____55910 = un tl1 w norm1  in
                         FStar_Util.bind_opt uu____55910
                           (fun tl2  ->
                              FStar_Pervasives_Native.Some (hd3 :: tl2)))
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(hd2,FStar_Pervasives_Native.None )::(tl1,FStar_Pervasives_Native.None
                                                            )::[])
                    when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.cons_lid
                    ->
                    let uu____55958 =
                      let uu____55961 = unembed ea hd2  in
                      uu____55961 w norm1  in
                    FStar_Util.bind_opt uu____55958
                      (fun hd3  ->
                         let uu____55973 = un tl1 w norm1  in
                         FStar_Util.bind_opt uu____55973
                           (fun tl2  ->
                              FStar_Pervasives_Native.Some (hd3 :: tl2)))
                | uu____55988 ->
                    (if w
                     then
                       (let uu____56003 =
                          let uu____56009 =
                            let uu____56011 =
                              FStar_Syntax_Print.term_to_string t0  in
                            FStar_Util.format1 "Not an embedded list: %s"
                              uu____56011
                             in
                          (FStar_Errors.Warning_NotEmbedded, uu____56009)  in
                        FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                          uu____56003)
                     else ();
                     FStar_Pervasives_Native.None)))
       in
    let uu____56019 =
      let uu____56020 = type_of ea  in
      FStar_Syntax_Syntax.t_list_of uu____56020  in
    mk_emb_full em un uu____56019 printer emb_t_list_a
  
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
    match projectee with | Simpl  -> true | uu____56063 -> false
  
let (uu___is_Weak : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Weak  -> true | uu____56074 -> false
  
let (uu___is_HNF : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | HNF  -> true | uu____56085 -> false
  
let (uu___is_Primops : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____56096 -> false
  
let (uu___is_Delta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Delta  -> true | uu____56107 -> false
  
let (uu___is_Zeta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Zeta  -> true | uu____56118 -> false
  
let (uu___is_Iota : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Iota  -> true | uu____56129 -> false
  
let (uu___is_Reify : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____56140 -> false
  
let (uu___is_UnfoldOnly : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____56155 -> false
  
let (__proj__UnfoldOnly__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldFully : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldFully _0 -> true | uu____56187 -> false
  
let (__proj__UnfoldFully__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldFully _0 -> _0 
let (uu___is_UnfoldAttr : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____56219 -> false
  
let (__proj__UnfoldAttr__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_NBE : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | NBE  -> true | uu____56247 -> false
  
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
    let uu____56265 =
      FStar_Ident.lid_of_str "FStar.Syntax.Embeddings.norm_step"  in
    FStar_Syntax_Util.fvar_const uu____56265  in
  let emb_t_norm_step =
    let uu____56268 =
      let uu____56276 =
        FStar_All.pipe_right FStar_Parser_Const.norm_step_lid
          FStar_Ident.string_of_lid
         in
      (uu____56276, [])  in
    FStar_Syntax_Syntax.ET_app uu____56268  in
  let printer uu____56288 = "norm_step"  in
  let em n1 rng _topt norm1 =
    lazy_embed printer emb_t_norm_step rng t_norm_step1 n1
      (fun uu____56314  ->
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
             let uu____56319 =
               let uu____56324 =
                 let uu____56325 =
                   let uu____56334 =
                     let uu____56335 =
                       let uu____56342 = e_list e_string  in
                       embed uu____56342 l  in
                     uu____56335 rng FStar_Pervasives_Native.None norm1  in
                   FStar_Syntax_Syntax.as_arg uu____56334  in
                 [uu____56325]  in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldOnly uu____56324  in
             uu____56319 FStar_Pervasives_Native.None rng
         | UnfoldFully l ->
             let uu____56374 =
               let uu____56379 =
                 let uu____56380 =
                   let uu____56389 =
                     let uu____56390 =
                       let uu____56397 = e_list e_string  in
                       embed uu____56397 l  in
                     uu____56390 rng FStar_Pervasives_Native.None norm1  in
                   FStar_Syntax_Syntax.as_arg uu____56389  in
                 [uu____56380]  in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldFully uu____56379
                in
             uu____56374 FStar_Pervasives_Native.None rng
         | UnfoldAttr l ->
             let uu____56429 =
               let uu____56434 =
                 let uu____56435 =
                   let uu____56444 =
                     let uu____56445 =
                       let uu____56452 = e_list e_string  in
                       embed uu____56452 l  in
                     uu____56445 rng FStar_Pervasives_Native.None norm1  in
                   FStar_Syntax_Syntax.as_arg uu____56444  in
                 [uu____56435]  in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldAttr uu____56434  in
             uu____56429 FStar_Pervasives_Native.None rng)
     in
  let un t0 w norm1 =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    lazy_unembed printer emb_t_norm_step t t_norm_step1
      (fun t1  ->
         let uu____56512 = FStar_Syntax_Util.head_and_args t1  in
         match uu____56512 with
         | (hd1,args) ->
             let uu____56557 =
               let uu____56572 =
                 let uu____56573 = FStar_Syntax_Util.un_uinst hd1  in
                 uu____56573.FStar_Syntax_Syntax.n  in
               (uu____56572, args)  in
             (match uu____56557 with
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
              | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____56761)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldonly
                  ->
                  let uu____56796 =
                    let uu____56802 =
                      let uu____56812 = e_list e_string  in
                      unembed uu____56812 l  in
                    uu____56802 w norm1  in
                  FStar_Util.bind_opt uu____56796
                    (fun ss  ->
                       FStar_All.pipe_left
                         (fun _56832  -> FStar_Pervasives_Native.Some _56832)
                         (UnfoldOnly ss))
              | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____56835)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldfully
                  ->
                  let uu____56870 =
                    let uu____56876 =
                      let uu____56886 = e_list e_string  in
                      unembed uu____56886 l  in
                    uu____56876 w norm1  in
                  FStar_Util.bind_opt uu____56870
                    (fun ss  ->
                       FStar_All.pipe_left
                         (fun _56906  -> FStar_Pervasives_Native.Some _56906)
                         (UnfoldFully ss))
              | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____56909)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldattr
                  ->
                  let uu____56944 =
                    let uu____56950 =
                      let uu____56960 = e_list e_string  in
                      unembed uu____56960 l  in
                    uu____56950 w norm1  in
                  FStar_Util.bind_opt uu____56944
                    (fun ss  ->
                       FStar_All.pipe_left
                         (fun _56980  -> FStar_Pervasives_Native.Some _56980)
                         (UnfoldAttr ss))
              | uu____56981 ->
                  (if w
                   then
                     (let uu____56998 =
                        let uu____57004 =
                          let uu____57006 =
                            FStar_Syntax_Print.term_to_string t0  in
                          FStar_Util.format1 "Not an embedded norm_step: %s"
                            uu____57006
                           in
                        (FStar_Errors.Warning_NotEmbedded, uu____57004)  in
                      FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                        uu____56998)
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
    | uu____57066 ->
        (if w
         then
           (let uu____57069 =
              let uu____57075 =
                let uu____57077 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded range: %s" uu____57077
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____57075)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____57069)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____57083 =
    let uu____57084 =
      let uu____57092 =
        FStar_All.pipe_right FStar_Parser_Const.range_lid
          FStar_Ident.string_of_lid
         in
      (uu____57092, [])  in
    FStar_Syntax_Syntax.ET_app uu____57084  in
  mk_emb_full em un FStar_Syntax_Syntax.t_range FStar_Range.string_of_range
    uu____57083
  
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
        let uu____57163 =
          let uu____57170 =
            let uu____57171 =
              let uu____57186 =
                let uu____57195 =
                  let uu____57202 = FStar_Syntax_Syntax.null_bv ea.typ  in
                  (uu____57202, FStar_Pervasives_Native.None)  in
                [uu____57195]  in
              let uu____57217 = FStar_Syntax_Syntax.mk_Total eb.typ  in
              (uu____57186, uu____57217)  in
            FStar_Syntax_Syntax.Tm_arrow uu____57171  in
          FStar_Syntax_Syntax.mk uu____57170  in
        uu____57163 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
      let emb_t_arr_a_b =
        FStar_Syntax_Syntax.ET_fun ((ea.emb_typ), (eb.emb_typ))  in
      let printer f = "<fun>"  in
      let em f rng shadow_f norm1 =
        lazy_embed (fun uu____57289  -> "<fun>") emb_t_arr_a_b rng t_arrow f
          (fun uu____57295  ->
             let uu____57296 = force_shadow shadow_f  in
             match uu____57296 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Exn.raise Embedding_failure
             | FStar_Pervasives_Native.Some repr_f ->
                 ((let uu____57301 =
                     FStar_ST.op_Bang FStar_Options.debug_embedding  in
                   if uu____57301
                   then
                     let uu____57325 =
                       FStar_Syntax_Print.term_to_string repr_f  in
                     let uu____57327 = FStar_Util.stack_dump ()  in
                     FStar_Util.print2
                       "e_arrow forced back to term using shadow %s; repr=%s\n"
                       uu____57325 uu____57327
                   else ());
                  (let res = norm1 (FStar_Util.Inr repr_f)  in
                   (let uu____57334 =
                      FStar_ST.op_Bang FStar_Options.debug_embedding  in
                    if uu____57334
                    then
                      let uu____57358 =
                        FStar_Syntax_Print.term_to_string repr_f  in
                      let uu____57360 = FStar_Syntax_Print.term_to_string res
                         in
                      let uu____57362 = FStar_Util.stack_dump ()  in
                      FStar_Util.print3
                        "e_arrow forced back to term using shadow %s; repr=%s\n\t%s\n"
                        uu____57358 uu____57360 uu____57362
                    else ());
                   res)))
         in
      let un f w norm1 =
        lazy_unembed printer emb_t_arr_a_b f t_arrow
          (fun f1  ->
             let f_wrapped a =
               (let uu____57421 =
                  FStar_ST.op_Bang FStar_Options.debug_embedding  in
                if uu____57421
                then
                  let uu____57445 = FStar_Syntax_Print.term_to_string f1  in
                  let uu____57447 = FStar_Util.stack_dump ()  in
                  FStar_Util.print2
                    "Calling back into normalizer for %s\n%s\n" uu____57445
                    uu____57447
                else ());
               (let a_tm =
                  let uu____57453 = embed ea a  in
                  uu____57453 f1.FStar_Syntax_Syntax.pos
                    FStar_Pervasives_Native.None norm1
                   in
                let b_tm =
                  let uu____57463 =
                    let uu____57468 =
                      let uu____57469 =
                        let uu____57474 =
                          let uu____57475 = FStar_Syntax_Syntax.as_arg a_tm
                             in
                          [uu____57475]  in
                        FStar_Syntax_Syntax.mk_Tm_app f1 uu____57474  in
                      uu____57469 FStar_Pervasives_Native.None
                        f1.FStar_Syntax_Syntax.pos
                       in
                    FStar_Util.Inr uu____57468  in
                  norm1 uu____57463  in
                let uu____57500 =
                  let uu____57503 = unembed eb b_tm  in uu____57503 w norm1
                   in
                match uu____57500 with
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
                let uu____57597 = FStar_List.splitAt n_tvars args  in
                match uu____57597 with
                | (_tvar_args,rest_args) ->
                    let uu____57674 = FStar_List.hd rest_args  in
                    (match uu____57674 with
                     | (x,uu____57694) ->
                         let shadow_app =
                           let uu____57708 =
                             FStar_Common.mk_thunk
                               (fun uu____57715  ->
                                  let uu____57716 =
                                    let uu____57721 =
                                      norm1 (FStar_Util.Inl fv_lid1)  in
                                    FStar_Syntax_Syntax.mk_Tm_app uu____57721
                                      args
                                     in
                                  uu____57716 FStar_Pervasives_Native.None
                                    rng)
                              in
                           FStar_Pervasives_Native.Some uu____57708  in
                         let uu____57724 =
                           let uu____57727 =
                             let uu____57730 = unembed ea x  in
                             uu____57730 true norm1  in
                           FStar_Util.map_opt uu____57727
                             (fun x1  ->
                                let uu____57741 =
                                  let uu____57748 = f x1  in
                                  embed eb uu____57748  in
                                uu____57741 rng shadow_app norm1)
                            in
                         (match uu____57724 with
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
                  let uu____57851 = FStar_List.splitAt n_tvars args  in
                  match uu____57851 with
                  | (_tvar_args,rest_args) ->
                      let uu____57914 = FStar_List.hd rest_args  in
                      (match uu____57914 with
                       | (x,uu____57930) ->
                           let uu____57935 =
                             let uu____57942 = FStar_List.tl rest_args  in
                             FStar_List.hd uu____57942  in
                           (match uu____57935 with
                            | (y,uu____57966) ->
                                let shadow_app =
                                  let uu____57976 =
                                    FStar_Common.mk_thunk
                                      (fun uu____57983  ->
                                         let uu____57984 =
                                           let uu____57989 =
                                             norm1 (FStar_Util.Inl fv_lid1)
                                              in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____57989 args
                                            in
                                         uu____57984
                                           FStar_Pervasives_Native.None rng)
                                     in
                                  FStar_Pervasives_Native.Some uu____57976
                                   in
                                let uu____57992 =
                                  let uu____57995 =
                                    let uu____57998 = unembed ea x  in
                                    uu____57998 true norm1  in
                                  FStar_Util.bind_opt uu____57995
                                    (fun x1  ->
                                       let uu____58009 =
                                         let uu____58012 = unembed eb y  in
                                         uu____58012 true norm1  in
                                       FStar_Util.bind_opt uu____58009
                                         (fun y1  ->
                                            let uu____58023 =
                                              let uu____58024 =
                                                let uu____58031 = f x1 y1  in
                                                embed ec uu____58031  in
                                              uu____58024 rng shadow_app
                                                norm1
                                               in
                                            FStar_Pervasives_Native.Some
                                              uu____58023))
                                   in
                                (match uu____57992 with
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
                    let uu____58153 = FStar_List.splitAt n_tvars args  in
                    match uu____58153 with
                    | (_tvar_args,rest_args) ->
                        let uu____58216 = FStar_List.hd rest_args  in
                        (match uu____58216 with
                         | (x,uu____58232) ->
                             let uu____58237 =
                               let uu____58244 = FStar_List.tl rest_args  in
                               FStar_List.hd uu____58244  in
                             (match uu____58237 with
                              | (y,uu____58268) ->
                                  let uu____58273 =
                                    let uu____58280 =
                                      let uu____58289 =
                                        FStar_List.tl rest_args  in
                                      FStar_List.tl uu____58289  in
                                    FStar_List.hd uu____58280  in
                                  (match uu____58273 with
                                   | (z,uu____58319) ->
                                       let shadow_app =
                                         let uu____58329 =
                                           FStar_Common.mk_thunk
                                             (fun uu____58336  ->
                                                let uu____58337 =
                                                  let uu____58342 =
                                                    norm1
                                                      (FStar_Util.Inl fv_lid1)
                                                     in
                                                  FStar_Syntax_Syntax.mk_Tm_app
                                                    uu____58342 args
                                                   in
                                                uu____58337
                                                  FStar_Pervasives_Native.None
                                                  rng)
                                            in
                                         FStar_Pervasives_Native.Some
                                           uu____58329
                                          in
                                       let uu____58345 =
                                         let uu____58348 =
                                           let uu____58351 = unembed ea x  in
                                           uu____58351 true norm1  in
                                         FStar_Util.bind_opt uu____58348
                                           (fun x1  ->
                                              let uu____58362 =
                                                let uu____58365 =
                                                  unembed eb y  in
                                                uu____58365 true norm1  in
                                              FStar_Util.bind_opt uu____58362
                                                (fun y1  ->
                                                   let uu____58376 =
                                                     let uu____58379 =
                                                       unembed ec z  in
                                                     uu____58379 true norm1
                                                      in
                                                   FStar_Util.bind_opt
                                                     uu____58376
                                                     (fun z1  ->
                                                        let uu____58390 =
                                                          let uu____58391 =
                                                            let uu____58398 =
                                                              f x1 y1 z1  in
                                                            embed ed
                                                              uu____58398
                                                             in
                                                          uu____58391 rng
                                                            shadow_app norm1
                                                           in
                                                        FStar_Pervasives_Native.Some
                                                          uu____58390)))
                                          in
                                       (match uu____58345 with
                                        | FStar_Pervasives_Native.Some x1 ->
                                            FStar_Pervasives_Native.Some x1
                                        | FStar_Pervasives_Native.None  ->
                                            force_shadow shadow_app))))
                     in
                  f_wrapped
  
let debug_wrap : 'a . Prims.string -> (unit -> 'a) -> 'a =
  fun s  ->
    fun f  ->
      (let uu____58428 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
       if uu____58428 then FStar_Util.print1 "++++starting %s\n" s else ());
      (let res = f ()  in
       (let uu____58457 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
        if uu____58457 then FStar_Util.print1 "------ending %s\n" s else ());
       res)
  