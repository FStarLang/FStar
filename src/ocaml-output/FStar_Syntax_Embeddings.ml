open Prims
type norm_cb =
  (FStar_Ident.lid,FStar_Syntax_Syntax.term) FStar_Util.either ->
    FStar_Syntax_Syntax.term
let (id_norm_cb : norm_cb) =
  fun uu___429_55308  ->
    match uu___429_55308 with
    | FStar_Util.Inr x -> x
    | FStar_Util.Inl l ->
        let uu____55315 =
          FStar_Syntax_Syntax.lid_as_fv l
            FStar_Syntax_Syntax.delta_equational FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.fv_to_tm uu____55315
  
exception Embedding_failure 
let (uu___is_Embedding_failure : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Embedding_failure  -> true | uu____55325 -> false
  
exception Unembedding_failure 
let (uu___is_Unembedding_failure : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Unembedding_failure  -> true
    | uu____55336 -> false
  
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
             (fun uu____55502  ->
                let uu____55503 = FStar_Common.force_thunk s1  in
                f uu____55503))
  
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
  'Auu____56137 . FStar_Syntax_Syntax.term -> 'Auu____56137 -> Prims.string =
  fun typ  ->
    fun uu____56148  ->
      let uu____56149 = FStar_Syntax_Print.term_to_string typ  in
      FStar_Util.format1 "unknown %s" uu____56149
  
let (term_as_fv : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.fv) =
  fun t  ->
    let uu____56158 =
      let uu____56159 = FStar_Syntax_Subst.compress t  in
      uu____56159.FStar_Syntax_Syntax.n  in
    match uu____56158 with
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv
    | uu____56163 ->
        let uu____56164 =
          let uu____56166 = FStar_Syntax_Print.term_to_string t  in
          FStar_Util.format1 "Embeddings not defined for type %s" uu____56166
           in
        failwith uu____56164
  
let mk_emb :
  'a .
    'a raw_embedder ->
      'a raw_unembedder -> FStar_Syntax_Syntax.fv -> 'a embedding
  =
  fun em  ->
    fun un  ->
      fun fv  ->
        let typ = FStar_Syntax_Syntax.fv_to_tm fv  in
        let uu____56294 =
          let uu____56295 =
            let uu____56303 =
              let uu____56305 = FStar_Syntax_Syntax.lid_of_fv fv  in
              FStar_All.pipe_right uu____56305 FStar_Ident.string_of_lid  in
            (uu____56303, [])  in
          FStar_Syntax_Syntax.ET_app uu____56295  in
        { em; un; typ; print = (unknown_printer typ); emb_typ = uu____56294 }
  
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
      fun n1  -> let uu____56715 = unembed e t  in uu____56715 true n1
  
let try_unembed :
  'a .
    'a embedding ->
      FStar_Syntax_Syntax.term ->
        norm_cb -> 'a FStar_Pervasives_Native.option
  =
  fun e  ->
    fun t  ->
      fun n1  -> let uu____56764 = unembed e t  in uu____56764 false n1
  
let type_of : 'a . 'a embedding -> FStar_Syntax_Syntax.typ = fun e  -> e.typ 
let set_type : 'a . FStar_Syntax_Syntax.typ -> 'a embedding -> 'a embedding =
  fun ty  ->
    fun e  ->
      let uu___508_56817 = e  in
      {
        em = (uu___508_56817.em);
        un = (uu___508_56817.un);
        typ = ty;
        print = (uu___508_56817.print);
        emb_typ = (uu___508_56817.emb_typ)
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
              (let uu____56886 =
                 FStar_ST.op_Bang FStar_Options.debug_embedding  in
               if uu____56886
               then
                 let uu____56910 = FStar_Syntax_Print.term_to_string ta  in
                 let uu____56912 = FStar_Syntax_Print.emb_typ_to_string et
                    in
                 let uu____56914 = pa x  in
                 FStar_Util.print3
                   "Embedding a %s\n\temb_typ=%s\n\tvalue is %s\n"
                   uu____56910 uu____56912 uu____56914
               else ());
              (let uu____56921 =
                 FStar_ST.op_Bang FStar_Options.eager_embedding  in
               if uu____56921
               then f ()
               else
                 (let thunk1 = FStar_Common.mk_thunk f  in
                  let uu____56956 =
                    let uu____56963 =
                      let uu____56964 =
                        let uu____56965 = FStar_Dyn.mkdyn x  in
                        {
                          FStar_Syntax_Syntax.blob = uu____56965;
                          FStar_Syntax_Syntax.lkind =
                            (FStar_Syntax_Syntax.Lazy_embedding (et, thunk1));
                          FStar_Syntax_Syntax.ltyp = FStar_Syntax_Syntax.tun;
                          FStar_Syntax_Syntax.rng = rng
                        }  in
                      FStar_Syntax_Syntax.Tm_lazy uu____56964  in
                    FStar_Syntax_Syntax.mk uu____56963  in
                  uu____56956 FStar_Pervasives_Native.None rng))
  
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
                  FStar_Syntax_Syntax.ltyp = uu____57081;
                  FStar_Syntax_Syntax.rng = uu____57082;_}
                ->
                let uu____57093 =
                  (et <> et') ||
                    (FStar_ST.op_Bang FStar_Options.eager_embedding)
                   in
                if uu____57093
                then
                  let res =
                    let uu____57122 = FStar_Common.force_thunk t  in
                    f uu____57122  in
                  ((let uu____57166 =
                      FStar_ST.op_Bang FStar_Options.debug_embedding  in
                    if uu____57166
                    then
                      let uu____57190 =
                        FStar_Syntax_Print.emb_typ_to_string et  in
                      let uu____57192 =
                        FStar_Syntax_Print.emb_typ_to_string et'  in
                      let uu____57194 =
                        match res with
                        | FStar_Pervasives_Native.None  -> "None"
                        | FStar_Pervasives_Native.Some x2 ->
                            let uu____57199 = pa x2  in
                            Prims.op_Hat "Some " uu____57199
                         in
                      FStar_Util.print3
                        "Unembed cancellation failed\n\t%s <> %s\nvalue is %s\n"
                        uu____57190 uu____57192 uu____57194
                    else ());
                   res)
                else
                  (let a = FStar_Dyn.undyn b  in
                   (let uu____57211 =
                      FStar_ST.op_Bang FStar_Options.debug_embedding  in
                    if uu____57211
                    then
                      let uu____57235 =
                        FStar_Syntax_Print.emb_typ_to_string et  in
                      let uu____57237 = pa a  in
                      FStar_Util.print2
                        "Unembed cancelled for %s\n\tvalue is %s\n"
                        uu____57235 uu____57237
                    else ());
                   FStar_Pervasives_Native.Some a)
            | uu____57244 ->
                let aopt = f x1  in
                ((let uu____57249 =
                    FStar_ST.op_Bang FStar_Options.debug_embedding  in
                  if uu____57249
                  then
                    let uu____57273 = FStar_Syntax_Print.emb_typ_to_string et
                       in
                    let uu____57275 = FStar_Syntax_Print.term_to_string x1
                       in
                    let uu____57277 =
                      match aopt with
                      | FStar_Pervasives_Native.None  -> "None"
                      | FStar_Pervasives_Native.Some a ->
                          let uu____57282 = pa a  in
                          Prims.op_Hat "Some " uu____57282
                       in
                    FStar_Util.print3
                      "Unembedding:\n\temb_typ=%s\n\tterm is %s\n\tvalue is %s\n"
                      uu____57273 uu____57275 uu____57277
                  else ());
                 aopt)
  
let (mk_any_emb :
  FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term embedding) =
  fun typ  ->
    let em t _r _topt _norm =
      (let uu____57362 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
       if uu____57362
       then
         let uu____57386 = unknown_printer typ t  in
         FStar_Util.print1 "Embedding abstract: %s\n" uu____57386
       else ());
      t  in
    let un t _w _n =
      (let uu____57416 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
       if uu____57416
       then
         let uu____57440 = unknown_printer typ t  in
         FStar_Util.print1 "Unembedding abstract: %s\n" uu____57440
       else ());
      FStar_Pervasives_Native.Some t  in
    mk_emb_full em un typ (unknown_printer typ)
      FStar_Syntax_Syntax.ET_abstract
  
let (e_any : FStar_Syntax_Syntax.term embedding) =
  let em t _r _topt _norm = t  in
  let un t _w _n = FStar_Pervasives_Native.Some t  in
  let uu____57535 =
    let uu____57536 =
      let uu____57544 =
        FStar_All.pipe_right FStar_Parser_Const.term_lid
          FStar_Ident.string_of_lid
         in
      (uu____57544, [])  in
    FStar_Syntax_Syntax.ET_app uu____57536  in
  mk_emb_full em un FStar_Syntax_Syntax.t_term
    FStar_Syntax_Print.term_to_string uu____57535
  
let (e_unit : unit embedding) =
  let em u rng _topt _norm =
    let uu___582_57616 = FStar_Syntax_Util.exp_unit  in
    {
      FStar_Syntax_Syntax.n = (uu___582_57616.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___582_57616.FStar_Syntax_Syntax.vars)
    }  in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unascribe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit ) ->
        FStar_Pervasives_Native.Some ()
    | uu____57646 ->
        (if w
         then
           (let uu____57649 =
              let uu____57655 =
                let uu____57657 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded unit: %s" uu____57657  in
              (FStar_Errors.Warning_NotEmbedded, uu____57655)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____57649)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____57663 =
    let uu____57664 =
      let uu____57672 =
        FStar_All.pipe_right FStar_Parser_Const.unit_lid
          FStar_Ident.string_of_lid
         in
      (uu____57672, [])  in
    FStar_Syntax_Syntax.ET_app uu____57664  in
  mk_emb_full em un FStar_Syntax_Syntax.t_unit (fun uu____57679  -> "()")
    uu____57663
  
let (e_bool : Prims.bool embedding) =
  let em b rng _topt _norm =
    let t =
      if b
      then FStar_Syntax_Util.exp_true_bool
      else FStar_Syntax_Util.exp_false_bool  in
    let uu___602_57758 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___602_57758.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___602_57758.FStar_Syntax_Syntax.vars)
    }  in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) ->
        FStar_Pervasives_Native.Some b
    | uu____57796 ->
        (if w
         then
           (let uu____57799 =
              let uu____57805 =
                let uu____57807 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded bool: %s" uu____57807  in
              (FStar_Errors.Warning_NotEmbedded, uu____57805)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____57799)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____57814 =
    let uu____57815 =
      let uu____57823 =
        FStar_All.pipe_right FStar_Parser_Const.bool_lid
          FStar_Ident.string_of_lid
         in
      (uu____57823, [])  in
    FStar_Syntax_Syntax.ET_app uu____57815  in
  mk_emb_full em un FStar_Syntax_Syntax.t_bool FStar_Util.string_of_bool
    uu____57814
  
let (e_char : FStar_Char.char embedding) =
  let em c rng _topt _norm =
    let t = FStar_Syntax_Util.exp_char c  in
    let uu___621_57900 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___621_57900.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___621_57900.FStar_Syntax_Syntax.vars)
    }  in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c) ->
        FStar_Pervasives_Native.Some c
    | uu____57936 ->
        (if w
         then
           (let uu____57939 =
              let uu____57945 =
                let uu____57947 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded char: %s" uu____57947  in
              (FStar_Errors.Warning_NotEmbedded, uu____57945)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____57939)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____57954 =
    let uu____57955 =
      let uu____57963 =
        FStar_All.pipe_right FStar_Parser_Const.char_lid
          FStar_Ident.string_of_lid
         in
      (uu____57963, [])  in
    FStar_Syntax_Syntax.ET_app uu____57955  in
  mk_emb_full em un FStar_Syntax_Syntax.t_char FStar_Util.string_of_char
    uu____57954
  
let (e_int : FStar_BigInt.t embedding) =
  let t_int1 = FStar_Syntax_Util.fvar_const FStar_Parser_Const.int_lid  in
  let emb_t_int =
    let uu____57975 =
      let uu____57983 =
        FStar_All.pipe_right FStar_Parser_Const.int_lid
          FStar_Ident.string_of_lid
         in
      (uu____57983, [])  in
    FStar_Syntax_Syntax.ET_app uu____57975  in
  let em i rng _topt _norm =
    lazy_embed FStar_BigInt.string_of_big_int emb_t_int rng t_int1 i
      (fun uu____58054  ->
         let uu____58055 = FStar_BigInt.string_of_big_int i  in
         FStar_Syntax_Util.exp_int uu____58055)
     in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    lazy_unembed FStar_BigInt.string_of_big_int emb_t_int t t_int1
      (fun t1  ->
         match t1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
             (s,uu____58092)) ->
             let uu____58107 = FStar_BigInt.big_int_of_string s  in
             FStar_Pervasives_Native.Some uu____58107
         | uu____58108 ->
             (if w
              then
                (let uu____58111 =
                   let uu____58117 =
                     let uu____58119 = FStar_Syntax_Print.term_to_string t0
                        in
                     FStar_Util.format1 "Not an embedded int: %s" uu____58119
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____58117)  in
                 FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                   uu____58111)
              else ();
              FStar_Pervasives_Native.None))
     in
  mk_emb_full em un FStar_Syntax_Syntax.t_int FStar_BigInt.string_of_big_int
    emb_t_int
  
let (e_string : Prims.string embedding) =
  let emb_t_string =
    let uu____58130 =
      let uu____58138 =
        FStar_All.pipe_right FStar_Parser_Const.string_lid
          FStar_Ident.string_of_lid
         in
      (uu____58138, [])  in
    FStar_Syntax_Syntax.ET_app uu____58130  in
  let em s rng _topt _norm =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, rng)))
      FStar_Pervasives_Native.None rng
     in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
        (s,uu____58243)) -> FStar_Pervasives_Native.Some s
    | uu____58247 ->
        (if w
         then
           (let uu____58250 =
              let uu____58256 =
                let uu____58258 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded string: %s" uu____58258
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____58256)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____58250)
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
      let uu____58294 =
        let uu____58299 =
          let uu____58300 = FStar_Syntax_Syntax.as_arg ea.typ  in
          [uu____58300]  in
        FStar_Syntax_Syntax.mk_Tm_app t_opt uu____58299  in
      uu____58294 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
    let emb_t_option_a =
      let uu____58328 =
        let uu____58336 =
          FStar_All.pipe_right FStar_Parser_Const.option_lid
            FStar_Ident.string_of_lid
           in
        (uu____58336, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____58328  in
    let printer uu___430_58350 =
      match uu___430_58350 with
      | FStar_Pervasives_Native.None  -> "None"
      | FStar_Pervasives_Native.Some x ->
          let uu____58356 =
            let uu____58358 = ea.print x  in Prims.op_Hat uu____58358 ")"  in
          Prims.op_Hat "(Some " uu____58356
       in
    let em o rng topt norm1 =
      lazy_embed printer emb_t_option_a rng t_option_a o
        (fun uu____58435  ->
           match o with
           | FStar_Pervasives_Native.None  ->
               let uu____58436 =
                 let uu____58441 =
                   let uu____58442 =
                     FStar_Syntax_Syntax.tdataconstr
                       FStar_Parser_Const.none_lid
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____58442
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 let uu____58443 =
                   let uu____58444 =
                     let uu____58453 = type_of ea  in
                     FStar_Syntax_Syntax.iarg uu____58453  in
                   [uu____58444]  in
                 FStar_Syntax_Syntax.mk_Tm_app uu____58441 uu____58443  in
               uu____58436 FStar_Pervasives_Native.None rng
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
                        let uu____58544 =
                          FStar_Syntax_Syntax.lid_as_fv some_v
                            FStar_Syntax_Syntax.delta_equational
                            FStar_Pervasives_Native.None
                           in
                        FStar_Syntax_Syntax.fv_to_tm uu____58544  in
                      let uu____58545 =
                        let uu____58550 =
                          FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm
                            [FStar_Syntax_Syntax.U_zero]
                           in
                        let uu____58551 =
                          let uu____58552 =
                            let uu____58561 = type_of ea  in
                            FStar_Syntax_Syntax.iarg uu____58561  in
                          let uu____58562 =
                            let uu____58573 = FStar_Syntax_Syntax.as_arg t
                               in
                            [uu____58573]  in
                          uu____58552 :: uu____58562  in
                        FStar_Syntax_Syntax.mk_Tm_app uu____58550 uu____58551
                         in
                      uu____58545 FStar_Pervasives_Native.None rng)
                  in
               let uu____58608 =
                 let uu____58613 =
                   let uu____58614 =
                     FStar_Syntax_Syntax.tdataconstr
                       FStar_Parser_Const.some_lid
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____58614
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 let uu____58615 =
                   let uu____58616 =
                     let uu____58625 = type_of ea  in
                     FStar_Syntax_Syntax.iarg uu____58625  in
                   let uu____58626 =
                     let uu____58637 =
                       let uu____58646 =
                         let uu____58647 = embed ea a  in
                         uu____58647 rng shadow_a norm1  in
                       FStar_Syntax_Syntax.as_arg uu____58646  in
                     [uu____58637]  in
                   uu____58616 :: uu____58626  in
                 FStar_Syntax_Syntax.mk_Tm_app uu____58613 uu____58615  in
               uu____58608 FStar_Pervasives_Native.None rng)
       in
    let un t0 w norm1 =
      let t = FStar_Syntax_Util.unmeta_safe t0  in
      lazy_unembed printer emb_t_option_a t t_option_a
        (fun t1  ->
           let uu____58784 = FStar_Syntax_Util.head_and_args' t1  in
           match uu____58784 with
           | (hd1,args) ->
               let uu____58825 =
                 let uu____58840 =
                   let uu____58841 = FStar_Syntax_Util.un_uinst hd1  in
                   uu____58841.FStar_Syntax_Syntax.n  in
                 (uu____58840, args)  in
               (match uu____58825 with
                | (FStar_Syntax_Syntax.Tm_fvar fv,uu____58859) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.none_lid
                    ->
                    FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,uu____58883::(a,uu____58885)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.some_lid
                    ->
                    let uu____58936 =
                      let uu____58939 = unembed ea a  in uu____58939 w norm1
                       in
                    FStar_Util.bind_opt uu____58936
                      (fun a1  ->
                         FStar_Pervasives_Native.Some
                           (FStar_Pervasives_Native.Some a1))
                | uu____58958 ->
                    (if w
                     then
                       (let uu____58975 =
                          let uu____58981 =
                            let uu____58983 =
                              FStar_Syntax_Print.term_to_string t0  in
                            FStar_Util.format1 "Not an embedded option: %s"
                              uu____58983
                             in
                          (FStar_Errors.Warning_NotEmbedded, uu____58981)  in
                        FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                          uu____58975)
                     else ();
                     FStar_Pervasives_Native.None)))
       in
    let uu____58991 =
      let uu____58992 = type_of ea  in
      FStar_Syntax_Syntax.t_option_of uu____58992  in
    mk_emb_full em un uu____58991 printer emb_t_option_a
  
let e_tuple2 : 'a 'b . 'a embedding -> 'b embedding -> ('a * 'b) embedding =
  fun ea  ->
    fun eb  ->
      let t_pair_a_b =
        let t_tup2 =
          FStar_Syntax_Util.fvar_const FStar_Parser_Const.lid_tuple2  in
        let uu____59034 =
          let uu____59039 =
            let uu____59040 = FStar_Syntax_Syntax.as_arg ea.typ  in
            let uu____59049 =
              let uu____59060 = FStar_Syntax_Syntax.as_arg eb.typ  in
              [uu____59060]  in
            uu____59040 :: uu____59049  in
          FStar_Syntax_Syntax.mk_Tm_app t_tup2 uu____59039  in
        uu____59034 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
      let emb_t_pair_a_b =
        let uu____59096 =
          let uu____59104 =
            FStar_All.pipe_right FStar_Parser_Const.lid_tuple2
              FStar_Ident.string_of_lid
             in
          (uu____59104, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____59096  in
      let printer uu____59120 =
        match uu____59120 with
        | (x,y) ->
            let uu____59128 = ea.print x  in
            let uu____59130 = eb.print y  in
            FStar_Util.format2 "(%s, %s)" uu____59128 uu____59130
         in
      let em x rng topt norm1 =
        lazy_embed printer emb_t_pair_a_b rng t_pair_a_b x
          (fun uu____59215  ->
             let proj i ab =
               let uu____59231 =
                 let uu____59236 =
                   FStar_Parser_Const.mk_tuple_data_lid (Prims.parse_int "2")
                     rng
                    in
                 let uu____59238 =
                   FStar_Syntax_Syntax.null_bv FStar_Syntax_Syntax.tun  in
                 FStar_Syntax_Util.mk_field_projector_name uu____59236
                   uu____59238 i
                  in
               match uu____59231 with
               | (proj_1,uu____59242) ->
                   let proj_1_tm =
                     let uu____59244 =
                       FStar_Syntax_Syntax.lid_as_fv proj_1
                         FStar_Syntax_Syntax.delta_equational
                         FStar_Pervasives_Native.None
                        in
                     FStar_Syntax_Syntax.fv_to_tm uu____59244  in
                   let uu____59245 =
                     let uu____59250 =
                       FStar_Syntax_Syntax.mk_Tm_uinst proj_1_tm
                         [FStar_Syntax_Syntax.U_zero]
                        in
                     let uu____59251 =
                       let uu____59252 =
                         let uu____59261 = type_of ea  in
                         FStar_Syntax_Syntax.iarg uu____59261  in
                       let uu____59262 =
                         let uu____59273 =
                           let uu____59282 = type_of eb  in
                           FStar_Syntax_Syntax.iarg uu____59282  in
                         let uu____59283 =
                           let uu____59294 = FStar_Syntax_Syntax.as_arg ab
                              in
                           [uu____59294]  in
                         uu____59273 :: uu____59283  in
                       uu____59252 :: uu____59262  in
                     FStar_Syntax_Syntax.mk_Tm_app uu____59250 uu____59251
                      in
                   uu____59245 FStar_Pervasives_Native.None rng
                in
             let shadow_a = map_shadow topt (proj (Prims.parse_int "1"))  in
             let shadow_b = map_shadow topt (proj (Prims.parse_int "2"))  in
             let uu____59455 =
               let uu____59460 =
                 let uu____59461 =
                   FStar_Syntax_Syntax.tdataconstr
                     FStar_Parser_Const.lid_Mktuple2
                    in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu____59461
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                  in
               let uu____59462 =
                 let uu____59463 =
                   let uu____59472 = type_of ea  in
                   FStar_Syntax_Syntax.iarg uu____59472  in
                 let uu____59473 =
                   let uu____59484 =
                     let uu____59493 = type_of eb  in
                     FStar_Syntax_Syntax.iarg uu____59493  in
                   let uu____59494 =
                     let uu____59505 =
                       let uu____59514 =
                         let uu____59515 =
                           embed ea (FStar_Pervasives_Native.fst x)  in
                         uu____59515 rng shadow_a norm1  in
                       FStar_Syntax_Syntax.as_arg uu____59514  in
                     let uu____59585 =
                       let uu____59596 =
                         let uu____59605 =
                           let uu____59606 =
                             embed eb (FStar_Pervasives_Native.snd x)  in
                           uu____59606 rng shadow_b norm1  in
                         FStar_Syntax_Syntax.as_arg uu____59605  in
                       [uu____59596]  in
                     uu____59505 :: uu____59585  in
                   uu____59484 :: uu____59494  in
                 uu____59463 :: uu____59473  in
               FStar_Syntax_Syntax.mk_Tm_app uu____59460 uu____59462  in
             uu____59455 FStar_Pervasives_Native.None rng)
         in
      let un t0 w norm1 =
        let t = FStar_Syntax_Util.unmeta_safe t0  in
        lazy_unembed printer emb_t_pair_a_b t t_pair_a_b
          (fun t1  ->
             let uu____59771 = FStar_Syntax_Util.head_and_args' t1  in
             match uu____59771 with
             | (hd1,args) ->
                 let uu____59814 =
                   let uu____59827 =
                     let uu____59828 = FStar_Syntax_Util.un_uinst hd1  in
                     uu____59828.FStar_Syntax_Syntax.n  in
                   (uu____59827, args)  in
                 (match uu____59814 with
                  | (FStar_Syntax_Syntax.Tm_fvar
                     fv,uu____59846::uu____59847::(a,uu____59849)::(b,uu____59851)::[])
                      when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.lid_Mktuple2
                      ->
                      let uu____59910 =
                        let uu____59913 = unembed ea a  in
                        uu____59913 w norm1  in
                      FStar_Util.bind_opt uu____59910
                        (fun a1  ->
                           let uu____59933 =
                             let uu____59936 = unembed eb b  in
                             uu____59936 w norm1  in
                           FStar_Util.bind_opt uu____59933
                             (fun b1  ->
                                FStar_Pervasives_Native.Some (a1, b1)))
                  | uu____59959 ->
                      (if w
                       then
                         (let uu____59974 =
                            let uu____59980 =
                              let uu____59982 =
                                FStar_Syntax_Print.term_to_string t0  in
                              FStar_Util.format1 "Not an embedded pair: %s"
                                uu____59982
                               in
                            (FStar_Errors.Warning_NotEmbedded, uu____59980)
                             in
                          FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                            uu____59974)
                       else ();
                       FStar_Pervasives_Native.None)))
         in
      let uu____59992 =
        let uu____59993 = type_of ea  in
        let uu____59994 = type_of eb  in
        FStar_Syntax_Syntax.t_tuple2_of uu____59993 uu____59994  in
      mk_emb_full em un uu____59992 printer emb_t_pair_a_b
  
let e_either :
  'a 'b . 'a embedding -> 'b embedding -> ('a,'b) FStar_Util.either embedding
  =
  fun ea  ->
    fun eb  ->
      let t_sum_a_b =
        let t_either =
          FStar_Syntax_Util.fvar_const FStar_Parser_Const.either_lid  in
        let uu____60038 =
          let uu____60043 =
            let uu____60044 = FStar_Syntax_Syntax.as_arg ea.typ  in
            let uu____60053 =
              let uu____60064 = FStar_Syntax_Syntax.as_arg eb.typ  in
              [uu____60064]  in
            uu____60044 :: uu____60053  in
          FStar_Syntax_Syntax.mk_Tm_app t_either uu____60043  in
        uu____60038 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
      let emb_t_sum_a_b =
        let uu____60100 =
          let uu____60108 =
            FStar_All.pipe_right FStar_Parser_Const.either_lid
              FStar_Ident.string_of_lid
             in
          (uu____60108, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____60100  in
      let printer s =
        match s with
        | FStar_Util.Inl a ->
            let uu____60131 = ea.print a  in
            FStar_Util.format1 "Inl %s" uu____60131
        | FStar_Util.Inr b ->
            let uu____60135 = eb.print b  in
            FStar_Util.format1 "Inr %s" uu____60135
         in
      let em s rng topt norm1 =
        lazy_embed printer emb_t_sum_a_b rng t_sum_a_b s
          (match s with
           | FStar_Util.Inl a ->
               (fun uu____60223  ->
                  let shadow_a =
                    map_shadow topt
                      (fun t  ->
                         let v1 = FStar_Ident.mk_ident ("v", rng)  in
                         let some_v =
                           FStar_Syntax_Util.mk_field_projector_name_from_ident
                             FStar_Parser_Const.inl_lid v1
                            in
                         let some_v_tm =
                           let uu____60295 =
                             FStar_Syntax_Syntax.lid_as_fv some_v
                               FStar_Syntax_Syntax.delta_equational
                               FStar_Pervasives_Native.None
                              in
                           FStar_Syntax_Syntax.fv_to_tm uu____60295  in
                         let uu____60296 =
                           let uu____60301 =
                             FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm
                               [FStar_Syntax_Syntax.U_zero]
                              in
                           let uu____60302 =
                             let uu____60303 =
                               let uu____60312 = type_of ea  in
                               FStar_Syntax_Syntax.iarg uu____60312  in
                             let uu____60313 =
                               let uu____60324 =
                                 let uu____60333 = type_of eb  in
                                 FStar_Syntax_Syntax.iarg uu____60333  in
                               let uu____60334 =
                                 let uu____60345 =
                                   FStar_Syntax_Syntax.as_arg t  in
                                 [uu____60345]  in
                               uu____60324 :: uu____60334  in
                             uu____60303 :: uu____60313  in
                           FStar_Syntax_Syntax.mk_Tm_app uu____60301
                             uu____60302
                            in
                         uu____60296 FStar_Pervasives_Native.None rng)
                     in
                  let uu____60388 =
                    let uu____60393 =
                      let uu____60394 =
                        FStar_Syntax_Syntax.tdataconstr
                          FStar_Parser_Const.inl_lid
                         in
                      FStar_Syntax_Syntax.mk_Tm_uinst uu____60394
                        [FStar_Syntax_Syntax.U_zero;
                        FStar_Syntax_Syntax.U_zero]
                       in
                    let uu____60395 =
                      let uu____60396 =
                        let uu____60405 = type_of ea  in
                        FStar_Syntax_Syntax.iarg uu____60405  in
                      let uu____60406 =
                        let uu____60417 =
                          let uu____60426 = type_of eb  in
                          FStar_Syntax_Syntax.iarg uu____60426  in
                        let uu____60427 =
                          let uu____60438 =
                            let uu____60447 =
                              let uu____60448 = embed ea a  in
                              uu____60448 rng shadow_a norm1  in
                            FStar_Syntax_Syntax.as_arg uu____60447  in
                          [uu____60438]  in
                        uu____60417 :: uu____60427  in
                      uu____60396 :: uu____60406  in
                    FStar_Syntax_Syntax.mk_Tm_app uu____60393 uu____60395  in
                  uu____60388 FStar_Pervasives_Native.None rng)
           | FStar_Util.Inr b ->
               (fun uu____60553  ->
                  let shadow_b =
                    map_shadow topt
                      (fun t  ->
                         let v1 = FStar_Ident.mk_ident ("v", rng)  in
                         let some_v =
                           FStar_Syntax_Util.mk_field_projector_name_from_ident
                             FStar_Parser_Const.inr_lid v1
                            in
                         let some_v_tm =
                           let uu____60625 =
                             FStar_Syntax_Syntax.lid_as_fv some_v
                               FStar_Syntax_Syntax.delta_equational
                               FStar_Pervasives_Native.None
                              in
                           FStar_Syntax_Syntax.fv_to_tm uu____60625  in
                         let uu____60626 =
                           let uu____60631 =
                             FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm
                               [FStar_Syntax_Syntax.U_zero]
                              in
                           let uu____60632 =
                             let uu____60633 =
                               let uu____60642 = type_of ea  in
                               FStar_Syntax_Syntax.iarg uu____60642  in
                             let uu____60643 =
                               let uu____60654 =
                                 let uu____60663 = type_of eb  in
                                 FStar_Syntax_Syntax.iarg uu____60663  in
                               let uu____60664 =
                                 let uu____60675 =
                                   FStar_Syntax_Syntax.as_arg t  in
                                 [uu____60675]  in
                               uu____60654 :: uu____60664  in
                             uu____60633 :: uu____60643  in
                           FStar_Syntax_Syntax.mk_Tm_app uu____60631
                             uu____60632
                            in
                         uu____60626 FStar_Pervasives_Native.None rng)
                     in
                  let uu____60718 =
                    let uu____60723 =
                      let uu____60724 =
                        FStar_Syntax_Syntax.tdataconstr
                          FStar_Parser_Const.inr_lid
                         in
                      FStar_Syntax_Syntax.mk_Tm_uinst uu____60724
                        [FStar_Syntax_Syntax.U_zero;
                        FStar_Syntax_Syntax.U_zero]
                       in
                    let uu____60725 =
                      let uu____60726 =
                        let uu____60735 = type_of ea  in
                        FStar_Syntax_Syntax.iarg uu____60735  in
                      let uu____60736 =
                        let uu____60747 =
                          let uu____60756 = type_of eb  in
                          FStar_Syntax_Syntax.iarg uu____60756  in
                        let uu____60757 =
                          let uu____60768 =
                            let uu____60777 =
                              let uu____60778 = embed eb b  in
                              uu____60778 rng shadow_b norm1  in
                            FStar_Syntax_Syntax.as_arg uu____60777  in
                          [uu____60768]  in
                        uu____60747 :: uu____60757  in
                      uu____60726 :: uu____60736  in
                    FStar_Syntax_Syntax.mk_Tm_app uu____60723 uu____60725  in
                  uu____60718 FStar_Pervasives_Native.None rng))
         in
      let un t0 w norm1 =
        let t = FStar_Syntax_Util.unmeta_safe t0  in
        lazy_unembed printer emb_t_sum_a_b t t_sum_a_b
          (fun t1  ->
             let uu____60933 = FStar_Syntax_Util.head_and_args' t1  in
             match uu____60933 with
             | (hd1,args) ->
                 let uu____60976 =
                   let uu____60991 =
                     let uu____60992 = FStar_Syntax_Util.un_uinst hd1  in
                     uu____60992.FStar_Syntax_Syntax.n  in
                   (uu____60991, args)  in
                 (match uu____60976 with
                  | (FStar_Syntax_Syntax.Tm_fvar
                     fv,uu____61012::uu____61013::(a,uu____61015)::[]) when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.inl_lid
                      ->
                      let uu____61082 =
                        let uu____61085 = unembed ea a  in
                        uu____61085 w norm1  in
                      FStar_Util.bind_opt uu____61082
                        (fun a1  ->
                           FStar_Pervasives_Native.Some (FStar_Util.Inl a1))
                  | (FStar_Syntax_Syntax.Tm_fvar
                     fv,uu____61109::uu____61110::(b,uu____61112)::[]) when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.inr_lid
                      ->
                      let uu____61179 =
                        let uu____61182 = unembed eb b  in
                        uu____61182 w norm1  in
                      FStar_Util.bind_opt uu____61179
                        (fun b1  ->
                           FStar_Pervasives_Native.Some (FStar_Util.Inr b1))
                  | uu____61205 ->
                      (if w
                       then
                         (let uu____61222 =
                            let uu____61228 =
                              let uu____61230 =
                                FStar_Syntax_Print.term_to_string t0  in
                              FStar_Util.format1 "Not an embedded sum: %s"
                                uu____61230
                               in
                            (FStar_Errors.Warning_NotEmbedded, uu____61228)
                             in
                          FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                            uu____61222)
                       else ();
                       FStar_Pervasives_Native.None)))
         in
      let uu____61240 =
        let uu____61241 = type_of ea  in
        let uu____61242 = type_of eb  in
        FStar_Syntax_Syntax.t_either_of uu____61241 uu____61242  in
      mk_emb_full em un uu____61240 printer emb_t_sum_a_b
  
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea  ->
    let t_list_a =
      let t_list = FStar_Syntax_Util.fvar_const FStar_Parser_Const.list_lid
         in
      let uu____61270 =
        let uu____61275 =
          let uu____61276 = FStar_Syntax_Syntax.as_arg ea.typ  in
          [uu____61276]  in
        FStar_Syntax_Syntax.mk_Tm_app t_list uu____61275  in
      uu____61270 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
    let emb_t_list_a =
      let uu____61304 =
        let uu____61312 =
          FStar_All.pipe_right FStar_Parser_Const.list_lid
            FStar_Ident.string_of_lid
           in
        (uu____61312, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____61304  in
    let printer l =
      let uu____61329 =
        let uu____61331 =
          let uu____61333 = FStar_List.map ea.print l  in
          FStar_All.pipe_right uu____61333 (FStar_String.concat "; ")  in
        Prims.op_Hat uu____61331 "]"  in
      Prims.op_Hat "[" uu____61329  in
    let rec em l rng shadow_l norm1 =
      lazy_embed printer emb_t_list_a rng t_list_a l
        (fun uu____61419  ->
           let t =
             let uu____61421 = type_of ea  in
             FStar_Syntax_Syntax.iarg uu____61421  in
           match l with
           | [] ->
               let uu____61422 =
                 let uu____61427 =
                   let uu____61428 =
                     FStar_Syntax_Syntax.tdataconstr
                       FStar_Parser_Const.nil_lid
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____61428
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 FStar_Syntax_Syntax.mk_Tm_app uu____61427 [t]  in
               uu____61422 FStar_Pervasives_Native.None rng
           | hd1::tl1 ->
               let cons1 =
                 let uu____61452 =
                   FStar_Syntax_Syntax.tdataconstr
                     FStar_Parser_Const.cons_lid
                    in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu____61452
                   [FStar_Syntax_Syntax.U_zero]
                  in
               let proj f cons_tm =
                 let fid = FStar_Ident.mk_ident (f, rng)  in
                 let proj =
                   FStar_Syntax_Util.mk_field_projector_name_from_ident
                     FStar_Parser_Const.cons_lid fid
                    in
                 let proj_tm =
                   let uu____61472 =
                     FStar_Syntax_Syntax.lid_as_fv proj
                       FStar_Syntax_Syntax.delta_equational
                       FStar_Pervasives_Native.None
                      in
                   FStar_Syntax_Syntax.fv_to_tm uu____61472  in
                 let uu____61473 =
                   let uu____61478 =
                     FStar_Syntax_Syntax.mk_Tm_uinst proj_tm
                       [FStar_Syntax_Syntax.U_zero]
                      in
                   let uu____61479 =
                     let uu____61480 =
                       let uu____61489 = type_of ea  in
                       FStar_Syntax_Syntax.iarg uu____61489  in
                     let uu____61490 =
                       let uu____61501 = FStar_Syntax_Syntax.as_arg cons_tm
                          in
                       [uu____61501]  in
                     uu____61480 :: uu____61490  in
                   FStar_Syntax_Syntax.mk_Tm_app uu____61478 uu____61479  in
                 uu____61473 FStar_Pervasives_Native.None rng  in
               let shadow_hd = map_shadow shadow_l (proj "hd")  in
               let shadow_tl = map_shadow shadow_l (proj "tl")  in
               let uu____61654 =
                 let uu____61659 =
                   let uu____61660 =
                     let uu____61671 =
                       let uu____61680 =
                         let uu____61681 = embed ea hd1  in
                         uu____61681 rng shadow_hd norm1  in
                       FStar_Syntax_Syntax.as_arg uu____61680  in
                     let uu____61751 =
                       let uu____61762 =
                         let uu____61771 = em tl1 rng shadow_tl norm1  in
                         FStar_Syntax_Syntax.as_arg uu____61771  in
                       [uu____61762]  in
                     uu____61671 :: uu____61751  in
                   t :: uu____61660  in
                 FStar_Syntax_Syntax.mk_Tm_app cons1 uu____61659  in
               uu____61654 FStar_Pervasives_Native.None rng)
       in
    let rec un t0 w norm1 =
      let t = FStar_Syntax_Util.unmeta_safe t0  in
      lazy_unembed printer emb_t_list_a t t_list_a
        (fun t1  ->
           let uu____61887 = FStar_Syntax_Util.head_and_args' t1  in
           match uu____61887 with
           | (hd1,args) ->
               let uu____61928 =
                 let uu____61941 =
                   let uu____61942 = FStar_Syntax_Util.un_uinst hd1  in
                   uu____61942.FStar_Syntax_Syntax.n  in
                 (uu____61941, args)  in
               (match uu____61928 with
                | (FStar_Syntax_Syntax.Tm_fvar fv,uu____61958) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.nil_lid
                    -> FStar_Pervasives_Native.Some []
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(uu____61978,FStar_Pervasives_Native.Some
                       (FStar_Syntax_Syntax.Implicit uu____61979))::(hd2,FStar_Pervasives_Native.None
                                                                    )::
                   (tl1,FStar_Pervasives_Native.None )::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.cons_lid
                    ->
                    let uu____62021 =
                      let uu____62024 = unembed ea hd2  in
                      uu____62024 w norm1  in
                    FStar_Util.bind_opt uu____62021
                      (fun hd3  ->
                         let uu____62042 = un tl1 w norm1  in
                         FStar_Util.bind_opt uu____62042
                           (fun tl2  ->
                              FStar_Pervasives_Native.Some (hd3 :: tl2)))
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(hd2,FStar_Pervasives_Native.None )::(tl1,FStar_Pervasives_Native.None
                                                            )::[])
                    when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.cons_lid
                    ->
                    let uu____62092 =
                      let uu____62095 = unembed ea hd2  in
                      uu____62095 w norm1  in
                    FStar_Util.bind_opt uu____62092
                      (fun hd3  ->
                         let uu____62113 = un tl1 w norm1  in
                         FStar_Util.bind_opt uu____62113
                           (fun tl2  ->
                              FStar_Pervasives_Native.Some (hd3 :: tl2)))
                | uu____62130 ->
                    (if w
                     then
                       (let uu____62145 =
                          let uu____62151 =
                            let uu____62153 =
                              FStar_Syntax_Print.term_to_string t0  in
                            FStar_Util.format1 "Not an embedded list: %s"
                              uu____62153
                             in
                          (FStar_Errors.Warning_NotEmbedded, uu____62151)  in
                        FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                          uu____62145)
                     else ();
                     FStar_Pervasives_Native.None)))
       in
    let uu____62161 =
      let uu____62162 = type_of ea  in
      FStar_Syntax_Syntax.t_list_of uu____62162  in
    mk_emb_full em un uu____62161 printer emb_t_list_a
  
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
    match projectee with | Simpl  -> true | uu____62205 -> false
  
let (uu___is_Weak : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Weak  -> true | uu____62216 -> false
  
let (uu___is_HNF : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | HNF  -> true | uu____62227 -> false
  
let (uu___is_Primops : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____62238 -> false
  
let (uu___is_Delta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Delta  -> true | uu____62249 -> false
  
let (uu___is_Zeta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Zeta  -> true | uu____62260 -> false
  
let (uu___is_Iota : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Iota  -> true | uu____62271 -> false
  
let (uu___is_Reify : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____62282 -> false
  
let (uu___is_UnfoldOnly : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____62297 -> false
  
let (__proj__UnfoldOnly__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldFully : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldFully _0 -> true | uu____62329 -> false
  
let (__proj__UnfoldFully__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldFully _0 -> _0 
let (uu___is_UnfoldAttr : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____62361 -> false
  
let (__proj__UnfoldAttr__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_NBE : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | NBE  -> true | uu____62389 -> false
  
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
    let uu____62407 =
      FStar_Ident.lid_of_str "FStar.Syntax.Embeddings.norm_step"  in
    FStar_Syntax_Util.fvar_const uu____62407  in
  let emb_t_norm_step =
    let uu____62410 =
      let uu____62418 =
        FStar_All.pipe_right FStar_Parser_Const.norm_step_lid
          FStar_Ident.string_of_lid
         in
      (uu____62418, [])  in
    FStar_Syntax_Syntax.ET_app uu____62410  in
  let printer uu____62430 = "norm_step"  in
  let em n1 rng _topt norm1 =
    lazy_embed printer emb_t_norm_step rng t_norm_step1 n1
      (fun uu____62496  ->
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
             let uu____62501 =
               let uu____62506 =
                 let uu____62507 =
                   let uu____62516 =
                     let uu____62517 =
                       let uu____62524 = e_list e_string  in
                       embed uu____62524 l  in
                     uu____62517 rng FStar_Pervasives_Native.None norm1  in
                   FStar_Syntax_Syntax.as_arg uu____62516  in
                 [uu____62507]  in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldOnly uu____62506  in
             uu____62501 FStar_Pervasives_Native.None rng
         | UnfoldFully l ->
             let uu____62583 =
               let uu____62588 =
                 let uu____62589 =
                   let uu____62598 =
                     let uu____62599 =
                       let uu____62606 = e_list e_string  in
                       embed uu____62606 l  in
                     uu____62599 rng FStar_Pervasives_Native.None norm1  in
                   FStar_Syntax_Syntax.as_arg uu____62598  in
                 [uu____62589]  in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldFully uu____62588
                in
             uu____62583 FStar_Pervasives_Native.None rng
         | UnfoldAttr l ->
             let uu____62665 =
               let uu____62670 =
                 let uu____62671 =
                   let uu____62680 =
                     let uu____62681 =
                       let uu____62688 = e_list e_string  in
                       embed uu____62688 l  in
                     uu____62681 rng FStar_Pervasives_Native.None norm1  in
                   FStar_Syntax_Syntax.as_arg uu____62680  in
                 [uu____62671]  in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldAttr uu____62670  in
             uu____62665 FStar_Pervasives_Native.None rng)
     in
  let un t0 w norm1 =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    lazy_unembed printer emb_t_norm_step t t_norm_step1
      (fun t1  ->
         let uu____62777 = FStar_Syntax_Util.head_and_args t1  in
         match uu____62777 with
         | (hd1,args) ->
             let uu____62822 =
               let uu____62837 =
                 let uu____62838 = FStar_Syntax_Util.un_uinst hd1  in
                 uu____62838.FStar_Syntax_Syntax.n  in
               (uu____62837, args)  in
             (match uu____62822 with
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
              | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____63026)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldonly
                  ->
                  let uu____63061 =
                    let uu____63067 =
                      let uu____63077 = e_list e_string  in
                      unembed uu____63077 l  in
                    uu____63067 w norm1  in
                  FStar_Util.bind_opt uu____63061
                    (fun ss  ->
                       FStar_All.pipe_left
                         (fun _63103  -> FStar_Pervasives_Native.Some _63103)
                         (UnfoldOnly ss))
              | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____63106)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldfully
                  ->
                  let uu____63141 =
                    let uu____63147 =
                      let uu____63157 = e_list e_string  in
                      unembed uu____63157 l  in
                    uu____63147 w norm1  in
                  FStar_Util.bind_opt uu____63141
                    (fun ss  ->
                       FStar_All.pipe_left
                         (fun _63183  -> FStar_Pervasives_Native.Some _63183)
                         (UnfoldFully ss))
              | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____63186)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldattr
                  ->
                  let uu____63221 =
                    let uu____63227 =
                      let uu____63237 = e_list e_string  in
                      unembed uu____63237 l  in
                    uu____63227 w norm1  in
                  FStar_Util.bind_opt uu____63221
                    (fun ss  ->
                       FStar_All.pipe_left
                         (fun _63263  -> FStar_Pervasives_Native.Some _63263)
                         (UnfoldAttr ss))
              | uu____63264 ->
                  (if w
                   then
                     (let uu____63281 =
                        let uu____63287 =
                          let uu____63289 =
                            FStar_Syntax_Print.term_to_string t0  in
                          FStar_Util.format1 "Not an embedded norm_step: %s"
                            uu____63289
                           in
                        (FStar_Errors.Warning_NotEmbedded, uu____63287)  in
                      FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                        uu____63281)
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
    | uu____63391 ->
        (if w
         then
           (let uu____63394 =
              let uu____63400 =
                let uu____63402 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded range: %s" uu____63402
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____63400)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____63394)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____63408 =
    let uu____63409 =
      let uu____63417 =
        FStar_All.pipe_right FStar_Parser_Const.range_lid
          FStar_Ident.string_of_lid
         in
      (uu____63417, [])  in
    FStar_Syntax_Syntax.ET_app uu____63409  in
  mk_emb_full em un FStar_Syntax_Syntax.t_range FStar_Range.string_of_range
    uu____63408
  
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
        let uu____63488 =
          let uu____63495 =
            let uu____63496 =
              let uu____63511 =
                let uu____63520 =
                  let uu____63527 = FStar_Syntax_Syntax.null_bv ea.typ  in
                  (uu____63527, FStar_Pervasives_Native.None)  in
                [uu____63520]  in
              let uu____63542 = FStar_Syntax_Syntax.mk_Total eb.typ  in
              (uu____63511, uu____63542)  in
            FStar_Syntax_Syntax.Tm_arrow uu____63496  in
          FStar_Syntax_Syntax.mk uu____63495  in
        uu____63488 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
      let emb_t_arr_a_b =
        FStar_Syntax_Syntax.ET_fun ((ea.emb_typ), (eb.emb_typ))  in
      let printer f = "<fun>"  in
      let em f rng shadow_f norm1 =
        lazy_embed (fun uu____63655  -> "<fun>") emb_t_arr_a_b rng t_arrow f
          (fun uu____63661  ->
             let uu____63662 = force_shadow shadow_f  in
             match uu____63662 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Exn.raise Embedding_failure
             | FStar_Pervasives_Native.Some repr_f ->
                 ((let uu____63724 =
                     FStar_ST.op_Bang FStar_Options.debug_embedding  in
                   if uu____63724
                   then
                     let uu____63748 =
                       FStar_Syntax_Print.term_to_string repr_f  in
                     let uu____63750 = FStar_Util.stack_dump ()  in
                     FStar_Util.print2
                       "e_arrow forced back to term using shadow %s; repr=%s\n"
                       uu____63748 uu____63750
                   else ());
                  (let res = norm1 (FStar_Util.Inr repr_f)  in
                   (let uu____63757 =
                      FStar_ST.op_Bang FStar_Options.debug_embedding  in
                    if uu____63757
                    then
                      let uu____63781 =
                        FStar_Syntax_Print.term_to_string repr_f  in
                      let uu____63783 = FStar_Syntax_Print.term_to_string res
                         in
                      let uu____63785 = FStar_Util.stack_dump ()  in
                      FStar_Util.print3
                        "e_arrow forced back to term using shadow %s; repr=%s\n\t%s\n"
                        uu____63781 uu____63783 uu____63785
                    else ());
                   res)))
         in
      let un f w norm1 =
        lazy_unembed printer emb_t_arr_a_b f t_arrow
          (fun f1  ->
             let f_wrapped a =
               (let uu____63844 =
                  FStar_ST.op_Bang FStar_Options.debug_embedding  in
                if uu____63844
                then
                  let uu____63868 = FStar_Syntax_Print.term_to_string f1  in
                  let uu____63870 = FStar_Util.stack_dump ()  in
                  FStar_Util.print2
                    "Calling back into normalizer for %s\n%s\n" uu____63868
                    uu____63870
                else ());
               (let a_tm =
                  let uu____63876 = embed ea a  in
                  uu____63876 f1.FStar_Syntax_Syntax.pos
                    FStar_Pervasives_Native.None norm1
                   in
                let b_tm =
                  let uu____63909 =
                    let uu____63914 =
                      let uu____63915 =
                        let uu____63920 =
                          let uu____63921 = FStar_Syntax_Syntax.as_arg a_tm
                             in
                          [uu____63921]  in
                        FStar_Syntax_Syntax.mk_Tm_app f1 uu____63920  in
                      uu____63915 FStar_Pervasives_Native.None
                        f1.FStar_Syntax_Syntax.pos
                       in
                    FStar_Util.Inr uu____63914  in
                  norm1 uu____63909  in
                let uu____63948 =
                  let uu____63951 = unembed eb b_tm  in uu____63951 w norm1
                   in
                match uu____63948 with
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
                let uu____64051 = FStar_List.splitAt n_tvars args  in
                match uu____64051 with
                | (_tvar_args,rest_args) ->
                    let uu____64128 = FStar_List.hd rest_args  in
                    (match uu____64128 with
                     | (x,uu____64148) ->
                         let shadow_app =
                           let uu____64162 =
                             FStar_Common.mk_thunk
                               (fun uu____64171  ->
                                  let uu____64172 =
                                    let uu____64177 =
                                      norm1 (FStar_Util.Inl fv_lid1)  in
                                    FStar_Syntax_Syntax.mk_Tm_app uu____64177
                                      args
                                     in
                                  uu____64172 FStar_Pervasives_Native.None
                                    rng)
                              in
                           FStar_Pervasives_Native.Some uu____64162  in
                         let uu____64223 =
                           let uu____64226 =
                             let uu____64229 = unembed ea x  in
                             uu____64229 true norm1  in
                           FStar_Util.map_opt uu____64226
                             (fun x1  ->
                                let uu____64269 =
                                  let uu____64276 = f x1  in
                                  embed eb uu____64276  in
                                uu____64269 rng shadow_app norm1)
                            in
                         (match uu____64223 with
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
                  let uu____64406 = FStar_List.splitAt n_tvars args  in
                  match uu____64406 with
                  | (_tvar_args,rest_args) ->
                      let uu____64469 = FStar_List.hd rest_args  in
                      (match uu____64469 with
                       | (x,uu____64485) ->
                           let uu____64490 =
                             let uu____64497 = FStar_List.tl rest_args  in
                             FStar_List.hd uu____64497  in
                           (match uu____64490 with
                            | (y,uu____64521) ->
                                let shadow_app =
                                  let uu____64531 =
                                    FStar_Common.mk_thunk
                                      (fun uu____64540  ->
                                         let uu____64541 =
                                           let uu____64546 =
                                             norm1 (FStar_Util.Inl fv_lid1)
                                              in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____64546 args
                                            in
                                         uu____64541
                                           FStar_Pervasives_Native.None rng)
                                     in
                                  FStar_Pervasives_Native.Some uu____64531
                                   in
                                let uu____64592 =
                                  let uu____64595 =
                                    let uu____64598 = unembed ea x  in
                                    uu____64598 true norm1  in
                                  FStar_Util.bind_opt uu____64595
                                    (fun x1  ->
                                       let uu____64615 =
                                         let uu____64618 = unembed eb y  in
                                         uu____64618 true norm1  in
                                       FStar_Util.bind_opt uu____64615
                                         (fun y1  ->
                                            let uu____64635 =
                                              let uu____64636 =
                                                let uu____64643 = f x1 y1  in
                                                embed ec uu____64643  in
                                              uu____64636 rng shadow_app
                                                norm1
                                               in
                                            FStar_Pervasives_Native.Some
                                              uu____64635))
                                   in
                                (match uu____64592 with
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
                    let uu____64792 = FStar_List.splitAt n_tvars args  in
                    match uu____64792 with
                    | (_tvar_args,rest_args) ->
                        let uu____64855 = FStar_List.hd rest_args  in
                        (match uu____64855 with
                         | (x,uu____64871) ->
                             let uu____64876 =
                               let uu____64883 = FStar_List.tl rest_args  in
                               FStar_List.hd uu____64883  in
                             (match uu____64876 with
                              | (y,uu____64907) ->
                                  let uu____64912 =
                                    let uu____64919 =
                                      let uu____64928 =
                                        FStar_List.tl rest_args  in
                                      FStar_List.tl uu____64928  in
                                    FStar_List.hd uu____64919  in
                                  (match uu____64912 with
                                   | (z,uu____64958) ->
                                       let shadow_app =
                                         let uu____64968 =
                                           FStar_Common.mk_thunk
                                             (fun uu____64977  ->
                                                let uu____64978 =
                                                  let uu____64983 =
                                                    norm1
                                                      (FStar_Util.Inl fv_lid1)
                                                     in
                                                  FStar_Syntax_Syntax.mk_Tm_app
                                                    uu____64983 args
                                                   in
                                                uu____64978
                                                  FStar_Pervasives_Native.None
                                                  rng)
                                            in
                                         FStar_Pervasives_Native.Some
                                           uu____64968
                                          in
                                       let uu____65029 =
                                         let uu____65032 =
                                           let uu____65035 = unembed ea x  in
                                           uu____65035 true norm1  in
                                         FStar_Util.bind_opt uu____65032
                                           (fun x1  ->
                                              let uu____65052 =
                                                let uu____65055 =
                                                  unembed eb y  in
                                                uu____65055 true norm1  in
                                              FStar_Util.bind_opt uu____65052
                                                (fun y1  ->
                                                   let uu____65072 =
                                                     let uu____65075 =
                                                       unembed ec z  in
                                                     uu____65075 true norm1
                                                      in
                                                   FStar_Util.bind_opt
                                                     uu____65072
                                                     (fun z1  ->
                                                        let uu____65092 =
                                                          let uu____65093 =
                                                            let uu____65100 =
                                                              f x1 y1 z1  in
                                                            embed ed
                                                              uu____65100
                                                             in
                                                          uu____65093 rng
                                                            shadow_app norm1
                                                           in
                                                        FStar_Pervasives_Native.Some
                                                          uu____65092)))
                                          in
                                       (match uu____65029 with
                                        | FStar_Pervasives_Native.Some x1 ->
                                            FStar_Pervasives_Native.Some x1
                                        | FStar_Pervasives_Native.None  ->
                                            force_shadow shadow_app))))
                     in
                  f_wrapped
  
let debug_wrap : 'a . Prims.string -> (unit -> 'a) -> 'a =
  fun s  ->
    fun f  ->
      (let uu____65155 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
       if uu____65155 then FStar_Util.print1 "++++starting %s\n" s else ());
      (let res = f ()  in
       (let uu____65184 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
        if uu____65184 then FStar_Util.print1 "------ending %s\n" s else ());
       res)
  