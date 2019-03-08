open Prims
type norm_cb =
  (FStar_Ident.lid,FStar_Syntax_Syntax.term) FStar_Util.either ->
    FStar_Syntax_Syntax.term
let (id_norm_cb : norm_cb) =
  fun uu___429_55312  ->
    match uu___429_55312 with
    | FStar_Util.Inr x -> x
    | FStar_Util.Inl l ->
        let uu____55319 =
          FStar_Syntax_Syntax.lid_as_fv l
            FStar_Syntax_Syntax.delta_equational FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.fv_to_tm uu____55319
  
exception Embedding_failure 
let (uu___is_Embedding_failure : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Embedding_failure  -> true | uu____55329 -> false
  
exception Unembedding_failure 
let (uu___is_Unembedding_failure : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Unembedding_failure  -> true
    | uu____55340 -> false
  
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
             (fun uu____55506  ->
                let uu____55507 = FStar_Common.force_thunk s1  in
                f uu____55507))
  
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
  'Auu____56141 . FStar_Syntax_Syntax.term -> 'Auu____56141 -> Prims.string =
  fun typ  ->
    fun uu____56152  ->
      let uu____56153 = FStar_Syntax_Print.term_to_string typ  in
      FStar_Util.format1 "unknown %s" uu____56153
  
let (term_as_fv : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.fv) =
  fun t  ->
    let uu____56162 =
      let uu____56163 = FStar_Syntax_Subst.compress t  in
      uu____56163.FStar_Syntax_Syntax.n  in
    match uu____56162 with
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv
    | uu____56167 ->
        let uu____56168 =
          let uu____56170 = FStar_Syntax_Print.term_to_string t  in
          FStar_Util.format1 "Embeddings not defined for type %s" uu____56170
           in
        failwith uu____56168
  
let mk_emb :
  'a .
    'a raw_embedder ->
      'a raw_unembedder -> FStar_Syntax_Syntax.fv -> 'a embedding
  =
  fun em  ->
    fun un  ->
      fun fv  ->
        let typ = FStar_Syntax_Syntax.fv_to_tm fv  in
        let uu____56298 =
          let uu____56299 =
            let uu____56307 =
              let uu____56309 = FStar_Syntax_Syntax.lid_of_fv fv  in
              FStar_All.pipe_right uu____56309 FStar_Ident.string_of_lid  in
            (uu____56307, [])  in
          FStar_Syntax_Syntax.ET_app uu____56299  in
        { em; un; typ; print = (unknown_printer typ); emb_typ = uu____56298 }
  
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
      fun n1  -> let uu____56719 = unembed e t  in uu____56719 true n1
  
let try_unembed :
  'a .
    'a embedding ->
      FStar_Syntax_Syntax.term ->
        norm_cb -> 'a FStar_Pervasives_Native.option
  =
  fun e  ->
    fun t  ->
      fun n1  -> let uu____56768 = unembed e t  in uu____56768 false n1
  
let type_of : 'a . 'a embedding -> FStar_Syntax_Syntax.typ = fun e  -> e.typ 
let set_type : 'a . FStar_Syntax_Syntax.typ -> 'a embedding -> 'a embedding =
  fun ty  ->
    fun e  ->
      let uu___508_56821 = e  in
      {
        em = (uu___508_56821.em);
        un = (uu___508_56821.un);
        typ = ty;
        print = (uu___508_56821.print);
        emb_typ = (uu___508_56821.emb_typ)
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
              (let uu____56890 =
                 FStar_ST.op_Bang FStar_Options.debug_embedding  in
               if uu____56890
               then
                 let uu____56914 = FStar_Syntax_Print.term_to_string ta  in
                 let uu____56916 = FStar_Syntax_Print.emb_typ_to_string et
                    in
                 let uu____56918 = pa x  in
                 FStar_Util.print3
                   "Embedding a %s\n\temb_typ=%s\n\tvalue is %s\n"
                   uu____56914 uu____56916 uu____56918
               else ());
              (let uu____56925 =
                 FStar_ST.op_Bang FStar_Options.eager_embedding  in
               if uu____56925
               then f ()
               else
                 (let thunk1 = FStar_Common.mk_thunk f  in
                  let uu____56960 =
                    let uu____56967 =
                      let uu____56968 =
                        let uu____56969 = FStar_Dyn.mkdyn x  in
                        {
                          FStar_Syntax_Syntax.blob = uu____56969;
                          FStar_Syntax_Syntax.lkind =
                            (FStar_Syntax_Syntax.Lazy_embedding (et, thunk1));
                          FStar_Syntax_Syntax.ltyp = FStar_Syntax_Syntax.tun;
                          FStar_Syntax_Syntax.rng = rng
                        }  in
                      FStar_Syntax_Syntax.Tm_lazy uu____56968  in
                    FStar_Syntax_Syntax.mk uu____56967  in
                  uu____56960 FStar_Pervasives_Native.None rng))
  
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
                  FStar_Syntax_Syntax.ltyp = uu____57085;
                  FStar_Syntax_Syntax.rng = uu____57086;_}
                ->
                let uu____57097 =
                  (et <> et') ||
                    (FStar_ST.op_Bang FStar_Options.eager_embedding)
                   in
                if uu____57097
                then
                  let res =
                    let uu____57126 = FStar_Common.force_thunk t  in
                    f uu____57126  in
                  ((let uu____57170 =
                      FStar_ST.op_Bang FStar_Options.debug_embedding  in
                    if uu____57170
                    then
                      let uu____57194 =
                        FStar_Syntax_Print.emb_typ_to_string et  in
                      let uu____57196 =
                        FStar_Syntax_Print.emb_typ_to_string et'  in
                      let uu____57198 =
                        match res with
                        | FStar_Pervasives_Native.None  -> "None"
                        | FStar_Pervasives_Native.Some x2 ->
                            let uu____57203 = pa x2  in
                            Prims.op_Hat "Some " uu____57203
                         in
                      FStar_Util.print3
                        "Unembed cancellation failed\n\t%s <> %s\nvalue is %s\n"
                        uu____57194 uu____57196 uu____57198
                    else ());
                   res)
                else
                  (let a = FStar_Dyn.undyn b  in
                   (let uu____57215 =
                      FStar_ST.op_Bang FStar_Options.debug_embedding  in
                    if uu____57215
                    then
                      let uu____57239 =
                        FStar_Syntax_Print.emb_typ_to_string et  in
                      let uu____57241 = pa a  in
                      FStar_Util.print2
                        "Unembed cancelled for %s\n\tvalue is %s\n"
                        uu____57239 uu____57241
                    else ());
                   FStar_Pervasives_Native.Some a)
            | uu____57248 ->
                let aopt = f x1  in
                ((let uu____57253 =
                    FStar_ST.op_Bang FStar_Options.debug_embedding  in
                  if uu____57253
                  then
                    let uu____57277 = FStar_Syntax_Print.emb_typ_to_string et
                       in
                    let uu____57279 = FStar_Syntax_Print.term_to_string x1
                       in
                    let uu____57281 =
                      match aopt with
                      | FStar_Pervasives_Native.None  -> "None"
                      | FStar_Pervasives_Native.Some a ->
                          let uu____57286 = pa a  in
                          Prims.op_Hat "Some " uu____57286
                       in
                    FStar_Util.print3
                      "Unembedding:\n\temb_typ=%s\n\tterm is %s\n\tvalue is %s\n"
                      uu____57277 uu____57279 uu____57281
                  else ());
                 aopt)
  
let (mk_any_emb :
  FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term embedding) =
  fun typ  ->
    let em t _r _topt _norm =
      (let uu____57366 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
       if uu____57366
       then
         let uu____57390 = unknown_printer typ t  in
         FStar_Util.print1 "Embedding abstract: %s\n" uu____57390
       else ());
      t  in
    let un t _w _n =
      (let uu____57420 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
       if uu____57420
       then
         let uu____57444 = unknown_printer typ t  in
         FStar_Util.print1 "Unembedding abstract: %s\n" uu____57444
       else ());
      FStar_Pervasives_Native.Some t  in
    mk_emb_full em un typ (unknown_printer typ)
      FStar_Syntax_Syntax.ET_abstract
  
let (e_any : FStar_Syntax_Syntax.term embedding) =
  let em t _r _topt _norm = t  in
  let un t _w _n = FStar_Pervasives_Native.Some t  in
  let uu____57539 =
    let uu____57540 =
      let uu____57548 =
        FStar_All.pipe_right FStar_Parser_Const.term_lid
          FStar_Ident.string_of_lid
         in
      (uu____57548, [])  in
    FStar_Syntax_Syntax.ET_app uu____57540  in
  mk_emb_full em un FStar_Syntax_Syntax.t_term
    FStar_Syntax_Print.term_to_string uu____57539
  
let (e_unit : unit embedding) =
  let em u rng _topt _norm =
    let uu___582_57620 = FStar_Syntax_Util.exp_unit  in
    {
      FStar_Syntax_Syntax.n = (uu___582_57620.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___582_57620.FStar_Syntax_Syntax.vars)
    }  in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unascribe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit ) ->
        FStar_Pervasives_Native.Some ()
    | uu____57650 ->
        (if w
         then
           (let uu____57653 =
              let uu____57659 =
                let uu____57661 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded unit: %s" uu____57661  in
              (FStar_Errors.Warning_NotEmbedded, uu____57659)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____57653)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____57667 =
    let uu____57668 =
      let uu____57676 =
        FStar_All.pipe_right FStar_Parser_Const.unit_lid
          FStar_Ident.string_of_lid
         in
      (uu____57676, [])  in
    FStar_Syntax_Syntax.ET_app uu____57668  in
  mk_emb_full em un FStar_Syntax_Syntax.t_unit (fun uu____57683  -> "()")
    uu____57667
  
let (e_bool : Prims.bool embedding) =
  let em b rng _topt _norm =
    let t =
      if b
      then FStar_Syntax_Util.exp_true_bool
      else FStar_Syntax_Util.exp_false_bool  in
    let uu___602_57762 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___602_57762.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___602_57762.FStar_Syntax_Syntax.vars)
    }  in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) ->
        FStar_Pervasives_Native.Some b
    | uu____57800 ->
        (if w
         then
           (let uu____57803 =
              let uu____57809 =
                let uu____57811 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded bool: %s" uu____57811  in
              (FStar_Errors.Warning_NotEmbedded, uu____57809)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____57803)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____57818 =
    let uu____57819 =
      let uu____57827 =
        FStar_All.pipe_right FStar_Parser_Const.bool_lid
          FStar_Ident.string_of_lid
         in
      (uu____57827, [])  in
    FStar_Syntax_Syntax.ET_app uu____57819  in
  mk_emb_full em un FStar_Syntax_Syntax.t_bool FStar_Util.string_of_bool
    uu____57818
  
let (e_char : FStar_Char.char embedding) =
  let em c rng _topt _norm =
    let t = FStar_Syntax_Util.exp_char c  in
    let uu___621_57904 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___621_57904.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___621_57904.FStar_Syntax_Syntax.vars)
    }  in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c) ->
        FStar_Pervasives_Native.Some c
    | uu____57940 ->
        (if w
         then
           (let uu____57943 =
              let uu____57949 =
                let uu____57951 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded char: %s" uu____57951  in
              (FStar_Errors.Warning_NotEmbedded, uu____57949)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____57943)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____57958 =
    let uu____57959 =
      let uu____57967 =
        FStar_All.pipe_right FStar_Parser_Const.char_lid
          FStar_Ident.string_of_lid
         in
      (uu____57967, [])  in
    FStar_Syntax_Syntax.ET_app uu____57959  in
  mk_emb_full em un FStar_Syntax_Syntax.t_char FStar_Util.string_of_char
    uu____57958
  
let (e_int : FStar_BigInt.t embedding) =
  let t_int1 = FStar_Syntax_Util.fvar_const FStar_Parser_Const.int_lid  in
  let emb_t_int =
    let uu____57979 =
      let uu____57987 =
        FStar_All.pipe_right FStar_Parser_Const.int_lid
          FStar_Ident.string_of_lid
         in
      (uu____57987, [])  in
    FStar_Syntax_Syntax.ET_app uu____57979  in
  let em i rng _topt _norm =
    lazy_embed FStar_BigInt.string_of_big_int emb_t_int rng t_int1 i
      (fun uu____58058  ->
         let uu____58059 = FStar_BigInt.string_of_big_int i  in
         FStar_Syntax_Util.exp_int uu____58059)
     in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    lazy_unembed FStar_BigInt.string_of_big_int emb_t_int t t_int1
      (fun t1  ->
         match t1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
             (s,uu____58096)) ->
             let uu____58111 = FStar_BigInt.big_int_of_string s  in
             FStar_Pervasives_Native.Some uu____58111
         | uu____58112 ->
             (if w
              then
                (let uu____58115 =
                   let uu____58121 =
                     let uu____58123 = FStar_Syntax_Print.term_to_string t0
                        in
                     FStar_Util.format1 "Not an embedded int: %s" uu____58123
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____58121)  in
                 FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                   uu____58115)
              else ();
              FStar_Pervasives_Native.None))
     in
  mk_emb_full em un FStar_Syntax_Syntax.t_int FStar_BigInt.string_of_big_int
    emb_t_int
  
let (e_string : Prims.string embedding) =
  let emb_t_string =
    let uu____58134 =
      let uu____58142 =
        FStar_All.pipe_right FStar_Parser_Const.string_lid
          FStar_Ident.string_of_lid
         in
      (uu____58142, [])  in
    FStar_Syntax_Syntax.ET_app uu____58134  in
  let em s rng _topt _norm =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, rng)))
      FStar_Pervasives_Native.None rng
     in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
        (s,uu____58247)) -> FStar_Pervasives_Native.Some s
    | uu____58251 ->
        (if w
         then
           (let uu____58254 =
              let uu____58260 =
                let uu____58262 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded string: %s" uu____58262
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____58260)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____58254)
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
      let uu____58298 =
        let uu____58303 =
          let uu____58304 = FStar_Syntax_Syntax.as_arg ea.typ  in
          [uu____58304]  in
        FStar_Syntax_Syntax.mk_Tm_app t_opt uu____58303  in
      uu____58298 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
    let emb_t_option_a =
      let uu____58332 =
        let uu____58340 =
          FStar_All.pipe_right FStar_Parser_Const.option_lid
            FStar_Ident.string_of_lid
           in
        (uu____58340, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____58332  in
    let printer uu___430_58354 =
      match uu___430_58354 with
      | FStar_Pervasives_Native.None  -> "None"
      | FStar_Pervasives_Native.Some x ->
          let uu____58360 =
            let uu____58362 = ea.print x  in Prims.op_Hat uu____58362 ")"  in
          Prims.op_Hat "(Some " uu____58360
       in
    let em o rng topt norm1 =
      lazy_embed printer emb_t_option_a rng t_option_a o
        (fun uu____58439  ->
           match o with
           | FStar_Pervasives_Native.None  ->
               let uu____58440 =
                 let uu____58445 =
                   let uu____58446 =
                     FStar_Syntax_Syntax.tdataconstr
                       FStar_Parser_Const.none_lid
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____58446
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 let uu____58447 =
                   let uu____58448 =
                     let uu____58457 = type_of ea  in
                     FStar_Syntax_Syntax.iarg uu____58457  in
                   [uu____58448]  in
                 FStar_Syntax_Syntax.mk_Tm_app uu____58445 uu____58447  in
               uu____58440 FStar_Pervasives_Native.None rng
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
                        let uu____58548 =
                          FStar_Syntax_Syntax.lid_as_fv some_v
                            FStar_Syntax_Syntax.delta_equational
                            FStar_Pervasives_Native.None
                           in
                        FStar_Syntax_Syntax.fv_to_tm uu____58548  in
                      let uu____58549 =
                        let uu____58554 =
                          FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm
                            [FStar_Syntax_Syntax.U_zero]
                           in
                        let uu____58555 =
                          let uu____58556 =
                            let uu____58565 = type_of ea  in
                            FStar_Syntax_Syntax.iarg uu____58565  in
                          let uu____58566 =
                            let uu____58577 = FStar_Syntax_Syntax.as_arg t
                               in
                            [uu____58577]  in
                          uu____58556 :: uu____58566  in
                        FStar_Syntax_Syntax.mk_Tm_app uu____58554 uu____58555
                         in
                      uu____58549 FStar_Pervasives_Native.None rng)
                  in
               let uu____58612 =
                 let uu____58617 =
                   let uu____58618 =
                     FStar_Syntax_Syntax.tdataconstr
                       FStar_Parser_Const.some_lid
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____58618
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 let uu____58619 =
                   let uu____58620 =
                     let uu____58629 = type_of ea  in
                     FStar_Syntax_Syntax.iarg uu____58629  in
                   let uu____58630 =
                     let uu____58641 =
                       let uu____58650 =
                         let uu____58651 = embed ea a  in
                         uu____58651 rng shadow_a norm1  in
                       FStar_Syntax_Syntax.as_arg uu____58650  in
                     [uu____58641]  in
                   uu____58620 :: uu____58630  in
                 FStar_Syntax_Syntax.mk_Tm_app uu____58617 uu____58619  in
               uu____58612 FStar_Pervasives_Native.None rng)
       in
    let un t0 w norm1 =
      let t = FStar_Syntax_Util.unmeta_safe t0  in
      lazy_unembed printer emb_t_option_a t t_option_a
        (fun t1  ->
           let uu____58788 = FStar_Syntax_Util.head_and_args' t1  in
           match uu____58788 with
           | (hd1,args) ->
               let uu____58829 =
                 let uu____58844 =
                   let uu____58845 = FStar_Syntax_Util.un_uinst hd1  in
                   uu____58845.FStar_Syntax_Syntax.n  in
                 (uu____58844, args)  in
               (match uu____58829 with
                | (FStar_Syntax_Syntax.Tm_fvar fv,uu____58863) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.none_lid
                    ->
                    FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,uu____58887::(a,uu____58889)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.some_lid
                    ->
                    let uu____58940 =
                      let uu____58943 = unembed ea a  in uu____58943 w norm1
                       in
                    FStar_Util.bind_opt uu____58940
                      (fun a1  ->
                         FStar_Pervasives_Native.Some
                           (FStar_Pervasives_Native.Some a1))
                | uu____58962 ->
                    (if w
                     then
                       (let uu____58979 =
                          let uu____58985 =
                            let uu____58987 =
                              FStar_Syntax_Print.term_to_string t0  in
                            FStar_Util.format1 "Not an embedded option: %s"
                              uu____58987
                             in
                          (FStar_Errors.Warning_NotEmbedded, uu____58985)  in
                        FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                          uu____58979)
                     else ();
                     FStar_Pervasives_Native.None)))
       in
    let uu____58995 =
      let uu____58996 = type_of ea  in
      FStar_Syntax_Syntax.t_option_of uu____58996  in
    mk_emb_full em un uu____58995 printer emb_t_option_a
  
let e_tuple2 : 'a 'b . 'a embedding -> 'b embedding -> ('a * 'b) embedding =
  fun ea  ->
    fun eb  ->
      let t_pair_a_b =
        let t_tup2 =
          FStar_Syntax_Util.fvar_const FStar_Parser_Const.lid_tuple2  in
        let uu____59038 =
          let uu____59043 =
            let uu____59044 = FStar_Syntax_Syntax.as_arg ea.typ  in
            let uu____59053 =
              let uu____59064 = FStar_Syntax_Syntax.as_arg eb.typ  in
              [uu____59064]  in
            uu____59044 :: uu____59053  in
          FStar_Syntax_Syntax.mk_Tm_app t_tup2 uu____59043  in
        uu____59038 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
      let emb_t_pair_a_b =
        let uu____59100 =
          let uu____59108 =
            FStar_All.pipe_right FStar_Parser_Const.lid_tuple2
              FStar_Ident.string_of_lid
             in
          (uu____59108, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____59100  in
      let printer uu____59124 =
        match uu____59124 with
        | (x,y) ->
            let uu____59132 = ea.print x  in
            let uu____59134 = eb.print y  in
            FStar_Util.format2 "(%s, %s)" uu____59132 uu____59134
         in
      let em x rng topt norm1 =
        lazy_embed printer emb_t_pair_a_b rng t_pair_a_b x
          (fun uu____59219  ->
             let proj i ab =
               let uu____59235 =
                 let uu____59240 =
                   FStar_Parser_Const.mk_tuple_data_lid (Prims.parse_int "2")
                     rng
                    in
                 let uu____59242 =
                   FStar_Syntax_Syntax.null_bv FStar_Syntax_Syntax.tun  in
                 FStar_Syntax_Util.mk_field_projector_name uu____59240
                   uu____59242 i
                  in
               match uu____59235 with
               | (proj_1,uu____59246) ->
                   let proj_1_tm =
                     let uu____59248 =
                       FStar_Syntax_Syntax.lid_as_fv proj_1
                         FStar_Syntax_Syntax.delta_equational
                         FStar_Pervasives_Native.None
                        in
                     FStar_Syntax_Syntax.fv_to_tm uu____59248  in
                   let uu____59249 =
                     let uu____59254 =
                       FStar_Syntax_Syntax.mk_Tm_uinst proj_1_tm
                         [FStar_Syntax_Syntax.U_zero]
                        in
                     let uu____59255 =
                       let uu____59256 =
                         let uu____59265 = type_of ea  in
                         FStar_Syntax_Syntax.iarg uu____59265  in
                       let uu____59266 =
                         let uu____59277 =
                           let uu____59286 = type_of eb  in
                           FStar_Syntax_Syntax.iarg uu____59286  in
                         let uu____59287 =
                           let uu____59298 = FStar_Syntax_Syntax.as_arg ab
                              in
                           [uu____59298]  in
                         uu____59277 :: uu____59287  in
                       uu____59256 :: uu____59266  in
                     FStar_Syntax_Syntax.mk_Tm_app uu____59254 uu____59255
                      in
                   uu____59249 FStar_Pervasives_Native.None rng
                in
             let shadow_a = map_shadow topt (proj (Prims.parse_int "1"))  in
             let shadow_b = map_shadow topt (proj (Prims.parse_int "2"))  in
             let uu____59459 =
               let uu____59464 =
                 let uu____59465 =
                   FStar_Syntax_Syntax.tdataconstr
                     FStar_Parser_Const.lid_Mktuple2
                    in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu____59465
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                  in
               let uu____59466 =
                 let uu____59467 =
                   let uu____59476 = type_of ea  in
                   FStar_Syntax_Syntax.iarg uu____59476  in
                 let uu____59477 =
                   let uu____59488 =
                     let uu____59497 = type_of eb  in
                     FStar_Syntax_Syntax.iarg uu____59497  in
                   let uu____59498 =
                     let uu____59509 =
                       let uu____59518 =
                         let uu____59519 =
                           embed ea (FStar_Pervasives_Native.fst x)  in
                         uu____59519 rng shadow_a norm1  in
                       FStar_Syntax_Syntax.as_arg uu____59518  in
                     let uu____59589 =
                       let uu____59600 =
                         let uu____59609 =
                           let uu____59610 =
                             embed eb (FStar_Pervasives_Native.snd x)  in
                           uu____59610 rng shadow_b norm1  in
                         FStar_Syntax_Syntax.as_arg uu____59609  in
                       [uu____59600]  in
                     uu____59509 :: uu____59589  in
                   uu____59488 :: uu____59498  in
                 uu____59467 :: uu____59477  in
               FStar_Syntax_Syntax.mk_Tm_app uu____59464 uu____59466  in
             uu____59459 FStar_Pervasives_Native.None rng)
         in
      let un t0 w norm1 =
        let t = FStar_Syntax_Util.unmeta_safe t0  in
        lazy_unembed printer emb_t_pair_a_b t t_pair_a_b
          (fun t1  ->
             let uu____59775 = FStar_Syntax_Util.head_and_args' t1  in
             match uu____59775 with
             | (hd1,args) ->
                 let uu____59818 =
                   let uu____59831 =
                     let uu____59832 = FStar_Syntax_Util.un_uinst hd1  in
                     uu____59832.FStar_Syntax_Syntax.n  in
                   (uu____59831, args)  in
                 (match uu____59818 with
                  | (FStar_Syntax_Syntax.Tm_fvar
                     fv,uu____59850::uu____59851::(a,uu____59853)::(b,uu____59855)::[])
                      when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.lid_Mktuple2
                      ->
                      let uu____59914 =
                        let uu____59917 = unembed ea a  in
                        uu____59917 w norm1  in
                      FStar_Util.bind_opt uu____59914
                        (fun a1  ->
                           let uu____59937 =
                             let uu____59940 = unembed eb b  in
                             uu____59940 w norm1  in
                           FStar_Util.bind_opt uu____59937
                             (fun b1  ->
                                FStar_Pervasives_Native.Some (a1, b1)))
                  | uu____59963 ->
                      (if w
                       then
                         (let uu____59978 =
                            let uu____59984 =
                              let uu____59986 =
                                FStar_Syntax_Print.term_to_string t0  in
                              FStar_Util.format1 "Not an embedded pair: %s"
                                uu____59986
                               in
                            (FStar_Errors.Warning_NotEmbedded, uu____59984)
                             in
                          FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                            uu____59978)
                       else ();
                       FStar_Pervasives_Native.None)))
         in
      let uu____59996 =
        let uu____59997 = type_of ea  in
        let uu____59998 = type_of eb  in
        FStar_Syntax_Syntax.t_tuple2_of uu____59997 uu____59998  in
      mk_emb_full em un uu____59996 printer emb_t_pair_a_b
  
let e_either :
  'a 'b . 'a embedding -> 'b embedding -> ('a,'b) FStar_Util.either embedding
  =
  fun ea  ->
    fun eb  ->
      let t_sum_a_b =
        let t_either =
          FStar_Syntax_Util.fvar_const FStar_Parser_Const.either_lid  in
        let uu____60042 =
          let uu____60047 =
            let uu____60048 = FStar_Syntax_Syntax.as_arg ea.typ  in
            let uu____60057 =
              let uu____60068 = FStar_Syntax_Syntax.as_arg eb.typ  in
              [uu____60068]  in
            uu____60048 :: uu____60057  in
          FStar_Syntax_Syntax.mk_Tm_app t_either uu____60047  in
        uu____60042 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
      let emb_t_sum_a_b =
        let uu____60104 =
          let uu____60112 =
            FStar_All.pipe_right FStar_Parser_Const.either_lid
              FStar_Ident.string_of_lid
             in
          (uu____60112, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____60104  in
      let printer s =
        match s with
        | FStar_Util.Inl a ->
            let uu____60135 = ea.print a  in
            FStar_Util.format1 "Inl %s" uu____60135
        | FStar_Util.Inr b ->
            let uu____60139 = eb.print b  in
            FStar_Util.format1 "Inr %s" uu____60139
         in
      let em s rng topt norm1 =
        lazy_embed printer emb_t_sum_a_b rng t_sum_a_b s
          (match s with
           | FStar_Util.Inl a ->
               (fun uu____60227  ->
                  let shadow_a =
                    map_shadow topt
                      (fun t  ->
                         let v1 = FStar_Ident.mk_ident ("v", rng)  in
                         let some_v =
                           FStar_Syntax_Util.mk_field_projector_name_from_ident
                             FStar_Parser_Const.inl_lid v1
                            in
                         let some_v_tm =
                           let uu____60299 =
                             FStar_Syntax_Syntax.lid_as_fv some_v
                               FStar_Syntax_Syntax.delta_equational
                               FStar_Pervasives_Native.None
                              in
                           FStar_Syntax_Syntax.fv_to_tm uu____60299  in
                         let uu____60300 =
                           let uu____60305 =
                             FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm
                               [FStar_Syntax_Syntax.U_zero]
                              in
                           let uu____60306 =
                             let uu____60307 =
                               let uu____60316 = type_of ea  in
                               FStar_Syntax_Syntax.iarg uu____60316  in
                             let uu____60317 =
                               let uu____60328 =
                                 let uu____60337 = type_of eb  in
                                 FStar_Syntax_Syntax.iarg uu____60337  in
                               let uu____60338 =
                                 let uu____60349 =
                                   FStar_Syntax_Syntax.as_arg t  in
                                 [uu____60349]  in
                               uu____60328 :: uu____60338  in
                             uu____60307 :: uu____60317  in
                           FStar_Syntax_Syntax.mk_Tm_app uu____60305
                             uu____60306
                            in
                         uu____60300 FStar_Pervasives_Native.None rng)
                     in
                  let uu____60392 =
                    let uu____60397 =
                      let uu____60398 =
                        FStar_Syntax_Syntax.tdataconstr
                          FStar_Parser_Const.inl_lid
                         in
                      FStar_Syntax_Syntax.mk_Tm_uinst uu____60398
                        [FStar_Syntax_Syntax.U_zero;
                        FStar_Syntax_Syntax.U_zero]
                       in
                    let uu____60399 =
                      let uu____60400 =
                        let uu____60409 = type_of ea  in
                        FStar_Syntax_Syntax.iarg uu____60409  in
                      let uu____60410 =
                        let uu____60421 =
                          let uu____60430 = type_of eb  in
                          FStar_Syntax_Syntax.iarg uu____60430  in
                        let uu____60431 =
                          let uu____60442 =
                            let uu____60451 =
                              let uu____60452 = embed ea a  in
                              uu____60452 rng shadow_a norm1  in
                            FStar_Syntax_Syntax.as_arg uu____60451  in
                          [uu____60442]  in
                        uu____60421 :: uu____60431  in
                      uu____60400 :: uu____60410  in
                    FStar_Syntax_Syntax.mk_Tm_app uu____60397 uu____60399  in
                  uu____60392 FStar_Pervasives_Native.None rng)
           | FStar_Util.Inr b ->
               (fun uu____60557  ->
                  let shadow_b =
                    map_shadow topt
                      (fun t  ->
                         let v1 = FStar_Ident.mk_ident ("v", rng)  in
                         let some_v =
                           FStar_Syntax_Util.mk_field_projector_name_from_ident
                             FStar_Parser_Const.inr_lid v1
                            in
                         let some_v_tm =
                           let uu____60629 =
                             FStar_Syntax_Syntax.lid_as_fv some_v
                               FStar_Syntax_Syntax.delta_equational
                               FStar_Pervasives_Native.None
                              in
                           FStar_Syntax_Syntax.fv_to_tm uu____60629  in
                         let uu____60630 =
                           let uu____60635 =
                             FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm
                               [FStar_Syntax_Syntax.U_zero]
                              in
                           let uu____60636 =
                             let uu____60637 =
                               let uu____60646 = type_of ea  in
                               FStar_Syntax_Syntax.iarg uu____60646  in
                             let uu____60647 =
                               let uu____60658 =
                                 let uu____60667 = type_of eb  in
                                 FStar_Syntax_Syntax.iarg uu____60667  in
                               let uu____60668 =
                                 let uu____60679 =
                                   FStar_Syntax_Syntax.as_arg t  in
                                 [uu____60679]  in
                               uu____60658 :: uu____60668  in
                             uu____60637 :: uu____60647  in
                           FStar_Syntax_Syntax.mk_Tm_app uu____60635
                             uu____60636
                            in
                         uu____60630 FStar_Pervasives_Native.None rng)
                     in
                  let uu____60722 =
                    let uu____60727 =
                      let uu____60728 =
                        FStar_Syntax_Syntax.tdataconstr
                          FStar_Parser_Const.inr_lid
                         in
                      FStar_Syntax_Syntax.mk_Tm_uinst uu____60728
                        [FStar_Syntax_Syntax.U_zero;
                        FStar_Syntax_Syntax.U_zero]
                       in
                    let uu____60729 =
                      let uu____60730 =
                        let uu____60739 = type_of ea  in
                        FStar_Syntax_Syntax.iarg uu____60739  in
                      let uu____60740 =
                        let uu____60751 =
                          let uu____60760 = type_of eb  in
                          FStar_Syntax_Syntax.iarg uu____60760  in
                        let uu____60761 =
                          let uu____60772 =
                            let uu____60781 =
                              let uu____60782 = embed eb b  in
                              uu____60782 rng shadow_b norm1  in
                            FStar_Syntax_Syntax.as_arg uu____60781  in
                          [uu____60772]  in
                        uu____60751 :: uu____60761  in
                      uu____60730 :: uu____60740  in
                    FStar_Syntax_Syntax.mk_Tm_app uu____60727 uu____60729  in
                  uu____60722 FStar_Pervasives_Native.None rng))
         in
      let un t0 w norm1 =
        let t = FStar_Syntax_Util.unmeta_safe t0  in
        lazy_unembed printer emb_t_sum_a_b t t_sum_a_b
          (fun t1  ->
             let uu____60937 = FStar_Syntax_Util.head_and_args' t1  in
             match uu____60937 with
             | (hd1,args) ->
                 let uu____60980 =
                   let uu____60995 =
                     let uu____60996 = FStar_Syntax_Util.un_uinst hd1  in
                     uu____60996.FStar_Syntax_Syntax.n  in
                   (uu____60995, args)  in
                 (match uu____60980 with
                  | (FStar_Syntax_Syntax.Tm_fvar
                     fv,uu____61016::uu____61017::(a,uu____61019)::[]) when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.inl_lid
                      ->
                      let uu____61086 =
                        let uu____61089 = unembed ea a  in
                        uu____61089 w norm1  in
                      FStar_Util.bind_opt uu____61086
                        (fun a1  ->
                           FStar_Pervasives_Native.Some (FStar_Util.Inl a1))
                  | (FStar_Syntax_Syntax.Tm_fvar
                     fv,uu____61113::uu____61114::(b,uu____61116)::[]) when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.inr_lid
                      ->
                      let uu____61183 =
                        let uu____61186 = unembed eb b  in
                        uu____61186 w norm1  in
                      FStar_Util.bind_opt uu____61183
                        (fun b1  ->
                           FStar_Pervasives_Native.Some (FStar_Util.Inr b1))
                  | uu____61209 ->
                      (if w
                       then
                         (let uu____61226 =
                            let uu____61232 =
                              let uu____61234 =
                                FStar_Syntax_Print.term_to_string t0  in
                              FStar_Util.format1 "Not an embedded sum: %s"
                                uu____61234
                               in
                            (FStar_Errors.Warning_NotEmbedded, uu____61232)
                             in
                          FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                            uu____61226)
                       else ();
                       FStar_Pervasives_Native.None)))
         in
      let uu____61244 =
        let uu____61245 = type_of ea  in
        let uu____61246 = type_of eb  in
        FStar_Syntax_Syntax.t_either_of uu____61245 uu____61246  in
      mk_emb_full em un uu____61244 printer emb_t_sum_a_b
  
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea  ->
    let t_list_a =
      let t_list = FStar_Syntax_Util.fvar_const FStar_Parser_Const.list_lid
         in
      let uu____61274 =
        let uu____61279 =
          let uu____61280 = FStar_Syntax_Syntax.as_arg ea.typ  in
          [uu____61280]  in
        FStar_Syntax_Syntax.mk_Tm_app t_list uu____61279  in
      uu____61274 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
    let emb_t_list_a =
      let uu____61308 =
        let uu____61316 =
          FStar_All.pipe_right FStar_Parser_Const.list_lid
            FStar_Ident.string_of_lid
           in
        (uu____61316, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____61308  in
    let printer l =
      let uu____61333 =
        let uu____61335 =
          let uu____61337 = FStar_List.map ea.print l  in
          FStar_All.pipe_right uu____61337 (FStar_String.concat "; ")  in
        Prims.op_Hat uu____61335 "]"  in
      Prims.op_Hat "[" uu____61333  in
    let rec em l rng shadow_l norm1 =
      lazy_embed printer emb_t_list_a rng t_list_a l
        (fun uu____61423  ->
           let t =
             let uu____61425 = type_of ea  in
             FStar_Syntax_Syntax.iarg uu____61425  in
           match l with
           | [] ->
               let uu____61426 =
                 let uu____61431 =
                   let uu____61432 =
                     FStar_Syntax_Syntax.tdataconstr
                       FStar_Parser_Const.nil_lid
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____61432
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 FStar_Syntax_Syntax.mk_Tm_app uu____61431 [t]  in
               uu____61426 FStar_Pervasives_Native.None rng
           | hd1::tl1 ->
               let cons1 =
                 let uu____61456 =
                   FStar_Syntax_Syntax.tdataconstr
                     FStar_Parser_Const.cons_lid
                    in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu____61456
                   [FStar_Syntax_Syntax.U_zero]
                  in
               let proj f cons_tm =
                 let fid = FStar_Ident.mk_ident (f, rng)  in
                 let proj =
                   FStar_Syntax_Util.mk_field_projector_name_from_ident
                     FStar_Parser_Const.cons_lid fid
                    in
                 let proj_tm =
                   let uu____61476 =
                     FStar_Syntax_Syntax.lid_as_fv proj
                       FStar_Syntax_Syntax.delta_equational
                       FStar_Pervasives_Native.None
                      in
                   FStar_Syntax_Syntax.fv_to_tm uu____61476  in
                 let uu____61477 =
                   let uu____61482 =
                     FStar_Syntax_Syntax.mk_Tm_uinst proj_tm
                       [FStar_Syntax_Syntax.U_zero]
                      in
                   let uu____61483 =
                     let uu____61484 =
                       let uu____61493 = type_of ea  in
                       FStar_Syntax_Syntax.iarg uu____61493  in
                     let uu____61494 =
                       let uu____61505 = FStar_Syntax_Syntax.as_arg cons_tm
                          in
                       [uu____61505]  in
                     uu____61484 :: uu____61494  in
                   FStar_Syntax_Syntax.mk_Tm_app uu____61482 uu____61483  in
                 uu____61477 FStar_Pervasives_Native.None rng  in
               let shadow_hd = map_shadow shadow_l (proj "hd")  in
               let shadow_tl = map_shadow shadow_l (proj "tl")  in
               let uu____61658 =
                 let uu____61663 =
                   let uu____61664 =
                     let uu____61675 =
                       let uu____61684 =
                         let uu____61685 = embed ea hd1  in
                         uu____61685 rng shadow_hd norm1  in
                       FStar_Syntax_Syntax.as_arg uu____61684  in
                     let uu____61755 =
                       let uu____61766 =
                         let uu____61775 = em tl1 rng shadow_tl norm1  in
                         FStar_Syntax_Syntax.as_arg uu____61775  in
                       [uu____61766]  in
                     uu____61675 :: uu____61755  in
                   t :: uu____61664  in
                 FStar_Syntax_Syntax.mk_Tm_app cons1 uu____61663  in
               uu____61658 FStar_Pervasives_Native.None rng)
       in
    let rec un t0 w norm1 =
      let t = FStar_Syntax_Util.unmeta_safe t0  in
      lazy_unembed printer emb_t_list_a t t_list_a
        (fun t1  ->
           let uu____61891 = FStar_Syntax_Util.head_and_args' t1  in
           match uu____61891 with
           | (hd1,args) ->
               let uu____61932 =
                 let uu____61945 =
                   let uu____61946 = FStar_Syntax_Util.un_uinst hd1  in
                   uu____61946.FStar_Syntax_Syntax.n  in
                 (uu____61945, args)  in
               (match uu____61932 with
                | (FStar_Syntax_Syntax.Tm_fvar fv,uu____61962) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.nil_lid
                    -> FStar_Pervasives_Native.Some []
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(uu____61982,FStar_Pervasives_Native.Some
                       (FStar_Syntax_Syntax.Implicit uu____61983))::(hd2,FStar_Pervasives_Native.None
                                                                    )::
                   (tl1,FStar_Pervasives_Native.None )::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.cons_lid
                    ->
                    let uu____62025 =
                      let uu____62028 = unembed ea hd2  in
                      uu____62028 w norm1  in
                    FStar_Util.bind_opt uu____62025
                      (fun hd3  ->
                         let uu____62046 = un tl1 w norm1  in
                         FStar_Util.bind_opt uu____62046
                           (fun tl2  ->
                              FStar_Pervasives_Native.Some (hd3 :: tl2)))
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(hd2,FStar_Pervasives_Native.None )::(tl1,FStar_Pervasives_Native.None
                                                            )::[])
                    when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.cons_lid
                    ->
                    let uu____62096 =
                      let uu____62099 = unembed ea hd2  in
                      uu____62099 w norm1  in
                    FStar_Util.bind_opt uu____62096
                      (fun hd3  ->
                         let uu____62117 = un tl1 w norm1  in
                         FStar_Util.bind_opt uu____62117
                           (fun tl2  ->
                              FStar_Pervasives_Native.Some (hd3 :: tl2)))
                | uu____62134 ->
                    (if w
                     then
                       (let uu____62149 =
                          let uu____62155 =
                            let uu____62157 =
                              FStar_Syntax_Print.term_to_string t0  in
                            FStar_Util.format1 "Not an embedded list: %s"
                              uu____62157
                             in
                          (FStar_Errors.Warning_NotEmbedded, uu____62155)  in
                        FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                          uu____62149)
                     else ();
                     FStar_Pervasives_Native.None)))
       in
    let uu____62165 =
      let uu____62166 = type_of ea  in
      FStar_Syntax_Syntax.t_list_of uu____62166  in
    mk_emb_full em un uu____62165 printer emb_t_list_a
  
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
    match projectee with | Simpl  -> true | uu____62209 -> false
  
let (uu___is_Weak : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Weak  -> true | uu____62220 -> false
  
let (uu___is_HNF : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | HNF  -> true | uu____62231 -> false
  
let (uu___is_Primops : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____62242 -> false
  
let (uu___is_Delta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Delta  -> true | uu____62253 -> false
  
let (uu___is_Zeta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Zeta  -> true | uu____62264 -> false
  
let (uu___is_Iota : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Iota  -> true | uu____62275 -> false
  
let (uu___is_Reify : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____62286 -> false
  
let (uu___is_UnfoldOnly : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____62301 -> false
  
let (__proj__UnfoldOnly__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldFully : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldFully _0 -> true | uu____62333 -> false
  
let (__proj__UnfoldFully__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldFully _0 -> _0 
let (uu___is_UnfoldAttr : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____62365 -> false
  
let (__proj__UnfoldAttr__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_NBE : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | NBE  -> true | uu____62393 -> false
  
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
    let uu____62411 =
      FStar_Ident.lid_of_str "FStar.Syntax.Embeddings.norm_step"  in
    FStar_Syntax_Util.fvar_const uu____62411  in
  let emb_t_norm_step =
    let uu____62414 =
      let uu____62422 =
        FStar_All.pipe_right FStar_Parser_Const.norm_step_lid
          FStar_Ident.string_of_lid
         in
      (uu____62422, [])  in
    FStar_Syntax_Syntax.ET_app uu____62414  in
  let printer uu____62434 = "norm_step"  in
  let em n1 rng _topt norm1 =
    lazy_embed printer emb_t_norm_step rng t_norm_step1 n1
      (fun uu____62500  ->
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
             let uu____62505 =
               let uu____62510 =
                 let uu____62511 =
                   let uu____62520 =
                     let uu____62521 =
                       let uu____62528 = e_list e_string  in
                       embed uu____62528 l  in
                     uu____62521 rng FStar_Pervasives_Native.None norm1  in
                   FStar_Syntax_Syntax.as_arg uu____62520  in
                 [uu____62511]  in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldOnly uu____62510  in
             uu____62505 FStar_Pervasives_Native.None rng
         | UnfoldFully l ->
             let uu____62587 =
               let uu____62592 =
                 let uu____62593 =
                   let uu____62602 =
                     let uu____62603 =
                       let uu____62610 = e_list e_string  in
                       embed uu____62610 l  in
                     uu____62603 rng FStar_Pervasives_Native.None norm1  in
                   FStar_Syntax_Syntax.as_arg uu____62602  in
                 [uu____62593]  in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldFully uu____62592
                in
             uu____62587 FStar_Pervasives_Native.None rng
         | UnfoldAttr l ->
             let uu____62669 =
               let uu____62674 =
                 let uu____62675 =
                   let uu____62684 =
                     let uu____62685 =
                       let uu____62692 = e_list e_string  in
                       embed uu____62692 l  in
                     uu____62685 rng FStar_Pervasives_Native.None norm1  in
                   FStar_Syntax_Syntax.as_arg uu____62684  in
                 [uu____62675]  in
               FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldAttr uu____62674  in
             uu____62669 FStar_Pervasives_Native.None rng)
     in
  let un t0 w norm1 =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    lazy_unembed printer emb_t_norm_step t t_norm_step1
      (fun t1  ->
         let uu____62781 = FStar_Syntax_Util.head_and_args t1  in
         match uu____62781 with
         | (hd1,args) ->
             let uu____62826 =
               let uu____62841 =
                 let uu____62842 = FStar_Syntax_Util.un_uinst hd1  in
                 uu____62842.FStar_Syntax_Syntax.n  in
               (uu____62841, args)  in
             (match uu____62826 with
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
              | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____63030)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldonly
                  ->
                  let uu____63065 =
                    let uu____63071 =
                      let uu____63081 = e_list e_string  in
                      unembed uu____63081 l  in
                    uu____63071 w norm1  in
                  FStar_Util.bind_opt uu____63065
                    (fun ss  ->
                       FStar_All.pipe_left
                         (fun _63107  -> FStar_Pervasives_Native.Some _63107)
                         (UnfoldOnly ss))
              | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____63110)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldfully
                  ->
                  let uu____63145 =
                    let uu____63151 =
                      let uu____63161 = e_list e_string  in
                      unembed uu____63161 l  in
                    uu____63151 w norm1  in
                  FStar_Util.bind_opt uu____63145
                    (fun ss  ->
                       FStar_All.pipe_left
                         (fun _63187  -> FStar_Pervasives_Native.Some _63187)
                         (UnfoldFully ss))
              | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____63190)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldattr
                  ->
                  let uu____63225 =
                    let uu____63231 =
                      let uu____63241 = e_list e_string  in
                      unembed uu____63241 l  in
                    uu____63231 w norm1  in
                  FStar_Util.bind_opt uu____63225
                    (fun ss  ->
                       FStar_All.pipe_left
                         (fun _63267  -> FStar_Pervasives_Native.Some _63267)
                         (UnfoldAttr ss))
              | uu____63268 ->
                  (if w
                   then
                     (let uu____63285 =
                        let uu____63291 =
                          let uu____63293 =
                            FStar_Syntax_Print.term_to_string t0  in
                          FStar_Util.format1 "Not an embedded norm_step: %s"
                            uu____63293
                           in
                        (FStar_Errors.Warning_NotEmbedded, uu____63291)  in
                      FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                        uu____63285)
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
    | uu____63395 ->
        (if w
         then
           (let uu____63398 =
              let uu____63404 =
                let uu____63406 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded range: %s" uu____63406
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____63404)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____63398)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____63412 =
    let uu____63413 =
      let uu____63421 =
        FStar_All.pipe_right FStar_Parser_Const.range_lid
          FStar_Ident.string_of_lid
         in
      (uu____63421, [])  in
    FStar_Syntax_Syntax.ET_app uu____63413  in
  mk_emb_full em un FStar_Syntax_Syntax.t_range FStar_Range.string_of_range
    uu____63412
  
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
        let uu____63492 =
          let uu____63499 =
            let uu____63500 =
              let uu____63515 =
                let uu____63524 =
                  let uu____63531 = FStar_Syntax_Syntax.null_bv ea.typ  in
                  (uu____63531, FStar_Pervasives_Native.None)  in
                [uu____63524]  in
              let uu____63546 = FStar_Syntax_Syntax.mk_Total eb.typ  in
              (uu____63515, uu____63546)  in
            FStar_Syntax_Syntax.Tm_arrow uu____63500  in
          FStar_Syntax_Syntax.mk uu____63499  in
        uu____63492 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
      let emb_t_arr_a_b =
        FStar_Syntax_Syntax.ET_fun ((ea.emb_typ), (eb.emb_typ))  in
      let printer f = "<fun>"  in
      let em f rng shadow_f norm1 =
        lazy_embed (fun uu____63659  -> "<fun>") emb_t_arr_a_b rng t_arrow f
          (fun uu____63665  ->
             let uu____63666 = force_shadow shadow_f  in
             match uu____63666 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Exn.raise Embedding_failure
             | FStar_Pervasives_Native.Some repr_f ->
                 ((let uu____63728 =
                     FStar_ST.op_Bang FStar_Options.debug_embedding  in
                   if uu____63728
                   then
                     let uu____63752 =
                       FStar_Syntax_Print.term_to_string repr_f  in
                     let uu____63754 = FStar_Util.stack_dump ()  in
                     FStar_Util.print2
                       "e_arrow forced back to term using shadow %s; repr=%s\n"
                       uu____63752 uu____63754
                   else ());
                  (let res = norm1 (FStar_Util.Inr repr_f)  in
                   (let uu____63761 =
                      FStar_ST.op_Bang FStar_Options.debug_embedding  in
                    if uu____63761
                    then
                      let uu____63785 =
                        FStar_Syntax_Print.term_to_string repr_f  in
                      let uu____63787 = FStar_Syntax_Print.term_to_string res
                         in
                      let uu____63789 = FStar_Util.stack_dump ()  in
                      FStar_Util.print3
                        "e_arrow forced back to term using shadow %s; repr=%s\n\t%s\n"
                        uu____63785 uu____63787 uu____63789
                    else ());
                   res)))
         in
      let un f w norm1 =
        lazy_unembed printer emb_t_arr_a_b f t_arrow
          (fun f1  ->
             let f_wrapped a =
               (let uu____63848 =
                  FStar_ST.op_Bang FStar_Options.debug_embedding  in
                if uu____63848
                then
                  let uu____63872 = FStar_Syntax_Print.term_to_string f1  in
                  let uu____63874 = FStar_Util.stack_dump ()  in
                  FStar_Util.print2
                    "Calling back into normalizer for %s\n%s\n" uu____63872
                    uu____63874
                else ());
               (let a_tm =
                  let uu____63880 = embed ea a  in
                  uu____63880 f1.FStar_Syntax_Syntax.pos
                    FStar_Pervasives_Native.None norm1
                   in
                let b_tm =
                  let uu____63913 =
                    let uu____63918 =
                      let uu____63919 =
                        let uu____63924 =
                          let uu____63925 = FStar_Syntax_Syntax.as_arg a_tm
                             in
                          [uu____63925]  in
                        FStar_Syntax_Syntax.mk_Tm_app f1 uu____63924  in
                      uu____63919 FStar_Pervasives_Native.None
                        f1.FStar_Syntax_Syntax.pos
                       in
                    FStar_Util.Inr uu____63918  in
                  norm1 uu____63913  in
                let uu____63952 =
                  let uu____63955 = unembed eb b_tm  in uu____63955 w norm1
                   in
                match uu____63952 with
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
                let uu____64055 = FStar_List.splitAt n_tvars args  in
                match uu____64055 with
                | (_tvar_args,rest_args) ->
                    let uu____64132 = FStar_List.hd rest_args  in
                    (match uu____64132 with
                     | (x,uu____64152) ->
                         let shadow_app =
                           let uu____64166 =
                             FStar_Common.mk_thunk
                               (fun uu____64175  ->
                                  let uu____64176 =
                                    let uu____64181 =
                                      norm1 (FStar_Util.Inl fv_lid1)  in
                                    FStar_Syntax_Syntax.mk_Tm_app uu____64181
                                      args
                                     in
                                  uu____64176 FStar_Pervasives_Native.None
                                    rng)
                              in
                           FStar_Pervasives_Native.Some uu____64166  in
                         let uu____64227 =
                           let uu____64230 =
                             let uu____64233 = unembed ea x  in
                             uu____64233 true norm1  in
                           FStar_Util.map_opt uu____64230
                             (fun x1  ->
                                let uu____64273 =
                                  let uu____64280 = f x1  in
                                  embed eb uu____64280  in
                                uu____64273 rng shadow_app norm1)
                            in
                         (match uu____64227 with
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
                  let uu____64410 = FStar_List.splitAt n_tvars args  in
                  match uu____64410 with
                  | (_tvar_args,rest_args) ->
                      let uu____64473 = FStar_List.hd rest_args  in
                      (match uu____64473 with
                       | (x,uu____64489) ->
                           let uu____64494 =
                             let uu____64501 = FStar_List.tl rest_args  in
                             FStar_List.hd uu____64501  in
                           (match uu____64494 with
                            | (y,uu____64525) ->
                                let shadow_app =
                                  let uu____64535 =
                                    FStar_Common.mk_thunk
                                      (fun uu____64544  ->
                                         let uu____64545 =
                                           let uu____64550 =
                                             norm1 (FStar_Util.Inl fv_lid1)
                                              in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____64550 args
                                            in
                                         uu____64545
                                           FStar_Pervasives_Native.None rng)
                                     in
                                  FStar_Pervasives_Native.Some uu____64535
                                   in
                                let uu____64596 =
                                  let uu____64599 =
                                    let uu____64602 = unembed ea x  in
                                    uu____64602 true norm1  in
                                  FStar_Util.bind_opt uu____64599
                                    (fun x1  ->
                                       let uu____64619 =
                                         let uu____64622 = unembed eb y  in
                                         uu____64622 true norm1  in
                                       FStar_Util.bind_opt uu____64619
                                         (fun y1  ->
                                            let uu____64639 =
                                              let uu____64640 =
                                                let uu____64647 = f x1 y1  in
                                                embed ec uu____64647  in
                                              uu____64640 rng shadow_app
                                                norm1
                                               in
                                            FStar_Pervasives_Native.Some
                                              uu____64639))
                                   in
                                (match uu____64596 with
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
                    let uu____64796 = FStar_List.splitAt n_tvars args  in
                    match uu____64796 with
                    | (_tvar_args,rest_args) ->
                        let uu____64859 = FStar_List.hd rest_args  in
                        (match uu____64859 with
                         | (x,uu____64875) ->
                             let uu____64880 =
                               let uu____64887 = FStar_List.tl rest_args  in
                               FStar_List.hd uu____64887  in
                             (match uu____64880 with
                              | (y,uu____64911) ->
                                  let uu____64916 =
                                    let uu____64923 =
                                      let uu____64932 =
                                        FStar_List.tl rest_args  in
                                      FStar_List.tl uu____64932  in
                                    FStar_List.hd uu____64923  in
                                  (match uu____64916 with
                                   | (z,uu____64962) ->
                                       let shadow_app =
                                         let uu____64972 =
                                           FStar_Common.mk_thunk
                                             (fun uu____64981  ->
                                                let uu____64982 =
                                                  let uu____64987 =
                                                    norm1
                                                      (FStar_Util.Inl fv_lid1)
                                                     in
                                                  FStar_Syntax_Syntax.mk_Tm_app
                                                    uu____64987 args
                                                   in
                                                uu____64982
                                                  FStar_Pervasives_Native.None
                                                  rng)
                                            in
                                         FStar_Pervasives_Native.Some
                                           uu____64972
                                          in
                                       let uu____65033 =
                                         let uu____65036 =
                                           let uu____65039 = unembed ea x  in
                                           uu____65039 true norm1  in
                                         FStar_Util.bind_opt uu____65036
                                           (fun x1  ->
                                              let uu____65056 =
                                                let uu____65059 =
                                                  unembed eb y  in
                                                uu____65059 true norm1  in
                                              FStar_Util.bind_opt uu____65056
                                                (fun y1  ->
                                                   let uu____65076 =
                                                     let uu____65079 =
                                                       unembed ec z  in
                                                     uu____65079 true norm1
                                                      in
                                                   FStar_Util.bind_opt
                                                     uu____65076
                                                     (fun z1  ->
                                                        let uu____65096 =
                                                          let uu____65097 =
                                                            let uu____65104 =
                                                              f x1 y1 z1  in
                                                            embed ed
                                                              uu____65104
                                                             in
                                                          uu____65097 rng
                                                            shadow_app norm1
                                                           in
                                                        FStar_Pervasives_Native.Some
                                                          uu____65096)))
                                          in
                                       (match uu____65033 with
                                        | FStar_Pervasives_Native.Some x1 ->
                                            FStar_Pervasives_Native.Some x1
                                        | FStar_Pervasives_Native.None  ->
                                            force_shadow shadow_app))))
                     in
                  f_wrapped
  
let debug_wrap : 'a . Prims.string -> (unit -> 'a) -> 'a =
  fun s  ->
    fun f  ->
      (let uu____65159 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
       if uu____65159 then FStar_Util.print1 "++++starting %s\n" s else ());
      (let res = f ()  in
       (let uu____65188 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
        if uu____65188 then FStar_Util.print1 "------ending %s\n" s else ());
       res)
  