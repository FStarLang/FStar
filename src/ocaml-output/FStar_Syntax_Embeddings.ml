open Prims
type norm_cb =
  (FStar_Ident.lid, FStar_Syntax_Syntax.term) FStar_Pervasives.either ->
    FStar_Syntax_Syntax.term
let (id_norm_cb : norm_cb) =
  fun uu___ ->
    match uu___ with
    | FStar_Pervasives.Inr x -> x
    | FStar_Pervasives.Inl l ->
        let uu___1 =
          FStar_Syntax_Syntax.lid_as_fv l
            FStar_Syntax_Syntax.delta_equational FStar_Pervasives_Native.None in
        FStar_Syntax_Syntax.fv_to_tm uu___1
exception Embedding_failure 
let (uu___is_Embedding_failure : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | Embedding_failure -> true | uu___ -> false
exception Unembedding_failure 
let (uu___is_Unembedding_failure : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | Unembedding_failure -> true | uu___ -> false
type shadow_term =
  FStar_Syntax_Syntax.term FStar_Thunk.t FStar_Pervasives_Native.option
let (map_shadow :
  shadow_term ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> shadow_term)
  = fun s -> fun f -> FStar_Util.map_opt s (FStar_Thunk.map f)
let (force_shadow :
  shadow_term -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option) =
  fun s -> FStar_Util.map_opt s FStar_Thunk.force
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
  fun projectee ->
    match projectee with | { em; un; typ; print; emb_typ;_} -> em
let __proj__Mkembedding__item__un :
  'a . 'a embedding -> FStar_Syntax_Syntax.term -> 'a unembed_t =
  fun projectee ->
    match projectee with | { em; un; typ; print; emb_typ;_} -> un
let __proj__Mkembedding__item__typ :
  'a . 'a embedding -> FStar_Syntax_Syntax.typ =
  fun projectee ->
    match projectee with | { em; un; typ; print; emb_typ;_} -> typ
let __proj__Mkembedding__item__print : 'a . 'a embedding -> 'a printer =
  fun projectee ->
    match projectee with | { em; un; typ; print; emb_typ;_} -> print
let __proj__Mkembedding__item__emb_typ :
  'a . 'a embedding -> FStar_Syntax_Syntax.emb_typ =
  fun projectee ->
    match projectee with | { em; un; typ; print; emb_typ;_} -> emb_typ
let emb_typ_of : 'a . 'a embedding -> FStar_Syntax_Syntax.emb_typ =
  fun e -> e.emb_typ
let unknown_printer :
  'uuuuu . FStar_Syntax_Syntax.term -> 'uuuuu -> Prims.string =
  fun typ ->
    fun uu___ ->
      let uu___1 = FStar_Syntax_Print.term_to_string typ in
      FStar_Util.format1 "unknown %s" uu___1
let (term_as_fv : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.fv) =
  fun t ->
    let uu___ =
      let uu___1 = FStar_Syntax_Subst.compress t in
      uu___1.FStar_Syntax_Syntax.n in
    match uu___ with
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv
    | uu___1 ->
        let uu___2 =
          let uu___3 = FStar_Syntax_Print.term_to_string t in
          FStar_Util.format1 "Embeddings not defined for type %s" uu___3 in
        failwith uu___2
let mk_emb :
  'a .
    'a raw_embedder ->
      'a raw_unembedder -> FStar_Syntax_Syntax.fv -> 'a embedding
  =
  fun em ->
    fun un ->
      fun fv ->
        let typ = FStar_Syntax_Syntax.fv_to_tm fv in
        let uu___ =
          let uu___1 =
            let uu___2 =
              let uu___3 = FStar_Syntax_Syntax.lid_of_fv fv in
              FStar_All.pipe_right uu___3 FStar_Ident.string_of_lid in
            (uu___2, []) in
          FStar_Syntax_Syntax.ET_app uu___1 in
        { em; un; typ; print = (unknown_printer typ); emb_typ = uu___ }
let mk_emb_full :
  'a .
    'a raw_embedder ->
      'a raw_unembedder ->
        FStar_Syntax_Syntax.typ ->
          ('a -> Prims.string) -> FStar_Syntax_Syntax.emb_typ -> 'a embedding
  =
  fun em ->
    fun un ->
      fun typ ->
        fun printer1 ->
          fun emb_typ -> { em; un; typ; print = printer1; emb_typ }
let embed : 'a . 'a embedding -> 'a -> embed_t = fun e -> fun x -> e.em x
let unembed : 'a . 'a embedding -> FStar_Syntax_Syntax.term -> 'a unembed_t =
  fun e -> fun t -> e.un t
let warn_unembed :
  'a .
    'a embedding ->
      FStar_Syntax_Syntax.term ->
        norm_cb -> 'a FStar_Pervasives_Native.option
  = fun e -> fun t -> fun n -> let uu___ = unembed e t in uu___ true n
let try_unembed :
  'a .
    'a embedding ->
      FStar_Syntax_Syntax.term ->
        norm_cb -> 'a FStar_Pervasives_Native.option
  = fun e -> fun t -> fun n -> let uu___ = unembed e t in uu___ false n
let type_of : 'a . 'a embedding -> FStar_Syntax_Syntax.typ = fun e -> e.typ
let set_type : 'a . FStar_Syntax_Syntax.typ -> 'a embedding -> 'a embedding =
  fun ty ->
    fun e ->
      let uu___ = e in
      {
        em = (uu___.em);
        un = (uu___.un);
        typ = ty;
        print = (uu___.print);
        emb_typ = (uu___.emb_typ)
      }
let embed_as :
  'a 'b .
    'a embedding ->
      ('a -> 'b) ->
        ('b -> 'a) ->
          FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
            'b embedding
  =
  fun ea ->
    fun ab ->
      fun ba ->
        fun o ->
          let uu___ =
            match o with
            | FStar_Pervasives_Native.Some t -> t
            | uu___1 -> type_of ea in
          mk_emb_full (fun x -> let uu___1 = ba x in embed ea uu___1)
            (fun t ->
               fun w ->
                 fun cb ->
                   let uu___1 = let uu___2 = unembed ea t in uu___2 w cb in
                   FStar_Util.map_opt uu___1 ab) uu___
            (fun x ->
               let uu___1 = let uu___2 = ba x in ea.print uu___2 in
               FStar_Util.format1 "(embed_as>> %s)\n" uu___1) ea.emb_typ
let lazy_embed :
  'a .
    'a printer ->
      FStar_Syntax_Syntax.emb_typ ->
        FStar_Range.range ->
          FStar_Syntax_Syntax.term ->
            'a ->
              (unit -> FStar_Syntax_Syntax.term) -> FStar_Syntax_Syntax.term
  =
  fun pa ->
    fun et ->
      fun rng ->
        fun ta ->
          fun x ->
            fun f ->
              (let uu___1 = FStar_ST.op_Bang FStar_Options.debug_embedding in
               if uu___1
               then
                 let uu___2 = FStar_Syntax_Print.term_to_string ta in
                 let uu___3 = FStar_Syntax_Print.emb_typ_to_string et in
                 let uu___4 = pa x in
                 FStar_Util.print3
                   "Embedding a %s\n\temb_typ=%s\n\tvalue is %s\n" uu___2
                   uu___3 uu___4
               else ());
              (let uu___1 = FStar_ST.op_Bang FStar_Options.eager_embedding in
               if uu___1
               then f ()
               else
                 (let thunk = FStar_Thunk.mk f in
                  FStar_Syntax_Util.mk_lazy x FStar_Syntax_Syntax.tun
                    (FStar_Syntax_Syntax.Lazy_embedding (et, thunk))
                    (FStar_Pervasives_Native.Some rng)))
let lazy_unembed :
  'a .
    'a printer ->
      FStar_Syntax_Syntax.emb_typ ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.term ->
            (FStar_Syntax_Syntax.term -> 'a FStar_Pervasives_Native.option)
              -> 'a FStar_Pervasives_Native.option
  =
  fun pa ->
    fun et ->
      fun x ->
        fun ta ->
          fun f ->
            let x1 = FStar_Syntax_Subst.compress x in
            match x1.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_lazy
                { FStar_Syntax_Syntax.blob = b;
                  FStar_Syntax_Syntax.lkind =
                    FStar_Syntax_Syntax.Lazy_embedding (et', t);
                  FStar_Syntax_Syntax.ltyp = uu___;
                  FStar_Syntax_Syntax.rng = uu___1;_}
                ->
                let uu___2 =
                  (et <> et') ||
                    (FStar_ST.op_Bang FStar_Options.eager_embedding) in
                if uu___2
                then
                  let res = let uu___3 = FStar_Thunk.force t in f uu___3 in
                  ((let uu___4 =
                      FStar_ST.op_Bang FStar_Options.debug_embedding in
                    if uu___4
                    then
                      let uu___5 = FStar_Syntax_Print.emb_typ_to_string et in
                      let uu___6 = FStar_Syntax_Print.emb_typ_to_string et' in
                      let uu___7 =
                        match res with
                        | FStar_Pervasives_Native.None -> "None"
                        | FStar_Pervasives_Native.Some x2 ->
                            let uu___8 = pa x2 in Prims.op_Hat "Some " uu___8 in
                      FStar_Util.print3
                        "Unembed cancellation failed\n\t%s <> %s\nvalue is %s\n"
                        uu___5 uu___6 uu___7
                    else ());
                   res)
                else
                  (let a1 = FStar_Dyn.undyn b in
                   (let uu___5 =
                      FStar_ST.op_Bang FStar_Options.debug_embedding in
                    if uu___5
                    then
                      let uu___6 = FStar_Syntax_Print.emb_typ_to_string et in
                      let uu___7 = pa a1 in
                      FStar_Util.print2
                        "Unembed cancelled for %s\n\tvalue is %s\n" uu___6
                        uu___7
                    else ());
                   FStar_Pervasives_Native.Some a1)
            | uu___ ->
                let aopt = f x1 in
                ((let uu___2 = FStar_ST.op_Bang FStar_Options.debug_embedding in
                  if uu___2
                  then
                    let uu___3 = FStar_Syntax_Print.emb_typ_to_string et in
                    let uu___4 = FStar_Syntax_Print.term_to_string x1 in
                    let uu___5 =
                      match aopt with
                      | FStar_Pervasives_Native.None -> "None"
                      | FStar_Pervasives_Native.Some a1 ->
                          let uu___6 = pa a1 in Prims.op_Hat "Some " uu___6 in
                    FStar_Util.print3
                      "Unembedding:\n\temb_typ=%s\n\tterm is %s\n\tvalue is %s\n"
                      uu___3 uu___4 uu___5
                  else ());
                 aopt)
let (mk_any_emb :
  FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term embedding) =
  fun typ ->
    let em t _r _topt _norm =
      (let uu___1 = FStar_ST.op_Bang FStar_Options.debug_embedding in
       if uu___1
       then
         let uu___2 = unknown_printer typ t in
         FStar_Util.print1 "Embedding abstract: %s\n" uu___2
       else ());
      t in
    let un t _w _n =
      (let uu___1 = FStar_ST.op_Bang FStar_Options.debug_embedding in
       if uu___1
       then
         let uu___2 = unknown_printer typ t in
         FStar_Util.print1 "Unembedding abstract: %s\n" uu___2
       else ());
      FStar_Pervasives_Native.Some t in
    mk_emb_full em un typ (unknown_printer typ)
      FStar_Syntax_Syntax.ET_abstract
let (e_any : FStar_Syntax_Syntax.term embedding) =
  let em t _r _topt _norm = t in
  let un t _w _n = FStar_Pervasives_Native.Some t in
  let uu___ =
    let uu___1 =
      let uu___2 =
        FStar_All.pipe_right FStar_Parser_Const.term_lid
          FStar_Ident.string_of_lid in
      (uu___2, []) in
    FStar_Syntax_Syntax.ET_app uu___1 in
  mk_emb_full em un FStar_Syntax_Syntax.t_term
    FStar_Syntax_Print.term_to_string uu___
let (e_unit : unit embedding) =
  let em u rng _topt _norm =
    let uu___ = FStar_Syntax_Util.exp_unit in
    {
      FStar_Syntax_Syntax.n = (uu___.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___.FStar_Syntax_Syntax.vars)
    } in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unascribe t0 in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit) ->
        FStar_Pervasives_Native.Some ()
    | uu___ ->
        (if w
         then
           (let uu___2 =
              let uu___3 =
                let uu___4 = FStar_Syntax_Print.term_to_string t in
                FStar_Util.format1 "Not an embedded unit: %s" uu___4 in
              (FStar_Errors.Warning_NotEmbedded, uu___3) in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu___2)
         else ();
         FStar_Pervasives_Native.None) in
  let uu___ =
    let uu___1 =
      let uu___2 =
        FStar_All.pipe_right FStar_Parser_Const.unit_lid
          FStar_Ident.string_of_lid in
      (uu___2, []) in
    FStar_Syntax_Syntax.ET_app uu___1 in
  mk_emb_full em un FStar_Syntax_Syntax.t_unit (fun uu___1 -> "()") uu___
let (e_bool : Prims.bool embedding) =
  let em b rng _topt _norm =
    let t =
      if b
      then FStar_Syntax_Util.exp_true_bool
      else FStar_Syntax_Util.exp_false_bool in
    let uu___ = t in
    {
      FStar_Syntax_Syntax.n = (uu___.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___.FStar_Syntax_Syntax.vars)
    } in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0 in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) ->
        FStar_Pervasives_Native.Some b
    | uu___ ->
        (if w
         then
           (let uu___2 =
              let uu___3 =
                let uu___4 = FStar_Syntax_Print.term_to_string t0 in
                FStar_Util.format1 "Not an embedded bool: %s" uu___4 in
              (FStar_Errors.Warning_NotEmbedded, uu___3) in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu___2)
         else ();
         FStar_Pervasives_Native.None) in
  let uu___ =
    let uu___1 =
      let uu___2 =
        FStar_All.pipe_right FStar_Parser_Const.bool_lid
          FStar_Ident.string_of_lid in
      (uu___2, []) in
    FStar_Syntax_Syntax.ET_app uu___1 in
  mk_emb_full em un FStar_Syntax_Syntax.t_bool FStar_Util.string_of_bool
    uu___
let (e_char : FStar_Char.char embedding) =
  let em c rng _topt _norm =
    let t = FStar_Syntax_Util.exp_char c in
    let uu___ = t in
    {
      FStar_Syntax_Syntax.n = (uu___.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___.FStar_Syntax_Syntax.vars)
    } in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0 in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c) ->
        FStar_Pervasives_Native.Some c
    | uu___ ->
        (if w
         then
           (let uu___2 =
              let uu___3 =
                let uu___4 = FStar_Syntax_Print.term_to_string t0 in
                FStar_Util.format1 "Not an embedded char: %s" uu___4 in
              (FStar_Errors.Warning_NotEmbedded, uu___3) in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu___2)
         else ();
         FStar_Pervasives_Native.None) in
  let uu___ =
    let uu___1 =
      let uu___2 =
        FStar_All.pipe_right FStar_Parser_Const.char_lid
          FStar_Ident.string_of_lid in
      (uu___2, []) in
    FStar_Syntax_Syntax.ET_app uu___1 in
  mk_emb_full em un FStar_Syntax_Syntax.t_char FStar_Util.string_of_char
    uu___
let (e_int : FStar_BigInt.t embedding) =
  let t_int = FStar_Syntax_Util.fvar_const FStar_Parser_Const.int_lid in
  let emb_t_int =
    let uu___ =
      let uu___1 =
        FStar_All.pipe_right FStar_Parser_Const.int_lid
          FStar_Ident.string_of_lid in
      (uu___1, []) in
    FStar_Syntax_Syntax.ET_app uu___ in
  let em i rng _topt _norm =
    lazy_embed FStar_BigInt.string_of_big_int emb_t_int rng t_int i
      (fun uu___ ->
         let uu___1 = FStar_BigInt.string_of_big_int i in
         FStar_Syntax_Util.exp_int uu___1) in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0 in
    lazy_unembed FStar_BigInt.string_of_big_int emb_t_int t t_int
      (fun t1 ->
         match t1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (s, uu___))
             ->
             let uu___1 = FStar_BigInt.big_int_of_string s in
             FStar_Pervasives_Native.Some uu___1
         | uu___ ->
             (if w
              then
                (let uu___2 =
                   let uu___3 =
                     let uu___4 = FStar_Syntax_Print.term_to_string t0 in
                     FStar_Util.format1 "Not an embedded int: %s" uu___4 in
                   (FStar_Errors.Warning_NotEmbedded, uu___3) in
                 FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu___2)
              else ();
              FStar_Pervasives_Native.None)) in
  mk_emb_full em un FStar_Syntax_Syntax.t_int FStar_BigInt.string_of_big_int
    emb_t_int
let (e_fsint : Prims.int embedding) =
  embed_as e_int FStar_BigInt.to_int_fs FStar_BigInt.of_int_fs
    FStar_Pervasives_Native.None
let (e_string : Prims.string embedding) =
  let emb_t_string =
    let uu___ =
      let uu___1 =
        FStar_All.pipe_right FStar_Parser_Const.string_lid
          FStar_Ident.string_of_lid in
      (uu___1, []) in
    FStar_Syntax_Syntax.ET_app uu___ in
  let em s rng _topt _norm =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, rng)))
      rng in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0 in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, uu___))
        -> FStar_Pervasives_Native.Some s
    | uu___ ->
        (if w
         then
           (let uu___2 =
              let uu___3 =
                let uu___4 = FStar_Syntax_Print.term_to_string t0 in
                FStar_Util.format1 "Not an embedded string: %s" uu___4 in
              (FStar_Errors.Warning_NotEmbedded, uu___3) in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu___2)
         else ();
         FStar_Pervasives_Native.None) in
  mk_emb_full em un FStar_Syntax_Syntax.t_string
    (fun x -> Prims.op_Hat "\"" (Prims.op_Hat x "\"")) emb_t_string
let e_option :
  'a . 'a embedding -> 'a FStar_Pervasives_Native.option embedding =
  fun ea ->
    let t_option_a =
      let t_opt = FStar_Syntax_Util.fvar_const FStar_Parser_Const.option_lid in
      let uu___ = let uu___1 = FStar_Syntax_Syntax.as_arg ea.typ in [uu___1] in
      FStar_Syntax_Syntax.mk_Tm_app t_opt uu___ FStar_Range.dummyRange in
    let emb_t_option_a =
      let uu___ =
        let uu___1 =
          FStar_All.pipe_right FStar_Parser_Const.option_lid
            FStar_Ident.string_of_lid in
        (uu___1, [ea.emb_typ]) in
      FStar_Syntax_Syntax.ET_app uu___ in
    let printer1 uu___ =
      match uu___ with
      | FStar_Pervasives_Native.None -> "None"
      | FStar_Pervasives_Native.Some x ->
          let uu___1 = let uu___2 = ea.print x in Prims.op_Hat uu___2 ")" in
          Prims.op_Hat "(Some " uu___1 in
    let em o rng topt norm =
      lazy_embed printer1 emb_t_option_a rng t_option_a o
        (fun uu___ ->
           match o with
           | FStar_Pervasives_Native.None ->
               let uu___1 =
                 let uu___2 =
                   FStar_Syntax_Syntax.tdataconstr
                     FStar_Parser_Const.none_lid in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu___2
                   [FStar_Syntax_Syntax.U_zero] in
               let uu___2 =
                 let uu___3 =
                   let uu___4 = type_of ea in FStar_Syntax_Syntax.iarg uu___4 in
                 [uu___3] in
               FStar_Syntax_Syntax.mk_Tm_app uu___1 uu___2 rng
           | FStar_Pervasives_Native.Some a1 ->
               let shadow_a =
                 map_shadow topt
                   (fun t ->
                      let v = FStar_Ident.mk_ident ("v", rng) in
                      let some_v =
                        FStar_Syntax_Util.mk_field_projector_name_from_ident
                          FStar_Parser_Const.some_lid v in
                      let some_v_tm =
                        let uu___1 =
                          FStar_Syntax_Syntax.lid_as_fv some_v
                            FStar_Syntax_Syntax.delta_equational
                            FStar_Pervasives_Native.None in
                        FStar_Syntax_Syntax.fv_to_tm uu___1 in
                      let uu___1 =
                        FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm
                          [FStar_Syntax_Syntax.U_zero] in
                      let uu___2 =
                        let uu___3 =
                          let uu___4 = type_of ea in
                          FStar_Syntax_Syntax.iarg uu___4 in
                        let uu___4 =
                          let uu___5 = FStar_Syntax_Syntax.as_arg t in
                          [uu___5] in
                        uu___3 :: uu___4 in
                      FStar_Syntax_Syntax.mk_Tm_app uu___1 uu___2 rng) in
               let uu___1 =
                 let uu___2 =
                   FStar_Syntax_Syntax.tdataconstr
                     FStar_Parser_Const.some_lid in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu___2
                   [FStar_Syntax_Syntax.U_zero] in
               let uu___2 =
                 let uu___3 =
                   let uu___4 = type_of ea in FStar_Syntax_Syntax.iarg uu___4 in
                 let uu___4 =
                   let uu___5 =
                     let uu___6 =
                       let uu___7 = embed ea a1 in uu___7 rng shadow_a norm in
                     FStar_Syntax_Syntax.as_arg uu___6 in
                   [uu___5] in
                 uu___3 :: uu___4 in
               FStar_Syntax_Syntax.mk_Tm_app uu___1 uu___2 rng) in
    let un t0 w norm =
      let t = FStar_Syntax_Util.unmeta_safe t0 in
      lazy_unembed printer1 emb_t_option_a t t_option_a
        (fun t1 ->
           let uu___ = FStar_Syntax_Util.head_and_args_full t1 in
           match uu___ with
           | (hd, args) ->
               let uu___1 =
                 let uu___2 =
                   let uu___3 = FStar_Syntax_Util.un_uinst hd in
                   uu___3.FStar_Syntax_Syntax.n in
                 (uu___2, args) in
               (match uu___1 with
                | (FStar_Syntax_Syntax.Tm_fvar fv, uu___2) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.none_lid
                    ->
                    FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
                | (FStar_Syntax_Syntax.Tm_fvar fv, uu___2::(a1, uu___3)::[])
                    when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.some_lid
                    ->
                    let uu___4 = let uu___5 = unembed ea a1 in uu___5 w norm in
                    FStar_Util.bind_opt uu___4
                      (fun a2 ->
                         FStar_Pervasives_Native.Some
                           (FStar_Pervasives_Native.Some a2))
                | uu___2 ->
                    (if w
                     then
                       (let uu___4 =
                          let uu___5 =
                            let uu___6 = FStar_Syntax_Print.term_to_string t0 in
                            FStar_Util.format1 "Not an embedded option: %s"
                              uu___6 in
                          (FStar_Errors.Warning_NotEmbedded, uu___5) in
                        FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                          uu___4)
                     else ();
                     FStar_Pervasives_Native.None))) in
    let uu___ =
      let uu___1 = type_of ea in FStar_Syntax_Syntax.t_option_of uu___1 in
    mk_emb_full em un uu___ printer1 emb_t_option_a
let e_tuple2 : 'a 'b . 'a embedding -> 'b embedding -> ('a * 'b) embedding =
  fun ea ->
    fun eb ->
      let t_pair_a_b =
        let t_tup2 =
          FStar_Syntax_Util.fvar_const FStar_Parser_Const.lid_tuple2 in
        let uu___ =
          let uu___1 = FStar_Syntax_Syntax.as_arg ea.typ in
          let uu___2 =
            let uu___3 = FStar_Syntax_Syntax.as_arg eb.typ in [uu___3] in
          uu___1 :: uu___2 in
        FStar_Syntax_Syntax.mk_Tm_app t_tup2 uu___ FStar_Range.dummyRange in
      let emb_t_pair_a_b =
        let uu___ =
          let uu___1 =
            FStar_All.pipe_right FStar_Parser_Const.lid_tuple2
              FStar_Ident.string_of_lid in
          (uu___1, [ea.emb_typ; eb.emb_typ]) in
        FStar_Syntax_Syntax.ET_app uu___ in
      let printer1 uu___ =
        match uu___ with
        | (x, y) ->
            let uu___1 = ea.print x in
            let uu___2 = eb.print y in
            FStar_Util.format2 "(%s, %s)" uu___1 uu___2 in
      let em x rng topt norm =
        lazy_embed printer1 emb_t_pair_a_b rng t_pair_a_b x
          (fun uu___ ->
             let proj i ab =
               let proj_1 =
                 let uu___1 =
                   FStar_Parser_Const.mk_tuple_data_lid (Prims.of_int (2))
                     rng in
                 let uu___2 =
                   FStar_Syntax_Syntax.null_bv FStar_Syntax_Syntax.tun in
                 FStar_Syntax_Util.mk_field_projector_name uu___1 uu___2 i in
               let proj_1_tm =
                 let uu___1 =
                   FStar_Syntax_Syntax.lid_as_fv proj_1
                     FStar_Syntax_Syntax.delta_equational
                     FStar_Pervasives_Native.None in
                 FStar_Syntax_Syntax.fv_to_tm uu___1 in
               let uu___1 =
                 FStar_Syntax_Syntax.mk_Tm_uinst proj_1_tm
                   [FStar_Syntax_Syntax.U_zero] in
               let uu___2 =
                 let uu___3 =
                   let uu___4 = type_of ea in FStar_Syntax_Syntax.iarg uu___4 in
                 let uu___4 =
                   let uu___5 =
                     let uu___6 = type_of eb in
                     FStar_Syntax_Syntax.iarg uu___6 in
                   let uu___6 =
                     let uu___7 = FStar_Syntax_Syntax.as_arg ab in [uu___7] in
                   uu___5 :: uu___6 in
                 uu___3 :: uu___4 in
               FStar_Syntax_Syntax.mk_Tm_app uu___1 uu___2 rng in
             let shadow_a = map_shadow topt (proj Prims.int_one) in
             let shadow_b = map_shadow topt (proj (Prims.of_int (2))) in
             let uu___1 =
               let uu___2 =
                 FStar_Syntax_Syntax.tdataconstr
                   FStar_Parser_Const.lid_Mktuple2 in
               FStar_Syntax_Syntax.mk_Tm_uinst uu___2
                 [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] in
             let uu___2 =
               let uu___3 =
                 let uu___4 = type_of ea in FStar_Syntax_Syntax.iarg uu___4 in
               let uu___4 =
                 let uu___5 =
                   let uu___6 = type_of eb in FStar_Syntax_Syntax.iarg uu___6 in
                 let uu___6 =
                   let uu___7 =
                     let uu___8 =
                       let uu___9 = embed ea (FStar_Pervasives_Native.fst x) in
                       uu___9 rng shadow_a norm in
                     FStar_Syntax_Syntax.as_arg uu___8 in
                   let uu___8 =
                     let uu___9 =
                       let uu___10 =
                         let uu___11 =
                           embed eb (FStar_Pervasives_Native.snd x) in
                         uu___11 rng shadow_b norm in
                       FStar_Syntax_Syntax.as_arg uu___10 in
                     [uu___9] in
                   uu___7 :: uu___8 in
                 uu___5 :: uu___6 in
               uu___3 :: uu___4 in
             FStar_Syntax_Syntax.mk_Tm_app uu___1 uu___2 rng) in
      let un t0 w norm =
        let t = FStar_Syntax_Util.unmeta_safe t0 in
        lazy_unembed printer1 emb_t_pair_a_b t t_pair_a_b
          (fun t1 ->
             let uu___ = FStar_Syntax_Util.head_and_args_full t1 in
             match uu___ with
             | (hd, args) ->
                 let uu___1 =
                   let uu___2 =
                     let uu___3 = FStar_Syntax_Util.un_uinst hd in
                     uu___3.FStar_Syntax_Syntax.n in
                   (uu___2, args) in
                 (match uu___1 with
                  | (FStar_Syntax_Syntax.Tm_fvar fv,
                     uu___2::uu___3::(a1, uu___4)::(b1, uu___5)::[]) when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.lid_Mktuple2
                      ->
                      let uu___6 =
                        let uu___7 = unembed ea a1 in uu___7 w norm in
                      FStar_Util.bind_opt uu___6
                        (fun a2 ->
                           let uu___7 =
                             let uu___8 = unembed eb b1 in uu___8 w norm in
                           FStar_Util.bind_opt uu___7
                             (fun b2 -> FStar_Pervasives_Native.Some (a2, b2)))
                  | uu___2 ->
                      (if w
                       then
                         (let uu___4 =
                            let uu___5 =
                              let uu___6 =
                                FStar_Syntax_Print.term_to_string t0 in
                              FStar_Util.format1 "Not an embedded pair: %s"
                                uu___6 in
                            (FStar_Errors.Warning_NotEmbedded, uu___5) in
                          FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                            uu___4)
                       else ();
                       FStar_Pervasives_Native.None))) in
      let uu___ =
        let uu___1 = type_of ea in
        let uu___2 = type_of eb in
        FStar_Syntax_Syntax.t_tuple2_of uu___1 uu___2 in
      mk_emb_full em un uu___ printer1 emb_t_pair_a_b
let e_either :
  'a 'b .
    'a embedding ->
      'b embedding -> ('a, 'b) FStar_Pervasives.either embedding
  =
  fun ea ->
    fun eb ->
      let t_sum_a_b =
        let t_either =
          FStar_Syntax_Util.fvar_const FStar_Parser_Const.either_lid in
        let uu___ =
          let uu___1 = FStar_Syntax_Syntax.as_arg ea.typ in
          let uu___2 =
            let uu___3 = FStar_Syntax_Syntax.as_arg eb.typ in [uu___3] in
          uu___1 :: uu___2 in
        FStar_Syntax_Syntax.mk_Tm_app t_either uu___ FStar_Range.dummyRange in
      let emb_t_sum_a_b =
        let uu___ =
          let uu___1 =
            FStar_All.pipe_right FStar_Parser_Const.either_lid
              FStar_Ident.string_of_lid in
          (uu___1, [ea.emb_typ; eb.emb_typ]) in
        FStar_Syntax_Syntax.ET_app uu___ in
      let printer1 s =
        match s with
        | FStar_Pervasives.Inl a1 ->
            let uu___ = ea.print a1 in FStar_Util.format1 "Inl %s" uu___
        | FStar_Pervasives.Inr b1 ->
            let uu___ = eb.print b1 in FStar_Util.format1 "Inr %s" uu___ in
      let em s rng topt norm =
        lazy_embed printer1 emb_t_sum_a_b rng t_sum_a_b s
          (match s with
           | FStar_Pervasives.Inl a1 ->
               (fun uu___ ->
                  let shadow_a =
                    map_shadow topt
                      (fun t ->
                         let v = FStar_Ident.mk_ident ("v", rng) in
                         let some_v =
                           FStar_Syntax_Util.mk_field_projector_name_from_ident
                             FStar_Parser_Const.inl_lid v in
                         let some_v_tm =
                           let uu___1 =
                             FStar_Syntax_Syntax.lid_as_fv some_v
                               FStar_Syntax_Syntax.delta_equational
                               FStar_Pervasives_Native.None in
                           FStar_Syntax_Syntax.fv_to_tm uu___1 in
                         let uu___1 =
                           FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm
                             [FStar_Syntax_Syntax.U_zero] in
                         let uu___2 =
                           let uu___3 =
                             let uu___4 = type_of ea in
                             FStar_Syntax_Syntax.iarg uu___4 in
                           let uu___4 =
                             let uu___5 =
                               let uu___6 = type_of eb in
                               FStar_Syntax_Syntax.iarg uu___6 in
                             let uu___6 =
                               let uu___7 = FStar_Syntax_Syntax.as_arg t in
                               [uu___7] in
                             uu___5 :: uu___6 in
                           uu___3 :: uu___4 in
                         FStar_Syntax_Syntax.mk_Tm_app uu___1 uu___2 rng) in
                  let uu___1 =
                    let uu___2 =
                      FStar_Syntax_Syntax.tdataconstr
                        FStar_Parser_Const.inl_lid in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu___2
                      [FStar_Syntax_Syntax.U_zero;
                      FStar_Syntax_Syntax.U_zero] in
                  let uu___2 =
                    let uu___3 =
                      let uu___4 = type_of ea in
                      FStar_Syntax_Syntax.iarg uu___4 in
                    let uu___4 =
                      let uu___5 =
                        let uu___6 = type_of eb in
                        FStar_Syntax_Syntax.iarg uu___6 in
                      let uu___6 =
                        let uu___7 =
                          let uu___8 =
                            let uu___9 = embed ea a1 in
                            uu___9 rng shadow_a norm in
                          FStar_Syntax_Syntax.as_arg uu___8 in
                        [uu___7] in
                      uu___5 :: uu___6 in
                    uu___3 :: uu___4 in
                  FStar_Syntax_Syntax.mk_Tm_app uu___1 uu___2 rng)
           | FStar_Pervasives.Inr b1 ->
               (fun uu___ ->
                  let shadow_b =
                    map_shadow topt
                      (fun t ->
                         let v = FStar_Ident.mk_ident ("v", rng) in
                         let some_v =
                           FStar_Syntax_Util.mk_field_projector_name_from_ident
                             FStar_Parser_Const.inr_lid v in
                         let some_v_tm =
                           let uu___1 =
                             FStar_Syntax_Syntax.lid_as_fv some_v
                               FStar_Syntax_Syntax.delta_equational
                               FStar_Pervasives_Native.None in
                           FStar_Syntax_Syntax.fv_to_tm uu___1 in
                         let uu___1 =
                           FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm
                             [FStar_Syntax_Syntax.U_zero] in
                         let uu___2 =
                           let uu___3 =
                             let uu___4 = type_of ea in
                             FStar_Syntax_Syntax.iarg uu___4 in
                           let uu___4 =
                             let uu___5 =
                               let uu___6 = type_of eb in
                               FStar_Syntax_Syntax.iarg uu___6 in
                             let uu___6 =
                               let uu___7 = FStar_Syntax_Syntax.as_arg t in
                               [uu___7] in
                             uu___5 :: uu___6 in
                           uu___3 :: uu___4 in
                         FStar_Syntax_Syntax.mk_Tm_app uu___1 uu___2 rng) in
                  let uu___1 =
                    let uu___2 =
                      FStar_Syntax_Syntax.tdataconstr
                        FStar_Parser_Const.inr_lid in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu___2
                      [FStar_Syntax_Syntax.U_zero;
                      FStar_Syntax_Syntax.U_zero] in
                  let uu___2 =
                    let uu___3 =
                      let uu___4 = type_of ea in
                      FStar_Syntax_Syntax.iarg uu___4 in
                    let uu___4 =
                      let uu___5 =
                        let uu___6 = type_of eb in
                        FStar_Syntax_Syntax.iarg uu___6 in
                      let uu___6 =
                        let uu___7 =
                          let uu___8 =
                            let uu___9 = embed eb b1 in
                            uu___9 rng shadow_b norm in
                          FStar_Syntax_Syntax.as_arg uu___8 in
                        [uu___7] in
                      uu___5 :: uu___6 in
                    uu___3 :: uu___4 in
                  FStar_Syntax_Syntax.mk_Tm_app uu___1 uu___2 rng)) in
      let un t0 w norm =
        let t = FStar_Syntax_Util.unmeta_safe t0 in
        lazy_unembed printer1 emb_t_sum_a_b t t_sum_a_b
          (fun t1 ->
             let uu___ = FStar_Syntax_Util.head_and_args_full t1 in
             match uu___ with
             | (hd, args) ->
                 let uu___1 =
                   let uu___2 =
                     let uu___3 = FStar_Syntax_Util.un_uinst hd in
                     uu___3.FStar_Syntax_Syntax.n in
                   (uu___2, args) in
                 (match uu___1 with
                  | (FStar_Syntax_Syntax.Tm_fvar fv,
                     uu___2::uu___3::(a1, uu___4)::[]) when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.inl_lid
                      ->
                      let uu___5 =
                        let uu___6 = unembed ea a1 in uu___6 w norm in
                      FStar_Util.bind_opt uu___5
                        (fun a2 ->
                           FStar_Pervasives_Native.Some
                             (FStar_Pervasives.Inl a2))
                  | (FStar_Syntax_Syntax.Tm_fvar fv,
                     uu___2::uu___3::(b1, uu___4)::[]) when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.inr_lid
                      ->
                      let uu___5 =
                        let uu___6 = unembed eb b1 in uu___6 w norm in
                      FStar_Util.bind_opt uu___5
                        (fun b2 ->
                           FStar_Pervasives_Native.Some
                             (FStar_Pervasives.Inr b2))
                  | uu___2 ->
                      (if w
                       then
                         (let uu___4 =
                            let uu___5 =
                              let uu___6 =
                                FStar_Syntax_Print.term_to_string t0 in
                              FStar_Util.format1 "Not an embedded sum: %s"
                                uu___6 in
                            (FStar_Errors.Warning_NotEmbedded, uu___5) in
                          FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                            uu___4)
                       else ();
                       FStar_Pervasives_Native.None))) in
      let uu___ =
        let uu___1 = type_of ea in
        let uu___2 = type_of eb in
        FStar_Syntax_Syntax.t_either_of uu___1 uu___2 in
      mk_emb_full em un uu___ printer1 emb_t_sum_a_b
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea ->
    let t_list_a =
      let t_list = FStar_Syntax_Util.fvar_const FStar_Parser_Const.list_lid in
      let uu___ = let uu___1 = FStar_Syntax_Syntax.as_arg ea.typ in [uu___1] in
      FStar_Syntax_Syntax.mk_Tm_app t_list uu___ FStar_Range.dummyRange in
    let emb_t_list_a =
      let uu___ =
        let uu___1 =
          FStar_All.pipe_right FStar_Parser_Const.list_lid
            FStar_Ident.string_of_lid in
        (uu___1, [ea.emb_typ]) in
      FStar_Syntax_Syntax.ET_app uu___ in
    let printer1 l =
      let uu___ =
        let uu___1 =
          let uu___2 = FStar_List.map ea.print l in
          FStar_All.pipe_right uu___2 (FStar_String.concat "; ") in
        Prims.op_Hat uu___1 "]" in
      Prims.op_Hat "[" uu___ in
    let rec em l rng shadow_l norm =
      lazy_embed printer1 emb_t_list_a rng t_list_a l
        (fun uu___ ->
           let t = let uu___1 = type_of ea in FStar_Syntax_Syntax.iarg uu___1 in
           match l with
           | [] ->
               let uu___1 =
                 let uu___2 =
                   FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.nil_lid in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu___2
                   [FStar_Syntax_Syntax.U_zero] in
               FStar_Syntax_Syntax.mk_Tm_app uu___1 [t] rng
           | hd::tl ->
               let cons =
                 let uu___1 =
                   FStar_Syntax_Syntax.tdataconstr
                     FStar_Parser_Const.cons_lid in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu___1
                   [FStar_Syntax_Syntax.U_zero] in
               let proj f cons_tm =
                 let fid = FStar_Ident.mk_ident (f, rng) in
                 let proj1 =
                   FStar_Syntax_Util.mk_field_projector_name_from_ident
                     FStar_Parser_Const.cons_lid fid in
                 let proj_tm =
                   let uu___1 =
                     FStar_Syntax_Syntax.lid_as_fv proj1
                       FStar_Syntax_Syntax.delta_equational
                       FStar_Pervasives_Native.None in
                   FStar_Syntax_Syntax.fv_to_tm uu___1 in
                 let uu___1 =
                   FStar_Syntax_Syntax.mk_Tm_uinst proj_tm
                     [FStar_Syntax_Syntax.U_zero] in
                 let uu___2 =
                   let uu___3 =
                     let uu___4 = type_of ea in
                     FStar_Syntax_Syntax.iarg uu___4 in
                   let uu___4 =
                     let uu___5 = FStar_Syntax_Syntax.as_arg cons_tm in
                     [uu___5] in
                   uu___3 :: uu___4 in
                 FStar_Syntax_Syntax.mk_Tm_app uu___1 uu___2 rng in
               let shadow_hd = map_shadow shadow_l (proj "hd") in
               let shadow_tl = map_shadow shadow_l (proj "tl") in
               let uu___1 =
                 let uu___2 =
                   let uu___3 =
                     let uu___4 =
                       let uu___5 = embed ea hd in uu___5 rng shadow_hd norm in
                     FStar_Syntax_Syntax.as_arg uu___4 in
                   let uu___4 =
                     let uu___5 =
                       let uu___6 = em tl rng shadow_tl norm in
                       FStar_Syntax_Syntax.as_arg uu___6 in
                     [uu___5] in
                   uu___3 :: uu___4 in
                 t :: uu___2 in
               FStar_Syntax_Syntax.mk_Tm_app cons uu___1 rng) in
    let rec un t0 w norm =
      let t = FStar_Syntax_Util.unmeta_safe t0 in
      lazy_unembed printer1 emb_t_list_a t t_list_a
        (fun t1 ->
           let uu___ = FStar_Syntax_Util.head_and_args_full t1 in
           match uu___ with
           | (hd, args) ->
               let uu___1 =
                 let uu___2 =
                   let uu___3 = FStar_Syntax_Util.un_uinst hd in
                   uu___3.FStar_Syntax_Syntax.n in
                 (uu___2, args) in
               (match uu___1 with
                | (FStar_Syntax_Syntax.Tm_fvar fv, uu___2) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.nil_lid
                    -> FStar_Pervasives_Native.Some []
                | (FStar_Syntax_Syntax.Tm_fvar fv,
                   (uu___2, FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Implicit uu___3))::(hd1,
                                                             FStar_Pervasives_Native.None)::
                   (tl, FStar_Pervasives_Native.None)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.cons_lid
                    ->
                    let uu___4 = let uu___5 = unembed ea hd1 in uu___5 w norm in
                    FStar_Util.bind_opt uu___4
                      (fun hd2 ->
                         let uu___5 = un tl w norm in
                         FStar_Util.bind_opt uu___5
                           (fun tl1 ->
                              FStar_Pervasives_Native.Some (hd2 :: tl1)))
                | (FStar_Syntax_Syntax.Tm_fvar fv,
                   (hd1, FStar_Pervasives_Native.None)::(tl,
                                                         FStar_Pervasives_Native.None)::[])
                    when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.cons_lid
                    ->
                    let uu___2 = let uu___3 = unembed ea hd1 in uu___3 w norm in
                    FStar_Util.bind_opt uu___2
                      (fun hd2 ->
                         let uu___3 = un tl w norm in
                         FStar_Util.bind_opt uu___3
                           (fun tl1 ->
                              FStar_Pervasives_Native.Some (hd2 :: tl1)))
                | uu___2 ->
                    (if w
                     then
                       (let uu___4 =
                          let uu___5 =
                            let uu___6 = FStar_Syntax_Print.term_to_string t0 in
                            FStar_Util.format1 "Not an embedded list: %s"
                              uu___6 in
                          (FStar_Errors.Warning_NotEmbedded, uu___5) in
                        FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                          uu___4)
                     else ();
                     FStar_Pervasives_Native.None))) in
    let uu___ =
      let uu___1 = type_of ea in FStar_Syntax_Syntax.t_list_of uu___1 in
    mk_emb_full em un uu___ printer1 emb_t_list_a
let (e_string_list : Prims.string Prims.list embedding) = e_list e_string
type norm_step =
  | Simpl 
  | Weak 
  | HNF 
  | Primops 
  | Delta 
  | Zeta 
  | ZetaFull 
  | Iota 
  | Reify 
  | UnfoldOnly of Prims.string Prims.list 
  | UnfoldFully of Prims.string Prims.list 
  | UnfoldAttr of Prims.string Prims.list 
  | UnfoldQual of Prims.string Prims.list 
  | NBE 
  | Unmeta 
let (uu___is_Simpl : norm_step -> Prims.bool) =
  fun projectee -> match projectee with | Simpl -> true | uu___ -> false
let (uu___is_Weak : norm_step -> Prims.bool) =
  fun projectee -> match projectee with | Weak -> true | uu___ -> false
let (uu___is_HNF : norm_step -> Prims.bool) =
  fun projectee -> match projectee with | HNF -> true | uu___ -> false
let (uu___is_Primops : norm_step -> Prims.bool) =
  fun projectee -> match projectee with | Primops -> true | uu___ -> false
let (uu___is_Delta : norm_step -> Prims.bool) =
  fun projectee -> match projectee with | Delta -> true | uu___ -> false
let (uu___is_Zeta : norm_step -> Prims.bool) =
  fun projectee -> match projectee with | Zeta -> true | uu___ -> false
let (uu___is_ZetaFull : norm_step -> Prims.bool) =
  fun projectee -> match projectee with | ZetaFull -> true | uu___ -> false
let (uu___is_Iota : norm_step -> Prims.bool) =
  fun projectee -> match projectee with | Iota -> true | uu___ -> false
let (uu___is_Reify : norm_step -> Prims.bool) =
  fun projectee -> match projectee with | Reify -> true | uu___ -> false
let (uu___is_UnfoldOnly : norm_step -> Prims.bool) =
  fun projectee ->
    match projectee with | UnfoldOnly _0 -> true | uu___ -> false
let (__proj__UnfoldOnly__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee -> match projectee with | UnfoldOnly _0 -> _0
let (uu___is_UnfoldFully : norm_step -> Prims.bool) =
  fun projectee ->
    match projectee with | UnfoldFully _0 -> true | uu___ -> false
let (__proj__UnfoldFully__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee -> match projectee with | UnfoldFully _0 -> _0
let (uu___is_UnfoldAttr : norm_step -> Prims.bool) =
  fun projectee ->
    match projectee with | UnfoldAttr _0 -> true | uu___ -> false
let (__proj__UnfoldAttr__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee -> match projectee with | UnfoldAttr _0 -> _0
let (uu___is_UnfoldQual : norm_step -> Prims.bool) =
  fun projectee ->
    match projectee with | UnfoldQual _0 -> true | uu___ -> false
let (__proj__UnfoldQual__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee -> match projectee with | UnfoldQual _0 -> _0
let (uu___is_NBE : norm_step -> Prims.bool) =
  fun projectee -> match projectee with | NBE -> true | uu___ -> false
let (uu___is_Unmeta : norm_step -> Prims.bool) =
  fun projectee -> match projectee with | Unmeta -> true | uu___ -> false
let (steps_Simpl : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tconst FStar_Parser_Const.steps_simpl
let (steps_Weak : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tconst FStar_Parser_Const.steps_weak
let (steps_HNF : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tconst FStar_Parser_Const.steps_hnf
let (steps_Primops : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tconst FStar_Parser_Const.steps_primops
let (steps_Delta : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tconst FStar_Parser_Const.steps_delta
let (steps_Zeta : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tconst FStar_Parser_Const.steps_zeta
let (steps_ZetaFull : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tconst FStar_Parser_Const.steps_zeta_full
let (steps_Iota : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tconst FStar_Parser_Const.steps_iota
let (steps_Reify : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tconst FStar_Parser_Const.steps_reify
let (steps_UnfoldOnly : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tconst FStar_Parser_Const.steps_unfoldonly
let (steps_UnfoldFully : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tconst FStar_Parser_Const.steps_unfoldonly
let (steps_UnfoldAttr : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tconst FStar_Parser_Const.steps_unfoldattr
let (steps_UnfoldQual : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tconst FStar_Parser_Const.steps_unfoldqual
let (steps_NBE : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tconst FStar_Parser_Const.steps_nbe
let (steps_Unmeta : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tconst FStar_Parser_Const.steps_unmeta
let (e_norm_step : norm_step embedding) =
  let t_norm_step =
    let uu___ = FStar_Ident.lid_of_str "FStar.Syntax.Embeddings.norm_step" in
    FStar_Syntax_Util.fvar_const uu___ in
  let emb_t_norm_step =
    let uu___ =
      let uu___1 =
        FStar_All.pipe_right FStar_Parser_Const.norm_step_lid
          FStar_Ident.string_of_lid in
      (uu___1, []) in
    FStar_Syntax_Syntax.ET_app uu___ in
  let printer1 uu___ = "norm_step" in
  let em n rng _topt norm =
    lazy_embed printer1 emb_t_norm_step rng t_norm_step n
      (fun uu___ ->
         match n with
         | Simpl -> steps_Simpl
         | Weak -> steps_Weak
         | HNF -> steps_HNF
         | Primops -> steps_Primops
         | Delta -> steps_Delta
         | Zeta -> steps_Zeta
         | ZetaFull -> steps_ZetaFull
         | Iota -> steps_Iota
         | NBE -> steps_NBE
         | Unmeta -> steps_Unmeta
         | Reify -> steps_Reify
         | UnfoldOnly l ->
             let uu___1 =
               let uu___2 =
                 let uu___3 =
                   let uu___4 =
                     let uu___5 = e_list e_string in embed uu___5 l in
                   uu___4 rng FStar_Pervasives_Native.None norm in
                 FStar_Syntax_Syntax.as_arg uu___3 in
               [uu___2] in
             FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldOnly uu___1 rng
         | UnfoldFully l ->
             let uu___1 =
               let uu___2 =
                 let uu___3 =
                   let uu___4 =
                     let uu___5 = e_list e_string in embed uu___5 l in
                   uu___4 rng FStar_Pervasives_Native.None norm in
                 FStar_Syntax_Syntax.as_arg uu___3 in
               [uu___2] in
             FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldFully uu___1 rng
         | UnfoldAttr l ->
             let uu___1 =
               let uu___2 =
                 let uu___3 =
                   let uu___4 =
                     let uu___5 = e_list e_string in embed uu___5 l in
                   uu___4 rng FStar_Pervasives_Native.None norm in
                 FStar_Syntax_Syntax.as_arg uu___3 in
               [uu___2] in
             FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldAttr uu___1 rng
         | UnfoldQual l ->
             let uu___1 =
               let uu___2 =
                 let uu___3 =
                   let uu___4 =
                     let uu___5 = e_list e_string in embed uu___5 l in
                   uu___4 rng FStar_Pervasives_Native.None norm in
                 FStar_Syntax_Syntax.as_arg uu___3 in
               [uu___2] in
             FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldQual uu___1 rng) in
  let un t0 w norm =
    let t = FStar_Syntax_Util.unmeta_safe t0 in
    lazy_unembed printer1 emb_t_norm_step t t_norm_step
      (fun t1 ->
         let uu___ = FStar_Syntax_Util.head_and_args t1 in
         match uu___ with
         | (hd, args) ->
             let uu___1 =
               let uu___2 =
                 let uu___3 = FStar_Syntax_Util.un_uinst hd in
                 uu___3.FStar_Syntax_Syntax.n in
               (uu___2, args) in
             (match uu___1 with
              | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_simpl
                  -> FStar_Pervasives_Native.Some Simpl
              | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_weak
                  -> FStar_Pervasives_Native.Some Weak
              | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_hnf
                  -> FStar_Pervasives_Native.Some HNF
              | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_primops
                  -> FStar_Pervasives_Native.Some Primops
              | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_delta
                  -> FStar_Pervasives_Native.Some Delta
              | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_zeta
                  -> FStar_Pervasives_Native.Some Zeta
              | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_zeta_full
                  -> FStar_Pervasives_Native.Some ZetaFull
              | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_iota
                  -> FStar_Pervasives_Native.Some Iota
              | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_nbe
                  -> FStar_Pervasives_Native.Some NBE
              | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unmeta
                  -> FStar_Pervasives_Native.Some Unmeta
              | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_reify
                  -> FStar_Pervasives_Native.Some Reify
              | (FStar_Syntax_Syntax.Tm_fvar fv, (l, uu___2)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldonly
                  ->
                  let uu___3 =
                    let uu___4 =
                      let uu___5 = e_list e_string in unembed uu___5 l in
                    uu___4 w norm in
                  FStar_Util.bind_opt uu___3
                    (fun ss ->
                       FStar_All.pipe_left
                         (fun uu___4 -> FStar_Pervasives_Native.Some uu___4)
                         (UnfoldOnly ss))
              | (FStar_Syntax_Syntax.Tm_fvar fv, (l, uu___2)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldfully
                  ->
                  let uu___3 =
                    let uu___4 =
                      let uu___5 = e_list e_string in unembed uu___5 l in
                    uu___4 w norm in
                  FStar_Util.bind_opt uu___3
                    (fun ss ->
                       FStar_All.pipe_left
                         (fun uu___4 -> FStar_Pervasives_Native.Some uu___4)
                         (UnfoldFully ss))
              | (FStar_Syntax_Syntax.Tm_fvar fv, (l, uu___2)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldattr
                  ->
                  let uu___3 =
                    let uu___4 =
                      let uu___5 = e_list e_string in unembed uu___5 l in
                    uu___4 w norm in
                  FStar_Util.bind_opt uu___3
                    (fun ss ->
                       FStar_All.pipe_left
                         (fun uu___4 -> FStar_Pervasives_Native.Some uu___4)
                         (UnfoldAttr ss))
              | (FStar_Syntax_Syntax.Tm_fvar fv, (l, uu___2)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldqual
                  ->
                  let uu___3 =
                    let uu___4 =
                      let uu___5 = e_list e_string in unembed uu___5 l in
                    uu___4 w norm in
                  FStar_Util.bind_opt uu___3
                    (fun ss ->
                       FStar_All.pipe_left
                         (fun uu___4 -> FStar_Pervasives_Native.Some uu___4)
                         (UnfoldQual ss))
              | uu___2 ->
                  (if w
                   then
                     (let uu___4 =
                        let uu___5 =
                          let uu___6 = FStar_Syntax_Print.term_to_string t0 in
                          FStar_Util.format1 "Not an embedded norm_step: %s"
                            uu___6 in
                        (FStar_Errors.Warning_NotEmbedded, uu___5) in
                      FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                        uu___4)
                   else ();
                   FStar_Pervasives_Native.None))) in
  mk_emb_full em un FStar_Syntax_Syntax.t_norm_step printer1 emb_t_norm_step
let (e_range : FStar_Range.range embedding) =
  let em r rng _shadow _norm =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range r)) rng in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0 in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range r) ->
        FStar_Pervasives_Native.Some r
    | uu___ ->
        (if w
         then
           (let uu___2 =
              let uu___3 =
                let uu___4 = FStar_Syntax_Print.term_to_string t0 in
                FStar_Util.format1 "Not an embedded range: %s" uu___4 in
              (FStar_Errors.Warning_NotEmbedded, uu___3) in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu___2)
         else ();
         FStar_Pervasives_Native.None) in
  let uu___ =
    let uu___1 =
      let uu___2 =
        FStar_All.pipe_right FStar_Parser_Const.range_lid
          FStar_Ident.string_of_lid in
      (uu___2, []) in
    FStar_Syntax_Syntax.ET_app uu___1 in
  mk_emb_full em un FStar_Syntax_Syntax.t_range FStar_Range.string_of_range
    uu___
let (e_vconfig : FStar_VConfig.vconfig embedding) =
  let em vcfg rng _shadow norm =
    let uu___ =
      FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.mkvconfig_lid in
    let uu___1 =
      let uu___2 =
        let uu___3 =
          let uu___4 = embed e_fsint vcfg.FStar_VConfig.initial_fuel in
          uu___4 rng FStar_Pervasives_Native.None norm in
        FStar_Syntax_Syntax.as_arg uu___3 in
      let uu___3 =
        let uu___4 =
          let uu___5 =
            let uu___6 = embed e_fsint vcfg.FStar_VConfig.max_fuel in
            uu___6 rng FStar_Pervasives_Native.None norm in
          FStar_Syntax_Syntax.as_arg uu___5 in
        let uu___5 =
          let uu___6 =
            let uu___7 =
              let uu___8 = embed e_fsint vcfg.FStar_VConfig.initial_ifuel in
              uu___8 rng FStar_Pervasives_Native.None norm in
            FStar_Syntax_Syntax.as_arg uu___7 in
          let uu___7 =
            let uu___8 =
              let uu___9 =
                let uu___10 = embed e_fsint vcfg.FStar_VConfig.max_ifuel in
                uu___10 rng FStar_Pervasives_Native.None norm in
              FStar_Syntax_Syntax.as_arg uu___9 in
            let uu___9 =
              let uu___10 =
                let uu___11 =
                  let uu___12 = embed e_bool vcfg.FStar_VConfig.detail_errors in
                  uu___12 rng FStar_Pervasives_Native.None norm in
                FStar_Syntax_Syntax.as_arg uu___11 in
              let uu___11 =
                let uu___12 =
                  let uu___13 =
                    let uu___14 =
                      embed e_bool vcfg.FStar_VConfig.detail_hint_replay in
                    uu___14 rng FStar_Pervasives_Native.None norm in
                  FStar_Syntax_Syntax.as_arg uu___13 in
                let uu___13 =
                  let uu___14 =
                    let uu___15 =
                      let uu___16 = embed e_bool vcfg.FStar_VConfig.no_smt in
                      uu___16 rng FStar_Pervasives_Native.None norm in
                    FStar_Syntax_Syntax.as_arg uu___15 in
                  let uu___15 =
                    let uu___16 =
                      let uu___17 =
                        let uu___18 =
                          embed e_fsint vcfg.FStar_VConfig.quake_lo in
                        uu___18 rng FStar_Pervasives_Native.None norm in
                      FStar_Syntax_Syntax.as_arg uu___17 in
                    let uu___17 =
                      let uu___18 =
                        let uu___19 =
                          let uu___20 =
                            embed e_fsint vcfg.FStar_VConfig.quake_hi in
                          uu___20 rng FStar_Pervasives_Native.None norm in
                        FStar_Syntax_Syntax.as_arg uu___19 in
                      let uu___19 =
                        let uu___20 =
                          let uu___21 =
                            let uu___22 =
                              embed e_bool vcfg.FStar_VConfig.quake_keep in
                            uu___22 rng FStar_Pervasives_Native.None norm in
                          FStar_Syntax_Syntax.as_arg uu___21 in
                        let uu___21 =
                          let uu___22 =
                            let uu___23 =
                              let uu___24 =
                                embed e_bool vcfg.FStar_VConfig.retry in
                              uu___24 rng FStar_Pervasives_Native.None norm in
                            FStar_Syntax_Syntax.as_arg uu___23 in
                          let uu___23 =
                            let uu___24 =
                              let uu___25 =
                                let uu___26 =
                                  embed e_bool
                                    vcfg.FStar_VConfig.smtencoding_elim_box in
                                uu___26 rng FStar_Pervasives_Native.None norm in
                              FStar_Syntax_Syntax.as_arg uu___25 in
                            let uu___25 =
                              let uu___26 =
                                let uu___27 =
                                  let uu___28 =
                                    embed e_string
                                      vcfg.FStar_VConfig.smtencoding_nl_arith_repr in
                                  uu___28 rng FStar_Pervasives_Native.None
                                    norm in
                                FStar_Syntax_Syntax.as_arg uu___27 in
                              let uu___27 =
                                let uu___28 =
                                  let uu___29 =
                                    let uu___30 =
                                      embed e_string
                                        vcfg.FStar_VConfig.smtencoding_l_arith_repr in
                                    uu___30 rng FStar_Pervasives_Native.None
                                      norm in
                                  FStar_Syntax_Syntax.as_arg uu___29 in
                                let uu___29 =
                                  let uu___30 =
                                    let uu___31 =
                                      let uu___32 =
                                        embed e_bool
                                          vcfg.FStar_VConfig.smtencoding_valid_intro in
                                      uu___32 rng
                                        FStar_Pervasives_Native.None norm in
                                    FStar_Syntax_Syntax.as_arg uu___31 in
                                  let uu___31 =
                                    let uu___32 =
                                      let uu___33 =
                                        let uu___34 =
                                          embed e_bool
                                            vcfg.FStar_VConfig.smtencoding_valid_elim in
                                        uu___34 rng
                                          FStar_Pervasives_Native.None norm in
                                      FStar_Syntax_Syntax.as_arg uu___33 in
                                    let uu___33 =
                                      let uu___34 =
                                        let uu___35 =
                                          let uu___36 =
                                            embed e_bool
                                              vcfg.FStar_VConfig.tcnorm in
                                          uu___36 rng
                                            FStar_Pervasives_Native.None norm in
                                        FStar_Syntax_Syntax.as_arg uu___35 in
                                      let uu___35 =
                                        let uu___36 =
                                          let uu___37 =
                                            let uu___38 =
                                              embed e_bool
                                                vcfg.FStar_VConfig.no_plugins in
                                            uu___38 rng
                                              FStar_Pervasives_Native.None
                                              norm in
                                          FStar_Syntax_Syntax.as_arg uu___37 in
                                        let uu___37 =
                                          let uu___38 =
                                            let uu___39 =
                                              let uu___40 =
                                                embed e_bool
                                                  vcfg.FStar_VConfig.no_tactics in
                                              uu___40 rng
                                                FStar_Pervasives_Native.None
                                                norm in
                                            FStar_Syntax_Syntax.as_arg
                                              uu___39 in
                                          let uu___39 =
                                            let uu___40 =
                                              let uu___41 =
                                                let uu___42 =
                                                  let uu___43 =
                                                    e_option e_string in
                                                  embed uu___43
                                                    vcfg.FStar_VConfig.vcgen_optimize_bind_as_seq in
                                                uu___42 rng
                                                  FStar_Pervasives_Native.None
                                                  norm in
                                              FStar_Syntax_Syntax.as_arg
                                                uu___41 in
                                            let uu___41 =
                                              let uu___42 =
                                                let uu___43 =
                                                  let uu___44 =
                                                    embed e_string_list
                                                      vcfg.FStar_VConfig.z3cliopt in
                                                  uu___44 rng
                                                    FStar_Pervasives_Native.None
                                                    norm in
                                                FStar_Syntax_Syntax.as_arg
                                                  uu___43 in
                                              let uu___43 =
                                                let uu___44 =
                                                  let uu___45 =
                                                    let uu___46 =
                                                      embed e_bool
                                                        vcfg.FStar_VConfig.z3refresh in
                                                    uu___46 rng
                                                      FStar_Pervasives_Native.None
                                                      norm in
                                                  FStar_Syntax_Syntax.as_arg
                                                    uu___45 in
                                                let uu___45 =
                                                  let uu___46 =
                                                    let uu___47 =
                                                      let uu___48 =
                                                        embed e_fsint
                                                          vcfg.FStar_VConfig.z3rlimit in
                                                      uu___48 rng
                                                        FStar_Pervasives_Native.None
                                                        norm in
                                                    FStar_Syntax_Syntax.as_arg
                                                      uu___47 in
                                                  let uu___47 =
                                                    let uu___48 =
                                                      let uu___49 =
                                                        let uu___50 =
                                                          embed e_fsint
                                                            vcfg.FStar_VConfig.z3rlimit_factor in
                                                        uu___50 rng
                                                          FStar_Pervasives_Native.None
                                                          norm in
                                                      FStar_Syntax_Syntax.as_arg
                                                        uu___49 in
                                                    let uu___49 =
                                                      let uu___50 =
                                                        let uu___51 =
                                                          let uu___52 =
                                                            embed e_fsint
                                                              vcfg.FStar_VConfig.z3seed in
                                                          uu___52 rng
                                                            FStar_Pervasives_Native.None
                                                            norm in
                                                        FStar_Syntax_Syntax.as_arg
                                                          uu___51 in
                                                      let uu___51 =
                                                        let uu___52 =
                                                          let uu___53 =
                                                            let uu___54 =
                                                              embed e_bool
                                                                vcfg.FStar_VConfig.trivial_pre_for_unannotated_effectful_fns in
                                                            uu___54 rng
                                                              FStar_Pervasives_Native.None
                                                              norm in
                                                          FStar_Syntax_Syntax.as_arg
                                                            uu___53 in
                                                        let uu___53 =
                                                          let uu___54 =
                                                            let uu___55 =
                                                              let uu___56 =
                                                                let uu___57 =
                                                                  e_option
                                                                    e_string in
                                                                embed uu___57
                                                                  vcfg.FStar_VConfig.reuse_hint_for in
                                                              uu___56 rng
                                                                FStar_Pervasives_Native.None
                                                                norm in
                                                            FStar_Syntax_Syntax.as_arg
                                                              uu___55 in
                                                          [uu___54] in
                                                        uu___52 :: uu___53 in
                                                      uu___50 :: uu___51 in
                                                    uu___48 :: uu___49 in
                                                  uu___46 :: uu___47 in
                                                uu___44 :: uu___45 in
                                              uu___42 :: uu___43 in
                                            uu___40 :: uu___41 in
                                          uu___38 :: uu___39 in
                                        uu___36 :: uu___37 in
                                      uu___34 :: uu___35 in
                                    uu___32 :: uu___33 in
                                  uu___30 :: uu___31 in
                                uu___28 :: uu___29 in
                              uu___26 :: uu___27 in
                            uu___24 :: uu___25 in
                          uu___22 :: uu___23 in
                        uu___20 :: uu___21 in
                      uu___18 :: uu___19 in
                    uu___16 :: uu___17 in
                  uu___14 :: uu___15 in
                uu___12 :: uu___13 in
              uu___10 :: uu___11 in
            uu___8 :: uu___9 in
          uu___6 :: uu___7 in
        uu___4 :: uu___5 in
      uu___2 :: uu___3 in
    FStar_Syntax_Syntax.mk_Tm_app uu___ uu___1 rng in
  let un t0 w norm =
    let t = FStar_Syntax_Util.unascribe t0 in
    let uu___ = FStar_Syntax_Util.head_and_args t in
    match uu___ with
    | (hd, args) ->
        let uu___1 =
          let uu___2 =
            let uu___3 = FStar_Syntax_Util.un_uinst hd in
            uu___3.FStar_Syntax_Syntax.n in
          (uu___2, args) in
        (match uu___1 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,
            (initial_fuel, uu___2)::(max_fuel, uu___3)::(initial_ifuel,
                                                         uu___4)::(max_ifuel,
                                                                   uu___5)::
            (detail_errors, uu___6)::(detail_hint_replay, uu___7)::(no_smt,
                                                                    uu___8)::
            (quake_lo, uu___9)::(quake_hi, uu___10)::(quake_keep, uu___11)::
            (retry, uu___12)::(smtencoding_elim_box, uu___13)::(smtencoding_nl_arith_repr,
                                                                uu___14)::
            (smtencoding_l_arith_repr, uu___15)::(smtencoding_valid_intro,
                                                  uu___16)::(smtencoding_valid_elim,
                                                             uu___17)::
            (tcnorm, uu___18)::(no_plugins, uu___19)::(no_tactics, uu___20)::
            (vcgen_optimize_bind_as_seq, uu___21)::(z3cliopt, uu___22)::
            (z3refresh, uu___23)::(z3rlimit, uu___24)::(z3rlimit_factor,
                                                        uu___25)::(z3seed,
                                                                   uu___26)::
            (trivial_pre_for_unannotated_effectful_fns, uu___27)::(reuse_hint_for,
                                                                   uu___28)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.mkvconfig_lid
             ->
             let uu___29 =
               let uu___30 = unembed e_fsint initial_fuel in uu___30 w norm in
             FStar_Util.bind_opt uu___29
               (fun initial_fuel1 ->
                  let uu___30 =
                    let uu___31 = unembed e_fsint max_fuel in uu___31 w norm in
                  FStar_Util.bind_opt uu___30
                    (fun max_fuel1 ->
                       let uu___31 =
                         let uu___32 = unembed e_fsint initial_ifuel in
                         uu___32 w norm in
                       FStar_Util.bind_opt uu___31
                         (fun initial_ifuel1 ->
                            let uu___32 =
                              let uu___33 = unembed e_fsint max_ifuel in
                              uu___33 w norm in
                            FStar_Util.bind_opt uu___32
                              (fun max_ifuel1 ->
                                 let uu___33 =
                                   let uu___34 = unembed e_bool detail_errors in
                                   uu___34 w norm in
                                 FStar_Util.bind_opt uu___33
                                   (fun detail_errors1 ->
                                      let uu___34 =
                                        let uu___35 =
                                          unembed e_bool detail_hint_replay in
                                        uu___35 w norm in
                                      FStar_Util.bind_opt uu___34
                                        (fun detail_hint_replay1 ->
                                           let uu___35 =
                                             let uu___36 =
                                               unembed e_bool no_smt in
                                             uu___36 w norm in
                                           FStar_Util.bind_opt uu___35
                                             (fun no_smt1 ->
                                                let uu___36 =
                                                  let uu___37 =
                                                    unembed e_fsint quake_lo in
                                                  uu___37 w norm in
                                                FStar_Util.bind_opt uu___36
                                                  (fun quake_lo1 ->
                                                     let uu___37 =
                                                       let uu___38 =
                                                         unembed e_fsint
                                                           quake_hi in
                                                       uu___38 w norm in
                                                     FStar_Util.bind_opt
                                                       uu___37
                                                       (fun quake_hi1 ->
                                                          let uu___38 =
                                                            let uu___39 =
                                                              unembed e_bool
                                                                quake_keep in
                                                            uu___39 w norm in
                                                          FStar_Util.bind_opt
                                                            uu___38
                                                            (fun quake_keep1
                                                               ->
                                                               let uu___39 =
                                                                 let uu___40
                                                                   =
                                                                   unembed
                                                                    e_bool
                                                                    retry in
                                                                 uu___40 w
                                                                   norm in
                                                               FStar_Util.bind_opt
                                                                 uu___39
                                                                 (fun retry1
                                                                    ->
                                                                    let uu___40
                                                                    =
                                                                    let uu___41
                                                                    =
                                                                    unembed
                                                                    e_bool
                                                                    smtencoding_elim_box in
                                                                    uu___41 w
                                                                    norm in
                                                                    FStar_Util.bind_opt
                                                                    uu___40
                                                                    (fun
                                                                    smtencoding_elim_box1
                                                                    ->
                                                                    let uu___41
                                                                    =
                                                                    let uu___42
                                                                    =
                                                                    unembed
                                                                    e_string
                                                                    smtencoding_nl_arith_repr in
                                                                    uu___42 w
                                                                    norm in
                                                                    FStar_Util.bind_opt
                                                                    uu___41
                                                                    (fun
                                                                    smtencoding_nl_arith_repr1
                                                                    ->
                                                                    let uu___42
                                                                    =
                                                                    let uu___43
                                                                    =
                                                                    unembed
                                                                    e_string
                                                                    smtencoding_l_arith_repr in
                                                                    uu___43 w
                                                                    norm in
                                                                    FStar_Util.bind_opt
                                                                    uu___42
                                                                    (fun
                                                                    smtencoding_l_arith_repr1
                                                                    ->
                                                                    let uu___43
                                                                    =
                                                                    let uu___44
                                                                    =
                                                                    unembed
                                                                    e_bool
                                                                    smtencoding_valid_intro in
                                                                    uu___44 w
                                                                    norm in
                                                                    FStar_Util.bind_opt
                                                                    uu___43
                                                                    (fun
                                                                    smtencoding_valid_intro1
                                                                    ->
                                                                    let uu___44
                                                                    =
                                                                    let uu___45
                                                                    =
                                                                    unembed
                                                                    e_bool
                                                                    smtencoding_valid_elim in
                                                                    uu___45 w
                                                                    norm in
                                                                    FStar_Util.bind_opt
                                                                    uu___44
                                                                    (fun
                                                                    smtencoding_valid_elim1
                                                                    ->
                                                                    let uu___45
                                                                    =
                                                                    let uu___46
                                                                    =
                                                                    unembed
                                                                    e_bool
                                                                    tcnorm in
                                                                    uu___46 w
                                                                    norm in
                                                                    FStar_Util.bind_opt
                                                                    uu___45
                                                                    (fun
                                                                    tcnorm1
                                                                    ->
                                                                    let uu___46
                                                                    =
                                                                    let uu___47
                                                                    =
                                                                    unembed
                                                                    e_bool
                                                                    no_plugins in
                                                                    uu___47 w
                                                                    norm in
                                                                    FStar_Util.bind_opt
                                                                    uu___46
                                                                    (fun
                                                                    no_plugins1
                                                                    ->
                                                                    let uu___47
                                                                    =
                                                                    let uu___48
                                                                    =
                                                                    unembed
                                                                    e_bool
                                                                    no_tactics in
                                                                    uu___48 w
                                                                    norm in
                                                                    FStar_Util.bind_opt
                                                                    uu___47
                                                                    (fun
                                                                    no_tactics1
                                                                    ->
                                                                    let uu___48
                                                                    =
                                                                    let uu___49
                                                                    =
                                                                    let uu___50
                                                                    =
                                                                    e_option
                                                                    e_string in
                                                                    unembed
                                                                    uu___50
                                                                    vcgen_optimize_bind_as_seq in
                                                                    uu___49 w
                                                                    norm in
                                                                    FStar_Util.bind_opt
                                                                    uu___48
                                                                    (fun
                                                                    vcgen_optimize_bind_as_seq1
                                                                    ->
                                                                    let uu___49
                                                                    =
                                                                    let uu___50
                                                                    =
                                                                    unembed
                                                                    e_string_list
                                                                    z3cliopt in
                                                                    uu___50 w
                                                                    norm in
                                                                    FStar_Util.bind_opt
                                                                    uu___49
                                                                    (fun
                                                                    z3cliopt1
                                                                    ->
                                                                    let uu___50
                                                                    =
                                                                    let uu___51
                                                                    =
                                                                    unembed
                                                                    e_bool
                                                                    z3refresh in
                                                                    uu___51 w
                                                                    norm in
                                                                    FStar_Util.bind_opt
                                                                    uu___50
                                                                    (fun
                                                                    z3refresh1
                                                                    ->
                                                                    let uu___51
                                                                    =
                                                                    let uu___52
                                                                    =
                                                                    unembed
                                                                    e_fsint
                                                                    z3rlimit in
                                                                    uu___52 w
                                                                    norm in
                                                                    FStar_Util.bind_opt
                                                                    uu___51
                                                                    (fun
                                                                    z3rlimit1
                                                                    ->
                                                                    let uu___52
                                                                    =
                                                                    let uu___53
                                                                    =
                                                                    unembed
                                                                    e_fsint
                                                                    z3rlimit_factor in
                                                                    uu___53 w
                                                                    norm in
                                                                    FStar_Util.bind_opt
                                                                    uu___52
                                                                    (fun
                                                                    z3rlimit_factor1
                                                                    ->
                                                                    let uu___53
                                                                    =
                                                                    let uu___54
                                                                    =
                                                                    unembed
                                                                    e_fsint
                                                                    z3seed in
                                                                    uu___54 w
                                                                    norm in
                                                                    FStar_Util.bind_opt
                                                                    uu___53
                                                                    (fun
                                                                    z3seed1
                                                                    ->
                                                                    let uu___54
                                                                    =
                                                                    let uu___55
                                                                    =
                                                                    unembed
                                                                    e_bool
                                                                    trivial_pre_for_unannotated_effectful_fns in
                                                                    uu___55 w
                                                                    norm in
                                                                    FStar_Util.bind_opt
                                                                    uu___54
                                                                    (fun
                                                                    trivial_pre_for_unannotated_effectful_fns1
                                                                    ->
                                                                    let uu___55
                                                                    =
                                                                    let uu___56
                                                                    =
                                                                    let uu___57
                                                                    =
                                                                    e_option
                                                                    e_string in
                                                                    unembed
                                                                    uu___57
                                                                    reuse_hint_for in
                                                                    uu___56 w
                                                                    norm in
                                                                    FStar_Util.bind_opt
                                                                    uu___55
                                                                    (fun
                                                                    reuse_hint_for1
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    {
                                                                    FStar_VConfig.initial_fuel
                                                                    =
                                                                    initial_fuel1;
                                                                    FStar_VConfig.max_fuel
                                                                    =
                                                                    max_fuel1;
                                                                    FStar_VConfig.initial_ifuel
                                                                    =
                                                                    initial_ifuel1;
                                                                    FStar_VConfig.max_ifuel
                                                                    =
                                                                    max_ifuel1;
                                                                    FStar_VConfig.detail_errors
                                                                    =
                                                                    detail_errors1;
                                                                    FStar_VConfig.detail_hint_replay
                                                                    =
                                                                    detail_hint_replay1;
                                                                    FStar_VConfig.no_smt
                                                                    = no_smt1;
                                                                    FStar_VConfig.quake_lo
                                                                    =
                                                                    quake_lo1;
                                                                    FStar_VConfig.quake_hi
                                                                    =
                                                                    quake_hi1;
                                                                    FStar_VConfig.quake_keep
                                                                    =
                                                                    quake_keep1;
                                                                    FStar_VConfig.retry
                                                                    = retry1;
                                                                    FStar_VConfig.smtencoding_elim_box
                                                                    =
                                                                    smtencoding_elim_box1;
                                                                    FStar_VConfig.smtencoding_nl_arith_repr
                                                                    =
                                                                    smtencoding_nl_arith_repr1;
                                                                    FStar_VConfig.smtencoding_l_arith_repr
                                                                    =
                                                                    smtencoding_l_arith_repr1;
                                                                    FStar_VConfig.smtencoding_valid_intro
                                                                    =
                                                                    smtencoding_valid_intro1;
                                                                    FStar_VConfig.smtencoding_valid_elim
                                                                    =
                                                                    smtencoding_valid_elim1;
                                                                    FStar_VConfig.tcnorm
                                                                    = tcnorm1;
                                                                    FStar_VConfig.no_plugins
                                                                    =
                                                                    no_plugins1;
                                                                    FStar_VConfig.no_tactics
                                                                    =
                                                                    no_tactics1;
                                                                    FStar_VConfig.vcgen_optimize_bind_as_seq
                                                                    =
                                                                    vcgen_optimize_bind_as_seq1;
                                                                    FStar_VConfig.z3cliopt
                                                                    =
                                                                    z3cliopt1;
                                                                    FStar_VConfig.z3refresh
                                                                    =
                                                                    z3refresh1;
                                                                    FStar_VConfig.z3rlimit
                                                                    =
                                                                    z3rlimit1;
                                                                    FStar_VConfig.z3rlimit_factor
                                                                    =
                                                                    z3rlimit_factor1;
                                                                    FStar_VConfig.z3seed
                                                                    = z3seed1;
                                                                    FStar_VConfig.trivial_pre_for_unannotated_effectful_fns
                                                                    =
                                                                    trivial_pre_for_unannotated_effectful_fns1;
                                                                    FStar_VConfig.reuse_hint_for
                                                                    =
                                                                    reuse_hint_for1
                                                                    })))))))))))))))))))))))))))
         | uu___2 ->
             (if w
              then
                (let uu___4 =
                   let uu___5 =
                     let uu___6 = FStar_Syntax_Print.term_to_string t0 in
                     FStar_Util.format1 "Not an embedded vconfig: %s" uu___6 in
                   (FStar_Errors.Warning_NotEmbedded, uu___5) in
                 FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu___4)
              else ();
              FStar_Pervasives_Native.None)) in
  let uu___ =
    let uu___1 =
      let uu___2 =
        FStar_All.pipe_right FStar_Parser_Const.vconfig_lid
          FStar_Ident.string_of_lid in
      (uu___2, []) in
    FStar_Syntax_Syntax.ET_app uu___1 in
  mk_emb_full em un FStar_Syntax_Syntax.t_vconfig (fun uu___1 -> "vconfig")
    uu___
let or_else : 'a . 'a FStar_Pervasives_Native.option -> (unit -> 'a) -> 'a =
  fun f ->
    fun g ->
      match f with
      | FStar_Pervasives_Native.Some x -> x
      | FStar_Pervasives_Native.None -> g ()
let e_arrow : 'a 'b . 'a embedding -> 'b embedding -> ('a -> 'b) embedding =
  fun ea ->
    fun eb ->
      let t_arrow =
        let uu___ =
          let uu___1 =
            let uu___2 =
              let uu___3 =
                let uu___4 = FStar_Syntax_Syntax.null_bv ea.typ in
                FStar_Syntax_Syntax.mk_binder uu___4 in
              [uu___3] in
            let uu___3 = FStar_Syntax_Syntax.mk_Total eb.typ in
            (uu___2, uu___3) in
          FStar_Syntax_Syntax.Tm_arrow uu___1 in
        FStar_Syntax_Syntax.mk uu___ FStar_Range.dummyRange in
      let emb_t_arr_a_b =
        FStar_Syntax_Syntax.ET_fun ((ea.emb_typ), (eb.emb_typ)) in
      let printer1 f = "<fun>" in
      let em f rng shadow_f norm =
        lazy_embed (fun uu___ -> "<fun>") emb_t_arr_a_b rng t_arrow f
          (fun uu___ ->
             let uu___1 = force_shadow shadow_f in
             match uu___1 with
             | FStar_Pervasives_Native.None ->
                 FStar_Exn.raise Embedding_failure
             | FStar_Pervasives_Native.Some repr_f ->
                 ((let uu___3 =
                     FStar_ST.op_Bang FStar_Options.debug_embedding in
                   if uu___3
                   then
                     let uu___4 = FStar_Syntax_Print.term_to_string repr_f in
                     let uu___5 = FStar_Util.stack_dump () in
                     FStar_Util.print2
                       "e_arrow forced back to term using shadow %s; repr=%s\n"
                       uu___4 uu___5
                   else ());
                  (let res = norm (FStar_Pervasives.Inr repr_f) in
                   (let uu___4 =
                      FStar_ST.op_Bang FStar_Options.debug_embedding in
                    if uu___4
                    then
                      let uu___5 = FStar_Syntax_Print.term_to_string repr_f in
                      let uu___6 = FStar_Syntax_Print.term_to_string res in
                      let uu___7 = FStar_Util.stack_dump () in
                      FStar_Util.print3
                        "e_arrow forced back to term using shadow %s; repr=%s\n\t%s\n"
                        uu___5 uu___6 uu___7
                    else ());
                   res))) in
      let un f w norm =
        lazy_unembed printer1 emb_t_arr_a_b f t_arrow
          (fun f1 ->
             let f_wrapped a1 =
               (let uu___1 = FStar_ST.op_Bang FStar_Options.debug_embedding in
                if uu___1
                then
                  let uu___2 = FStar_Syntax_Print.term_to_string f1 in
                  let uu___3 = FStar_Util.stack_dump () in
                  FStar_Util.print2
                    "Calling back into normalizer for %s\n%s\n" uu___2 uu___3
                else ());
               (let a_tm =
                  let uu___1 = embed ea a1 in
                  uu___1 f1.FStar_Syntax_Syntax.pos
                    FStar_Pervasives_Native.None norm in
                let b_tm =
                  let uu___1 =
                    let uu___2 =
                      let uu___3 =
                        let uu___4 = FStar_Syntax_Syntax.as_arg a_tm in
                        [uu___4] in
                      FStar_Syntax_Syntax.mk_Tm_app f1 uu___3
                        f1.FStar_Syntax_Syntax.pos in
                    FStar_Pervasives.Inr uu___2 in
                  norm uu___1 in
                let uu___1 = let uu___2 = unembed eb b_tm in uu___2 w norm in
                match uu___1 with
                | FStar_Pervasives_Native.None ->
                    FStar_Exn.raise Unembedding_failure
                | FStar_Pervasives_Native.Some b1 -> b1) in
             FStar_Pervasives_Native.Some f_wrapped) in
      mk_emb_full em un t_arrow printer1 emb_t_arr_a_b
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
  fun ea ->
    fun eb ->
      fun f ->
        fun n_tvars ->
          fun fv_lid ->
            fun norm ->
              let rng = FStar_Ident.range_of_lid fv_lid in
              let f_wrapped args =
                let uu___ = FStar_List.splitAt n_tvars args in
                match uu___ with
                | (_tvar_args, rest_args) ->
                    let uu___1 = FStar_List.hd rest_args in
                    (match uu___1 with
                     | (x, uu___2) ->
                         let shadow_app =
                           let uu___3 =
                             FStar_Thunk.mk
                               (fun uu___4 ->
                                  let uu___5 =
                                    norm (FStar_Pervasives.Inl fv_lid) in
                                  FStar_Syntax_Syntax.mk_Tm_app uu___5 args
                                    rng) in
                           FStar_Pervasives_Native.Some uu___3 in
                         let uu___3 =
                           let uu___4 =
                             let uu___5 = unembed ea x in uu___5 true norm in
                           FStar_Util.map_opt uu___4
                             (fun x1 ->
                                let uu___5 =
                                  let uu___6 = f x1 in embed eb uu___6 in
                                uu___5 rng shadow_app norm) in
                         (match uu___3 with
                          | FStar_Pervasives_Native.Some x1 ->
                              FStar_Pervasives_Native.Some x1
                          | FStar_Pervasives_Native.None ->
                              force_shadow shadow_app)) in
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
  fun ea ->
    fun eb ->
      fun ec ->
        fun f ->
          fun n_tvars ->
            fun fv_lid ->
              fun norm ->
                let rng = FStar_Ident.range_of_lid fv_lid in
                let f_wrapped args =
                  let uu___ = FStar_List.splitAt n_tvars args in
                  match uu___ with
                  | (_tvar_args, rest_args) ->
                      let uu___1 = FStar_List.hd rest_args in
                      (match uu___1 with
                       | (x, uu___2) ->
                           let uu___3 =
                             let uu___4 = FStar_List.tl rest_args in
                             FStar_List.hd uu___4 in
                           (match uu___3 with
                            | (y, uu___4) ->
                                let shadow_app =
                                  let uu___5 =
                                    FStar_Thunk.mk
                                      (fun uu___6 ->
                                         let uu___7 =
                                           norm (FStar_Pervasives.Inl fv_lid) in
                                         FStar_Syntax_Syntax.mk_Tm_app uu___7
                                           args rng) in
                                  FStar_Pervasives_Native.Some uu___5 in
                                let uu___5 =
                                  let uu___6 =
                                    let uu___7 = unembed ea x in
                                    uu___7 true norm in
                                  FStar_Util.bind_opt uu___6
                                    (fun x1 ->
                                       let uu___7 =
                                         let uu___8 = unembed eb y in
                                         uu___8 true norm in
                                       FStar_Util.bind_opt uu___7
                                         (fun y1 ->
                                            let uu___8 =
                                              let uu___9 =
                                                let uu___10 = f x1 y1 in
                                                embed ec uu___10 in
                                              uu___9 rng shadow_app norm in
                                            FStar_Pervasives_Native.Some
                                              uu___8)) in
                                (match uu___5 with
                                 | FStar_Pervasives_Native.Some x1 ->
                                     FStar_Pervasives_Native.Some x1
                                 | FStar_Pervasives_Native.None ->
                                     force_shadow shadow_app))) in
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
  fun ea ->
    fun eb ->
      fun ec ->
        fun ed ->
          fun f ->
            fun n_tvars ->
              fun fv_lid ->
                fun norm ->
                  let rng = FStar_Ident.range_of_lid fv_lid in
                  let f_wrapped args =
                    let uu___ = FStar_List.splitAt n_tvars args in
                    match uu___ with
                    | (_tvar_args, rest_args) ->
                        let uu___1 = FStar_List.hd rest_args in
                        (match uu___1 with
                         | (x, uu___2) ->
                             let uu___3 =
                               let uu___4 = FStar_List.tl rest_args in
                               FStar_List.hd uu___4 in
                             (match uu___3 with
                              | (y, uu___4) ->
                                  let uu___5 =
                                    let uu___6 =
                                      let uu___7 = FStar_List.tl rest_args in
                                      FStar_List.tl uu___7 in
                                    FStar_List.hd uu___6 in
                                  (match uu___5 with
                                   | (z, uu___6) ->
                                       let shadow_app =
                                         let uu___7 =
                                           FStar_Thunk.mk
                                             (fun uu___8 ->
                                                let uu___9 =
                                                  norm
                                                    (FStar_Pervasives.Inl
                                                       fv_lid) in
                                                FStar_Syntax_Syntax.mk_Tm_app
                                                  uu___9 args rng) in
                                         FStar_Pervasives_Native.Some uu___7 in
                                       let uu___7 =
                                         let uu___8 =
                                           let uu___9 = unembed ea x in
                                           uu___9 true norm in
                                         FStar_Util.bind_opt uu___8
                                           (fun x1 ->
                                              let uu___9 =
                                                let uu___10 = unembed eb y in
                                                uu___10 true norm in
                                              FStar_Util.bind_opt uu___9
                                                (fun y1 ->
                                                   let uu___10 =
                                                     let uu___11 =
                                                       unembed ec z in
                                                     uu___11 true norm in
                                                   FStar_Util.bind_opt
                                                     uu___10
                                                     (fun z1 ->
                                                        let uu___11 =
                                                          let uu___12 =
                                                            let uu___13 =
                                                              f x1 y1 z1 in
                                                            embed ed uu___13 in
                                                          uu___12 rng
                                                            shadow_app norm in
                                                        FStar_Pervasives_Native.Some
                                                          uu___11))) in
                                       (match uu___7 with
                                        | FStar_Pervasives_Native.Some x1 ->
                                            FStar_Pervasives_Native.Some x1
                                        | FStar_Pervasives_Native.None ->
                                            force_shadow shadow_app)))) in
                  f_wrapped
let debug_wrap : 'a . Prims.string -> (unit -> 'a) -> 'a =
  fun s ->
    fun f ->
      (let uu___1 = FStar_ST.op_Bang FStar_Options.debug_embedding in
       if uu___1 then FStar_Util.print1 "++++starting %s\n" s else ());
      (let res = f () in
       (let uu___2 = FStar_ST.op_Bang FStar_Options.debug_embedding in
        if uu___2 then FStar_Util.print1 "------ending %s\n" s else ());
       res)