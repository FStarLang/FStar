open Prims
type norm_cb =
  (FStarC_Ident.lident, FStarC_Syntax_Syntax.term) FStar_Pervasives.either ->
    FStarC_Syntax_Syntax.term
type shadow_term =
  FStarC_Syntax_Syntax.term FStarC_Thunk.t FStar_Pervasives_Native.option
type embed_t =
  FStarC_Compiler_Range_Type.range ->
    shadow_term -> norm_cb -> FStarC_Syntax_Syntax.term
type 'a unembed_t = norm_cb -> 'a FStar_Pervasives_Native.option
type 'a raw_embedder = 'a -> embed_t
type 'a raw_unembedder = FStarC_Syntax_Syntax.term -> 'a unembed_t
type 'a printer = 'a -> Prims.string
let (id_norm_cb : norm_cb) =
  fun uu___ ->
    match uu___ with
    | FStar_Pervasives.Inr x -> x
    | FStar_Pervasives.Inl l ->
        let uu___1 =
          FStarC_Syntax_Syntax.lid_as_fv l FStar_Pervasives_Native.None in
        FStarC_Syntax_Syntax.fv_to_tm uu___1
exception Embedding_failure 
let (uu___is_Embedding_failure : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | Embedding_failure -> true | uu___ -> false
exception Unembedding_failure 
let (uu___is_Unembedding_failure : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | Unembedding_failure -> true | uu___ -> false
let (map_shadow :
  shadow_term ->
    (FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term) -> shadow_term)
  = fun s -> fun f -> FStarC_Compiler_Util.map_opt s (FStarC_Thunk.map f)
let (force_shadow :
  shadow_term -> FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option) =
  fun s -> FStarC_Compiler_Util.map_opt s FStarC_Thunk.force
type 'a embedding =
  {
  em: 'a -> embed_t ;
  un: FStarC_Syntax_Syntax.term -> 'a unembed_t ;
  print: 'a printer ;
  typ: unit -> FStarC_Syntax_Syntax.typ ;
  e_typ: unit -> FStarC_Syntax_Syntax.emb_typ }
let __proj__Mkembedding__item__em : 'a . 'a embedding -> 'a -> embed_t =
  fun projectee ->
    match projectee with | { em; un; print; typ; e_typ;_} -> em
let __proj__Mkembedding__item__un :
  'a . 'a embedding -> FStarC_Syntax_Syntax.term -> 'a unembed_t =
  fun projectee ->
    match projectee with | { em; un; print; typ; e_typ;_} -> un
let __proj__Mkembedding__item__print : 'a . 'a embedding -> 'a printer =
  fun projectee ->
    match projectee with | { em; un; print; typ; e_typ;_} -> print
let __proj__Mkembedding__item__typ :
  'a . 'a embedding -> unit -> FStarC_Syntax_Syntax.typ =
  fun projectee ->
    match projectee with | { em; un; print; typ; e_typ;_} -> typ
let __proj__Mkembedding__item__e_typ :
  'a . 'a embedding -> unit -> FStarC_Syntax_Syntax.emb_typ =
  fun projectee ->
    match projectee with | { em; un; print; typ; e_typ;_} -> e_typ
let em : 'a . 'a embedding -> 'a -> embed_t =
  fun projectee ->
    match projectee with | { em = em1; un; print; typ; e_typ;_} -> em1
let un : 'a . 'a embedding -> FStarC_Syntax_Syntax.term -> 'a unembed_t =
  fun projectee ->
    match projectee with | { em = em1; un = un1; print; typ; e_typ;_} -> un1
let print : 'a . 'a embedding -> 'a printer =
  fun projectee ->
    match projectee with
    | { em = em1; un = un1; print = print1; typ; e_typ;_} -> print1
let typ : 'a . 'a embedding -> unit -> FStarC_Syntax_Syntax.typ =
  fun projectee ->
    match projectee with
    | { em = em1; un = un1; print = print1; typ = typ1; e_typ;_} -> typ1
let e_typ : 'a . 'a embedding -> unit -> FStarC_Syntax_Syntax.emb_typ =
  fun projectee ->
    match projectee with
    | { em = em1; un = un1; print = print1; typ = typ1; e_typ = e_typ1;_} ->
        e_typ1
let emb_typ_of : 'a . 'a embedding -> unit -> FStarC_Syntax_Syntax.emb_typ =
  fun e -> fun uu___ -> e.e_typ ()
let unknown_printer : 'a . FStarC_Syntax_Syntax.term -> 'a -> Prims.string =
  fun typ1 ->
    fun uu___ ->
      let uu___1 =
        FStarC_Class_Show.show FStarC_Syntax_Print.showable_term typ1 in
      FStarC_Compiler_Util.format1 "unknown %s" uu___1
let (term_as_fv : FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.fv) =
  fun t ->
    let uu___ =
      let uu___1 = FStarC_Syntax_Subst.compress t in
      uu___1.FStarC_Syntax_Syntax.n in
    match uu___ with
    | FStarC_Syntax_Syntax.Tm_fvar fv -> fv
    | uu___1 ->
        let uu___2 =
          let uu___3 =
            FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t in
          FStarC_Compiler_Util.format1 "Embeddings not defined for type %s"
            uu___3 in
        failwith uu___2
let mk_emb :
  'a .
    'a raw_embedder ->
      'a raw_unembedder -> FStarC_Syntax_Syntax.fv -> 'a embedding
  =
  fun em1 ->
    fun un1 ->
      fun fv ->
        {
          em = em1;
          un = un1;
          print =
            (fun x ->
               let typ1 = FStarC_Syntax_Syntax.fv_to_tm fv in
               unknown_printer typ1 x);
          typ = (fun uu___ -> FStarC_Syntax_Syntax.fv_to_tm fv);
          e_typ =
            (fun uu___ ->
               let uu___1 =
                 let uu___2 =
                   let uu___3 = FStarC_Syntax_Syntax.lid_of_fv fv in
                   FStarC_Ident.string_of_lid uu___3 in
                 (uu___2, []) in
               FStarC_Syntax_Syntax.ET_app uu___1)
        }
let mk_emb_full :
  'a .
    'a raw_embedder ->
      'a raw_unembedder ->
        (unit -> FStarC_Syntax_Syntax.typ) ->
          ('a -> Prims.string) ->
            (unit -> FStarC_Syntax_Syntax.emb_typ) -> 'a embedding
  =
  fun em1 ->
    fun un1 ->
      fun typ1 ->
        fun printe ->
          fun emb_typ ->
            { em = em1; un = un1; print = printe; typ = typ1; e_typ = emb_typ
            }
let rec (unmeta_div_results :
  FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term) =
  fun t ->
    let uu___ =
      let uu___1 = FStarC_Syntax_Subst.compress t in
      uu___1.FStarC_Syntax_Syntax.n in
    match uu___ with
    | FStarC_Syntax_Syntax.Tm_meta
        { FStarC_Syntax_Syntax.tm2 = t';
          FStarC_Syntax_Syntax.meta = FStarC_Syntax_Syntax.Meta_monadic_lift
            (src, dst, uu___1);_}
        ->
        let uu___2 =
          (FStarC_Ident.lid_equals src FStarC_Parser_Const.effect_PURE_lid)
            &&
            (FStarC_Ident.lid_equals dst FStarC_Parser_Const.effect_DIV_lid) in
        if uu___2 then unmeta_div_results t' else t
    | FStarC_Syntax_Syntax.Tm_meta
        { FStarC_Syntax_Syntax.tm2 = t';
          FStarC_Syntax_Syntax.meta = FStarC_Syntax_Syntax.Meta_monadic
            (m, uu___1);_}
        ->
        let uu___2 =
          FStarC_Ident.lid_equals m FStarC_Parser_Const.effect_DIV_lid in
        if uu___2 then unmeta_div_results t' else t
    | FStarC_Syntax_Syntax.Tm_meta
        { FStarC_Syntax_Syntax.tm2 = t';
          FStarC_Syntax_Syntax.meta = uu___1;_}
        -> unmeta_div_results t'
    | FStarC_Syntax_Syntax.Tm_ascribed
        { FStarC_Syntax_Syntax.tm = t'; FStarC_Syntax_Syntax.asc = uu___1;
          FStarC_Syntax_Syntax.eff_opt = uu___2;_}
        -> unmeta_div_results t'
    | uu___1 -> t
let type_of : 'a . 'a embedding -> FStarC_Syntax_Syntax.typ =
  fun e -> e.typ ()
let printer_of : 'a . 'a embedding -> 'a printer = fun e -> e.print
let set_type : 'a . FStarC_Syntax_Syntax.typ -> 'a embedding -> 'a embedding
  =
  fun ty ->
    fun e ->
      {
        em = (e.em);
        un = (e.un);
        print = (e.print);
        typ = (fun uu___ -> ty);
        e_typ = (e.e_typ)
      }
let embed : 'a . 'a embedding -> 'a -> embed_t = fun e -> e.em
let try_unembed :
  'a .
    'a embedding ->
      FStarC_Syntax_Syntax.term ->
        norm_cb -> 'a FStar_Pervasives_Native.option
  =
  fun e ->
    fun t ->
      fun n ->
        let t1 = unmeta_div_results t in
        let uu___ =
          let uu___1 = FStarC_Syntax_Subst.compress t1 in e.un uu___1 in
        uu___ n
let unembed :
  'a .
    'a embedding ->
      FStarC_Syntax_Syntax.term ->
        norm_cb -> 'a FStar_Pervasives_Native.option
  =
  fun e ->
    fun t ->
      fun n ->
        let r = try_unembed e t n in
        if FStar_Pervasives_Native.uu___is_None r
        then
          (let uu___1 =
             let uu___2 =
               let uu___3 =
                 FStarC_Errors_Msg.text "Unembedding failed for type" in
               let uu___4 =
                 let uu___5 = type_of e in
                 FStarC_Class_PP.pp FStarC_Syntax_Print.pretty_term uu___5 in
               FStarC_Pprint.op_Hat_Slash_Hat uu___3 uu___4 in
             let uu___3 =
               let uu___4 =
                 let uu___5 = FStarC_Errors_Msg.text "emb_typ = " in
                 let uu___6 =
                   let uu___7 =
                     let uu___8 = emb_typ_of e () in
                     FStarC_Class_Show.show
                       FStarC_Syntax_Syntax.showable_emb_typ uu___8 in
                   FStarC_Pprint.doc_of_string uu___7 in
                 FStarC_Pprint.op_Hat_Slash_Hat uu___5 uu___6 in
               let uu___5 =
                 let uu___6 =
                   let uu___7 = FStarC_Errors_Msg.text "Term =" in
                   let uu___8 =
                     FStarC_Class_PP.pp FStarC_Syntax_Print.pretty_term t in
                   FStarC_Pprint.op_Hat_Slash_Hat uu___7 uu___8 in
                 [uu___6] in
               uu___4 :: uu___5 in
             uu___2 :: uu___3 in
           FStarC_Errors.log_issue (FStarC_Syntax_Syntax.has_range_syntax ())
             t FStarC_Errors_Codes.Warning_NotEmbedded ()
             (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
             (Obj.magic uu___1))
        else ();
        r
let embed_as :
  'a 'b .
    'a embedding ->
      ('a -> 'b) ->
        ('b -> 'a) ->
          FStarC_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
            'b embedding
  =
  fun ea ->
    fun ab ->
      fun ba ->
        fun o ->
          mk_emb_full (fun x -> let uu___ = ba x in embed ea uu___)
            (fun t ->
               fun cb ->
                 let uu___ = try_unembed ea t cb in
                 FStarC_Compiler_Util.map_opt uu___ ab)
            (fun uu___ ->
               match o with
               | FStar_Pervasives_Native.Some t -> t
               | uu___1 -> type_of ea)
            (fun x ->
               let uu___ = let uu___1 = ba x in ea.print uu___1 in
               FStarC_Compiler_Util.format1 "(embed_as>> %s)\n" uu___)
            ea.e_typ
let e_lazy :
  'a .
    FStarC_Syntax_Syntax.lazy_kind ->
      FStarC_Syntax_Syntax.term -> 'a embedding
  =
  fun k ->
    fun ty ->
      let ee x rng _topt _norm =
        FStarC_Syntax_Util.mk_lazy x ty k (FStar_Pervasives_Native.Some rng) in
      let uu t _norm =
        let t0 = t in
        let uu___ =
          let uu___1 = FStarC_Syntax_Subst.compress t in
          uu___1.FStarC_Syntax_Syntax.n in
        match uu___ with
        | FStarC_Syntax_Syntax.Tm_lazy
            { FStarC_Syntax_Syntax.blob = b;
              FStarC_Syntax_Syntax.lkind = lkind;
              FStarC_Syntax_Syntax.ltyp = uu___1;
              FStarC_Syntax_Syntax.rng = uu___2;_}
            when
            FStarC_Class_Deq.op_Equals_Question
              FStarC_Syntax_Syntax.deq_lazy_kind lkind k
            ->
            let uu___3 = FStarC_Dyn.undyn b in
            FStar_Pervasives_Native.Some uu___3
        | FStarC_Syntax_Syntax.Tm_lazy
            { FStarC_Syntax_Syntax.blob = b;
              FStarC_Syntax_Syntax.lkind = lkind;
              FStarC_Syntax_Syntax.ltyp = uu___1;
              FStarC_Syntax_Syntax.rng = uu___2;_}
            ->
            ((let uu___4 =
                let uu___5 =
                  FStarC_Class_Show.show
                    FStarC_Syntax_Syntax.showable_lazy_kind k in
                let uu___6 =
                  FStarC_Class_Show.show
                    FStarC_Syntax_Syntax.showable_lazy_kind lkind in
                let uu___7 =
                  FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t0 in
                FStarC_Compiler_Util.format3
                  "Warning, lazy unembedding failed, tag mismatch.\n\tExpected %s, got %s\n\tt = %s."
                  uu___5 uu___6 uu___7 in
              FStarC_Errors.log_issue
                (FStarC_Syntax_Syntax.has_range_syntax ()) t0
                FStarC_Errors_Codes.Warning_NotEmbedded ()
                (Obj.magic FStarC_Errors_Msg.is_error_message_string)
                (Obj.magic uu___4));
             FStar_Pervasives_Native.None)
        | uu___1 -> FStar_Pervasives_Native.None in
      let uu___ = term_as_fv ty in mk_emb ee uu uu___
let lazy_embed :
  'a .
    'a printer ->
      FStarC_Syntax_Syntax.emb_typ ->
        FStarC_Compiler_Range_Type.range ->
          FStarC_Syntax_Syntax.term ->
            'a ->
              (unit -> FStarC_Syntax_Syntax.term) ->
                FStarC_Syntax_Syntax.term
  =
  fun pa ->
    fun et ->
      fun rng ->
        fun ta ->
          fun x ->
            fun f ->
              (let uu___1 =
                 FStarC_Compiler_Effect.op_Bang
                   FStarC_Options.debug_embedding in
               if uu___1
               then
                 let uu___2 =
                   FStarC_Class_Show.show FStarC_Syntax_Print.showable_term
                     ta in
                 let uu___3 =
                   FStarC_Class_Show.show
                     FStarC_Syntax_Syntax.showable_emb_typ et in
                 let uu___4 = pa x in
                 FStarC_Compiler_Util.print3
                   "Embedding a %s\n\temb_typ=%s\n\tvalue is %s\n" uu___2
                   uu___3 uu___4
               else ());
              (let uu___1 =
                 FStarC_Compiler_Effect.op_Bang
                   FStarC_Options.eager_embedding in
               if uu___1
               then f ()
               else
                 (let thunk = FStarC_Thunk.mk f in
                  FStarC_Syntax_Util.mk_lazy x FStarC_Syntax_Syntax.tun
                    (FStarC_Syntax_Syntax.Lazy_embedding (et, thunk))
                    (FStar_Pervasives_Native.Some rng)))
let lazy_unembed :
  'a .
    'a printer ->
      FStarC_Syntax_Syntax.emb_typ ->
        FStarC_Syntax_Syntax.term ->
          FStarC_Syntax_Syntax.term ->
            (FStarC_Syntax_Syntax.term -> 'a FStar_Pervasives_Native.option)
              -> 'a FStar_Pervasives_Native.option
  =
  fun pa ->
    fun et ->
      fun x ->
        fun ta ->
          fun f ->
            let x1 = FStarC_Syntax_Subst.compress x in
            match x1.FStarC_Syntax_Syntax.n with
            | FStarC_Syntax_Syntax.Tm_lazy
                { FStarC_Syntax_Syntax.blob = b;
                  FStarC_Syntax_Syntax.lkind =
                    FStarC_Syntax_Syntax.Lazy_embedding (et', t);
                  FStarC_Syntax_Syntax.ltyp = uu___;
                  FStarC_Syntax_Syntax.rng = uu___1;_}
                ->
                let uu___2 =
                  (et <> et') ||
                    (FStarC_Compiler_Effect.op_Bang
                       FStarC_Options.eager_embedding) in
                if uu___2
                then
                  let res = let uu___3 = FStarC_Thunk.force t in f uu___3 in
                  ((let uu___4 =
                      FStarC_Compiler_Effect.op_Bang
                        FStarC_Options.debug_embedding in
                    if uu___4
                    then
                      let uu___5 =
                        FStarC_Class_Show.show
                          FStarC_Syntax_Syntax.showable_emb_typ et in
                      let uu___6 =
                        FStarC_Class_Show.show
                          FStarC_Syntax_Syntax.showable_emb_typ et' in
                      let uu___7 =
                        match res with
                        | FStar_Pervasives_Native.None -> "None"
                        | FStar_Pervasives_Native.Some x2 ->
                            let uu___8 = pa x2 in Prims.strcat "Some " uu___8 in
                      FStarC_Compiler_Util.print3
                        "Unembed cancellation failed\n\t%s <> %s\nvalue is %s\n"
                        uu___5 uu___6 uu___7
                    else ());
                   res)
                else
                  (let a1 = FStarC_Dyn.undyn b in
                   (let uu___5 =
                      FStarC_Compiler_Effect.op_Bang
                        FStarC_Options.debug_embedding in
                    if uu___5
                    then
                      let uu___6 =
                        FStarC_Class_Show.show
                          FStarC_Syntax_Syntax.showable_emb_typ et in
                      let uu___7 = pa a1 in
                      FStarC_Compiler_Util.print2
                        "Unembed cancelled for %s\n\tvalue is %s\n" uu___6
                        uu___7
                    else ());
                   FStar_Pervasives_Native.Some a1)
            | uu___ ->
                let aopt = f x1 in
                ((let uu___2 =
                    FStarC_Compiler_Effect.op_Bang
                      FStarC_Options.debug_embedding in
                  if uu___2
                  then
                    let uu___3 =
                      FStarC_Class_Show.show
                        FStarC_Syntax_Syntax.showable_emb_typ et in
                    let uu___4 =
                      FStarC_Class_Show.show
                        FStarC_Syntax_Print.showable_term x1 in
                    let uu___5 =
                      match aopt with
                      | FStar_Pervasives_Native.None -> "None"
                      | FStar_Pervasives_Native.Some a1 ->
                          let uu___6 = pa a1 in Prims.strcat "Some " uu___6 in
                    FStarC_Compiler_Util.print3
                      "Unembedding:\n\temb_typ=%s\n\tterm is %s\n\tvalue is %s\n"
                      uu___3 uu___4 uu___5
                  else ());
                 aopt)
let op_let_Question :
  'uuuuu 'uuuuu1 .
    'uuuuu FStar_Pervasives_Native.option ->
      ('uuuuu -> 'uuuuu1 FStar_Pervasives_Native.option) ->
        'uuuuu1 FStar_Pervasives_Native.option
  = fun o -> fun f -> FStarC_Compiler_Util.bind_opt o f
let mk_extracted_embedding :
  'a .
    Prims.string ->
      ((Prims.string * FStarC_Syntax_Syntax.term Prims.list) ->
         'a FStar_Pervasives_Native.option)
        -> ('a -> FStarC_Syntax_Syntax.term) -> 'a embedding
  =
  fun name ->
    fun u ->
      fun e ->
        let uu t _norm =
          let uu___ = FStarC_Syntax_Util.head_and_args t in
          match uu___ with
          | (hd, args) ->
              let uu___1 =
                let uu___2 =
                  let uu___3 =
                    let uu___4 = FStarC_Syntax_Util.un_uinst hd in
                    FStarC_Syntax_Subst.compress uu___4 in
                  uu___3.FStarC_Syntax_Syntax.n in
                match uu___2 with
                | FStarC_Syntax_Syntax.Tm_fvar fv ->
                    FStar_Pervasives_Native.Some
                      ((fv.FStarC_Syntax_Syntax.fv_name).FStarC_Syntax_Syntax.v)
                | uu___3 -> FStar_Pervasives_Native.None in
              op_let_Question uu___1
                (fun hd_lid ->
                   let uu___2 =
                     let uu___3 = FStarC_Ident.string_of_lid hd_lid in
                     let uu___4 =
                       FStarC_Compiler_List.map FStar_Pervasives_Native.fst
                         args in
                     (uu___3, uu___4) in
                   u uu___2) in
        let ee x rng _topt _norm = e x in
        let uu___ =
          let uu___1 = FStarC_Ident.lid_of_str name in
          FStarC_Syntax_Syntax.lid_as_fv uu___1 FStar_Pervasives_Native.None in
        mk_emb ee uu uu___
let extracted_embed : 'a . 'a embedding -> 'a -> FStarC_Syntax_Syntax.term =
  fun e ->
    fun x ->
      let uu___ = embed e x in
      uu___ FStarC_Compiler_Range_Type.dummyRange
        FStar_Pervasives_Native.None id_norm_cb
let extracted_unembed :
  'a .
    'a embedding ->
      FStarC_Syntax_Syntax.term -> 'a FStar_Pervasives_Native.option
  = fun e -> fun t -> try_unembed e t id_norm_cb