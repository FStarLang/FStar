open Prims
let (id_norm_cb : FStarC_Syntax_Embeddings_Base.norm_cb) =
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
  FStarC_Syntax_Embeddings_Base.shadow_term ->
    (FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term) ->
      FStarC_Syntax_Embeddings_Base.shadow_term)
  = fun s -> fun f -> FStarC_Compiler_Util.map_opt s (FStarC_Thunk.map f)
let (force_shadow :
  FStarC_Syntax_Embeddings_Base.shadow_term ->
    FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option)
  = fun s -> FStarC_Compiler_Util.map_opt s FStarC_Thunk.force
type 'a printer = 'a -> Prims.string
let unknown_printer :
  'uuuuu . FStarC_Syntax_Syntax.typ -> 'uuuuu -> Prims.string =
  fun typ ->
    fun uu___ ->
      let uu___1 =
        FStarC_Class_Show.show FStarC_Syntax_Print.showable_term typ in
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
let lazy_embed :
  'a .
    'a printer ->
      (unit -> FStarC_Syntax_Syntax.emb_typ) ->
        FStarC_Compiler_Range_Type.range ->
          (unit -> FStarC_Syntax_Syntax.term) ->
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
                   let uu___3 = ta () in
                   FStarC_Class_Show.show FStarC_Syntax_Print.showable_term
                     uu___3 in
                 let uu___3 =
                   let uu___4 = et () in
                   FStarC_Class_Show.show
                     FStarC_Syntax_Syntax.showable_emb_typ uu___4 in
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
                  let uu___3 =
                    let uu___4 = let uu___5 = et () in (uu___5, thunk) in
                    FStarC_Syntax_Syntax.Lazy_embedding uu___4 in
                  FStarC_Syntax_Util.mk_lazy x FStarC_Syntax_Syntax.tun
                    uu___3 (FStar_Pervasives_Native.Some rng)))
let lazy_unembed :
  'a .
    'a printer ->
      (unit -> FStarC_Syntax_Syntax.emb_typ) ->
        FStarC_Syntax_Syntax.term ->
          (unit -> FStarC_Syntax_Syntax.term) ->
            (FStarC_Syntax_Syntax.term -> 'a FStar_Pervasives_Native.option)
              -> 'a FStar_Pervasives_Native.option
  =
  fun pa ->
    fun et ->
      fun x ->
        fun ta ->
          fun f ->
            let et1 = et () in
            let x1 = FStarC_Syntax_Embeddings_Base.unmeta_div_results x in
            match x1.FStarC_Syntax_Syntax.n with
            | FStarC_Syntax_Syntax.Tm_lazy
                { FStarC_Syntax_Syntax.blob = b;
                  FStarC_Syntax_Syntax.lkind =
                    FStarC_Syntax_Syntax.Lazy_embedding (et', t);
                  FStarC_Syntax_Syntax.ltyp = uu___;
                  FStarC_Syntax_Syntax.rng = uu___1;_}
                ->
                let uu___2 =
                  (et1 <> et') ||
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
                          FStarC_Syntax_Syntax.showable_emb_typ et1 in
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
                          FStarC_Syntax_Syntax.showable_emb_typ et1 in
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
                        FStarC_Syntax_Syntax.showable_emb_typ et1 in
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
let (mk_any_emb :
  FStarC_Syntax_Syntax.typ ->
    FStarC_Syntax_Syntax.term FStarC_Syntax_Embeddings_Base.embedding)
  =
  fun typ ->
    let em t _r _shadow _norm =
      (let uu___1 =
         FStarC_Compiler_Effect.op_Bang FStarC_Options.debug_embedding in
       if uu___1
       then
         let uu___2 = unknown_printer typ t in
         FStarC_Compiler_Util.print1 "Embedding abstract: %s\n" uu___2
       else ());
      t in
    let un t _n =
      (let uu___1 =
         FStarC_Compiler_Effect.op_Bang FStarC_Options.debug_embedding in
       if uu___1
       then
         let uu___2 = unknown_printer typ t in
         FStarC_Compiler_Util.print1 "Unembedding abstract: %s\n" uu___2
       else ());
      FStar_Pervasives_Native.Some t in
    FStarC_Syntax_Embeddings_Base.mk_emb_full em un (fun uu___ -> typ)
      (unknown_printer typ) (fun uu___ -> FStarC_Syntax_Syntax.ET_abstract)
let (e_any :
  FStarC_Syntax_Syntax.term FStarC_Syntax_Embeddings_Base.embedding) =
  let em t r _shadow _norm =
    {
      FStarC_Syntax_Syntax.n = (t.FStarC_Syntax_Syntax.n);
      FStarC_Syntax_Syntax.pos = r;
      FStarC_Syntax_Syntax.vars = (t.FStarC_Syntax_Syntax.vars);
      FStarC_Syntax_Syntax.hash_code = (t.FStarC_Syntax_Syntax.hash_code)
    } in
  let un t _n = FStar_Pervasives_Native.Some t in
  FStarC_Syntax_Embeddings_Base.mk_emb_full em un
    (fun uu___ -> FStarC_Syntax_Syntax.t_term)
    (FStarC_Class_Show.show FStarC_Syntax_Print.showable_term)
    (fun uu___ ->
       let uu___1 =
         let uu___2 = FStarC_Ident.string_of_lid FStarC_Parser_Const.term_lid in
         (uu___2, []) in
       FStarC_Syntax_Syntax.ET_app uu___1)
let (e_unit : unit FStarC_Syntax_Embeddings_Base.embedding) =
  let em u rng _shadow _norm =
    {
      FStarC_Syntax_Syntax.n =
        (FStarC_Syntax_Util.exp_unit.FStarC_Syntax_Syntax.n);
      FStarC_Syntax_Syntax.pos = rng;
      FStarC_Syntax_Syntax.vars =
        (FStarC_Syntax_Util.exp_unit.FStarC_Syntax_Syntax.vars);
      FStarC_Syntax_Syntax.hash_code =
        (FStarC_Syntax_Util.exp_unit.FStarC_Syntax_Syntax.hash_code)
    } in
  let un t0 _norm =
    let t = FStarC_Syntax_Util.unascribe t0 in
    match t.FStarC_Syntax_Syntax.n with
    | FStarC_Syntax_Syntax.Tm_constant (FStarC_Const.Const_unit) ->
        FStar_Pervasives_Native.Some ()
    | uu___ -> FStar_Pervasives_Native.None in
  FStarC_Syntax_Embeddings_Base.mk_emb_full em un
    (fun uu___ -> FStarC_Syntax_Syntax.t_unit) (fun uu___ -> "()")
    (fun uu___ ->
       let uu___1 =
         let uu___2 = FStarC_Ident.string_of_lid FStarC_Parser_Const.unit_lid in
         (uu___2, []) in
       FStarC_Syntax_Syntax.ET_app uu___1)
let (e_bool : Prims.bool FStarC_Syntax_Embeddings_Base.embedding) =
  let em b rng _shadow _norm =
    let t =
      if b
      then FStarC_Syntax_Util.exp_true_bool
      else FStarC_Syntax_Util.exp_false_bool in
    {
      FStarC_Syntax_Syntax.n = (t.FStarC_Syntax_Syntax.n);
      FStarC_Syntax_Syntax.pos = rng;
      FStarC_Syntax_Syntax.vars = (t.FStarC_Syntax_Syntax.vars);
      FStarC_Syntax_Syntax.hash_code = (t.FStarC_Syntax_Syntax.hash_code)
    } in
  let un t _norm =
    let uu___ =
      let uu___1 = FStarC_Syntax_Subst.compress t in
      uu___1.FStarC_Syntax_Syntax.n in
    match uu___ with
    | FStarC_Syntax_Syntax.Tm_constant (FStarC_Const.Const_bool b) ->
        FStar_Pervasives_Native.Some b
    | uu___1 -> FStar_Pervasives_Native.None in
  FStarC_Syntax_Embeddings_Base.mk_emb_full em un
    (fun uu___ -> FStarC_Syntax_Syntax.t_bool)
    FStarC_Compiler_Util.string_of_bool
    (fun uu___ ->
       let uu___1 =
         let uu___2 = FStarC_Ident.string_of_lid FStarC_Parser_Const.bool_lid in
         (uu___2, []) in
       FStarC_Syntax_Syntax.ET_app uu___1)
let (e_char : FStar_Char.char FStarC_Syntax_Embeddings_Base.embedding) =
  let em c rng _shadow _norm =
    let t = FStarC_Syntax_Util.exp_char c in
    {
      FStarC_Syntax_Syntax.n = (t.FStarC_Syntax_Syntax.n);
      FStarC_Syntax_Syntax.pos = rng;
      FStarC_Syntax_Syntax.vars = (t.FStarC_Syntax_Syntax.vars);
      FStarC_Syntax_Syntax.hash_code = (t.FStarC_Syntax_Syntax.hash_code)
    } in
  let un t _norm =
    let uu___ =
      let uu___1 = FStarC_Syntax_Subst.compress t in
      uu___1.FStarC_Syntax_Syntax.n in
    match uu___ with
    | FStarC_Syntax_Syntax.Tm_constant (FStarC_Const.Const_char c) ->
        FStar_Pervasives_Native.Some c
    | uu___1 -> FStar_Pervasives_Native.None in
  FStarC_Syntax_Embeddings_Base.mk_emb_full em un
    (fun uu___ -> FStarC_Syntax_Syntax.t_char)
    FStarC_Compiler_Util.string_of_char
    (fun uu___ ->
       let uu___1 =
         let uu___2 = FStarC_Ident.string_of_lid FStarC_Parser_Const.char_lid in
         (uu___2, []) in
       FStarC_Syntax_Syntax.ET_app uu___1)
let (e_int : FStarC_BigInt.t FStarC_Syntax_Embeddings_Base.embedding) =
  let ty = FStarC_Syntax_Syntax.t_int in
  let emb_t_int =
    let uu___ =
      let uu___1 = FStarC_Ident.string_of_lid FStarC_Parser_Const.int_lid in
      (uu___1, []) in
    FStarC_Syntax_Syntax.ET_app uu___ in
  let em i rng _shadow _norm =
    lazy_embed FStarC_BigInt.string_of_big_int (fun uu___ -> emb_t_int) rng
      (fun uu___ -> ty) i
      (fun uu___ ->
         let uu___1 = FStarC_BigInt.string_of_big_int i in
         FStarC_Syntax_Util.exp_int uu___1) in
  let un t _norm =
    lazy_unembed FStarC_BigInt.string_of_big_int (fun uu___ -> emb_t_int) t
      (fun uu___ -> ty)
      (fun t1 ->
         match t1.FStarC_Syntax_Syntax.n with
         | FStarC_Syntax_Syntax.Tm_constant (FStarC_Const.Const_int
             (s, uu___)) ->
             let uu___1 = FStarC_BigInt.big_int_of_string s in
             FStar_Pervasives_Native.Some uu___1
         | uu___ -> FStar_Pervasives_Native.None) in
  FStarC_Syntax_Embeddings_Base.mk_emb_full em un (fun uu___ -> ty)
    FStarC_BigInt.string_of_big_int (fun uu___ -> emb_t_int)
let (e_fsint : Prims.int FStarC_Syntax_Embeddings_Base.embedding) =
  FStarC_Syntax_Embeddings_Base.embed_as e_int FStarC_BigInt.to_int_fs
    FStarC_BigInt.of_int_fs FStar_Pervasives_Native.None
let (e_string : Prims.string FStarC_Syntax_Embeddings_Base.embedding) =
  let emb_t_string =
    let uu___ =
      let uu___1 = FStarC_Ident.string_of_lid FStarC_Parser_Const.string_lid in
      (uu___1, []) in
    FStarC_Syntax_Syntax.ET_app uu___ in
  let em s rng _shadow _norm =
    FStarC_Syntax_Syntax.mk
      (FStarC_Syntax_Syntax.Tm_constant (FStarC_Const.Const_string (s, rng)))
      rng in
  let un t _norm =
    let uu___ =
      let uu___1 = FStarC_Syntax_Subst.compress t in
      uu___1.FStarC_Syntax_Syntax.n in
    match uu___ with
    | FStarC_Syntax_Syntax.Tm_constant (FStarC_Const.Const_string
        (s, uu___1)) -> FStar_Pervasives_Native.Some s
    | uu___1 -> FStar_Pervasives_Native.None in
  FStarC_Syntax_Embeddings_Base.mk_emb_full em un
    (fun uu___ -> FStarC_Syntax_Syntax.t_string)
    (fun x -> Prims.strcat "\"" (Prims.strcat x "\""))
    (fun uu___ -> emb_t_string)
let (e_real :
  FStarC_Compiler_Real.real FStarC_Syntax_Embeddings_Base.embedding) =
  let ty = FStarC_Syntax_Syntax.t_real in
  let emb_t_real =
    let uu___ =
      let uu___1 = FStarC_Ident.string_of_lid FStarC_Parser_Const.real_lid in
      (uu___1, []) in
    FStarC_Syntax_Syntax.ET_app uu___ in
  let em r rng _shadow _norm =
    let uu___ = r in
    match uu___ with
    | FStarC_Compiler_Real.Real s ->
        FStarC_Syntax_Syntax.mk
          (FStarC_Syntax_Syntax.Tm_constant (FStarC_Const.Const_real s)) rng in
  let un t _norm =
    let uu___ =
      let uu___1 = FStarC_Syntax_Embeddings_Base.unmeta_div_results t in
      uu___1.FStarC_Syntax_Syntax.n in
    match uu___ with
    | FStarC_Syntax_Syntax.Tm_constant (FStarC_Const.Const_real s) ->
        FStar_Pervasives_Native.Some (FStarC_Compiler_Real.Real s)
    | uu___1 -> FStar_Pervasives_Native.None in
  FStarC_Syntax_Embeddings_Base.mk_emb_full em un (fun uu___ -> ty)
    (fun uu___ -> "<real>") (fun uu___ -> emb_t_real)
let e_option :
  'a .
    'a FStarC_Syntax_Embeddings_Base.embedding ->
      'a FStar_Pervasives_Native.option
        FStarC_Syntax_Embeddings_Base.embedding
  =
  fun ea ->
    let typ uu___ =
      let uu___1 = FStarC_Syntax_Embeddings_Base.type_of ea in
      FStarC_Syntax_Syntax.t_option_of uu___1 in
    let emb_t_option_a uu___ =
      let uu___1 =
        let uu___2 =
          FStarC_Ident.string_of_lid FStarC_Parser_Const.option_lid in
        let uu___3 =
          let uu___4 = FStarC_Syntax_Embeddings_Base.emb_typ_of ea () in
          [uu___4] in
        (uu___2, uu___3) in
      FStarC_Syntax_Syntax.ET_app uu___1 in
    let printer1 x =
      let uu___ = FStarC_Syntax_Embeddings_Base.printer_of ea in
      FStarC_Common.string_of_option uu___ x in
    let em o rng shadow norm =
      lazy_embed printer1 emb_t_option_a rng
        (fun uu___ ->
           let uu___1 = FStarC_Syntax_Embeddings_Base.type_of ea in
           FStarC_Syntax_Syntax.t_option_of uu___1) o
        (fun uu___ ->
           match o with
           | FStar_Pervasives_Native.None ->
               let uu___1 =
                 let uu___2 =
                   FStarC_Syntax_Syntax.tdataconstr
                     FStarC_Parser_Const.none_lid in
                 FStarC_Syntax_Syntax.mk_Tm_uinst uu___2
                   [FStarC_Syntax_Syntax.U_zero] in
               let uu___2 =
                 let uu___3 =
                   let uu___4 = FStarC_Syntax_Embeddings_Base.type_of ea in
                   FStarC_Syntax_Syntax.iarg uu___4 in
                 [uu___3] in
               FStarC_Syntax_Syntax.mk_Tm_app uu___1 uu___2 rng
           | FStar_Pervasives_Native.Some a1 ->
               let shadow_a =
                 map_shadow shadow
                   (fun t ->
                      let v = FStarC_Ident.mk_ident ("v", rng) in
                      let some_v =
                        FStarC_Syntax_Util.mk_field_projector_name_from_ident
                          FStarC_Parser_Const.some_lid v in
                      let some_v_tm =
                        let uu___1 =
                          FStarC_Syntax_Syntax.lid_as_fv some_v
                            FStar_Pervasives_Native.None in
                        FStarC_Syntax_Syntax.fv_to_tm uu___1 in
                      let uu___1 =
                        FStarC_Syntax_Syntax.mk_Tm_uinst some_v_tm
                          [FStarC_Syntax_Syntax.U_zero] in
                      let uu___2 =
                        let uu___3 =
                          let uu___4 =
                            FStarC_Syntax_Embeddings_Base.type_of ea in
                          FStarC_Syntax_Syntax.iarg uu___4 in
                        let uu___4 =
                          let uu___5 = FStarC_Syntax_Syntax.as_arg t in
                          [uu___5] in
                        uu___3 :: uu___4 in
                      FStarC_Syntax_Syntax.mk_Tm_app uu___1 uu___2 rng) in
               let uu___1 =
                 let uu___2 =
                   FStarC_Syntax_Syntax.tdataconstr
                     FStarC_Parser_Const.some_lid in
                 FStarC_Syntax_Syntax.mk_Tm_uinst uu___2
                   [FStarC_Syntax_Syntax.U_zero] in
               let uu___2 =
                 let uu___3 =
                   let uu___4 = FStarC_Syntax_Embeddings_Base.type_of ea in
                   FStarC_Syntax_Syntax.iarg uu___4 in
                 let uu___4 =
                   let uu___5 =
                     let uu___6 =
                       let uu___7 = FStarC_Syntax_Embeddings_Base.embed ea a1 in
                       uu___7 rng shadow_a norm in
                     FStarC_Syntax_Syntax.as_arg uu___6 in
                   [uu___5] in
                 uu___3 :: uu___4 in
               FStarC_Syntax_Syntax.mk_Tm_app uu___1 uu___2 rng) in
    let un t norm =
      lazy_unembed printer1 emb_t_option_a t
        (fun uu___ ->
           let uu___1 = FStarC_Syntax_Embeddings_Base.type_of ea in
           FStarC_Syntax_Syntax.t_option_of uu___1)
        (fun t1 ->
           let uu___ = FStarC_Syntax_Util.head_and_args_full t1 in
           match uu___ with
           | (hd, args) ->
               let uu___1 =
                 let uu___2 =
                   let uu___3 = FStarC_Syntax_Util.un_uinst hd in
                   uu___3.FStarC_Syntax_Syntax.n in
                 (uu___2, args) in
               (match uu___1 with
                | (FStarC_Syntax_Syntax.Tm_fvar fv, uu___2) when
                    FStarC_Syntax_Syntax.fv_eq_lid fv
                      FStarC_Parser_Const.none_lid
                    ->
                    FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
                | (FStarC_Syntax_Syntax.Tm_fvar fv, uu___2::(a1, uu___3)::[])
                    when
                    FStarC_Syntax_Syntax.fv_eq_lid fv
                      FStarC_Parser_Const.some_lid
                    ->
                    let uu___4 =
                      FStarC_Syntax_Embeddings_Base.try_unembed ea a1 norm in
                    FStarC_Compiler_Util.bind_opt uu___4
                      (fun a2 ->
                         FStar_Pervasives_Native.Some
                           (FStar_Pervasives_Native.Some a2))
                | uu___2 -> FStar_Pervasives_Native.None)) in
    FStarC_Syntax_Embeddings_Base.mk_emb_full em un typ printer1
      emb_t_option_a
let e_tuple2 :
  'a 'b .
    'a FStarC_Syntax_Embeddings_Base.embedding ->
      'b FStarC_Syntax_Embeddings_Base.embedding ->
        ('a * 'b) FStarC_Syntax_Embeddings_Base.embedding
  =
  fun ea ->
    fun eb ->
      let typ uu___ =
        let uu___1 = FStarC_Syntax_Embeddings_Base.type_of ea in
        let uu___2 = FStarC_Syntax_Embeddings_Base.type_of eb in
        FStarC_Syntax_Syntax.t_tuple2_of uu___1 uu___2 in
      let emb_t_pair uu___ =
        let uu___1 =
          let uu___2 =
            FStarC_Ident.string_of_lid FStarC_Parser_Const.lid_tuple2 in
          let uu___3 =
            let uu___4 = FStarC_Syntax_Embeddings_Base.emb_typ_of ea () in
            let uu___5 =
              let uu___6 = FStarC_Syntax_Embeddings_Base.emb_typ_of eb () in
              [uu___6] in
            uu___4 :: uu___5 in
          (uu___2, uu___3) in
        FStarC_Syntax_Syntax.ET_app uu___1 in
      let printer1 uu___ =
        match uu___ with
        | (x, y) ->
            let uu___1 =
              let uu___2 = FStarC_Syntax_Embeddings_Base.printer_of ea in
              uu___2 x in
            let uu___2 =
              let uu___3 = FStarC_Syntax_Embeddings_Base.printer_of eb in
              uu___3 y in
            FStarC_Compiler_Util.format2 "(%s, %s)" uu___1 uu___2 in
      let em x rng shadow norm =
        lazy_embed printer1 emb_t_pair rng typ x
          (fun uu___ ->
             let proj i ab =
               let proj_1 =
                 let uu___1 =
                   FStarC_Parser_Const.mk_tuple_data_lid (Prims.of_int (2))
                     rng in
                 let uu___2 =
                   FStarC_Syntax_Syntax.null_bv FStarC_Syntax_Syntax.tun in
                 FStarC_Syntax_Util.mk_field_projector_name uu___1 uu___2 i in
               let proj_1_tm =
                 let uu___1 =
                   FStarC_Syntax_Syntax.lid_as_fv proj_1
                     FStar_Pervasives_Native.None in
                 FStarC_Syntax_Syntax.fv_to_tm uu___1 in
               let uu___1 =
                 FStarC_Syntax_Syntax.mk_Tm_uinst proj_1_tm
                   [FStarC_Syntax_Syntax.U_zero] in
               let uu___2 =
                 let uu___3 =
                   let uu___4 = FStarC_Syntax_Embeddings_Base.type_of ea in
                   FStarC_Syntax_Syntax.iarg uu___4 in
                 let uu___4 =
                   let uu___5 =
                     let uu___6 = FStarC_Syntax_Embeddings_Base.type_of eb in
                     FStarC_Syntax_Syntax.iarg uu___6 in
                   let uu___6 =
                     let uu___7 = FStarC_Syntax_Syntax.as_arg ab in [uu___7] in
                   uu___5 :: uu___6 in
                 uu___3 :: uu___4 in
               FStarC_Syntax_Syntax.mk_Tm_app uu___1 uu___2 rng in
             let shadow_a = map_shadow shadow (proj Prims.int_one) in
             let shadow_b = map_shadow shadow (proj (Prims.of_int (2))) in
             let uu___1 =
               let uu___2 =
                 FStarC_Syntax_Syntax.tdataconstr
                   FStarC_Parser_Const.lid_Mktuple2 in
               FStarC_Syntax_Syntax.mk_Tm_uinst uu___2
                 [FStarC_Syntax_Syntax.U_zero; FStarC_Syntax_Syntax.U_zero] in
             let uu___2 =
               let uu___3 =
                 let uu___4 = FStarC_Syntax_Embeddings_Base.type_of ea in
                 FStarC_Syntax_Syntax.iarg uu___4 in
               let uu___4 =
                 let uu___5 =
                   let uu___6 = FStarC_Syntax_Embeddings_Base.type_of eb in
                   FStarC_Syntax_Syntax.iarg uu___6 in
                 let uu___6 =
                   let uu___7 =
                     let uu___8 =
                       let uu___9 =
                         FStarC_Syntax_Embeddings_Base.embed ea
                           (FStar_Pervasives_Native.fst x) in
                       uu___9 rng shadow_a norm in
                     FStarC_Syntax_Syntax.as_arg uu___8 in
                   let uu___8 =
                     let uu___9 =
                       let uu___10 =
                         let uu___11 =
                           FStarC_Syntax_Embeddings_Base.embed eb
                             (FStar_Pervasives_Native.snd x) in
                         uu___11 rng shadow_b norm in
                       FStarC_Syntax_Syntax.as_arg uu___10 in
                     [uu___9] in
                   uu___7 :: uu___8 in
                 uu___5 :: uu___6 in
               uu___3 :: uu___4 in
             FStarC_Syntax_Syntax.mk_Tm_app uu___1 uu___2 rng) in
      let un t norm =
        lazy_unembed printer1 emb_t_pair t typ
          (fun uu___ ->
             (fun t1 ->
                let uu___ = FStarC_Syntax_Util.head_and_args_full t1 in
                match uu___ with
                | (hd, args) ->
                    let uu___1 =
                      let uu___2 =
                        let uu___3 = FStarC_Syntax_Util.un_uinst hd in
                        uu___3.FStarC_Syntax_Syntax.n in
                      (uu___2, args) in
                    (match uu___1 with
                     | (FStarC_Syntax_Syntax.Tm_fvar fv,
                        uu___2::uu___3::(a1, uu___4)::(b1, uu___5)::[]) when
                         FStarC_Syntax_Syntax.fv_eq_lid fv
                           FStarC_Parser_Const.lid_Mktuple2
                         ->
                         Obj.magic
                           (Obj.repr
                              (let uu___6 =
                                 FStarC_Syntax_Embeddings_Base.try_unembed ea
                                   a1 norm in
                               FStarC_Class_Monad.op_let_Bang
                                 FStarC_Class_Monad.monad_option () ()
                                 (Obj.magic uu___6)
                                 (fun uu___7 ->
                                    (fun a2 ->
                                       let a2 = Obj.magic a2 in
                                       let uu___7 =
                                         FStarC_Syntax_Embeddings_Base.try_unembed
                                           eb b1 norm in
                                       Obj.magic
                                         (FStarC_Class_Monad.op_let_Bang
                                            FStarC_Class_Monad.monad_option
                                            () () (Obj.magic uu___7)
                                            (fun uu___8 ->
                                               (fun b2 ->
                                                  let b2 = Obj.magic b2 in
                                                  Obj.magic
                                                    (FStar_Pervasives_Native.Some
                                                       (a2, b2))) uu___8)))
                                      uu___7)))
                     | uu___2 ->
                         Obj.magic (Obj.repr FStar_Pervasives_Native.None)))
               uu___) in
      FStarC_Syntax_Embeddings_Base.mk_emb_full em un typ printer1 emb_t_pair
let e_tuple3 :
  'a 'b 'c .
    'a FStarC_Syntax_Embeddings_Base.embedding ->
      'b FStarC_Syntax_Embeddings_Base.embedding ->
        'c FStarC_Syntax_Embeddings_Base.embedding ->
          ('a * 'b * 'c) FStarC_Syntax_Embeddings_Base.embedding
  =
  fun ea ->
    fun eb ->
      fun ec ->
        let typ uu___ =
          let uu___1 = FStarC_Syntax_Embeddings_Base.type_of ea in
          let uu___2 = FStarC_Syntax_Embeddings_Base.type_of eb in
          let uu___3 = FStarC_Syntax_Embeddings_Base.type_of ec in
          FStarC_Syntax_Syntax.t_tuple3_of uu___1 uu___2 uu___3 in
        let emb_t_pair uu___ =
          let uu___1 =
            let uu___2 =
              FStarC_Ident.string_of_lid FStarC_Parser_Const.lid_tuple3 in
            let uu___3 =
              let uu___4 = FStarC_Syntax_Embeddings_Base.emb_typ_of ea () in
              let uu___5 =
                let uu___6 = FStarC_Syntax_Embeddings_Base.emb_typ_of eb () in
                let uu___7 =
                  let uu___8 = FStarC_Syntax_Embeddings_Base.emb_typ_of ec () in
                  [uu___8] in
                uu___6 :: uu___7 in
              uu___4 :: uu___5 in
            (uu___2, uu___3) in
          FStarC_Syntax_Syntax.ET_app uu___1 in
        let printer1 uu___ =
          match uu___ with
          | (x, y, z) ->
              let uu___1 =
                let uu___2 = FStarC_Syntax_Embeddings_Base.printer_of ea in
                uu___2 x in
              let uu___2 =
                let uu___3 = FStarC_Syntax_Embeddings_Base.printer_of eb in
                uu___3 y in
              let uu___3 =
                let uu___4 = FStarC_Syntax_Embeddings_Base.printer_of ec in
                uu___4 z in
              FStarC_Compiler_Util.format3 "(%s, %s, %s)" uu___1 uu___2
                uu___3 in
        let em uu___ rng shadow norm =
          match uu___ with
          | (x1, x2, x3) ->
              lazy_embed printer1 emb_t_pair rng typ (x1, x2, x3)
                (fun uu___1 ->
                   let proj i abc =
                     let proj_i =
                       let uu___2 =
                         FStarC_Parser_Const.mk_tuple_data_lid
                           (Prims.of_int (3)) rng in
                       let uu___3 =
                         FStarC_Syntax_Syntax.null_bv
                           FStarC_Syntax_Syntax.tun in
                       FStarC_Syntax_Util.mk_field_projector_name uu___2
                         uu___3 i in
                     let proj_i_tm =
                       let uu___2 =
                         FStarC_Syntax_Syntax.lid_as_fv proj_i
                           FStar_Pervasives_Native.None in
                       FStarC_Syntax_Syntax.fv_to_tm uu___2 in
                     let uu___2 =
                       FStarC_Syntax_Syntax.mk_Tm_uinst proj_i_tm
                         [FStarC_Syntax_Syntax.U_zero] in
                     let uu___3 =
                       let uu___4 =
                         let uu___5 =
                           FStarC_Syntax_Embeddings_Base.type_of ea in
                         FStarC_Syntax_Syntax.iarg uu___5 in
                       let uu___5 =
                         let uu___6 =
                           let uu___7 =
                             FStarC_Syntax_Embeddings_Base.type_of eb in
                           FStarC_Syntax_Syntax.iarg uu___7 in
                         let uu___7 =
                           let uu___8 =
                             let uu___9 =
                               FStarC_Syntax_Embeddings_Base.type_of ec in
                             FStarC_Syntax_Syntax.iarg uu___9 in
                           let uu___9 =
                             let uu___10 = FStarC_Syntax_Syntax.as_arg abc in
                             [uu___10] in
                           uu___8 :: uu___9 in
                         uu___6 :: uu___7 in
                       uu___4 :: uu___5 in
                     FStarC_Syntax_Syntax.mk_Tm_app uu___2 uu___3 rng in
                   let shadow_a = map_shadow shadow (proj Prims.int_one) in
                   let shadow_b = map_shadow shadow (proj (Prims.of_int (2))) in
                   let shadow_c = map_shadow shadow (proj (Prims.of_int (3))) in
                   let uu___2 =
                     let uu___3 =
                       FStarC_Syntax_Syntax.tdataconstr
                         FStarC_Parser_Const.lid_Mktuple3 in
                     FStarC_Syntax_Syntax.mk_Tm_uinst uu___3
                       [FStarC_Syntax_Syntax.U_zero;
                       FStarC_Syntax_Syntax.U_zero;
                       FStarC_Syntax_Syntax.U_zero] in
                   let uu___3 =
                     let uu___4 =
                       let uu___5 = FStarC_Syntax_Embeddings_Base.type_of ea in
                       FStarC_Syntax_Syntax.iarg uu___5 in
                     let uu___5 =
                       let uu___6 =
                         let uu___7 =
                           FStarC_Syntax_Embeddings_Base.type_of eb in
                         FStarC_Syntax_Syntax.iarg uu___7 in
                       let uu___7 =
                         let uu___8 =
                           let uu___9 =
                             FStarC_Syntax_Embeddings_Base.type_of ec in
                           FStarC_Syntax_Syntax.iarg uu___9 in
                         let uu___9 =
                           let uu___10 =
                             let uu___11 =
                               let uu___12 =
                                 FStarC_Syntax_Embeddings_Base.embed ea x1 in
                               uu___12 rng shadow_a norm in
                             FStarC_Syntax_Syntax.as_arg uu___11 in
                           let uu___11 =
                             let uu___12 =
                               let uu___13 =
                                 let uu___14 =
                                   FStarC_Syntax_Embeddings_Base.embed eb x2 in
                                 uu___14 rng shadow_b norm in
                               FStarC_Syntax_Syntax.as_arg uu___13 in
                             let uu___13 =
                               let uu___14 =
                                 let uu___15 =
                                   let uu___16 =
                                     FStarC_Syntax_Embeddings_Base.embed ec
                                       x3 in
                                   uu___16 rng shadow_c norm in
                                 FStarC_Syntax_Syntax.as_arg uu___15 in
                               [uu___14] in
                             uu___12 :: uu___13 in
                           uu___10 :: uu___11 in
                         uu___8 :: uu___9 in
                       uu___6 :: uu___7 in
                     uu___4 :: uu___5 in
                   FStarC_Syntax_Syntax.mk_Tm_app uu___2 uu___3 rng) in
        let un t norm =
          lazy_unembed printer1 emb_t_pair t typ
            (fun uu___ ->
               (fun t1 ->
                  let uu___ = FStarC_Syntax_Util.head_and_args_full t1 in
                  match uu___ with
                  | (hd, args) ->
                      let uu___1 =
                        let uu___2 =
                          let uu___3 = FStarC_Syntax_Util.un_uinst hd in
                          uu___3.FStarC_Syntax_Syntax.n in
                        (uu___2, args) in
                      (match uu___1 with
                       | (FStarC_Syntax_Syntax.Tm_fvar fv,
                          uu___2::uu___3::uu___4::(a1, uu___5)::(b1, uu___6)::
                          (c1, uu___7)::[]) when
                           FStarC_Syntax_Syntax.fv_eq_lid fv
                             FStarC_Parser_Const.lid_Mktuple3
                           ->
                           Obj.magic
                             (Obj.repr
                                (let uu___8 =
                                   FStarC_Syntax_Embeddings_Base.try_unembed
                                     ea a1 norm in
                                 FStarC_Class_Monad.op_let_Bang
                                   FStarC_Class_Monad.monad_option () ()
                                   (Obj.magic uu___8)
                                   (fun uu___9 ->
                                      (fun a2 ->
                                         let a2 = Obj.magic a2 in
                                         let uu___9 =
                                           FStarC_Syntax_Embeddings_Base.try_unembed
                                             eb b1 norm in
                                         Obj.magic
                                           (FStarC_Class_Monad.op_let_Bang
                                              FStarC_Class_Monad.monad_option
                                              () () (Obj.magic uu___9)
                                              (fun uu___10 ->
                                                 (fun b2 ->
                                                    let b2 = Obj.magic b2 in
                                                    let uu___10 =
                                                      FStarC_Syntax_Embeddings_Base.try_unembed
                                                        ec c1 norm in
                                                    Obj.magic
                                                      (FStarC_Class_Monad.op_let_Bang
                                                         FStarC_Class_Monad.monad_option
                                                         () ()
                                                         (Obj.magic uu___10)
                                                         (fun uu___11 ->
                                                            (fun c2 ->
                                                               let c2 =
                                                                 Obj.magic c2 in
                                                               Obj.magic
                                                                 (FStar_Pervasives_Native.Some
                                                                    (a2, b2,
                                                                    c2)))
                                                              uu___11)))
                                                   uu___10))) uu___9)))
                       | uu___2 ->
                           Obj.magic (Obj.repr FStar_Pervasives_Native.None)))
                 uu___) in
        FStarC_Syntax_Embeddings_Base.mk_emb_full em un typ printer1
          emb_t_pair
let e_tuple4 :
  'a 'b 'c 'd .
    'a FStarC_Syntax_Embeddings_Base.embedding ->
      'b FStarC_Syntax_Embeddings_Base.embedding ->
        'c FStarC_Syntax_Embeddings_Base.embedding ->
          'd FStarC_Syntax_Embeddings_Base.embedding ->
            ('a * 'b * 'c * 'd) FStarC_Syntax_Embeddings_Base.embedding
  =
  fun ea ->
    fun eb ->
      fun ec ->
        fun ed ->
          let typ uu___ =
            let uu___1 = FStarC_Syntax_Embeddings_Base.type_of ea in
            let uu___2 = FStarC_Syntax_Embeddings_Base.type_of eb in
            let uu___3 = FStarC_Syntax_Embeddings_Base.type_of ec in
            let uu___4 = FStarC_Syntax_Embeddings_Base.type_of ed in
            FStarC_Syntax_Syntax.t_tuple4_of uu___1 uu___2 uu___3 uu___4 in
          let emb_t_pair uu___ =
            let uu___1 =
              let uu___2 =
                FStarC_Ident.string_of_lid FStarC_Parser_Const.lid_tuple4 in
              let uu___3 =
                let uu___4 = FStarC_Syntax_Embeddings_Base.emb_typ_of ea () in
                let uu___5 =
                  let uu___6 = FStarC_Syntax_Embeddings_Base.emb_typ_of eb () in
                  let uu___7 =
                    let uu___8 =
                      FStarC_Syntax_Embeddings_Base.emb_typ_of ec () in
                    let uu___9 =
                      let uu___10 =
                        FStarC_Syntax_Embeddings_Base.emb_typ_of ed () in
                      [uu___10] in
                    uu___8 :: uu___9 in
                  uu___6 :: uu___7 in
                uu___4 :: uu___5 in
              (uu___2, uu___3) in
            FStarC_Syntax_Syntax.ET_app uu___1 in
          let printer1 uu___ =
            match uu___ with
            | (x, y, z, w) ->
                let uu___1 =
                  let uu___2 = FStarC_Syntax_Embeddings_Base.printer_of ea in
                  uu___2 x in
                let uu___2 =
                  let uu___3 = FStarC_Syntax_Embeddings_Base.printer_of eb in
                  uu___3 y in
                let uu___3 =
                  let uu___4 = FStarC_Syntax_Embeddings_Base.printer_of ec in
                  uu___4 z in
                let uu___4 =
                  let uu___5 = FStarC_Syntax_Embeddings_Base.printer_of ed in
                  uu___5 w in
                FStarC_Compiler_Util.format4 "(%s, %s, %s, %s)" uu___1 uu___2
                  uu___3 uu___4 in
          let em uu___ rng shadow norm =
            match uu___ with
            | (x1, x2, x3, x4) ->
                lazy_embed printer1 emb_t_pair rng typ (x1, x2, x3, x4)
                  (fun uu___1 ->
                     let proj i abcd =
                       let proj_i =
                         let uu___2 =
                           FStarC_Parser_Const.mk_tuple_data_lid
                             (Prims.of_int (4)) rng in
                         let uu___3 =
                           FStarC_Syntax_Syntax.null_bv
                             FStarC_Syntax_Syntax.tun in
                         FStarC_Syntax_Util.mk_field_projector_name uu___2
                           uu___3 i in
                       let proj_i_tm =
                         let uu___2 =
                           FStarC_Syntax_Syntax.lid_as_fv proj_i
                             FStar_Pervasives_Native.None in
                         FStarC_Syntax_Syntax.fv_to_tm uu___2 in
                       let uu___2 =
                         FStarC_Syntax_Syntax.mk_Tm_uinst proj_i_tm
                           [FStarC_Syntax_Syntax.U_zero] in
                       let uu___3 =
                         let uu___4 =
                           let uu___5 =
                             FStarC_Syntax_Embeddings_Base.type_of ea in
                           FStarC_Syntax_Syntax.iarg uu___5 in
                         let uu___5 =
                           let uu___6 =
                             let uu___7 =
                               FStarC_Syntax_Embeddings_Base.type_of eb in
                             FStarC_Syntax_Syntax.iarg uu___7 in
                           let uu___7 =
                             let uu___8 =
                               let uu___9 =
                                 FStarC_Syntax_Embeddings_Base.type_of ec in
                               FStarC_Syntax_Syntax.iarg uu___9 in
                             let uu___9 =
                               let uu___10 =
                                 let uu___11 =
                                   FStarC_Syntax_Embeddings_Base.type_of ed in
                                 FStarC_Syntax_Syntax.iarg uu___11 in
                               let uu___11 =
                                 let uu___12 =
                                   FStarC_Syntax_Syntax.as_arg abcd in
                                 [uu___12] in
                               uu___10 :: uu___11 in
                             uu___8 :: uu___9 in
                           uu___6 :: uu___7 in
                         uu___4 :: uu___5 in
                       FStarC_Syntax_Syntax.mk_Tm_app uu___2 uu___3 rng in
                     let shadow_a = map_shadow shadow (proj Prims.int_one) in
                     let shadow_b =
                       map_shadow shadow (proj (Prims.of_int (2))) in
                     let shadow_c =
                       map_shadow shadow (proj (Prims.of_int (3))) in
                     let shadow_d =
                       map_shadow shadow (proj (Prims.of_int (4))) in
                     let uu___2 =
                       let uu___3 =
                         FStarC_Syntax_Syntax.tdataconstr
                           FStarC_Parser_Const.lid_Mktuple4 in
                       FStarC_Syntax_Syntax.mk_Tm_uinst uu___3
                         [FStarC_Syntax_Syntax.U_zero;
                         FStarC_Syntax_Syntax.U_zero;
                         FStarC_Syntax_Syntax.U_zero;
                         FStarC_Syntax_Syntax.U_zero] in
                     let uu___3 =
                       let uu___4 =
                         let uu___5 =
                           FStarC_Syntax_Embeddings_Base.type_of ea in
                         FStarC_Syntax_Syntax.iarg uu___5 in
                       let uu___5 =
                         let uu___6 =
                           let uu___7 =
                             FStarC_Syntax_Embeddings_Base.type_of eb in
                           FStarC_Syntax_Syntax.iarg uu___7 in
                         let uu___7 =
                           let uu___8 =
                             let uu___9 =
                               FStarC_Syntax_Embeddings_Base.type_of ec in
                             FStarC_Syntax_Syntax.iarg uu___9 in
                           let uu___9 =
                             let uu___10 =
                               let uu___11 =
                                 FStarC_Syntax_Embeddings_Base.type_of ed in
                               FStarC_Syntax_Syntax.iarg uu___11 in
                             let uu___11 =
                               let uu___12 =
                                 let uu___13 =
                                   let uu___14 =
                                     FStarC_Syntax_Embeddings_Base.embed ea
                                       x1 in
                                   uu___14 rng shadow_a norm in
                                 FStarC_Syntax_Syntax.as_arg uu___13 in
                               let uu___13 =
                                 let uu___14 =
                                   let uu___15 =
                                     let uu___16 =
                                       FStarC_Syntax_Embeddings_Base.embed eb
                                         x2 in
                                     uu___16 rng shadow_b norm in
                                   FStarC_Syntax_Syntax.as_arg uu___15 in
                                 let uu___15 =
                                   let uu___16 =
                                     let uu___17 =
                                       let uu___18 =
                                         FStarC_Syntax_Embeddings_Base.embed
                                           ec x3 in
                                       uu___18 rng shadow_c norm in
                                     FStarC_Syntax_Syntax.as_arg uu___17 in
                                   let uu___17 =
                                     let uu___18 =
                                       let uu___19 =
                                         let uu___20 =
                                           FStarC_Syntax_Embeddings_Base.embed
                                             ed x4 in
                                         uu___20 rng shadow_d norm in
                                       FStarC_Syntax_Syntax.as_arg uu___19 in
                                     [uu___18] in
                                   uu___16 :: uu___17 in
                                 uu___14 :: uu___15 in
                               uu___12 :: uu___13 in
                             uu___10 :: uu___11 in
                           uu___8 :: uu___9 in
                         uu___6 :: uu___7 in
                       uu___4 :: uu___5 in
                     FStarC_Syntax_Syntax.mk_Tm_app uu___2 uu___3 rng) in
          let un t norm =
            lazy_unembed printer1 emb_t_pair t typ
              (fun uu___ ->
                 (fun t1 ->
                    let uu___ = FStarC_Syntax_Util.head_and_args_full t1 in
                    match uu___ with
                    | (hd, args) ->
                        let uu___1 =
                          let uu___2 =
                            let uu___3 = FStarC_Syntax_Util.un_uinst hd in
                            uu___3.FStarC_Syntax_Syntax.n in
                          (uu___2, args) in
                        (match uu___1 with
                         | (FStarC_Syntax_Syntax.Tm_fvar fv,
                            uu___2::uu___3::uu___4::uu___5::(a1, uu___6)::
                            (b1, uu___7)::(c1, uu___8)::(d1, uu___9)::[])
                             when
                             FStarC_Syntax_Syntax.fv_eq_lid fv
                               FStarC_Parser_Const.lid_Mktuple4
                             ->
                             Obj.magic
                               (Obj.repr
                                  (let uu___10 =
                                     FStarC_Syntax_Embeddings_Base.try_unembed
                                       ea a1 norm in
                                   FStarC_Class_Monad.op_let_Bang
                                     FStarC_Class_Monad.monad_option () ()
                                     (Obj.magic uu___10)
                                     (fun uu___11 ->
                                        (fun a2 ->
                                           let a2 = Obj.magic a2 in
                                           let uu___11 =
                                             FStarC_Syntax_Embeddings_Base.try_unembed
                                               eb b1 norm in
                                           Obj.magic
                                             (FStarC_Class_Monad.op_let_Bang
                                                FStarC_Class_Monad.monad_option
                                                () () (Obj.magic uu___11)
                                                (fun uu___12 ->
                                                   (fun b2 ->
                                                      let b2 = Obj.magic b2 in
                                                      let uu___12 =
                                                        FStarC_Syntax_Embeddings_Base.try_unembed
                                                          ec c1 norm in
                                                      Obj.magic
                                                        (FStarC_Class_Monad.op_let_Bang
                                                           FStarC_Class_Monad.monad_option
                                                           () ()
                                                           (Obj.magic uu___12)
                                                           (fun uu___13 ->
                                                              (fun c2 ->
                                                                 let c2 =
                                                                   Obj.magic
                                                                    c2 in
                                                                 let uu___13
                                                                   =
                                                                   FStarC_Syntax_Embeddings_Base.try_unembed
                                                                    ed d1
                                                                    norm in
                                                                 Obj.magic
                                                                   (FStarC_Class_Monad.op_let_Bang
                                                                    FStarC_Class_Monad.monad_option
                                                                    () ()
                                                                    (Obj.magic
                                                                    uu___13)
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    (fun d2
                                                                    ->
                                                                    let d2 =
                                                                    Obj.magic
                                                                    d2 in
                                                                    Obj.magic
                                                                    (FStar_Pervasives_Native.Some
                                                                    (a2, b2,
                                                                    c2, d2)))
                                                                    uu___14)))
                                                                uu___13)))
                                                     uu___12))) uu___11)))
                         | uu___2 ->
                             Obj.magic
                               (Obj.repr FStar_Pervasives_Native.None)))
                   uu___) in
          FStarC_Syntax_Embeddings_Base.mk_emb_full em un typ printer1
            emb_t_pair
let e_tuple5 :
  'a 'b 'c 'd 'e .
    'a FStarC_Syntax_Embeddings_Base.embedding ->
      'b FStarC_Syntax_Embeddings_Base.embedding ->
        'c FStarC_Syntax_Embeddings_Base.embedding ->
          'd FStarC_Syntax_Embeddings_Base.embedding ->
            'e FStarC_Syntax_Embeddings_Base.embedding ->
              ('a * 'b * 'c * 'd * 'e)
                FStarC_Syntax_Embeddings_Base.embedding
  =
  fun ea ->
    fun eb ->
      fun ec ->
        fun ed ->
          fun ee ->
            let typ uu___ =
              let uu___1 = FStarC_Syntax_Embeddings_Base.type_of ea in
              let uu___2 = FStarC_Syntax_Embeddings_Base.type_of eb in
              let uu___3 = FStarC_Syntax_Embeddings_Base.type_of ec in
              let uu___4 = FStarC_Syntax_Embeddings_Base.type_of ed in
              let uu___5 = FStarC_Syntax_Embeddings_Base.type_of ee in
              FStarC_Syntax_Syntax.t_tuple5_of uu___1 uu___2 uu___3 uu___4
                uu___5 in
            let emb_t_pair uu___ =
              let uu___1 =
                let uu___2 =
                  FStarC_Ident.string_of_lid FStarC_Parser_Const.lid_tuple5 in
                let uu___3 =
                  let uu___4 = FStarC_Syntax_Embeddings_Base.emb_typ_of ea () in
                  let uu___5 =
                    let uu___6 =
                      FStarC_Syntax_Embeddings_Base.emb_typ_of eb () in
                    let uu___7 =
                      let uu___8 =
                        FStarC_Syntax_Embeddings_Base.emb_typ_of ec () in
                      let uu___9 =
                        let uu___10 =
                          FStarC_Syntax_Embeddings_Base.emb_typ_of ed () in
                        let uu___11 =
                          let uu___12 =
                            FStarC_Syntax_Embeddings_Base.emb_typ_of ee () in
                          [uu___12] in
                        uu___10 :: uu___11 in
                      uu___8 :: uu___9 in
                    uu___6 :: uu___7 in
                  uu___4 :: uu___5 in
                (uu___2, uu___3) in
              FStarC_Syntax_Syntax.ET_app uu___1 in
            let printer1 uu___ =
              match uu___ with
              | (x, y, z, w, v) ->
                  let uu___1 =
                    let uu___2 = FStarC_Syntax_Embeddings_Base.printer_of ea in
                    uu___2 x in
                  let uu___2 =
                    let uu___3 = FStarC_Syntax_Embeddings_Base.printer_of eb in
                    uu___3 y in
                  let uu___3 =
                    let uu___4 = FStarC_Syntax_Embeddings_Base.printer_of ec in
                    uu___4 z in
                  let uu___4 =
                    let uu___5 = FStarC_Syntax_Embeddings_Base.printer_of ed in
                    uu___5 w in
                  let uu___5 =
                    let uu___6 = FStarC_Syntax_Embeddings_Base.printer_of ee in
                    uu___6 v in
                  FStarC_Compiler_Util.format5 "(%s, %s, %s, %s, %s)" uu___1
                    uu___2 uu___3 uu___4 uu___5 in
            let em uu___ rng shadow norm =
              match uu___ with
              | (x1, x2, x3, x4, x5) ->
                  lazy_embed printer1 emb_t_pair rng typ (x1, x2, x3, x4, x5)
                    (fun uu___1 ->
                       let proj i abcde =
                         let proj_i =
                           let uu___2 =
                             FStarC_Parser_Const.mk_tuple_data_lid
                               (Prims.of_int (5)) rng in
                           let uu___3 =
                             FStarC_Syntax_Syntax.null_bv
                               FStarC_Syntax_Syntax.tun in
                           FStarC_Syntax_Util.mk_field_projector_name uu___2
                             uu___3 i in
                         let proj_i_tm =
                           let uu___2 =
                             FStarC_Syntax_Syntax.lid_as_fv proj_i
                               FStar_Pervasives_Native.None in
                           FStarC_Syntax_Syntax.fv_to_tm uu___2 in
                         let uu___2 =
                           FStarC_Syntax_Syntax.mk_Tm_uinst proj_i_tm
                             [FStarC_Syntax_Syntax.U_zero] in
                         let uu___3 =
                           let uu___4 =
                             let uu___5 =
                               FStarC_Syntax_Embeddings_Base.type_of ea in
                             FStarC_Syntax_Syntax.iarg uu___5 in
                           let uu___5 =
                             let uu___6 =
                               let uu___7 =
                                 FStarC_Syntax_Embeddings_Base.type_of eb in
                               FStarC_Syntax_Syntax.iarg uu___7 in
                             let uu___7 =
                               let uu___8 =
                                 let uu___9 =
                                   FStarC_Syntax_Embeddings_Base.type_of ec in
                                 FStarC_Syntax_Syntax.iarg uu___9 in
                               let uu___9 =
                                 let uu___10 =
                                   let uu___11 =
                                     FStarC_Syntax_Embeddings_Base.type_of ed in
                                   FStarC_Syntax_Syntax.iarg uu___11 in
                                 let uu___11 =
                                   let uu___12 =
                                     let uu___13 =
                                       FStarC_Syntax_Embeddings_Base.type_of
                                         ee in
                                     FStarC_Syntax_Syntax.iarg uu___13 in
                                   let uu___13 =
                                     let uu___14 =
                                       FStarC_Syntax_Syntax.as_arg abcde in
                                     [uu___14] in
                                   uu___12 :: uu___13 in
                                 uu___10 :: uu___11 in
                               uu___8 :: uu___9 in
                             uu___6 :: uu___7 in
                           uu___4 :: uu___5 in
                         FStarC_Syntax_Syntax.mk_Tm_app uu___2 uu___3 rng in
                       let shadow_a = map_shadow shadow (proj Prims.int_one) in
                       let shadow_b =
                         map_shadow shadow (proj (Prims.of_int (2))) in
                       let shadow_c =
                         map_shadow shadow (proj (Prims.of_int (3))) in
                       let shadow_d =
                         map_shadow shadow (proj (Prims.of_int (4))) in
                       let shadow_e =
                         map_shadow shadow (proj (Prims.of_int (5))) in
                       let uu___2 =
                         let uu___3 =
                           FStarC_Syntax_Syntax.tdataconstr
                             FStarC_Parser_Const.lid_Mktuple5 in
                         FStarC_Syntax_Syntax.mk_Tm_uinst uu___3
                           [FStarC_Syntax_Syntax.U_zero;
                           FStarC_Syntax_Syntax.U_zero;
                           FStarC_Syntax_Syntax.U_zero;
                           FStarC_Syntax_Syntax.U_zero;
                           FStarC_Syntax_Syntax.U_zero] in
                       let uu___3 =
                         let uu___4 =
                           let uu___5 =
                             FStarC_Syntax_Embeddings_Base.type_of ea in
                           FStarC_Syntax_Syntax.iarg uu___5 in
                         let uu___5 =
                           let uu___6 =
                             let uu___7 =
                               FStarC_Syntax_Embeddings_Base.type_of eb in
                             FStarC_Syntax_Syntax.iarg uu___7 in
                           let uu___7 =
                             let uu___8 =
                               let uu___9 =
                                 FStarC_Syntax_Embeddings_Base.type_of ec in
                               FStarC_Syntax_Syntax.iarg uu___9 in
                             let uu___9 =
                               let uu___10 =
                                 let uu___11 =
                                   FStarC_Syntax_Embeddings_Base.type_of ed in
                                 FStarC_Syntax_Syntax.iarg uu___11 in
                               let uu___11 =
                                 let uu___12 =
                                   let uu___13 =
                                     FStarC_Syntax_Embeddings_Base.type_of ee in
                                   FStarC_Syntax_Syntax.iarg uu___13 in
                                 let uu___13 =
                                   let uu___14 =
                                     let uu___15 =
                                       let uu___16 =
                                         FStarC_Syntax_Embeddings_Base.embed
                                           ea x1 in
                                       uu___16 rng shadow_a norm in
                                     FStarC_Syntax_Syntax.as_arg uu___15 in
                                   let uu___15 =
                                     let uu___16 =
                                       let uu___17 =
                                         let uu___18 =
                                           FStarC_Syntax_Embeddings_Base.embed
                                             eb x2 in
                                         uu___18 rng shadow_b norm in
                                       FStarC_Syntax_Syntax.as_arg uu___17 in
                                     let uu___17 =
                                       let uu___18 =
                                         let uu___19 =
                                           let uu___20 =
                                             FStarC_Syntax_Embeddings_Base.embed
                                               ec x3 in
                                           uu___20 rng shadow_c norm in
                                         FStarC_Syntax_Syntax.as_arg uu___19 in
                                       let uu___19 =
                                         let uu___20 =
                                           let uu___21 =
                                             let uu___22 =
                                               FStarC_Syntax_Embeddings_Base.embed
                                                 ed x4 in
                                             uu___22 rng shadow_d norm in
                                           FStarC_Syntax_Syntax.as_arg
                                             uu___21 in
                                         let uu___21 =
                                           let uu___22 =
                                             let uu___23 =
                                               let uu___24 =
                                                 FStarC_Syntax_Embeddings_Base.embed
                                                   ee x5 in
                                               uu___24 rng shadow_e norm in
                                             FStarC_Syntax_Syntax.as_arg
                                               uu___23 in
                                           [uu___22] in
                                         uu___20 :: uu___21 in
                                       uu___18 :: uu___19 in
                                     uu___16 :: uu___17 in
                                   uu___14 :: uu___15 in
                                 uu___12 :: uu___13 in
                               uu___10 :: uu___11 in
                             uu___8 :: uu___9 in
                           uu___6 :: uu___7 in
                         uu___4 :: uu___5 in
                       FStarC_Syntax_Syntax.mk_Tm_app uu___2 uu___3 rng) in
            let un t norm =
              lazy_unembed printer1 emb_t_pair t typ
                (fun uu___ ->
                   (fun t1 ->
                      let uu___ = FStarC_Syntax_Util.head_and_args_full t1 in
                      match uu___ with
                      | (hd, args) ->
                          let uu___1 =
                            let uu___2 =
                              let uu___3 = FStarC_Syntax_Util.un_uinst hd in
                              uu___3.FStarC_Syntax_Syntax.n in
                            (uu___2, args) in
                          (match uu___1 with
                           | (FStarC_Syntax_Syntax.Tm_fvar fv,
                              uu___2::uu___3::uu___4::uu___5::uu___6::
                              (a1, uu___7)::(b1, uu___8)::(c1, uu___9)::
                              (d1, uu___10)::(e1, uu___11)::[]) when
                               FStarC_Syntax_Syntax.fv_eq_lid fv
                                 FStarC_Parser_Const.lid_Mktuple5
                               ->
                               Obj.magic
                                 (Obj.repr
                                    (let uu___12 =
                                       FStarC_Syntax_Embeddings_Base.try_unembed
                                         ea a1 norm in
                                     FStarC_Class_Monad.op_let_Bang
                                       FStarC_Class_Monad.monad_option () ()
                                       (Obj.magic uu___12)
                                       (fun uu___13 ->
                                          (fun a2 ->
                                             let a2 = Obj.magic a2 in
                                             let uu___13 =
                                               FStarC_Syntax_Embeddings_Base.try_unembed
                                                 eb b1 norm in
                                             Obj.magic
                                               (FStarC_Class_Monad.op_let_Bang
                                                  FStarC_Class_Monad.monad_option
                                                  () () (Obj.magic uu___13)
                                                  (fun uu___14 ->
                                                     (fun b2 ->
                                                        let b2 = Obj.magic b2 in
                                                        let uu___14 =
                                                          FStarC_Syntax_Embeddings_Base.try_unembed
                                                            ec c1 norm in
                                                        Obj.magic
                                                          (FStarC_Class_Monad.op_let_Bang
                                                             FStarC_Class_Monad.monad_option
                                                             () ()
                                                             (Obj.magic
                                                                uu___14)
                                                             (fun uu___15 ->
                                                                (fun c2 ->
                                                                   let c2 =
                                                                    Obj.magic
                                                                    c2 in
                                                                   let uu___15
                                                                    =
                                                                    FStarC_Syntax_Embeddings_Base.try_unembed
                                                                    ed d1
                                                                    norm in
                                                                   Obj.magic
                                                                    (FStarC_Class_Monad.op_let_Bang
                                                                    FStarC_Class_Monad.monad_option
                                                                    () ()
                                                                    (Obj.magic
                                                                    uu___15)
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    (fun d2
                                                                    ->
                                                                    let d2 =
                                                                    Obj.magic
                                                                    d2 in
                                                                    let uu___16
                                                                    =
                                                                    FStarC_Syntax_Embeddings_Base.try_unembed
                                                                    ee e1
                                                                    norm in
                                                                    Obj.magic
                                                                    (FStarC_Class_Monad.op_let_Bang
                                                                    FStarC_Class_Monad.monad_option
                                                                    () ()
                                                                    (Obj.magic
                                                                    uu___16)
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    (fun e2
                                                                    ->
                                                                    let e2 =
                                                                    Obj.magic
                                                                    e2 in
                                                                    Obj.magic
                                                                    (FStar_Pervasives_Native.Some
                                                                    (a2, b2,
                                                                    c2, d2,
                                                                    e2)))
                                                                    uu___17)))
                                                                    uu___16)))
                                                                  uu___15)))
                                                       uu___14))) uu___13)))
                           | uu___2 ->
                               Obj.magic
                                 (Obj.repr FStar_Pervasives_Native.None)))
                     uu___) in
            FStarC_Syntax_Embeddings_Base.mk_emb_full em un typ printer1
              emb_t_pair
let e_either :
  'a 'b .
    'a FStarC_Syntax_Embeddings_Base.embedding ->
      'b FStarC_Syntax_Embeddings_Base.embedding ->
        ('a, 'b) FStar_Pervasives.either
          FStarC_Syntax_Embeddings_Base.embedding
  =
  fun ea ->
    fun eb ->
      let typ uu___ =
        let uu___1 = FStarC_Syntax_Embeddings_Base.type_of ea in
        let uu___2 = FStarC_Syntax_Embeddings_Base.type_of eb in
        FStarC_Syntax_Syntax.t_either_of uu___1 uu___2 in
      let emb_t_sum_a_b uu___ =
        let uu___1 =
          let uu___2 =
            FStarC_Ident.string_of_lid FStarC_Parser_Const.either_lid in
          let uu___3 =
            let uu___4 = FStarC_Syntax_Embeddings_Base.emb_typ_of ea () in
            let uu___5 =
              let uu___6 = FStarC_Syntax_Embeddings_Base.emb_typ_of eb () in
              [uu___6] in
            uu___4 :: uu___5 in
          (uu___2, uu___3) in
        FStarC_Syntax_Syntax.ET_app uu___1 in
      let printer1 s =
        match s with
        | FStar_Pervasives.Inl a1 ->
            let uu___ =
              let uu___1 = FStarC_Syntax_Embeddings_Base.printer_of ea in
              uu___1 a1 in
            FStarC_Compiler_Util.format1 "Inl %s" uu___
        | FStar_Pervasives.Inr b1 ->
            let uu___ =
              let uu___1 = FStarC_Syntax_Embeddings_Base.printer_of eb in
              uu___1 b1 in
            FStarC_Compiler_Util.format1 "Inr %s" uu___ in
      let em s rng shadow norm =
        lazy_embed printer1 emb_t_sum_a_b rng typ s
          (match s with
           | FStar_Pervasives.Inl a1 ->
               (fun uu___ ->
                  let shadow_a =
                    map_shadow shadow
                      (fun t ->
                         let v = FStarC_Ident.mk_ident ("v", rng) in
                         let some_v =
                           FStarC_Syntax_Util.mk_field_projector_name_from_ident
                             FStarC_Parser_Const.inl_lid v in
                         let some_v_tm =
                           let uu___1 =
                             FStarC_Syntax_Syntax.lid_as_fv some_v
                               FStar_Pervasives_Native.None in
                           FStarC_Syntax_Syntax.fv_to_tm uu___1 in
                         let uu___1 =
                           FStarC_Syntax_Syntax.mk_Tm_uinst some_v_tm
                             [FStarC_Syntax_Syntax.U_zero] in
                         let uu___2 =
                           let uu___3 =
                             let uu___4 =
                               FStarC_Syntax_Embeddings_Base.type_of ea in
                             FStarC_Syntax_Syntax.iarg uu___4 in
                           let uu___4 =
                             let uu___5 =
                               let uu___6 =
                                 FStarC_Syntax_Embeddings_Base.type_of eb in
                               FStarC_Syntax_Syntax.iarg uu___6 in
                             let uu___6 =
                               let uu___7 = FStarC_Syntax_Syntax.as_arg t in
                               [uu___7] in
                             uu___5 :: uu___6 in
                           uu___3 :: uu___4 in
                         FStarC_Syntax_Syntax.mk_Tm_app uu___1 uu___2 rng) in
                  let uu___1 =
                    let uu___2 =
                      FStarC_Syntax_Syntax.tdataconstr
                        FStarC_Parser_Const.inl_lid in
                    FStarC_Syntax_Syntax.mk_Tm_uinst uu___2
                      [FStarC_Syntax_Syntax.U_zero;
                      FStarC_Syntax_Syntax.U_zero] in
                  let uu___2 =
                    let uu___3 =
                      let uu___4 = FStarC_Syntax_Embeddings_Base.type_of ea in
                      FStarC_Syntax_Syntax.iarg uu___4 in
                    let uu___4 =
                      let uu___5 =
                        let uu___6 = FStarC_Syntax_Embeddings_Base.type_of eb in
                        FStarC_Syntax_Syntax.iarg uu___6 in
                      let uu___6 =
                        let uu___7 =
                          let uu___8 =
                            let uu___9 =
                              FStarC_Syntax_Embeddings_Base.embed ea a1 in
                            uu___9 rng shadow_a norm in
                          FStarC_Syntax_Syntax.as_arg uu___8 in
                        [uu___7] in
                      uu___5 :: uu___6 in
                    uu___3 :: uu___4 in
                  FStarC_Syntax_Syntax.mk_Tm_app uu___1 uu___2 rng)
           | FStar_Pervasives.Inr b1 ->
               (fun uu___ ->
                  let shadow_b =
                    map_shadow shadow
                      (fun t ->
                         let v = FStarC_Ident.mk_ident ("v", rng) in
                         let some_v =
                           FStarC_Syntax_Util.mk_field_projector_name_from_ident
                             FStarC_Parser_Const.inr_lid v in
                         let some_v_tm =
                           let uu___1 =
                             FStarC_Syntax_Syntax.lid_as_fv some_v
                               FStar_Pervasives_Native.None in
                           FStarC_Syntax_Syntax.fv_to_tm uu___1 in
                         let uu___1 =
                           FStarC_Syntax_Syntax.mk_Tm_uinst some_v_tm
                             [FStarC_Syntax_Syntax.U_zero] in
                         let uu___2 =
                           let uu___3 =
                             let uu___4 =
                               FStarC_Syntax_Embeddings_Base.type_of ea in
                             FStarC_Syntax_Syntax.iarg uu___4 in
                           let uu___4 =
                             let uu___5 =
                               let uu___6 =
                                 FStarC_Syntax_Embeddings_Base.type_of eb in
                               FStarC_Syntax_Syntax.iarg uu___6 in
                             let uu___6 =
                               let uu___7 = FStarC_Syntax_Syntax.as_arg t in
                               [uu___7] in
                             uu___5 :: uu___6 in
                           uu___3 :: uu___4 in
                         FStarC_Syntax_Syntax.mk_Tm_app uu___1 uu___2 rng) in
                  let uu___1 =
                    let uu___2 =
                      FStarC_Syntax_Syntax.tdataconstr
                        FStarC_Parser_Const.inr_lid in
                    FStarC_Syntax_Syntax.mk_Tm_uinst uu___2
                      [FStarC_Syntax_Syntax.U_zero;
                      FStarC_Syntax_Syntax.U_zero] in
                  let uu___2 =
                    let uu___3 =
                      let uu___4 = FStarC_Syntax_Embeddings_Base.type_of ea in
                      FStarC_Syntax_Syntax.iarg uu___4 in
                    let uu___4 =
                      let uu___5 =
                        let uu___6 = FStarC_Syntax_Embeddings_Base.type_of eb in
                        FStarC_Syntax_Syntax.iarg uu___6 in
                      let uu___6 =
                        let uu___7 =
                          let uu___8 =
                            let uu___9 =
                              FStarC_Syntax_Embeddings_Base.embed eb b1 in
                            uu___9 rng shadow_b norm in
                          FStarC_Syntax_Syntax.as_arg uu___8 in
                        [uu___7] in
                      uu___5 :: uu___6 in
                    uu___3 :: uu___4 in
                  FStarC_Syntax_Syntax.mk_Tm_app uu___1 uu___2 rng)) in
      let un t norm =
        lazy_unembed printer1 emb_t_sum_a_b t typ
          (fun t1 ->
             let uu___ = FStarC_Syntax_Util.head_and_args_full t1 in
             match uu___ with
             | (hd, args) ->
                 let uu___1 =
                   let uu___2 =
                     let uu___3 = FStarC_Syntax_Util.un_uinst hd in
                     uu___3.FStarC_Syntax_Syntax.n in
                   (uu___2, args) in
                 (match uu___1 with
                  | (FStarC_Syntax_Syntax.Tm_fvar fv,
                     uu___2::uu___3::(a1, uu___4)::[]) when
                      FStarC_Syntax_Syntax.fv_eq_lid fv
                        FStarC_Parser_Const.inl_lid
                      ->
                      let uu___5 =
                        FStarC_Syntax_Embeddings_Base.try_unembed ea a1 norm in
                      FStarC_Compiler_Util.bind_opt uu___5
                        (fun a2 ->
                           FStar_Pervasives_Native.Some
                             (FStar_Pervasives.Inl a2))
                  | (FStarC_Syntax_Syntax.Tm_fvar fv,
                     uu___2::uu___3::(b1, uu___4)::[]) when
                      FStarC_Syntax_Syntax.fv_eq_lid fv
                        FStarC_Parser_Const.inr_lid
                      ->
                      let uu___5 =
                        FStarC_Syntax_Embeddings_Base.try_unembed eb b1 norm in
                      FStarC_Compiler_Util.bind_opt uu___5
                        (fun b2 ->
                           FStar_Pervasives_Native.Some
                             (FStar_Pervasives.Inr b2))
                  | uu___2 -> FStar_Pervasives_Native.None)) in
      FStarC_Syntax_Embeddings_Base.mk_emb_full em un typ printer1
        emb_t_sum_a_b
let e_list :
  'a .
    'a FStarC_Syntax_Embeddings_Base.embedding ->
      'a Prims.list FStarC_Syntax_Embeddings_Base.embedding
  =
  fun ea ->
    let typ uu___ =
      let uu___1 = FStarC_Syntax_Embeddings_Base.type_of ea in
      FStarC_Syntax_Syntax.t_list_of uu___1 in
    let emb_t_list_a uu___ =
      let uu___1 =
        let uu___2 = FStarC_Ident.string_of_lid FStarC_Parser_Const.list_lid in
        let uu___3 =
          let uu___4 = FStarC_Syntax_Embeddings_Base.emb_typ_of ea () in
          [uu___4] in
        (uu___2, uu___3) in
      FStarC_Syntax_Syntax.ET_app uu___1 in
    let printer1 l =
      let uu___ =
        let uu___1 =
          let uu___2 =
            let uu___3 = FStarC_Syntax_Embeddings_Base.printer_of ea in
            FStarC_Compiler_List.map uu___3 l in
          FStarC_Compiler_String.concat "; " uu___2 in
        Prims.strcat uu___1 "]" in
      Prims.strcat "[" uu___ in
    let rec em l rng shadow_l norm =
      lazy_embed printer1 emb_t_list_a rng typ l
        (fun uu___ ->
           let t =
             let uu___1 = FStarC_Syntax_Embeddings_Base.type_of ea in
             FStarC_Syntax_Syntax.iarg uu___1 in
           match l with
           | [] ->
               let uu___1 =
                 let uu___2 =
                   FStarC_Syntax_Syntax.tdataconstr
                     FStarC_Parser_Const.nil_lid in
                 FStarC_Syntax_Syntax.mk_Tm_uinst uu___2
                   [FStarC_Syntax_Syntax.U_zero] in
               FStarC_Syntax_Syntax.mk_Tm_app uu___1 [t] rng
           | hd::tl ->
               let cons =
                 let uu___1 =
                   FStarC_Syntax_Syntax.tdataconstr
                     FStarC_Parser_Const.cons_lid in
                 FStarC_Syntax_Syntax.mk_Tm_uinst uu___1
                   [FStarC_Syntax_Syntax.U_zero] in
               let proj f cons_tm =
                 let fid = FStarC_Ident.mk_ident (f, rng) in
                 let proj1 =
                   FStarC_Syntax_Util.mk_field_projector_name_from_ident
                     FStarC_Parser_Const.cons_lid fid in
                 let proj_tm =
                   let uu___1 =
                     FStarC_Syntax_Syntax.lid_as_fv proj1
                       FStar_Pervasives_Native.None in
                   FStarC_Syntax_Syntax.fv_to_tm uu___1 in
                 let uu___1 =
                   FStarC_Syntax_Syntax.mk_Tm_uinst proj_tm
                     [FStarC_Syntax_Syntax.U_zero] in
                 let uu___2 =
                   let uu___3 =
                     let uu___4 = FStarC_Syntax_Embeddings_Base.type_of ea in
                     FStarC_Syntax_Syntax.iarg uu___4 in
                   let uu___4 =
                     let uu___5 = FStarC_Syntax_Syntax.as_arg cons_tm in
                     [uu___5] in
                   uu___3 :: uu___4 in
                 FStarC_Syntax_Syntax.mk_Tm_app uu___1 uu___2 rng in
               let shadow_hd = map_shadow shadow_l (proj "hd") in
               let shadow_tl = map_shadow shadow_l (proj "tl") in
               let uu___1 =
                 let uu___2 =
                   let uu___3 =
                     let uu___4 =
                       let uu___5 = FStarC_Syntax_Embeddings_Base.embed ea hd in
                       uu___5 rng shadow_hd norm in
                     FStarC_Syntax_Syntax.as_arg uu___4 in
                   let uu___4 =
                     let uu___5 =
                       let uu___6 = em tl rng shadow_tl norm in
                       FStarC_Syntax_Syntax.as_arg uu___6 in
                     [uu___5] in
                   uu___3 :: uu___4 in
                 t :: uu___2 in
               FStarC_Syntax_Syntax.mk_Tm_app cons uu___1 rng) in
    let rec un t norm =
      lazy_unembed printer1 emb_t_list_a t typ
        (fun t1 ->
           let uu___ = FStarC_Syntax_Util.head_and_args_full t1 in
           match uu___ with
           | (hd, args) ->
               let uu___1 =
                 let uu___2 =
                   let uu___3 = FStarC_Syntax_Util.un_uinst hd in
                   uu___3.FStarC_Syntax_Syntax.n in
                 (uu___2, args) in
               (match uu___1 with
                | (FStarC_Syntax_Syntax.Tm_fvar fv, uu___2) when
                    FStarC_Syntax_Syntax.fv_eq_lid fv
                      FStarC_Parser_Const.nil_lid
                    -> FStar_Pervasives_Native.Some []
                | (FStarC_Syntax_Syntax.Tm_fvar fv,
                   (uu___2, FStar_Pervasives_Native.Some
                    { FStarC_Syntax_Syntax.aqual_implicit = true;
                      FStarC_Syntax_Syntax.aqual_attributes = uu___3;_})::
                   (hd1, FStar_Pervasives_Native.None)::(tl,
                                                         FStar_Pervasives_Native.None)::[])
                    when
                    FStarC_Syntax_Syntax.fv_eq_lid fv
                      FStarC_Parser_Const.cons_lid
                    ->
                    let uu___4 =
                      FStarC_Syntax_Embeddings_Base.try_unembed ea hd1 norm in
                    FStarC_Compiler_Util.bind_opt uu___4
                      (fun hd2 ->
                         let uu___5 = un tl norm in
                         FStarC_Compiler_Util.bind_opt uu___5
                           (fun tl1 ->
                              FStar_Pervasives_Native.Some (hd2 :: tl1)))
                | (FStarC_Syntax_Syntax.Tm_fvar fv,
                   (hd1, FStar_Pervasives_Native.None)::(tl,
                                                         FStar_Pervasives_Native.None)::[])
                    when
                    FStarC_Syntax_Syntax.fv_eq_lid fv
                      FStarC_Parser_Const.cons_lid
                    ->
                    let uu___2 =
                      FStarC_Syntax_Embeddings_Base.try_unembed ea hd1 norm in
                    FStarC_Compiler_Util.bind_opt uu___2
                      (fun hd2 ->
                         let uu___3 = un tl norm in
                         FStarC_Compiler_Util.bind_opt uu___3
                           (fun tl1 ->
                              FStar_Pervasives_Native.Some (hd2 :: tl1)))
                | uu___2 -> FStar_Pervasives_Native.None)) in
    FStarC_Syntax_Embeddings_Base.mk_emb_full em un typ printer1 emb_t_list_a
let (e_string_list :
  Prims.string Prims.list FStarC_Syntax_Embeddings_Base.embedding) =
  e_list e_string
let (steps_Simpl : FStarC_Syntax_Syntax.term) =
  FStarC_Syntax_Syntax.tconst FStarC_Parser_Const.steps_simpl
let (steps_Weak : FStarC_Syntax_Syntax.term) =
  FStarC_Syntax_Syntax.tconst FStarC_Parser_Const.steps_weak
let (steps_HNF : FStarC_Syntax_Syntax.term) =
  FStarC_Syntax_Syntax.tconst FStarC_Parser_Const.steps_hnf
let (steps_Primops : FStarC_Syntax_Syntax.term) =
  FStarC_Syntax_Syntax.tconst FStarC_Parser_Const.steps_primops
let (steps_Delta : FStarC_Syntax_Syntax.term) =
  FStarC_Syntax_Syntax.tconst FStarC_Parser_Const.steps_delta
let (steps_Zeta : FStarC_Syntax_Syntax.term) =
  FStarC_Syntax_Syntax.tconst FStarC_Parser_Const.steps_zeta
let (steps_ZetaFull : FStarC_Syntax_Syntax.term) =
  FStarC_Syntax_Syntax.tconst FStarC_Parser_Const.steps_zeta_full
let (steps_Iota : FStarC_Syntax_Syntax.term) =
  FStarC_Syntax_Syntax.tconst FStarC_Parser_Const.steps_iota
let (steps_Reify : FStarC_Syntax_Syntax.term) =
  FStarC_Syntax_Syntax.tconst FStarC_Parser_Const.steps_reify
let (steps_NormDebug : FStarC_Syntax_Syntax.term) =
  FStarC_Syntax_Syntax.tconst FStarC_Parser_Const.steps_norm_debug
let (steps_UnfoldOnly : FStarC_Syntax_Syntax.term) =
  FStarC_Syntax_Syntax.tconst FStarC_Parser_Const.steps_unfoldonly
let (steps_UnfoldFully : FStarC_Syntax_Syntax.term) =
  FStarC_Syntax_Syntax.tconst FStarC_Parser_Const.steps_unfoldonly
let (steps_UnfoldAttr : FStarC_Syntax_Syntax.term) =
  FStarC_Syntax_Syntax.tconst FStarC_Parser_Const.steps_unfoldattr
let (steps_UnfoldQual : FStarC_Syntax_Syntax.term) =
  FStarC_Syntax_Syntax.tconst FStarC_Parser_Const.steps_unfoldqual
let (steps_UnfoldNamespace : FStarC_Syntax_Syntax.term) =
  FStarC_Syntax_Syntax.tconst FStarC_Parser_Const.steps_unfoldnamespace
let (steps_Unascribe : FStarC_Syntax_Syntax.term) =
  FStarC_Syntax_Syntax.tconst FStarC_Parser_Const.steps_unascribe
let (steps_NBE : FStarC_Syntax_Syntax.term) =
  FStarC_Syntax_Syntax.tconst FStarC_Parser_Const.steps_nbe
let (steps_Unmeta : FStarC_Syntax_Syntax.term) =
  FStarC_Syntax_Syntax.tconst FStarC_Parser_Const.steps_unmeta
let (e_norm_step :
  FStar_Pervasives.norm_step FStarC_Syntax_Embeddings_Base.embedding) =
  let typ uu___ = FStarC_Syntax_Syntax.t_norm_step in
  let emb_t_norm_step uu___ =
    let uu___1 =
      let uu___2 =
        FStarC_Ident.string_of_lid FStarC_Parser_Const.norm_step_lid in
      (uu___2, []) in
    FStarC_Syntax_Syntax.ET_app uu___1 in
  let printer1 uu___ = "norm_step" in
  let em n rng _shadow norm =
    lazy_embed printer1 emb_t_norm_step rng typ n
      (fun uu___ ->
         match n with
         | FStar_Pervasives.Simpl -> steps_Simpl
         | FStar_Pervasives.Weak -> steps_Weak
         | FStar_Pervasives.HNF -> steps_HNF
         | FStar_Pervasives.Primops -> steps_Primops
         | FStar_Pervasives.Delta -> steps_Delta
         | FStar_Pervasives.Zeta -> steps_Zeta
         | FStar_Pervasives.ZetaFull -> steps_ZetaFull
         | FStar_Pervasives.Iota -> steps_Iota
         | FStar_Pervasives.Unascribe -> steps_Unascribe
         | FStar_Pervasives.NBE -> steps_NBE
         | FStar_Pervasives.Unmeta -> steps_Unmeta
         | FStar_Pervasives.Reify -> steps_Reify
         | FStar_Pervasives.NormDebug -> steps_NormDebug
         | FStar_Pervasives.UnfoldOnly l ->
             let uu___1 =
               let uu___2 =
                 let uu___3 =
                   let uu___4 =
                     FStarC_Syntax_Embeddings_Base.embed e_string_list l in
                   uu___4 rng FStar_Pervasives_Native.None norm in
                 FStarC_Syntax_Syntax.as_arg uu___3 in
               [uu___2] in
             FStarC_Syntax_Syntax.mk_Tm_app steps_UnfoldOnly uu___1 rng
         | FStar_Pervasives.UnfoldFully l ->
             let uu___1 =
               let uu___2 =
                 let uu___3 =
                   let uu___4 =
                     FStarC_Syntax_Embeddings_Base.embed e_string_list l in
                   uu___4 rng FStar_Pervasives_Native.None norm in
                 FStarC_Syntax_Syntax.as_arg uu___3 in
               [uu___2] in
             FStarC_Syntax_Syntax.mk_Tm_app steps_UnfoldFully uu___1 rng
         | FStar_Pervasives.UnfoldAttr l ->
             let uu___1 =
               let uu___2 =
                 let uu___3 =
                   let uu___4 =
                     FStarC_Syntax_Embeddings_Base.embed e_string_list l in
                   uu___4 rng FStar_Pervasives_Native.None norm in
                 FStarC_Syntax_Syntax.as_arg uu___3 in
               [uu___2] in
             FStarC_Syntax_Syntax.mk_Tm_app steps_UnfoldAttr uu___1 rng
         | FStar_Pervasives.UnfoldQual l ->
             let uu___1 =
               let uu___2 =
                 let uu___3 =
                   let uu___4 =
                     FStarC_Syntax_Embeddings_Base.embed e_string_list l in
                   uu___4 rng FStar_Pervasives_Native.None norm in
                 FStarC_Syntax_Syntax.as_arg uu___3 in
               [uu___2] in
             FStarC_Syntax_Syntax.mk_Tm_app steps_UnfoldQual uu___1 rng
         | FStar_Pervasives.UnfoldNamespace l ->
             let uu___1 =
               let uu___2 =
                 let uu___3 =
                   let uu___4 =
                     FStarC_Syntax_Embeddings_Base.embed e_string_list l in
                   uu___4 rng FStar_Pervasives_Native.None norm in
                 FStarC_Syntax_Syntax.as_arg uu___3 in
               [uu___2] in
             FStarC_Syntax_Syntax.mk_Tm_app steps_UnfoldNamespace uu___1 rng) in
  let un t norm =
    lazy_unembed printer1 emb_t_norm_step t typ
      (fun t1 ->
         let uu___ = FStarC_Syntax_Util.head_and_args t1 in
         match uu___ with
         | (hd, args) ->
             let uu___1 =
               let uu___2 =
                 let uu___3 = FStarC_Syntax_Util.un_uinst hd in
                 uu___3.FStarC_Syntax_Syntax.n in
               (uu___2, args) in
             (match uu___1 with
              | (FStarC_Syntax_Syntax.Tm_fvar fv, []) when
                  FStarC_Syntax_Syntax.fv_eq_lid fv
                    FStarC_Parser_Const.steps_simpl
                  -> FStar_Pervasives_Native.Some FStar_Pervasives.Simpl
              | (FStarC_Syntax_Syntax.Tm_fvar fv, []) when
                  FStarC_Syntax_Syntax.fv_eq_lid fv
                    FStarC_Parser_Const.steps_weak
                  -> FStar_Pervasives_Native.Some FStar_Pervasives.Weak
              | (FStarC_Syntax_Syntax.Tm_fvar fv, []) when
                  FStarC_Syntax_Syntax.fv_eq_lid fv
                    FStarC_Parser_Const.steps_hnf
                  -> FStar_Pervasives_Native.Some FStar_Pervasives.HNF
              | (FStarC_Syntax_Syntax.Tm_fvar fv, []) when
                  FStarC_Syntax_Syntax.fv_eq_lid fv
                    FStarC_Parser_Const.steps_primops
                  -> FStar_Pervasives_Native.Some FStar_Pervasives.Primops
              | (FStarC_Syntax_Syntax.Tm_fvar fv, []) when
                  FStarC_Syntax_Syntax.fv_eq_lid fv
                    FStarC_Parser_Const.steps_delta
                  -> FStar_Pervasives_Native.Some FStar_Pervasives.Delta
              | (FStarC_Syntax_Syntax.Tm_fvar fv, []) when
                  FStarC_Syntax_Syntax.fv_eq_lid fv
                    FStarC_Parser_Const.steps_zeta
                  -> FStar_Pervasives_Native.Some FStar_Pervasives.Zeta
              | (FStarC_Syntax_Syntax.Tm_fvar fv, []) when
                  FStarC_Syntax_Syntax.fv_eq_lid fv
                    FStarC_Parser_Const.steps_zeta_full
                  -> FStar_Pervasives_Native.Some FStar_Pervasives.ZetaFull
              | (FStarC_Syntax_Syntax.Tm_fvar fv, []) when
                  FStarC_Syntax_Syntax.fv_eq_lid fv
                    FStarC_Parser_Const.steps_iota
                  -> FStar_Pervasives_Native.Some FStar_Pervasives.Iota
              | (FStarC_Syntax_Syntax.Tm_fvar fv, []) when
                  FStarC_Syntax_Syntax.fv_eq_lid fv
                    FStarC_Parser_Const.steps_unascribe
                  -> FStar_Pervasives_Native.Some FStar_Pervasives.Unascribe
              | (FStarC_Syntax_Syntax.Tm_fvar fv, []) when
                  FStarC_Syntax_Syntax.fv_eq_lid fv
                    FStarC_Parser_Const.steps_nbe
                  -> FStar_Pervasives_Native.Some FStar_Pervasives.NBE
              | (FStarC_Syntax_Syntax.Tm_fvar fv, []) when
                  FStarC_Syntax_Syntax.fv_eq_lid fv
                    FStarC_Parser_Const.steps_unmeta
                  -> FStar_Pervasives_Native.Some FStar_Pervasives.Unmeta
              | (FStarC_Syntax_Syntax.Tm_fvar fv, []) when
                  FStarC_Syntax_Syntax.fv_eq_lid fv
                    FStarC_Parser_Const.steps_reify
                  -> FStar_Pervasives_Native.Some FStar_Pervasives.Reify
              | (FStarC_Syntax_Syntax.Tm_fvar fv, []) when
                  FStarC_Syntax_Syntax.fv_eq_lid fv
                    FStarC_Parser_Const.steps_norm_debug
                  -> FStar_Pervasives_Native.Some FStar_Pervasives.NormDebug
              | (FStarC_Syntax_Syntax.Tm_fvar fv, (l, uu___2)::[]) when
                  FStarC_Syntax_Syntax.fv_eq_lid fv
                    FStarC_Parser_Const.steps_unfoldonly
                  ->
                  let uu___3 =
                    FStarC_Syntax_Embeddings_Base.try_unembed e_string_list l
                      norm in
                  FStarC_Compiler_Util.bind_opt uu___3
                    (fun ss ->
                       FStar_Pervasives_Native.Some
                         (FStar_Pervasives.UnfoldOnly ss))
              | (FStarC_Syntax_Syntax.Tm_fvar fv, (l, uu___2)::[]) when
                  FStarC_Syntax_Syntax.fv_eq_lid fv
                    FStarC_Parser_Const.steps_unfoldfully
                  ->
                  let uu___3 =
                    FStarC_Syntax_Embeddings_Base.try_unembed e_string_list l
                      norm in
                  FStarC_Compiler_Util.bind_opt uu___3
                    (fun ss ->
                       FStar_Pervasives_Native.Some
                         (FStar_Pervasives.UnfoldFully ss))
              | (FStarC_Syntax_Syntax.Tm_fvar fv, (l, uu___2)::[]) when
                  FStarC_Syntax_Syntax.fv_eq_lid fv
                    FStarC_Parser_Const.steps_unfoldattr
                  ->
                  let uu___3 =
                    FStarC_Syntax_Embeddings_Base.try_unembed e_string_list l
                      norm in
                  FStarC_Compiler_Util.bind_opt uu___3
                    (fun ss ->
                       FStar_Pervasives_Native.Some
                         (FStar_Pervasives.UnfoldAttr ss))
              | (FStarC_Syntax_Syntax.Tm_fvar fv, (l, uu___2)::[]) when
                  FStarC_Syntax_Syntax.fv_eq_lid fv
                    FStarC_Parser_Const.steps_unfoldqual
                  ->
                  let uu___3 =
                    FStarC_Syntax_Embeddings_Base.try_unembed e_string_list l
                      norm in
                  FStarC_Compiler_Util.bind_opt uu___3
                    (fun ss ->
                       FStar_Pervasives_Native.Some
                         (FStar_Pervasives.UnfoldQual ss))
              | (FStarC_Syntax_Syntax.Tm_fvar fv, (l, uu___2)::[]) when
                  FStarC_Syntax_Syntax.fv_eq_lid fv
                    FStarC_Parser_Const.steps_unfoldnamespace
                  ->
                  let uu___3 =
                    FStarC_Syntax_Embeddings_Base.try_unembed e_string_list l
                      norm in
                  FStarC_Compiler_Util.bind_opt uu___3
                    (fun ss ->
                       FStar_Pervasives_Native.Some
                         (FStar_Pervasives.UnfoldNamespace ss))
              | uu___2 -> FStar_Pervasives_Native.None)) in
  FStarC_Syntax_Embeddings_Base.mk_emb_full em un typ printer1
    emb_t_norm_step
let (e_vconfig :
  FStarC_VConfig.vconfig FStarC_Syntax_Embeddings_Base.embedding) =
  let em vcfg rng _shadow norm =
    let uu___ =
      FStarC_Syntax_Syntax.tdataconstr FStarC_Parser_Const.mkvconfig_lid in
    let uu___1 =
      let uu___2 =
        let uu___3 =
          let uu___4 =
            FStarC_Syntax_Embeddings_Base.embed e_fsint
              vcfg.FStarC_VConfig.initial_fuel in
          uu___4 rng FStar_Pervasives_Native.None norm in
        FStarC_Syntax_Syntax.as_arg uu___3 in
      let uu___3 =
        let uu___4 =
          let uu___5 =
            let uu___6 =
              FStarC_Syntax_Embeddings_Base.embed e_fsint
                vcfg.FStarC_VConfig.max_fuel in
            uu___6 rng FStar_Pervasives_Native.None norm in
          FStarC_Syntax_Syntax.as_arg uu___5 in
        let uu___5 =
          let uu___6 =
            let uu___7 =
              let uu___8 =
                FStarC_Syntax_Embeddings_Base.embed e_fsint
                  vcfg.FStarC_VConfig.initial_ifuel in
              uu___8 rng FStar_Pervasives_Native.None norm in
            FStarC_Syntax_Syntax.as_arg uu___7 in
          let uu___7 =
            let uu___8 =
              let uu___9 =
                let uu___10 =
                  FStarC_Syntax_Embeddings_Base.embed e_fsint
                    vcfg.FStarC_VConfig.max_ifuel in
                uu___10 rng FStar_Pervasives_Native.None norm in
              FStarC_Syntax_Syntax.as_arg uu___9 in
            let uu___9 =
              let uu___10 =
                let uu___11 =
                  let uu___12 =
                    FStarC_Syntax_Embeddings_Base.embed e_bool
                      vcfg.FStarC_VConfig.detail_errors in
                  uu___12 rng FStar_Pervasives_Native.None norm in
                FStarC_Syntax_Syntax.as_arg uu___11 in
              let uu___11 =
                let uu___12 =
                  let uu___13 =
                    let uu___14 =
                      FStarC_Syntax_Embeddings_Base.embed e_bool
                        vcfg.FStarC_VConfig.detail_hint_replay in
                    uu___14 rng FStar_Pervasives_Native.None norm in
                  FStarC_Syntax_Syntax.as_arg uu___13 in
                let uu___13 =
                  let uu___14 =
                    let uu___15 =
                      let uu___16 =
                        FStarC_Syntax_Embeddings_Base.embed e_bool
                          vcfg.FStarC_VConfig.no_smt in
                      uu___16 rng FStar_Pervasives_Native.None norm in
                    FStarC_Syntax_Syntax.as_arg uu___15 in
                  let uu___15 =
                    let uu___16 =
                      let uu___17 =
                        let uu___18 =
                          FStarC_Syntax_Embeddings_Base.embed e_fsint
                            vcfg.FStarC_VConfig.quake_lo in
                        uu___18 rng FStar_Pervasives_Native.None norm in
                      FStarC_Syntax_Syntax.as_arg uu___17 in
                    let uu___17 =
                      let uu___18 =
                        let uu___19 =
                          let uu___20 =
                            FStarC_Syntax_Embeddings_Base.embed e_fsint
                              vcfg.FStarC_VConfig.quake_hi in
                          uu___20 rng FStar_Pervasives_Native.None norm in
                        FStarC_Syntax_Syntax.as_arg uu___19 in
                      let uu___19 =
                        let uu___20 =
                          let uu___21 =
                            let uu___22 =
                              FStarC_Syntax_Embeddings_Base.embed e_bool
                                vcfg.FStarC_VConfig.quake_keep in
                            uu___22 rng FStar_Pervasives_Native.None norm in
                          FStarC_Syntax_Syntax.as_arg uu___21 in
                        let uu___21 =
                          let uu___22 =
                            let uu___23 =
                              let uu___24 =
                                FStarC_Syntax_Embeddings_Base.embed e_bool
                                  vcfg.FStarC_VConfig.retry in
                              uu___24 rng FStar_Pervasives_Native.None norm in
                            FStarC_Syntax_Syntax.as_arg uu___23 in
                          let uu___23 =
                            let uu___24 =
                              let uu___25 =
                                let uu___26 =
                                  FStarC_Syntax_Embeddings_Base.embed e_bool
                                    vcfg.FStarC_VConfig.smtencoding_elim_box in
                                uu___26 rng FStar_Pervasives_Native.None norm in
                              FStarC_Syntax_Syntax.as_arg uu___25 in
                            let uu___25 =
                              let uu___26 =
                                let uu___27 =
                                  let uu___28 =
                                    FStarC_Syntax_Embeddings_Base.embed
                                      e_string
                                      vcfg.FStarC_VConfig.smtencoding_nl_arith_repr in
                                  uu___28 rng FStar_Pervasives_Native.None
                                    norm in
                                FStarC_Syntax_Syntax.as_arg uu___27 in
                              let uu___27 =
                                let uu___28 =
                                  let uu___29 =
                                    let uu___30 =
                                      FStarC_Syntax_Embeddings_Base.embed
                                        e_string
                                        vcfg.FStarC_VConfig.smtencoding_l_arith_repr in
                                    uu___30 rng FStar_Pervasives_Native.None
                                      norm in
                                  FStarC_Syntax_Syntax.as_arg uu___29 in
                                let uu___29 =
                                  let uu___30 =
                                    let uu___31 =
                                      let uu___32 =
                                        FStarC_Syntax_Embeddings_Base.embed
                                          e_bool
                                          vcfg.FStarC_VConfig.smtencoding_valid_intro in
                                      uu___32 rng
                                        FStar_Pervasives_Native.None norm in
                                    FStarC_Syntax_Syntax.as_arg uu___31 in
                                  let uu___31 =
                                    let uu___32 =
                                      let uu___33 =
                                        let uu___34 =
                                          FStarC_Syntax_Embeddings_Base.embed
                                            e_bool
                                            vcfg.FStarC_VConfig.smtencoding_valid_elim in
                                        uu___34 rng
                                          FStar_Pervasives_Native.None norm in
                                      FStarC_Syntax_Syntax.as_arg uu___33 in
                                    let uu___33 =
                                      let uu___34 =
                                        let uu___35 =
                                          let uu___36 =
                                            FStarC_Syntax_Embeddings_Base.embed
                                              e_bool
                                              vcfg.FStarC_VConfig.tcnorm in
                                          uu___36 rng
                                            FStar_Pervasives_Native.None norm in
                                        FStarC_Syntax_Syntax.as_arg uu___35 in
                                      let uu___35 =
                                        let uu___36 =
                                          let uu___37 =
                                            let uu___38 =
                                              FStarC_Syntax_Embeddings_Base.embed
                                                e_bool
                                                vcfg.FStarC_VConfig.no_plugins in
                                            uu___38 rng
                                              FStar_Pervasives_Native.None
                                              norm in
                                          FStarC_Syntax_Syntax.as_arg uu___37 in
                                        let uu___37 =
                                          let uu___38 =
                                            let uu___39 =
                                              let uu___40 =
                                                FStarC_Syntax_Embeddings_Base.embed
                                                  e_bool
                                                  vcfg.FStarC_VConfig.no_tactics in
                                              uu___40 rng
                                                FStar_Pervasives_Native.None
                                                norm in
                                            FStarC_Syntax_Syntax.as_arg
                                              uu___39 in
                                          let uu___39 =
                                            let uu___40 =
                                              let uu___41 =
                                                let uu___42 =
                                                  FStarC_Syntax_Embeddings_Base.embed
                                                    e_string_list
                                                    vcfg.FStarC_VConfig.z3cliopt in
                                                uu___42 rng
                                                  FStar_Pervasives_Native.None
                                                  norm in
                                              FStarC_Syntax_Syntax.as_arg
                                                uu___41 in
                                            let uu___41 =
                                              let uu___42 =
                                                let uu___43 =
                                                  let uu___44 =
                                                    FStarC_Syntax_Embeddings_Base.embed
                                                      e_string_list
                                                      vcfg.FStarC_VConfig.z3smtopt in
                                                  uu___44 rng
                                                    FStar_Pervasives_Native.None
                                                    norm in
                                                FStarC_Syntax_Syntax.as_arg
                                                  uu___43 in
                                              let uu___43 =
                                                let uu___44 =
                                                  let uu___45 =
                                                    let uu___46 =
                                                      FStarC_Syntax_Embeddings_Base.embed
                                                        e_bool
                                                        vcfg.FStarC_VConfig.z3refresh in
                                                    uu___46 rng
                                                      FStar_Pervasives_Native.None
                                                      norm in
                                                  FStarC_Syntax_Syntax.as_arg
                                                    uu___45 in
                                                let uu___45 =
                                                  let uu___46 =
                                                    let uu___47 =
                                                      let uu___48 =
                                                        FStarC_Syntax_Embeddings_Base.embed
                                                          e_fsint
                                                          vcfg.FStarC_VConfig.z3rlimit in
                                                      uu___48 rng
                                                        FStar_Pervasives_Native.None
                                                        norm in
                                                    FStarC_Syntax_Syntax.as_arg
                                                      uu___47 in
                                                  let uu___47 =
                                                    let uu___48 =
                                                      let uu___49 =
                                                        let uu___50 =
                                                          FStarC_Syntax_Embeddings_Base.embed
                                                            e_fsint
                                                            vcfg.FStarC_VConfig.z3rlimit_factor in
                                                        uu___50 rng
                                                          FStar_Pervasives_Native.None
                                                          norm in
                                                      FStarC_Syntax_Syntax.as_arg
                                                        uu___49 in
                                                    let uu___49 =
                                                      let uu___50 =
                                                        let uu___51 =
                                                          let uu___52 =
                                                            FStarC_Syntax_Embeddings_Base.embed
                                                              e_fsint
                                                              vcfg.FStarC_VConfig.z3seed in
                                                          uu___52 rng
                                                            FStar_Pervasives_Native.None
                                                            norm in
                                                        FStarC_Syntax_Syntax.as_arg
                                                          uu___51 in
                                                      let uu___51 =
                                                        let uu___52 =
                                                          let uu___53 =
                                                            let uu___54 =
                                                              FStarC_Syntax_Embeddings_Base.embed
                                                                e_string
                                                                vcfg.FStarC_VConfig.z3version in
                                                            uu___54 rng
                                                              FStar_Pervasives_Native.None
                                                              norm in
                                                          FStarC_Syntax_Syntax.as_arg
                                                            uu___53 in
                                                        let uu___53 =
                                                          let uu___54 =
                                                            let uu___55 =
                                                              let uu___56 =
                                                                FStarC_Syntax_Embeddings_Base.embed
                                                                  e_bool
                                                                  vcfg.FStarC_VConfig.trivial_pre_for_unannotated_effectful_fns in
                                                              uu___56 rng
                                                                FStar_Pervasives_Native.None
                                                                norm in
                                                            FStarC_Syntax_Syntax.as_arg
                                                              uu___55 in
                                                          let uu___55 =
                                                            let uu___56 =
                                                              let uu___57 =
                                                                let uu___58 =
                                                                  FStarC_Syntax_Embeddings_Base.embed
                                                                    (
                                                                    e_option
                                                                    e_string)
                                                                    vcfg.FStarC_VConfig.reuse_hint_for in
                                                                uu___58 rng
                                                                  FStar_Pervasives_Native.None
                                                                  norm in
                                                              FStarC_Syntax_Syntax.as_arg
                                                                uu___57 in
                                                            [uu___56] in
                                                          uu___54 :: uu___55 in
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
    FStarC_Syntax_Syntax.mk_Tm_app uu___ uu___1 rng in
  let un t norm =
    let uu___ = FStarC_Syntax_Util.head_and_args t in
    match uu___ with
    | (hd, args) ->
        let uu___1 =
          let uu___2 =
            let uu___3 = FStarC_Syntax_Util.un_uinst hd in
            uu___3.FStarC_Syntax_Syntax.n in
          (uu___2, args) in
        (match uu___1 with
         | (FStarC_Syntax_Syntax.Tm_fvar fv,
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
            (z3cliopt, uu___21)::(z3smtopt, uu___22)::(z3refresh, uu___23)::
            (z3rlimit, uu___24)::(z3rlimit_factor, uu___25)::(z3seed,
                                                              uu___26)::
            (z3version, uu___27)::(trivial_pre_for_unannotated_effectful_fns,
                                   uu___28)::(reuse_hint_for, uu___29)::[])
             when
             FStarC_Syntax_Syntax.fv_eq_lid fv
               FStarC_Parser_Const.mkvconfig_lid
             ->
             let uu___30 =
               FStarC_Syntax_Embeddings_Base.try_unembed e_fsint initial_fuel
                 norm in
             FStarC_Compiler_Util.bind_opt uu___30
               (fun initial_fuel1 ->
                  let uu___31 =
                    FStarC_Syntax_Embeddings_Base.try_unembed e_fsint
                      max_fuel norm in
                  FStarC_Compiler_Util.bind_opt uu___31
                    (fun max_fuel1 ->
                       let uu___32 =
                         FStarC_Syntax_Embeddings_Base.try_unembed e_fsint
                           initial_ifuel norm in
                       FStarC_Compiler_Util.bind_opt uu___32
                         (fun initial_ifuel1 ->
                            let uu___33 =
                              FStarC_Syntax_Embeddings_Base.try_unembed
                                e_fsint max_ifuel norm in
                            FStarC_Compiler_Util.bind_opt uu___33
                              (fun max_ifuel1 ->
                                 let uu___34 =
                                   FStarC_Syntax_Embeddings_Base.try_unembed
                                     e_bool detail_errors norm in
                                 FStarC_Compiler_Util.bind_opt uu___34
                                   (fun detail_errors1 ->
                                      let uu___35 =
                                        FStarC_Syntax_Embeddings_Base.try_unembed
                                          e_bool detail_hint_replay norm in
                                      FStarC_Compiler_Util.bind_opt uu___35
                                        (fun detail_hint_replay1 ->
                                           let uu___36 =
                                             FStarC_Syntax_Embeddings_Base.try_unembed
                                               e_bool no_smt norm in
                                           FStarC_Compiler_Util.bind_opt
                                             uu___36
                                             (fun no_smt1 ->
                                                let uu___37 =
                                                  FStarC_Syntax_Embeddings_Base.try_unembed
                                                    e_fsint quake_lo norm in
                                                FStarC_Compiler_Util.bind_opt
                                                  uu___37
                                                  (fun quake_lo1 ->
                                                     let uu___38 =
                                                       FStarC_Syntax_Embeddings_Base.try_unembed
                                                         e_fsint quake_hi
                                                         norm in
                                                     FStarC_Compiler_Util.bind_opt
                                                       uu___38
                                                       (fun quake_hi1 ->
                                                          let uu___39 =
                                                            FStarC_Syntax_Embeddings_Base.try_unembed
                                                              e_bool
                                                              quake_keep norm in
                                                          FStarC_Compiler_Util.bind_opt
                                                            uu___39
                                                            (fun quake_keep1
                                                               ->
                                                               let uu___40 =
                                                                 FStarC_Syntax_Embeddings_Base.try_unembed
                                                                   e_bool
                                                                   retry norm in
                                                               FStarC_Compiler_Util.bind_opt
                                                                 uu___40
                                                                 (fun retry1
                                                                    ->
                                                                    let uu___41
                                                                    =
                                                                    FStarC_Syntax_Embeddings_Base.try_unembed
                                                                    e_bool
                                                                    smtencoding_elim_box
                                                                    norm in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___41
                                                                    (fun
                                                                    smtencoding_elim_box1
                                                                    ->
                                                                    let uu___42
                                                                    =
                                                                    FStarC_Syntax_Embeddings_Base.try_unembed
                                                                    e_string
                                                                    smtencoding_nl_arith_repr
                                                                    norm in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___42
                                                                    (fun
                                                                    smtencoding_nl_arith_repr1
                                                                    ->
                                                                    let uu___43
                                                                    =
                                                                    FStarC_Syntax_Embeddings_Base.try_unembed
                                                                    e_string
                                                                    smtencoding_l_arith_repr
                                                                    norm in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___43
                                                                    (fun
                                                                    smtencoding_l_arith_repr1
                                                                    ->
                                                                    let uu___44
                                                                    =
                                                                    FStarC_Syntax_Embeddings_Base.try_unembed
                                                                    e_bool
                                                                    smtencoding_valid_intro
                                                                    norm in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___44
                                                                    (fun
                                                                    smtencoding_valid_intro1
                                                                    ->
                                                                    let uu___45
                                                                    =
                                                                    FStarC_Syntax_Embeddings_Base.try_unembed
                                                                    e_bool
                                                                    smtencoding_valid_elim
                                                                    norm in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___45
                                                                    (fun
                                                                    smtencoding_valid_elim1
                                                                    ->
                                                                    let uu___46
                                                                    =
                                                                    FStarC_Syntax_Embeddings_Base.try_unembed
                                                                    e_bool
                                                                    tcnorm
                                                                    norm in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___46
                                                                    (fun
                                                                    tcnorm1
                                                                    ->
                                                                    let uu___47
                                                                    =
                                                                    FStarC_Syntax_Embeddings_Base.try_unembed
                                                                    e_bool
                                                                    no_plugins
                                                                    norm in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___47
                                                                    (fun
                                                                    no_plugins1
                                                                    ->
                                                                    let uu___48
                                                                    =
                                                                    FStarC_Syntax_Embeddings_Base.try_unembed
                                                                    e_bool
                                                                    no_tactics
                                                                    norm in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___48
                                                                    (fun
                                                                    no_tactics1
                                                                    ->
                                                                    let uu___49
                                                                    =
                                                                    FStarC_Syntax_Embeddings_Base.try_unembed
                                                                    e_string_list
                                                                    z3cliopt
                                                                    norm in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___49
                                                                    (fun
                                                                    z3cliopt1
                                                                    ->
                                                                    let uu___50
                                                                    =
                                                                    FStarC_Syntax_Embeddings_Base.try_unembed
                                                                    e_string_list
                                                                    z3smtopt
                                                                    norm in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___50
                                                                    (fun
                                                                    z3smtopt1
                                                                    ->
                                                                    let uu___51
                                                                    =
                                                                    FStarC_Syntax_Embeddings_Base.try_unembed
                                                                    e_bool
                                                                    z3refresh
                                                                    norm in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___51
                                                                    (fun
                                                                    z3refresh1
                                                                    ->
                                                                    let uu___52
                                                                    =
                                                                    FStarC_Syntax_Embeddings_Base.try_unembed
                                                                    e_fsint
                                                                    z3rlimit
                                                                    norm in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___52
                                                                    (fun
                                                                    z3rlimit1
                                                                    ->
                                                                    let uu___53
                                                                    =
                                                                    FStarC_Syntax_Embeddings_Base.try_unembed
                                                                    e_fsint
                                                                    z3rlimit_factor
                                                                    norm in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___53
                                                                    (fun
                                                                    z3rlimit_factor1
                                                                    ->
                                                                    let uu___54
                                                                    =
                                                                    FStarC_Syntax_Embeddings_Base.try_unembed
                                                                    e_fsint
                                                                    z3seed
                                                                    norm in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___54
                                                                    (fun
                                                                    z3seed1
                                                                    ->
                                                                    let uu___55
                                                                    =
                                                                    FStarC_Syntax_Embeddings_Base.try_unembed
                                                                    e_string
                                                                    z3version
                                                                    norm in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___55
                                                                    (fun
                                                                    z3version1
                                                                    ->
                                                                    let uu___56
                                                                    =
                                                                    FStarC_Syntax_Embeddings_Base.try_unembed
                                                                    e_bool
                                                                    trivial_pre_for_unannotated_effectful_fns
                                                                    norm in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___56
                                                                    (fun
                                                                    trivial_pre_for_unannotated_effectful_fns1
                                                                    ->
                                                                    let uu___57
                                                                    =
                                                                    FStarC_Syntax_Embeddings_Base.try_unembed
                                                                    (e_option
                                                                    e_string)
                                                                    reuse_hint_for
                                                                    norm in
                                                                    FStarC_Compiler_Util.bind_opt
                                                                    uu___57
                                                                    (fun
                                                                    reuse_hint_for1
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    {
                                                                    FStarC_VConfig.initial_fuel
                                                                    =
                                                                    initial_fuel1;
                                                                    FStarC_VConfig.max_fuel
                                                                    =
                                                                    max_fuel1;
                                                                    FStarC_VConfig.initial_ifuel
                                                                    =
                                                                    initial_ifuel1;
                                                                    FStarC_VConfig.max_ifuel
                                                                    =
                                                                    max_ifuel1;
                                                                    FStarC_VConfig.detail_errors
                                                                    =
                                                                    detail_errors1;
                                                                    FStarC_VConfig.detail_hint_replay
                                                                    =
                                                                    detail_hint_replay1;
                                                                    FStarC_VConfig.no_smt
                                                                    = no_smt1;
                                                                    FStarC_VConfig.quake_lo
                                                                    =
                                                                    quake_lo1;
                                                                    FStarC_VConfig.quake_hi
                                                                    =
                                                                    quake_hi1;
                                                                    FStarC_VConfig.quake_keep
                                                                    =
                                                                    quake_keep1;
                                                                    FStarC_VConfig.retry
                                                                    = retry1;
                                                                    FStarC_VConfig.smtencoding_elim_box
                                                                    =
                                                                    smtencoding_elim_box1;
                                                                    FStarC_VConfig.smtencoding_nl_arith_repr
                                                                    =
                                                                    smtencoding_nl_arith_repr1;
                                                                    FStarC_VConfig.smtencoding_l_arith_repr
                                                                    =
                                                                    smtencoding_l_arith_repr1;
                                                                    FStarC_VConfig.smtencoding_valid_intro
                                                                    =
                                                                    smtencoding_valid_intro1;
                                                                    FStarC_VConfig.smtencoding_valid_elim
                                                                    =
                                                                    smtencoding_valid_elim1;
                                                                    FStarC_VConfig.tcnorm
                                                                    = tcnorm1;
                                                                    FStarC_VConfig.no_plugins
                                                                    =
                                                                    no_plugins1;
                                                                    FStarC_VConfig.no_tactics
                                                                    =
                                                                    no_tactics1;
                                                                    FStarC_VConfig.z3cliopt
                                                                    =
                                                                    z3cliopt1;
                                                                    FStarC_VConfig.z3smtopt
                                                                    =
                                                                    z3smtopt1;
                                                                    FStarC_VConfig.z3refresh
                                                                    =
                                                                    z3refresh1;
                                                                    FStarC_VConfig.z3rlimit
                                                                    =
                                                                    z3rlimit1;
                                                                    FStarC_VConfig.z3rlimit_factor
                                                                    =
                                                                    z3rlimit_factor1;
                                                                    FStarC_VConfig.z3seed
                                                                    = z3seed1;
                                                                    FStarC_VConfig.z3version
                                                                    =
                                                                    z3version1;
                                                                    FStarC_VConfig.trivial_pre_for_unannotated_effectful_fns
                                                                    =
                                                                    trivial_pre_for_unannotated_effectful_fns1;
                                                                    FStarC_VConfig.reuse_hint_for
                                                                    =
                                                                    reuse_hint_for1
                                                                    }))))))))))))))))))))))))))))
         | uu___2 -> FStar_Pervasives_Native.None) in
  FStarC_Syntax_Embeddings_Base.mk_emb_full em un
    (fun uu___ -> FStarC_Syntax_Syntax.t_vconfig) (fun uu___ -> "vconfig")
    (fun uu___ ->
       let uu___1 =
         let uu___2 =
           FStarC_Ident.string_of_lid FStarC_Parser_Const.vconfig_lid in
         (uu___2, []) in
       FStarC_Syntax_Syntax.ET_app uu___1)
let (e_order : FStar_Order.order FStarC_Syntax_Embeddings_Base.embedding) =
  let ord_Lt_lid =
    FStarC_Ident.lid_of_path ["FStar"; "Order"; "Lt"]
      FStarC_Compiler_Range_Type.dummyRange in
  let ord_Eq_lid =
    FStarC_Ident.lid_of_path ["FStar"; "Order"; "Eq"]
      FStarC_Compiler_Range_Type.dummyRange in
  let ord_Gt_lid =
    FStarC_Ident.lid_of_path ["FStar"; "Order"; "Gt"]
      FStarC_Compiler_Range_Type.dummyRange in
  let ord_Lt = FStarC_Syntax_Syntax.tdataconstr ord_Lt_lid in
  let ord_Eq = FStarC_Syntax_Syntax.tdataconstr ord_Eq_lid in
  let ord_Gt = FStarC_Syntax_Syntax.tdataconstr ord_Gt_lid in
  let ord_Lt_fv =
    FStarC_Syntax_Syntax.lid_as_fv ord_Lt_lid
      (FStar_Pervasives_Native.Some FStarC_Syntax_Syntax.Data_ctor) in
  let ord_Eq_fv =
    FStarC_Syntax_Syntax.lid_as_fv ord_Eq_lid
      (FStar_Pervasives_Native.Some FStarC_Syntax_Syntax.Data_ctor) in
  let ord_Gt_fv =
    FStarC_Syntax_Syntax.lid_as_fv ord_Gt_lid
      (FStar_Pervasives_Native.Some FStarC_Syntax_Syntax.Data_ctor) in
  let embed_order o rng shadow cb =
    let r =
      match o with
      | FStar_Order.Lt -> ord_Lt
      | FStar_Order.Eq -> ord_Eq
      | FStar_Order.Gt -> ord_Gt in
    {
      FStarC_Syntax_Syntax.n = (r.FStarC_Syntax_Syntax.n);
      FStarC_Syntax_Syntax.pos = rng;
      FStarC_Syntax_Syntax.vars = (r.FStarC_Syntax_Syntax.vars);
      FStarC_Syntax_Syntax.hash_code = (r.FStarC_Syntax_Syntax.hash_code)
    } in
  let unembed_order t cb =
    let t1 = FStarC_Syntax_Util.unascribe t in
    let uu___ = FStarC_Syntax_Util.head_and_args t1 in
    match uu___ with
    | (hd, args) ->
        let uu___1 =
          let uu___2 =
            let uu___3 = FStarC_Syntax_Util.un_uinst hd in
            uu___3.FStarC_Syntax_Syntax.n in
          (uu___2, args) in
        (match uu___1 with
         | (FStarC_Syntax_Syntax.Tm_fvar fv, []) when
             FStarC_Syntax_Syntax.fv_eq_lid fv ord_Lt_lid ->
             FStar_Pervasives_Native.Some FStar_Order.Lt
         | (FStarC_Syntax_Syntax.Tm_fvar fv, []) when
             FStarC_Syntax_Syntax.fv_eq_lid fv ord_Eq_lid ->
             FStar_Pervasives_Native.Some FStar_Order.Eq
         | (FStarC_Syntax_Syntax.Tm_fvar fv, []) when
             FStarC_Syntax_Syntax.fv_eq_lid fv ord_Gt_lid ->
             FStar_Pervasives_Native.Some FStar_Order.Gt
         | uu___2 -> FStar_Pervasives_Native.None) in
  let uu___ =
    FStarC_Syntax_Syntax.lid_as_fv FStarC_Parser_Const.order_lid
      FStar_Pervasives_Native.None in
  FStarC_Syntax_Embeddings_Base.mk_emb embed_order unembed_order uu___
let or_else : 'a . 'a FStar_Pervasives_Native.option -> (unit -> 'a) -> 'a =
  fun f ->
    fun g ->
      match f with
      | FStar_Pervasives_Native.Some x -> x
      | FStar_Pervasives_Native.None -> g ()
let e_arrow :
  'a 'b .
    'a FStarC_Syntax_Embeddings_Base.embedding ->
      'b FStarC_Syntax_Embeddings_Base.embedding ->
        ('a -> 'b) FStarC_Syntax_Embeddings_Base.embedding
  =
  fun ea ->
    fun eb ->
      let typ uu___ =
        let uu___1 =
          let uu___2 =
            let uu___3 =
              let uu___4 =
                let uu___5 =
                  let uu___6 = FStarC_Syntax_Embeddings_Base.type_of ea in
                  FStarC_Syntax_Syntax.null_bv uu___6 in
                FStarC_Syntax_Syntax.mk_binder uu___5 in
              [uu___4] in
            let uu___4 =
              let uu___5 = FStarC_Syntax_Embeddings_Base.type_of eb in
              FStarC_Syntax_Syntax.mk_Total uu___5 in
            {
              FStarC_Syntax_Syntax.bs1 = uu___3;
              FStarC_Syntax_Syntax.comp = uu___4
            } in
          FStarC_Syntax_Syntax.Tm_arrow uu___2 in
        FStarC_Syntax_Syntax.mk uu___1 FStarC_Compiler_Range_Type.dummyRange in
      let emb_t_arr_a_b uu___ =
        let uu___1 =
          let uu___2 = FStarC_Syntax_Embeddings_Base.emb_typ_of ea () in
          let uu___3 = FStarC_Syntax_Embeddings_Base.emb_typ_of eb () in
          (uu___2, uu___3) in
        FStarC_Syntax_Syntax.ET_fun uu___1 in
      let printer1 f = "<fun>" in
      let em f rng shadow_f norm =
        lazy_embed printer1 emb_t_arr_a_b rng typ f
          (fun uu___ ->
             let uu___1 = force_shadow shadow_f in
             match uu___1 with
             | FStar_Pervasives_Native.None ->
                 FStarC_Compiler_Effect.raise Embedding_failure
             | FStar_Pervasives_Native.Some repr_f ->
                 ((let uu___3 =
                     FStarC_Compiler_Effect.op_Bang
                       FStarC_Options.debug_embedding in
                   if uu___3
                   then
                     let uu___4 =
                       FStarC_Class_Show.show
                         FStarC_Syntax_Print.showable_term repr_f in
                     let uu___5 = FStarC_Compiler_Util.stack_dump () in
                     FStarC_Compiler_Util.print2
                       "e_arrow forced back to term using shadow %s; repr=%s\n"
                       uu___4 uu___5
                   else ());
                  (let res = norm (FStar_Pervasives.Inr repr_f) in
                   (let uu___4 =
                      FStarC_Compiler_Effect.op_Bang
                        FStarC_Options.debug_embedding in
                    if uu___4
                    then
                      let uu___5 =
                        FStarC_Class_Show.show
                          FStarC_Syntax_Print.showable_term repr_f in
                      let uu___6 =
                        FStarC_Class_Show.show
                          FStarC_Syntax_Print.showable_term res in
                      let uu___7 = FStarC_Compiler_Util.stack_dump () in
                      FStarC_Compiler_Util.print3
                        "e_arrow forced back to term using shadow %s; repr=%s\n\t%s\n"
                        uu___5 uu___6 uu___7
                    else ());
                   res))) in
      let un f norm =
        lazy_unembed printer1 emb_t_arr_a_b f typ
          (fun f1 ->
             let f_wrapped a1 =
               (let uu___1 =
                  FStarC_Compiler_Effect.op_Bang
                    FStarC_Options.debug_embedding in
                if uu___1
                then
                  let uu___2 =
                    FStarC_Class_Show.show FStarC_Syntax_Print.showable_term
                      f1 in
                  let uu___3 = FStarC_Compiler_Util.stack_dump () in
                  FStarC_Compiler_Util.print2
                    "Calling back into normalizer for %s\n%s\n" uu___2 uu___3
                else ());
               (let a_tm =
                  let uu___1 = FStarC_Syntax_Embeddings_Base.embed ea a1 in
                  uu___1 f1.FStarC_Syntax_Syntax.pos
                    FStar_Pervasives_Native.None norm in
                let b_tm =
                  let uu___1 =
                    let uu___2 =
                      let uu___3 =
                        let uu___4 = FStarC_Syntax_Syntax.as_arg a_tm in
                        [uu___4] in
                      FStarC_Syntax_Syntax.mk_Tm_app f1 uu___3
                        f1.FStarC_Syntax_Syntax.pos in
                    FStar_Pervasives.Inr uu___2 in
                  norm uu___1 in
                let uu___1 =
                  FStarC_Syntax_Embeddings_Base.unembed eb b_tm norm in
                match uu___1 with
                | FStar_Pervasives_Native.None ->
                    FStarC_Compiler_Effect.raise Unembedding_failure
                | FStar_Pervasives_Native.Some b1 -> b1) in
             FStar_Pervasives_Native.Some f_wrapped) in
      FStarC_Syntax_Embeddings_Base.mk_emb_full em un typ printer1
        emb_t_arr_a_b
let e_sealed :
  'a .
    'a FStarC_Syntax_Embeddings_Base.embedding ->
      'a FStarC_Compiler_Sealed.sealed
        FStarC_Syntax_Embeddings_Base.embedding
  =
  fun ea ->
    let typ uu___ =
      let uu___1 = FStarC_Syntax_Embeddings_Base.type_of ea in
      FStarC_Syntax_Syntax.t_sealed_of uu___1 in
    let emb_ty_a uu___ =
      let uu___1 =
        let uu___2 =
          FStarC_Ident.string_of_lid FStarC_Parser_Const.sealed_lid in
        let uu___3 =
          let uu___4 = FStarC_Syntax_Embeddings_Base.emb_typ_of ea () in
          [uu___4] in
        (uu___2, uu___3) in
      FStarC_Syntax_Syntax.ET_app uu___1 in
    let printer1 x =
      let uu___ =
        let uu___1 =
          let uu___2 = FStarC_Syntax_Embeddings_Base.printer_of ea in
          uu___2 (FStarC_Compiler_Sealed.unseal x) in
        Prims.strcat uu___1 ")" in
      Prims.strcat "(seal " uu___ in
    let em a1 rng shadow norm =
      let shadow_a =
        map_shadow shadow
          (fun t ->
             let unseal =
               FStarC_Syntax_Util.fvar_const FStarC_Parser_Const.unseal_lid in
             let uu___ =
               FStarC_Syntax_Syntax.mk_Tm_uinst unseal
                 [FStarC_Syntax_Syntax.U_zero] in
             let uu___1 =
               let uu___2 =
                 let uu___3 = FStarC_Syntax_Embeddings_Base.type_of ea in
                 FStarC_Syntax_Syntax.iarg uu___3 in
               let uu___3 =
                 let uu___4 = FStarC_Syntax_Syntax.as_arg t in [uu___4] in
               uu___2 :: uu___3 in
             FStarC_Syntax_Syntax.mk_Tm_app uu___ uu___1 rng) in
      let uu___ =
        let uu___1 =
          FStarC_Syntax_Util.fvar_const FStarC_Parser_Const.seal_lid in
        FStarC_Syntax_Syntax.mk_Tm_uinst uu___1 [FStarC_Syntax_Syntax.U_zero] in
      let uu___1 =
        let uu___2 =
          let uu___3 = FStarC_Syntax_Embeddings_Base.type_of ea in
          FStarC_Syntax_Syntax.iarg uu___3 in
        let uu___3 =
          let uu___4 =
            let uu___5 =
              let uu___6 =
                FStarC_Syntax_Embeddings_Base.embed ea
                  (FStarC_Compiler_Sealed.unseal a1) in
              uu___6 rng shadow_a norm in
            FStarC_Syntax_Syntax.as_arg uu___5 in
          [uu___4] in
        uu___2 :: uu___3 in
      FStarC_Syntax_Syntax.mk_Tm_app uu___ uu___1 rng in
    let un uu___1 uu___ =
      (fun t ->
         fun norm ->
           let uu___ = FStarC_Syntax_Util.head_and_args_full t in
           match uu___ with
           | (hd, args) ->
               let uu___1 =
                 let uu___2 =
                   let uu___3 = FStarC_Syntax_Util.un_uinst hd in
                   uu___3.FStarC_Syntax_Syntax.n in
                 (uu___2, args) in
               (match uu___1 with
                | (FStarC_Syntax_Syntax.Tm_fvar fv, uu___2::(a1, uu___3)::[])
                    when
                    FStarC_Syntax_Syntax.fv_eq_lid fv
                      FStarC_Parser_Const.seal_lid
                    ->
                    Obj.magic
                      (Obj.repr
                         (let uu___4 =
                            FStarC_Syntax_Embeddings_Base.try_unembed ea a1
                              norm in
                          FStarC_Class_Monad.fmap
                            FStarC_Class_Monad.monad_option () ()
                            (fun uu___5 ->
                               (Obj.magic FStarC_Compiler_Sealed.seal) uu___5)
                            (Obj.magic uu___4)))
                | uu___2 -> Obj.magic (Obj.repr FStar_Pervasives_Native.None)))
        uu___1 uu___ in
    FStarC_Syntax_Embeddings_Base.mk_emb_full em un typ printer1 emb_ty_a
let (e___range :
  FStarC_Compiler_Range_Type.range FStarC_Syntax_Embeddings_Base.embedding) =
  let em r rng _shadow _norm =
    FStarC_Syntax_Syntax.mk
      (FStarC_Syntax_Syntax.Tm_constant (FStarC_Const.Const_range r)) rng in
  let un t _norm =
    let uu___ =
      let uu___1 = FStarC_Syntax_Subst.compress t in
      uu___1.FStarC_Syntax_Syntax.n in
    match uu___ with
    | FStarC_Syntax_Syntax.Tm_constant (FStarC_Const.Const_range r) ->
        FStar_Pervasives_Native.Some r
    | uu___1 -> FStar_Pervasives_Native.None in
  FStarC_Syntax_Embeddings_Base.mk_emb_full em un
    (fun uu___ -> FStarC_Syntax_Syntax.t___range)
    FStarC_Compiler_Range_Ops.string_of_range
    (fun uu___ ->
       let uu___1 =
         let uu___2 =
           FStarC_Ident.string_of_lid FStarC_Parser_Const.range_lid in
         (uu___2, []) in
       FStarC_Syntax_Syntax.ET_app uu___1)
let (e_range :
  FStarC_Compiler_Range_Type.range FStarC_Syntax_Embeddings_Base.embedding) =
  FStarC_Syntax_Embeddings_Base.embed_as (e_sealed e___range)
    FStarC_Compiler_Sealed.unseal FStarC_Compiler_Sealed.seal
    FStar_Pervasives_Native.None
let (e_issue : FStarC_Errors.issue FStarC_Syntax_Embeddings_Base.embedding) =
  let uu___ =
    FStarC_Syntax_Syntax.fvar FStarC_Parser_Const.issue_lid
      FStar_Pervasives_Native.None in
  FStarC_Syntax_Embeddings_Base.e_lazy FStarC_Syntax_Syntax.Lazy_issue uu___
let (e_document :
  FStarC_Pprint.document FStarC_Syntax_Embeddings_Base.embedding) =
  let uu___ =
    FStarC_Syntax_Syntax.fvar FStarC_Parser_Const.document_lid
      FStar_Pervasives_Native.None in
  FStarC_Syntax_Embeddings_Base.e_lazy FStarC_Syntax_Syntax.Lazy_doc uu___
type abstract_term =
  | Abstract of FStarC_Syntax_Syntax.term 
let (uu___is_Abstract : abstract_term -> Prims.bool) = fun projectee -> true
let (__proj__Abstract__item__t : abstract_term -> FStarC_Syntax_Syntax.term)
  = fun projectee -> match projectee with | Abstract t -> t
let arrow_as_prim_step_1 :
  'a 'b .
    'a FStarC_Syntax_Embeddings_Base.embedding ->
      'b FStarC_Syntax_Embeddings_Base.embedding ->
        ('a -> 'b) ->
          FStarC_Ident.lid ->
            FStarC_Syntax_Embeddings_Base.norm_cb ->
              FStarC_Syntax_Syntax.universes ->
                FStarC_Syntax_Syntax.args ->
                  FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun ea ->
    fun eb ->
      fun f ->
        fun fv_lid ->
          fun norm ->
            let rng = FStarC_Ident.range_of_lid fv_lid in
            let f_wrapped _us args =
              let uu___ = args in
              match uu___ with
              | (x, uu___1)::[] ->
                  let shadow_app =
                    let uu___2 =
                      FStarC_Thunk.mk
                        (fun uu___3 ->
                           let uu___4 = norm (FStar_Pervasives.Inl fv_lid) in
                           FStarC_Syntax_Syntax.mk_Tm_app uu___4 args rng) in
                    FStar_Pervasives_Native.Some uu___2 in
                  let uu___2 =
                    let uu___3 =
                      FStarC_Syntax_Embeddings_Base.try_unembed ea x norm in
                    FStarC_Compiler_Util.map_opt uu___3
                      (fun x1 ->
                         let uu___4 =
                           let uu___5 = f x1 in
                           FStarC_Syntax_Embeddings_Base.embed eb uu___5 in
                         uu___4 rng shadow_app norm) in
                  (match uu___2 with
                   | FStar_Pervasives_Native.Some x1 ->
                       FStar_Pervasives_Native.Some x1
                   | FStar_Pervasives_Native.None -> force_shadow shadow_app) in
            f_wrapped
let arrow_as_prim_step_2 :
  'a 'b 'c .
    'a FStarC_Syntax_Embeddings_Base.embedding ->
      'b FStarC_Syntax_Embeddings_Base.embedding ->
        'c FStarC_Syntax_Embeddings_Base.embedding ->
          ('a -> 'b -> 'c) ->
            FStarC_Ident.lid ->
              FStarC_Syntax_Embeddings_Base.norm_cb ->
                FStarC_Syntax_Syntax.universes ->
                  FStarC_Syntax_Syntax.args ->
                    FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun ea ->
    fun eb ->
      fun ec ->
        fun f ->
          fun fv_lid ->
            fun norm ->
              let rng = FStarC_Ident.range_of_lid fv_lid in
              let f_wrapped _us args =
                let uu___ = args in
                match uu___ with
                | (x, uu___1)::(y, uu___2)::[] ->
                    let shadow_app =
                      let uu___3 =
                        FStarC_Thunk.mk
                          (fun uu___4 ->
                             let uu___5 = norm (FStar_Pervasives.Inl fv_lid) in
                             FStarC_Syntax_Syntax.mk_Tm_app uu___5 args rng) in
                      FStar_Pervasives_Native.Some uu___3 in
                    let uu___3 =
                      let uu___4 =
                        FStarC_Syntax_Embeddings_Base.try_unembed ea x norm in
                      FStarC_Compiler_Util.bind_opt uu___4
                        (fun x1 ->
                           let uu___5 =
                             FStarC_Syntax_Embeddings_Base.try_unembed eb y
                               norm in
                           FStarC_Compiler_Util.bind_opt uu___5
                             (fun y1 ->
                                let uu___6 =
                                  let uu___7 =
                                    let uu___8 = f x1 y1 in
                                    FStarC_Syntax_Embeddings_Base.embed ec
                                      uu___8 in
                                  uu___7 rng shadow_app norm in
                                FStar_Pervasives_Native.Some uu___6)) in
                    (match uu___3 with
                     | FStar_Pervasives_Native.Some x1 ->
                         FStar_Pervasives_Native.Some x1
                     | FStar_Pervasives_Native.None ->
                         force_shadow shadow_app) in
              f_wrapped
let arrow_as_prim_step_3 :
  'a 'b 'c 'd .
    'a FStarC_Syntax_Embeddings_Base.embedding ->
      'b FStarC_Syntax_Embeddings_Base.embedding ->
        'c FStarC_Syntax_Embeddings_Base.embedding ->
          'd FStarC_Syntax_Embeddings_Base.embedding ->
            ('a -> 'b -> 'c -> 'd) ->
              FStarC_Ident.lid ->
                FStarC_Syntax_Embeddings_Base.norm_cb ->
                  FStarC_Syntax_Syntax.universes ->
                    FStarC_Syntax_Syntax.args ->
                      FStarC_Syntax_Syntax.term
                        FStar_Pervasives_Native.option
  =
  fun ea ->
    fun eb ->
      fun ec ->
        fun ed ->
          fun f ->
            fun fv_lid ->
              fun norm ->
                let rng = FStarC_Ident.range_of_lid fv_lid in
                let f_wrapped _us args =
                  let uu___ = args in
                  match uu___ with
                  | (x, uu___1)::(y, uu___2)::(z, uu___3)::[] ->
                      let shadow_app =
                        let uu___4 =
                          FStarC_Thunk.mk
                            (fun uu___5 ->
                               let uu___6 =
                                 norm (FStar_Pervasives.Inl fv_lid) in
                               FStarC_Syntax_Syntax.mk_Tm_app uu___6 args rng) in
                        FStar_Pervasives_Native.Some uu___4 in
                      let uu___4 =
                        let uu___5 =
                          FStarC_Syntax_Embeddings_Base.try_unembed ea x norm in
                        FStarC_Compiler_Util.bind_opt uu___5
                          (fun x1 ->
                             let uu___6 =
                               FStarC_Syntax_Embeddings_Base.try_unembed eb y
                                 norm in
                             FStarC_Compiler_Util.bind_opt uu___6
                               (fun y1 ->
                                  let uu___7 =
                                    FStarC_Syntax_Embeddings_Base.try_unembed
                                      ec z norm in
                                  FStarC_Compiler_Util.bind_opt uu___7
                                    (fun z1 ->
                                       let uu___8 =
                                         let uu___9 =
                                           let uu___10 = f x1 y1 z1 in
                                           FStarC_Syntax_Embeddings_Base.embed
                                             ed uu___10 in
                                         uu___9 rng shadow_app norm in
                                       FStar_Pervasives_Native.Some uu___8))) in
                      (match uu___4 with
                       | FStar_Pervasives_Native.Some x1 ->
                           FStar_Pervasives_Native.Some x1
                       | FStar_Pervasives_Native.None ->
                           force_shadow shadow_app) in
                f_wrapped
let debug_wrap : 'a . Prims.string -> (unit -> 'a) -> 'a =
  fun s ->
    fun f ->
      (let uu___1 =
         FStarC_Compiler_Effect.op_Bang FStarC_Options.debug_embedding in
       if uu___1
       then FStarC_Compiler_Util.print1 "++++starting %s\n" s
       else ());
      (let res = f () in
       (let uu___2 =
          FStarC_Compiler_Effect.op_Bang FStarC_Options.debug_embedding in
        if uu___2
        then FStarC_Compiler_Util.print1 "------ending %s\n" s
        else ());
       res)
let (e_abstract_term : abstract_term FStarC_Syntax_Embeddings_Base.embedding)
  =
  FStarC_Syntax_Embeddings_Base.embed_as e_any (fun x -> Abstract x)
    (fun x -> match x with | Abstract x1 -> x1) FStar_Pervasives_Native.None