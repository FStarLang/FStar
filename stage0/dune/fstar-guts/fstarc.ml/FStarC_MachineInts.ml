open Prims
type machint_kind =
  | Int8 
  | Int16 
  | Int32 
  | Int64 
  | UInt8 
  | UInt16 
  | UInt32 
  | UInt64 
  | UInt128 
  | SizeT 
let uu___is_Int8 (projectee : machint_kind) : Prims.bool=
  match projectee with | Int8 -> true | uu___ -> false
let uu___is_Int16 (projectee : machint_kind) : Prims.bool=
  match projectee with | Int16 -> true | uu___ -> false
let uu___is_Int32 (projectee : machint_kind) : Prims.bool=
  match projectee with | Int32 -> true | uu___ -> false
let uu___is_Int64 (projectee : machint_kind) : Prims.bool=
  match projectee with | Int64 -> true | uu___ -> false
let uu___is_UInt8 (projectee : machint_kind) : Prims.bool=
  match projectee with | UInt8 -> true | uu___ -> false
let uu___is_UInt16 (projectee : machint_kind) : Prims.bool=
  match projectee with | UInt16 -> true | uu___ -> false
let uu___is_UInt32 (projectee : machint_kind) : Prims.bool=
  match projectee with | UInt32 -> true | uu___ -> false
let uu___is_UInt64 (projectee : machint_kind) : Prims.bool=
  match projectee with | UInt64 -> true | uu___ -> false
let uu___is_UInt128 (projectee : machint_kind) : Prims.bool=
  match projectee with | UInt128 -> true | uu___ -> false
let uu___is_SizeT (projectee : machint_kind) : Prims.bool=
  match projectee with | SizeT -> true | uu___ -> false
let all_machint_kinds : machint_kind Prims.list=
  [Int8; Int16; Int32; Int64; UInt8; UInt16; UInt32; UInt64; UInt128; SizeT]
let is_unsigned (k : machint_kind) : Prims.bool=
  match k with
  | Int8 -> false
  | Int16 -> false
  | Int32 -> false
  | Int64 -> false
  | UInt8 -> true
  | UInt16 -> true
  | UInt32 -> true
  | UInt64 -> true
  | UInt128 -> true
  | SizeT -> true
let is_signed (k : machint_kind) : Prims.bool=
  let uu___ = is_unsigned k in Prims.op_Negation uu___
let width (k : machint_kind) : Prims.int=
  match k with
  | Int8 -> (Prims.of_int (8))
  | Int16 -> (Prims.of_int (16))
  | Int32 -> (Prims.of_int (32))
  | Int64 -> (Prims.of_int (64))
  | UInt8 -> (Prims.of_int (8))
  | UInt16 -> (Prims.of_int (16))
  | UInt32 -> (Prims.of_int (32))
  | UInt64 -> (Prims.of_int (64))
  | UInt128 -> (Prims.of_int (128))
  | SizeT -> (Prims.of_int (64))
let module_name_for (k : machint_kind) : Prims.string=
  match k with
  | Int8 -> "Int8"
  | Int16 -> "Int16"
  | Int32 -> "Int32"
  | Int64 -> "Int64"
  | UInt8 -> "UInt8"
  | UInt16 -> "UInt16"
  | UInt32 -> "UInt32"
  | UInt64 -> "UInt64"
  | UInt128 -> "UInt128"
  | SizeT -> "SizeT"
let mask (k : machint_kind) : Prims.int=
  let uu___ = width k in
  match uu___ with
  | uu___1 when uu___1 = (Prims.of_int (8)) -> (Prims.of_int (0xff))
  | uu___1 when uu___1 = (Prims.of_int (16)) -> (Prims.parse_int "0xffff")
  | uu___1 when uu___1 = (Prims.of_int (32)) ->
      (Prims.parse_int "0xffffffff")
  | uu___1 when uu___1 = (Prims.of_int (64)) ->
      (Prims.parse_int "0xffffffffffffffff")
  | uu___1 when uu___1 = (Prims.of_int (128)) ->
      (Prims.parse_int "0xffffffffffffffffffffffffffffffff")
let int_to_t_lid_for (k : machint_kind) : FStarC_Ident.lid=
  let path =
    let uu___ =
      let uu___1 = module_name_for k in
      let uu___2 =
        let uu___3 =
          let uu___4 = is_unsigned k in
          if uu___4 then "uint_to_t" else "int_to_t" in
        [uu___3] in
      uu___1 :: uu___2 in
    "FStar" :: uu___ in
  FStarC_Ident.lid_of_path path FStarC_Range_Type.dummyRange
let int_to_t_for (k : machint_kind) : FStarC_Syntax_Syntax.term=
  let lid = int_to_t_lid_for k in
  FStarC_Syntax_Syntax.fvar lid FStar_Pervasives_Native.None
let __int_to_t_lid_for (k : machint_kind) : FStarC_Ident.lid=
  let path =
    let uu___ =
      let uu___1 = module_name_for k in
      let uu___2 =
        let uu___3 =
          let uu___4 = is_unsigned k in
          if uu___4 then "__uint_to_t" else "__int_to_t" in
        [uu___3] in
      uu___1 :: uu___2 in
    "FStar" :: uu___ in
  FStarC_Ident.lid_of_path path FStarC_Range_Type.dummyRange
let __int_to_t_for (k : machint_kind) : FStarC_Syntax_Syntax.term=
  let lid = __int_to_t_lid_for k in
  FStarC_Syntax_Syntax.fvar lid FStar_Pervasives_Native.None
type 'k machint =
  | Mk of Prims.int * FStarC_Syntax_Syntax.meta_source_info
  FStar_Pervasives_Native.option 
let uu___is_Mk (k : machint_kind) (projectee : Obj.t machint) : Prims.bool=
  true
let __proj__Mk__item___0 (k : machint_kind) (projectee : Obj.t machint) :
  Prims.int= match projectee with | Mk (_0, _1) -> _0
let __proj__Mk__item___1 (k : machint_kind) (projectee : Obj.t machint) :
  FStarC_Syntax_Syntax.meta_source_info FStar_Pervasives_Native.option=
  match projectee with | Mk (_0, _1) -> _1
let mk (k : machint_kind) (x : Prims.int)
  (m : FStarC_Syntax_Syntax.meta_source_info FStar_Pervasives_Native.option)
  : Obj.t machint= Mk (x, m)
let v (k : machint_kind) (x : Obj.t machint) : Prims.int=
  let uu___ = x in match uu___ with | Mk (v1, uu___1) -> v1
let meta (k : machint_kind) (x : Obj.t machint) :
  FStarC_Syntax_Syntax.meta_source_info FStar_Pervasives_Native.option=
  let uu___ = x in match uu___ with | Mk (uu___1, meta1) -> meta1
let make_as (k : machint_kind) (x : Obj.t machint) (z : Prims.int) :
  Obj.t machint= let uu___ = meta k x in Mk (z, uu___)
let showable_bounded_k (k : machint_kind) :
  Obj.t machint FStarC_Class_Show.showable=
  {
    FStarC_Class_Show.show =
      (fun uu___ ->
         match uu___ with
         | Mk (x, m) ->
             let uu___1 =
               let uu___2 =
                 FStarC_Class_Show.show FStarC_Class_Show.showable_int x in
               let uu___3 =
                 let uu___4 = module_name_for k in Prims.strcat "@@" uu___4 in
               Prims.strcat uu___2 uu___3 in
             Prims.strcat "machine integer " uu___1)
  }
let e_machint (k : machint_kind) :
  Obj.t machint FStarC_Syntax_Embeddings_Base.embedding=
  let with_meta_ds r t m =
    match m with
    | FStar_Pervasives_Native.None -> t
    | FStar_Pervasives_Native.Some m1 ->
        FStarC_Syntax_Syntax.mk
          (FStarC_Syntax_Syntax.Tm_meta
             {
               FStarC_Syntax_Syntax.tm2 = t;
               FStarC_Syntax_Syntax.meta =
                 (FStarC_Syntax_Syntax.Meta_desugared m1)
             }) r in
  let em x rng shadow cb =
    let uu___ = x in
    match uu___ with
    | Mk (i, m) ->
        let it =
          let uu___1 =
            FStarC_Syntax_Embeddings_Base.embed
              FStarC_Syntax_Embeddings.e_int i in
          uu___1 rng FStar_Pervasives_Native.None cb in
        let int_to_t = int_to_t_for k in
        let t =
          let uu___1 =
            let uu___2 = FStarC_Syntax_Syntax.as_arg it in [uu___2] in
          FStarC_Syntax_Syntax.mk_Tm_app int_to_t uu___1 rng in
        with_meta_ds rng t m in
  let un uu___1 uu___ =
    (fun t cb ->
       let uu___ =
         let uu___1 =
           let uu___2 = FStarC_Syntax_Subst.compress t in
           uu___2.FStarC_Syntax_Syntax.n in
         match uu___1 with
         | FStarC_Syntax_Syntax.Tm_meta
             { FStarC_Syntax_Syntax.tm2 = t1;
               FStarC_Syntax_Syntax.meta =
                 FStarC_Syntax_Syntax.Meta_desugared m;_}
             -> (t1, (FStar_Pervasives_Native.Some m))
         | uu___2 -> (t, FStar_Pervasives_Native.None) in
       match uu___ with
       | (t1, m) ->
           let t2 = FStarC_Syntax_Util.unmeta_safe t1 in
           let uu___1 =
             let uu___2 = FStarC_Syntax_Subst.compress t2 in
             uu___2.FStarC_Syntax_Syntax.n in
           (match uu___1 with
            | FStarC_Syntax_Syntax.Tm_app
                { FStarC_Syntax_Syntax.hd = hd;
                  FStarC_Syntax_Syntax.args = (a, uu___2)::[];_}
                when
                (let uu___3 = int_to_t_lid_for k in
                 FStarC_Syntax_Util.is_fvar uu___3 hd) ||
                  (let uu___3 = __int_to_t_lid_for k in
                   FStarC_Syntax_Util.is_fvar uu___3 hd)
                ->
                Obj.magic
                  (Obj.repr
                     (let a1 = FStarC_Syntax_Util.unlazy_emb a in
                      let uu___3 =
                        FStarC_Syntax_Embeddings_Base.try_unembed
                          FStarC_Syntax_Embeddings.e_int a1 cb in
                      FStarC_Class_Monad.op_let_Bang
                        FStarC_Class_Monad.monad_option () ()
                        (Obj.magic uu___3)
                        (fun uu___4 ->
                           (fun a2 ->
                              let a2 = Obj.magic a2 in
                              Obj.magic
                                (FStar_Pervasives_Native.Some (Mk (a2, m))))
                             uu___4)))
            | uu___2 -> Obj.magic (Obj.repr FStar_Pervasives_Native.None)))
      uu___1 uu___ in
  FStarC_Syntax_Embeddings_Base.mk_emb_full em un
    (fun uu___ ->
       let uu___1 =
         let uu___2 =
           let uu___3 = let uu___4 = module_name_for k in [uu___4; "t"] in
           "FStar" :: uu___3 in
         FStarC_Ident.lid_of_path uu___2 FStarC_Range_Type.dummyRange in
       FStarC_Syntax_Syntax.fvar uu___1 FStar_Pervasives_Native.None)
    (fun uu___ -> "boundedint")
    (fun uu___ -> FStarC_Syntax_Syntax.ET_abstract)
let nbe_machint (k : machint_kind) :
  Obj.t machint FStarC_TypeChecker_NBETerm.embedding=
  let with_meta_ds t m =
    match m with
    | FStar_Pervasives_Native.None -> t
    | FStar_Pervasives_Native.Some m1 ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              FStarC_Thunk.mk
                (fun uu___3 -> FStarC_Syntax_Syntax.Meta_desugared m1) in
            (t, uu___2) in
          FStarC_TypeChecker_NBETerm.Meta uu___1 in
        FStarC_TypeChecker_NBETerm.mk_t uu___ in
  let em cbs x =
    let uu___ = x in
    match uu___ with
    | Mk (i, m) ->
        let it =
          FStarC_TypeChecker_NBETerm.embed FStarC_TypeChecker_NBETerm.e_int
            cbs i in
        let int_to_t args =
          let uu___1 =
            let uu___2 =
              let uu___3 =
                let uu___4 = __int_to_t_lid_for k in
                FStarC_Syntax_Syntax.lid_as_fv uu___4
                  FStar_Pervasives_Native.None in
              (uu___3, [], args) in
            FStarC_TypeChecker_NBETerm.FV uu___2 in
          FStarC_TypeChecker_NBETerm.mk_t uu___1 in
        let t =
          let uu___1 =
            let uu___2 = FStarC_TypeChecker_NBETerm.as_arg it in [uu___2] in
          int_to_t uu___1 in
        with_meta_ds t m in
  let un uu___1 uu___ =
    (fun cbs a ->
       let uu___ =
         match a.FStarC_TypeChecker_NBETerm.nbe_t with
         | FStarC_TypeChecker_NBETerm.Meta (t, tm) ->
             let uu___1 = FStarC_Thunk.force tm in
             (match uu___1 with
              | FStarC_Syntax_Syntax.Meta_desugared m ->
                  (t, (FStar_Pervasives_Native.Some m))
              | uu___2 -> (a, FStar_Pervasives_Native.None))
         | uu___1 -> (a, FStar_Pervasives_Native.None) in
       match uu___ with
       | (a1, m) ->
           (match a1.FStarC_TypeChecker_NBETerm.nbe_t with
            | FStarC_TypeChecker_NBETerm.FV (fv1, [], (a2, uu___1)::[]) when
                (let uu___2 = int_to_t_lid_for k in
                 FStarC_Ident.lid_equals fv1.FStarC_Syntax_Syntax.fv_name
                   uu___2)
                  ||
                  (let uu___2 = __int_to_t_lid_for k in
                   FStarC_Ident.lid_equals fv1.FStarC_Syntax_Syntax.fv_name
                     uu___2)
                ->
                Obj.magic
                  (Obj.repr
                     (let uu___2 =
                        FStarC_TypeChecker_NBETerm.unembed
                          FStarC_TypeChecker_NBETerm.e_int cbs a2 in
                      FStarC_Class_Monad.op_let_Bang
                        FStarC_Class_Monad.monad_option () ()
                        (Obj.magic uu___2)
                        (fun uu___3 ->
                           (fun a3 ->
                              let a3 = Obj.magic a3 in
                              Obj.magic
                                (FStar_Pervasives_Native.Some (Mk (a3, m))))
                             uu___3)))
            | uu___1 -> Obj.magic (Obj.repr FStar_Pervasives_Native.None)))
      uu___1 uu___ in
  FStarC_TypeChecker_NBETerm.mk_emb em un
    (fun uu___ ->
       let uu___1 =
         let uu___2 =
           let uu___3 =
             let uu___4 = let uu___5 = module_name_for k in [uu___5; "t"] in
             "FStar" :: uu___4 in
           FStarC_Ident.lid_of_path uu___3 FStarC_Range_Type.dummyRange in
         FStarC_Syntax_Syntax.lid_as_fv uu___2 FStar_Pervasives_Native.None in
       FStarC_TypeChecker_NBETerm.mkFV uu___1 [] [])
    (fun uu___ -> FStarC_Syntax_Syntax.ET_abstract)
