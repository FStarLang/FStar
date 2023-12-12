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
let (uu___is_Int8 : machint_kind -> Prims.bool) =
  fun projectee -> match projectee with | Int8 -> true | uu___ -> false
let (uu___is_Int16 : machint_kind -> Prims.bool) =
  fun projectee -> match projectee with | Int16 -> true | uu___ -> false
let (uu___is_Int32 : machint_kind -> Prims.bool) =
  fun projectee -> match projectee with | Int32 -> true | uu___ -> false
let (uu___is_Int64 : machint_kind -> Prims.bool) =
  fun projectee -> match projectee with | Int64 -> true | uu___ -> false
let (uu___is_UInt8 : machint_kind -> Prims.bool) =
  fun projectee -> match projectee with | UInt8 -> true | uu___ -> false
let (uu___is_UInt16 : machint_kind -> Prims.bool) =
  fun projectee -> match projectee with | UInt16 -> true | uu___ -> false
let (uu___is_UInt32 : machint_kind -> Prims.bool) =
  fun projectee -> match projectee with | UInt32 -> true | uu___ -> false
let (uu___is_UInt64 : machint_kind -> Prims.bool) =
  fun projectee -> match projectee with | UInt64 -> true | uu___ -> false
let (uu___is_UInt128 : machint_kind -> Prims.bool) =
  fun projectee -> match projectee with | UInt128 -> true | uu___ -> false
let (uu___is_SizeT : machint_kind -> Prims.bool) =
  fun projectee -> match projectee with | SizeT -> true | uu___ -> false
let (all_machint_kinds : machint_kind Prims.list) =
  [Int8; Int16; Int32; Int64; UInt8; UInt16; UInt32; UInt64; UInt128; SizeT]
let (is_unsigned : machint_kind -> Prims.bool) =
  fun k ->
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
let (width : machint_kind -> Prims.int) =
  fun k ->
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
let (module_name_for : machint_kind -> Prims.string) =
  fun k ->
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
let (mask : machint_kind -> FStar_BigInt.t) =
  fun k ->
    let uu___ = width k in
    match uu___ with
    | uu___1 when uu___1 = (Prims.of_int (8)) -> FStar_BigInt.of_hex "ff"
    | uu___1 when uu___1 = (Prims.of_int (16)) -> FStar_BigInt.of_hex "ffff"
    | uu___1 when uu___1 = (Prims.of_int (32)) ->
        FStar_BigInt.of_hex "ffffffff"
    | uu___1 when uu___1 = (Prims.of_int (64)) ->
        FStar_BigInt.of_hex "ffffffffffffffff"
    | uu___1 when uu___1 = (Prims.of_int (128)) ->
        FStar_BigInt.of_hex "ffffffffffffffffffffffffffffffff"
let (int_to_t_lid_for : machint_kind -> FStar_Ident.lid) =
  fun k ->
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
    FStar_Ident.lid_of_path path FStar_Compiler_Range_Type.dummyRange
let (int_to_t_for : machint_kind -> FStar_Syntax_Syntax.term) =
  fun k ->
    let lid = int_to_t_lid_for k in
    FStar_Syntax_Syntax.fvar lid FStar_Pervasives_Native.None
let (__int_to_t_lid_for : machint_kind -> FStar_Ident.lid) =
  fun k ->
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
    FStar_Ident.lid_of_path path FStar_Compiler_Range_Type.dummyRange
let (__int_to_t_for : machint_kind -> FStar_Syntax_Syntax.term) =
  fun k ->
    let lid = __int_to_t_lid_for k in
    FStar_Syntax_Syntax.fvar lid FStar_Pervasives_Native.None
type 'k machint =
  | Mk of FStar_BigInt.t * FStar_Syntax_Syntax.meta_source_info
  FStar_Pervasives_Native.option 
let (uu___is_Mk : machint_kind -> unit machint -> Prims.bool) =
  fun k -> fun projectee -> true
let (__proj__Mk__item___0 : machint_kind -> unit machint -> FStar_BigInt.t) =
  fun k -> fun projectee -> match projectee with | Mk (_0, _1) -> _0
let (__proj__Mk__item___1 :
  machint_kind ->
    unit machint ->
      FStar_Syntax_Syntax.meta_source_info FStar_Pervasives_Native.option)
  = fun k -> fun projectee -> match projectee with | Mk (_0, _1) -> _1
let (showable_bounded_K :
  machint_kind -> unit machint FStar_Class_Show.showable) =
  fun k ->
    {
      FStar_Class_Show.show =
        (fun uu___ ->
           match uu___ with
           | Mk (x, m) ->
               let uu___1 =
                 let uu___2 =
                   let uu___3 = FStar_BigInt.to_int_fs x in
                   FStar_Class_Show.show
                     (FStar_Class_Show.printableshow
                        FStar_Class_Printable.printable_int) uu___3 in
                 let uu___3 =
                   let uu___4 = module_name_for k in Prims.strcat "@@" uu___4 in
                 Prims.strcat uu___2 uu___3 in
               Prims.strcat "machine integer " uu___1)
    }
let (e_machint :
  machint_kind -> unit machint FStar_Syntax_Embeddings_Base.embedding) =
  fun k ->
    let with_meta_ds r t m =
      match m with
      | FStar_Pervasives_Native.None -> t
      | FStar_Pervasives_Native.Some m1 ->
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_meta
               {
                 FStar_Syntax_Syntax.tm2 = t;
                 FStar_Syntax_Syntax.meta =
                   (FStar_Syntax_Syntax.Meta_desugared m1)
               }) r in
    let em x rng shadow cb =
      let uu___ = x in
      match uu___ with
      | Mk (i, m) ->
          let it =
            FStar_TypeChecker_Primops_Base.embed_simple
              FStar_Syntax_Embeddings.e_int rng i in
          let int_to_t = int_to_t_for k in
          let t =
            let uu___1 =
              let uu___2 = FStar_Syntax_Syntax.as_arg it in [uu___2] in
            FStar_Syntax_Syntax.mk_Tm_app int_to_t uu___1 rng in
          with_meta_ds rng t m in
    let un uu___1 uu___ =
      (fun t ->
         fun cb ->
           let uu___ =
             let uu___1 =
               let uu___2 = FStar_Syntax_Subst.compress t in
               uu___2.FStar_Syntax_Syntax.n in
             match uu___1 with
             | FStar_Syntax_Syntax.Tm_meta
                 { FStar_Syntax_Syntax.tm2 = t1;
                   FStar_Syntax_Syntax.meta =
                     FStar_Syntax_Syntax.Meta_desugared m;_}
                 -> (t1, (FStar_Pervasives_Native.Some m))
             | uu___2 -> (t, FStar_Pervasives_Native.None) in
           match uu___ with
           | (t1, m) ->
               let t2 = FStar_Syntax_Util.unmeta_safe t1 in
               let uu___1 =
                 let uu___2 = FStar_Syntax_Subst.compress t2 in
                 uu___2.FStar_Syntax_Syntax.n in
               (match uu___1 with
                | FStar_Syntax_Syntax.Tm_app
                    { FStar_Syntax_Syntax.hd = hd;
                      FStar_Syntax_Syntax.args = (a, uu___2)::[];_}
                    when
                    (let uu___3 = int_to_t_lid_for k in
                     FStar_Syntax_Util.is_fvar uu___3 hd) ||
                      (let uu___3 = __int_to_t_lid_for k in
                       FStar_Syntax_Util.is_fvar uu___3 hd)
                    ->
                    Obj.magic
                      (Obj.repr
                         (let a1 = FStar_Syntax_Util.unlazy_emb a in
                          let uu___3 =
                            FStar_TypeChecker_Primops_Base.try_unembed_simple
                              FStar_Syntax_Embeddings.e_int a1 in
                          FStar_Class_Monad.op_let_Bang
                            FStar_Class_Monad.monad_option () ()
                            (Obj.magic uu___3)
                            (fun uu___4 ->
                               (fun a2 ->
                                  let a2 = Obj.magic a2 in
                                  Obj.magic
                                    (FStar_Pervasives_Native.Some
                                       (Mk (a2, m)))) uu___4)))
                | uu___2 -> Obj.magic (Obj.repr FStar_Pervasives_Native.None)))
        uu___1 uu___ in
    FStar_Syntax_Embeddings_Base.mk_emb_full em un
      (fun uu___ -> FStar_Syntax_Syntax.t_int) (fun uu___ -> "boundedint")
      (fun uu___ -> FStar_Syntax_Syntax.ET_abstract)
let (nbe_machint :
  machint_kind -> unit machint FStar_TypeChecker_NBETerm.embedding) =
  fun k ->
    let with_meta_ds t m =
      match m with
      | FStar_Pervasives_Native.None -> t
      | FStar_Pervasives_Native.Some m1 ->
          let uu___ =
            let uu___1 =
              let uu___2 =
                FStar_Thunk.mk
                  (fun uu___3 -> FStar_Syntax_Syntax.Meta_desugared m1) in
              (t, uu___2) in
            FStar_TypeChecker_NBETerm.Meta uu___1 in
          FStar_TypeChecker_NBETerm.mk_t uu___ in
    let em cbs x =
      let uu___ = x in
      match uu___ with
      | Mk (i, m) ->
          let it =
            FStar_TypeChecker_NBETerm.embed FStar_TypeChecker_NBETerm.e_int
              cbs i in
          let int_to_t args =
            let uu___1 =
              let uu___2 =
                let uu___3 =
                  let uu___4 = __int_to_t_lid_for k in
                  FStar_Syntax_Syntax.lid_as_fv uu___4
                    FStar_Pervasives_Native.None in
                (uu___3, [], args) in
              FStar_TypeChecker_NBETerm.FV uu___2 in
            FStar_TypeChecker_NBETerm.mk_t uu___1 in
          let t =
            let uu___1 =
              let uu___2 = FStar_TypeChecker_NBETerm.as_arg it in [uu___2] in
            int_to_t uu___1 in
          with_meta_ds t m in
    let un uu___1 uu___ =
      (fun cbs ->
         fun a ->
           let uu___ =
             match a.FStar_TypeChecker_NBETerm.nbe_t with
             | FStar_TypeChecker_NBETerm.Meta (t, tm) ->
                 let uu___1 = FStar_Thunk.force tm in
                 (match uu___1 with
                  | FStar_Syntax_Syntax.Meta_desugared m ->
                      (t, (FStar_Pervasives_Native.Some m))
                  | uu___2 -> (a, FStar_Pervasives_Native.None))
             | uu___1 -> (a, FStar_Pervasives_Native.None) in
           match uu___ with
           | (a1, m) ->
               (match a1.FStar_TypeChecker_NBETerm.nbe_t with
                | FStar_TypeChecker_NBETerm.FV (fv1, [], (a2, uu___1)::[])
                    when
                    let uu___2 = int_to_t_lid_for k in
                    FStar_Ident.lid_equals
                      (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      uu___2
                    ->
                    Obj.magic
                      (Obj.repr
                         (let uu___2 =
                            FStar_TypeChecker_NBETerm.unembed
                              FStar_TypeChecker_NBETerm.e_int cbs a2 in
                          FStar_Class_Monad.op_let_Bang
                            FStar_Class_Monad.monad_option () ()
                            (Obj.magic uu___2)
                            (fun uu___3 ->
                               (fun a3 ->
                                  let a3 = Obj.magic a3 in
                                  Obj.magic
                                    (FStar_Pervasives_Native.Some
                                       (Mk (a3, m)))) uu___3)))
                | uu___1 -> Obj.magic (Obj.repr FStar_Pervasives_Native.None)))
        uu___1 uu___ in
    FStar_TypeChecker_NBETerm.mk_emb em un
      (fun uu___ ->
         let uu___1 =
           FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.int_lid
             FStar_Pervasives_Native.None in
         FStar_TypeChecker_NBETerm.mkFV uu___1 [] [])
      (fun uu___ -> FStar_Syntax_Syntax.ET_abstract)
let (v : machint_kind -> unit machint -> FStar_BigInt.t) =
  fun k -> fun x -> let uu___ = x in match uu___ with | Mk (v1, uu___1) -> v1
let (meta :
  machint_kind ->
    unit machint ->
      FStar_Syntax_Syntax.meta_source_info FStar_Pervasives_Native.option)
  =
  fun k ->
    fun x -> let uu___ = x in match uu___ with | Mk (uu___1, meta1) -> meta1
let (make_as :
  machint_kind -> unit machint -> FStar_BigInt.t -> unit machint) =
  fun k -> fun x -> fun z -> Mk (z, (meta k x))
type 'a mymon =
  (FStar_TypeChecker_Primops_Base.primitive_step Prims.list, unit, 'a)
    FStar_Compiler_Writer.writer
let (bounded_arith_ops_for : machint_kind -> unit mymon) =
  fun k ->
    let mod_name = module_name_for k in
    let nm s =
      let uu___ =
        let uu___1 = let uu___2 = module_name_for k in [uu___2; s] in "FStar"
          :: uu___1 in
      FStar_Parser_Const.p2l uu___ in
    let uu___ =
      let uu___1 =
        let uu___2 =
          let uu___3 = nm "v" in
          FStar_TypeChecker_Primops_Base.mk1 Prims.int_zero uu___3
            (e_machint k) (nbe_machint k) FStar_Syntax_Embeddings.e_int
            FStar_TypeChecker_NBETerm.e_int (v k) in
        let uu___3 =
          let uu___4 =
            let uu___5 = nm "add" in
            FStar_TypeChecker_Primops_Base.mk2 Prims.int_zero uu___5
              (e_machint k) (nbe_machint k) (e_machint k) (nbe_machint k)
              (e_machint k) (nbe_machint k)
              (fun x ->
                 fun y ->
                   let uu___6 = FStar_BigInt.add_big_int (v k x) (v k y) in
                   make_as k x uu___6) in
          let uu___5 =
            let uu___6 =
              let uu___7 = nm "sub" in
              FStar_TypeChecker_Primops_Base.mk2 Prims.int_zero uu___7
                (e_machint k) (nbe_machint k) (e_machint k) (nbe_machint k)
                (e_machint k) (nbe_machint k)
                (fun x ->
                   fun y ->
                     let uu___8 = FStar_BigInt.sub_big_int (v k x) (v k y) in
                     make_as k x uu___8) in
            let uu___7 =
              let uu___8 =
                let uu___9 = nm "mul" in
                FStar_TypeChecker_Primops_Base.mk2 Prims.int_zero uu___9
                  (e_machint k) (nbe_machint k) (e_machint k) (nbe_machint k)
                  (e_machint k) (nbe_machint k)
                  (fun x ->
                     fun y ->
                       let uu___10 =
                         FStar_BigInt.mult_big_int (v k x) (v k y) in
                       make_as k x uu___10) in
              let uu___9 =
                let uu___10 =
                  let uu___11 = nm "gt" in
                  FStar_TypeChecker_Primops_Base.mk2 Prims.int_zero uu___11
                    (e_machint k) (nbe_machint k) (e_machint k)
                    (nbe_machint k) FStar_Syntax_Embeddings.e_bool
                    FStar_TypeChecker_NBETerm.e_bool
                    (fun x ->
                       fun y -> FStar_BigInt.gt_big_int (v k x) (v k y)) in
                let uu___11 =
                  let uu___12 =
                    let uu___13 = nm "gte" in
                    FStar_TypeChecker_Primops_Base.mk2 Prims.int_zero uu___13
                      (e_machint k) (nbe_machint k) (e_machint k)
                      (nbe_machint k) FStar_Syntax_Embeddings.e_bool
                      FStar_TypeChecker_NBETerm.e_bool
                      (fun x ->
                         fun y -> FStar_BigInt.ge_big_int (v k x) (v k y)) in
                  let uu___13 =
                    let uu___14 =
                      let uu___15 = nm "lt" in
                      FStar_TypeChecker_Primops_Base.mk2 Prims.int_zero
                        uu___15 (e_machint k) (nbe_machint k) (e_machint k)
                        (nbe_machint k) FStar_Syntax_Embeddings.e_bool
                        FStar_TypeChecker_NBETerm.e_bool
                        (fun x ->
                           fun y -> FStar_BigInt.lt_big_int (v k x) (v k y)) in
                    let uu___15 =
                      let uu___16 =
                        let uu___17 = nm "lte" in
                        FStar_TypeChecker_Primops_Base.mk2 Prims.int_zero
                          uu___17 (e_machint k) (nbe_machint k) (e_machint k)
                          (nbe_machint k) FStar_Syntax_Embeddings.e_bool
                          FStar_TypeChecker_NBETerm.e_bool
                          (fun x ->
                             fun y -> FStar_BigInt.le_big_int (v k x) (v k y)) in
                      [uu___16] in
                    uu___14 :: uu___15 in
                  uu___12 :: uu___13 in
                uu___10 :: uu___11 in
              uu___8 :: uu___9 in
            uu___6 :: uu___7 in
          uu___4 :: uu___5 in
        uu___2 :: uu___3 in
      FStar_Compiler_Writer.emit (FStar_Class_Monoid.monoid_list ()) uu___1 in
    FStar_Class_Monad.op_let_Bang
      (FStar_Compiler_Writer.monad_writer (FStar_Class_Monoid.monoid_list ()))
      () () uu___
      (fun uu___1 ->
         (fun uu___1 ->
            let uu___1 = Obj.magic uu___1 in
            let sz = width k in
            let modulus =
              let uu___2 = FStar_BigInt.of_int_fs sz in
              FStar_BigInt.shift_left_big_int FStar_BigInt.one uu___2 in
            let mod1 x = FStar_BigInt.mod_big_int x modulus in
            let uu___2 =
              let uu___3 = is_unsigned k in
              if uu___3
              then
                let uu___4 =
                  let uu___5 =
                    let uu___6 = nm "add_mod" in
                    FStar_TypeChecker_Primops_Base.mk2 Prims.int_zero uu___6
                      (e_machint k) (nbe_machint k) (e_machint k)
                      (nbe_machint k) (e_machint k) (nbe_machint k)
                      (fun x ->
                         fun y ->
                           let uu___7 =
                             let uu___8 =
                               FStar_BigInt.add_big_int (v k x) (v k y) in
                             mod1 uu___8 in
                           make_as k x uu___7) in
                  let uu___6 =
                    let uu___7 =
                      let uu___8 = nm "sub_mod" in
                      FStar_TypeChecker_Primops_Base.mk2 Prims.int_zero
                        uu___8 (e_machint k) (nbe_machint k) (e_machint k)
                        (nbe_machint k) (e_machint k) (nbe_machint k)
                        (fun x ->
                           fun y ->
                             let uu___9 =
                               let uu___10 =
                                 FStar_BigInt.sub_big_int (v k x) (v k y) in
                               mod1 uu___10 in
                             make_as k x uu___9) in
                    let uu___8 =
                      let uu___9 =
                        let uu___10 = nm "div" in
                        FStar_TypeChecker_Primops_Base.mk2 Prims.int_zero
                          uu___10 (e_machint k) (nbe_machint k) (e_machint k)
                          (nbe_machint k) (e_machint k) (nbe_machint k)
                          (fun x ->
                             fun y ->
                               let uu___11 =
                                 let uu___12 =
                                   FStar_BigInt.div_big_int (v k x) (v k y) in
                                 mod1 uu___12 in
                               make_as k x uu___11) in
                      let uu___10 =
                        let uu___11 =
                          let uu___12 = nm "rem" in
                          FStar_TypeChecker_Primops_Base.mk2 Prims.int_zero
                            uu___12 (e_machint k) (nbe_machint k)
                            (e_machint k) (nbe_machint k) (e_machint k)
                            (nbe_machint k)
                            (fun x ->
                               fun y ->
                                 let uu___13 =
                                   let uu___14 =
                                     FStar_BigInt.mod_big_int (v k x) (v k y) in
                                   mod1 uu___14 in
                                 make_as k x uu___13) in
                        let uu___12 =
                          let uu___13 =
                            let uu___14 = nm "logor" in
                            FStar_TypeChecker_Primops_Base.mk2 Prims.int_zero
                              uu___14 (e_machint k) (nbe_machint k)
                              (e_machint k) (nbe_machint k) (e_machint k)
                              (nbe_machint k)
                              (fun x ->
                                 fun y ->
                                   let uu___15 =
                                     FStar_BigInt.logor_big_int (v k x)
                                       (v k y) in
                                   make_as k x uu___15) in
                          let uu___14 =
                            let uu___15 =
                              let uu___16 = nm "logand" in
                              FStar_TypeChecker_Primops_Base.mk2
                                Prims.int_zero uu___16 (e_machint k)
                                (nbe_machint k) (e_machint k) (nbe_machint k)
                                (e_machint k) (nbe_machint k)
                                (fun x ->
                                   fun y ->
                                     let uu___17 =
                                       FStar_BigInt.logand_big_int (v k x)
                                         (v k y) in
                                     make_as k x uu___17) in
                            let uu___16 =
                              let uu___17 =
                                let uu___18 = nm "logxor" in
                                FStar_TypeChecker_Primops_Base.mk2
                                  Prims.int_zero uu___18 (e_machint k)
                                  (nbe_machint k) (e_machint k)
                                  (nbe_machint k) (e_machint k)
                                  (nbe_machint k)
                                  (fun x ->
                                     fun y ->
                                       let uu___19 =
                                         FStar_BigInt.logxor_big_int (
                                           v k x) (v k y) in
                                       make_as k x uu___19) in
                              let uu___18 =
                                let uu___19 =
                                  let uu___20 = nm "lognot" in
                                  FStar_TypeChecker_Primops_Base.mk1
                                    Prims.int_zero uu___20 (e_machint k)
                                    (nbe_machint k) (e_machint k)
                                    (nbe_machint k)
                                    (fun x ->
                                       let uu___21 =
                                         let uu___22 =
                                           FStar_BigInt.lognot_big_int
                                             (v k x) in
                                         let uu___23 = mask k in
                                         FStar_BigInt.logand_big_int uu___22
                                           uu___23 in
                                       make_as k x uu___21) in
                                let uu___20 =
                                  let uu___21 =
                                    let uu___22 = nm "shift_left" in
                                    FStar_TypeChecker_Primops_Base.mk2
                                      Prims.int_zero uu___22 (e_machint k)
                                      (nbe_machint k) (e_machint UInt32)
                                      (nbe_machint UInt32) (e_machint k)
                                      (nbe_machint k)
                                      (fun x ->
                                         fun y ->
                                           let uu___23 =
                                             let uu___24 =
                                               FStar_BigInt.shift_left_big_int
                                                 (v k x) (v UInt32 y) in
                                             let uu___25 = mask k in
                                             FStar_BigInt.logand_big_int
                                               uu___24 uu___25 in
                                           make_as k x uu___23) in
                                  let uu___22 =
                                    let uu___23 =
                                      let uu___24 = nm "shift_right" in
                                      FStar_TypeChecker_Primops_Base.mk2
                                        Prims.int_zero uu___24 (e_machint k)
                                        (nbe_machint k) (e_machint UInt32)
                                        (nbe_machint UInt32) (e_machint k)
                                        (nbe_machint k)
                                        (fun x ->
                                           fun y ->
                                             let uu___25 =
                                               let uu___26 =
                                                 FStar_BigInt.shift_right_big_int
                                                   (v k x) (v UInt32 y) in
                                               let uu___27 = mask k in
                                               FStar_BigInt.logand_big_int
                                                 uu___26 uu___27 in
                                             make_as k x uu___25) in
                                    [uu___23] in
                                  uu___21 :: uu___22 in
                                uu___19 :: uu___20 in
                              uu___17 :: uu___18 in
                            uu___15 :: uu___16 in
                          uu___13 :: uu___14 in
                        uu___11 :: uu___12 in
                      uu___9 :: uu___10 in
                    uu___7 :: uu___8 in
                  uu___5 :: uu___6 in
                FStar_Compiler_Writer.emit
                  (FStar_Class_Monoid.monoid_list ()) uu___4
              else
                FStar_Class_Monad.return
                  (FStar_Compiler_Writer.monad_writer
                     (FStar_Class_Monoid.monoid_list ())) () (Obj.repr ()) in
            Obj.magic
              (FStar_Class_Monad.op_let_Bang
                 (FStar_Compiler_Writer.monad_writer
                    (FStar_Class_Monoid.monoid_list ())) () () uu___2
                 (fun uu___3 ->
                    (fun uu___3 ->
                       let uu___3 = Obj.magic uu___3 in
                       let uu___4 =
                         let uu___5 = (is_unsigned k) && (k <> SizeT) in
                         if uu___5
                         then
                           let uu___6 =
                             let uu___7 =
                               let uu___8 = nm "add_underspec" in
                               FStar_TypeChecker_Primops_Base.mk2
                                 Prims.int_zero uu___8 (e_machint k)
                                 (nbe_machint k) (e_machint k)
                                 (nbe_machint k) (e_machint k)
                                 (nbe_machint k)
                                 (fun x ->
                                    fun y ->
                                      let uu___9 =
                                        FStar_BigInt.add_big_int (v k x)
                                          (v k y) in
                                      make_as k x uu___9) in
                             let uu___8 =
                               let uu___9 =
                                 let uu___10 = nm "sub_underspec" in
                                 FStar_TypeChecker_Primops_Base.mk2
                                   Prims.int_zero uu___10 (e_machint k)
                                   (nbe_machint k) (e_machint k)
                                   (nbe_machint k) (e_machint k)
                                   (nbe_machint k)
                                   (fun x ->
                                      fun y ->
                                        let uu___11 =
                                          FStar_BigInt.sub_big_int (v k x)
                                            (v k y) in
                                        make_as k x uu___11) in
                               let uu___10 =
                                 let uu___11 =
                                   let uu___12 = nm "mul_underspec" in
                                   FStar_TypeChecker_Primops_Base.mk2
                                     Prims.int_zero uu___12 (e_machint k)
                                     (nbe_machint k) (e_machint k)
                                     (nbe_machint k) (e_machint k)
                                     (nbe_machint k)
                                     (fun x ->
                                        fun y ->
                                          let uu___13 =
                                            FStar_BigInt.mult_big_int (
                                              v k x) (v k y) in
                                          make_as k x uu___13) in
                                 [uu___11] in
                               uu___9 :: uu___10 in
                             uu___7 :: uu___8 in
                           FStar_Compiler_Writer.emit
                             (FStar_Class_Monoid.monoid_list ()) uu___6
                         else
                           FStar_Class_Monad.return
                             (FStar_Compiler_Writer.monad_writer
                                (FStar_Class_Monoid.monoid_list ())) ()
                             (Obj.repr ()) in
                       Obj.magic
                         (FStar_Class_Monad.op_let_Bang
                            (FStar_Compiler_Writer.monad_writer
                               (FStar_Class_Monoid.monoid_list ())) () ()
                            uu___4
                            (fun uu___5 ->
                               (fun uu___5 ->
                                  let uu___5 = Obj.magic uu___5 in
                                  let uu___6 =
                                    let uu___7 =
                                      (is_unsigned k) &&
                                        ((k <> SizeT) && (k <> UInt128)) in
                                    if uu___7
                                    then
                                      let uu___8 =
                                        let uu___9 =
                                          let uu___10 = nm "mul_mod" in
                                          FStar_TypeChecker_Primops_Base.mk2
                                            Prims.int_zero uu___10
                                            (e_machint k) (nbe_machint k)
                                            (e_machint k) (nbe_machint k)
                                            (e_machint k) (nbe_machint k)
                                            (fun x ->
                                               fun y ->
                                                 let uu___11 =
                                                   let uu___12 =
                                                     FStar_BigInt.mult_big_int
                                                       (v k x) (v k y) in
                                                   mod1 uu___12 in
                                                 make_as k x uu___11) in
                                        [uu___9] in
                                      FStar_Compiler_Writer.emit
                                        (FStar_Class_Monoid.monoid_list ())
                                        uu___8
                                    else
                                      FStar_Class_Monad.return
                                        (FStar_Compiler_Writer.monad_writer
                                           (FStar_Class_Monoid.monoid_list ()))
                                        () (Obj.repr ()) in
                                  Obj.magic
                                    (FStar_Class_Monad.op_let_Bang
                                       (FStar_Compiler_Writer.monad_writer
                                          (FStar_Class_Monoid.monoid_list ()))
                                       () () uu___6
                                       (fun uu___7 ->
                                          (fun uu___7 ->
                                             let uu___7 = Obj.magic uu___7 in
                                             Obj.magic
                                               (FStar_Class_Monad.return
                                                  (FStar_Compiler_Writer.monad_writer
                                                     (FStar_Class_Monoid.monoid_list
                                                        ())) () (Obj.repr ())))
                                            uu___7))) uu___5))) uu___3)))
           uu___1)
let (bounded_arith_ops :
  FStar_TypeChecker_Primops_Base.primitive_step Prims.list) =
  let uu___ =
    let uu___1 =
      let uu___2 =
        FStar_Class_Monad.iterM
          (FStar_Compiler_Writer.monad_writer
             (FStar_Class_Monoid.monoid_list ())) ()
          (fun uu___3 -> (Obj.magic bounded_arith_ops_for) uu___3)
          (Obj.magic all_machint_kinds) in
      FStar_Class_Monad.op_let_Bang
        (FStar_Compiler_Writer.monad_writer
           (FStar_Class_Monoid.monoid_list ())) () () uu___2
        (fun uu___3 ->
           (fun uu___3 ->
              let uu___3 = Obj.magic uu___3 in
              let uu___4 =
                let uu___5 =
                  FStar_TypeChecker_Primops_Base.mk1 Prims.int_zero
                    FStar_Parser_Const.char_u32_of_char
                    FStar_Syntax_Embeddings.e_char
                    FStar_TypeChecker_NBETerm.e_char (e_machint UInt32)
                    (nbe_machint UInt32)
                    (fun c ->
                       let n =
                         FStar_BigInt.of_int_fs
                           (FStar_Compiler_Util.int_of_char c) in
                       Mk (n, FStar_Pervasives_Native.None)) in
                [uu___5] in
              Obj.magic
                (FStar_Compiler_Writer.emit
                   (FStar_Class_Monoid.monoid_list ()) uu___4)) uu___3) in
    Obj.magic
      (FStar_Compiler_Writer.run_writer (FStar_Class_Monoid.monoid_list ())
         () (Obj.magic uu___1)) in
  FStar_Pervasives_Native.fst uu___