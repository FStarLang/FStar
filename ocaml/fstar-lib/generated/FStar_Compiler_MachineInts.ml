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
let (is_signed : machint_kind -> Prims.bool) =
  fun k -> let uu___ = is_unsigned k in Prims.op_Negation uu___
let (widthn : machint_kind -> Prims.int) =
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
    let uu___ = widthn k in
    match uu___ with
    | uu___1 when uu___1 = (Prims.of_int (8)) -> FStar_BigInt.of_hex "ff"
    | uu___1 when uu___1 = (Prims.of_int (16)) -> FStar_BigInt.of_hex "ffff"
    | uu___1 when uu___1 = (Prims.of_int (32)) ->
        FStar_BigInt.of_hex "ffffffff"
    | uu___1 when uu___1 = (Prims.of_int (64)) ->
        FStar_BigInt.of_hex "ffffffffffffffff"
    | uu___1 when uu___1 = (Prims.of_int (128)) ->
        FStar_BigInt.of_hex "ffffffffffffffffffffffffffffffff"
let (signedness : machint_kind -> FStar_Const.signedness) =
  fun k ->
    let uu___ = is_unsigned k in
    if uu___ then FStar_Const.Unsigned else FStar_Const.Signed
let (width : machint_kind -> FStar_Const.width) =
  fun k ->
    match k with
    | Int8 -> FStar_Const.Int8
    | UInt8 -> FStar_Const.Int8
    | Int16 -> FStar_Const.Int16
    | UInt16 -> FStar_Const.Int16
    | Int32 -> FStar_Const.Int32
    | UInt32 -> FStar_Const.Int32
    | Int64 -> FStar_Const.Int64
    | UInt64 -> FStar_Const.Int64
    | UInt128 -> FStar_Const.Int128
    | SizeT -> FStar_Const.Sizet
type 'k machint =
  | Mk of FStar_BigInt.t 
let (uu___is_Mk : machint_kind -> unit machint -> Prims.bool) =
  fun k -> fun projectee -> true
let (__proj__Mk__item___0 : machint_kind -> unit machint -> FStar_BigInt.t) =
  fun k -> fun projectee -> match projectee with | Mk _0 -> _0
let (mk : machint_kind -> FStar_BigInt.t -> unit machint) =
  fun k -> fun x -> Mk x
let (v : machint_kind -> unit machint -> FStar_BigInt.t) =
  fun k -> fun x -> let uu___ = x in match uu___ with | Mk v1 -> v1
let (int_to_t : machint_kind -> FStar_BigInt.t -> unit machint) =
  fun k -> fun i -> Mk i
let (make_as :
  machint_kind -> unit machint -> FStar_BigInt.t -> unit machint) =
  fun k -> fun x -> fun z -> Mk z
let (showable_bounded_k :
  machint_kind -> unit machint FStar_Class_Show.showable) =
  fun k ->
    {
      FStar_Class_Show.show =
        (fun uu___ ->
           match uu___ with
           | Mk x ->
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
      | Mk i ->
          let const =
            let uu___1 =
              let uu___2 = FStar_BigInt.string_of_big_int i in
              let uu___3 =
                let uu___4 =
                  let uu___5 = signedness k in
                  let uu___6 = width k in (uu___5, uu___6) in
                FStar_Pervasives_Native.Some uu___4 in
              (uu___2, uu___3) in
            FStar_Const.Const_int uu___1 in
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant const) rng in
    let un t cb =
      let t1 = FStar_Syntax_Util.unmeta_safe t in
      let uu___ =
        let uu___1 = FStar_Syntax_Subst.compress t1 in
        uu___1.FStar_Syntax_Syntax.n in
      match uu___ with
      | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
          (str, FStar_Pervasives_Native.Some (s, w))) when
          (let uu___1 = signedness k in s = uu___1) &&
            (let uu___1 = width k in w = uu___1)
          ->
          let n = FStar_BigInt.big_int_of_string str in
          FStar_Pervasives_Native.Some (Mk n)
      | uu___1 -> FStar_Pervasives_Native.None in
    FStar_Syntax_Embeddings_Base.mk_emb_full em un
      (fun uu___ ->
         let uu___1 =
           let uu___2 =
             let uu___3 = let uu___4 = module_name_for k in [uu___4; "t"] in
             "FStar" :: uu___3 in
           FStar_Ident.lid_of_path uu___2
             FStar_Compiler_Range_Type.dummyRange in
         FStar_Syntax_Syntax.fvar uu___1 FStar_Pervasives_Native.None)
      (fun uu___ -> "boundedint")
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
      | Mk i ->
          let const =
            let uu___1 =
              let uu___2 = FStar_BigInt.string_of_big_int i in
              let uu___3 =
                let uu___4 =
                  let uu___5 = signedness k in
                  let uu___6 = width k in (uu___5, uu___6) in
                FStar_Pervasives_Native.Some uu___4 in
              (uu___2, uu___3) in
            FStar_Const.Const_int uu___1 in
          FStar_TypeChecker_NBETerm.mk_t
            (FStar_TypeChecker_NBETerm.Constant
               (FStar_TypeChecker_NBETerm.SConst const)) in
    let un cbs a =
      match a.FStar_TypeChecker_NBETerm.nbe_t with
      | FStar_TypeChecker_NBETerm.Constant (FStar_TypeChecker_NBETerm.SConst
          (FStar_Const.Const_int (str, FStar_Pervasives_Native.Some (s, w))))
          when
          (let uu___ = signedness k in s = uu___) &&
            (let uu___ = width k in w = uu___)
          ->
          let n = FStar_BigInt.big_int_of_string str in
          FStar_Pervasives_Native.Some (Mk n)
      | uu___ -> FStar_Pervasives_Native.None in
    FStar_TypeChecker_NBETerm.mk_emb em un
      (fun uu___ ->
         let uu___1 =
           let uu___2 =
             let uu___3 =
               let uu___4 = let uu___5 = module_name_for k in [uu___5; "t"] in
               "FStar" :: uu___4 in
             FStar_Ident.lid_of_path uu___3
               FStar_Compiler_Range_Type.dummyRange in
           FStar_Syntax_Syntax.lid_as_fv uu___2 FStar_Pervasives_Native.None in
         FStar_TypeChecker_NBETerm.mkFV uu___1 [] [])
      (fun uu___ -> FStar_Syntax_Syntax.ET_abstract)