open Prims
type extern =
  {
  x_name: Prims.string FStar_Pervasives_Native.option ;
  x_header: Prims.string FStar_Pervasives_Native.option }
let __proj__Mkextern__item__x_name (projectee : extern) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with | { x_name; x_header;_} -> x_name
let __proj__Mkextern__item__x_header (projectee : extern) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with | { x_name; x_header;_} -> x_header
type rule =
  | Rule_prim of (Prims.int *
  (FStarC_Custard_Syntax.cty Prims.list ->
     FStarC_Custard_Syntax.expr Prims.list -> FStarC_Custard_Syntax.expr))
  
  | Rule_type of
  (FStarC_Custard_Syntax.cty Prims.list -> FStarC_Custard_Syntax.cty) 
  | Rule_extern of extern 
  | Rule_opaque 
  | Rule_realized 
let uu___is_Rule_prim (projectee : rule) : Prims.bool=
  match projectee with | Rule_prim _0 -> true | uu___ -> false
let __proj__Rule_prim__item___0 (projectee : rule) :
  (Prims.int *
    (FStarC_Custard_Syntax.cty Prims.list ->
       FStarC_Custard_Syntax.expr Prims.list -> FStarC_Custard_Syntax.expr))=
  match projectee with | Rule_prim _0 -> _0
let uu___is_Rule_type (projectee : rule) : Prims.bool=
  match projectee with | Rule_type _0 -> true | uu___ -> false
let __proj__Rule_type__item___0 (projectee : rule) :
  FStarC_Custard_Syntax.cty Prims.list -> FStarC_Custard_Syntax.cty=
  match projectee with | Rule_type _0 -> _0
let uu___is_Rule_extern (projectee : rule) : Prims.bool=
  match projectee with | Rule_extern _0 -> true | uu___ -> false
let __proj__Rule_extern__item___0 (projectee : rule) : extern=
  match projectee with | Rule_extern _0 -> _0
let uu___is_Rule_opaque (projectee : rule) : Prims.bool=
  match projectee with | Rule_opaque -> true | uu___ -> false
let uu___is_Rule_realized (projectee : rule) : Prims.bool=
  match projectee with | Rule_realized -> true | uu___ -> false
let table : rule FStarC_SMap.t= FStarC_SMap.create (Prims.of_int 100)
let register_rule (l : FStarC_Ident.lident) (r : rule) : unit=
  FStarC_SMap.add table (FStarC_Ident.string_of_lid l) r
let int128_enabled (uu___ : unit) : Prims.bool=
  let b = FStarC_Options.custard_backend () in
  if (b = "C") || (b = "FSharp")
  then FStarC_Options.custard_int128 ()
  else false
let machine_int_of_module (ns : Prims.string Prims.list) :
  (FStarC_Const.signedness * FStarC_Custard_Syntax.iwidth)
    FStar_Pervasives_Native.option=
  match ns with
  | "FStar"::m::[] ->
      (match m with
       | "UInt8" ->
           FStar_Pervasives_Native.Some
             (FStarC_Const.Unsigned, FStarC_Custard_Syntax.W8)
       | "UInt16" ->
           FStar_Pervasives_Native.Some
             (FStarC_Const.Unsigned, FStarC_Custard_Syntax.W16)
       | "UInt32" ->
           FStar_Pervasives_Native.Some
             (FStarC_Const.Unsigned, FStarC_Custard_Syntax.W32)
       | "UInt64" ->
           FStar_Pervasives_Native.Some
             (FStarC_Const.Unsigned, FStarC_Custard_Syntax.W64)
       | "Int8" ->
           FStar_Pervasives_Native.Some
             (FStarC_Const.Signed, FStarC_Custard_Syntax.W8)
       | "Int16" ->
           FStar_Pervasives_Native.Some
             (FStarC_Const.Signed, FStarC_Custard_Syntax.W16)
       | "Int32" ->
           FStar_Pervasives_Native.Some
             (FStarC_Const.Signed, FStarC_Custard_Syntax.W32)
       | "Int64" ->
           FStar_Pervasives_Native.Some
             (FStarC_Const.Signed, FStarC_Custard_Syntax.W64)
       | "UInt128" ->
           let uu___ = int128_enabled () in
           if uu___
           then
             FStar_Pervasives_Native.Some
               (FStarC_Const.Unsigned, FStarC_Custard_Syntax.W128)
           else FStar_Pervasives_Native.None
       | "Int128" ->
           let uu___ = int128_enabled () in
           if uu___
           then
             FStar_Pervasives_Native.Some
               (FStarC_Const.Signed, FStarC_Custard_Syntax.W128)
           else FStar_Pervasives_Native.None
       | "SizeT" ->
           FStar_Pervasives_Native.Some
             (FStarC_Const.Unsigned, FStarC_Custard_Syntax.WSizet)
       | uu___ -> FStar_Pervasives_Native.None)
  | uu___ -> FStar_Pervasives_Native.None
let machine_int_of_name (s : Prims.string) :
  (FStarC_Const.signedness * FStarC_Custard_Syntax.iwidth)
    FStar_Pervasives_Native.option=
  match s with
  | "uint8" ->
      FStar_Pervasives_Native.Some
        (FStarC_Const.Unsigned, FStarC_Custard_Syntax.W8)
  | "uint16" ->
      FStar_Pervasives_Native.Some
        (FStarC_Const.Unsigned, FStarC_Custard_Syntax.W16)
  | "uint32" ->
      FStar_Pervasives_Native.Some
        (FStarC_Const.Unsigned, FStarC_Custard_Syntax.W32)
  | "uint64" ->
      FStar_Pervasives_Native.Some
        (FStarC_Const.Unsigned, FStarC_Custard_Syntax.W64)
  | "int8" ->
      FStar_Pervasives_Native.Some
        (FStarC_Const.Signed, FStarC_Custard_Syntax.W8)
  | "int16" ->
      FStar_Pervasives_Native.Some
        (FStarC_Const.Signed, FStarC_Custard_Syntax.W16)
  | "int32" ->
      FStar_Pervasives_Native.Some
        (FStarC_Const.Signed, FStarC_Custard_Syntax.W32)
  | "int64" ->
      FStar_Pervasives_Native.Some
        (FStarC_Const.Signed, FStarC_Custard_Syntax.W64)
  | "uint128" ->
      let uu___ = int128_enabled () in
      if uu___
      then
        FStar_Pervasives_Native.Some
          (FStarC_Const.Unsigned, FStarC_Custard_Syntax.W128)
      else FStar_Pervasives_Native.None
  | "int128" ->
      let uu___ = int128_enabled () in
      if uu___
      then
        FStar_Pervasives_Native.Some
          (FStarC_Const.Signed, FStarC_Custard_Syntax.W128)
      else FStar_Pervasives_Native.None
  | uu___ -> FStar_Pervasives_Native.None
let int_op (id : Prims.string) :
  (FStarC_Custard_Syntax.op * Prims.int) FStar_Pervasives_Native.option=
  match id with
  | "add" ->
      FStar_Pervasives_Native.Some
        (FStarC_Custard_Syntax.Add, (Prims.of_int 2))
  | "add_underspec" ->
      FStar_Pervasives_Native.Some
        (FStarC_Custard_Syntax.Add, (Prims.of_int 2))
  | "add_mod" ->
      FStar_Pervasives_Native.Some
        (FStarC_Custard_Syntax.AddW, (Prims.of_int 2))
  | "sub" ->
      FStar_Pervasives_Native.Some
        (FStarC_Custard_Syntax.Sub, (Prims.of_int 2))
  | "sub_underspec" ->
      FStar_Pervasives_Native.Some
        (FStarC_Custard_Syntax.Sub, (Prims.of_int 2))
  | "sub_mod" ->
      FStar_Pervasives_Native.Some
        (FStarC_Custard_Syntax.SubW, (Prims.of_int 2))
  | "mul" ->
      FStar_Pervasives_Native.Some
        (FStarC_Custard_Syntax.Mult, (Prims.of_int 2))
  | "mul_underspec" ->
      FStar_Pervasives_Native.Some
        (FStarC_Custard_Syntax.Mult, (Prims.of_int 2))
  | "mul_mod" ->
      FStar_Pervasives_Native.Some
        (FStarC_Custard_Syntax.MultW, (Prims.of_int 2))
  | "div" ->
      FStar_Pervasives_Native.Some
        (FStarC_Custard_Syntax.Div, (Prims.of_int 2))
  | "rem" ->
      FStar_Pervasives_Native.Some
        (FStarC_Custard_Syntax.Mod, (Prims.of_int 2))
  | "logor" ->
      FStar_Pervasives_Native.Some
        (FStarC_Custard_Syntax.BOr, (Prims.of_int 2))
  | "logxor" ->
      FStar_Pervasives_Native.Some
        (FStarC_Custard_Syntax.BXor, (Prims.of_int 2))
  | "logand" ->
      FStar_Pervasives_Native.Some
        (FStarC_Custard_Syntax.BAnd, (Prims.of_int 2))
  | "lognot" ->
      FStar_Pervasives_Native.Some
        (FStarC_Custard_Syntax.BNot, Prims.int_one)
  | "shift_right" ->
      FStar_Pervasives_Native.Some
        (FStarC_Custard_Syntax.BShiftR, (Prims.of_int 2))
  | "shift_left" ->
      FStar_Pervasives_Native.Some
        (FStarC_Custard_Syntax.BShiftL, (Prims.of_int 2))
  | "eq" ->
      FStar_Pervasives_Native.Some
        (FStarC_Custard_Syntax.Eq, (Prims.of_int 2))
  | "ne" ->
      FStar_Pervasives_Native.Some
        (FStarC_Custard_Syntax.Neq, (Prims.of_int 2))
  | "gt" ->
      FStar_Pervasives_Native.Some
        (FStarC_Custard_Syntax.Gt, (Prims.of_int 2))
  | "gte" ->
      FStar_Pervasives_Native.Some
        (FStarC_Custard_Syntax.Gte, (Prims.of_int 2))
  | "lt" ->
      FStar_Pervasives_Native.Some
        (FStarC_Custard_Syntax.Lt, (Prims.of_int 2))
  | "lte" ->
      FStar_Pervasives_Native.Some
        (FStarC_Custard_Syntax.Lte, (Prims.of_int 2))
  | uu___ -> FStar_Pervasives_Native.None
let bool_name : FStarC_Custard_Syntax.name=
  {
    FStarC_Custard_Syntax.ns = ["Prims"];
    FStarC_Custard_Syntax.id = "bool";
    FStarC_Custard_Syntax.spec = FStar_Pervasives_Native.None
  }
let int_lit (sw : (FStarC_Const.signedness * FStarC_Custard_Syntax.iwidth))
  (v : Prims.int) : FStarC_Custard_Syntax.expr=
  FStarC_Custard_Syntax.mk
    (FStarC_Custard_Syntax.EConst
       (FStarC_Custard_Syntax.CInt
          (v, FStar_IntegerLiteral.Dec, (FStar_Pervasives_Native.Some sw))))
    (FStarC_Custard_Syntax.TInt sw) FStarC_Custard_Syntax.E_Pure
let i128_op (sw : (FStarC_Const.signedness * FStarC_Custard_Syntax.iwidth))
  (o : FStarC_Custard_Syntax.op)
  (args : FStarC_Custard_Syntax.expr Prims.list) :
  FStarC_Custard_Syntax.expr=
  let uu___ =
    FStarC_List.fold_left
      (fun a e ->
         FStarC_Custard_Syntax.join_eff a e.FStarC_Custard_Syntax.eff)
      FStarC_Custard_Syntax.E_Pure args in
  FStarC_Custard_Syntax.mk
    (FStarC_Custard_Syntax.EOp
       ({
          FStarC_Custard_Syntax.po_op = o;
          FStarC_Custard_Syntax.po_ty =
            (FStar_Pervasives_Native.Some (FStarC_Custard_Syntax.PInt sw))
        }, args)) (FStarC_Custard_Syntax.TInt sw) uu___
let i128_shift_count (n : Prims.int) : FStarC_Custard_Syntax.expr=
  FStarC_Custard_Syntax.mk
    (FStarC_Custard_Syntax.EConst
       (FStarC_Custard_Syntax.CInt
          (n, FStar_IntegerLiteral.Dec,
            (FStar_Pervasives_Native.Some
               (FStarC_Const.Unsigned, FStarC_Custard_Syntax.W32)))))
    (FStarC_Custard_Syntax.TInt
       (FStarC_Const.Unsigned, FStarC_Custard_Syntax.W32))
    FStarC_Custard_Syntax.E_Pure
let i128_masks
  (sw : (FStarC_Const.signedness * FStarC_Custard_Syntax.iwidth))
  (which : Prims.string) : rule=
  let ty = FStarC_Custard_Syntax.TInt sw in
  let bind nm e k =
    FStarC_Custard_Syntax.mk (FStarC_Custard_Syntax.ELet (nm, ty, e, k))
      k.FStarC_Custard_Syntax.ty
      (FStarC_Custard_Syntax.join_eff e.FStarC_Custard_Syntax.eff
         k.FStarC_Custard_Syntax.eff) in
  let v nm =
    FStarC_Custard_Syntax.mk (FStarC_Custard_Syntax.EVar nm) ty
      FStarC_Custard_Syntax.E_Pure in
  let op o args = i128_op sw o args in
  let x = v "custard_mask_x" in
  let y = v "custard_mask_y" in
  let one = int_lit sw Prims.int_one in
  let top = i128_shift_count (Prims.of_int 127) in
  let body =
    if which = "eq_mask"
    then
      let uu___ = op FStarC_Custard_Syntax.BXor [x; y] in
      let uu___1 =
        let d = v "custard_mask_d" in
        let minus_d =
          let uu___2 =
            let uu___3 = op FStarC_Custard_Syntax.BNot [d] in [uu___3; one] in
          op FStarC_Custard_Syntax.AddW uu___2 in
        let uu___2 =
          let uu___3 =
            let uu___4 =
              let uu___5 = op FStarC_Custard_Syntax.BOr [d; minus_d] in
              [uu___5; top] in
            op FStarC_Custard_Syntax.BShiftR uu___4 in
          [uu___3; one] in
        op FStarC_Custard_Syntax.SubW uu___2 in
      bind "custard_mask_d" uu___ uu___1
    else
      (let q =
         let uu___ =
           let uu___1 = op FStarC_Custard_Syntax.BXor [x; y] in
           let uu___2 =
             let uu___3 =
               let uu___4 =
                 let uu___5 = op FStarC_Custard_Syntax.SubW [x; y] in
                 [uu___5; y] in
               op FStarC_Custard_Syntax.BXor uu___4 in
             [uu___3] in
           uu___1 :: uu___2 in
         op FStarC_Custard_Syntax.BOr uu___ in
       let uu___ =
         let uu___1 =
           let uu___2 =
             let uu___3 = op FStarC_Custard_Syntax.BXor [x; q] in
             [uu___3; top] in
           op FStarC_Custard_Syntax.BShiftR uu___2 in
         [uu___1; one] in
       op FStarC_Custard_Syntax.SubW uu___) in
  Rule_prim
    ((Prims.of_int 2),
      (fun uu___ args ->
         match args with
         | a::b::[] -> bind "custard_mask_x" a (bind "custard_mask_y" b body)
         | uu___1 ->
             FStarC_Effect.failwith
               "Custard: mask applied to the wrong arity"))
let rotate_rule
  (sw : (FStarC_Const.signedness * FStarC_Custard_Syntax.iwidth))
  (left : Prims.bool) : rule=
  let n = FStarC_Custard_Syntax.width_bits (FStar_Pervasives_Native.snd sw) in
  let uw = (FStarC_Const.Unsigned, (FStar_Pervasives_Native.snd sw)) in
  let cnt = (FStarC_Const.Unsigned, FStarC_Custard_Syntax.W32) in
  let cnt_ty = FStarC_Custard_Syntax.TInt cnt in
  let ua =
    FStarC_Custard_Syntax.mk (FStarC_Custard_Syntax.EVar "custard_rot_a")
      (FStarC_Custard_Syntax.TInt uw) FStarC_Custard_Syntax.E_Pure in
  let us =
    FStarC_Custard_Syntax.mk (FStarC_Custard_Syntax.EVar "custard_rot_s")
      cnt_ty FStarC_Custard_Syntax.E_Pure in
  let ucount e =
    FStarC_Custard_Syntax.mk
      (FStarC_Custard_Syntax.EOp
         ({
            FStarC_Custard_Syntax.po_op = FStarC_Custard_Syntax.BAnd;
            FStarC_Custard_Syntax.po_ty =
              (FStar_Pervasives_Native.Some (FStarC_Custard_Syntax.PInt cnt))
          }, [e; int_lit cnt (n - Prims.int_one)])) cnt_ty
      FStarC_Custard_Syntax.E_Pure in
  let far =
    ucount
      (FStarC_Custard_Syntax.mk
         (FStarC_Custard_Syntax.EOp
            ({
               FStarC_Custard_Syntax.po_op = FStarC_Custard_Syntax.SubW;
               FStarC_Custard_Syntax.po_ty =
                 (FStar_Pervasives_Native.Some
                    (FStarC_Custard_Syntax.PInt cnt))
             }, [int_lit cnt n; us])) cnt_ty FStarC_Custard_Syntax.E_Pure) in
  let shift o d =
    FStarC_Custard_Syntax.mk
      (FStarC_Custard_Syntax.EOp
         ({
            FStarC_Custard_Syntax.po_op = o;
            FStarC_Custard_Syntax.po_ty =
              (FStar_Pervasives_Native.Some (FStarC_Custard_Syntax.PInt uw))
          }, [ua; d])) (FStarC_Custard_Syntax.TInt uw)
      FStarC_Custard_Syntax.E_Pure in
  let uu___ =
    if left
    then (FStarC_Custard_Syntax.BShiftL, FStarC_Custard_Syntax.BShiftR)
    else (FStarC_Custard_Syntax.BShiftR, FStarC_Custard_Syntax.BShiftL) in
  match uu___ with
  | (near_op, far_op) ->
      let body =
        FStarC_Custard_Syntax.mk
          (FStarC_Custard_Syntax.EOp
             ({
                FStarC_Custard_Syntax.po_op = FStarC_Custard_Syntax.BOr;
                FStarC_Custard_Syntax.po_ty =
                  (FStar_Pervasives_Native.Some
                     (FStarC_Custard_Syntax.PInt uw))
              }, [shift near_op us; shift far_op far]))
          (FStarC_Custard_Syntax.TInt uw) FStarC_Custard_Syntax.E_Pure in
      let result =
        if
          match FStar_Pervasives_Native.fst sw with
          | FStarC_Const.Unsigned -> true
          | uu___1 -> false
        then body
        else
          FStarC_Custard_Syntax.mk
            (FStarC_Custard_Syntax.ECast
               (body, (FStarC_Custard_Syntax.TInt sw)))
            (FStarC_Custard_Syntax.TInt sw) body.FStarC_Custard_Syntax.eff in
      Rule_prim
        ((Prims.of_int 2),
          ((fun uu___1 args ->
              match args with
              | a::s::[] ->
                  let a1 =
                    if
                      match FStar_Pervasives_Native.fst sw with
                      | FStarC_Const.Unsigned -> true
                      | uu___2 -> false
                    then a
                    else
                      FStarC_Custard_Syntax.mk
                        (FStarC_Custard_Syntax.ECast
                           (a, (FStarC_Custard_Syntax.TInt uw)))
                        (FStarC_Custard_Syntax.TInt uw)
                        a.FStarC_Custard_Syntax.eff in
                  FStarC_Custard_Syntax.mk
                    (FStarC_Custard_Syntax.ELet
                       ("custard_rot_a", (FStarC_Custard_Syntax.TInt uw), a1,
                         (FStarC_Custard_Syntax.mk
                            (FStarC_Custard_Syntax.ELet
                               ("custard_rot_s", cnt_ty, s, result))
                            result.FStarC_Custard_Syntax.ty
                            (FStarC_Custard_Syntax.join_eff
                               s.FStarC_Custard_Syntax.eff
                               result.FStarC_Custard_Syntax.eff))))
                    result.FStarC_Custard_Syntax.ty
                    (FStarC_Custard_Syntax.join_eff
                       a1.FStarC_Custard_Syntax.eff
                       (FStarC_Custard_Syntax.join_eff
                          s.FStarC_Custard_Syntax.eff
                          result.FStarC_Custard_Syntax.eff))
              | uu___2 ->
                  FStarC_Effect.failwith
                    "Custard: rotate applied to the wrong arity")))
let machine_int_rule
  (sw : (FStarC_Const.signedness * FStarC_Custard_Syntax.iwidth))
  (id : Prims.string) : rule FStar_Pervasives_Native.option=
  match int_op id with
  | FStar_Pervasives_Native.Some (o, arity) ->
      let po =
        {
          FStarC_Custard_Syntax.po_op = o;
          FStarC_Custard_Syntax.po_ty =
            (FStar_Pervasives_Native.Some (FStarC_Custard_Syntax.PInt sw))
        } in
      let ret =
        match o with
        | FStarC_Custard_Syntax.Eq ->
            FStarC_Custard_Syntax.TApp (bool_name, [])
        | FStarC_Custard_Syntax.Neq ->
            FStarC_Custard_Syntax.TApp (bool_name, [])
        | FStarC_Custard_Syntax.Lt ->
            FStarC_Custard_Syntax.TApp (bool_name, [])
        | FStarC_Custard_Syntax.Lte ->
            FStarC_Custard_Syntax.TApp (bool_name, [])
        | FStarC_Custard_Syntax.Gt ->
            FStarC_Custard_Syntax.TApp (bool_name, [])
        | FStarC_Custard_Syntax.Gte ->
            FStarC_Custard_Syntax.TApp (bool_name, [])
        | uu___ -> FStarC_Custard_Syntax.TInt sw in
      FStar_Pervasives_Native.Some
        (Rule_prim
           (arity,
             ((fun uu___ args ->
                 FStarC_Custard_Syntax.mk
                   (FStarC_Custard_Syntax.EOp (po, args)) ret
                   FStarC_Custard_Syntax.E_Pure))))
  | FStar_Pervasives_Native.None ->
      (match id with
       | "t" ->
           FStar_Pervasives_Native.Some
             (Rule_type ((fun uu___ -> FStarC_Custard_Syntax.TInt sw)))
       | "zero" ->
           FStar_Pervasives_Native.Some
             (Rule_prim
                (Prims.int_zero,
                  ((fun uu___ uu___1 -> int_lit sw Prims.int_zero))))
       | "one" ->
           FStar_Pervasives_Native.Some
             (Rule_prim
                (Prims.int_zero,
                  ((fun uu___ uu___1 -> int_lit sw Prims.int_one))))
       | "uint_to_t" ->
           FStar_Pervasives_Native.Some
             (Rule_prim
                (Prims.int_one,
                  ((fun uu___ args ->
                      match args with
                      | {
                          FStarC_Custard_Syntax.e =
                            FStarC_Custard_Syntax.EConst
                            (FStarC_Custard_Syntax.CInt (v, b, uu___1));
                          FStarC_Custard_Syntax.ty = uu___2;
                          FStarC_Custard_Syntax.eff = uu___3;_}::[] ->
                          FStarC_Custard_Syntax.mk
                            (FStarC_Custard_Syntax.EConst
                               (FStarC_Custard_Syntax.CInt
                                  (v, b, (FStar_Pervasives_Native.Some sw))))
                            (FStarC_Custard_Syntax.TInt sw)
                            FStarC_Custard_Syntax.E_Pure
                      | a::[] ->
                          FStarC_Custard_Syntax.mk
                            (FStarC_Custard_Syntax.ECast
                               (a, (FStarC_Custard_Syntax.TInt sw)))
                            (FStarC_Custard_Syntax.TInt sw)
                            a.FStarC_Custard_Syntax.eff
                      | uu___1 ->
                          FStarC_Effect.failwith
                            "Custard: machine integer literal rule applied to the wrong arity"))))
       | "int_to_t" ->
           FStar_Pervasives_Native.Some
             (Rule_prim
                (Prims.int_one,
                  ((fun uu___ args ->
                      match args with
                      | {
                          FStarC_Custard_Syntax.e =
                            FStarC_Custard_Syntax.EConst
                            (FStarC_Custard_Syntax.CInt (v, b, uu___1));
                          FStarC_Custard_Syntax.ty = uu___2;
                          FStarC_Custard_Syntax.eff = uu___3;_}::[] ->
                          FStarC_Custard_Syntax.mk
                            (FStarC_Custard_Syntax.EConst
                               (FStarC_Custard_Syntax.CInt
                                  (v, b, (FStar_Pervasives_Native.Some sw))))
                            (FStarC_Custard_Syntax.TInt sw)
                            FStarC_Custard_Syntax.E_Pure
                      | a::[] ->
                          FStarC_Custard_Syntax.mk
                            (FStarC_Custard_Syntax.ECast
                               (a, (FStarC_Custard_Syntax.TInt sw)))
                            (FStarC_Custard_Syntax.TInt sw)
                            a.FStarC_Custard_Syntax.eff
                      | uu___1 ->
                          FStarC_Effect.failwith
                            "Custard: machine integer literal rule applied to the wrong arity"))))
       | "__uint_to_t" ->
           FStar_Pervasives_Native.Some
             (Rule_prim
                (Prims.int_one,
                  ((fun uu___ args ->
                      match args with
                      | {
                          FStarC_Custard_Syntax.e =
                            FStarC_Custard_Syntax.EConst
                            (FStarC_Custard_Syntax.CInt (v, b, uu___1));
                          FStarC_Custard_Syntax.ty = uu___2;
                          FStarC_Custard_Syntax.eff = uu___3;_}::[] ->
                          FStarC_Custard_Syntax.mk
                            (FStarC_Custard_Syntax.EConst
                               (FStarC_Custard_Syntax.CInt
                                  (v, b, (FStar_Pervasives_Native.Some sw))))
                            (FStarC_Custard_Syntax.TInt sw)
                            FStarC_Custard_Syntax.E_Pure
                      | a::[] ->
                          FStarC_Custard_Syntax.mk
                            (FStarC_Custard_Syntax.ECast
                               (a, (FStarC_Custard_Syntax.TInt sw)))
                            (FStarC_Custard_Syntax.TInt sw)
                            a.FStarC_Custard_Syntax.eff
                      | uu___1 ->
                          FStarC_Effect.failwith
                            "Custard: machine integer literal rule applied to the wrong arity"))))
       | "__int_to_t" ->
           FStar_Pervasives_Native.Some
             (Rule_prim
                (Prims.int_one,
                  ((fun uu___ args ->
                      match args with
                      | {
                          FStarC_Custard_Syntax.e =
                            FStarC_Custard_Syntax.EConst
                            (FStarC_Custard_Syntax.CInt (v, b, uu___1));
                          FStarC_Custard_Syntax.ty = uu___2;
                          FStarC_Custard_Syntax.eff = uu___3;_}::[] ->
                          FStarC_Custard_Syntax.mk
                            (FStarC_Custard_Syntax.EConst
                               (FStarC_Custard_Syntax.CInt
                                  (v, b, (FStar_Pervasives_Native.Some sw))))
                            (FStarC_Custard_Syntax.TInt sw)
                            FStarC_Custard_Syntax.E_Pure
                      | a::[] ->
                          FStarC_Custard_Syntax.mk
                            (FStarC_Custard_Syntax.ECast
                               (a, (FStarC_Custard_Syntax.TInt sw)))
                            (FStarC_Custard_Syntax.TInt sw)
                            a.FStarC_Custard_Syntax.eff
                      | uu___1 ->
                          FStarC_Effect.failwith
                            "Custard: machine integer literal rule applied to the wrong arity"))))
       | "v" ->
           FStar_Pervasives_Native.Some
             (Rule_extern
                {
                  x_name = FStar_Pervasives_Native.None;
                  x_header = FStar_Pervasives_Native.None
                })
       | "to_string" ->
           FStar_Pervasives_Native.Some
             (Rule_extern
                {
                  x_name = FStar_Pervasives_Native.None;
                  x_header = FStar_Pervasives_Native.None
                })
       | "to_string_hex" ->
           FStar_Pervasives_Native.Some
             (Rule_extern
                {
                  x_name = FStar_Pervasives_Native.None;
                  x_header = FStar_Pervasives_Native.None
                })
       | "to_string_hex_pad" ->
           FStar_Pervasives_Native.Some
             (Rule_extern
                {
                  x_name = FStar_Pervasives_Native.None;
                  x_header = FStar_Pervasives_Native.None
                })
       | "of_string" ->
           FStar_Pervasives_Native.Some
             (Rule_extern
                {
                  x_name = FStar_Pervasives_Native.None;
                  x_header = FStar_Pervasives_Native.None
                })
       | "uint16_to_sizet" when
           (FStar_Pervasives_Native.snd sw) = FStarC_Custard_Syntax.WSizet ->
           FStar_Pervasives_Native.Some
             (Rule_prim
                (Prims.int_one,
                  ((fun uu___ args ->
                      match args with
                      | a::[] ->
                          FStarC_Custard_Syntax.mk
                            (FStarC_Custard_Syntax.ECast
                               (a, (FStarC_Custard_Syntax.TInt sw)))
                            (FStarC_Custard_Syntax.TInt sw)
                            a.FStarC_Custard_Syntax.eff
                      | uu___1 ->
                          FStarC_Effect.failwith
                            "Custard: SizeT conversion applied to the wrong arity"))))
       | "uint32_to_sizet" when
           (FStar_Pervasives_Native.snd sw) = FStarC_Custard_Syntax.WSizet ->
           FStar_Pervasives_Native.Some
             (Rule_prim
                (Prims.int_one,
                  ((fun uu___ args ->
                      match args with
                      | a::[] ->
                          FStarC_Custard_Syntax.mk
                            (FStarC_Custard_Syntax.ECast
                               (a, (FStarC_Custard_Syntax.TInt sw)))
                            (FStarC_Custard_Syntax.TInt sw)
                            a.FStarC_Custard_Syntax.eff
                      | uu___1 ->
                          FStarC_Effect.failwith
                            "Custard: SizeT conversion applied to the wrong arity"))))
       | "uint64_to_sizet" when
           (FStar_Pervasives_Native.snd sw) = FStarC_Custard_Syntax.WSizet ->
           FStar_Pervasives_Native.Some
             (Rule_prim
                (Prims.int_one,
                  ((fun uu___ args ->
                      match args with
                      | a::[] ->
                          FStarC_Custard_Syntax.mk
                            (FStarC_Custard_Syntax.ECast
                               (a, (FStarC_Custard_Syntax.TInt sw)))
                            (FStarC_Custard_Syntax.TInt sw)
                            a.FStarC_Custard_Syntax.eff
                      | uu___1 ->
                          FStarC_Effect.failwith
                            "Custard: SizeT conversion applied to the wrong arity"))))
       | "of_u32" when
           (FStar_Pervasives_Native.snd sw) = FStarC_Custard_Syntax.WSizet ->
           FStar_Pervasives_Native.Some
             (Rule_prim
                (Prims.int_one,
                  ((fun uu___ args ->
                      match args with
                      | a::[] ->
                          FStarC_Custard_Syntax.mk
                            (FStarC_Custard_Syntax.ECast
                               (a, (FStarC_Custard_Syntax.TInt sw)))
                            (FStarC_Custard_Syntax.TInt sw)
                            a.FStarC_Custard_Syntax.eff
                      | uu___1 ->
                          FStarC_Effect.failwith
                            "Custard: SizeT conversion applied to the wrong arity"))))
       | "of_u64" when
           (FStar_Pervasives_Native.snd sw) = FStarC_Custard_Syntax.WSizet ->
           FStar_Pervasives_Native.Some
             (Rule_prim
                (Prims.int_one,
                  ((fun uu___ args ->
                      match args with
                      | a::[] ->
                          FStarC_Custard_Syntax.mk
                            (FStarC_Custard_Syntax.ECast
                               (a, (FStarC_Custard_Syntax.TInt sw)))
                            (FStarC_Custard_Syntax.TInt sw)
                            a.FStarC_Custard_Syntax.eff
                      | uu___1 ->
                          FStarC_Effect.failwith
                            "Custard: SizeT conversion applied to the wrong arity"))))
       | "sizet_to_uint32" when
           (FStar_Pervasives_Native.snd sw) = FStarC_Custard_Syntax.WSizet ->
           let target =
             if id = "sizet_to_uint32"
             then (FStarC_Const.Unsigned, FStarC_Custard_Syntax.W32)
             else (FStarC_Const.Unsigned, FStarC_Custard_Syntax.W64) in
           FStar_Pervasives_Native.Some
             (Rule_prim
                (Prims.int_one,
                  ((fun uu___ args ->
                      match args with
                      | a::[] ->
                          FStarC_Custard_Syntax.mk
                            (FStarC_Custard_Syntax.ECast
                               (a, (FStarC_Custard_Syntax.TInt target)))
                            (FStarC_Custard_Syntax.TInt target)
                            a.FStarC_Custard_Syntax.eff
                      | uu___1 ->
                          FStarC_Effect.failwith
                            "Custard: SizeT conversion applied to the wrong arity"))))
       | "sizet_to_uint64" when
           (FStar_Pervasives_Native.snd sw) = FStarC_Custard_Syntax.WSizet ->
           let target =
             if id = "sizet_to_uint32"
             then (FStarC_Const.Unsigned, FStarC_Custard_Syntax.W32)
             else (FStarC_Const.Unsigned, FStarC_Custard_Syntax.W64) in
           FStar_Pervasives_Native.Some
             (Rule_prim
                (Prims.int_one,
                  ((fun uu___ args ->
                      match args with
                      | a::[] ->
                          FStarC_Custard_Syntax.mk
                            (FStarC_Custard_Syntax.ECast
                               (a, (FStarC_Custard_Syntax.TInt target)))
                            (FStarC_Custard_Syntax.TInt target)
                            a.FStarC_Custard_Syntax.eff
                      | uu___1 ->
                          FStarC_Effect.failwith
                            "Custard: SizeT conversion applied to the wrong arity"))))
       | "uint64_to_uint128" when
           (FStar_Pervasives_Native.snd sw) = FStarC_Custard_Syntax.W128 ->
           FStar_Pervasives_Native.Some
             (Rule_prim
                (Prims.int_one,
                  ((fun uu___ args ->
                      match args with
                      | a::[] ->
                          FStarC_Custard_Syntax.mk
                            (FStarC_Custard_Syntax.ECast
                               (a, (FStarC_Custard_Syntax.TInt sw)))
                            (FStarC_Custard_Syntax.TInt sw)
                            a.FStarC_Custard_Syntax.eff
                      | uu___1 ->
                          FStarC_Effect.failwith
                            "Custard: 128-bit conversion applied to the wrong arity"))))
       | "uint128_to_uint64" when
           (FStar_Pervasives_Native.snd sw) = FStarC_Custard_Syntax.W128 ->
           let target = (FStarC_Const.Unsigned, FStarC_Custard_Syntax.W64) in
           FStar_Pervasives_Native.Some
             (Rule_prim
                (Prims.int_one,
                  ((fun uu___ args ->
                      match args with
                      | a::[] ->
                          FStarC_Custard_Syntax.mk
                            (FStarC_Custard_Syntax.ECast
                               (a, (FStarC_Custard_Syntax.TInt target)))
                            (FStarC_Custard_Syntax.TInt target)
                            a.FStarC_Custard_Syntax.eff
                      | uu___1 ->
                          FStarC_Effect.failwith
                            "Custard: 128-bit conversion applied to the wrong arity"))))
       | "mul_wide" when
           (FStar_Pervasives_Native.snd sw) = FStarC_Custard_Syntax.W128 ->
           FStar_Pervasives_Native.Some
             (Rule_prim
                ((Prims.of_int 2),
                  ((fun uu___ args ->
                      match args with
                      | a::b::[] ->
                          let wide e =
                            FStarC_Custard_Syntax.mk
                              (FStarC_Custard_Syntax.ECast
                                 (e, (FStarC_Custard_Syntax.TInt sw)))
                              (FStarC_Custard_Syntax.TInt sw)
                              e.FStarC_Custard_Syntax.eff in
                          i128_op sw FStarC_Custard_Syntax.Mult
                            [wide a; wide b]
                      | uu___1 ->
                          FStarC_Effect.failwith
                            "Custard: mul_wide applied to the wrong arity"))))
       | "mul32" when
           (FStar_Pervasives_Native.snd sw) = FStarC_Custard_Syntax.W128 ->
           FStar_Pervasives_Native.Some
             (Rule_prim
                ((Prims.of_int 2),
                  ((fun uu___ args ->
                      match args with
                      | a::b::[] ->
                          let wide e =
                            FStarC_Custard_Syntax.mk
                              (FStarC_Custard_Syntax.ECast
                                 (e, (FStarC_Custard_Syntax.TInt sw)))
                              (FStarC_Custard_Syntax.TInt sw)
                              e.FStarC_Custard_Syntax.eff in
                          i128_op sw FStarC_Custard_Syntax.Mult
                            [wide a; wide b]
                      | uu___1 ->
                          FStarC_Effect.failwith
                            "Custard: mul_wide applied to the wrong arity"))))
       | "shift_arithmetic_right" when
           match FStar_Pervasives_Native.fst sw with
           | FStarC_Const.Signed -> true
           | uu___ -> false ->
           FStar_Pervasives_Native.Some
             (Rule_prim
                ((Prims.of_int 2),
                  ((fun uu___ args ->
                      let uu___1 =
                        FStarC_List.fold_left
                          (fun a e ->
                             FStarC_Custard_Syntax.join_eff a
                               e.FStarC_Custard_Syntax.eff)
                          FStarC_Custard_Syntax.E_Pure args in
                      FStarC_Custard_Syntax.mk
                        (FStarC_Custard_Syntax.EOp
                           ({
                              FStarC_Custard_Syntax.po_op =
                                FStarC_Custard_Syntax.BShiftR;
                              FStarC_Custard_Syntax.po_ty =
                                (FStar_Pervasives_Native.Some
                                   (FStarC_Custard_Syntax.PInt sw))
                            }, args)) (FStarC_Custard_Syntax.TInt sw) uu___1))))
       | "rotate_left" when
           ((FStar_Pervasives_Native.snd sw) <> FStarC_Custard_Syntax.W128)
             &&
             ((FStar_Pervasives_Native.snd sw) <>
                FStarC_Custard_Syntax.WSizet)
           ->
           let uu___ = rotate_rule sw (id = "rotate_left") in
           FStar_Pervasives_Native.Some uu___
       | "rotate_right" when
           ((FStar_Pervasives_Native.snd sw) <> FStarC_Custard_Syntax.W128)
             &&
             ((FStar_Pervasives_Native.snd sw) <>
                FStarC_Custard_Syntax.WSizet)
           ->
           let uu___ = rotate_rule sw (id = "rotate_left") in
           FStar_Pervasives_Native.Some uu___
       | "eq_mask" when
           (FStar_Pervasives_Native.snd sw) = FStarC_Custard_Syntax.W128 ->
           let uu___ = i128_masks sw id in FStar_Pervasives_Native.Some uu___
       | "gte_mask" when
           (FStar_Pervasives_Native.snd sw) = FStarC_Custard_Syntax.W128 ->
           let uu___ = i128_masks sw id in FStar_Pervasives_Native.Some uu___
       | uu___ -> FStar_Pervasives_Native.None)
let float_modules : FStarC_Custard_Syntax.fwidth FStarC_SMap.t=
  FStarC_SMap.create (Prims.of_int 10)
let float_probed : Prims.bool FStarC_SMap.t=
  FStarC_SMap.create (Prims.of_int 10)
let float_probe :
  (Prims.string Prims.list ->
     FStarC_Custard_Syntax.fwidth FStar_Pervasives_Native.option)
    FStarC_Effect.ref=
  FStarC_Effect.mk_ref (fun uu___ -> FStar_Pervasives_Native.None)
let set_float_probe
  (f :
    Prims.string Prims.list ->
      FStarC_Custard_Syntax.fwidth FStar_Pervasives_Native.option)
  : unit= FStarC_Effect.op_Colon_Equals float_probe f
let float_of_module (ns : Prims.string Prims.list) :
  FStarC_Custard_Syntax.fwidth FStar_Pervasives_Native.option=
  match ns with
  | "FStar"::"Float32"::[] ->
      FStar_Pervasives_Native.Some FStarC_Custard_Syntax.Float32
  | "FStar"::"Float64"::[] ->
      FStar_Pervasives_Native.Some FStarC_Custard_Syntax.Float64
  | uu___ ->
      let key = FStarC_String.concat "." ns in
      let uu___1 = FStarC_SMap.try_find float_modules key in
      (match uu___1 with
       | FStar_Pervasives_Native.Some fw -> FStar_Pervasives_Native.Some fw
       | FStar_Pervasives_Native.None ->
           let uu___2 =
             let uu___3 = FStarC_SMap.try_find float_probed key in
             match uu___3 with
             | FStar_Pervasives_Native.Some v -> true
             | uu___4 -> false in
           if uu___2
           then FStar_Pervasives_Native.None
           else
             (FStarC_SMap.add float_probed key true;
              (let uu___4 =
                 let uu___5 = FStarC_Effect.op_Bang float_probe in uu___5 ns in
               match uu___4 with
               | FStar_Pervasives_Native.Some fw ->
                   (FStarC_SMap.add float_modules key fw;
                    FStar_Pervasives_Native.Some fw)
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)))
let float_op (id : Prims.string) :
  (FStarC_Custard_Syntax.op * Prims.int) FStar_Pervasives_Native.option=
  match id with
  | "add" ->
      FStar_Pervasives_Native.Some
        (FStarC_Custard_Syntax.Add, (Prims.of_int 2))
  | "sub" ->
      FStar_Pervasives_Native.Some
        (FStarC_Custard_Syntax.Sub, (Prims.of_int 2))
  | "mul" ->
      FStar_Pervasives_Native.Some
        (FStarC_Custard_Syntax.Mult, (Prims.of_int 2))
  | "div" ->
      FStar_Pervasives_Native.Some
        (FStarC_Custard_Syntax.Div, (Prims.of_int 2))
  | "lt" ->
      FStar_Pervasives_Native.Some
        (FStarC_Custard_Syntax.Lt, (Prims.of_int 2))
  | "lte" ->
      FStar_Pervasives_Native.Some
        (FStarC_Custard_Syntax.Lte, (Prims.of_int 2))
  | "ieee_eq" ->
      FStar_Pervasives_Native.Some
        (FStarC_Custard_Syntax.Eq, (Prims.of_int 2))
  | uu___ -> FStar_Pervasives_Native.None
let float_rule (fw : FStarC_Custard_Syntax.fwidth) (id : Prims.string) :
  rule FStar_Pervasives_Native.option=
  match float_op id with
  | FStar_Pervasives_Native.Some (o, arity) ->
      let po =
        {
          FStarC_Custard_Syntax.po_op = o;
          FStarC_Custard_Syntax.po_ty =
            (FStar_Pervasives_Native.Some (FStarC_Custard_Syntax.PFloat fw))
        } in
      let ret =
        match o with
        | FStarC_Custard_Syntax.Eq ->
            FStarC_Custard_Syntax.TApp (bool_name, [])
        | FStarC_Custard_Syntax.Neq ->
            FStarC_Custard_Syntax.TApp (bool_name, [])
        | FStarC_Custard_Syntax.Lt ->
            FStarC_Custard_Syntax.TApp (bool_name, [])
        | FStarC_Custard_Syntax.Lte ->
            FStarC_Custard_Syntax.TApp (bool_name, [])
        | FStarC_Custard_Syntax.Gt ->
            FStarC_Custard_Syntax.TApp (bool_name, [])
        | FStarC_Custard_Syntax.Gte ->
            FStarC_Custard_Syntax.TApp (bool_name, [])
        | uu___ -> FStarC_Custard_Syntax.TFloat fw in
      FStar_Pervasives_Native.Some
        (Rule_prim
           (arity,
             ((fun uu___ args ->
                 FStarC_Custard_Syntax.mk
                   (FStarC_Custard_Syntax.EOp (po, args)) ret
                   FStarC_Custard_Syntax.E_Pure))))
  | FStar_Pervasives_Native.None ->
      (match id with
       | "t" ->
           FStar_Pervasives_Native.Some
             (Rule_type ((fun uu___ -> FStarC_Custard_Syntax.TFloat fw)))
       | "of_int" ->
           FStar_Pervasives_Native.Some
             (Rule_prim
                (Prims.int_one,
                  ((fun uu___ args ->
                      match args with
                      | a::[] ->
                          FStarC_Custard_Syntax.mk
                            (FStarC_Custard_Syntax.ECast
                               (a, (FStarC_Custard_Syntax.TFloat fw)))
                            (FStarC_Custard_Syntax.TFloat fw)
                            a.FStarC_Custard_Syntax.eff
                      | uu___1 ->
                          FStarC_Effect.failwith
                            "Custard: FStar.Float.of_int applied to the wrong arity"))))
       | "of_literal" ->
           FStar_Pervasives_Native.Some
             (Rule_prim
                (Prims.int_one,
                  ((fun uu___ args ->
                      match args with
                      | {
                          FStarC_Custard_Syntax.e =
                            FStarC_Custard_Syntax.EConst
                            (FStarC_Custard_Syntax.CString v);
                          FStarC_Custard_Syntax.ty = uu___1;
                          FStarC_Custard_Syntax.eff = uu___2;_}::[] ->
                          (match FStarC_Custard_Syntax.float_lit_of_string v
                           with
                           | FStar_Pervasives_Native.Some f ->
                               FStarC_Custard_Syntax.mk
                                 (FStarC_Custard_Syntax.EConst
                                    (FStarC_Custard_Syntax.CFloat (f, fw)))
                                 (FStarC_Custard_Syntax.TFloat fw)
                                 FStarC_Custard_Syntax.E_Pure
                           | FStar_Pervasives_Native.None ->
                               FStarC_Errors.raise_error0
                                 FStarC_Errors_Codes.Error_CustardBadFloatLiteral
                                 ()
                                 (Obj.magic
                                    FStarC_Errors_Msg.is_error_message_list_doc)
                                 (Obj.magic
                                    [FStarC_Errors_Msg.text
                                       (Prims.strcat "Custard: "
                                          (Prims.strcat v
                                             " is not a floating-point literal."));
                                    FStarC_Errors_Msg.text
                                      "of_literal's argument becomes a constant in the generated code, so it                  is accepted only as an optional sign, a mantissa with at least                  one digit, and an optional decimal exponent (section 39.2)."]))
                      | uu___1::[] ->
                          FStarC_Errors.raise_error0
                            FStarC_Errors_Codes.Error_CustardBadFloatLiteral
                            ()
                            (Obj.magic
                               FStarC_Errors_Msg.is_error_message_list_doc)
                            (Obj.magic
                               [FStarC_Errors_Msg.text
                                  "Custard: FStar.Float.of_literal was applied to something that is                not a string literal.";
                               FStarC_Errors_Msg.text
                                 "Its argument has to be concrete: it becomes a constant in the                generated code, and there is nothing else it could become."])
                      | uu___1 ->
                          FStarC_Effect.failwith
                            "Custard: FStar.Float.of_literal applied to the wrong arity"))))
       | "zero" ->
           let s = if id = "zero" then "0" else "1" in
           (match FStarC_Custard_Syntax.float_lit_of_string s with
            | FStar_Pervasives_Native.Some f ->
                FStar_Pervasives_Native.Some
                  (Rule_prim
                     (Prims.int_zero,
                       ((fun uu___ uu___1 ->
                           FStarC_Custard_Syntax.mk
                             (FStarC_Custard_Syntax.EConst
                                (FStarC_Custard_Syntax.CFloat (f, fw)))
                             (FStarC_Custard_Syntax.TFloat fw)
                             FStarC_Custard_Syntax.E_Pure))))
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
       | "one" ->
           let s = if id = "zero" then "0" else "1" in
           (match FStarC_Custard_Syntax.float_lit_of_string s with
            | FStar_Pervasives_Native.Some f ->
                FStar_Pervasives_Native.Some
                  (Rule_prim
                     (Prims.int_zero,
                       ((fun uu___ uu___1 ->
                           FStarC_Custard_Syntax.mk
                             (FStarC_Custard_Syntax.EConst
                                (FStarC_Custard_Syntax.CFloat (f, fw)))
                             (FStarC_Custard_Syntax.TFloat fw)
                             FStarC_Custard_Syntax.E_Pure))))
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
       | "bit_eq" ->
           FStar_Pervasives_Native.Some
             (Rule_extern
                {
                  x_name = FStar_Pervasives_Native.None;
                  x_header = FStar_Pervasives_Native.None
                })
       | "to_string" ->
           FStar_Pervasives_Native.Some
             (Rule_extern
                {
                  x_name = FStar_Pervasives_Native.None;
                  x_header = FStar_Pervasives_Native.None
                })
       | "of_string" ->
           FStar_Pervasives_Native.Some
             (Rule_extern
                {
                  x_name = FStar_Pervasives_Native.None;
                  x_header = FStar_Pervasives_Native.None
                })
       | uu___ -> FStar_Pervasives_Native.None)
let int_cast_rule (id : Prims.string) : rule FStar_Pervasives_Native.option=
  match FStarC_String.split [95] id with
  | src::"to"::dst::[] ->
      let uu___ =
        let uu___1 = machine_int_of_name src in
        let uu___2 = machine_int_of_name dst in (uu___1, uu___2) in
      (match uu___ with
       | (FStar_Pervasives_Native.Some uu___1, FStar_Pervasives_Native.Some
          sw) ->
           FStar_Pervasives_Native.Some
             (Rule_prim
                (Prims.int_one,
                  ((fun uu___2 args ->
                      match args with
                      | a::[] ->
                          FStarC_Custard_Syntax.mk
                            (FStarC_Custard_Syntax.ECast
                               (a, (FStarC_Custard_Syntax.TInt sw)))
                            (FStarC_Custard_Syntax.TInt sw)
                            a.FStarC_Custard_Syntax.eff
                      | uu___3 ->
                          FStarC_Effect.failwith
                            "Custard: integer conversion applied to the wrong arity"))))
       | uu___1 -> FStar_Pervasives_Native.None)
  | uu___ -> FStar_Pervasives_Native.None
let pervasives_rule (id : Prims.string) :
  rule FStar_Pervasives_Native.option=
  match id with
  | "false_elim" ->
      FStar_Pervasives_Native.Some
        (Rule_prim
           (Prims.int_one,
             ((fun uu___ uu___1 ->
                 FStarC_Custard_Syntax.mk
                   (FStarC_Custard_Syntax.EAbort
                      "FStar.Pervasives.false_elim")
                   FStarC_Custard_Syntax.TAny FStarC_Custard_Syntax.E_Impure))))
  | uu___ -> FStar_Pervasives_Native.None
let prims_rule (id : Prims.string) : rule FStar_Pervasives_Native.option=
  let bool_op o arity =
    let po =
      {
        FStarC_Custard_Syntax.po_op = o;
        FStarC_Custard_Syntax.po_ty = FStar_Pervasives_Native.None
      } in
    FStar_Pervasives_Native.Some
      (Rule_prim
         (arity,
           (fun uu___ args ->
              FStarC_Custard_Syntax.mk (FStarC_Custard_Syntax.EOp (po, args))
                (FStarC_Custard_Syntax.TApp (bool_name, []))
                FStarC_Custard_Syntax.E_Pure))) in
  match id with
  | "op_Amp_Amp" -> bool_op FStarC_Custard_Syntax.And (Prims.of_int 2)
  | "op_Bar_Bar" -> bool_op FStarC_Custard_Syntax.Or (Prims.of_int 2)
  | "not" -> bool_op FStarC_Custard_Syntax.Not Prims.int_one
  | "op_Equals" -> bool_op FStarC_Custard_Syntax.Eq (Prims.of_int 2)
  | "op_Less_Greater" -> bool_op FStarC_Custard_Syntax.Neq (Prims.of_int 2)
  | "exn" ->
      FStar_Pervasives_Native.Some
        (Rule_type ((fun uu___ -> FStarC_Custard_Syntax.TExn)))
  | "magic" ->
      FStar_Pervasives_Native.Some
        (Rule_prim
           (Prims.int_one,
             ((fun uu___ uu___1 ->
                 FStarC_Custard_Syntax.mk
                   (FStarC_Custard_Syntax.EAbort (Prims.strcat "Prims." id))
                   FStarC_Custard_Syntax.TAny FStarC_Custard_Syntax.E_Impure))))
  | "admit" ->
      FStar_Pervasives_Native.Some
        (Rule_prim
           (Prims.int_one,
             ((fun uu___ uu___1 ->
                 FStarC_Custard_Syntax.mk
                   (FStarC_Custard_Syntax.EAbort (Prims.strcat "Prims." id))
                   FStarC_Custard_Syntax.TAny FStarC_Custard_Syntax.E_Impure))))
  | uu___ -> FStar_Pervasives_Native.None
let size_lit (n : Prims.int) : FStarC_Custard_Syntax.expr=
  FStarC_Custard_Syntax.mk
    (FStarC_Custard_Syntax.EConst
       (FStarC_Custard_Syntax.CInt
          (n, FStar_IntegerLiteral.Dec,
            (FStar_Pervasives_Native.Some
               (FStarC_Const.Unsigned, FStarC_Custard_Syntax.WSizet)))))
    (FStarC_Custard_Syntax.TInt
       (FStarC_Const.Unsigned, FStarC_Custard_Syntax.WSizet))
    FStarC_Custard_Syntax.E_Pure
let elt_of (tys : FStarC_Custard_Syntax.cty Prims.list) :
  FStarC_Custard_Syntax.cty=
  match tys with | t::uu___ -> t | [] -> FStarC_Custard_Syntax.TAny
let buf_prim (n : Prims.int) (o : FStarC_Custard_Syntax.op)
  (ef : FStarC_Custard_Syntax.eff)
  (ret :
    FStarC_Custard_Syntax.cty Prims.list ->
      FStarC_Custard_Syntax.expr Prims.list -> FStarC_Custard_Syntax.cty)
  (mk_args :
    FStarC_Custard_Syntax.expr Prims.list ->
      FStarC_Custard_Syntax.expr Prims.list)
  : rule=
  Rule_prim
    (n,
      (fun tys args ->
         let uu___ =
           let uu___1 =
             let uu___2 = mk_args args in
             ({
                FStarC_Custard_Syntax.po_op = o;
                FStarC_Custard_Syntax.po_ty = FStar_Pervasives_Native.None
              }, uu___2) in
           FStarC_Custard_Syntax.EOp uu___1 in
         let uu___1 = ret tys args in
         FStarC_Custard_Syntax.mk uu___ uu___1 ef))
let unit_rule (n : Prims.int) : rule=
  Rule_prim (n, (fun uu___ uu___1 -> FStarC_Custard_Syntax.unit_expr))
let identity_rule (n : Prims.int) : rule=
  Rule_prim
    (n,
      (fun uu___ args ->
         match args with
         | a::uu___1 -> a
         | [] -> FStarC_Custard_Syntax.unit_expr))
let describe_shape (x : FStarC_Custard_Syntax.expr) : Prims.string=
  match x.FStarC_Custard_Syntax.e with
  | FStarC_Custard_Syntax.EQual (n, uu___) ->
      let uu___1 = FStarC_Custard_Syntax.string_of_name n in
      Prims.strcat "a reference to " uu___1
  | FStarC_Custard_Syntax.EApp
      ({ FStarC_Custard_Syntax.e = FStarC_Custard_Syntax.EQual (n, uu___);
         FStarC_Custard_Syntax.ty = uu___1;
         FStarC_Custard_Syntax.eff = uu___2;_},
       uu___3)
      ->
      let uu___4 = FStarC_Custard_Syntax.string_of_name n in
      Prims.strcat "an application of " uu___4
  | FStarC_Custard_Syntax.EApp uu___ -> "a function application"
  | FStarC_Custard_Syntax.EVar v -> Prims.strcat "the local variable " v
  | FStarC_Custard_Syntax.EMatch uu___ -> "a match"
  | FStarC_Custard_Syntax.EIf uu___ -> "a conditional"
  | FStarC_Custard_Syntax.ECtor (n, uu___) ->
      let uu___1 =
        let uu___2 = FStarC_Custard_Syntax.string_of_name n in
        Prims.strcat uu___2 " application" in
      Prims.strcat "a " uu___1
  | uu___ -> "not a literal list"
let rec list_literal (x : FStarC_Custard_Syntax.expr) :
  FStarC_Custard_Syntax.expr Prims.list FStar_Pervasives_Native.option=
  match x.FStarC_Custard_Syntax.e with
  | FStarC_Custard_Syntax.ECoerce (e1, uu___) -> list_literal e1
  | FStarC_Custard_Syntax.ECtor (n, []) when
      n.FStarC_Custard_Syntax.id = "Nil" -> FStar_Pervasives_Native.Some []
  | FStarC_Custard_Syntax.ECtor (n, hd::tl::[]) when
      n.FStarC_Custard_Syntax.id = "Cons" ->
      let uu___ = list_literal tl in
      (match uu___ with
       | FStar_Pervasives_Native.Some rest ->
           FStar_Pervasives_Native.Some (hd :: rest)
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
  | uu___ -> FStar_Pervasives_Native.None
let comment_text (which : Prims.string) (role : Prims.string)
  (x : FStarC_Custard_Syntax.expr) : Prims.string=
  let what =
    Prims.strcat "Pulse.Lib.Comment."
      (Prims.strcat which
         (if role = ""
          then ""
          else Prims.strcat "'s " (Prims.strcat role " argument"))) in
  match x.FStarC_Custard_Syntax.e with
  | FStarC_Custard_Syntax.EConst (FStarC_Custard_Syntax.CString s) ->
      if FStarC_Util.contains s "*/"
      then
        FStarC_Errors.raise_error0
          FStarC_Errors_Codes.Error_CustardBadComment ()
          (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
          (Obj.magic
             [FStarC_Errors_Msg.text
                (Prims.strcat "Custard: the text given to "
                   (Prims.strcat what
                      " contains */, which would end the comment it is emitted into."));
             FStarC_Errors_Msg.text (Prims.strcat "The text is: " s)])
      else s
  | uu___ ->
      let uu___1 =
        let uu___2 =
          let uu___3 =
            let uu___4 =
              let uu___5 =
                let uu___6 =
                  let uu___7 = describe_shape x in Prims.strcat uu___7 "." in
                Prims.strcat
                  " has to be a string literal, and after reduction this one is "
                  uu___6 in
              Prims.strcat what uu___5 in
            Prims.strcat "Custard: " uu___4 in
          FStarC_Errors_Msg.text uu___3 in
        [uu___2;
        FStarC_Errors_Msg.text
          "It becomes a comment in the generated code, so there is nowhere to evaluate it."] in
      FStarC_Errors.raise_error0 FStarC_Errors_Codes.Error_CustardBadComment
        () (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
        (Obj.magic uu___1)
let pulse_rule (ns : Prims.string Prims.list) (id : Prims.string) :
  rule FStar_Pervasives_Native.option=
  let buf tys uu___ = FStarC_Custard_Syntax.TBuf (elt_of tys) in
  let rf tys uu___ = FStarC_Custard_Syntax.TRef (elt_of tys) in
  let unit_ty uu___ uu___1 = FStarC_Custard_Syntax.TUnit in
  let bool_ty uu___ uu___1 = FStarC_Custard_Syntax.TApp (bool_name, []) in
  let elt_of_arg uu___ args =
    match args with
    | { FStarC_Custard_Syntax.e = uu___1;
        FStarC_Custard_Syntax.ty = FStarC_Custard_Syntax.TBuf t;
        FStarC_Custard_Syntax.eff = uu___2;_}::uu___3 -> t
    | { FStarC_Custard_Syntax.e = uu___1;
        FStarC_Custard_Syntax.ty = FStarC_Custard_Syntax.TRef t;
        FStarC_Custard_Syntax.eff = uu___2;_}::uu___3 -> t
    | uu___1 -> FStarC_Custard_Syntax.TAny in
  let as_buf uu___ args =
    match args with
    | { FStarC_Custard_Syntax.e = uu___1;
        FStarC_Custard_Syntax.ty = FStarC_Custard_Syntax.TRef t;
        FStarC_Custard_Syntax.eff = uu___2;_}::uu___3 ->
        FStarC_Custard_Syntax.TBuf t
    | a::uu___1 -> a.FStarC_Custard_Syntax.ty
    | uu___1 -> FStarC_Custard_Syntax.TAny in
  let self uu___ args =
    match args with
    | a::uu___1 -> a.FStarC_Custard_Syntax.ty
    | uu___1 -> FStarC_Custard_Syntax.TAny in
  match (ns, id) with
  | ("Pulse"::"Lib"::"Vec"::[], "vec") ->
      FStar_Pervasives_Native.Some
        (Rule_type ((fun tys -> FStarC_Custard_Syntax.TBuf (elt_of tys))))
  | ("Pulse"::"Lib"::"Array"::"Core"::[], "array") ->
      FStar_Pervasives_Native.Some
        (Rule_type ((fun tys -> FStarC_Custard_Syntax.TBuf (elt_of tys))))
  | ("Pulse"::"Lib"::"ArrayPtr"::[], "ptr") ->
      FStar_Pervasives_Native.Some
        (Rule_type ((fun tys -> FStarC_Custard_Syntax.TBuf (elt_of tys))))
  | ("Pulse"::"Lib"::"Reference"::[], "ref") ->
      FStar_Pervasives_Native.Some
        (Rule_type ((fun tys -> FStarC_Custard_Syntax.TRef (elt_of tys))))
  | ("Pulse"::"Lib"::"Box"::[], "box") ->
      FStar_Pervasives_Native.Some
        (Rule_type ((fun tys -> FStarC_Custard_Syntax.TRef (elt_of tys))))
  | ("Pulse"::"Lib"::"Reference"::[], "alloc") ->
      FStar_Pervasives_Native.Some
        (buf_prim Prims.int_one
           (FStarC_Custard_Syntax.BufCreate FStarC_Custard_Syntax.LStack)
           FStarC_Custard_Syntax.E_Impure rf
           (fun args -> FStarC_List.op_At args [size_lit Prims.int_one]))
  | ("Pulse"::"Lib"::"Reference"::[], "alloc_uninit") ->
      FStar_Pervasives_Native.Some
        (Rule_prim
           (Prims.int_one,
             ((fun tys uu___ ->
                 let t = elt_of tys in
                 FStarC_Custard_Syntax.mk
                   (FStarC_Custard_Syntax.EOp
                      ({
                         FStarC_Custard_Syntax.po_op =
                           (FStarC_Custard_Syntax.BufCreate
                              FStarC_Custard_Syntax.LStack);
                         FStarC_Custard_Syntax.po_ty =
                           FStar_Pervasives_Native.None
                       },
                        [FStarC_Custard_Syntax.mk FStarC_Custard_Syntax.EAny
                           t FStarC_Custard_Syntax.E_Pure;
                        size_lit Prims.int_one]))
                   (FStarC_Custard_Syntax.TRef t)
                   FStarC_Custard_Syntax.E_Impure))))
  | ("Pulse"::"Lib"::"Reference"::[], "free") ->
      FStar_Pervasives_Native.Some (unit_rule Prims.int_one)
  | ("Pulse"::"Lib"::"Reference"::[], "read") ->
      FStar_Pervasives_Native.Some
        (buf_prim Prims.int_one FStarC_Custard_Syntax.BufRead
           FStarC_Custard_Syntax.E_Impure elt_of_arg
           (fun args -> FStarC_List.op_At args [size_lit Prims.int_zero]))
  | ("Pulse"::"Lib"::"Reference"::[], "op_Bang") ->
      FStar_Pervasives_Native.Some
        (buf_prim Prims.int_one FStarC_Custard_Syntax.BufRead
           FStarC_Custard_Syntax.E_Impure elt_of_arg
           (fun args -> FStarC_List.op_At args [size_lit Prims.int_zero]))
  | ("Pulse"::"Lib"::"Reference"::[], "write") ->
      FStar_Pervasives_Native.Some
        (buf_prim (Prims.of_int 2) FStarC_Custard_Syntax.BufWrite
           FStarC_Custard_Syntax.E_Impure unit_ty
           (fun args ->
              match args with
              | r::v::[] -> [r; size_lit Prims.int_zero; v]
              | args1 -> args1))
  | ("Pulse"::"Lib"::"Reference"::[], "op_Colon_Equals") ->
      FStar_Pervasives_Native.Some
        (buf_prim (Prims.of_int 2) FStarC_Custard_Syntax.BufWrite
           FStarC_Custard_Syntax.E_Impure unit_ty
           (fun args ->
              match args with
              | r::v::[] -> [r; size_lit Prims.int_zero; v]
              | args1 -> args1))
  | ("Pulse"::"Lib"::"Reference"::[], "to_array_mask") ->
      FStar_Pervasives_Native.Some
        (buf_prim Prims.int_one FStarC_Custard_Syntax.BufSub
           FStarC_Custard_Syntax.E_Pure as_buf
           (fun args -> FStarC_List.op_At args [size_lit Prims.int_zero]))
  | ("Pulse"::"Lib"::"Reference"::[], "array_at") ->
      FStar_Pervasives_Native.Some
        (buf_prim (Prims.of_int 2) FStarC_Custard_Syntax.BufSub
           FStarC_Custard_Syntax.E_Pure as_buf (fun args -> args))
  | ("Pulse"::"Lib"::"Reference"::[], "array_at_uninit") ->
      FStar_Pervasives_Native.Some
        (buf_prim (Prims.of_int 2) FStarC_Custard_Syntax.BufSub
           FStarC_Custard_Syntax.E_Pure as_buf (fun args -> args))
  | ("Pulse"::"Lib"::"Box"::[], "alloc") ->
      FStar_Pervasives_Native.Some
        (buf_prim Prims.int_one
           (FStarC_Custard_Syntax.BufCreate FStarC_Custard_Syntax.LHeap)
           FStarC_Custard_Syntax.E_Impure rf
           (fun args -> FStarC_List.op_At args [size_lit Prims.int_one]))
  | ("Pulse"::"Lib"::"Box"::[], "free") ->
      FStar_Pervasives_Native.Some
        (buf_prim Prims.int_one FStarC_Custard_Syntax.BufFree
           FStarC_Custard_Syntax.E_Impure unit_ty (fun args -> args))
  | ("Pulse"::"Lib"::"Box"::[], "op_Bang") ->
      FStar_Pervasives_Native.Some
        (buf_prim Prims.int_one FStarC_Custard_Syntax.BufRead
           FStarC_Custard_Syntax.E_Impure elt_of_arg
           (fun args -> FStarC_List.op_At args [size_lit Prims.int_zero]))
  | ("Pulse"::"Lib"::"Box"::[], "op_Colon_Equals") ->
      FStar_Pervasives_Native.Some
        (buf_prim (Prims.of_int 2) FStarC_Custard_Syntax.BufWrite
           FStarC_Custard_Syntax.E_Impure unit_ty
           (fun args ->
              match args with
              | r::v::[] -> [r; size_lit Prims.int_zero; v]
              | args1 -> args1))
  | ("Pulse"::"Lib"::"Box"::[], "box_to_ref") ->
      FStar_Pervasives_Native.Some (identity_rule Prims.int_one)
  | ("Pulse"::"Lib"::"Vec"::[], "alloc") ->
      FStar_Pervasives_Native.Some
        (buf_prim (Prims.of_int 2)
           (FStarC_Custard_Syntax.BufCreate FStarC_Custard_Syntax.LHeap)
           FStarC_Custard_Syntax.E_Impure buf (fun args -> args))
  | ("Pulse"::"Lib"::"Vec"::[], "free") ->
      FStar_Pervasives_Native.Some
        (buf_prim Prims.int_one FStarC_Custard_Syntax.BufFree
           FStarC_Custard_Syntax.E_Impure unit_ty (fun args -> args))
  | ("Pulse"::"Lib"::"Vec"::[], "op_Dot_Lparen_Rparen") ->
      FStar_Pervasives_Native.Some
        (buf_prim (Prims.of_int 2) FStarC_Custard_Syntax.BufRead
           FStarC_Custard_Syntax.E_Impure elt_of_arg (fun args -> args))
  | ("Pulse"::"Lib"::"Vec"::[], "op_Dot_Lparen_Rparen_Less_Minus") ->
      FStar_Pervasives_Native.Some
        (buf_prim (Prims.of_int 3) FStarC_Custard_Syntax.BufWrite
           FStarC_Custard_Syntax.E_Impure unit_ty (fun args -> args))
  | ("Pulse"::"Lib"::"Vec"::[], "vec_to_array") ->
      FStar_Pervasives_Native.Some (identity_rule Prims.int_one)
  | ("Pulse"::"Lib"::"Array"::"PtsTo"::[], "alloc") ->
      FStar_Pervasives_Native.Some
        (buf_prim (Prims.of_int 2)
           (FStarC_Custard_Syntax.BufCreate FStarC_Custard_Syntax.LStack)
           FStarC_Custard_Syntax.E_Impure buf (fun args -> args))
  | ("Pulse"::"Lib"::"Array"::"Core"::[], "mask_alloc") ->
      FStar_Pervasives_Native.Some
        (Rule_prim
           (Prims.int_one,
             ((fun tys args ->
                 let t = elt_of tys in
                 let n =
                   match args with
                   | a::uu___ -> a
                   | [] -> size_lit Prims.int_zero in
                 FStarC_Custard_Syntax.mk
                   (FStarC_Custard_Syntax.EOp
                      ({
                         FStarC_Custard_Syntax.po_op =
                           (FStarC_Custard_Syntax.BufCreate
                              FStarC_Custard_Syntax.LStack);
                         FStarC_Custard_Syntax.po_ty =
                           FStar_Pervasives_Native.None
                       },
                        [FStarC_Custard_Syntax.mk FStarC_Custard_Syntax.EAny
                           t FStarC_Custard_Syntax.E_Pure;
                        n])) (FStarC_Custard_Syntax.TBuf t)
                   FStarC_Custard_Syntax.E_Impure))))
  | ("Pulse"::"Lib"::"Array"::"Core"::[], "mask_alloc_with_vis") ->
      FStar_Pervasives_Native.Some
        (Rule_prim
           (Prims.int_one,
             ((fun tys args ->
                 let t = elt_of tys in
                 let n =
                   match args with
                   | a::uu___ -> a
                   | [] -> size_lit Prims.int_zero in
                 FStarC_Custard_Syntax.mk
                   (FStarC_Custard_Syntax.EOp
                      ({
                         FStarC_Custard_Syntax.po_op =
                           (FStarC_Custard_Syntax.BufCreate
                              FStarC_Custard_Syntax.LStack);
                         FStarC_Custard_Syntax.po_ty =
                           FStar_Pervasives_Native.None
                       },
                        [FStarC_Custard_Syntax.mk FStarC_Custard_Syntax.EAny
                           t FStarC_Custard_Syntax.E_Pure;
                        n])) (FStarC_Custard_Syntax.TBuf t)
                   FStarC_Custard_Syntax.E_Impure))))
  | ("Pulse"::"Lib"::"Array"::"Core"::[], "mask_free") ->
      FStar_Pervasives_Native.Some (unit_rule Prims.int_one)
  | ("Pulse"::"Lib"::"Array"::"Core"::[], "mask_read") ->
      FStar_Pervasives_Native.Some
        (buf_prim (Prims.of_int 2) FStarC_Custard_Syntax.BufRead
           FStarC_Custard_Syntax.E_Impure elt_of_arg (fun args -> args))
  | ("Pulse"::"Lib"::"Array"::"Core"::[], "mask_write") ->
      FStar_Pervasives_Native.Some
        (buf_prim (Prims.of_int 3) FStarC_Custard_Syntax.BufWrite
           FStarC_Custard_Syntax.E_Impure unit_ty (fun args -> args))
  | ("Pulse"::"Lib"::"Array"::"Core"::[], "sub") ->
      FStar_Pervasives_Native.Some
        (buf_prim (Prims.of_int 2) FStarC_Custard_Syntax.BufSub
           FStarC_Custard_Syntax.E_Pure self (fun args -> args))
  | ("Pulse"::"Lib"::"ArrayPtr"::[], "op_Dot_Lparen_Rparen") ->
      FStar_Pervasives_Native.Some
        (buf_prim (Prims.of_int 2) FStarC_Custard_Syntax.BufRead
           FStarC_Custard_Syntax.E_Impure elt_of_arg (fun args -> args))
  | ("Pulse"::"Lib"::"ArrayPtr"::[], "op_Dot_Lparen_Rparen_Less_Minus") ->
      FStar_Pervasives_Native.Some
        (buf_prim (Prims.of_int 3) FStarC_Custard_Syntax.BufWrite
           FStarC_Custard_Syntax.E_Impure unit_ty (fun args -> args))
  | ("Pulse"::"Lib"::"ArrayPtr"::[], "split") ->
      FStar_Pervasives_Native.Some
        (buf_prim (Prims.of_int 2) FStarC_Custard_Syntax.BufSub
           FStarC_Custard_Syntax.E_Pure self (fun args -> args))
  | ("Pulse"::"Lib"::"ArrayPtr"::[], "as_ref") ->
      FStar_Pervasives_Native.Some (identity_rule Prims.int_one)
  | ("Pulse"::"Lib"::"ArrayPtr"::[], "from_ref") ->
      FStar_Pervasives_Native.Some (identity_rule Prims.int_one)
  | ("Pulse"::"Lib"::"ArrayPtr"::[], "from_array") ->
      FStar_Pervasives_Native.Some (identity_rule Prims.int_one)
  | ("Pulse"::"Lib"::"ArrayPtr"::[], "memcpy") ->
      FStar_Pervasives_Native.Some
        (buf_prim (Prims.of_int 5) FStarC_Custard_Syntax.BufBlit
           FStarC_Custard_Syntax.E_Impure unit_ty (fun args -> args))
  | ("Pulse"::"Lib"::"GlobalArray"::[], "static_array") ->
      FStar_Pervasives_Native.Some
        (Rule_type ((fun tys -> FStarC_Custard_Syntax.TBuf (elt_of tys))))
  | ("Pulse"::"Lib"::"GlobalArray"::[], "mk_static_array") ->
      FStar_Pervasives_Native.Some
        (Rule_prim
           (Prims.int_one,
             ((fun tys args ->
                 let t = elt_of tys in
                 match args with
                 | l::[] ->
                     let uu___ = list_literal l in
                     (match uu___ with
                      | FStar_Pervasives_Native.Some elems ->
                          FStarC_Custard_Syntax.mk
                            (FStarC_Custard_Syntax.EOp
                               ({
                                  FStarC_Custard_Syntax.po_op =
                                    FStarC_Custard_Syntax.BufLit;
                                  FStarC_Custard_Syntax.po_ty =
                                    FStar_Pervasives_Native.None
                                }, elems)) (FStarC_Custard_Syntax.TBuf t)
                            FStarC_Custard_Syntax.E_Pure
                      | FStar_Pervasives_Native.None ->
                          let uu___1 =
                            let uu___2 =
                              let uu___3 =
                                let uu___4 =
                                  let uu___5 = describe_shape l in
                                  Prims.strcat uu___5 "." in
                                Prims.strcat
                                  "Custard: the elements of a Pulse.Lib.GlobalArray.static_array have to be known at compile time, and these are not: after reduction the argument is "
                                  uu___4 in
                              FStarC_Errors_Msg.text uu___3 in
                            [uu___2;
                            FStarC_Errors_Msg.text
                              "The whole point of the type is that the run is baked into the program image, so there is nowhere to evaluate this: the argument of mk_static_array has to reduce to a literal list.";
                            FStarC_Errors_Msg.text
                              "If the contents really are computed, allocate a Pulse.Lib.Vec or a Pulse.Lib.Array and fill it instead.  If they are constant but Custard could not see it, the norm budget may have run out: try raising --custard_norm_budget."] in
                          FStarC_Errors.raise_error0
                            FStarC_Errors_Codes.Error_CustardBadStaticArray
                            ()
                            (Obj.magic
                               FStarC_Errors_Msg.is_error_message_list_doc)
                            (Obj.magic uu___1))
                 | uu___ ->
                     FStarC_Effect.failwith
                       "Custard: mk_static_array applied to the wrong number of arguments"))))
  | ("Pulse"::"Lib"::"GlobalArray"::[], "array_of_static_array") ->
      FStar_Pervasives_Native.Some
        (buf_prim Prims.int_one FStarC_Custard_Syntax.BufUnconst
           FStarC_Custard_Syntax.E_Pure self (fun args -> args))
  | ("Pulse"::"Lib"::"Reference"::[], "null") ->
      FStar_Pervasives_Native.Some
        (Rule_prim
           (Prims.int_zero,
             ((fun tys uu___ ->
                 FStarC_Custard_Syntax.mk
                   (FStarC_Custard_Syntax.EOp
                      ({
                         FStarC_Custard_Syntax.po_op =
                           FStarC_Custard_Syntax.BufNull;
                         FStarC_Custard_Syntax.po_ty =
                           FStar_Pervasives_Native.None
                       }, [])) (FStarC_Custard_Syntax.TRef (elt_of tys))
                   FStarC_Custard_Syntax.E_Pure))))
  | ("Pulse"::"Lib"::"Box"::[], "null") ->
      FStar_Pervasives_Native.Some
        (Rule_prim
           (Prims.int_zero,
             ((fun tys uu___ ->
                 FStarC_Custard_Syntax.mk
                   (FStarC_Custard_Syntax.EOp
                      ({
                         FStarC_Custard_Syntax.po_op =
                           FStarC_Custard_Syntax.BufNull;
                         FStarC_Custard_Syntax.po_ty =
                           FStar_Pervasives_Native.None
                       }, [])) (FStarC_Custard_Syntax.TRef (elt_of tys))
                   FStarC_Custard_Syntax.E_Pure))))
  | ("Pulse"::"Lib"::"Array"::"Core"::[], "null") ->
      FStar_Pervasives_Native.Some
        (Rule_prim
           (Prims.int_zero,
             ((fun tys uu___ ->
                 FStarC_Custard_Syntax.mk
                   (FStarC_Custard_Syntax.EOp
                      ({
                         FStarC_Custard_Syntax.po_op =
                           FStarC_Custard_Syntax.BufNull;
                         FStarC_Custard_Syntax.po_ty =
                           FStar_Pervasives_Native.None
                       }, [])) (FStarC_Custard_Syntax.TBuf (elt_of tys))
                   FStarC_Custard_Syntax.E_Pure))))
  | ("Pulse"::"Lib"::"ArrayPtr"::[], "null") ->
      FStar_Pervasives_Native.Some
        (Rule_prim
           (Prims.int_zero,
             ((fun tys uu___ ->
                 FStarC_Custard_Syntax.mk
                   (FStarC_Custard_Syntax.EOp
                      ({
                         FStarC_Custard_Syntax.po_op =
                           FStarC_Custard_Syntax.BufNull;
                         FStarC_Custard_Syntax.po_ty =
                           FStar_Pervasives_Native.None
                       }, [])) (FStarC_Custard_Syntax.TBuf (elt_of tys))
                   FStarC_Custard_Syntax.E_Pure))))
  | ("Pulse"::"Lib"::"Reference"::[], "is_null") ->
      FStar_Pervasives_Native.Some
        (buf_prim Prims.int_one FStarC_Custard_Syntax.BufIsNull
           FStarC_Custard_Syntax.E_Pure bool_ty (fun args -> args))
  | ("Pulse"::"Lib"::"Box"::[], "is_null") ->
      FStar_Pervasives_Native.Some
        (buf_prim Prims.int_one FStarC_Custard_Syntax.BufIsNull
           FStarC_Custard_Syntax.E_Pure bool_ty (fun args -> args))
  | ("Pulse"::"Lib"::"Array"::"Core"::[], "is_null") ->
      FStar_Pervasives_Native.Some
        (buf_prim Prims.int_one FStarC_Custard_Syntax.BufIsNull
           FStarC_Custard_Syntax.E_Pure bool_ty (fun args -> args))
  | ("Pulse"::"Lib"::"ArrayPtr"::[], "is_null") ->
      FStar_Pervasives_Native.Some
        (buf_prim Prims.int_one FStarC_Custard_Syntax.BufIsNull
           FStarC_Custard_Syntax.E_Pure bool_ty (fun args -> args))
  | ("Pulse"::"Lib"::"Dv"::[], "while_") ->
      FStar_Pervasives_Native.Some
        (Rule_prim
           ((Prims.of_int 2),
             ((fun uu___ args ->
                 match args with
                 | {
                     FStarC_Custard_Syntax.e = FStarC_Custard_Syntax.EFun
                       (uu___1, cond);
                     FStarC_Custard_Syntax.ty = uu___2;
                     FStarC_Custard_Syntax.eff = uu___3;_}::{
                                                              FStarC_Custard_Syntax.e
                                                                =
                                                                FStarC_Custard_Syntax.EFun
                                                                (uu___4,
                                                                 body);
                                                              FStarC_Custard_Syntax.ty
                                                                = uu___5;
                                                              FStarC_Custard_Syntax.eff
                                                                = uu___6;_}::[]
                     ->
                     FStarC_Custard_Syntax.mk
                       (FStarC_Custard_Syntax.EWhile (cond, body))
                       FStarC_Custard_Syntax.TUnit
                       FStarC_Custard_Syntax.E_Impure
                 | uu___1 ->
                     FStarC_Effect.failwith
                       "Custard: Pulse.Lib.Dv.while_ applied to something other than two thunks"))))
  | ("Pulse"::"Lib"::"Dv"::[], "unreachable") ->
      FStar_Pervasives_Native.Some
        (Rule_prim
           (Prims.int_one,
             ((fun uu___ uu___1 ->
                 FStarC_Custard_Syntax.mk
                   (FStarC_Custard_Syntax.EAbort "Pulse.Lib.Dv.unreachable")
                   FStarC_Custard_Syntax.TAny FStarC_Custard_Syntax.E_Impure))))
  | ("Pulse"::"Lib"::"GlobalVar"::[], "gvar") ->
      FStar_Pervasives_Native.Some (Rule_type ((fun tys -> elt_of tys)))
  | ("Pulse"::"Lib"::"GlobalVar"::[], "mk_gvar") ->
      FStar_Pervasives_Native.Some
        (Rule_prim
           (Prims.int_one,
             ((fun tys args ->
                 match args with
                 | init::uu___ ->
                     let ret =
                       match init.FStarC_Custard_Syntax.ty with
                       | FStarC_Custard_Syntax.TArrow (uu___1, uu___2, r) ->
                           r
                       | uu___1 -> elt_of tys in
                     FStarC_Custard_Syntax.mk
                       (FStarC_Custard_Syntax.EApp
                          (init, [FStarC_Custard_Syntax.unit_expr])) ret
                       FStarC_Custard_Syntax.E_Impure
                 | [] -> FStarC_Custard_Syntax.unit_expr))))
  | ("Pulse"::"Lib"::"GlobalVar"::[], "read_gvar") ->
      FStar_Pervasives_Native.Some (identity_rule Prims.int_one)
  | ("Pulse"::"Lib"::"Comment"::[], "comment_gen") ->
      FStar_Pervasives_Native.Some
        (Rule_prim
           ((Prims.of_int 3),
             ((fun uu___ args ->
                 match args with
                 | before::body::after::[] ->
                     let b = comment_text "comment_gen" "before" before in
                     let a = comment_text "comment_gen" "after" after in
                     FStarC_Custard_Syntax.mk
                       (FStarC_Custard_Syntax.EOp
                          ({
                             FStarC_Custard_Syntax.po_op =
                               (FStarC_Custard_Syntax.Commented (b, a));
                             FStarC_Custard_Syntax.po_ty =
                               FStar_Pervasives_Native.None
                           }, [body])) body.FStarC_Custard_Syntax.ty
                       body.FStarC_Custard_Syntax.eff
                 | uu___1 ->
                     FStarC_Effect.failwith
                       "Custard: Pulse.Lib.Comment.comment_gen applied to other than three arguments"))))
  | ("Pulse"::"Lib"::"Comment"::[], "comment") ->
      FStar_Pervasives_Native.Some
        (Rule_prim
           (Prims.int_one,
             ((fun uu___ args ->
                 match args with
                 | s::[] ->
                     let t = comment_text "comment" "" s in
                     FStarC_Custard_Syntax.mk
                       (FStarC_Custard_Syntax.EOp
                          ({
                             FStarC_Custard_Syntax.po_op =
                               (FStarC_Custard_Syntax.Commented (t, ""));
                             FStarC_Custard_Syntax.po_ty =
                               FStar_Pervasives_Native.None
                           }, [FStarC_Custard_Syntax.unit_expr]))
                       FStarC_Custard_Syntax.TUnit
                       FStarC_Custard_Syntax.E_Impure
                 | uu___1 ->
                     FStarC_Effect.failwith
                       "Custard: Pulse.Lib.Comment.comment applied to other than one argument"))))
  | uu___ -> FStar_Pervasives_Native.None
let exn_var : Prims.string= "_cexn"
let exn_rule (id : Prims.string) : rule FStar_Pervasives_Native.option=
  let force f =
    match f.FStarC_Custard_Syntax.e with
    | FStarC_Custard_Syntax.EFun (b::[], body) ->
        FStarC_Custard_Syntax.mk
          (FStarC_Custard_Syntax.ELet
             ((b.FStarC_Custard_Syntax.b_name), FStarC_Custard_Syntax.TUnit,
               FStarC_Custard_Syntax.unit_expr, body))
          body.FStarC_Custard_Syntax.ty body.FStarC_Custard_Syntax.eff
    | uu___ ->
        FStarC_Custard_Syntax.mk
          (FStarC_Custard_Syntax.EApp (f, [FStarC_Custard_Syntax.unit_expr]))
          FStarC_Custard_Syntax.TAny FStarC_Custard_Syntax.E_Impure in
  match id with
  | "raise" ->
      FStar_Pervasives_Native.Some
        (Rule_prim
           (Prims.int_one,
             ((fun uu___ args ->
                 match args with
                 | e::[] ->
                     FStarC_Custard_Syntax.mk
                       (FStarC_Custard_Syntax.ERaise e)
                       FStarC_Custard_Syntax.TAny
                       FStarC_Custard_Syntax.E_Impure
                 | uu___1 ->
                     FStarC_Effect.failwith
                       "Custard: raise applied to the wrong number of arguments"))))
  | "try_with" ->
      FStar_Pervasives_Native.Some
        (Rule_prim
           ((Prims.of_int 2),
             ((fun uu___ args ->
                 match args with
                 | f::h::[] ->
                     let body = force f in
                     let x =
                       FStarC_Custard_Syntax.mk
                         (FStarC_Custard_Syntax.EVar exn_var)
                         FStarC_Custard_Syntax.TExn
                         FStarC_Custard_Syntax.E_Pure in
                     FStarC_Custard_Syntax.mk
                       (FStarC_Custard_Syntax.ETry
                          (body,
                            [((FStarC_Custard_Syntax.PVar exn_var),
                               FStar_Pervasives_Native.None,
                               (FStarC_Custard_Syntax.mk
                                  (FStarC_Custard_Syntax.EApp (h, [x]))
                                  body.FStarC_Custard_Syntax.ty
                                  FStarC_Custard_Syntax.E_Impure))]))
                       body.FStarC_Custard_Syntax.ty
                       FStarC_Custard_Syntax.E_Impure
                 | uu___1 ->
                     FStarC_Effect.failwith
                       "Custard: try_with applied to the wrong number of arguments"))))
  | "failwith" ->
      FStar_Pervasives_Native.Some
        (Rule_extern
           {
             x_name = FStar_Pervasives_Native.None;
             x_header = FStar_Pervasives_Native.None
           })
  | "exit" ->
      FStar_Pervasives_Native.Some
        (Rule_extern
           {
             x_name = FStar_Pervasives_Native.None;
             x_header = FStar_Pervasives_Native.None
           })
  | uu___ -> FStar_Pervasives_Native.None
let ref_rule (id : Prims.string) : rule FStar_Pervasives_Native.option=
  let rf tys uu___ = FStarC_Custard_Syntax.TRef (elt_of tys) in
  let unit_ty uu___ uu___1 = FStarC_Custard_Syntax.TUnit in
  let elt_of_arg uu___ args =
    match args with
    | { FStarC_Custard_Syntax.e = uu___1;
        FStarC_Custard_Syntax.ty = FStarC_Custard_Syntax.TRef t;
        FStarC_Custard_Syntax.eff = uu___2;_}::uu___3 -> t
    | { FStarC_Custard_Syntax.e = uu___1;
        FStarC_Custard_Syntax.ty = FStarC_Custard_Syntax.TBuf t;
        FStarC_Custard_Syntax.eff = uu___2;_}::uu___3 -> t
    | uu___1 -> FStarC_Custard_Syntax.TAny in
  match id with
  | "ref" ->
      FStar_Pervasives_Native.Some
        (Rule_type ((fun tys -> FStarC_Custard_Syntax.TRef (elt_of tys))))
  | "alloc" ->
      FStar_Pervasives_Native.Some
        (buf_prim Prims.int_one
           (FStarC_Custard_Syntax.BufCreate FStarC_Custard_Syntax.LHeap)
           FStarC_Custard_Syntax.E_Impure rf
           (fun args -> FStarC_List.op_At args [size_lit Prims.int_one]))
  | "mk_ref" ->
      FStar_Pervasives_Native.Some
        (buf_prim Prims.int_one
           (FStarC_Custard_Syntax.BufCreate FStarC_Custard_Syntax.LHeap)
           FStarC_Custard_Syntax.E_Impure rf
           (fun args -> FStarC_List.op_At args [size_lit Prims.int_one]))
  | "read" ->
      FStar_Pervasives_Native.Some
        (buf_prim Prims.int_one FStarC_Custard_Syntax.BufRead
           FStarC_Custard_Syntax.E_Impure elt_of_arg
           (fun args -> FStarC_List.op_At args [size_lit Prims.int_zero]))
  | "op_Bang" ->
      FStar_Pervasives_Native.Some
        (buf_prim Prims.int_one FStarC_Custard_Syntax.BufRead
           FStarC_Custard_Syntax.E_Impure elt_of_arg
           (fun args -> FStarC_List.op_At args [size_lit Prims.int_zero]))
  | "write" ->
      FStar_Pervasives_Native.Some
        (buf_prim (Prims.of_int 2) FStarC_Custard_Syntax.BufWrite
           FStarC_Custard_Syntax.E_Impure unit_ty
           (fun args ->
              match args with
              | r::v::[] -> [r; size_lit Prims.int_zero; v]
              | args1 -> args1))
  | "op_Colon_Equals" ->
      FStar_Pervasives_Native.Some
        (buf_prim (Prims.of_int 2) FStarC_Custard_Syntax.BufWrite
           FStarC_Custard_Syntax.E_Impure unit_ty
           (fun args ->
              match args with
              | r::v::[] -> [r; size_lit Prims.int_zero; v]
              | args1 -> args1))
  | uu___ -> FStar_Pervasives_Native.None
let string_arg (t : FStarC_Syntax_Syntax.term) :
  Prims.string FStar_Pervasives_Native.option=
  let uu___ =
    let uu___1 = FStarC_Syntax_Subst.compress t in
    uu___1.FStarC_Syntax_Syntax.n in
  match uu___ with
  | FStarC_Syntax_Syntax.Tm_constant (FStarC_Const.Const_string (s, uu___1))
      -> FStar_Pervasives_Native.Some s
  | uu___1 -> FStar_Pervasives_Native.None
let attribute_string (attrs : FStarC_Syntax_Syntax.term Prims.list)
  (a : FStarC_Ident.lident) : Prims.string FStar_Pervasives_Native.option=
  let uu___ = FStarC_Syntax_Util.get_attribute a attrs in
  match uu___ with
  | FStar_Pervasives_Native.Some ((arg, uu___1)::uu___2) -> string_arg arg
  | uu___1 -> FStar_Pervasives_Native.None
let fwidth_of_attributes (attrs : FStarC_Syntax_Syntax.term Prims.list) :
  FStarC_Custard_Syntax.fwidth FStar_Pervasives_Native.option=
  let uu___ =
    FStarC_Syntax_Util.has_attribute attrs
      FStarC_Parser_Const.custard_bfloat16_attr in
  if uu___
  then FStar_Pervasives_Native.Some FStarC_Custard_Syntax.BFloat16
  else
    (let uu___1 =
       FStarC_Syntax_Util.get_attribute
         FStarC_Parser_Const.custard_float_attr attrs in
     match uu___1 with
     | FStar_Pervasives_Native.Some ((arg, uu___2)::uu___3) ->
         let uu___4 =
           let uu___5 = FStarC_Syntax_Subst.compress arg in
           uu___5.FStarC_Syntax_Syntax.n in
         (match uu___4 with
          | FStarC_Syntax_Syntax.Tm_constant (FStarC_Const.Const_int
              (uu___5, uu___6)) when uu___5 = (Prims.of_int 16) ->
              FStar_Pervasives_Native.Some FStarC_Custard_Syntax.Float16
          | FStarC_Syntax_Syntax.Tm_constant (FStarC_Const.Const_int
              (uu___5, uu___6)) when uu___5 = (Prims.of_int 32) ->
              FStar_Pervasives_Native.Some FStarC_Custard_Syntax.Float32
          | FStarC_Syntax_Syntax.Tm_constant (FStarC_Const.Const_int
              (uu___5, uu___6)) when uu___5 = (Prims.of_int 64) ->
              FStar_Pervasives_Native.Some FStarC_Custard_Syntax.Float64
          | FStarC_Syntax_Syntax.Tm_constant (FStarC_Const.Const_int
              (n, uu___5)) ->
              FStarC_Errors.raise_error0
                FStarC_Errors_Codes.Error_CustardBadFloatWidth ()
                (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
                (Obj.magic
                   [FStarC_Errors_Msg.text
                      (Prims.strcat "Custard: [@@custard_float "
                         (Prims.strcat (Prims.string_of_int n)
                            "] is not a floating-point width Custard implements."));
                   FStarC_Errors_Msg.text
                     "The accepted widths are 16, 32 and 64, which are IEEE-754                  binary16, binary32 and binary64.  bfloat16 is not an IEEE-754                  format and is [@@custard_bfloat16] rather than a width."])
          | uu___5 ->
              FStarC_Errors.raise_error0
                FStarC_Errors_Codes.Error_CustardBadFloatWidth ()
                (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
                (Obj.magic
                   [FStarC_Errors_Msg.text
                      "Custard: the argument of [@@custard_float] must be an integer                  literal, 16, 32 or 64."]))
     | uu___2 -> FStar_Pervasives_Native.None)
let rule_of_attributes (attrs : FStarC_Syntax_Syntax.term Prims.list) :
  rule FStar_Pervasives_Native.option=
  let uu___ =
    FStarC_Syntax_Util.has_attribute attrs
      FStarC_Parser_Const.custard_opaque_attr in
  if uu___
  then FStar_Pervasives_Native.Some Rule_opaque
  else
    (let uu___1 =
       let uu___2 =
         FStarC_Syntax_Util.get_attribute
           FStarC_Parser_Const.custard_extern_attr attrs in
       match uu___2 with
       | FStar_Pervasives_Native.Some v -> true
       | uu___3 -> false in
     if uu___1
     then
       let name =
         let uu___2 =
           attribute_string attrs FStarC_Parser_Const.custard_extern_attr in
         match uu___2 with
         | FStar_Pervasives_Native.Some "" -> FStar_Pervasives_Native.None
         | r -> r in
       let uu___2 =
         let uu___3 =
           let uu___4 =
             attribute_string attrs FStarC_Parser_Const.custard_c_header_attr in
           { x_name = name; x_header = uu___4 } in
         Rule_extern uu___3 in
       FStar_Pervasives_Native.Some uu___2
     else FStar_Pervasives_Native.None)
let no_fstar_stubs (ns : Prims.string Prims.list) : Prims.string Prims.list=
  match ns with
  | "FStar"::"NormSteps"::rest -> "FStarC" :: "NormSteps" :: rest
  | "FStar"::"Stubs"::rest -> "FStarC" :: rest
  | uu___ -> ns
let float_vocabulary_hint (l : FStarC_Ident.lident) :
  Prims.string FStar_Pervasives_Native.option=
  let uu___ =
    let uu___1 = FStarC_Ident.path_of_lid l in FStarC_List.rev uu___1 in
  match uu___ with
  | id::rev_ns ->
      let uu___1 = float_of_module (no_fstar_stubs (FStarC_List.rev rev_ns)) in
      (match uu___1 with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some uu___2 ->
           (match id with
            | "eq" -> FStar_Pervasives_Native.Some "ieee_eq"
            | "equal" -> FStar_Pervasives_Native.Some "ieee_eq"
            | "equals" -> FStar_Pervasives_Native.Some "ieee_eq"
            | uu___3 -> FStar_Pervasives_Native.None))
  | uu___1 -> FStar_Pervasives_Native.None
let is_stub_module (ns : Prims.string Prims.list) : Prims.bool=
  match ns with | "FStar"::"Stubs"::uu___ -> true | uu___ -> false
let stub_aliases : (Prims.string * Prims.string) Prims.list=
  [("FStar.Stubs.Tactics.Common.Stop", "FStarC.Errors.Stop")]
let parse_extern_type (spec : Prims.string) :
  (Prims.string * extern) FStar_Pervasives_Native.option=
  let opt s =
    if s = ""
    then FStar_Pervasives_Native.None
    else FStar_Pervasives_Native.Some s in
  let uu___ =
    match FStarC_String.split [64] spec with
    | a::[] -> (a, FStar_Pervasives_Native.None)
    | a::h::[] -> (a, (opt h))
    | uu___1 -> (spec, FStar_Pervasives_Native.None) in
  match uu___ with
  | (lid, rest) ->
      let uu___1 =
        match FStarC_String.split [61] lid with
        | a::[] -> (a, FStar_Pervasives_Native.None)
        | a::n::[] -> (a, (opt n))
        | uu___2 -> (lid, FStar_Pervasives_Native.None) in
      (match uu___1 with
       | (lid1, nm) ->
           if lid1 = ""
           then FStar_Pervasives_Native.None
           else
             FStar_Pervasives_Native.Some
               (lid1, { x_name = nm; x_header = rest }))
let extern_types : (Prims.string * extern) Prims.list= []
let extern_type_of_lid (l : FStarC_Ident.lident) :
  extern FStar_Pervasives_Native.option=
  let s = FStarC_Ident.string_of_lid l in
  let from_cmdline =
    let uu___ = FStarC_Options.custard_extern_types () in
    FStarC_List.collect
      (fun spec ->
         let uu___1 = parse_extern_type spec in
         match uu___1 with
         | FStar_Pervasives_Native.Some (k, x) when k = s -> [x]
         | uu___2 -> []) uu___ in
  match from_cmdline with
  | x::uu___ -> FStar_Pervasives_Native.Some x
  | [] ->
      FStarC_List.tryPick
        (fun uu___ ->
           match uu___ with
           | (k, x) ->
               if k = s
               then FStar_Pervasives_Native.Some x
               else FStar_Pervasives_Native.None) extern_types
let realized_modules : Prims.string Prims.list Prims.list=
  [["FStar"; "All"];
  ["FStar"; "Bytes"];
  ["FStar"; "Char"];
  ["FStar"; "Dyn"];
  ["FStar"; "Exception"];
  ["FStar"; "Exn"];
  ["FStar"; "IO"];
  ["FStar"; "ImmutableArray"];
  ["FStar"; "ImmutableArray"; "Base"];
  ["FStar"; "Issue"];
  ["FStar"; "List"];
  ["FStar"; "List"; "Tot"; "Base"];
  ["FStar"; "Option"];
  ["FStar"; "Parse"];
  ["FStar"; "Pervasives"];
  ["FStar"; "Pervasives"; "Native"];
  ["FStar"; "Pprint"];
  ["FStar"; "Sealed"];
  ["FStar"; "String"];
  ["FStar"; "UInt8"];
  ["FStarC"; "Array"];
  ["FStarC"; "BaseTypes"];
  ["FStarC"; "Effect"];
  ["FStarC"; "Extraction"; "ML"; "PrintML"];
  ["FStarC"; "Filepath"];
  ["FStarC"; "Format"];
  ["FStarC"; "Getopt"];
  ["FStarC"; "Hash"];
  ["FStarC"; "Hints"];
  ["FStarC"; "IMap"];
  ["FStarC"; "Int"; "Extra"];
  ["FStarC"; "Json"];
  ["FStarC"; "List"];
  ["FStarC"; "PIMap"];
  ["FStarC"; "PSMap"];
  ["FStarC"; "Parser"; "ParseIt"];
  ["FStarC"; "Platform"; "Base"];
  ["FStarC"; "Plugins"; "Base"];
  ["FStarC"; "Pprint"];
  ["FStarC"; "Range"];
  ["FStarC"; "Reflection"; "Types"];
  ["FStarC"; "Tactics"; "Unseal"];
  ["FStarC"; "Tactics"; "V2"; "Builtins"];
  ["FStarC"; "SMap"];
  ["FStarC"; "String"];
  ["FStarC"; "StringBuffer"];
  ["FStarC"; "Syntax"; "TermHashTable"];
  ["FStarC"; "Tactics"; "Native"];
  ["FStarC"; "Time"];
  ["FStarC"; "Timing"];
  ["FStarC"; "Unionfind"];
  ["FStarC"; "Util"];
  ["Prims"];
  ["Pulse"; "Lib"; "SpinLock"]]
let builtin_krml_models : Prims.string Prims.list Prims.list=
  [["Pulse"; "Lib"; "Slice"]]
let is_krml_model (ns : Prims.string Prims.list) : Prims.bool=
  let uu___ =
    let uu___1 = FStarC_Options.custard_backend () in uu___1 = "KrmlRust" in
  if uu___
  then
    let uu___1 = FStarC_List.existsb (fun m -> m = ns) builtin_krml_models in
    (if uu___1
     then true
     else
       (let uu___2 = FStarC_Options.custard_krml_models () in
        FStarC_List.existsb (fun m -> m = (FStarC_String.concat "." ns))
          uu___2))
  else false
let is_krml_model_name (ns : Prims.string Prims.list) (id : Prims.string) :
  Prims.bool=
  let uu___ = is_krml_model ns in
  if uu___
  then true
  else
    (let uu___1 =
       let uu___2 =
         let uu___3 = FStarC_Options.custard_backend () in
         uu___3 = "KrmlRust" in
       if uu___2 then ns = ["FStar"; "Pervasives"; "Native"] else false in
     if uu___1
     then
       (FStarC_Util.starts_with id "tuple") ||
         (FStarC_Util.starts_with id "Mktuple")
     else false)
let krml_compat_name (ns : Prims.string Prims.list) (id : Prims.string) :
  (Prims.string Prims.list * Prims.string)=
  match (ns, id) with
  | ("Prims"::[], "op_Plus") -> (ns, "op_Addition")
  | ("Prims"::[], "op_Minus") -> (ns, "op_Subtraction")
  | ("Prims"::[], "op_Tilde_Minus") -> (ns, "op_Minus")
  | ("Prims"::[], "op_Star") -> (ns, "op_Multiply")
  | ("Prims"::[], "op_Slash") -> (ns, "op_Division")
  | ("Prims"::[], "op_Percent") -> (ns, "op_Modulus")
  | ("Prims"::[], "op_Less") -> (ns, "op_LessThan")
  | ("Prims"::[], "op_Less_Equals") -> (ns, "op_LessThanOrEqual")
  | ("Prims"::[], "op_Greater") -> (ns, "op_GreaterThan")
  | ("Prims"::[], "op_Greater_Equals") -> (ns, "op_GreaterThanOrEqual")
  | ("Pulse"::"Lib"::"Slice"::[], "op_Dot_Lparen_Rparen") ->
      (ns, "op_Array_Access")
  | ("Pulse"::"Lib"::"Slice"::[], "op_Dot_Lparen_Rparen_Less_Minus") ->
      (ns, "op_Array_Assignment")
  | uu___ -> (ns, id)
let builtin_krml_model_ops :
  (Prims.string Prims.list * Prims.string Prims.list) Prims.list=
  [(["Pulse"; "Lib"; "Slice"],
     ["from_array";
     "op_Array_Access";
     "op_Array_Assignment";
     "split";
     "subslice";
     "copy";
     "len"])]
let is_known_krml_model_op (ns : Prims.string Prims.list) (id : Prims.string)
  : Prims.bool=
  let uu___ =
    FStarC_List.tryFind
      (fun uu___1 -> match uu___1 with | (m, uu___2) -> m = ns)
      builtin_krml_model_ops in
  match uu___ with
  | FStar_Pervasives_Native.None -> true
  | FStar_Pervasives_Native.Some (uu___1, ops) ->
      let uu___2 = krml_compat_name ns id in
      (match uu___2 with
       | (uu___3, id1) -> FStarC_List.existsb (fun o -> o = id1) ops)
let is_realized_module (ns : Prims.string Prims.list) : Prims.bool=
  let uu___ = FStarC_List.existsb (fun m -> m = ns) realized_modules in
  if uu___ then true else is_krml_model ns
let type_only_realized_modules : Prims.string Prims.list Prims.list=
  [["FStar"; "Pervasives"]; ["FStar"; "Pervasives"; "Native"]]
let is_type_only_realized_module (ns : Prims.string Prims.list) : Prims.bool=
  FStarC_List.existsb (fun m -> m = ns) type_only_realized_modules
let c_realized_modules : Prims.string Prims.list Prims.list=
  [["Pulse"; "Lib"; "SpinLock"]]
let c_realization_header (ns : Prims.string Prims.list) :
  Prims.string FStar_Pervasives_Native.option=
  let uu___ = FStarC_List.existsb (fun m -> m = ns) c_realized_modules in
  if uu___
  then
    FStar_Pervasives_Native.Some
      (Prims.strcat (FStarC_String.concat "_" ns) ".h")
  else FStar_Pervasives_Native.None
exception No_custard_rule 
let uu___is_No_custard_rule (projectee : Prims.exn) : Prims.bool= true
type rule_lookup_t = FStarC_Ident.lident -> rule
let custard_rule (id : Prims.string) : rule FStar_Pervasives_Native.option=
  match id with
  | "dyn" ->
      FStar_Pervasives_Native.Some
        (Rule_prim
           (Prims.int_one,
             ((fun uu___ args ->
                 match args with
                 | e::[] -> e
                 | uu___1 ->
                     FStarC_Effect.failwith
                       "FStar.Custard.dyn applied to the wrong number of arguments"))))
  | uu___ -> FStar_Pervasives_Native.None
let normalizes_arguments (l : FStarC_Ident.lident) : Prims.bool=
  (FStarC_Ident.string_of_lid l) = "Pulse.Lib.GlobalArray.mk_static_array"
let builtin_rule (l : FStarC_Ident.lident) : rule=
  let r =
    let uu___ = FStarC_SMap.try_find table (FStarC_Ident.string_of_lid l) in
    match uu___ with
    | FStar_Pervasives_Native.Some r1 -> FStar_Pervasives_Native.Some r1
    | FStar_Pervasives_Native.None ->
        let path = FStarC_Ident.path_of_lid l in
        (match FStarC_List.rev path with
         | id::rev_ns ->
             let ns = no_fstar_stubs (FStarC_List.rev rev_ns) in
             let uu___1 = machine_int_of_module ns in
             (match uu___1 with
              | FStar_Pervasives_Native.Some sw -> machine_int_rule sw id
              | FStar_Pervasives_Native.None ->
                  let uu___2 = float_of_module ns in
                  (match uu___2 with
                   | FStar_Pervasives_Native.Some fw -> float_rule fw id
                   | FStar_Pervasives_Native.None ->
                       if ns = ["Prims"]
                       then prims_rule id
                       else
                         (let uu___3 =
                            if ns = ["FStar"; "Pervasives"]
                            then
                              let uu___4 = pervasives_rule id in
                              match uu___4 with
                              | FStar_Pervasives_Native.Some v -> true
                              | uu___5 -> false
                            else false in
                          if uu___3
                          then pervasives_rule id
                          else
                            if
                              (ns = ["FStar"; "Int"; "Cast"]) ||
                                (ns = ["FStar"; "Int"; "Cast"; "Full"])
                            then int_cast_rule id
                            else
                              if
                                (ns = ["FStar"; "All"]) ||
                                  (ns = ["FStarC"; "Effect"])
                              then
                                (let uu___4 = ref_rule id in
                                 match uu___4 with
                                 | FStar_Pervasives_Native.Some r1 ->
                                     FStar_Pervasives_Native.Some r1
                                 | FStar_Pervasives_Native.None ->
                                     let uu___5 = exn_rule id in
                                     (match uu___5 with
                                      | FStar_Pervasives_Native.Some r1 ->
                                          FStar_Pervasives_Native.Some r1
                                      | FStar_Pervasives_Native.None ->
                                          pulse_rule ns id))
                              else
                                if ns = ["FStar"; "Custard"]
                                then custard_rule id
                                else
                                  if ns = ["FStar"; "Exn"]
                                  then exn_rule id
                                  else
                                    (let uu___4 = is_realized_module ns in
                                     if uu___4
                                     then
                                       FStar_Pervasives_Native.Some
                                         Rule_realized
                                     else pulse_rule ns id))))
         | [] -> FStar_Pervasives_Native.None) in
  match r with
  | FStar_Pervasives_Native.Some r1 -> r1
  | FStar_Pervasives_Native.None -> FStarC_Effect.raise No_custard_rule
let ref_lookup_rule : rule_lookup_t FStarC_Effect.ref=
  FStarC_Effect.mk_ref builtin_rule
let register_pre_rule (f : rule_lookup_t) : unit=
  let before = FStarC_Effect.op_Bang ref_lookup_rule in
  FStarC_Effect.op_Colon_Equals ref_lookup_rule
    (fun l ->
       try (fun uu___ -> match () with | () -> f l) ()
       with | No_custard_rule -> before l)
let register_post_rule (f : rule_lookup_t) : unit=
  let before = FStarC_Effect.op_Bang ref_lookup_rule in
  FStarC_Effect.op_Colon_Equals ref_lookup_rule
    (fun l ->
       try (fun uu___ -> match () with | () -> before l) ()
       with | No_custard_rule -> f l)
let lookup_rule (l : FStarC_Ident.lident) :
  rule FStar_Pervasives_Native.option=
  try
    (fun uu___ ->
       match () with
       | () ->
           let uu___1 =
             let uu___2 = FStarC_Effect.op_Bang ref_lookup_rule in uu___2 l in
           FStar_Pervasives_Native.Some uu___1) ()
  with | No_custard_rule -> FStar_Pervasives_Native.None
let plugin_roots : FStarC_Ident.lident Prims.list FStarC_Effect.ref=
  FStarC_Effect.mk_ref []
let register_root (l : FStarC_Ident.lident) : unit=
  let uu___ =
    let uu___1 = FStarC_Effect.op_Bang plugin_roots in
    FStarC_List.op_At uu___1 [l] in
  FStarC_Effect.op_Colon_Equals plugin_roots uu___
let registered_roots (uu___ : unit) : FStarC_Ident.lident Prims.list=
  FStarC_Effect.op_Bang plugin_roots
let lifted : FStarC_Custard_Syntax.decl Prims.list FStarC_Effect.ref=
  FStarC_Effect.mk_ref []
let lift_named (id : Prims.string)
  (fs : FStarC_Custard_Syntax.flag Prims.list)
  (e : FStarC_Custard_Syntax.expr) : FStarC_Custard_Syntax.expr=
  let n =
    {
      FStarC_Custard_Syntax.ns = [];
      FStarC_Custard_Syntax.id = id;
      FStarC_Custard_Syntax.spec = FStar_Pervasives_Native.None
    } in
  let uu___ =
    match e.FStarC_Custard_Syntax.e with
    | FStarC_Custard_Syntax.EFun (b::bs, body) -> ((b :: bs), body)
    | uu___1 ->
        FStarC_Errors.raise_error0 FStarC_Errors_Codes.Error_CustardBadLift
          () (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
          (Obj.magic
             [FStarC_Errors_Msg.text
                (Prims.strcat
                   "Custard: lift_named was given something other than a lambda for `"
                   (Prims.strcat id "'."));
             FStarC_Errors_Msg.text
               "Only a lambda has parameters and a body to lift; anything else is already a value and can be referred to where it stands.";
             FStarC_Errors_Msg.text
               "A lambda with an empty binder list counts as `anything else': it is its own body, and lifting it would make a top-level variable rather than a function.  Give it a parameter -- a unit one if it needs none."]) in
  match uu___ with
  | (bs, body) ->
      let ret =
        match e.FStarC_Custard_Syntax.ty with
        | FStarC_Custard_Syntax.TArrow uu___1 ->
            FStarC_List.fold_left
              (fun t uu___2 ->
                 match t with
                 | FStarC_Custard_Syntax.TArrow (uu___3, uu___4, r) -> r
                 | uu___3 -> t) e.FStarC_Custard_Syntax.ty bs
        | t -> t in
      ((let uu___2 =
          let uu___3 = FStarC_Effect.op_Bang lifted in
          FStarC_List.existsb
            (fun d ->
               (FStarC_Custard_Syntax.name_of_decl d).FStarC_Custard_Syntax.id
                 = id) uu___3 in
        if uu___2
        then
          FStarC_Errors.raise_error0 FStarC_Errors_Codes.Error_CustardBadLift
            () (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
            (Obj.magic
               [FStarC_Errors_Msg.text
                  (Prims.strcat
                     "Custard: lift_named was asked for the name `"
                     (Prims.strcat id "' twice."));
               FStarC_Errors_Msg.text
                 "A lifted name is emitted verbatim, so two of them are one symbol. Derive a distinct name from whatever distinguishes the two lifts."])
        else ());
       (let uu___3 =
          let uu___4 = FStarC_Effect.op_Bang lifted in
          FStarC_List.op_At uu___4
            [FStarC_Custard_Syntax.DLet
               {
                 FStarC_Custard_Syntax.dl_name = n;
                 FStarC_Custard_Syntax.dl_typars = [];
                 FStarC_Custard_Syntax.dl_binders = bs;
                 FStarC_Custard_Syntax.dl_ret = ret;
                 FStarC_Custard_Syntax.dl_eff =
                   (body.FStarC_Custard_Syntax.eff);
                 FStarC_Custard_Syntax.dl_body = body;
                 FStarC_Custard_Syntax.dl_flags = (FStarC_Custard_Syntax.Root
                   :: fs)
               }] in
        FStarC_Effect.op_Colon_Equals lifted uu___3);
       FStarC_Custard_Syntax.mk (FStarC_Custard_Syntax.EQual (n, []))
         e.FStarC_Custard_Syntax.ty e.FStarC_Custard_Syntax.eff)
let take_lifted (uu___ : unit) : FStarC_Custard_Syntax.decl Prims.list=
  let ds = FStarC_Effect.op_Bang lifted in
  FStarC_Effect.op_Colon_Equals lifted []; ds
