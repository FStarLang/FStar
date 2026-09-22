open Prims
type kenv =
  {
  names: Prims.string Prims.list ;
  names_t: Prims.string Prims.list ;
  ctor_arity: Prims.int FStarC_SMap.t ;
  tvars_any: Prims.bool }
let __proj__Mkkenv__item__names (projectee : kenv) : Prims.string Prims.list=
  match projectee with | { names; names_t; ctor_arity; tvars_any;_} -> names
let __proj__Mkkenv__item__names_t (projectee : kenv) :
  Prims.string Prims.list=
  match projectee with
  | { names; names_t; ctor_arity; tvars_any;_} -> names_t
let __proj__Mkkenv__item__ctor_arity (projectee : kenv) :
  Prims.int FStarC_SMap.t=
  match projectee with
  | { names; names_t; ctor_arity; tvars_any;_} -> ctor_arity
let __proj__Mkkenv__item__tvars_any (projectee : kenv) : Prims.bool=
  match projectee with
  | { names; names_t; ctor_arity; tvars_any;_} -> tvars_any
let extend (env : kenv) (x : Prims.string) : kenv=
  {
    names = (x :: (env.names));
    names_t = (env.names_t);
    ctor_arity = (env.ctor_arity);
    tvars_any = (env.tvars_any)
  }
let extend_t (env : kenv) (x : Prims.string) : kenv=
  {
    names = (env.names);
    names_t = (x :: (env.names_t));
    ctor_arity = (env.ctor_arity);
    tvars_any = (env.tvars_any)
  }
let current : Prims.string FStarC_Effect.ref= FStarC_Effect.mk_ref "<none>"
let reject_ir (what : Prims.string) : 'a=
  let uu___ =
    let uu___1 =
      let uu___2 =
        let uu___3 =
          let uu___4 =
            let uu___5 =
              let uu___6 = FStarC_Effect.op_Bang current in
              Prims.strcat uu___6 "." in
            Prims.strcat " reached the karamel backend, in " uu___5 in
          Prims.strcat what uu___4 in
        Prims.strcat "Custard: " uu___3 in
      FStarC_Errors_Msg.text uu___2 in
    [uu___1;
    FStarC_Errors_Msg.text "No binder in this definition introduces it.";
    FStarC_Errors_Msg.text
      "This is a compiler bug: please report it, with the definition named above."] in
  FStarC_Errors.raise_error0
    FStarC_Errors_Codes.Error_CustardNoCRepresentation ()
    (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc) (Obj.magic uu___)
let find (env : kenv) (x : Prims.string) : Prims.int=
  try
    (fun uu___ ->
       match () with | () -> FStarC_List.index (fun y -> y = x) env.names) ()
  with | uu___ -> reject_ir (Prims.strcat "the unbound variable " x)
let find_t (env : kenv) (x : Prims.string) : Prims.int=
  try
    (fun uu___ ->
       match () with | () -> FStarC_List.index (fun y -> y = x) env.names_t)
      ()
  with | uu___ -> reject_ir (Prims.strcat "the unbound type variable " x)
let fresh_local (env : kenv) (base : Prims.string) : Prims.string=
  let rec go n =
    let x =
      if n = Prims.int_zero
      then base
      else
        (let uu___ = FStarC_Class_Show.show FStarC_Class_Show.showable_int n in
         Prims.strcat base uu___) in
    let uu___ = FStarC_List.existsb (fun y -> y = x) env.names in
    if uu___ then go (n + Prims.int_one) else x in
  go Prims.int_zero
let rec by_value_names (c : FStarC_Custard_Syntax.cty) :
  Prims.string Prims.list=
  match c with
  | FStarC_Custard_Syntax.TApp (n, args) ->
      let uu___ =
        FStarC_Custard_Builtins.is_krml_model n.FStarC_Custard_Syntax.ns in
      if uu___
      then []
      else
        (let uu___1 = FStarC_Custard_Syntax.string_of_name n in
         let uu___2 = FStarC_List.collect by_value_names args in uu___1 ::
           uu___2)
  | FStarC_Custard_Syntax.TInline c1 -> by_value_names c1
  | FStarC_Custard_Syntax.TBuf uu___ -> []
  | FStarC_Custard_Syntax.TRef uu___ -> []
  | FStarC_Custard_Syntax.TArrow uu___ -> []
  | uu___ -> []
let rec_type_table (p : FStarC_Custard_Syntax.program) :
  Prims.bool FStarC_SMap.t=
  let refs = FStarC_SMap.create (Prims.of_int 100) in
  FStarC_List.iter
    (fun d ->
       match d with
       | FStarC_Custard_Syntax.DType t ->
           let body =
             match t.FStarC_Custard_Syntax.dt_body with
             | FStarC_Custard_Syntax.TAbbrev c -> by_value_names c
             | FStarC_Custard_Syntax.TRecord fs ->
                 FStarC_List.collect
                   (fun uu___1 ->
                      match uu___1 with | (uu___2, c) -> by_value_names c) fs
             | FStarC_Custard_Syntax.TVariant cs ->
                 FStarC_List.collect
                   (fun uu___1 ->
                      match uu___1 with
                      | (uu___2, fs) ->
                          FStarC_List.collect
                            (fun uu___3 ->
                               match uu___3 with
                               | (uu___4, c) -> by_value_names c) fs) cs
             | uu___1 -> [] in
           let uu___1 =
             FStarC_Custard_Syntax.string_of_name
               t.FStarC_Custard_Syntax.dt_name in
           FStarC_SMap.add refs uu___1 body
       | uu___1 -> ()) p;
  (let out = FStarC_SMap.create (Prims.of_int 20) in
   (let uu___2 = FStarC_SMap.keys refs in
    FStarC_List.iter
      (fun start ->
         let seen = FStarC_SMap.create (Prims.of_int 20) in
         let rec go n =
           let uu___3 =
             if n = start
             then
               let uu___4 = FStarC_SMap.try_find seen n in
               (FStar_Pervasives_Native.Some true) = uu___4
             else false in
           if uu___3
           then true
           else
             (let uu___4 =
                let uu___5 = FStarC_SMap.try_find seen n in
                (FStar_Pervasives_Native.Some true) = uu___5 in
              if uu___4
              then false
              else
                (FStarC_SMap.add seen n true;
                 (let uu___6 = FStarC_SMap.try_find refs n in
                  match uu___6 with
                  | FStar_Pervasives_Native.None -> false
                  | FStar_Pervasives_Native.Some ns ->
                      FStarC_List.existsb
                        (fun m -> if m = start then true else go m) ns))) in
         let uu___3 = FStarC_SMap.try_find refs start in
         match uu___3 with
         | FStar_Pervasives_Native.Some ns when
             FStarC_List.existsb (fun m -> if m = start then true else go m)
               ns
             -> FStarC_SMap.add out start true
         | uu___4 -> ()) uu___2);
   out)
let rec_types : Prims.bool FStarC_SMap.t FStarC_Effect.ref=
  let uu___ = FStarC_SMap.create Prims.int_zero in FStarC_Effect.mk_ref uu___
let dead_abbrev_table (p : FStarC_Custard_Syntax.program) :
  Prims.bool FStarC_SMap.t=
  let out = FStarC_SMap.create (Prims.of_int 20) in
  let uu___ =
    let uu___1 = FStarC_Options.custard_backend () in uu___1 <> "KrmlRust" in
  if uu___
  then out
  else
    (let modelled_abbrev t =
       match t.FStarC_Custard_Syntax.dt_body with
       | FStarC_Custard_Syntax.TAbbrev (FStarC_Custard_Syntax.TApp
           (n, uu___1)) ->
           FStarC_Custard_Builtins.is_krml_model_name
             n.FStarC_Custard_Syntax.ns n.FStarC_Custard_Syntax.id
       | uu___1 -> false in
     let is_cand d =
       match d with
       | FStarC_Custard_Syntax.DType t ->
           let uu___1 =
             let uu___2 =
               FStarC_Custard_Syntax.string_of_name
                 t.FStarC_Custard_Syntax.dt_name in
             FStarC_SMap.try_find out uu___2 in
           (FStar_Pervasives_Native.Some true) = uu___1
       | uu___1 -> false in
     FStarC_List.iter
       (fun d ->
          match d with
          | FStarC_Custard_Syntax.DType t when modelled_abbrev t ->
              let uu___2 =
                FStarC_Custard_Syntax.string_of_name
                  t.FStarC_Custard_Syntax.dt_name in
              FStarC_SMap.add out uu___2 true
          | uu___2 -> ()) p;
     (let rec go fuel =
        if fuel <= Prims.int_zero
        then ()
        else
          (let changed = FStarC_Effect.mk_ref false in
           FStarC_List.iter
             (fun d ->
                let uu___3 = is_cand d in
                if uu___3
                then ()
                else
                  (let uu___4 = FStarC_Custard_Simplify.decl_deps d in
                   FStarC_List.iter
                     (fun n ->
                        let uu___5 =
                          let uu___6 = FStarC_SMap.try_find out n in
                          (FStar_Pervasives_Native.Some true) = uu___6 in
                        if uu___5
                        then
                          (FStarC_SMap.remove out n;
                           FStarC_Effect.op_Colon_Equals changed true)
                        else ()) uu___4)) p;
           (let uu___3 = FStarC_Effect.op_Bang changed in
            if uu___3 then go (fuel - Prims.int_one) else ())) in
      go ((FStarC_List.length p) + Prims.int_one); out))
let dead_abbrevs : Prims.bool FStarC_SMap.t FStarC_Effect.ref=
  let uu___ = FStarC_SMap.create Prims.int_zero in FStarC_Effect.mk_ref uu___
let shadowed : Prims.bool FStarC_SMap.t FStarC_Effect.ref=
  let uu___ = FStarC_SMap.create Prims.int_zero in FStarC_Effect.mk_ref uu___
let lident_of_name (n : FStarC_Custard_Syntax.name) :
  FStarC_Extraction_KrmlAst.lident=
  let uu___ =
    FStarC_Custard_Builtins.krml_compat_name n.FStarC_Custard_Syntax.ns
      n.FStarC_Custard_Syntax.id in
  match uu___ with
  | (ns, id) ->
      let id1 =
        match n.FStarC_Custard_Syntax.spec with
        | FStar_Pervasives_Native.None -> id
        | FStar_Pervasives_Native.Some s ->
            Prims.strcat id (Prims.strcat "__" s) in
      let ns1 =
        let uu___1 =
          let uu___2 =
            let uu___3 = FStarC_Effect.op_Bang shadowed in
            let uu___4 = FStarC_Custard_Syntax.string_of_name n in
            FStarC_SMap.try_find uu___3 uu___4 in
          (FStar_Pervasives_Native.Some true) = uu___2 in
        if uu___1 then "Custard" :: ns else ns in
      (ns1, id1)
let extern_types : Prims.string FStarC_SMap.t FStarC_Effect.ref=
  let uu___ = FStarC_SMap.create Prims.int_zero in FStarC_Effect.mk_ref uu___
let type_lident_of_name (n : FStarC_Custard_Syntax.name) :
  FStarC_Extraction_KrmlAst.lident=
  let lid = lident_of_name n in
  let uu___ =
    let uu___1 = FStarC_Effect.op_Bang extern_types in
    let uu___2 = FStarC_Custard_Syntax.string_of_name n in
    FStarC_SMap.try_find uu___1 uu___2 in
  match uu___ with
  | FStar_Pervasives_Native.Some t -> ([], t)
  | FStar_Pervasives_Native.None -> lid
let extern_values : Prims.string FStarC_SMap.t FStarC_Effect.ref=
  let uu___ = FStarC_SMap.create Prims.int_zero in FStarC_Effect.mk_ref uu___
let value_lident_of_name (n : FStarC_Custard_Syntax.name) :
  FStarC_Extraction_KrmlAst.lident=
  let uu___ =
    let uu___1 = FStarC_Effect.op_Bang extern_values in
    let uu___2 = FStarC_Custard_Syntax.string_of_name n in
    FStarC_SMap.try_find uu___1 uu___2 in
  match uu___ with
  | FStar_Pervasives_Native.Some t -> ([], t)
  | FStar_Pervasives_Native.None -> lident_of_name n
let is_tuple_type_name (n : FStarC_Custard_Syntax.name) : Prims.bool=
  if
    (n.FStarC_Custard_Syntax.ns = ["FStar"; "Pervasives"; "Native"]) &&
      (FStarC_Util.starts_with n.FStarC_Custard_Syntax.id "tuple")
  then let uu___ = FStarC_Options.custard_backend () in uu___ = "KrmlRust"
  else false
let is_tuple_ctor_name (n : FStarC_Custard_Syntax.name) : Prims.bool=
  if
    (n.FStarC_Custard_Syntax.ns = ["FStar"; "Pervasives"; "Native"]) &&
      (FStarC_Util.starts_with n.FStarC_Custard_Syntax.id "Mktuple")
  then let uu___ = FStarC_Options.custard_backend () in uu___ = "KrmlRust"
  else false
let ctor_name (n : FStarC_Custard_Syntax.name) : Prims.string=
  match n.FStarC_Custard_Syntax.spec with
  | FStar_Pervasives_Native.None -> n.FStarC_Custard_Syntax.id
  | FStar_Pervasives_Native.Some s ->
      Prims.strcat n.FStarC_Custard_Syntax.id (Prims.strcat "__" s)
let krml_fwidth (fw : FStarC_Custard_Syntax.fwidth) :
  FStarC_Extraction_KrmlAst.width=
  match fw with
  | FStarC_Custard_Syntax.Float32 -> FStarC_Extraction_KrmlAst.Float32
  | FStarC_Custard_Syntax.Float64 -> FStarC_Extraction_KrmlAst.Float64
  | FStarC_Custard_Syntax.Float16 ->
      FStarC_Errors.raise_error0
        FStarC_Errors_Codes.Error_CustardNoCRepresentation ()
        (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
        (Obj.magic
           [FStarC_Errors_Msg.text
              (Prims.strcat "Custard: "
                 (Prims.strcat (FStarC_Custard_Syntax.fwidth_to_string fw)
                    " has no krml representation."));
           FStarC_Errors_Msg.text
             "karamel's IR has no 16-bit floating-point width (section 66).";
           FStarC_Errors_Msg.text
             "Extract with --custard_backend C, which emits these as a two-byte struct with the arithmetic in the support header."])
  | FStarC_Custard_Syntax.BFloat16 ->
      FStarC_Errors.raise_error0
        FStarC_Errors_Codes.Error_CustardNoCRepresentation ()
        (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
        (Obj.magic
           [FStarC_Errors_Msg.text
              (Prims.strcat "Custard: "
                 (Prims.strcat (FStarC_Custard_Syntax.fwidth_to_string fw)
                    " has no krml representation."));
           FStarC_Errors_Msg.text
             "karamel's IR has no 16-bit floating-point width (section 66).";
           FStarC_Errors_Msg.text
             "Extract with --custard_backend C, which emits these as a two-byte struct with the arithmetic in the support header."])
let krml_int_lit (v : Prims.int) (b : FStar_IntegerLiteral.int_base) :
  Prims.string=
  let uu___ =
    let uu___1 = FStarC_Options.custard_backend () in uu___1 = "KrmlRust" in
  if uu___
  then FStarC_Custard_Syntax.int_lit_to_string v b
  else
    (match b with
     | FStar_IntegerLiteral.Hex ->
         FStarC_Custard_Syntax.int_lit_to_string v FStar_IntegerLiteral.Hex
     | uu___1 ->
         FStarC_Custard_Syntax.int_lit_to_string v FStar_IntegerLiteral.Dec)
let krml_reject_with (what : Prims.string) (where : Prims.string) : 'a=
  FStarC_Errors.raise_error0
    FStarC_Errors_Codes.Error_CustardNoCRepresentation ()
    (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
    (Obj.magic
       [FStarC_Errors_Msg.text
          (Prims.strcat "Custard: "
             (Prims.strcat what " has no karamel representation."));
       FStarC_Errors_Msg.text
         (Prims.strcat
            "The karamel backend's AST has no node for it, so there is no translation to give.  "
            where)])
let krml_reject_c_ok (what : Prims.string) : 'a=
  krml_reject_with what
    "The direct C backend (--custard_backend C) does accept it."
let krml_reject (what : Prims.string) : 'a=
  krml_reject_with what
    "The direct C backend (--custard_backend C) has no representation for it either."
let krml_reject_rust (what : Prims.string) (why : Prims.string) : 'a=
  FStarC_Errors.raise_error0
    FStarC_Errors_Codes.Error_CustardNoCRepresentation ()
    (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
    (Obj.magic
       [FStarC_Errors_Msg.text
          (Prims.strcat "Custard: "
             (Prims.strcat what
                " has no representation in karamel's Rust backend."));
       FStarC_Errors_Msg.text why;
       FStarC_Errors_Msg.text
         "Both C routes accept it: --custard_backend KrmlC and --custard_backend C."])
let krml_float_lit (fw : FStarC_Custard_Syntax.fwidth)
  (v : FStarC_Custard_Syntax.float_lit) : Prims.string=
  (match v with
   | FStarC_Custard_Syntax.FLNan -> krml_reject_c_ok "a NaN literal"
   | FStarC_Custard_Syntax.FLInf uu___1 ->
       krml_reject_c_ok "an infinity literal"
   | FStarC_Custard_Syntax.FLNum uu___1 -> ());
  (let s = FStarC_Custard_Syntax.float_lit_to_string v in
   let uu___1 =
     if
       match fw with
       | FStarC_Custard_Syntax.Float32 -> true
       | uu___2 -> false
     then let uu___2 = FStarC_Options.custard_backend () in uu___2 = "KrmlC"
     else false in
   if uu___1 then Prims.strcat s "f" else s)
let krml_width
  (sw : (FStarC_Const.signedness * FStarC_Custard_Syntax.iwidth)) :
  FStarC_Extraction_KrmlAst.width=
  match sw with
  | (FStarC_Const.Signed, FStarC_Custard_Syntax.W8) ->
      FStarC_Extraction_KrmlAst.Int8
  | (FStarC_Const.Signed, FStarC_Custard_Syntax.W16) ->
      FStarC_Extraction_KrmlAst.Int16
  | (FStarC_Const.Signed, FStarC_Custard_Syntax.W32) ->
      FStarC_Extraction_KrmlAst.Int32
  | (FStarC_Const.Signed, FStarC_Custard_Syntax.W64) ->
      FStarC_Extraction_KrmlAst.Int64
  | (FStarC_Const.Signed, FStarC_Custard_Syntax.WSizet) ->
      FStarC_Extraction_KrmlAst.PtrdiffT
  | (FStarC_Const.Unsigned, FStarC_Custard_Syntax.W8) ->
      FStarC_Extraction_KrmlAst.UInt8
  | (FStarC_Const.Unsigned, FStarC_Custard_Syntax.W16) ->
      FStarC_Extraction_KrmlAst.UInt16
  | (FStarC_Const.Unsigned, FStarC_Custard_Syntax.W32) ->
      FStarC_Extraction_KrmlAst.UInt32
  | (FStarC_Const.Unsigned, FStarC_Custard_Syntax.W64) ->
      FStarC_Extraction_KrmlAst.UInt64
  | (FStarC_Const.Unsigned, FStarC_Custard_Syntax.WSizet) ->
      FStarC_Extraction_KrmlAst.SizeT
  | (uu___, FStarC_Custard_Syntax.W128) ->
      FStarC_Effect.failwith
        "Custard: a 128-bit machine integer reached the krml backend"
let krml_op (o : FStarC_Custard_Syntax.op) : FStarC_Extraction_KrmlAst.op=
  match o with
  | FStarC_Custard_Syntax.Add -> FStarC_Extraction_KrmlAst.Add
  | FStarC_Custard_Syntax.AddW -> FStarC_Extraction_KrmlAst.AddW
  | FStarC_Custard_Syntax.Sub -> FStarC_Extraction_KrmlAst.Sub
  | FStarC_Custard_Syntax.SubW -> FStarC_Extraction_KrmlAst.SubW
  | FStarC_Custard_Syntax.Mult -> FStarC_Extraction_KrmlAst.Mult
  | FStarC_Custard_Syntax.MultW -> FStarC_Extraction_KrmlAst.MultW
  | FStarC_Custard_Syntax.Div -> FStarC_Extraction_KrmlAst.Div
  | FStarC_Custard_Syntax.DivW -> FStarC_Extraction_KrmlAst.DivW
  | FStarC_Custard_Syntax.Mod -> FStarC_Extraction_KrmlAst.Mod
  | FStarC_Custard_Syntax.BOr -> FStarC_Extraction_KrmlAst.BOr
  | FStarC_Custard_Syntax.BAnd -> FStarC_Extraction_KrmlAst.BAnd
  | FStarC_Custard_Syntax.BXor -> FStarC_Extraction_KrmlAst.BXor
  | FStarC_Custard_Syntax.BShiftL -> FStarC_Extraction_KrmlAst.BShiftL
  | FStarC_Custard_Syntax.BShiftR -> FStarC_Extraction_KrmlAst.BShiftR
  | FStarC_Custard_Syntax.BNot -> FStarC_Extraction_KrmlAst.BNot
  | FStarC_Custard_Syntax.Eq -> FStarC_Extraction_KrmlAst.Eq
  | FStarC_Custard_Syntax.Neq -> FStarC_Extraction_KrmlAst.Neq
  | FStarC_Custard_Syntax.Lt -> FStarC_Extraction_KrmlAst.Lt
  | FStarC_Custard_Syntax.Lte -> FStarC_Extraction_KrmlAst.Lte
  | FStarC_Custard_Syntax.Gt -> FStarC_Extraction_KrmlAst.Gt
  | FStarC_Custard_Syntax.Gte -> FStarC_Extraction_KrmlAst.Gte
  | FStarC_Custard_Syntax.And -> FStarC_Extraction_KrmlAst.And
  | FStarC_Custard_Syntax.Or -> FStarC_Extraction_KrmlAst.Or
  | FStarC_Custard_Syntax.Not -> FStarC_Extraction_KrmlAst.Not
  | FStarC_Custard_Syntax.BufRead ->
      FStarC_Effect.failwith
        "Custard: a buffer operation is not a karamel operator"
  | FStarC_Custard_Syntax.BufWrite ->
      FStarC_Effect.failwith
        "Custard: a buffer operation is not a karamel operator"
  | FStarC_Custard_Syntax.BufSub ->
      FStarC_Effect.failwith
        "Custard: a buffer operation is not a karamel operator"
  | FStarC_Custard_Syntax.BufFree ->
      FStarC_Effect.failwith
        "Custard: a buffer operation is not a karamel operator"
  | FStarC_Custard_Syntax.BufNull ->
      FStarC_Effect.failwith
        "Custard: a buffer operation is not a karamel operator"
  | FStarC_Custard_Syntax.BufIsNull ->
      FStarC_Effect.failwith
        "Custard: a buffer operation is not a karamel operator"
  | FStarC_Custard_Syntax.BufBlit ->
      FStarC_Effect.failwith
        "Custard: a buffer operation is not a karamel operator"
  | FStarC_Custard_Syntax.BufCreate uu___ ->
      FStarC_Effect.failwith
        "Custard: a buffer operation is not a karamel operator"
  | FStarC_Custard_Syntax.BufLit ->
      FStarC_Effect.failwith
        "Custard: a buffer operation is not a karamel operator"
  | FStarC_Custard_Syntax.BufUnconst ->
      FStarC_Effect.failwith
        "Custard: a buffer operation is not a karamel operator"
  | FStarC_Custard_Syntax.Commented uu___ ->
      FStarC_Effect.failwith "Custard: a comment is not a karamel operator"
let is_string_cty (t : FStarC_Custard_Syntax.cty) : Prims.bool=
  match t with
  | FStarC_Custard_Syntax.TApp (n, []) ->
      (match n.FStarC_Custard_Syntax.spec with
       | FStar_Pervasives_Native.None -> true
       | uu___ -> false) &&
        ((FStarC_String.concat "."
            (FStarC_List.op_At n.FStarC_Custard_Syntax.ns
               [n.FStarC_Custard_Syntax.id]))
           = "Prims.string")
  | uu___ -> false
let prim_type (n : FStarC_Custard_Syntax.name) :
  FStarC_Extraction_KrmlAst.typ FStar_Pervasives_Native.option=
  match if
          match n.FStarC_Custard_Syntax.spec with
          | FStar_Pervasives_Native.Some v -> true
          | uu___ -> false
        then ""
        else
          FStarC_String.concat "."
            (FStarC_List.op_At n.FStarC_Custard_Syntax.ns
               [n.FStarC_Custard_Syntax.id])
  with
  | "Prims.unit" ->
      FStar_Pervasives_Native.Some FStarC_Extraction_KrmlAst.TUnit
  | "Prims.bool" ->
      FStar_Pervasives_Native.Some FStarC_Extraction_KrmlAst.TBool
  | "Prims.int" ->
      FStar_Pervasives_Native.Some
        (FStarC_Extraction_KrmlAst.TInt FStarC_Extraction_KrmlAst.CInt)
  | "Prims.string" ->
      FStar_Pervasives_Native.Some
        (FStarC_Extraction_KrmlAst.TQualified (["Prims"], "string"))
  | "FStar.Char.char" ->
      FStar_Pervasives_Native.Some
        (FStarC_Extraction_KrmlAst.TInt FStarC_Extraction_KrmlAst.UInt32)
  | uu___ -> FStar_Pervasives_Native.None
let karamel_declares (n : FStarC_Custard_Syntax.name) : Prims.bool=
  let uu___ = lident_of_name n in
  match uu___ with
  | (ns, id) ->
      (match FStarC_String.concat "." (FStarC_List.op_At ns [id]) with
       | "Prims.op_Addition" -> true
       | "Prims.op_Subtraction" -> true
       | "Prims.op_Multiply" -> true
       | "Prims.op_Division" -> true
       | "Prims.op_Modulus" -> true
       | "Prims.op_Minus" -> true
       | "Prims.op_LessThan" -> true
       | "Prims.op_LessThanOrEqual" -> true
       | "Prims.op_GreaterThan" -> true
       | "Prims.op_GreaterThanOrEqual" -> true
       | "Prims.pow2" -> true
       | "Prims.abs" -> true
       | "Prims.strcat" -> true
       | "Prims.string_of_int" -> true
       | uu___1 -> false)
let rec krml_typ (env : kenv) (t : FStarC_Custard_Syntax.cty) :
  FStarC_Extraction_KrmlAst.typ=
  match t with
  | FStarC_Custard_Syntax.TUnit -> FStarC_Extraction_KrmlAst.TUnit
  | FStarC_Custard_Syntax.TAny -> FStarC_Extraction_KrmlAst.TAny
  | FStarC_Custard_Syntax.TExn -> FStarC_Extraction_KrmlAst.TAny
  | FStarC_Custard_Syntax.TInt sw ->
      let uu___ = krml_width sw in FStarC_Extraction_KrmlAst.TInt uu___
  | FStarC_Custard_Syntax.TFloat fw ->
      let uu___ = krml_fwidth fw in FStarC_Extraction_KrmlAst.TInt uu___
  | FStarC_Custard_Syntax.TVar x ->
      if env.tvars_any
      then FStarC_Extraction_KrmlAst.TAny
      else
        (let uu___ = find_t env x in FStarC_Extraction_KrmlAst.TBound uu___)
  | FStarC_Custard_Syntax.TArrow (a, uu___, b) ->
      let uu___1 =
        let uu___2 = krml_typ env a in
        let uu___3 = krml_typ env b in (uu___2, uu___3) in
      FStarC_Extraction_KrmlAst.TArrow uu___1
  | FStarC_Custard_Syntax.TTuple ts ->
      let uu___ = FStarC_List.map (krml_typ env) ts in
      FStarC_Extraction_KrmlAst.TTuple uu___
  | FStarC_Custard_Syntax.TBuf t1 ->
      let uu___ = krml_typ env t1 in FStarC_Extraction_KrmlAst.TBuf uu___
  | FStarC_Custard_Syntax.TRef t1 ->
      let uu___ = krml_typ env t1 in FStarC_Extraction_KrmlAst.TBuf uu___
  | FStarC_Custard_Syntax.TInline uu___ ->
      FStarC_Effect.failwith
        "Custard: an inline-field marker reached the karamel backend"
  | FStarC_Custard_Syntax.TConst uu___ ->
      FStarC_Errors.raise_error0
        FStarC_Errors_Codes.Error_CustardBadTemplateArg ()
        (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
        (Obj.magic
           [FStarC_Errors_Msg.text
              "Custard: an external type with a template target reached the karamel backend.";
           FStarC_Errors_Msg.text
             "A template-id is a C++ construction: [wmma::fragment<matrix_a, 16, 16, 16, half, row_major>] is one type and [wmma::fragment<matrix_b, ...>] another, and neither the OCaml nor the karamel type language has anywhere to put the arguments.  Section 69 is a C-backend feature (--custard_backend C).";
           FStarC_Errors_Msg.text
             "The unparameterized form still works everywhere: a [@@custard_extern] target with no [{0}] placeholder names one target type and its arguments are dropped."])
  | FStarC_Custard_Syntax.TApp (n, args) when
      if match args with | hd::tl -> true | uu___ -> false
      then
        let uu___ =
          let uu___1 = FStarC_Effect.op_Bang extern_types in
          let uu___2 = FStarC_Custard_Syntax.string_of_name n in
          FStarC_SMap.try_find uu___1 uu___2 in
        match uu___ with
        | FStar_Pervasives_Native.Some t1 ->
            let uu___1 = FStarC_Custard_Syntax.template_of_string t1 in
            FStarC_Custard_Syntax.is_template uu___1
        | FStar_Pervasives_Native.None -> false
      else false ->
      FStarC_Errors.raise_error0
        FStarC_Errors_Codes.Error_CustardBadTemplateArg ()
        (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
        (Obj.magic
           [FStarC_Errors_Msg.text
              "Custard: an external type with a template target reached the karamel backend.";
           FStarC_Errors_Msg.text
             "A template-id is a C++ construction: [wmma::fragment<matrix_a, 16, 16, 16, half, row_major>] is one type and [wmma::fragment<matrix_b, ...>] another, and neither the OCaml nor the karamel type language has anywhere to put the arguments.  Section 69 is a C-backend feature (--custard_backend C).";
           FStarC_Errors_Msg.text
             "The unparameterized form still works everywhere: a [@@custard_extern] target with no [{0}] placeholder names one target type and its arguments are dropped."])
  | FStarC_Custard_Syntax.TApp (n, []) ->
      (match prim_type n with
       | FStar_Pervasives_Native.Some t1 -> t1
       | FStar_Pervasives_Native.None ->
           let uu___ = type_lident_of_name n in
           FStarC_Extraction_KrmlAst.TQualified uu___)
  | FStarC_Custard_Syntax.TApp (n, args) when is_tuple_type_name n ->
      let uu___ = FStarC_List.map (krml_typ env) args in
      FStarC_Extraction_KrmlAst.TTuple uu___
  | FStarC_Custard_Syntax.TApp (n, args) ->
      let uu___ =
        let uu___1 = type_lident_of_name n in
        let uu___2 = FStarC_List.map (krml_typ env) args in (uu___1, uu___2) in
      FStarC_Extraction_KrmlAst.TApp uu___
let binder_of (env : kenv) (b : FStarC_Custard_Syntax.binder) :
  FStarC_Extraction_KrmlAst.binder=
  let uu___ = krml_typ env b.FStarC_Custard_Syntax.b_ty in
  {
    FStarC_Extraction_KrmlAst.name = (b.FStarC_Custard_Syntax.b_name);
    FStarC_Extraction_KrmlAst.typ = uu___;
    FStarC_Extraction_KrmlAst.mut = false;
    FStarC_Extraction_KrmlAst.meta = []
  }
let dummy_binder (x : Prims.string) : FStarC_Extraction_KrmlAst.binder=
  {
    FStarC_Extraction_KrmlAst.name = x;
    FStarC_Extraction_KrmlAst.typ = FStarC_Extraction_KrmlAst.TAny;
    FStarC_Extraction_KrmlAst.mut = false;
    FStarC_Extraction_KrmlAst.meta = []
  }
let krml_const (c : FStarC_Custard_Syntax.constant) :
  FStarC_Extraction_KrmlAst.expr=
  match c with
  | FStarC_Custard_Syntax.CUnit -> FStarC_Extraction_KrmlAst.EUnit
  | FStarC_Custard_Syntax.CBool b -> FStarC_Extraction_KrmlAst.EBool b
  | FStarC_Custard_Syntax.CString s -> FStarC_Extraction_KrmlAst.EString s
  | FStarC_Custard_Syntax.CInt (v, b, FStar_Pervasives_Native.None) ->
      let uu___ =
        let uu___1 = krml_int_lit v b in
        (FStarC_Extraction_KrmlAst.CInt, uu___1) in
      FStarC_Extraction_KrmlAst.EConstant uu___
  | FStarC_Custard_Syntax.CInt (v, b, FStar_Pervasives_Native.Some sw) ->
      let uu___ =
        let uu___1 = krml_width sw in
        let uu___2 = krml_int_lit v b in (uu___1, uu___2) in
      FStarC_Extraction_KrmlAst.EConstant uu___
  | FStarC_Custard_Syntax.CFloat (v, fw) ->
      let uu___ =
        let uu___1 = krml_fwidth fw in
        let uu___2 = krml_float_lit fw v in (uu___1, uu___2) in
      FStarC_Extraction_KrmlAst.EConstant uu___
  | FStarC_Custard_Syntax.CChar c1 ->
      let uu___ =
        let uu___1 =
          FStarC_Class_Show.show FStarC_Class_Show.showable_nat
            (FStar_Char.int_of_char c1) in
        (FStarC_Extraction_KrmlAst.UInt32, uu___1) in
      FStarC_Extraction_KrmlAst.EConstant uu___
let rec krml_pat (env : kenv) (p : FStarC_Custard_Syntax.pat) :
  (kenv * FStarC_Extraction_KrmlAst.pattern)=
  match p with
  | FStarC_Custard_Syntax.PWild ->
      ((extend env "_"), (FStarC_Extraction_KrmlAst.PVar (dummy_binder "_")))
  | FStarC_Custard_Syntax.PVar x ->
      ((extend env x), (FStarC_Extraction_KrmlAst.PVar (dummy_binder x)))
  | FStarC_Custard_Syntax.PConst (FStarC_Custard_Syntax.CUnit) ->
      (env, FStarC_Extraction_KrmlAst.PUnit)
  | FStarC_Custard_Syntax.PConst (FStarC_Custard_Syntax.CBool b) ->
      (env, (FStarC_Extraction_KrmlAst.PBool b))
  | FStarC_Custard_Syntax.PConst (FStarC_Custard_Syntax.CInt
      (v, b, FStar_Pervasives_Native.None)) ->
      let uu___ =
        let uu___1 =
          let uu___2 = krml_int_lit v b in
          (FStarC_Extraction_KrmlAst.CInt, uu___2) in
        FStarC_Extraction_KrmlAst.PConstant uu___1 in
      (env, uu___)
  | FStarC_Custard_Syntax.PConst (FStarC_Custard_Syntax.CInt
      (v, b, FStar_Pervasives_Native.Some sw)) ->
      let uu___ =
        let uu___1 =
          let uu___2 = krml_width sw in
          let uu___3 = krml_int_lit v b in (uu___2, uu___3) in
        FStarC_Extraction_KrmlAst.PConstant uu___1 in
      (env, uu___)
  | FStarC_Custard_Syntax.PConst (FStarC_Custard_Syntax.CChar c) ->
      let uu___ =
        let uu___1 =
          let uu___2 =
            FStarC_Class_Show.show FStarC_Class_Show.showable_nat
              (FStar_Char.int_of_char c) in
          (FStarC_Extraction_KrmlAst.UInt32, uu___2) in
        FStarC_Extraction_KrmlAst.PConstant uu___1 in
      (env, uu___)
  | FStarC_Custard_Syntax.PConst (FStarC_Custard_Syntax.CString uu___) ->
      let uu___1 =
        let uu___2 = FStarC_Options.custard_backend () in uu___2 = "KrmlRust" in
      if uu___1
      then
        krml_reject_rust "a string pattern"
          "A flat string match is compiled to a comparison chain using krmllib's __eq__Prims_string, which is C and has no Rust counterpart."
      else krml_reject_c_ok "a string pattern"
  | FStarC_Custard_Syntax.PConst (FStarC_Custard_Syntax.CFloat uu___) ->
      krml_reject_c_ok "a floating-point pattern"
  | FStarC_Custard_Syntax.PConst uu___ -> krml_reject "this constant pattern"
  | FStarC_Custard_Syntax.PCtor (n, ps) when is_tuple_ctor_name n ->
      let uu___ = krml_pats env ps in
      (match uu___ with
       | (env1, ps1) -> (env1, (FStarC_Extraction_KrmlAst.PTuple ps1)))
  | FStarC_Custard_Syntax.PCtor (n, ps) ->
      let uu___ = krml_pats env ps in
      (match uu___ with
       | (env1, ps1) ->
           let uu___1 =
             let uu___2 = let uu___3 = ctor_name n in (uu___3, ps1) in
             FStarC_Extraction_KrmlAst.PCons uu___2 in
           (env1, uu___1))
  | FStarC_Custard_Syntax.PRecord (uu___, fs) ->
      let uu___1 =
        let uu___2 = FStarC_List.map FStar_Pervasives_Native.snd fs in
        krml_pats env uu___2 in
      (match uu___1 with
       | (env1, ps) ->
           let uu___2 =
             let uu___3 =
               let uu___4 = FStarC_List.map FStar_Pervasives_Native.fst fs in
               FStarC_List.zip uu___4 ps in
             FStarC_Extraction_KrmlAst.PRecord uu___3 in
           (env1, uu___2))
  | FStarC_Custard_Syntax.PTuple ps ->
      let uu___ = krml_pats env ps in
      (match uu___ with
       | (env1, ps1) -> (env1, (FStarC_Extraction_KrmlAst.PTuple ps1)))
  | FStarC_Custard_Syntax.POr uu___ -> krml_reject "a pattern disjunction"
and krml_pats (env : kenv) (ps : FStarC_Custard_Syntax.pat Prims.list) :
  (kenv * FStarC_Extraction_KrmlAst.pattern Prims.list)=
  match ps with
  | [] -> (env, [])
  | p::ps1 ->
      let uu___ = krml_pat env p in
      (match uu___ with
       | (env1, p1) ->
           let uu___1 = krml_pats env1 ps1 in
           (match uu___1 with | (env2, ps2) -> (env2, (p1 :: ps2))))
let rec krml_expr (env : kenv) (e : FStarC_Custard_Syntax.expr) :
  FStarC_Extraction_KrmlAst.expr=
  match e.FStarC_Custard_Syntax.e with
  | FStarC_Custard_Syntax.EConst c -> krml_const c
  | FStarC_Custard_Syntax.EVar x ->
      let uu___ = find env x in FStarC_Extraction_KrmlAst.EBound uu___
  | FStarC_Custard_Syntax.EQual (n, []) ->
      let uu___ = value_lident_of_name n in
      FStarC_Extraction_KrmlAst.EQualified uu___
  | FStarC_Custard_Syntax.EQual (n, tys) ->
      let uu___ =
        let uu___1 =
          let uu___2 = value_lident_of_name n in
          FStarC_Extraction_KrmlAst.EQualified uu___2 in
        let uu___2 = FStarC_List.map (krml_typ env) tys in (uu___1, uu___2) in
      FStarC_Extraction_KrmlAst.ETypApp uu___
  | FStarC_Custard_Syntax.ELet (x, t, e1, e2) ->
      let b =
        let uu___ = krml_typ env t in
        {
          FStarC_Extraction_KrmlAst.name = x;
          FStarC_Extraction_KrmlAst.typ = uu___;
          FStarC_Extraction_KrmlAst.mut = false;
          FStarC_Extraction_KrmlAst.meta = []
        } in
      let uu___ =
        let uu___1 = krml_expr env e1 in
        let uu___2 = krml_expr (extend env x) e2 in (b, uu___1, uu___2) in
      FStarC_Extraction_KrmlAst.ELet uu___
  | FStarC_Custard_Syntax.EApp (hd, args) ->
      let uu___ =
        let uu___1 = krml_expr env hd in
        let uu___2 = FStarC_List.map (krml_expr env) args in (uu___1, uu___2) in
      FStarC_Extraction_KrmlAst.EApp uu___
  | FStarC_Custard_Syntax.EFun (bs, body) ->
      let env' =
        FStarC_List.fold_left
          (fun env1 b -> extend env1 b.FStarC_Custard_Syntax.b_name) env bs in
      let uu___ =
        let uu___1 = FStarC_List.map (binder_of env) bs in
        let uu___2 = krml_expr env' body in
        let uu___3 = krml_typ env body.FStarC_Custard_Syntax.ty in
        (uu___1, uu___2, uu___3) in
      FStarC_Extraction_KrmlAst.EFun uu___
  | FStarC_Custard_Syntax.EMatch (scrut, brs) when is_string_match scrut brs
      -> string_match env scrut brs
  | FStarC_Custard_Syntax.EMatch (scrut, brs) ->
      let uu___ =
        let uu___1 = krml_expr env scrut in
        let uu___2 = FStarC_List.map (krml_branch env) brs in
        (uu___1, uu___2) in
      FStarC_Extraction_KrmlAst.EMatch uu___
  | FStarC_Custard_Syntax.EIf (c, t, f) ->
      let uu___ =
        let uu___1 = krml_expr env c in
        let uu___2 = krml_expr env t in
        let uu___3 = krml_expr env f in (uu___1, uu___2, uu___3) in
      FStarC_Extraction_KrmlAst.EIfThenElse uu___
  | FStarC_Custard_Syntax.ESeq (e1, e2) when
      e1.FStarC_Custard_Syntax.ty = FStarC_Custard_Syntax.TUnit ->
      let uu___ =
        let uu___1 = krml_expr env e1 in
        let uu___2 = let uu___3 = krml_expr env e2 in [uu___3] in uu___1 ::
          uu___2 in
      FStarC_Extraction_KrmlAst.ESequence uu___
  | FStarC_Custard_Syntax.ESeq (e1, e2) ->
      let x = fresh_local env "discarded" in
      let b =
        {
          FStarC_Extraction_KrmlAst.name = x;
          FStarC_Extraction_KrmlAst.typ = FStarC_Extraction_KrmlAst.TAny;
          FStarC_Extraction_KrmlAst.mut = false;
          FStarC_Extraction_KrmlAst.meta = []
        } in
      let uu___ =
        let uu___1 = krml_expr env e1 in
        let uu___2 = krml_expr (extend env x) e2 in (b, uu___1, uu___2) in
      FStarC_Extraction_KrmlAst.ELet uu___
  | FStarC_Custard_Syntax.ECtor (n, args) when is_tuple_ctor_name n ->
      let uu___ = FStarC_List.map (krml_expr env) args in
      FStarC_Extraction_KrmlAst.ETuple uu___
  | FStarC_Custard_Syntax.ECtor (n, args) ->
      let uu___ =
        let uu___1 = krml_typ env e.FStarC_Custard_Syntax.ty in
        let uu___2 = ctor_name n in
        let uu___3 = FStarC_List.map (krml_expr env) args in
        (uu___1, uu___2, uu___3) in
      FStarC_Extraction_KrmlAst.ECons uu___
  | FStarC_Custard_Syntax.ETuple es ->
      let uu___ = FStarC_List.map (krml_expr env) es in
      FStarC_Extraction_KrmlAst.ETuple uu___
  | FStarC_Custard_Syntax.ERecord (uu___, fs) ->
      let uu___1 =
        let uu___2 = krml_typ env e.FStarC_Custard_Syntax.ty in
        let uu___3 =
          FStarC_List.map
            (fun uu___4 ->
               match uu___4 with
               | (f, x) -> let uu___5 = krml_expr env x in (f, uu___5)) fs in
        (uu___2, uu___3) in
      FStarC_Extraction_KrmlAst.EFlat uu___1
  | FStarC_Custard_Syntax.EProj (e1, uu___, f) ->
      let uu___1 =
        let uu___2 = krml_typ env e1.FStarC_Custard_Syntax.ty in
        let uu___3 = krml_expr env e1 in (uu___2, uu___3, f) in
      FStarC_Extraction_KrmlAst.EField uu___1
  | FStarC_Custard_Syntax.EDiscrim (e1, n) ->
      let arity =
        let uu___ =
          let uu___1 = FStarC_Custard_Syntax.mangled_name n in
          FStarC_SMap.try_find env.ctor_arity uu___1 in
        match uu___ with
        | FStar_Pervasives_Native.Some n1 -> n1
        | FStar_Pervasives_Native.None -> Prims.int_zero in
      let wilds =
        let uu___ = repeat_unit arity in
        FStarC_List.map
          (fun uu___1 -> FStarC_Extraction_KrmlAst.PVar (dummy_binder "_"))
          uu___ in
      let uu___ =
        let uu___1 = krml_expr env e1 in
        let uu___2 =
          let uu___3 =
            let uu___4 =
              let uu___5 = let uu___6 = ctor_name n in (uu___6, wilds) in
              FStarC_Extraction_KrmlAst.PCons uu___5 in
            (uu___4, (FStarC_Extraction_KrmlAst.EBool true)) in
          [uu___3;
          ((FStarC_Extraction_KrmlAst.PVar (dummy_binder "_")),
            (FStarC_Extraction_KrmlAst.EBool false))] in
        (uu___1, uu___2) in
      FStarC_Extraction_KrmlAst.EMatch uu___
  | FStarC_Custard_Syntax.ECast (e1, t) ->
      let uu___ =
        let uu___1 = krml_expr env e1 in
        let uu___2 = krml_typ env t in (uu___1, uu___2) in
      FStarC_Extraction_KrmlAst.ECast uu___
  | FStarC_Custard_Syntax.ECoerce (e1, t) ->
      let uu___ =
        let uu___1 = krml_expr env e1 in
        let uu___2 = krml_typ env t in (uu___1, uu___2) in
      FStarC_Extraction_KrmlAst.ECast uu___
  | FStarC_Custard_Syntax.EOp
      ({ FStarC_Custard_Syntax.po_op = FStarC_Custard_Syntax.BufCreate l;
         FStarC_Custard_Syntax.po_ty = uu___;_},
       init::len::[])
      ->
      let uu___1 =
        let uu___2 = krml_expr env init in
        let uu___3 = krml_expr env len in
        ((match l with
          | FStarC_Custard_Syntax.LStack -> FStarC_Extraction_KrmlAst.Stack
          | FStarC_Custard_Syntax.LHeap ->
              FStarC_Extraction_KrmlAst.ManuallyManaged), uu___2, uu___3) in
      FStarC_Extraction_KrmlAst.EBufCreate uu___1
  | FStarC_Custard_Syntax.EOp
      ({ FStarC_Custard_Syntax.po_op = FStarC_Custard_Syntax.BufRead;
         FStarC_Custard_Syntax.po_ty = uu___;_},
       b::i::[])
      ->
      let uu___1 =
        let uu___2 = krml_expr env b in
        let uu___3 = krml_expr env i in (uu___2, uu___3) in
      FStarC_Extraction_KrmlAst.EBufRead uu___1
  | FStarC_Custard_Syntax.EOp
      ({ FStarC_Custard_Syntax.po_op = FStarC_Custard_Syntax.BufWrite;
         FStarC_Custard_Syntax.po_ty = uu___;_},
       b::i::v::[])
      ->
      let uu___1 =
        let uu___2 = krml_expr env b in
        let uu___3 = krml_expr env i in
        let uu___4 = krml_expr env v in (uu___2, uu___3, uu___4) in
      FStarC_Extraction_KrmlAst.EBufWrite uu___1
  | FStarC_Custard_Syntax.EOp
      ({ FStarC_Custard_Syntax.po_op = FStarC_Custard_Syntax.BufSub;
         FStarC_Custard_Syntax.po_ty = uu___;_},
       b::i::[])
      ->
      let uu___1 =
        let uu___2 = krml_expr env b in
        let uu___3 = krml_expr env i in (uu___2, uu___3) in
      FStarC_Extraction_KrmlAst.EBufSub uu___1
  | FStarC_Custard_Syntax.EOp
      ({ FStarC_Custard_Syntax.po_op = FStarC_Custard_Syntax.BufFree;
         FStarC_Custard_Syntax.po_ty = uu___;_},
       b::[])
      ->
      let uu___1 = krml_expr env b in
      FStarC_Extraction_KrmlAst.EBufFree uu___1
  | FStarC_Custard_Syntax.EOp
      ({ FStarC_Custard_Syntax.po_op = FStarC_Custard_Syntax.BufNull;
         FStarC_Custard_Syntax.po_ty = uu___;_},
       [])
      ->
      let uu___1 =
        match e.FStarC_Custard_Syntax.ty with
        | FStarC_Custard_Syntax.TBuf t -> krml_typ env t
        | FStarC_Custard_Syntax.TRef t -> krml_typ env t
        | uu___2 -> FStarC_Extraction_KrmlAst.TAny in
      FStarC_Extraction_KrmlAst.EBufNull uu___1
  | FStarC_Custard_Syntax.EOp
      ({ FStarC_Custard_Syntax.po_op = FStarC_Custard_Syntax.BufIsNull;
         FStarC_Custard_Syntax.po_ty = uu___;_},
       b::[])
      ->
      let t =
        match b.FStarC_Custard_Syntax.ty with
        | FStarC_Custard_Syntax.TBuf t1 -> krml_typ env t1
        | FStarC_Custard_Syntax.TRef t1 -> krml_typ env t1
        | uu___1 -> FStarC_Extraction_KrmlAst.TAny in
      let pt = FStarC_Extraction_KrmlAst.TBuf t in
      let uu___1 =
        let uu___2 =
          let uu___3 = krml_expr env b in
          [uu___3; FStarC_Extraction_KrmlAst.EBufNull t] in
        ((FStarC_Extraction_KrmlAst.ETypApp
            ((FStarC_Extraction_KrmlAst.EOp
                (FStarC_Extraction_KrmlAst.Eq,
                  FStarC_Extraction_KrmlAst.Bool)), [pt])), uu___2) in
      FStarC_Extraction_KrmlAst.EApp uu___1
  | FStarC_Custard_Syntax.EOp
      ({ FStarC_Custard_Syntax.po_op = FStarC_Custard_Syntax.BufBlit;
         FStarC_Custard_Syntax.po_ty = uu___;_},
       src::srci::dst::dsti::len::[])
      ->
      let uu___1 =
        let uu___2 = krml_expr env src in
        let uu___3 = krml_expr env srci in
        let uu___4 = krml_expr env dst in
        let uu___5 = krml_expr env dsti in
        let uu___6 = krml_expr env len in
        (uu___2, uu___3, uu___4, uu___5, uu___6) in
      FStarC_Extraction_KrmlAst.EBufBlit uu___1
  | FStarC_Custard_Syntax.EOp
      ({ FStarC_Custard_Syntax.po_op = FStarC_Custard_Syntax.BufLit;
         FStarC_Custard_Syntax.po_ty = uu___;_},
       elems)
      ->
      let uu___1 =
        let uu___2 = FStarC_List.map (krml_expr env) elems in
        (FStarC_Extraction_KrmlAst.Eternal, uu___2) in
      FStarC_Extraction_KrmlAst.EBufCreateL uu___1
  | FStarC_Custard_Syntax.EOp
      ({ FStarC_Custard_Syntax.po_op = FStarC_Custard_Syntax.BufUnconst;
         FStarC_Custard_Syntax.po_ty = uu___;_},
       b::[])
      -> krml_expr env b
  | FStarC_Custard_Syntax.EOp
      ({
         FStarC_Custard_Syntax.po_op = FStarC_Custard_Syntax.Commented
           (before, "");
         FStarC_Custard_Syntax.po_ty = uu___;_},
       {
         FStarC_Custard_Syntax.e = FStarC_Custard_Syntax.EConst
           (FStarC_Custard_Syntax.CUnit);
         FStarC_Custard_Syntax.ty = uu___1;
         FStarC_Custard_Syntax.eff = uu___2;_}::[])
      -> FStarC_Extraction_KrmlAst.EStandaloneComment before
  | FStarC_Custard_Syntax.EOp
      ({
         FStarC_Custard_Syntax.po_op = FStarC_Custard_Syntax.Commented
           (before, after);
         FStarC_Custard_Syntax.po_ty = uu___;_},
       b::[])
      ->
      let uu___1 = let uu___2 = krml_expr env b in (before, uu___2, after) in
      FStarC_Extraction_KrmlAst.EComment uu___1
  | FStarC_Custard_Syntax.EOp
      ({ FStarC_Custard_Syntax.po_op = o;
         FStarC_Custard_Syntax.po_ty = FStar_Pervasives_Native.None;_},
       args)
      when
      let uu___ =
        if
          ((match o with | FStarC_Custard_Syntax.Eq -> true | uu___1 -> false)
             ||
             (match o with
              | FStarC_Custard_Syntax.Neq -> true
              | uu___1 -> false))
            && (match args with | hd::tl -> true | uu___1 -> false)
        then
          let uu___1 = FStarC_Options.custard_backend () in
          uu___1 = "KrmlRust"
        else false in
      if uu___
      then
        match args with
        | a::uu___1 -> is_string_cty a.FStarC_Custard_Syntax.ty
        | [] -> false
      else false ->
      krml_reject_rust "string equality"
        "It is realized by krmllib's __eq__Prims_string, a C function with no Rust counterpart, so karamel's Rust backend fails to translate it."
  | FStarC_Custard_Syntax.EOp
      ({ FStarC_Custard_Syntax.po_op = o;
         FStarC_Custard_Syntax.po_ty = FStar_Pervasives_Native.None;_},
       args)
      when
      ((match o with | FStarC_Custard_Syntax.Eq -> true | uu___ -> false) ||
         (match o with | FStarC_Custard_Syntax.Neq -> true | uu___ -> false))
        && (match args with | hd::tl -> true | uu___ -> false)
      ->
      let t =
        match args with
        | a::uu___ -> krml_typ env a.FStarC_Custard_Syntax.ty
        | [] -> FStarC_Extraction_KrmlAst.TAny in
      let uu___ =
        let uu___1 =
          let uu___2 =
            let uu___3 =
              let uu___4 =
                let uu___5 = krml_op o in
                (uu___5, FStarC_Extraction_KrmlAst.Bool) in
              FStarC_Extraction_KrmlAst.EOp uu___4 in
            (uu___3, [t]) in
          FStarC_Extraction_KrmlAst.ETypApp uu___2 in
        let uu___2 = FStarC_List.map (krml_expr env) args in (uu___1, uu___2) in
      FStarC_Extraction_KrmlAst.EApp uu___
  | FStarC_Custard_Syntax.EOp (o, args) ->
      let w =
        match o.FStarC_Custard_Syntax.po_ty with
        | FStar_Pervasives_Native.Some (FStarC_Custard_Syntax.PInt sw) ->
            krml_width sw
        | FStar_Pervasives_Native.Some (FStarC_Custard_Syntax.PFloat fw) ->
            krml_fwidth fw
        | FStar_Pervasives_Native.None ->
            (match o.FStarC_Custard_Syntax.po_op with
             | FStarC_Custard_Syntax.And -> FStarC_Extraction_KrmlAst.Bool
             | FStarC_Custard_Syntax.Or -> FStarC_Extraction_KrmlAst.Bool
             | FStarC_Custard_Syntax.Not -> FStarC_Extraction_KrmlAst.Bool
             | FStarC_Custard_Syntax.Eq -> FStarC_Extraction_KrmlAst.Bool
             | FStarC_Custard_Syntax.Neq -> FStarC_Extraction_KrmlAst.Bool
             | uu___ -> FStarC_Extraction_KrmlAst.CInt) in
      let uu___ =
        let uu___1 =
          let uu___2 =
            let uu___3 = krml_op o.FStarC_Custard_Syntax.po_op in (uu___3, w) in
          FStarC_Extraction_KrmlAst.EOp uu___2 in
        let uu___2 = FStarC_List.map (krml_expr env) args in (uu___1, uu___2) in
      FStarC_Extraction_KrmlAst.EApp uu___
  | FStarC_Custard_Syntax.EWhile (c, body) ->
      let uu___ =
        let uu___1 = krml_expr env c in
        let uu___2 = krml_expr env body in (uu___1, uu___2) in
      FStarC_Extraction_KrmlAst.EWhile uu___
  | FStarC_Custard_Syntax.EAny -> FStarC_Extraction_KrmlAst.EAny
  | FStarC_Custard_Syntax.EAbort s -> FStarC_Extraction_KrmlAst.EAbortS s
  | FStarC_Custard_Syntax.ETry uu___ -> krml_reject "an exception handler"
  | FStarC_Custard_Syntax.ERaise uu___ ->
      FStarC_Extraction_KrmlAst.EAbortS
        "Custard: an uncaught exception was raised"
and is_string_match (scrut : FStarC_Custard_Syntax.expr)
  (brs : FStarC_Custard_Syntax.branch Prims.list) : Prims.bool=
  let uu___ =
    let uu___1 =
      let uu___2 =
        let uu___3 =
          let uu___4 = FStarC_Options.custard_backend () in uu___4 = "KrmlC" in
        if uu___3
        then is_string_cty scrut.FStarC_Custard_Syntax.ty
        else false in
      if uu___2
      then match brs with | hd::tl -> true | uu___3 -> false
      else false in
    if uu___1
    then
      FStarC_List.for_all
        (fun uu___2 ->
           match uu___2 with
           | (p, g, uu___3) ->
               (match g with
                | FStar_Pervasives_Native.None -> true
                | uu___4 -> false) &&
                 ((match p with
                   | FStarC_Custard_Syntax.PConst
                       (FStarC_Custard_Syntax.CString uu___4) -> true
                   | FStarC_Custard_Syntax.PVar uu___4 -> true
                   | FStarC_Custard_Syntax.PWild -> true
                   | uu___4 -> false))) brs
    else false in
  if uu___
  then
    match FStarC_List.last brs with
    | (FStarC_Custard_Syntax.PVar uu___1, uu___2, uu___3) -> true
    | (FStarC_Custard_Syntax.PWild, uu___1, uu___2) -> true
    | uu___1 -> false
  else false
and string_match (env : kenv) (scrut : FStarC_Custard_Syntax.expr)
  (brs : FStarC_Custard_Syntax.branch Prims.list) :
  FStarC_Extraction_KrmlAst.expr=
  let x = fresh_local env "scrut" in
  let st = krml_typ env scrut.FStarC_Custard_Syntax.ty in
  let b =
    {
      FStarC_Extraction_KrmlAst.name = x;
      FStarC_Extraction_KrmlAst.typ = st;
      FStarC_Extraction_KrmlAst.mut = false;
      FStarC_Extraction_KrmlAst.meta = []
    } in
  let env' = extend env x in
  let rec chain brs1 =
    match brs1 with
    | [] -> krml_reject "a string match with no catch-all"
    | (FStarC_Custard_Syntax.PWild, uu___, body)::uu___1 ->
        krml_expr env' body
    | (FStarC_Custard_Syntax.PVar y, uu___, body)::uu___1 ->
        let yb =
          {
            FStarC_Extraction_KrmlAst.name = y;
            FStarC_Extraction_KrmlAst.typ = st;
            FStarC_Extraction_KrmlAst.mut = false;
            FStarC_Extraction_KrmlAst.meta = []
          } in
        let uu___2 =
          let uu___3 =
            let uu___4 = find env' x in
            FStarC_Extraction_KrmlAst.EBound uu___4 in
          let uu___4 = krml_expr (extend env' y) body in (yb, uu___3, uu___4) in
        FStarC_Extraction_KrmlAst.ELet uu___2
    | (FStarC_Custard_Syntax.PConst (FStarC_Custard_Syntax.CString v), uu___,
       body)::rest ->
        let uu___1 =
          let uu___2 =
            let uu___3 =
              let uu___4 =
                let uu___5 =
                  let uu___6 = find env' x in
                  FStarC_Extraction_KrmlAst.EBound uu___6 in
                [uu___5; FStarC_Extraction_KrmlAst.EString v] in
              ((FStarC_Extraction_KrmlAst.ETypApp
                  ((FStarC_Extraction_KrmlAst.EOp
                      (FStarC_Extraction_KrmlAst.Eq,
                        FStarC_Extraction_KrmlAst.Bool)), [st])), uu___4) in
            FStarC_Extraction_KrmlAst.EApp uu___3 in
          let uu___3 = krml_expr env' body in
          let uu___4 = chain rest in (uu___2, uu___3, uu___4) in
        FStarC_Extraction_KrmlAst.EIfThenElse uu___1
    | uu___ -> krml_reject "a string pattern" in
  let uu___ =
    let uu___1 = krml_expr env scrut in
    let uu___2 = chain brs in (b, uu___1, uu___2) in
  FStarC_Extraction_KrmlAst.ELet uu___
and krml_branch (env : kenv) (br : FStarC_Custard_Syntax.branch) :
  FStarC_Extraction_KrmlAst.branch=
  let uu___ = br in
  match uu___ with
  | (p, g, body) ->
      let uu___1 = krml_pat env p in
      (match uu___1 with
       | (env', p1) ->
           (match g with
            | FStar_Pervasives_Native.None ->
                let uu___2 = krml_expr env' body in (p1, uu___2)
            | FStar_Pervasives_Native.Some uu___2 ->
                krml_reject "a pattern guard"))
and repeat_unit (n : Prims.int) : unit Prims.list=
  if n <= Prims.int_zero
  then []
  else (let uu___ = repeat_unit (n - Prims.int_one) in () :: uu___)
let krml_flags (fs : FStarC_Custard_Syntax.flag Prims.list) :
  FStarC_Extraction_KrmlAst.flag Prims.list=
  FStarC_List.collect
    (fun f ->
       match f with
       | FStarC_Custard_Syntax.Private -> [FStarC_Extraction_KrmlAst.Private]
       | FStarC_Custard_Syntax.Erased ->
           [FStarC_Extraction_KrmlAst.MustDisappear]
       | FStarC_Custard_Syntax.Comment c ->
           [FStarC_Extraction_KrmlAst.Comment c]
       | FStarC_Custard_Syntax.Prologue s ->
           [FStarC_Extraction_KrmlAst.Prologue s]
       | FStarC_Custard_Syntax.Epilogue s ->
           [FStarC_Extraction_KrmlAst.Epilogue s]
       | FStarC_Custard_Syntax.CInline -> [FStarC_Extraction_KrmlAst.CInline]
       | FStarC_Custard_Syntax.CMacro -> [FStarC_Extraction_KrmlAst.Macro]
       | uu___ -> []) fs
let with_typars (env : kenv) (ps : Prims.string Prims.list) : kenv=
  FStarC_List.fold_left extend_t env ps
let krml_decl (env : kenv) (d : FStarC_Custard_Syntax.decl) :
  FStarC_Extraction_KrmlAst.decl FStar_Pervasives_Native.option=
  (match d with
   | FStarC_Custard_Syntax.DLet l ->
       let uu___1 =
         FStarC_Custard_Syntax.string_of_name l.FStarC_Custard_Syntax.dl_name in
       FStarC_Effect.op_Colon_Equals current uu___1
   | FStarC_Custard_Syntax.DType t ->
       let uu___1 =
         FStarC_Custard_Syntax.string_of_name t.FStarC_Custard_Syntax.dt_name in
       FStarC_Effect.op_Colon_Equals current uu___1
   | uu___1 -> ());
  (match d with
   | FStarC_Custard_Syntax.DType
       { FStarC_Custard_Syntax.dt_name = n;
         FStarC_Custard_Syntax.dt_params = uu___1;
         FStarC_Custard_Syntax.dt_body = uu___2;
         FStarC_Custard_Syntax.dt_flags = uu___3;_}
       when
       match prim_type n with
       | FStar_Pervasives_Native.Some v -> true
       | uu___4 -> false -> FStar_Pervasives_Native.None
   | FStarC_Custard_Syntax.DLet l ->
       let env1 = with_typars env l.FStarC_Custard_Syntax.dl_typars in
       let n_t = FStarC_List.length l.FStarC_Custard_Syntax.dl_typars in
       let flags = krml_flags l.FStarC_Custard_Syntax.dl_flags in
       let env' =
         FStarC_List.fold_left
           (fun env2 b -> extend env2 b.FStarC_Custard_Syntax.b_name) env1
           l.FStarC_Custard_Syntax.dl_binders in
       let body = krml_expr env' l.FStarC_Custard_Syntax.dl_body in
       (match l.FStarC_Custard_Syntax.dl_binders with
        | [] ->
            let uu___1 =
              let uu___2 =
                let uu___3 = lident_of_name l.FStarC_Custard_Syntax.dl_name in
                let uu___4 = krml_typ env1 l.FStarC_Custard_Syntax.dl_ret in
                (flags, uu___3, n_t, uu___4, body) in
              FStarC_Extraction_KrmlAst.DGlobal uu___2 in
            FStar_Pervasives_Native.Some uu___1
        | bs ->
            let uu___1 =
              let uu___2 =
                let uu___3 = krml_typ env1 l.FStarC_Custard_Syntax.dl_ret in
                let uu___4 = lident_of_name l.FStarC_Custard_Syntax.dl_name in
                let uu___5 = FStarC_List.map (binder_of env1) bs in
                (FStar_Pervasives_Native.None, flags, n_t, uu___3, uu___4,
                  uu___5, body) in
              FStarC_Extraction_KrmlAst.DFunction uu___2 in
            FStar_Pervasives_Native.Some uu___1)
   | FStarC_Custard_Syntax.DType t when
       FStarC_Custard_Syntax.has_flag t.FStarC_Custard_Syntax.dt_flags
         FStarC_Custard_Syntax.Modelled
       -> FStar_Pervasives_Native.None
   | FStarC_Custard_Syntax.DType t when
       let uu___1 =
         let uu___2 = FStarC_Effect.op_Bang dead_abbrevs in
         let uu___3 =
           FStarC_Custard_Syntax.string_of_name
             t.FStarC_Custard_Syntax.dt_name in
         FStarC_SMap.try_find uu___2 uu___3 in
       (FStar_Pervasives_Native.Some true) = uu___1 ->
       FStar_Pervasives_Native.None
   | FStarC_Custard_Syntax.DType t ->
       let env1 = with_typars env t.FStarC_Custard_Syntax.dt_params in
       let n_t = FStarC_List.length t.FStarC_Custard_Syntax.dt_params in
       let flags =
         let uu___1 = krml_flags t.FStarC_Custard_Syntax.dt_flags in
         let uu___2 =
           let uu___3 =
             let uu___4 =
               let uu___5 = FStarC_Effect.op_Bang rec_types in
               let uu___6 =
                 FStarC_Custard_Syntax.string_of_name
                   t.FStarC_Custard_Syntax.dt_name in
               FStarC_SMap.try_find uu___5 uu___6 in
             (FStar_Pervasives_Native.Some true) = uu___4 in
           if uu___3 then [FStarC_Extraction_KrmlAst.GCType] else [] in
         FStarC_List.op_At uu___1 uu___2 in
       let lid = lident_of_name t.FStarC_Custard_Syntax.dt_name in
       (match t.FStarC_Custard_Syntax.dt_body with
        | FStarC_Custard_Syntax.TAbbrev c ->
            let uu___1 =
              let uu___2 =
                let uu___3 = krml_typ env1 c in (lid, flags, n_t, uu___3) in
              FStarC_Extraction_KrmlAst.DTypeAlias uu___2 in
            FStar_Pervasives_Native.Some uu___1
        | FStarC_Custard_Syntax.TRecord fs ->
            let uu___1 =
              let uu___2 =
                let uu___3 =
                  FStarC_List.map
                    (fun uu___4 ->
                       match uu___4 with
                       | (f, c) ->
                           let uu___5 =
                             let uu___6 = krml_typ env1 c in (uu___6, false) in
                           (f, uu___5)) fs in
                (lid, flags, n_t, uu___3) in
              FStarC_Extraction_KrmlAst.DTypeFlat uu___2 in
            FStar_Pervasives_Native.Some uu___1
        | FStarC_Custard_Syntax.TVariant cs ->
            let uu___1 =
              let uu___2 =
                let uu___3 =
                  FStarC_List.map
                    (fun uu___4 ->
                       match uu___4 with
                       | (cn, fs) ->
                           let uu___5 = ctor_name cn in
                           let uu___6 =
                             FStarC_List.map
                               (fun uu___7 ->
                                  match uu___7 with
                                  | (f, c) ->
                                      let uu___8 =
                                        let uu___9 = krml_typ env1 c in
                                        (uu___9, false) in
                                      (f, uu___8)) fs in
                           (uu___5, uu___6)) cs in
                (lid, flags, n_t, uu___3) in
              FStarC_Extraction_KrmlAst.DTypeVariant uu___2 in
            FStar_Pervasives_Native.Some uu___1
        | FStarC_Custard_Syntax.TAbstract ->
            let uu___1 =
              FStarC_List.existsb FStarC_Custard_Syntax.uu___is_Extern
                t.FStarC_Custard_Syntax.dt_flags in
            if uu___1
            then FStar_Pervasives_Native.None
            else
              FStar_Pervasives_Native.Some
                (FStarC_Extraction_KrmlAst.DTypeAbstractStruct lid))
   | FStarC_Custard_Syntax.DExternal x when
       if
         match x.FStarC_Custard_Syntax.dx_target with
         | FStar_Pervasives_Native.None -> true
         | uu___1 -> false
       then karamel_declares x.FStarC_Custard_Syntax.dx_name
       else false -> FStar_Pervasives_Native.None
   | FStarC_Custard_Syntax.DExternal x ->
       let lid =
         match x.FStarC_Custard_Syntax.dx_target with
         | FStar_Pervasives_Native.Some t -> ([], t)
         | FStar_Pervasives_Native.None ->
             lident_of_name x.FStarC_Custard_Syntax.dx_name in
       let env1 =
         let uu___1 =
           FStarC_Custard_Syntax.has_flag x.FStarC_Custard_Syntax.dx_flags
             FStarC_Custard_Syntax.Modelled in
         if uu___1
         then with_typars env x.FStarC_Custard_Syntax.dx_typars
         else
           {
             names = (env.names);
             names_t = (env.names_t);
             ctor_arity = (env.ctor_arity);
             tvars_any = true
           } in
       ((let uu___2 =
           let uu___3 =
             FStarC_Custard_Syntax.has_flag x.FStarC_Custard_Syntax.dx_flags
               FStarC_Custard_Syntax.Modelled in
           if uu___3
           then
             let uu___4 =
               FStarC_Custard_Builtins.is_known_krml_model_op
                 (x.FStarC_Custard_Syntax.dx_name).FStarC_Custard_Syntax.ns
                 (x.FStarC_Custard_Syntax.dx_name).FStarC_Custard_Syntax.id in
             Prims.not uu___4
           else false in
         if uu___2
         then
           let uu___3 =
             let uu___4 =
               let uu___5 =
                 let uu___6 =
                   let uu___7 =
                     FStarC_Custard_Syntax.string_of_name
                       x.FStarC_Custard_Syntax.dx_name in
                   Prims.strcat uu___7
                     " is in a module karamel models on this backend, but karamel has no translation for it." in
                 Prims.strcat "Custard: " uu___6 in
               FStarC_Errors_Msg.text uu___5 in
             [uu___4;
             FStarC_Errors_Msg.text
               "Only the operations karamel recognizes can be used from a modelled module; use the F* definition through --custard_backend KrmlC, or extend the model in karamel."] in
           FStarC_Errors.raise_error0
             FStarC_Errors_Codes.Fatal_ExtractionUnsupported ()
             (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
             (Obj.magic uu___3)
         else ());
        (let flags =
           let uu___2 = krml_flags x.FStarC_Custard_Syntax.dx_flags in
           FStarC_List.op_At uu___2
             (match x.FStarC_Custard_Syntax.dx_header with
              | FStar_Pervasives_Native.Some h ->
                  [FStarC_Extraction_KrmlAst.Prologue
                     (Prims.strcat "#include \"" (Prims.strcat h "\""))]
              | FStar_Pervasives_Native.None -> []) in
         let uu___2 =
           let uu___3 =
             let uu___4 = krml_typ env1 x.FStarC_Custard_Syntax.dx_ty in
             (FStar_Pervasives_Native.None, flags, lid, uu___4, []) in
           FStarC_Extraction_KrmlAst.DExternal uu___3 in
         FStar_Pervasives_Native.Some uu___2))
   | FStarC_Custard_Syntax.DExn e ->
       ((let uu___2 =
           let uu___3 =
             let uu___4 =
               let uu___5 =
                 let uu___6 =
                   FStarC_Custard_Syntax.string_of_name
                     e.FStarC_Custard_Syntax.de_name in
                 Prims.strcat uu___6
                   " has no karamel counterpart and was dropped." in
               Prims.strcat "Custard: the exception " uu___5 in
             FStarC_Errors_Msg.text uu___4 in
           [uu___3] in
         FStarC_Errors.log_issue0
           FStarC_Errors_Codes.Warning_DefinitionNotTranslated ()
           (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
           (Obj.magic uu___2));
        FStar_Pervasives_Native.None))
let ctor_table (p : FStarC_Custard_Syntax.program) : Prims.int FStarC_SMap.t=
  let t = FStarC_SMap.create (Prims.of_int 100) in
  FStarC_List.iter
    (fun d ->
       match d with
       | FStarC_Custard_Syntax.DType
           { FStarC_Custard_Syntax.dt_name = uu___1;
             FStarC_Custard_Syntax.dt_params = uu___2;
             FStarC_Custard_Syntax.dt_body = FStarC_Custard_Syntax.TVariant
               cs;
             FStarC_Custard_Syntax.dt_flags = uu___3;_}
           ->
           FStarC_List.iter
             (fun uu___4 ->
                match uu___4 with
                | (cn, fs) ->
                    let uu___5 = FStarC_Custard_Syntax.mangled_name cn in
                    FStarC_SMap.add t uu___5 (FStarC_List.length fs)) cs
       | uu___1 -> ()) p;
  t
let extern_type_table (p : FStarC_Custard_Syntax.program) :
  Prims.string FStarC_SMap.t=
  let t = FStarC_SMap.create (Prims.of_int 20) in
  FStarC_List.iter
    (fun d ->
       match d with
       | FStarC_Custard_Syntax.DType ty ->
           FStarC_List.iter
             (fun f ->
                match f with
                | FStarC_Custard_Syntax.Extern
                    (FStar_Pervasives_Native.Some target, uu___1) ->
                    let uu___2 =
                      FStarC_Custard_Syntax.string_of_name
                        ty.FStarC_Custard_Syntax.dt_name in
                    FStarC_SMap.add t uu___2 target
                | uu___1 -> ()) ty.FStarC_Custard_Syntax.dt_flags
       | uu___1 -> ()) p;
  t
let extern_value_table (p : FStarC_Custard_Syntax.program) :
  Prims.string FStarC_SMap.t=
  let t = FStarC_SMap.create (Prims.of_int 20) in
  FStarC_List.iter
    (fun d ->
       match d with
       | FStarC_Custard_Syntax.DExternal x ->
           (match x.FStarC_Custard_Syntax.dx_target with
            | FStar_Pervasives_Native.Some target when target <> "" ->
                let uu___1 =
                  FStarC_Custard_Syntax.string_of_name
                    x.FStarC_Custard_Syntax.dx_name in
                FStarC_SMap.add t uu___1 target
            | uu___1 -> ())
       | uu___1 -> ()) p;
  t
let krml_file_name (m : Prims.string) : Prims.string=
  FStarC_String.concat "_" (FStarC_String.split [46] m)
let decls_of (p : FStarC_Custard_Syntax.program) :
  FStarC_Extraction_KrmlAst.decl Prims.list=
  let env =
    let uu___ = ctor_table p in
    { names = []; names_t = []; ctor_arity = uu___; tvars_any = false } in
  FStarC_List.collect
    (fun d ->
       let uu___ = krml_decl env d in
       match uu___ with
       | FStar_Pervasives_Native.Some d1 -> [d1]
       | FStar_Pervasives_Native.None -> []) p
let shadow_table (p : FStarC_Custard_Syntax.program) :
  Prims.bool FStarC_SMap.t=
  let t = FStarC_SMap.create (Prims.of_int 20) in
  let emits d =
    let uu___ =
      let uu___1 = FStarC_Custard_Syntax.imported_unit d in
      match uu___1 with
      | FStar_Pervasives_Native.None -> true
      | uu___2 -> false in
    if uu___
    then
      match d with
      | FStarC_Custard_Syntax.DExternal uu___1 -> false
      | FStarC_Custard_Syntax.DType ty ->
          let uu___1 =
            let uu___2 =
              FStarC_Custard_Syntax.has_flag
                ty.FStarC_Custard_Syntax.dt_flags
                FStarC_Custard_Syntax.Realized in
            Prims.not uu___2 in
          (if uu___1
           then
             let uu___2 =
               FStarC_Custard_Syntax.has_flag
                 ty.FStarC_Custard_Syntax.dt_flags
                 FStarC_Custard_Syntax.Modelled in
             Prims.not uu___2
           else false)
      | uu___1 -> true
    else false in
  FStarC_List.iter
    (fun d ->
       let n = FStarC_Custard_Syntax.name_of_decl d in
       let uu___1 =
         let uu___2 = emits d in
         if uu___2
         then
           FStarC_Custard_Builtins.is_realized_module
             n.FStarC_Custard_Syntax.ns
         else false in
       if uu___1
       then
         let uu___2 = FStarC_Custard_Syntax.string_of_name n in
         FStarC_SMap.add t uu___2 true
       else ()) p;
  t
let reject_target_only_types (p : FStarC_Custard_Syntax.program) : unit=
  FStarC_List.iter
    (fun d ->
       match d with
       | FStarC_Custard_Syntax.DType ty ->
           FStarC_List.iter
             (fun f ->
                match f with
                | FStarC_Custard_Syntax.Extern
                    (FStar_Pervasives_Native.Some target, uu___) when
                    let uu___1 =
                      FStarC_Custard_Syntax.template_of_string target in
                    FStarC_Custard_Syntax.is_template uu___1 ->
                    let uu___1 =
                      let uu___2 =
                        let uu___3 =
                          let uu___4 =
                            let uu___5 =
                              FStarC_Custard_Syntax.string_of_name
                                ty.FStarC_Custard_Syntax.dt_name in
                            Prims.strcat uu___5
                              " has a template target, and templates reached the karamel backend." in
                          Prims.strcat "Custard: the external type " uu___4 in
                        FStarC_Errors_Msg.text uu___3 in
                      [uu___2;
                      FStarC_Errors_Msg.text
                        (Prims.strcat "Its target spelling ["
                           (Prims.strcat target
                              "] has a placeholder for an argument, so two instantiations of it are two different target types; karamel has no such construction.  Section 69 is a C-backend feature (--custard_backend C)."));
                      FStarC_Errors_Msg.text
                        "The unparameterized form still works everywhere: a [@@custard_extern] target with no [{0}] placeholder names one target type, and its arguments are dropped."] in
                    FStarC_Errors.raise_error0
                      FStarC_Errors_Codes.Error_CustardBadTemplateArg ()
                      (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
                      (Obj.magic uu___1)
                | FStarC_Custard_Syntax.CReference ->
                    let uu___ =
                      let uu___1 =
                        let uu___2 =
                          let uu___3 =
                            let uu___4 =
                              FStarC_Custard_Syntax.string_of_name
                                ty.FStarC_Custard_Syntax.dt_name in
                            Prims.strcat uu___4
                              " is [@@custard_c_reference], and reference bindings reached the karamel backend." in
                          Prims.strcat "Custard: the external type " uu___3 in
                        FStarC_Errors_Msg.text uu___2 in
                      [uu___1;
                      FStarC_Errors_Msg.text
                        "The attribute says that values of the type are handles, so a binding of one has to alias rather than copy -- which is C++ [T &x = ...], and karamel has no way to spell it.  Emitting a copy instead would compile and be wrong, which is the exact failure the attribute exists to prevent.";
                      FStarC_Errors_Msg.text
                        "Section 70.2 is a C-backend feature (--custard_backend C)."] in
                    FStarC_Errors.raise_error0
                      FStarC_Errors_Codes.Error_CustardBadReference ()
                      (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
                      (Obj.magic uu___)
                | uu___ -> ()) ty.FStarC_Custard_Syntax.dt_flags
       | uu___ -> ()) p
let print_program (p : FStarC_Custard_Syntax.program) :
  FStarC_Extraction_Krml.file Prims.list=
  reject_target_only_types p;
  (let uu___2 = extern_type_table p in
   FStarC_Effect.op_Colon_Equals extern_types uu___2);
  (let uu___3 = extern_value_table p in
   FStarC_Effect.op_Colon_Equals extern_values uu___3);
  (let uu___4 = shadow_table p in
   FStarC_Effect.op_Colon_Equals shadowed uu___4);
  (let uu___5 = rec_type_table p in
   FStarC_Effect.op_Colon_Equals rec_types uu___5);
  (let uu___6 = dead_abbrev_table p in
   FStarC_Effect.op_Colon_Equals dead_abbrevs uu___6);
  (let uu___6 = let uu___7 = decls_of p in ("Custard", uu___7) in [uu___6])
let print_split
  (fs : (Prims.string * FStarC_Custard_Syntax.program) Prims.list) :
  FStarC_Extraction_Krml.file Prims.list=
  let whole = FStarC_List.collect FStar_Pervasives_Native.snd fs in
  reject_target_only_types whole;
  (let uu___2 = extern_type_table whole in
   FStarC_Effect.op_Colon_Equals extern_types uu___2);
  (let uu___3 = extern_value_table whole in
   FStarC_Effect.op_Colon_Equals extern_values uu___3);
  (let uu___4 = shadow_table whole in
   FStarC_Effect.op_Colon_Equals shadowed uu___4);
  (let uu___5 = rec_type_table whole in
   FStarC_Effect.op_Colon_Equals rec_types uu___5);
  (let uu___6 = dead_abbrev_table whole in
   FStarC_Effect.op_Colon_Equals dead_abbrevs uu___6);
  (let arity = ctor_table whole in
   FStarC_List.collect
     (fun uu___6 ->
        match uu___6 with
        | (m, p) ->
            let env =
              {
                names = [];
                names_t = [];
                ctor_arity = arity;
                tvars_any = false
              } in
            let ds =
              FStarC_List.collect
                (fun d ->
                   let uu___7 = krml_decl env d in
                   match uu___7 with
                   | FStar_Pervasives_Native.Some d1 -> [d1]
                   | FStar_Pervasives_Native.None -> []) p in
            let uu___7 = let uu___8 = krml_file_name m in (uu___8, ds) in
            [uu___7]) fs)
let write_files (fn : Prims.string)
  (fs : FStarC_Extraction_Krml.file Prims.list) : unit=
  let bin = (FStarC_Extraction_Krml.current_version, fs) in
  FStarC_Util.save_value_to_file fn bin
let write_program (fn : Prims.string) (p : FStarC_Custard_Syntax.program) :
  unit= let uu___ = print_program p in write_files fn uu___
