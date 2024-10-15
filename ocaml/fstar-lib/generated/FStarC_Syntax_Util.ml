open Prims
let (tts_f :
  (FStarC_Syntax_Syntax.term -> Prims.string) FStar_Pervasives_Native.option
    FStarC_Compiler_Effect.ref)
  = FStarC_Compiler_Util.mk_ref FStar_Pervasives_Native.None
let (tts : FStarC_Syntax_Syntax.term -> Prims.string) =
  fun t ->
    let uu___ = FStarC_Compiler_Effect.op_Bang tts_f in
    match uu___ with
    | FStar_Pervasives_Native.None -> "<<hook unset>>"
    | FStar_Pervasives_Native.Some f -> f t
let (ttd_f :
  (FStarC_Syntax_Syntax.term -> FStarC_Pprint.document)
    FStar_Pervasives_Native.option FStarC_Compiler_Effect.ref)
  = FStarC_Compiler_Util.mk_ref FStar_Pervasives_Native.None
let (ttd : FStarC_Syntax_Syntax.term -> FStarC_Pprint.document) =
  fun t ->
    let uu___ = FStarC_Compiler_Effect.op_Bang ttd_f in
    match uu___ with
    | FStar_Pervasives_Native.None ->
        FStarC_Pprint.doc_of_string "<<hook unset>>"
    | FStar_Pervasives_Native.Some f -> f t
let (mk_discriminator : FStarC_Ident.lident -> FStarC_Ident.lident) =
  fun lid ->
    let uu___ =
      let uu___1 = FStarC_Ident.ns_of_lid lid in
      let uu___2 =
        let uu___3 =
          let uu___4 =
            let uu___5 =
              let uu___6 =
                let uu___7 =
                  let uu___8 = FStarC_Ident.ident_of_lid lid in
                  FStarC_Ident.string_of_id uu___8 in
                Prims.strcat "is_" uu___7 in
              Prims.strcat FStarC_Ident.reserved_prefix uu___6 in
            let uu___6 = FStarC_Ident.range_of_lid lid in (uu___5, uu___6) in
          FStarC_Ident.mk_ident uu___4 in
        [uu___3] in
      FStarC_Compiler_List.op_At uu___1 uu___2 in
    FStarC_Ident.lid_of_ids uu___
let (is_name : FStarC_Ident.lident -> Prims.bool) =
  fun lid ->
    let c =
      let uu___ =
        let uu___1 = FStarC_Ident.ident_of_lid lid in
        FStarC_Ident.string_of_id uu___1 in
      FStarC_Compiler_Util.char_at uu___ Prims.int_zero in
    FStarC_Compiler_Util.is_upper c
let (aqual_of_binder :
  FStarC_Syntax_Syntax.binder -> FStarC_Syntax_Syntax.aqual) =
  fun b ->
    match ((b.FStarC_Syntax_Syntax.binder_qual),
            (b.FStarC_Syntax_Syntax.binder_attrs))
    with
    | (FStar_Pervasives_Native.Some (FStarC_Syntax_Syntax.Implicit uu___),
       uu___1) ->
        FStar_Pervasives_Native.Some
          {
            FStarC_Syntax_Syntax.aqual_implicit = true;
            FStarC_Syntax_Syntax.aqual_attributes =
              (b.FStarC_Syntax_Syntax.binder_attrs)
          }
    | (FStar_Pervasives_Native.Some (FStarC_Syntax_Syntax.Meta uu___),
       uu___1) ->
        FStar_Pervasives_Native.Some
          {
            FStarC_Syntax_Syntax.aqual_implicit = true;
            FStarC_Syntax_Syntax.aqual_attributes =
              (b.FStarC_Syntax_Syntax.binder_attrs)
          }
    | (uu___, uu___1::uu___2) ->
        FStar_Pervasives_Native.Some
          {
            FStarC_Syntax_Syntax.aqual_implicit = false;
            FStarC_Syntax_Syntax.aqual_attributes =
              (b.FStarC_Syntax_Syntax.binder_attrs)
          }
    | uu___ -> FStar_Pervasives_Native.None
let (bqual_and_attrs_of_aqual :
  FStarC_Syntax_Syntax.aqual ->
    (FStarC_Syntax_Syntax.bqual * FStarC_Syntax_Syntax.attribute Prims.list))
  =
  fun a ->
    match a with
    | FStar_Pervasives_Native.None -> (FStar_Pervasives_Native.None, [])
    | FStar_Pervasives_Native.Some a1 ->
        ((if a1.FStarC_Syntax_Syntax.aqual_implicit
          then FStar_Pervasives_Native.Some FStarC_Syntax_Syntax.imp_tag
          else FStar_Pervasives_Native.None),
          (a1.FStarC_Syntax_Syntax.aqual_attributes))
let (arg_of_non_null_binder :
  FStarC_Syntax_Syntax.binder ->
    (FStarC_Syntax_Syntax.term * FStarC_Syntax_Syntax.aqual))
  =
  fun b ->
    let uu___ =
      FStarC_Syntax_Syntax.bv_to_name b.FStarC_Syntax_Syntax.binder_bv in
    let uu___1 = aqual_of_binder b in (uu___, uu___1)
let (args_of_non_null_binders :
  FStarC_Syntax_Syntax.binders ->
    (FStarC_Syntax_Syntax.term * FStarC_Syntax_Syntax.aqual) Prims.list)
  =
  fun binders ->
    FStarC_Compiler_List.collect
      (fun b ->
         let uu___ = FStarC_Syntax_Syntax.is_null_binder b in
         if uu___
         then []
         else (let uu___2 = arg_of_non_null_binder b in [uu___2])) binders
let (args_of_binders :
  FStarC_Syntax_Syntax.binders ->
    (FStarC_Syntax_Syntax.binders * FStarC_Syntax_Syntax.args))
  =
  fun binders ->
    let uu___ =
      FStarC_Compiler_List.map
        (fun b ->
           let uu___1 = FStarC_Syntax_Syntax.is_null_binder b in
           if uu___1
           then
             let b1 =
               let uu___2 =
                 FStarC_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                   (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
               {
                 FStarC_Syntax_Syntax.binder_bv = uu___2;
                 FStarC_Syntax_Syntax.binder_qual =
                   (b.FStarC_Syntax_Syntax.binder_qual);
                 FStarC_Syntax_Syntax.binder_positivity =
                   (b.FStarC_Syntax_Syntax.binder_positivity);
                 FStarC_Syntax_Syntax.binder_attrs =
                   (b.FStarC_Syntax_Syntax.binder_attrs)
               } in
             let uu___2 = arg_of_non_null_binder b1 in (b1, uu___2)
           else (let uu___3 = arg_of_non_null_binder b in (b, uu___3)))
        binders in
    FStarC_Compiler_List.unzip uu___
let (name_binders :
  FStarC_Syntax_Syntax.binder Prims.list ->
    FStarC_Syntax_Syntax.binder Prims.list)
  =
  fun binders ->
    FStarC_Compiler_List.mapi
      (fun i ->
         fun b ->
           let uu___ = FStarC_Syntax_Syntax.is_null_binder b in
           if uu___
           then
             let bname =
               let uu___1 =
                 let uu___2 = FStarC_Compiler_Util.string_of_int i in
                 Prims.strcat "_" uu___2 in
               FStarC_Ident.id_of_text uu___1 in
             let bv =
               {
                 FStarC_Syntax_Syntax.ppname = bname;
                 FStarC_Syntax_Syntax.index = Prims.int_zero;
                 FStarC_Syntax_Syntax.sort =
                   ((b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort)
               } in
             {
               FStarC_Syntax_Syntax.binder_bv = bv;
               FStarC_Syntax_Syntax.binder_qual =
                 (b.FStarC_Syntax_Syntax.binder_qual);
               FStarC_Syntax_Syntax.binder_positivity =
                 (b.FStarC_Syntax_Syntax.binder_positivity);
               FStarC_Syntax_Syntax.binder_attrs =
                 (b.FStarC_Syntax_Syntax.binder_attrs)
             }
           else b) binders
let (name_function_binders :
  FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax ->
    FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax)
  =
  fun t ->
    match t.FStarC_Syntax_Syntax.n with
    | FStarC_Syntax_Syntax.Tm_arrow
        { FStarC_Syntax_Syntax.bs1 = binders;
          FStarC_Syntax_Syntax.comp = comp;_}
        ->
        let uu___ =
          let uu___1 =
            let uu___2 = name_binders binders in
            {
              FStarC_Syntax_Syntax.bs1 = uu___2;
              FStarC_Syntax_Syntax.comp = comp
            } in
          FStarC_Syntax_Syntax.Tm_arrow uu___1 in
        FStarC_Syntax_Syntax.mk uu___ t.FStarC_Syntax_Syntax.pos
    | uu___ -> t
let (null_binders_of_tks :
  (FStarC_Syntax_Syntax.typ * FStarC_Syntax_Syntax.bqual) Prims.list ->
    FStarC_Syntax_Syntax.binders)
  =
  fun tks ->
    FStarC_Compiler_List.map
      (fun uu___ ->
         match uu___ with
         | (t, imp) ->
             let uu___1 = FStarC_Syntax_Syntax.null_binder t in
             {
               FStarC_Syntax_Syntax.binder_bv =
                 (uu___1.FStarC_Syntax_Syntax.binder_bv);
               FStarC_Syntax_Syntax.binder_qual = imp;
               FStarC_Syntax_Syntax.binder_positivity =
                 (uu___1.FStarC_Syntax_Syntax.binder_positivity);
               FStarC_Syntax_Syntax.binder_attrs =
                 (uu___1.FStarC_Syntax_Syntax.binder_attrs)
             }) tks
let (binders_of_tks :
  (FStarC_Syntax_Syntax.typ * FStarC_Syntax_Syntax.bqual) Prims.list ->
    FStarC_Syntax_Syntax.binders)
  =
  fun tks ->
    FStarC_Compiler_List.map
      (fun uu___ ->
         match uu___ with
         | (t, imp) ->
             let uu___1 =
               FStarC_Syntax_Syntax.new_bv
                 (FStar_Pervasives_Native.Some (t.FStarC_Syntax_Syntax.pos))
                 t in
             FStarC_Syntax_Syntax.mk_binder_with_attrs uu___1 imp
               FStar_Pervasives_Native.None []) tks
let mk_subst : 'uuuuu . 'uuuuu -> 'uuuuu Prims.list = fun s -> [s]
let (subst_of_list :
  FStarC_Syntax_Syntax.binders ->
    FStarC_Syntax_Syntax.args -> FStarC_Syntax_Syntax.subst_t)
  =
  fun formals ->
    fun actuals ->
      if
        (FStarC_Compiler_List.length formals) =
          (FStarC_Compiler_List.length actuals)
      then
        FStarC_Compiler_List.fold_right2
          (fun f ->
             fun a ->
               fun out ->
                 (FStarC_Syntax_Syntax.NT
                    ((f.FStarC_Syntax_Syntax.binder_bv),
                      (FStar_Pervasives_Native.fst a)))
                 :: out) formals actuals []
      else failwith "Ill-formed substitution"
let (rename_binders :
  FStarC_Syntax_Syntax.binders ->
    FStarC_Syntax_Syntax.binders -> FStarC_Syntax_Syntax.subst_t)
  =
  fun replace_xs ->
    fun with_ys ->
      if
        (FStarC_Compiler_List.length replace_xs) =
          (FStarC_Compiler_List.length with_ys)
      then
        FStarC_Compiler_List.map2
          (fun x ->
             fun y ->
               let uu___ =
                 let uu___1 =
                   FStarC_Syntax_Syntax.bv_to_name
                     y.FStarC_Syntax_Syntax.binder_bv in
                 ((x.FStarC_Syntax_Syntax.binder_bv), uu___1) in
               FStarC_Syntax_Syntax.NT uu___) replace_xs with_ys
      else failwith "Ill-formed substitution"
let rec (unmeta : FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term) =
  fun e ->
    let e1 = FStarC_Syntax_Subst.compress e in
    match e1.FStarC_Syntax_Syntax.n with
    | FStarC_Syntax_Syntax.Tm_meta
        { FStarC_Syntax_Syntax.tm2 = e2; FStarC_Syntax_Syntax.meta = uu___;_}
        -> unmeta e2
    | FStarC_Syntax_Syntax.Tm_ascribed
        { FStarC_Syntax_Syntax.tm = e2; FStarC_Syntax_Syntax.asc = uu___;
          FStarC_Syntax_Syntax.eff_opt = uu___1;_}
        -> unmeta e2
    | uu___ -> e1
let rec (unmeta_safe :
  FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term) =
  fun e ->
    let e1 = FStarC_Syntax_Subst.compress e in
    match e1.FStarC_Syntax_Syntax.n with
    | FStarC_Syntax_Syntax.Tm_meta
        { FStarC_Syntax_Syntax.tm2 = e'; FStarC_Syntax_Syntax.meta = m;_} ->
        (match m with
         | FStarC_Syntax_Syntax.Meta_monadic uu___ -> e1
         | FStarC_Syntax_Syntax.Meta_monadic_lift uu___ -> e1
         | uu___ -> unmeta_safe e')
    | FStarC_Syntax_Syntax.Tm_ascribed
        { FStarC_Syntax_Syntax.tm = e2; FStarC_Syntax_Syntax.asc = uu___;
          FStarC_Syntax_Syntax.eff_opt = uu___1;_}
        -> unmeta_safe e2
    | uu___ -> e1
let (unmeta_lift : FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term) =
  fun t ->
    let uu___ =
      let uu___1 = FStarC_Syntax_Subst.compress t in
      uu___1.FStarC_Syntax_Syntax.n in
    match uu___ with
    | FStarC_Syntax_Syntax.Tm_meta
        { FStarC_Syntax_Syntax.tm2 = t1;
          FStarC_Syntax_Syntax.meta = FStarC_Syntax_Syntax.Meta_monadic_lift
            uu___1;_}
        -> t1
    | uu___1 -> t
let rec (univ_kernel :
  FStarC_Syntax_Syntax.universe ->
    (FStarC_Syntax_Syntax.universe * Prims.int))
  =
  fun u ->
    let uu___ = FStarC_Syntax_Subst.compress_univ u in
    match uu___ with
    | FStarC_Syntax_Syntax.U_unknown -> (u, Prims.int_zero)
    | FStarC_Syntax_Syntax.U_name uu___1 -> (u, Prims.int_zero)
    | FStarC_Syntax_Syntax.U_unif uu___1 -> (u, Prims.int_zero)
    | FStarC_Syntax_Syntax.U_max uu___1 -> (u, Prims.int_zero)
    | FStarC_Syntax_Syntax.U_zero -> (u, Prims.int_zero)
    | FStarC_Syntax_Syntax.U_succ u1 ->
        let uu___1 = univ_kernel u1 in
        (match uu___1 with | (k, n) -> (k, (n + Prims.int_one)))
    | FStarC_Syntax_Syntax.U_bvar i ->
        let uu___1 =
          let uu___2 =
            let uu___3 =
              FStarC_Class_Show.show FStarC_Class_Show.showable_int i in
            Prims.strcat uu___3 ")" in
          Prims.strcat "Imposible: univ_kernel (U_bvar " uu___2 in
        failwith uu___1
let (constant_univ_as_nat : FStarC_Syntax_Syntax.universe -> Prims.int) =
  fun u -> let uu___ = univ_kernel u in FStar_Pervasives_Native.snd uu___
let rec (compare_univs :
  FStarC_Syntax_Syntax.universe -> FStarC_Syntax_Syntax.universe -> Prims.int)
  =
  fun u1 ->
    fun u2 ->
      let rec compare_kernel uk1 uk2 =
        let uu___ =
          let uu___1 = FStarC_Syntax_Subst.compress_univ uk1 in
          let uu___2 = FStarC_Syntax_Subst.compress_univ uk2 in
          (uu___1, uu___2) in
        match uu___ with
        | (FStarC_Syntax_Syntax.U_bvar uu___1, uu___2) ->
            failwith "Impossible: compare_kernel bvar"
        | (uu___1, FStarC_Syntax_Syntax.U_bvar uu___2) ->
            failwith "Impossible: compare_kernel bvar"
        | (FStarC_Syntax_Syntax.U_succ uu___1, uu___2) ->
            failwith "Impossible: compare_kernel succ"
        | (uu___1, FStarC_Syntax_Syntax.U_succ uu___2) ->
            failwith "Impossible: compare_kernel succ"
        | (FStarC_Syntax_Syntax.U_unknown, FStarC_Syntax_Syntax.U_unknown) ->
            Prims.int_zero
        | (FStarC_Syntax_Syntax.U_unknown, uu___1) -> (Prims.of_int (-1))
        | (uu___1, FStarC_Syntax_Syntax.U_unknown) -> Prims.int_one
        | (FStarC_Syntax_Syntax.U_zero, FStarC_Syntax_Syntax.U_zero) ->
            Prims.int_zero
        | (FStarC_Syntax_Syntax.U_zero, uu___1) -> (Prims.of_int (-1))
        | (uu___1, FStarC_Syntax_Syntax.U_zero) -> Prims.int_one
        | (FStarC_Syntax_Syntax.U_name u11, FStarC_Syntax_Syntax.U_name u21)
            ->
            let uu___1 = FStarC_Ident.string_of_id u11 in
            let uu___2 = FStarC_Ident.string_of_id u21 in
            FStarC_Compiler_String.compare uu___1 uu___2
        | (FStarC_Syntax_Syntax.U_name uu___1, uu___2) -> (Prims.of_int (-1))
        | (uu___1, FStarC_Syntax_Syntax.U_name uu___2) -> Prims.int_one
        | (FStarC_Syntax_Syntax.U_unif u11, FStarC_Syntax_Syntax.U_unif u21)
            ->
            let uu___1 = FStarC_Syntax_Unionfind.univ_uvar_id u11 in
            let uu___2 = FStarC_Syntax_Unionfind.univ_uvar_id u21 in
            uu___1 - uu___2
        | (FStarC_Syntax_Syntax.U_unif uu___1, uu___2) -> (Prims.of_int (-1))
        | (uu___1, FStarC_Syntax_Syntax.U_unif uu___2) -> Prims.int_one
        | (FStarC_Syntax_Syntax.U_max us1, FStarC_Syntax_Syntax.U_max us2) ->
            let n1 = FStarC_Compiler_List.length us1 in
            let n2 = FStarC_Compiler_List.length us2 in
            if n1 <> n2
            then n1 - n2
            else
              (let copt =
                 let uu___2 = FStarC_Compiler_List.zip us1 us2 in
                 FStarC_Compiler_Util.find_map uu___2
                   (fun uu___3 ->
                      match uu___3 with
                      | (u11, u21) ->
                          let c = compare_univs u11 u21 in
                          if c <> Prims.int_zero
                          then FStar_Pervasives_Native.Some c
                          else FStar_Pervasives_Native.None) in
               match copt with
               | FStar_Pervasives_Native.None -> Prims.int_zero
               | FStar_Pervasives_Native.Some c -> c) in
      let uu___ = univ_kernel u1 in
      match uu___ with
      | (uk1, n1) ->
          let uu___1 = univ_kernel u2 in
          (match uu___1 with
           | (uk2, n2) ->
               let uu___2 = compare_kernel uk1 uk2 in
               (match uu___2 with
                | uu___3 when uu___3 = Prims.int_zero -> n1 - n2
                | n -> n))
let (eq_univs :
  FStarC_Syntax_Syntax.universe ->
    FStarC_Syntax_Syntax.universe -> Prims.bool)
  =
  fun u1 ->
    fun u2 -> let uu___ = compare_univs u1 u2 in uu___ = Prims.int_zero
let (eq_univs_list :
  FStarC_Syntax_Syntax.universes ->
    FStarC_Syntax_Syntax.universes -> Prims.bool)
  =
  fun us ->
    fun vs ->
      ((FStarC_Compiler_List.length us) = (FStarC_Compiler_List.length vs))
        && (FStarC_Compiler_List.forall2 eq_univs us vs)
let (ml_comp :
  FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax ->
    FStarC_Compiler_Range_Type.range -> FStarC_Syntax_Syntax.comp)
  =
  fun t ->
    fun r ->
      let uu___ =
        let uu___1 =
          let uu___2 = FStarC_Parser_Const.effect_ML_lid () in
          FStarC_Ident.set_lid_range uu___2 r in
        {
          FStarC_Syntax_Syntax.comp_univs = [FStarC_Syntax_Syntax.U_zero];
          FStarC_Syntax_Syntax.effect_name = uu___1;
          FStarC_Syntax_Syntax.result_typ = t;
          FStarC_Syntax_Syntax.effect_args = [];
          FStarC_Syntax_Syntax.flags = [FStarC_Syntax_Syntax.MLEFFECT]
        } in
      FStarC_Syntax_Syntax.mk_Comp uu___
let (comp_effect_name :
  FStarC_Syntax_Syntax.comp' FStarC_Syntax_Syntax.syntax ->
    FStarC_Ident.lident)
  =
  fun c ->
    match c.FStarC_Syntax_Syntax.n with
    | FStarC_Syntax_Syntax.Comp c1 -> c1.FStarC_Syntax_Syntax.effect_name
    | FStarC_Syntax_Syntax.Total uu___ -> FStarC_Parser_Const.effect_Tot_lid
    | FStarC_Syntax_Syntax.GTotal uu___ ->
        FStarC_Parser_Const.effect_GTot_lid
let (comp_flags :
  FStarC_Syntax_Syntax.comp' FStarC_Syntax_Syntax.syntax ->
    FStarC_Syntax_Syntax.cflag Prims.list)
  =
  fun c ->
    match c.FStarC_Syntax_Syntax.n with
    | FStarC_Syntax_Syntax.Total uu___ -> [FStarC_Syntax_Syntax.TOTAL]
    | FStarC_Syntax_Syntax.GTotal uu___ -> [FStarC_Syntax_Syntax.SOMETRIVIAL]
    | FStarC_Syntax_Syntax.Comp ct -> ct.FStarC_Syntax_Syntax.flags
let (comp_eff_name_res_and_args :
  FStarC_Syntax_Syntax.comp ->
    (FStarC_Ident.lident * FStarC_Syntax_Syntax.typ *
      FStarC_Syntax_Syntax.args))
  =
  fun c ->
    match c.FStarC_Syntax_Syntax.n with
    | FStarC_Syntax_Syntax.Total t ->
        (FStarC_Parser_Const.effect_Tot_lid, t, [])
    | FStarC_Syntax_Syntax.GTotal t ->
        (FStarC_Parser_Const.effect_GTot_lid, t, [])
    | FStarC_Syntax_Syntax.Comp c1 ->
        ((c1.FStarC_Syntax_Syntax.effect_name),
          (c1.FStarC_Syntax_Syntax.result_typ),
          (c1.FStarC_Syntax_Syntax.effect_args))
let (effect_indices_from_repr :
  FStarC_Syntax_Syntax.term ->
    Prims.bool ->
      FStarC_Compiler_Range_Type.range ->
        Prims.string -> FStarC_Syntax_Syntax.term Prims.list)
  =
  fun repr ->
    fun is_layered ->
      fun r ->
        fun err ->
          let err1 uu___ =
            FStarC_Errors.raise_error FStarC_Class_HasRange.hasRange_range r
              FStarC_Errors_Codes.Fatal_UnexpectedEffect ()
              (Obj.magic FStarC_Errors_Msg.is_error_message_string)
              (Obj.magic err) in
          let repr1 = FStarC_Syntax_Subst.compress repr in
          if is_layered
          then
            match repr1.FStarC_Syntax_Syntax.n with
            | FStarC_Syntax_Syntax.Tm_app
                { FStarC_Syntax_Syntax.hd = uu___;
                  FStarC_Syntax_Syntax.args = uu___1::is;_}
                -> FStarC_Compiler_List.map FStar_Pervasives_Native.fst is
            | uu___ -> err1 ()
          else
            (match repr1.FStarC_Syntax_Syntax.n with
             | FStarC_Syntax_Syntax.Tm_arrow
                 { FStarC_Syntax_Syntax.bs1 = uu___1;
                   FStarC_Syntax_Syntax.comp = c;_}
                 ->
                 let uu___2 = comp_eff_name_res_and_args c in
                 (match uu___2 with
                  | (uu___3, uu___4, args) ->
                      FStarC_Compiler_List.map FStar_Pervasives_Native.fst
                        args)
             | uu___1 -> err1 ())
let (destruct_comp :
  FStarC_Syntax_Syntax.comp_typ ->
    (FStarC_Syntax_Syntax.universe * FStarC_Syntax_Syntax.typ *
      FStarC_Syntax_Syntax.typ))
  =
  fun c ->
    let wp =
      match c.FStarC_Syntax_Syntax.effect_args with
      | (wp1, uu___)::[] -> wp1
      | uu___ ->
          let uu___1 =
            let uu___2 =
              FStarC_Ident.string_of_lid c.FStarC_Syntax_Syntax.effect_name in
            let uu___3 =
              FStarC_Compiler_Util.string_of_int
                (FStarC_Compiler_List.length
                   c.FStarC_Syntax_Syntax.effect_args) in
            FStarC_Compiler_Util.format2
              "Impossible: Got a computation %s with %s effect args" uu___2
              uu___3 in
          failwith uu___1 in
    let uu___ = FStarC_Compiler_List.hd c.FStarC_Syntax_Syntax.comp_univs in
    (uu___, (c.FStarC_Syntax_Syntax.result_typ), wp)
let (is_named_tot :
  FStarC_Syntax_Syntax.comp' FStarC_Syntax_Syntax.syntax -> Prims.bool) =
  fun c ->
    match c.FStarC_Syntax_Syntax.n with
    | FStarC_Syntax_Syntax.Comp c1 ->
        FStarC_Ident.lid_equals c1.FStarC_Syntax_Syntax.effect_name
          FStarC_Parser_Const.effect_Tot_lid
    | FStarC_Syntax_Syntax.Total uu___ -> true
    | FStarC_Syntax_Syntax.GTotal uu___ -> false
let (is_total_comp :
  FStarC_Syntax_Syntax.comp' FStarC_Syntax_Syntax.syntax -> Prims.bool) =
  fun c ->
    (FStarC_Ident.lid_equals (comp_effect_name c)
       FStarC_Parser_Const.effect_Tot_lid)
      ||
      (FStarC_Compiler_Util.for_some
         (fun uu___ ->
            match uu___ with
            | FStarC_Syntax_Syntax.TOTAL -> true
            | FStarC_Syntax_Syntax.RETURN -> true
            | uu___1 -> false) (comp_flags c))
let (is_partial_return :
  FStarC_Syntax_Syntax.comp' FStarC_Syntax_Syntax.syntax -> Prims.bool) =
  fun c ->
    FStarC_Compiler_Util.for_some
      (fun uu___ ->
         match uu___ with
         | FStarC_Syntax_Syntax.RETURN -> true
         | FStarC_Syntax_Syntax.PARTIAL_RETURN -> true
         | uu___1 -> false) (comp_flags c)
let (is_tot_or_gtot_comp :
  FStarC_Syntax_Syntax.comp' FStarC_Syntax_Syntax.syntax -> Prims.bool) =
  fun c ->
    (is_total_comp c) ||
      (FStarC_Ident.lid_equals FStarC_Parser_Const.effect_GTot_lid
         (comp_effect_name c))
let (is_pure_effect : FStarC_Ident.lident -> Prims.bool) =
  fun l ->
    ((FStarC_Ident.lid_equals l FStarC_Parser_Const.effect_Tot_lid) ||
       (FStarC_Ident.lid_equals l FStarC_Parser_Const.effect_PURE_lid))
      || (FStarC_Ident.lid_equals l FStarC_Parser_Const.effect_Pure_lid)
let (is_pure_comp :
  FStarC_Syntax_Syntax.comp' FStarC_Syntax_Syntax.syntax -> Prims.bool) =
  fun c ->
    match c.FStarC_Syntax_Syntax.n with
    | FStarC_Syntax_Syntax.Total uu___ -> true
    | FStarC_Syntax_Syntax.GTotal uu___ -> false
    | FStarC_Syntax_Syntax.Comp ct ->
        ((is_total_comp c) ||
           (is_pure_effect ct.FStarC_Syntax_Syntax.effect_name))
          ||
          (FStarC_Compiler_Util.for_some
             (fun uu___ ->
                match uu___ with
                | FStarC_Syntax_Syntax.LEMMA -> true
                | uu___1 -> false) ct.FStarC_Syntax_Syntax.flags)
let (is_ghost_effect : FStarC_Ident.lident -> Prims.bool) =
  fun l ->
    ((FStarC_Ident.lid_equals FStarC_Parser_Const.effect_GTot_lid l) ||
       (FStarC_Ident.lid_equals FStarC_Parser_Const.effect_GHOST_lid l))
      || (FStarC_Ident.lid_equals FStarC_Parser_Const.effect_Ghost_lid l)
let (is_div_effect : FStarC_Ident.lident -> Prims.bool) =
  fun l ->
    ((FStarC_Ident.lid_equals l FStarC_Parser_Const.effect_DIV_lid) ||
       (FStarC_Ident.lid_equals l FStarC_Parser_Const.effect_Div_lid))
      || (FStarC_Ident.lid_equals l FStarC_Parser_Const.effect_Dv_lid)
let (is_pure_or_ghost_comp :
  FStarC_Syntax_Syntax.comp' FStarC_Syntax_Syntax.syntax -> Prims.bool) =
  fun c -> (is_pure_comp c) || (is_ghost_effect (comp_effect_name c))
let (is_pure_or_ghost_effect : FStarC_Ident.lident -> Prims.bool) =
  fun l -> (is_pure_effect l) || (is_ghost_effect l)
let (is_pure_or_ghost_function : FStarC_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu___ =
      let uu___1 = FStarC_Syntax_Subst.compress t in
      uu___1.FStarC_Syntax_Syntax.n in
    match uu___ with
    | FStarC_Syntax_Syntax.Tm_arrow
        { FStarC_Syntax_Syntax.bs1 = uu___1; FStarC_Syntax_Syntax.comp = c;_}
        -> is_pure_or_ghost_comp c
    | uu___1 -> true
let (is_lemma_comp :
  FStarC_Syntax_Syntax.comp' FStarC_Syntax_Syntax.syntax -> Prims.bool) =
  fun c ->
    match c.FStarC_Syntax_Syntax.n with
    | FStarC_Syntax_Syntax.Comp ct ->
        FStarC_Ident.lid_equals ct.FStarC_Syntax_Syntax.effect_name
          FStarC_Parser_Const.effect_Lemma_lid
    | uu___ -> false
let (is_lemma : FStarC_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu___ =
      let uu___1 = FStarC_Syntax_Subst.compress t in
      uu___1.FStarC_Syntax_Syntax.n in
    match uu___ with
    | FStarC_Syntax_Syntax.Tm_arrow
        { FStarC_Syntax_Syntax.bs1 = uu___1; FStarC_Syntax_Syntax.comp = c;_}
        -> is_lemma_comp c
    | uu___1 -> false
let rec (head_of : FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term) =
  fun t ->
    let uu___ =
      let uu___1 = FStarC_Syntax_Subst.compress t in
      uu___1.FStarC_Syntax_Syntax.n in
    match uu___ with
    | FStarC_Syntax_Syntax.Tm_app
        { FStarC_Syntax_Syntax.hd = t1; FStarC_Syntax_Syntax.args = uu___1;_}
        -> head_of t1
    | FStarC_Syntax_Syntax.Tm_match
        { FStarC_Syntax_Syntax.scrutinee = t1;
          FStarC_Syntax_Syntax.ret_opt = uu___1;
          FStarC_Syntax_Syntax.brs = uu___2;
          FStarC_Syntax_Syntax.rc_opt1 = uu___3;_}
        -> head_of t1
    | FStarC_Syntax_Syntax.Tm_abs
        { FStarC_Syntax_Syntax.bs = uu___1; FStarC_Syntax_Syntax.body = t1;
          FStarC_Syntax_Syntax.rc_opt = uu___2;_}
        -> head_of t1
    | FStarC_Syntax_Syntax.Tm_ascribed
        { FStarC_Syntax_Syntax.tm = t1; FStarC_Syntax_Syntax.asc = uu___1;
          FStarC_Syntax_Syntax.eff_opt = uu___2;_}
        -> head_of t1
    | FStarC_Syntax_Syntax.Tm_meta
        { FStarC_Syntax_Syntax.tm2 = t1;
          FStarC_Syntax_Syntax.meta = uu___1;_}
        -> head_of t1
    | uu___1 -> t
let (head_and_args :
  FStarC_Syntax_Syntax.term ->
    (FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax *
      (FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax *
      FStarC_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
      Prims.list))
  =
  fun t ->
    let t1 = FStarC_Syntax_Subst.compress t in
    match t1.FStarC_Syntax_Syntax.n with
    | FStarC_Syntax_Syntax.Tm_app
        { FStarC_Syntax_Syntax.hd = head; FStarC_Syntax_Syntax.args = args;_}
        -> (head, args)
    | uu___ -> (t1, [])
let rec (__head_and_args_full :
  (FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax *
    FStarC_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
    Prims.list ->
    Prims.bool ->
      FStarC_Syntax_Syntax.term ->
        (FStarC_Syntax_Syntax.term * (FStarC_Syntax_Syntax.term'
          FStarC_Syntax_Syntax.syntax * FStarC_Syntax_Syntax.arg_qualifier
          FStar_Pervasives_Native.option) Prims.list))
  =
  fun acc ->
    fun unmeta1 ->
      fun t ->
        let t1 = FStarC_Syntax_Subst.compress t in
        match t1.FStarC_Syntax_Syntax.n with
        | FStarC_Syntax_Syntax.Tm_app
            { FStarC_Syntax_Syntax.hd = head;
              FStarC_Syntax_Syntax.args = args;_}
            ->
            __head_and_args_full (FStarC_Compiler_List.op_At args acc)
              unmeta1 head
        | FStarC_Syntax_Syntax.Tm_meta
            { FStarC_Syntax_Syntax.tm2 = tm;
              FStarC_Syntax_Syntax.meta = uu___;_}
            when unmeta1 -> __head_and_args_full acc unmeta1 tm
        | uu___ -> (t1, acc)
let (head_and_args_full :
  FStarC_Syntax_Syntax.term ->
    (FStarC_Syntax_Syntax.term * (FStarC_Syntax_Syntax.term'
      FStarC_Syntax_Syntax.syntax * FStarC_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list))
  = fun t -> __head_and_args_full [] false t
let (head_and_args_full_unmeta :
  FStarC_Syntax_Syntax.term ->
    (FStarC_Syntax_Syntax.term * (FStarC_Syntax_Syntax.term'
      FStarC_Syntax_Syntax.syntax * FStarC_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list))
  = fun t -> __head_and_args_full [] true t
let rec (leftmost_head :
  FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term) =
  fun t ->
    let t1 = FStarC_Syntax_Subst.compress t in
    match t1.FStarC_Syntax_Syntax.n with
    | FStarC_Syntax_Syntax.Tm_app
        { FStarC_Syntax_Syntax.hd = t0; FStarC_Syntax_Syntax.args = uu___;_}
        -> leftmost_head t0
    | FStarC_Syntax_Syntax.Tm_meta
        { FStarC_Syntax_Syntax.tm2 = t0;
          FStarC_Syntax_Syntax.meta = FStarC_Syntax_Syntax.Meta_pattern uu___;_}
        -> leftmost_head t0
    | FStarC_Syntax_Syntax.Tm_meta
        { FStarC_Syntax_Syntax.tm2 = t0;
          FStarC_Syntax_Syntax.meta = FStarC_Syntax_Syntax.Meta_named uu___;_}
        -> leftmost_head t0
    | FStarC_Syntax_Syntax.Tm_meta
        { FStarC_Syntax_Syntax.tm2 = t0;
          FStarC_Syntax_Syntax.meta = FStarC_Syntax_Syntax.Meta_labeled uu___;_}
        -> leftmost_head t0
    | FStarC_Syntax_Syntax.Tm_meta
        { FStarC_Syntax_Syntax.tm2 = t0;
          FStarC_Syntax_Syntax.meta = FStarC_Syntax_Syntax.Meta_desugared
            uu___;_}
        -> leftmost_head t0
    | FStarC_Syntax_Syntax.Tm_ascribed
        { FStarC_Syntax_Syntax.tm = t0; FStarC_Syntax_Syntax.asc = uu___;
          FStarC_Syntax_Syntax.eff_opt = uu___1;_}
        -> leftmost_head t0
    | uu___ -> t1
let (leftmost_head_and_args :
  FStarC_Syntax_Syntax.term ->
    (FStarC_Syntax_Syntax.term * (FStarC_Syntax_Syntax.term'
      FStarC_Syntax_Syntax.syntax * FStarC_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list))
  =
  fun t ->
    let rec aux t1 args =
      let t2 = FStarC_Syntax_Subst.compress t1 in
      match t2.FStarC_Syntax_Syntax.n with
      | FStarC_Syntax_Syntax.Tm_app
          { FStarC_Syntax_Syntax.hd = t0;
            FStarC_Syntax_Syntax.args = args';_}
          -> aux t0 (FStarC_Compiler_List.op_At args' args)
      | FStarC_Syntax_Syntax.Tm_meta
          { FStarC_Syntax_Syntax.tm2 = t0;
            FStarC_Syntax_Syntax.meta = FStarC_Syntax_Syntax.Meta_pattern
              uu___;_}
          -> aux t0 args
      | FStarC_Syntax_Syntax.Tm_meta
          { FStarC_Syntax_Syntax.tm2 = t0;
            FStarC_Syntax_Syntax.meta = FStarC_Syntax_Syntax.Meta_named uu___;_}
          -> aux t0 args
      | FStarC_Syntax_Syntax.Tm_meta
          { FStarC_Syntax_Syntax.tm2 = t0;
            FStarC_Syntax_Syntax.meta = FStarC_Syntax_Syntax.Meta_labeled
              uu___;_}
          -> aux t0 args
      | FStarC_Syntax_Syntax.Tm_meta
          { FStarC_Syntax_Syntax.tm2 = t0;
            FStarC_Syntax_Syntax.meta = FStarC_Syntax_Syntax.Meta_desugared
              uu___;_}
          -> aux t0 args
      | FStarC_Syntax_Syntax.Tm_ascribed
          { FStarC_Syntax_Syntax.tm = t0; FStarC_Syntax_Syntax.asc = uu___;
            FStarC_Syntax_Syntax.eff_opt = uu___1;_}
          -> aux t0 args
      | uu___ -> (t2, args) in
    aux t []
let (un_uinst : FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term) =
  fun t ->
    let t1 = FStarC_Syntax_Subst.compress t in
    match t1.FStarC_Syntax_Syntax.n with
    | FStarC_Syntax_Syntax.Tm_uinst (t2, uu___) ->
        FStarC_Syntax_Subst.compress t2
    | uu___ -> t1
let (is_ml_comp :
  FStarC_Syntax_Syntax.comp' FStarC_Syntax_Syntax.syntax -> Prims.bool) =
  fun c ->
    match c.FStarC_Syntax_Syntax.n with
    | FStarC_Syntax_Syntax.Comp c1 ->
        (let uu___ = FStarC_Parser_Const.effect_ML_lid () in
         FStarC_Ident.lid_equals c1.FStarC_Syntax_Syntax.effect_name uu___)
          ||
          (FStarC_Compiler_Util.for_some
             (fun uu___ ->
                match uu___ with
                | FStarC_Syntax_Syntax.MLEFFECT -> true
                | uu___1 -> false) c1.FStarC_Syntax_Syntax.flags)
    | uu___ -> false
let (comp_result :
  FStarC_Syntax_Syntax.comp' FStarC_Syntax_Syntax.syntax ->
    FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax)
  =
  fun c ->
    match c.FStarC_Syntax_Syntax.n with
    | FStarC_Syntax_Syntax.Total t -> t
    | FStarC_Syntax_Syntax.GTotal t -> t
    | FStarC_Syntax_Syntax.Comp ct -> ct.FStarC_Syntax_Syntax.result_typ
let (set_result_typ :
  FStarC_Syntax_Syntax.comp' FStarC_Syntax_Syntax.syntax ->
    FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax ->
      FStarC_Syntax_Syntax.comp)
  =
  fun c ->
    fun t ->
      match c.FStarC_Syntax_Syntax.n with
      | FStarC_Syntax_Syntax.Total uu___ -> FStarC_Syntax_Syntax.mk_Total t
      | FStarC_Syntax_Syntax.GTotal uu___ -> FStarC_Syntax_Syntax.mk_GTotal t
      | FStarC_Syntax_Syntax.Comp ct ->
          FStarC_Syntax_Syntax.mk_Comp
            {
              FStarC_Syntax_Syntax.comp_univs =
                (ct.FStarC_Syntax_Syntax.comp_univs);
              FStarC_Syntax_Syntax.effect_name =
                (ct.FStarC_Syntax_Syntax.effect_name);
              FStarC_Syntax_Syntax.result_typ = t;
              FStarC_Syntax_Syntax.effect_args =
                (ct.FStarC_Syntax_Syntax.effect_args);
              FStarC_Syntax_Syntax.flags = (ct.FStarC_Syntax_Syntax.flags)
            }
let (is_trivial_wp :
  FStarC_Syntax_Syntax.comp' FStarC_Syntax_Syntax.syntax -> Prims.bool) =
  fun c ->
    FStarC_Compiler_Util.for_some
      (fun uu___ ->
         match uu___ with
         | FStarC_Syntax_Syntax.TOTAL -> true
         | FStarC_Syntax_Syntax.RETURN -> true
         | uu___1 -> false) (comp_flags c)
let (comp_effect_args :
  FStarC_Syntax_Syntax.comp -> FStarC_Syntax_Syntax.args) =
  fun c ->
    match c.FStarC_Syntax_Syntax.n with
    | FStarC_Syntax_Syntax.Total uu___ -> []
    | FStarC_Syntax_Syntax.GTotal uu___ -> []
    | FStarC_Syntax_Syntax.Comp ct -> ct.FStarC_Syntax_Syntax.effect_args
let (primops : FStarC_Ident.lident Prims.list) =
  [FStarC_Parser_Const.op_Eq;
  FStarC_Parser_Const.op_notEq;
  FStarC_Parser_Const.op_LT;
  FStarC_Parser_Const.op_LTE;
  FStarC_Parser_Const.op_GT;
  FStarC_Parser_Const.op_GTE;
  FStarC_Parser_Const.op_Subtraction;
  FStarC_Parser_Const.op_Minus;
  FStarC_Parser_Const.op_Addition;
  FStarC_Parser_Const.op_Multiply;
  FStarC_Parser_Const.op_Division;
  FStarC_Parser_Const.op_Modulus;
  FStarC_Parser_Const.op_And;
  FStarC_Parser_Const.op_Or;
  FStarC_Parser_Const.op_Negation]
let (is_primop_lid : FStarC_Ident.lident -> Prims.bool) =
  fun l -> FStarC_Compiler_Util.for_some (FStarC_Ident.lid_equals l) primops
let (is_primop :
  FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax -> Prims.bool) =
  fun f ->
    match f.FStarC_Syntax_Syntax.n with
    | FStarC_Syntax_Syntax.Tm_fvar fv ->
        is_primop_lid
          (fv.FStarC_Syntax_Syntax.fv_name).FStarC_Syntax_Syntax.v
    | uu___ -> false
let rec (unascribe : FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term)
  =
  fun e ->
    let e1 = FStarC_Syntax_Subst.compress e in
    match e1.FStarC_Syntax_Syntax.n with
    | FStarC_Syntax_Syntax.Tm_ascribed
        { FStarC_Syntax_Syntax.tm = e2; FStarC_Syntax_Syntax.asc = uu___;
          FStarC_Syntax_Syntax.eff_opt = uu___1;_}
        -> unascribe e2
    | uu___ -> e1
let rec (ascribe :
  FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax ->
    ((FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax,
      FStarC_Syntax_Syntax.comp' FStarC_Syntax_Syntax.syntax)
      FStar_Pervasives.either * FStarC_Syntax_Syntax.term'
      FStarC_Syntax_Syntax.syntax FStar_Pervasives_Native.option *
      Prims.bool) -> FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax)
  =
  fun t ->
    fun k ->
      match t.FStarC_Syntax_Syntax.n with
      | FStarC_Syntax_Syntax.Tm_ascribed
          { FStarC_Syntax_Syntax.tm = t'; FStarC_Syntax_Syntax.asc = uu___;
            FStarC_Syntax_Syntax.eff_opt = uu___1;_}
          -> ascribe t' k
      | uu___ ->
          FStarC_Syntax_Syntax.mk
            (FStarC_Syntax_Syntax.Tm_ascribed
               {
                 FStarC_Syntax_Syntax.tm = t;
                 FStarC_Syntax_Syntax.asc = k;
                 FStarC_Syntax_Syntax.eff_opt = FStar_Pervasives_Native.None
               }) t.FStarC_Syntax_Syntax.pos
let (unfold_lazy :
  FStarC_Syntax_Syntax.lazyinfo -> FStarC_Syntax_Syntax.term) =
  fun i ->
    let uu___ =
      let uu___1 =
        FStarC_Compiler_Effect.op_Bang FStarC_Syntax_Syntax.lazy_chooser in
      FStarC_Compiler_Util.must uu___1 in
    uu___ i.FStarC_Syntax_Syntax.lkind i
let rec (unlazy : FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term) =
  fun t ->
    let uu___ =
      let uu___1 = FStarC_Syntax_Subst.compress t in
      uu___1.FStarC_Syntax_Syntax.n in
    match uu___ with
    | FStarC_Syntax_Syntax.Tm_lazy i ->
        let uu___1 = unfold_lazy i in unlazy uu___1
    | uu___1 -> t
let (unlazy_emb : FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term) =
  fun t ->
    let uu___ =
      let uu___1 = FStarC_Syntax_Subst.compress t in
      uu___1.FStarC_Syntax_Syntax.n in
    match uu___ with
    | FStarC_Syntax_Syntax.Tm_lazy i ->
        (match i.FStarC_Syntax_Syntax.lkind with
         | FStarC_Syntax_Syntax.Lazy_embedding uu___1 ->
             let uu___2 = unfold_lazy i in unlazy uu___2
         | uu___1 -> t)
    | uu___1 -> t
let unlazy_as_t :
  'uuuuu .
    FStarC_Syntax_Syntax.lazy_kind -> FStarC_Syntax_Syntax.term -> 'uuuuu
  =
  fun k ->
    fun t ->
      let uu___ =
        let uu___1 = FStarC_Syntax_Subst.compress t in
        uu___1.FStarC_Syntax_Syntax.n in
      match uu___ with
      | FStarC_Syntax_Syntax.Tm_lazy
          { FStarC_Syntax_Syntax.blob = v; FStarC_Syntax_Syntax.lkind = k';
            FStarC_Syntax_Syntax.ltyp = uu___1;
            FStarC_Syntax_Syntax.rng = uu___2;_}
          ->
          let uu___3 =
            FStarC_Class_Deq.op_Equals_Question
              FStarC_Syntax_Syntax.deq_lazy_kind k k' in
          if uu___3
          then FStarC_Dyn.undyn v
          else
            (let uu___5 =
               let uu___6 =
                 FStarC_Class_Show.show
                   FStarC_Syntax_Syntax.showable_lazy_kind k in
               let uu___7 =
                 FStarC_Class_Show.show
                   FStarC_Syntax_Syntax.showable_lazy_kind k' in
               FStarC_Compiler_Util.format2
                 "Expected Tm_lazy of kind %s, got %s" uu___6 uu___7 in
             failwith uu___5)
      | uu___1 -> failwith "Not a Tm_lazy of the expected kind"
let mk_lazy :
  'a .
    'a ->
      FStarC_Syntax_Syntax.typ ->
        FStarC_Syntax_Syntax.lazy_kind ->
          FStarC_Compiler_Range_Type.range FStar_Pervasives_Native.option ->
            FStarC_Syntax_Syntax.term
  =
  fun t ->
    fun typ ->
      fun k ->
        fun r ->
          let rng =
            match r with
            | FStar_Pervasives_Native.Some r1 -> r1
            | FStar_Pervasives_Native.None ->
                FStarC_Compiler_Range_Type.dummyRange in
          let i =
            let uu___ = FStarC_Dyn.mkdyn t in
            {
              FStarC_Syntax_Syntax.blob = uu___;
              FStarC_Syntax_Syntax.lkind = k;
              FStarC_Syntax_Syntax.ltyp = typ;
              FStarC_Syntax_Syntax.rng = rng
            } in
          FStarC_Syntax_Syntax.mk (FStarC_Syntax_Syntax.Tm_lazy i) rng
let (canon_app :
  FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax ->
    FStarC_Syntax_Syntax.term)
  =
  fun t ->
    let uu___ = let uu___1 = unascribe t in head_and_args_full uu___1 in
    match uu___ with
    | (hd, args) ->
        FStarC_Syntax_Syntax.mk_Tm_app hd args t.FStarC_Syntax_Syntax.pos
let rec (unrefine : FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term) =
  fun t ->
    let t1 = FStarC_Syntax_Subst.compress t in
    match t1.FStarC_Syntax_Syntax.n with
    | FStarC_Syntax_Syntax.Tm_refine
        { FStarC_Syntax_Syntax.b = x; FStarC_Syntax_Syntax.phi = uu___;_} ->
        unrefine x.FStarC_Syntax_Syntax.sort
    | FStarC_Syntax_Syntax.Tm_ascribed
        { FStarC_Syntax_Syntax.tm = t2; FStarC_Syntax_Syntax.asc = uu___;
          FStarC_Syntax_Syntax.eff_opt = uu___1;_}
        -> unrefine t2
    | uu___ -> t1
let rec (is_uvar : FStarC_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu___ =
      let uu___1 = FStarC_Syntax_Subst.compress t in
      uu___1.FStarC_Syntax_Syntax.n in
    match uu___ with
    | FStarC_Syntax_Syntax.Tm_uvar uu___1 -> true
    | FStarC_Syntax_Syntax.Tm_uinst (t1, uu___1) -> is_uvar t1
    | FStarC_Syntax_Syntax.Tm_app uu___1 ->
        let uu___2 =
          let uu___3 = head_and_args t in FStar_Pervasives_Native.fst uu___3 in
        is_uvar uu___2
    | FStarC_Syntax_Syntax.Tm_ascribed
        { FStarC_Syntax_Syntax.tm = t1; FStarC_Syntax_Syntax.asc = uu___1;
          FStarC_Syntax_Syntax.eff_opt = uu___2;_}
        -> is_uvar t1
    | uu___1 -> false
let rec (is_unit : FStarC_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu___ = let uu___1 = unrefine t in uu___1.FStarC_Syntax_Syntax.n in
    match uu___ with
    | FStarC_Syntax_Syntax.Tm_fvar fv ->
        ((FStarC_Syntax_Syntax.fv_eq_lid fv FStarC_Parser_Const.unit_lid) ||
           (FStarC_Syntax_Syntax.fv_eq_lid fv FStarC_Parser_Const.squash_lid))
          ||
          (FStarC_Syntax_Syntax.fv_eq_lid fv
             FStarC_Parser_Const.auto_squash_lid)
    | FStarC_Syntax_Syntax.Tm_app
        { FStarC_Syntax_Syntax.hd = head;
          FStarC_Syntax_Syntax.args = uu___1;_}
        -> is_unit head
    | FStarC_Syntax_Syntax.Tm_uinst (t1, uu___1) -> is_unit t1
    | uu___1 -> false
let (is_eqtype_no_unrefine : FStarC_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu___ =
      let uu___1 = FStarC_Syntax_Subst.compress t in
      uu___1.FStarC_Syntax_Syntax.n in
    match uu___ with
    | FStarC_Syntax_Syntax.Tm_fvar fv ->
        FStarC_Syntax_Syntax.fv_eq_lid fv FStarC_Parser_Const.eqtype_lid
    | uu___1 -> false
let (is_fun : FStarC_Syntax_Syntax.term -> Prims.bool) =
  fun e ->
    let uu___ =
      let uu___1 = FStarC_Syntax_Subst.compress e in
      uu___1.FStarC_Syntax_Syntax.n in
    match uu___ with
    | FStarC_Syntax_Syntax.Tm_abs uu___1 -> true
    | uu___1 -> false
let (is_function_typ : FStarC_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu___ =
      let uu___1 = FStarC_Syntax_Subst.compress t in
      uu___1.FStarC_Syntax_Syntax.n in
    match uu___ with
    | FStarC_Syntax_Syntax.Tm_arrow uu___1 -> true
    | uu___1 -> false
let rec (pre_typ : FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term) =
  fun t ->
    let t1 = FStarC_Syntax_Subst.compress t in
    match t1.FStarC_Syntax_Syntax.n with
    | FStarC_Syntax_Syntax.Tm_refine
        { FStarC_Syntax_Syntax.b = x; FStarC_Syntax_Syntax.phi = uu___;_} ->
        pre_typ x.FStarC_Syntax_Syntax.sort
    | FStarC_Syntax_Syntax.Tm_ascribed
        { FStarC_Syntax_Syntax.tm = t2; FStarC_Syntax_Syntax.asc = uu___;
          FStarC_Syntax_Syntax.eff_opt = uu___1;_}
        -> pre_typ t2
    | uu___ -> t1
let (destruct :
  FStarC_Syntax_Syntax.term ->
    FStarC_Ident.lident ->
      (FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax *
        FStarC_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
        Prims.list FStar_Pervasives_Native.option)
  =
  fun typ ->
    fun lid ->
      let typ1 = FStarC_Syntax_Subst.compress typ in
      let uu___ = let uu___1 = un_uinst typ1 in uu___1.FStarC_Syntax_Syntax.n in
      match uu___ with
      | FStarC_Syntax_Syntax.Tm_app
          { FStarC_Syntax_Syntax.hd = head;
            FStarC_Syntax_Syntax.args = args;_}
          ->
          let head1 = un_uinst head in
          (match head1.FStarC_Syntax_Syntax.n with
           | FStarC_Syntax_Syntax.Tm_fvar tc when
               FStarC_Syntax_Syntax.fv_eq_lid tc lid ->
               FStar_Pervasives_Native.Some args
           | uu___1 -> FStar_Pervasives_Native.None)
      | FStarC_Syntax_Syntax.Tm_fvar tc when
          FStarC_Syntax_Syntax.fv_eq_lid tc lid ->
          FStar_Pervasives_Native.Some []
      | uu___1 -> FStar_Pervasives_Native.None
let (lids_of_sigelt :
  FStarC_Syntax_Syntax.sigelt -> FStarC_Ident.lident Prims.list) =
  fun se ->
    match se.FStarC_Syntax_Syntax.sigel with
    | FStarC_Syntax_Syntax.Sig_let
        { FStarC_Syntax_Syntax.lbs1 = uu___;
          FStarC_Syntax_Syntax.lids1 = lids;_}
        -> lids
    | FStarC_Syntax_Syntax.Sig_splice
        { FStarC_Syntax_Syntax.is_typed = uu___;
          FStarC_Syntax_Syntax.lids2 = lids;
          FStarC_Syntax_Syntax.tac = uu___1;_}
        -> lids
    | FStarC_Syntax_Syntax.Sig_bundle
        { FStarC_Syntax_Syntax.ses = uu___;
          FStarC_Syntax_Syntax.lids = lids;_}
        -> lids
    | FStarC_Syntax_Syntax.Sig_inductive_typ
        { FStarC_Syntax_Syntax.lid = lid; FStarC_Syntax_Syntax.us = uu___;
          FStarC_Syntax_Syntax.params = uu___1;
          FStarC_Syntax_Syntax.num_uniform_params = uu___2;
          FStarC_Syntax_Syntax.t = uu___3;
          FStarC_Syntax_Syntax.mutuals = uu___4;
          FStarC_Syntax_Syntax.ds = uu___5;
          FStarC_Syntax_Syntax.injective_type_params = uu___6;_}
        -> [lid]
    | FStarC_Syntax_Syntax.Sig_effect_abbrev
        { FStarC_Syntax_Syntax.lid4 = lid; FStarC_Syntax_Syntax.us4 = uu___;
          FStarC_Syntax_Syntax.bs2 = uu___1;
          FStarC_Syntax_Syntax.comp1 = uu___2;
          FStarC_Syntax_Syntax.cflags = uu___3;_}
        -> [lid]
    | FStarC_Syntax_Syntax.Sig_datacon
        { FStarC_Syntax_Syntax.lid1 = lid; FStarC_Syntax_Syntax.us1 = uu___;
          FStarC_Syntax_Syntax.t1 = uu___1;
          FStarC_Syntax_Syntax.ty_lid = uu___2;
          FStarC_Syntax_Syntax.num_ty_params = uu___3;
          FStarC_Syntax_Syntax.mutuals1 = uu___4;
          FStarC_Syntax_Syntax.injective_type_params1 = uu___5;_}
        -> [lid]
    | FStarC_Syntax_Syntax.Sig_declare_typ
        { FStarC_Syntax_Syntax.lid2 = lid; FStarC_Syntax_Syntax.us2 = uu___;
          FStarC_Syntax_Syntax.t2 = uu___1;_}
        -> [lid]
    | FStarC_Syntax_Syntax.Sig_assume
        { FStarC_Syntax_Syntax.lid3 = lid; FStarC_Syntax_Syntax.us3 = uu___;
          FStarC_Syntax_Syntax.phi1 = uu___1;_}
        -> [lid]
    | FStarC_Syntax_Syntax.Sig_new_effect d -> [d.FStarC_Syntax_Syntax.mname]
    | FStarC_Syntax_Syntax.Sig_sub_effect uu___ -> []
    | FStarC_Syntax_Syntax.Sig_pragma uu___ -> []
    | FStarC_Syntax_Syntax.Sig_fail uu___ -> []
    | FStarC_Syntax_Syntax.Sig_polymonadic_bind uu___ -> []
    | FStarC_Syntax_Syntax.Sig_polymonadic_subcomp uu___ -> []
let (lid_of_sigelt :
  FStarC_Syntax_Syntax.sigelt ->
    FStarC_Ident.lident FStar_Pervasives_Native.option)
  =
  fun se ->
    match lids_of_sigelt se with
    | l::[] -> FStar_Pervasives_Native.Some l
    | uu___ -> FStar_Pervasives_Native.None
let (quals_of_sigelt :
  FStarC_Syntax_Syntax.sigelt -> FStarC_Syntax_Syntax.qualifier Prims.list) =
  fun x -> x.FStarC_Syntax_Syntax.sigquals
let (range_of_sigelt :
  FStarC_Syntax_Syntax.sigelt -> FStarC_Compiler_Range_Type.range) =
  fun x -> x.FStarC_Syntax_Syntax.sigrng
let range_of_arg :
  'uuuuu 'uuuuu1 .
    ('uuuuu FStarC_Syntax_Syntax.syntax * 'uuuuu1) ->
      FStarC_Compiler_Range_Type.range
  =
  fun uu___ -> match uu___ with | (hd, uu___1) -> hd.FStarC_Syntax_Syntax.pos
let range_of_args :
  'uuuuu 'uuuuu1 .
    ('uuuuu FStarC_Syntax_Syntax.syntax * 'uuuuu1) Prims.list ->
      FStarC_Compiler_Range_Type.range -> FStarC_Compiler_Range_Type.range
  =
  fun args ->
    fun r ->
      FStarC_Compiler_List.fold_left
        (fun r1 ->
           fun a ->
             FStarC_Compiler_Range_Ops.union_ranges r1 (range_of_arg a)) r
        args
let (mk_app :
  FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax ->
    (FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax *
      FStarC_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
      Prims.list -> FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax)
  =
  fun f ->
    fun args ->
      match args with
      | [] -> f
      | uu___ ->
          let r = range_of_args args f.FStarC_Syntax_Syntax.pos in
          FStarC_Syntax_Syntax.mk
            (FStarC_Syntax_Syntax.Tm_app
               {
                 FStarC_Syntax_Syntax.hd = f;
                 FStarC_Syntax_Syntax.args = args
               }) r
let (mk_app_binders :
  FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax ->
    FStarC_Syntax_Syntax.binder Prims.list ->
      FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax)
  =
  fun f ->
    fun bs ->
      let uu___ =
        FStarC_Compiler_List.map
          (fun b ->
             let uu___1 =
               FStarC_Syntax_Syntax.bv_to_name
                 b.FStarC_Syntax_Syntax.binder_bv in
             let uu___2 = aqual_of_binder b in (uu___1, uu___2)) bs in
      mk_app f uu___
let (field_projector_prefix : Prims.string) = "__proj__"
let (field_projector_sep : Prims.string) = "__item__"
let (field_projector_contains_constructor : Prims.string -> Prims.bool) =
  fun s -> FStarC_Compiler_Util.starts_with s field_projector_prefix
let (mk_field_projector_name_from_string :
  Prims.string -> Prims.string -> Prims.string) =
  fun constr ->
    fun field ->
      Prims.strcat field_projector_prefix
        (Prims.strcat constr (Prims.strcat field_projector_sep field))
let (mk_field_projector_name_from_ident :
  FStarC_Ident.lident -> FStarC_Ident.ident -> FStarC_Ident.lident) =
  fun lid ->
    fun i ->
      let itext = FStarC_Ident.string_of_id i in
      let newi =
        if field_projector_contains_constructor itext
        then i
        else
          (let uu___1 =
             let uu___2 =
               let uu___3 =
                 let uu___4 = FStarC_Ident.ident_of_lid lid in
                 FStarC_Ident.string_of_id uu___4 in
               mk_field_projector_name_from_string uu___3 itext in
             let uu___3 = FStarC_Ident.range_of_id i in (uu___2, uu___3) in
           FStarC_Ident.mk_ident uu___1) in
      let uu___ =
        let uu___1 = FStarC_Ident.ns_of_lid lid in
        FStarC_Compiler_List.op_At uu___1 [newi] in
      FStarC_Ident.lid_of_ids uu___
let (mk_field_projector_name :
  FStarC_Ident.lident ->
    FStarC_Syntax_Syntax.bv -> Prims.int -> FStarC_Ident.lident)
  =
  fun lid ->
    fun x ->
      fun i ->
        let nm =
          let uu___ = FStarC_Syntax_Syntax.is_null_bv x in
          if uu___
          then
            let uu___1 =
              let uu___2 =
                let uu___3 = FStarC_Compiler_Util.string_of_int i in
                Prims.strcat "_" uu___3 in
              let uu___3 = FStarC_Syntax_Syntax.range_of_bv x in
              (uu___2, uu___3) in
            FStarC_Ident.mk_ident uu___1
          else x.FStarC_Syntax_Syntax.ppname in
        mk_field_projector_name_from_ident lid nm
let (ses_of_sigbundle :
  FStarC_Syntax_Syntax.sigelt -> FStarC_Syntax_Syntax.sigelt Prims.list) =
  fun se ->
    match se.FStarC_Syntax_Syntax.sigel with
    | FStarC_Syntax_Syntax.Sig_bundle
        { FStarC_Syntax_Syntax.ses = ses;
          FStarC_Syntax_Syntax.lids = uu___;_}
        -> ses
    | uu___ -> failwith "ses_of_sigbundle: not a Sig_bundle"
let (set_uvar :
  FStarC_Syntax_Syntax.uvar -> FStarC_Syntax_Syntax.term -> unit) =
  fun uv ->
    fun t ->
      let uu___ = FStarC_Syntax_Unionfind.find uv in
      match uu___ with
      | FStar_Pervasives_Native.Some t' ->
          let uu___1 =
            let uu___2 =
              let uu___3 = FStarC_Syntax_Unionfind.uvar_id uv in
              FStarC_Compiler_Util.string_of_int uu___3 in
            let uu___3 = tts t in
            let uu___4 = tts t' in
            FStarC_Compiler_Util.format3
              "Changing a fixed uvar! ?%s to %s but it is already set to %s\n"
              uu___2 uu___3 uu___4 in
          failwith uu___1
      | uu___1 -> FStarC_Syntax_Unionfind.change uv t
let (qualifier_equal :
  FStarC_Syntax_Syntax.qualifier ->
    FStarC_Syntax_Syntax.qualifier -> Prims.bool)
  =
  fun q1 ->
    fun q2 ->
      match (q1, q2) with
      | (FStarC_Syntax_Syntax.Discriminator l1,
         FStarC_Syntax_Syntax.Discriminator l2) ->
          FStarC_Ident.lid_equals l1 l2
      | (FStarC_Syntax_Syntax.Projector (l1a, l1b),
         FStarC_Syntax_Syntax.Projector (l2a, l2b)) ->
          (FStarC_Ident.lid_equals l1a l2a) &&
            (let uu___ = FStarC_Ident.string_of_id l1b in
             let uu___1 = FStarC_Ident.string_of_id l2b in uu___ = uu___1)
      | (FStarC_Syntax_Syntax.RecordType (ns1, f1),
         FStarC_Syntax_Syntax.RecordType (ns2, f2)) ->
          ((((FStarC_Compiler_List.length ns1) =
               (FStarC_Compiler_List.length ns2))
              &&
              (FStarC_Compiler_List.forall2
                 (fun x1 ->
                    fun x2 ->
                      let uu___ = FStarC_Ident.string_of_id x1 in
                      let uu___1 = FStarC_Ident.string_of_id x2 in
                      uu___ = uu___1) f1 f2))
             &&
             ((FStarC_Compiler_List.length f1) =
                (FStarC_Compiler_List.length f2)))
            &&
            (FStarC_Compiler_List.forall2
               (fun x1 ->
                  fun x2 ->
                    let uu___ = FStarC_Ident.string_of_id x1 in
                    let uu___1 = FStarC_Ident.string_of_id x2 in
                    uu___ = uu___1) f1 f2)
      | (FStarC_Syntax_Syntax.RecordConstructor (ns1, f1),
         FStarC_Syntax_Syntax.RecordConstructor (ns2, f2)) ->
          ((((FStarC_Compiler_List.length ns1) =
               (FStarC_Compiler_List.length ns2))
              &&
              (FStarC_Compiler_List.forall2
                 (fun x1 ->
                    fun x2 ->
                      let uu___ = FStarC_Ident.string_of_id x1 in
                      let uu___1 = FStarC_Ident.string_of_id x2 in
                      uu___ = uu___1) f1 f2))
             &&
             ((FStarC_Compiler_List.length f1) =
                (FStarC_Compiler_List.length f2)))
            &&
            (FStarC_Compiler_List.forall2
               (fun x1 ->
                  fun x2 ->
                    let uu___ = FStarC_Ident.string_of_id x1 in
                    let uu___1 = FStarC_Ident.string_of_id x2 in
                    uu___ = uu___1) f1 f2)
      | uu___ -> q1 = q2
let (abs :
  FStarC_Syntax_Syntax.binders ->
    FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax ->
      FStarC_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
        FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax)
  =
  fun bs ->
    fun t ->
      fun lopt ->
        let close_lopt lopt1 =
          match lopt1 with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some rc ->
              let uu___ =
                let uu___1 =
                  FStarC_Compiler_Util.map_opt
                    rc.FStarC_Syntax_Syntax.residual_typ
                    (FStarC_Syntax_Subst.close bs) in
                {
                  FStarC_Syntax_Syntax.residual_effect =
                    (rc.FStarC_Syntax_Syntax.residual_effect);
                  FStarC_Syntax_Syntax.residual_typ = uu___1;
                  FStarC_Syntax_Syntax.residual_flags =
                    (rc.FStarC_Syntax_Syntax.residual_flags)
                } in
              FStar_Pervasives_Native.Some uu___ in
        match bs with
        | [] -> t
        | uu___ ->
            let body =
              let uu___1 = FStarC_Syntax_Subst.close bs t in
              FStarC_Syntax_Subst.compress uu___1 in
            (match body.FStarC_Syntax_Syntax.n with
             | FStarC_Syntax_Syntax.Tm_abs
                 { FStarC_Syntax_Syntax.bs = bs';
                   FStarC_Syntax_Syntax.body = t1;
                   FStarC_Syntax_Syntax.rc_opt = lopt';_}
                 ->
                 let uu___1 =
                   let uu___2 =
                     let uu___3 =
                       let uu___4 = FStarC_Syntax_Subst.close_binders bs in
                       FStarC_Compiler_List.op_At uu___4 bs' in
                     let uu___4 = close_lopt lopt' in
                     {
                       FStarC_Syntax_Syntax.bs = uu___3;
                       FStarC_Syntax_Syntax.body = t1;
                       FStarC_Syntax_Syntax.rc_opt = uu___4
                     } in
                   FStarC_Syntax_Syntax.Tm_abs uu___2 in
                 FStarC_Syntax_Syntax.mk uu___1 t1.FStarC_Syntax_Syntax.pos
             | uu___1 ->
                 let uu___2 =
                   let uu___3 =
                     let uu___4 = FStarC_Syntax_Subst.close_binders bs in
                     let uu___5 = close_lopt lopt in
                     {
                       FStarC_Syntax_Syntax.bs = uu___4;
                       FStarC_Syntax_Syntax.body = body;
                       FStarC_Syntax_Syntax.rc_opt = uu___5
                     } in
                   FStarC_Syntax_Syntax.Tm_abs uu___3 in
                 FStarC_Syntax_Syntax.mk uu___2 t.FStarC_Syntax_Syntax.pos)
let (arrow_ln :
  FStarC_Syntax_Syntax.binder Prims.list ->
    FStarC_Syntax_Syntax.comp' FStarC_Syntax_Syntax.syntax ->
      FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax)
  =
  fun bs ->
    fun c ->
      match bs with
      | [] -> comp_result c
      | uu___ ->
          let uu___1 =
            FStarC_Compiler_List.fold_left
              (fun a ->
                 fun b ->
                   FStarC_Compiler_Range_Ops.union_ranges a
                     ((b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort).FStarC_Syntax_Syntax.pos)
              c.FStarC_Syntax_Syntax.pos bs in
          FStarC_Syntax_Syntax.mk
            (FStarC_Syntax_Syntax.Tm_arrow
               { FStarC_Syntax_Syntax.bs1 = bs; FStarC_Syntax_Syntax.comp = c
               }) uu___1
let (arrow :
  FStarC_Syntax_Syntax.binders ->
    FStarC_Syntax_Syntax.comp ->
      FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax)
  =
  fun bs ->
    fun c ->
      let c1 = FStarC_Syntax_Subst.close_comp bs c in
      let bs1 = FStarC_Syntax_Subst.close_binders bs in arrow_ln bs1 c1
let (flat_arrow :
  FStarC_Syntax_Syntax.binders ->
    FStarC_Syntax_Syntax.comp ->
      FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax)
  =
  fun bs ->
    fun c ->
      let t = arrow bs c in
      let uu___ =
        let uu___1 = FStarC_Syntax_Subst.compress t in
        uu___1.FStarC_Syntax_Syntax.n in
      match uu___ with
      | FStarC_Syntax_Syntax.Tm_arrow
          { FStarC_Syntax_Syntax.bs1 = bs1; FStarC_Syntax_Syntax.comp = c1;_}
          ->
          (match c1.FStarC_Syntax_Syntax.n with
           | FStarC_Syntax_Syntax.Total tres ->
               let uu___1 =
                 let uu___2 = FStarC_Syntax_Subst.compress tres in
                 uu___2.FStarC_Syntax_Syntax.n in
               (match uu___1 with
                | FStarC_Syntax_Syntax.Tm_arrow
                    { FStarC_Syntax_Syntax.bs1 = bs';
                      FStarC_Syntax_Syntax.comp = c';_}
                    ->
                    FStarC_Syntax_Syntax.mk
                      (FStarC_Syntax_Syntax.Tm_arrow
                         {
                           FStarC_Syntax_Syntax.bs1 =
                             (FStarC_Compiler_List.op_At bs1 bs');
                           FStarC_Syntax_Syntax.comp = c'
                         }) t.FStarC_Syntax_Syntax.pos
                | uu___2 -> t)
           | uu___1 -> t)
      | uu___1 -> t
let rec (canon_arrow :
  FStarC_Syntax_Syntax.term ->
    FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax)
  =
  fun t ->
    let uu___ =
      let uu___1 = FStarC_Syntax_Subst.compress t in
      uu___1.FStarC_Syntax_Syntax.n in
    match uu___ with
    | FStarC_Syntax_Syntax.Tm_arrow
        { FStarC_Syntax_Syntax.bs1 = bs; FStarC_Syntax_Syntax.comp = c;_} ->
        let cn =
          match c.FStarC_Syntax_Syntax.n with
          | FStarC_Syntax_Syntax.Total t1 ->
              let uu___1 = canon_arrow t1 in
              FStarC_Syntax_Syntax.Total uu___1
          | uu___1 -> c.FStarC_Syntax_Syntax.n in
        let c1 =
          {
            FStarC_Syntax_Syntax.n = cn;
            FStarC_Syntax_Syntax.pos = (c.FStarC_Syntax_Syntax.pos);
            FStarC_Syntax_Syntax.vars = (c.FStarC_Syntax_Syntax.vars);
            FStarC_Syntax_Syntax.hash_code =
              (c.FStarC_Syntax_Syntax.hash_code)
          } in
        flat_arrow bs c1
    | uu___1 -> t
let (refine :
  FStarC_Syntax_Syntax.bv ->
    FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax ->
      FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax)
  =
  fun b ->
    fun t ->
      let uu___ =
        let uu___1 =
          let uu___2 =
            let uu___3 =
              let uu___4 = FStarC_Syntax_Syntax.mk_binder b in [uu___4] in
            FStarC_Syntax_Subst.close uu___3 t in
          { FStarC_Syntax_Syntax.b = b; FStarC_Syntax_Syntax.phi = uu___2 } in
        FStarC_Syntax_Syntax.Tm_refine uu___1 in
      let uu___1 =
        let uu___2 = FStarC_Syntax_Syntax.range_of_bv b in
        FStarC_Compiler_Range_Ops.union_ranges uu___2
          t.FStarC_Syntax_Syntax.pos in
      FStarC_Syntax_Syntax.mk uu___ uu___1
let (branch : FStarC_Syntax_Syntax.branch -> FStarC_Syntax_Syntax.branch) =
  fun b -> FStarC_Syntax_Subst.close_branch b
let (has_decreases : FStarC_Syntax_Syntax.comp -> Prims.bool) =
  fun c ->
    match c.FStarC_Syntax_Syntax.n with
    | FStarC_Syntax_Syntax.Comp ct ->
        let uu___ =
          FStarC_Compiler_Util.find_opt
            (fun uu___1 ->
               match uu___1 with
               | FStarC_Syntax_Syntax.DECREASES uu___2 -> true
               | uu___2 -> false) ct.FStarC_Syntax_Syntax.flags in
        (match uu___ with
         | FStar_Pervasives_Native.Some (FStarC_Syntax_Syntax.DECREASES
             uu___1) -> true
         | uu___1 -> false)
    | uu___ -> false
let rec (arrow_formals_comp_ln :
  FStarC_Syntax_Syntax.term ->
    (FStarC_Syntax_Syntax.binder Prims.list * FStarC_Syntax_Syntax.comp))
  =
  fun k ->
    let k1 = FStarC_Syntax_Subst.compress k in
    match k1.FStarC_Syntax_Syntax.n with
    | FStarC_Syntax_Syntax.Tm_arrow
        { FStarC_Syntax_Syntax.bs1 = bs; FStarC_Syntax_Syntax.comp = c;_} ->
        let uu___ =
          (is_total_comp c) &&
            (let uu___1 = has_decreases c in Prims.op_Negation uu___1) in
        if uu___
        then
          let uu___1 = arrow_formals_comp_ln (comp_result c) in
          (match uu___1 with
           | (bs', k2) -> ((FStarC_Compiler_List.op_At bs bs'), k2))
        else (bs, c)
    | FStarC_Syntax_Syntax.Tm_refine
        {
          FStarC_Syntax_Syntax.b =
            { FStarC_Syntax_Syntax.ppname = uu___;
              FStarC_Syntax_Syntax.index = uu___1;
              FStarC_Syntax_Syntax.sort = s;_};
          FStarC_Syntax_Syntax.phi = uu___2;_}
        ->
        let rec aux s1 k2 =
          let uu___3 =
            let uu___4 = FStarC_Syntax_Subst.compress s1 in
            uu___4.FStarC_Syntax_Syntax.n in
          match uu___3 with
          | FStarC_Syntax_Syntax.Tm_arrow uu___4 -> arrow_formals_comp_ln s1
          | FStarC_Syntax_Syntax.Tm_refine
              {
                FStarC_Syntax_Syntax.b =
                  { FStarC_Syntax_Syntax.ppname = uu___4;
                    FStarC_Syntax_Syntax.index = uu___5;
                    FStarC_Syntax_Syntax.sort = s2;_};
                FStarC_Syntax_Syntax.phi = uu___6;_}
              -> aux s2 k2
          | uu___4 ->
              let uu___5 = FStarC_Syntax_Syntax.mk_Total k2 in ([], uu___5) in
        aux s k1
    | uu___ -> let uu___1 = FStarC_Syntax_Syntax.mk_Total k1 in ([], uu___1)
let (arrow_formals_comp :
  FStarC_Syntax_Syntax.term ->
    (FStarC_Syntax_Syntax.binders * FStarC_Syntax_Syntax.comp))
  =
  fun k ->
    let uu___ = arrow_formals_comp_ln k in
    match uu___ with | (bs, c) -> FStarC_Syntax_Subst.open_comp bs c
let (arrow_formals_ln :
  FStarC_Syntax_Syntax.term ->
    (FStarC_Syntax_Syntax.binder Prims.list * FStarC_Syntax_Syntax.term'
      FStarC_Syntax_Syntax.syntax))
  =
  fun k ->
    let uu___ = arrow_formals_comp_ln k in
    match uu___ with | (bs, c) -> (bs, (comp_result c))
let (arrow_formals :
  FStarC_Syntax_Syntax.term ->
    (FStarC_Syntax_Syntax.binders * FStarC_Syntax_Syntax.term'
      FStarC_Syntax_Syntax.syntax))
  =
  fun k ->
    let uu___ = arrow_formals_comp k in
    match uu___ with | (bs, c) -> (bs, (comp_result c))
let (let_rec_arity :
  FStarC_Syntax_Syntax.letbinding ->
    (Prims.int * Prims.bool Prims.list FStar_Pervasives_Native.option))
  =
  fun lb ->
    let rec arrow_until_decreases k =
      let k1 = FStarC_Syntax_Subst.compress k in
      match k1.FStarC_Syntax_Syntax.n with
      | FStarC_Syntax_Syntax.Tm_arrow
          { FStarC_Syntax_Syntax.bs1 = bs; FStarC_Syntax_Syntax.comp = c;_}
          ->
          let uu___ = FStarC_Syntax_Subst.open_comp bs c in
          (match uu___ with
           | (bs1, c1) ->
               let uu___1 =
                 FStarC_Compiler_Util.find_opt
                   (fun uu___2 ->
                      match uu___2 with
                      | FStarC_Syntax_Syntax.DECREASES uu___3 -> true
                      | uu___3 -> false) (comp_flags c1) in
               (match uu___1 with
                | FStar_Pervasives_Native.Some
                    (FStarC_Syntax_Syntax.DECREASES d) ->
                    (bs1, (FStar_Pervasives_Native.Some d))
                | uu___2 ->
                    let uu___3 = is_total_comp c1 in
                    if uu___3
                    then
                      let uu___4 = arrow_until_decreases (comp_result c1) in
                      (match uu___4 with
                       | (bs', d) ->
                           ((FStarC_Compiler_List.op_At bs1 bs'), d))
                    else (bs1, FStar_Pervasives_Native.None)))
      | FStarC_Syntax_Syntax.Tm_refine
          {
            FStarC_Syntax_Syntax.b =
              { FStarC_Syntax_Syntax.ppname = uu___;
                FStarC_Syntax_Syntax.index = uu___1;
                FStarC_Syntax_Syntax.sort = k2;_};
            FStarC_Syntax_Syntax.phi = uu___2;_}
          -> arrow_until_decreases k2
      | uu___ -> ([], FStar_Pervasives_Native.None) in
    let uu___ = arrow_until_decreases lb.FStarC_Syntax_Syntax.lbtyp in
    match uu___ with
    | (bs, dopt) ->
        let n_univs =
          FStarC_Compiler_List.length lb.FStarC_Syntax_Syntax.lbunivs in
        let uu___1 =
          FStarC_Compiler_Util.map_opt dopt
            (fun d ->
               let d_bvs =
                 match d with
                 | FStarC_Syntax_Syntax.Decreases_lex l ->
                     Obj.magic
                       (Obj.repr
                          (let uu___2 =
                             Obj.magic
                               (FStarC_Class_Setlike.empty ()
                                  (Obj.magic
                                     (FStarC_Compiler_FlatSet.setlike_flat_set
                                        FStarC_Syntax_Syntax.ord_bv)) ()) in
                           FStarC_Compiler_List.fold_left
                             (fun uu___4 ->
                                fun uu___3 ->
                                  (fun s ->
                                     fun t ->
                                       let uu___3 =
                                         FStarC_Syntax_Free.names t in
                                       Obj.magic
                                         (FStarC_Class_Setlike.union ()
                                            (Obj.magic
                                               (FStarC_Compiler_FlatSet.setlike_flat_set
                                                  FStarC_Syntax_Syntax.ord_bv))
                                            (Obj.magic s) (Obj.magic uu___3)))
                                    uu___4 uu___3) uu___2 l))
                 | FStarC_Syntax_Syntax.Decreases_wf (rel, e) ->
                     Obj.magic
                       (Obj.repr
                          (let uu___2 = FStarC_Syntax_Free.names rel in
                           let uu___3 = FStarC_Syntax_Free.names e in
                           FStarC_Class_Setlike.union ()
                             (Obj.magic
                                (FStarC_Compiler_FlatSet.setlike_flat_set
                                   FStarC_Syntax_Syntax.ord_bv))
                             (Obj.magic uu___2) (Obj.magic uu___3))) in
               let uu___2 =
                 FStarC_Common.tabulate n_univs (fun uu___3 -> false) in
               let uu___3 =
                 FStarC_Compiler_List.map
                   (fun b ->
                      FStarC_Class_Setlike.mem ()
                        (Obj.magic
                           (FStarC_Compiler_FlatSet.setlike_flat_set
                              FStarC_Syntax_Syntax.ord_bv))
                        b.FStarC_Syntax_Syntax.binder_bv (Obj.magic d_bvs))
                   bs in
               FStarC_Compiler_List.op_At uu___2 uu___3) in
        ((n_univs + (FStarC_Compiler_List.length bs)), uu___1)
let (abs_formals_maybe_unascribe_body :
  Prims.bool ->
    FStarC_Syntax_Syntax.term ->
      (FStarC_Syntax_Syntax.binders * FStarC_Syntax_Syntax.term *
        FStarC_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option))
  =
  fun maybe_unascribe ->
    fun t ->
      let subst_lcomp_opt s l =
        match l with
        | FStar_Pervasives_Native.Some rc ->
            let uu___ =
              let uu___1 =
                FStarC_Compiler_Util.map_opt
                  rc.FStarC_Syntax_Syntax.residual_typ
                  (FStarC_Syntax_Subst.subst s) in
              {
                FStarC_Syntax_Syntax.residual_effect =
                  (rc.FStarC_Syntax_Syntax.residual_effect);
                FStarC_Syntax_Syntax.residual_typ = uu___1;
                FStarC_Syntax_Syntax.residual_flags =
                  (rc.FStarC_Syntax_Syntax.residual_flags)
              } in
            FStar_Pervasives_Native.Some uu___
        | uu___ -> l in
      let rec aux t1 abs_body_lcomp =
        let uu___ =
          let uu___1 = unmeta_safe t1 in uu___1.FStarC_Syntax_Syntax.n in
        match uu___ with
        | FStarC_Syntax_Syntax.Tm_abs
            { FStarC_Syntax_Syntax.bs = bs; FStarC_Syntax_Syntax.body = t2;
              FStarC_Syntax_Syntax.rc_opt = what;_}
            ->
            if maybe_unascribe
            then
              let uu___1 = aux t2 what in
              (match uu___1 with
               | (bs', t3, what1) ->
                   ((FStarC_Compiler_List.op_At bs bs'), t3, what1))
            else (bs, t2, what)
        | uu___1 -> ([], t1, abs_body_lcomp) in
      let uu___ = aux t FStar_Pervasives_Native.None in
      match uu___ with
      | (bs, t1, abs_body_lcomp) ->
          let uu___1 = FStarC_Syntax_Subst.open_term' bs t1 in
          (match uu___1 with
           | (bs1, t2, opening) ->
               let abs_body_lcomp1 = subst_lcomp_opt opening abs_body_lcomp in
               (bs1, t2, abs_body_lcomp1))
let (abs_formals :
  FStarC_Syntax_Syntax.term ->
    (FStarC_Syntax_Syntax.binders * FStarC_Syntax_Syntax.term *
      FStarC_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option))
  = fun t -> abs_formals_maybe_unascribe_body true t
let (remove_inacc : FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term) =
  fun t ->
    let no_acc b =
      let aq =
        match b.FStarC_Syntax_Syntax.binder_qual with
        | FStar_Pervasives_Native.Some (FStarC_Syntax_Syntax.Implicit (true))
            ->
            FStar_Pervasives_Native.Some
              (FStarC_Syntax_Syntax.Implicit false)
        | aq1 -> aq1 in
      {
        FStarC_Syntax_Syntax.binder_bv = (b.FStarC_Syntax_Syntax.binder_bv);
        FStarC_Syntax_Syntax.binder_qual = aq;
        FStarC_Syntax_Syntax.binder_positivity =
          (b.FStarC_Syntax_Syntax.binder_positivity);
        FStarC_Syntax_Syntax.binder_attrs =
          (b.FStarC_Syntax_Syntax.binder_attrs)
      } in
    let uu___ = arrow_formals_comp_ln t in
    match uu___ with
    | (bs, c) ->
        (match bs with
         | [] -> t
         | uu___1 ->
             let uu___2 =
               let uu___3 =
                 let uu___4 = FStarC_Compiler_List.map no_acc bs in
                 {
                   FStarC_Syntax_Syntax.bs1 = uu___4;
                   FStarC_Syntax_Syntax.comp = c
                 } in
               FStarC_Syntax_Syntax.Tm_arrow uu___3 in
             FStarC_Syntax_Syntax.mk uu___2 t.FStarC_Syntax_Syntax.pos)
let (mk_letbinding :
  (FStarC_Syntax_Syntax.bv, FStarC_Syntax_Syntax.fv) FStar_Pervasives.either
    ->
    FStarC_Syntax_Syntax.univ_name Prims.list ->
      FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax ->
        FStarC_Ident.lident ->
          FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax ->
            FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax Prims.list
              ->
              FStarC_Compiler_Range_Type.range ->
                FStarC_Syntax_Syntax.letbinding)
  =
  fun lbname ->
    fun univ_vars ->
      fun typ ->
        fun eff ->
          fun def ->
            fun lbattrs ->
              fun pos ->
                {
                  FStarC_Syntax_Syntax.lbname = lbname;
                  FStarC_Syntax_Syntax.lbunivs = univ_vars;
                  FStarC_Syntax_Syntax.lbtyp = typ;
                  FStarC_Syntax_Syntax.lbeff = eff;
                  FStarC_Syntax_Syntax.lbdef = def;
                  FStarC_Syntax_Syntax.lbattrs = lbattrs;
                  FStarC_Syntax_Syntax.lbpos = pos
                }
let (close_univs_and_mk_letbinding :
  FStarC_Syntax_Syntax.fv Prims.list FStar_Pervasives_Native.option ->
    (FStarC_Syntax_Syntax.bv, FStarC_Syntax_Syntax.fv)
      FStar_Pervasives.either ->
      FStarC_Syntax_Syntax.univ_name Prims.list ->
        FStarC_Syntax_Syntax.term ->
          FStarC_Ident.lident ->
            FStarC_Syntax_Syntax.term ->
              FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax
                Prims.list ->
                FStarC_Compiler_Range_Type.range ->
                  FStarC_Syntax_Syntax.letbinding)
  =
  fun recs ->
    fun lbname ->
      fun univ_vars ->
        fun typ ->
          fun eff ->
            fun def ->
              fun attrs ->
                fun pos ->
                  let def1 =
                    match (recs, univ_vars) with
                    | (FStar_Pervasives_Native.None, uu___) -> def
                    | (uu___, []) -> def
                    | (FStar_Pervasives_Native.Some fvs, uu___) ->
                        let universes =
                          FStarC_Compiler_List.map
                            (fun uu___1 -> FStarC_Syntax_Syntax.U_name uu___1)
                            univ_vars in
                        let inst =
                          FStarC_Compiler_List.map
                            (fun fv ->
                               (((fv.FStarC_Syntax_Syntax.fv_name).FStarC_Syntax_Syntax.v),
                                 universes)) fvs in
                        FStarC_Syntax_InstFV.instantiate inst def in
                  let typ1 =
                    FStarC_Syntax_Subst.close_univ_vars univ_vars typ in
                  let def2 =
                    FStarC_Syntax_Subst.close_univ_vars univ_vars def1 in
                  mk_letbinding lbname univ_vars typ1 eff def2 attrs pos
let (open_univ_vars_binders_and_comp :
  FStarC_Syntax_Syntax.univ_names ->
    FStarC_Syntax_Syntax.binder Prims.list ->
      FStarC_Syntax_Syntax.comp ->
        (FStarC_Syntax_Syntax.univ_names * FStarC_Syntax_Syntax.binder
          Prims.list * FStarC_Syntax_Syntax.comp))
  =
  fun uvs ->
    fun binders ->
      fun c ->
        match binders with
        | [] ->
            let uu___ = FStarC_Syntax_Subst.open_univ_vars_comp uvs c in
            (match uu___ with | (uvs1, c1) -> (uvs1, [], c1))
        | uu___ ->
            let t' = arrow binders c in
            let uu___1 = FStarC_Syntax_Subst.open_univ_vars uvs t' in
            (match uu___1 with
             | (uvs1, t'1) ->
                 let uu___2 =
                   let uu___3 = FStarC_Syntax_Subst.compress t'1 in
                   uu___3.FStarC_Syntax_Syntax.n in
                 (match uu___2 with
                  | FStarC_Syntax_Syntax.Tm_arrow
                      { FStarC_Syntax_Syntax.bs1 = binders1;
                        FStarC_Syntax_Syntax.comp = c1;_}
                      -> (uvs1, binders1, c1)
                  | uu___3 -> failwith "Impossible"))
let (is_tuple_constructor : FStarC_Syntax_Syntax.typ -> Prims.bool) =
  fun t ->
    match t.FStarC_Syntax_Syntax.n with
    | FStarC_Syntax_Syntax.Tm_fvar fv ->
        let uu___ =
          FStarC_Ident.string_of_lid
            (fv.FStarC_Syntax_Syntax.fv_name).FStarC_Syntax_Syntax.v in
        FStarC_Parser_Const.is_tuple_constructor_string uu___
    | uu___ -> false
let (is_dtuple_constructor : FStarC_Syntax_Syntax.typ -> Prims.bool) =
  fun t ->
    match t.FStarC_Syntax_Syntax.n with
    | FStarC_Syntax_Syntax.Tm_fvar fv ->
        FStarC_Parser_Const.is_dtuple_constructor_lid
          (fv.FStarC_Syntax_Syntax.fv_name).FStarC_Syntax_Syntax.v
    | uu___ -> false
let (is_lid_equality : FStarC_Ident.lident -> Prims.bool) =
  fun x -> FStarC_Ident.lid_equals x FStarC_Parser_Const.eq2_lid
let (is_forall : FStarC_Ident.lident -> Prims.bool) =
  fun lid -> FStarC_Ident.lid_equals lid FStarC_Parser_Const.forall_lid
let (is_exists : FStarC_Ident.lident -> Prims.bool) =
  fun lid -> FStarC_Ident.lid_equals lid FStarC_Parser_Const.exists_lid
let (is_qlid : FStarC_Ident.lident -> Prims.bool) =
  fun lid -> (is_forall lid) || (is_exists lid)
let (is_equality :
  FStarC_Ident.lident FStarC_Syntax_Syntax.withinfo_t -> Prims.bool) =
  fun x -> is_lid_equality x.FStarC_Syntax_Syntax.v
let (lid_is_connective : FStarC_Ident.lident -> Prims.bool) =
  let lst =
    [FStarC_Parser_Const.and_lid;
    FStarC_Parser_Const.or_lid;
    FStarC_Parser_Const.not_lid;
    FStarC_Parser_Const.iff_lid;
    FStarC_Parser_Const.imp_lid] in
  fun lid -> FStarC_Compiler_Util.for_some (FStarC_Ident.lid_equals lid) lst
let (is_constructor :
  FStarC_Syntax_Syntax.term -> FStarC_Ident.lident -> Prims.bool) =
  fun t ->
    fun lid ->
      let uu___ = let uu___1 = pre_typ t in uu___1.FStarC_Syntax_Syntax.n in
      match uu___ with
      | FStarC_Syntax_Syntax.Tm_fvar tc ->
          FStarC_Ident.lid_equals
            (tc.FStarC_Syntax_Syntax.fv_name).FStarC_Syntax_Syntax.v lid
      | uu___1 -> false
let rec (is_constructed_typ :
  FStarC_Syntax_Syntax.term -> FStarC_Ident.lident -> Prims.bool) =
  fun t ->
    fun lid ->
      let uu___ = let uu___1 = pre_typ t in uu___1.FStarC_Syntax_Syntax.n in
      match uu___ with
      | FStarC_Syntax_Syntax.Tm_fvar uu___1 -> is_constructor t lid
      | FStarC_Syntax_Syntax.Tm_app
          { FStarC_Syntax_Syntax.hd = t1;
            FStarC_Syntax_Syntax.args = uu___1;_}
          -> is_constructed_typ t1 lid
      | FStarC_Syntax_Syntax.Tm_uinst (t1, uu___1) ->
          is_constructed_typ t1 lid
      | uu___1 -> false
let rec (get_tycon :
  FStarC_Syntax_Syntax.term ->
    FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun t ->
    let t1 = pre_typ t in
    match t1.FStarC_Syntax_Syntax.n with
    | FStarC_Syntax_Syntax.Tm_bvar uu___ -> FStar_Pervasives_Native.Some t1
    | FStarC_Syntax_Syntax.Tm_name uu___ -> FStar_Pervasives_Native.Some t1
    | FStarC_Syntax_Syntax.Tm_fvar uu___ -> FStar_Pervasives_Native.Some t1
    | FStarC_Syntax_Syntax.Tm_app
        { FStarC_Syntax_Syntax.hd = t2; FStarC_Syntax_Syntax.args = uu___;_}
        -> get_tycon t2
    | uu___ -> FStar_Pervasives_Native.None
let (is_fstar_tactics_by_tactic : FStarC_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu___ = let uu___1 = un_uinst t in uu___1.FStarC_Syntax_Syntax.n in
    match uu___ with
    | FStarC_Syntax_Syntax.Tm_fvar fv ->
        FStarC_Syntax_Syntax.fv_eq_lid fv FStarC_Parser_Const.by_tactic_lid
    | uu___1 -> false
let (ktype : FStarC_Syntax_Syntax.term) =
  FStarC_Syntax_Syntax.mk
    (FStarC_Syntax_Syntax.Tm_type FStarC_Syntax_Syntax.U_unknown)
    FStarC_Compiler_Range_Type.dummyRange
let (ktype0 : FStarC_Syntax_Syntax.term) =
  FStarC_Syntax_Syntax.mk
    (FStarC_Syntax_Syntax.Tm_type FStarC_Syntax_Syntax.U_zero)
    FStarC_Compiler_Range_Type.dummyRange
let (type_u :
  unit -> (FStarC_Syntax_Syntax.typ * FStarC_Syntax_Syntax.universe)) =
  fun uu___ ->
    let u =
      let uu___1 =
        FStarC_Syntax_Unionfind.univ_fresh
          FStarC_Compiler_Range_Type.dummyRange in
      FStarC_Syntax_Syntax.U_unif uu___1 in
    let uu___1 =
      FStarC_Syntax_Syntax.mk (FStarC_Syntax_Syntax.Tm_type u)
        FStarC_Compiler_Range_Type.dummyRange in
    (uu___1, u)
let (type_with_u : FStarC_Syntax_Syntax.universe -> FStarC_Syntax_Syntax.typ)
  =
  fun u ->
    FStarC_Syntax_Syntax.mk (FStarC_Syntax_Syntax.Tm_type u)
      FStarC_Compiler_Range_Type.dummyRange
let (attr_substitute :
  FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax) =
  let uu___ =
    let uu___1 =
      FStarC_Syntax_Syntax.lid_as_fv FStarC_Parser_Const.attr_substitute_lid
        FStar_Pervasives_Native.None in
    FStarC_Syntax_Syntax.Tm_fvar uu___1 in
  FStarC_Syntax_Syntax.mk uu___ FStarC_Compiler_Range_Type.dummyRange
let (exp_bool : Prims.bool -> FStarC_Syntax_Syntax.term) =
  fun b ->
    FStarC_Syntax_Syntax.mk
      (FStarC_Syntax_Syntax.Tm_constant (FStarC_Const.Const_bool b))
      FStarC_Compiler_Range_Type.dummyRange
let (exp_true_bool : FStarC_Syntax_Syntax.term) = exp_bool true
let (exp_false_bool : FStarC_Syntax_Syntax.term) = exp_bool false
let (exp_unit : FStarC_Syntax_Syntax.term) =
  FStarC_Syntax_Syntax.mk
    (FStarC_Syntax_Syntax.Tm_constant FStarC_Const.Const_unit)
    FStarC_Compiler_Range_Type.dummyRange
let (exp_int : Prims.string -> FStarC_Syntax_Syntax.term) =
  fun s ->
    FStarC_Syntax_Syntax.mk
      (FStarC_Syntax_Syntax.Tm_constant
         (FStarC_Const.Const_int (s, FStar_Pervasives_Native.None)))
      FStarC_Compiler_Range_Type.dummyRange
let (exp_char : FStarC_BaseTypes.char -> FStarC_Syntax_Syntax.term) =
  fun c ->
    FStarC_Syntax_Syntax.mk
      (FStarC_Syntax_Syntax.Tm_constant (FStarC_Const.Const_char c))
      FStarC_Compiler_Range_Type.dummyRange
let (exp_string : Prims.string -> FStarC_Syntax_Syntax.term) =
  fun s ->
    FStarC_Syntax_Syntax.mk
      (FStarC_Syntax_Syntax.Tm_constant
         (FStarC_Const.Const_string
            (s, FStarC_Compiler_Range_Type.dummyRange)))
      FStarC_Compiler_Range_Type.dummyRange
let (fvar_const : FStarC_Ident.lident -> FStarC_Syntax_Syntax.term) =
  fun l -> FStarC_Syntax_Syntax.fvar_with_dd l FStar_Pervasives_Native.None
let (tand : FStarC_Syntax_Syntax.term) =
  fvar_const FStarC_Parser_Const.and_lid
let (tor : FStarC_Syntax_Syntax.term) = fvar_const FStarC_Parser_Const.or_lid
let (timp : FStarC_Syntax_Syntax.term) =
  FStarC_Syntax_Syntax.fvar_with_dd FStarC_Parser_Const.imp_lid
    FStar_Pervasives_Native.None
let (tiff : FStarC_Syntax_Syntax.term) =
  FStarC_Syntax_Syntax.fvar_with_dd FStarC_Parser_Const.iff_lid
    FStar_Pervasives_Native.None
let (t_bool : FStarC_Syntax_Syntax.term) =
  fvar_const FStarC_Parser_Const.bool_lid
let (b2t_v : FStarC_Syntax_Syntax.term) =
  fvar_const FStarC_Parser_Const.b2t_lid
let (t_not : FStarC_Syntax_Syntax.term) =
  fvar_const FStarC_Parser_Const.not_lid
let (t_false : FStarC_Syntax_Syntax.term) =
  fvar_const FStarC_Parser_Const.false_lid
let (t_true : FStarC_Syntax_Syntax.term) =
  fvar_const FStarC_Parser_Const.true_lid
let (tac_opaque_attr : FStarC_Syntax_Syntax.term) = exp_string "tac_opaque"
let (dm4f_bind_range_attr : FStarC_Syntax_Syntax.term) =
  fvar_const FStarC_Parser_Const.dm4f_bind_range_attr
let (tcdecltime_attr : FStarC_Syntax_Syntax.term) =
  fvar_const FStarC_Parser_Const.tcdecltime_attr
let (inline_let_attr : FStarC_Syntax_Syntax.term) =
  fvar_const FStarC_Parser_Const.inline_let_attr
let (rename_let_attr : FStarC_Syntax_Syntax.term) =
  fvar_const FStarC_Parser_Const.rename_let_attr
let (t_ctx_uvar_and_sust : FStarC_Syntax_Syntax.term) =
  fvar_const FStarC_Parser_Const.ctx_uvar_and_subst_lid
let (t_universe_uvar : FStarC_Syntax_Syntax.term) =
  fvar_const FStarC_Parser_Const.universe_uvar_lid
let (t_dsl_tac_typ : FStarC_Syntax_Syntax.term) =
  FStarC_Syntax_Syntax.fvar FStarC_Parser_Const.dsl_tac_typ_lid
    FStar_Pervasives_Native.None
let (mk_conj_opt :
  FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax
    FStar_Pervasives_Native.option ->
    FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax ->
      FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax
        FStar_Pervasives_Native.option)
  =
  fun phi1 ->
    fun phi2 ->
      match phi1 with
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.Some phi2
      | FStar_Pervasives_Native.Some phi11 ->
          let uu___ =
            let uu___1 =
              let uu___2 =
                let uu___3 =
                  let uu___4 = FStarC_Syntax_Syntax.as_arg phi11 in
                  let uu___5 =
                    let uu___6 = FStarC_Syntax_Syntax.as_arg phi2 in [uu___6] in
                  uu___4 :: uu___5 in
                {
                  FStarC_Syntax_Syntax.hd = tand;
                  FStarC_Syntax_Syntax.args = uu___3
                } in
              FStarC_Syntax_Syntax.Tm_app uu___2 in
            let uu___2 =
              FStarC_Compiler_Range_Ops.union_ranges
                phi11.FStarC_Syntax_Syntax.pos phi2.FStarC_Syntax_Syntax.pos in
            FStarC_Syntax_Syntax.mk uu___1 uu___2 in
          FStar_Pervasives_Native.Some uu___
let (mk_binop :
  FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax ->
    FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax ->
      FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax ->
        FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax)
  =
  fun op_t ->
    fun phi1 ->
      fun phi2 ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              let uu___3 = FStarC_Syntax_Syntax.as_arg phi1 in
              let uu___4 =
                let uu___5 = FStarC_Syntax_Syntax.as_arg phi2 in [uu___5] in
              uu___3 :: uu___4 in
            {
              FStarC_Syntax_Syntax.hd = op_t;
              FStarC_Syntax_Syntax.args = uu___2
            } in
          FStarC_Syntax_Syntax.Tm_app uu___1 in
        let uu___1 =
          FStarC_Compiler_Range_Ops.union_ranges
            phi1.FStarC_Syntax_Syntax.pos phi2.FStarC_Syntax_Syntax.pos in
        FStarC_Syntax_Syntax.mk uu___ uu___1
let (mk_neg :
  FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax ->
    FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax)
  =
  fun phi ->
    let uu___ =
      let uu___1 =
        let uu___2 = let uu___3 = FStarC_Syntax_Syntax.as_arg phi in [uu___3] in
        { FStarC_Syntax_Syntax.hd = t_not; FStarC_Syntax_Syntax.args = uu___2
        } in
      FStarC_Syntax_Syntax.Tm_app uu___1 in
    FStarC_Syntax_Syntax.mk uu___ phi.FStarC_Syntax_Syntax.pos
let (mk_conj :
  FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax ->
    FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax ->
      FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax)
  = fun phi1 -> fun phi2 -> mk_binop tand phi1 phi2
let (mk_conj_l :
  FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax Prims.list ->
    FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax)
  =
  fun phi ->
    match phi with
    | [] ->
        FStarC_Syntax_Syntax.fvar_with_dd FStarC_Parser_Const.true_lid
          FStar_Pervasives_Native.None
    | hd::tl -> FStarC_Compiler_List.fold_right mk_conj tl hd
let (mk_disj :
  FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax ->
    FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax ->
      FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax)
  = fun phi1 -> fun phi2 -> mk_binop tor phi1 phi2
let (mk_disj_l :
  FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax Prims.list ->
    FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax)
  =
  fun phi ->
    match phi with
    | [] -> t_false
    | hd::tl -> FStarC_Compiler_List.fold_right mk_disj tl hd
let (mk_imp :
  FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax ->
    FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax ->
      FStarC_Syntax_Syntax.term)
  = fun phi1 -> fun phi2 -> mk_binop timp phi1 phi2
let (mk_iff :
  FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax ->
    FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax ->
      FStarC_Syntax_Syntax.term)
  = fun phi1 -> fun phi2 -> mk_binop tiff phi1 phi2
let (b2t :
  FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax ->
    FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax)
  =
  fun e ->
    let uu___ =
      let uu___1 =
        let uu___2 = let uu___3 = FStarC_Syntax_Syntax.as_arg e in [uu___3] in
        { FStarC_Syntax_Syntax.hd = b2t_v; FStarC_Syntax_Syntax.args = uu___2
        } in
      FStarC_Syntax_Syntax.Tm_app uu___1 in
    FStarC_Syntax_Syntax.mk uu___ e.FStarC_Syntax_Syntax.pos
let (unb2t :
  FStarC_Syntax_Syntax.term ->
    FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun e ->
    let uu___ = head_and_args e in
    match uu___ with
    | (hd, args) ->
        let uu___1 =
          let uu___2 =
            let uu___3 = FStarC_Syntax_Subst.compress hd in
            uu___3.FStarC_Syntax_Syntax.n in
          (uu___2, args) in
        (match uu___1 with
         | (FStarC_Syntax_Syntax.Tm_fvar fv, (e1, uu___2)::[]) when
             FStarC_Syntax_Syntax.fv_eq_lid fv FStarC_Parser_Const.b2t_lid ->
             FStar_Pervasives_Native.Some e1
         | uu___2 -> FStar_Pervasives_Native.None)
let (is_t_true : FStarC_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu___ = let uu___1 = unmeta t in uu___1.FStarC_Syntax_Syntax.n in
    match uu___ with
    | FStarC_Syntax_Syntax.Tm_fvar fv ->
        FStarC_Syntax_Syntax.fv_eq_lid fv FStarC_Parser_Const.true_lid
    | uu___1 -> false
let (mk_conj_simp :
  FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax ->
    FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax ->
      FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax)
  =
  fun t1 ->
    fun t2 ->
      let uu___ = is_t_true t1 in
      if uu___
      then t2
      else
        (let uu___2 = is_t_true t2 in if uu___2 then t1 else mk_conj t1 t2)
let (mk_disj_simp :
  FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax ->
    FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax ->
      FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax)
  =
  fun t1 ->
    fun t2 ->
      let uu___ = is_t_true t1 in
      if uu___
      then t_true
      else
        (let uu___2 = is_t_true t2 in
         if uu___2 then t_true else mk_disj t1 t2)
let (teq : FStarC_Syntax_Syntax.term) =
  fvar_const FStarC_Parser_Const.eq2_lid
let (mk_untyped_eq2 :
  FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax ->
    FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax ->
      FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax)
  =
  fun e1 ->
    fun e2 ->
      let uu___ =
        let uu___1 =
          let uu___2 =
            let uu___3 = FStarC_Syntax_Syntax.as_arg e1 in
            let uu___4 =
              let uu___5 = FStarC_Syntax_Syntax.as_arg e2 in [uu___5] in
            uu___3 :: uu___4 in
          { FStarC_Syntax_Syntax.hd = teq; FStarC_Syntax_Syntax.args = uu___2
          } in
        FStarC_Syntax_Syntax.Tm_app uu___1 in
      let uu___1 =
        FStarC_Compiler_Range_Ops.union_ranges e1.FStarC_Syntax_Syntax.pos
          e2.FStarC_Syntax_Syntax.pos in
      FStarC_Syntax_Syntax.mk uu___ uu___1
let (mk_eq2 :
  FStarC_Syntax_Syntax.universe ->
    FStarC_Syntax_Syntax.typ ->
      FStarC_Syntax_Syntax.term ->
        FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term)
  =
  fun u ->
    fun t ->
      fun e1 ->
        fun e2 ->
          let eq_inst = FStarC_Syntax_Syntax.mk_Tm_uinst teq [u] in
          let uu___ =
            let uu___1 =
              let uu___2 =
                let uu___3 = FStarC_Syntax_Syntax.iarg t in
                let uu___4 =
                  let uu___5 = FStarC_Syntax_Syntax.as_arg e1 in
                  let uu___6 =
                    let uu___7 = FStarC_Syntax_Syntax.as_arg e2 in [uu___7] in
                  uu___5 :: uu___6 in
                uu___3 :: uu___4 in
              {
                FStarC_Syntax_Syntax.hd = eq_inst;
                FStarC_Syntax_Syntax.args = uu___2
              } in
            FStarC_Syntax_Syntax.Tm_app uu___1 in
          let uu___1 =
            FStarC_Compiler_Range_Ops.union_ranges
              e1.FStarC_Syntax_Syntax.pos e2.FStarC_Syntax_Syntax.pos in
          FStarC_Syntax_Syntax.mk uu___ uu___1
let (mk_eq3_no_univ :
  FStarC_Syntax_Syntax.term ->
    FStarC_Syntax_Syntax.term ->
      FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax ->
        FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax ->
          FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax)
  =
  let teq3 = fvar_const FStarC_Parser_Const.eq3_lid in
  fun t1 ->
    fun t2 ->
      fun e1 ->
        fun e2 ->
          let uu___ =
            let uu___1 =
              let uu___2 =
                let uu___3 = FStarC_Syntax_Syntax.iarg t1 in
                let uu___4 =
                  let uu___5 = FStarC_Syntax_Syntax.iarg t2 in
                  let uu___6 =
                    let uu___7 = FStarC_Syntax_Syntax.as_arg e1 in
                    let uu___8 =
                      let uu___9 = FStarC_Syntax_Syntax.as_arg e2 in [uu___9] in
                    uu___7 :: uu___8 in
                  uu___5 :: uu___6 in
                uu___3 :: uu___4 in
              {
                FStarC_Syntax_Syntax.hd = teq3;
                FStarC_Syntax_Syntax.args = uu___2
              } in
            FStarC_Syntax_Syntax.Tm_app uu___1 in
          let uu___1 =
            FStarC_Compiler_Range_Ops.union_ranges
              e1.FStarC_Syntax_Syntax.pos e2.FStarC_Syntax_Syntax.pos in
          FStarC_Syntax_Syntax.mk uu___ uu___1
let (mk_has_type :
  FStarC_Syntax_Syntax.term ->
    FStarC_Syntax_Syntax.term ->
      FStarC_Syntax_Syntax.term ->
        FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax)
  =
  fun t ->
    fun x ->
      fun t' ->
        let t_has_type = fvar_const FStarC_Parser_Const.has_type_lid in
        let t_has_type1 =
          FStarC_Syntax_Syntax.mk
            (FStarC_Syntax_Syntax.Tm_uinst
               (t_has_type,
                 [FStarC_Syntax_Syntax.U_zero; FStarC_Syntax_Syntax.U_zero]))
            FStarC_Compiler_Range_Type.dummyRange in
        let uu___ =
          let uu___1 =
            let uu___2 =
              let uu___3 = FStarC_Syntax_Syntax.iarg t in
              let uu___4 =
                let uu___5 = FStarC_Syntax_Syntax.as_arg x in
                let uu___6 =
                  let uu___7 = FStarC_Syntax_Syntax.as_arg t' in [uu___7] in
                uu___5 :: uu___6 in
              uu___3 :: uu___4 in
            {
              FStarC_Syntax_Syntax.hd = t_has_type1;
              FStarC_Syntax_Syntax.args = uu___2
            } in
          FStarC_Syntax_Syntax.Tm_app uu___1 in
        FStarC_Syntax_Syntax.mk uu___ FStarC_Compiler_Range_Type.dummyRange
let (tforall : FStarC_Syntax_Syntax.term) =
  FStarC_Syntax_Syntax.fvar_with_dd FStarC_Parser_Const.forall_lid
    FStar_Pervasives_Native.None
let (texists : FStarC_Syntax_Syntax.term) =
  FStarC_Syntax_Syntax.fvar_with_dd FStarC_Parser_Const.exists_lid
    FStar_Pervasives_Native.None
let (t_haseq : FStarC_Syntax_Syntax.term) =
  FStarC_Syntax_Syntax.fvar_with_dd FStarC_Parser_Const.haseq_lid
    FStar_Pervasives_Native.None
let (decidable_eq : FStarC_Syntax_Syntax.term) =
  fvar_const FStarC_Parser_Const.op_Eq
let (mk_decidable_eq :
  FStarC_Syntax_Syntax.term ->
    FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax ->
      FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax ->
        FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax)
  =
  fun t ->
    fun e1 ->
      fun e2 ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              let uu___3 = FStarC_Syntax_Syntax.iarg t in
              let uu___4 =
                let uu___5 = FStarC_Syntax_Syntax.as_arg e1 in
                let uu___6 =
                  let uu___7 = FStarC_Syntax_Syntax.as_arg e2 in [uu___7] in
                uu___5 :: uu___6 in
              uu___3 :: uu___4 in
            {
              FStarC_Syntax_Syntax.hd = decidable_eq;
              FStarC_Syntax_Syntax.args = uu___2
            } in
          FStarC_Syntax_Syntax.Tm_app uu___1 in
        let uu___1 =
          FStarC_Compiler_Range_Ops.union_ranges e1.FStarC_Syntax_Syntax.pos
            e2.FStarC_Syntax_Syntax.pos in
        FStarC_Syntax_Syntax.mk uu___ uu___1
let (b_and : FStarC_Syntax_Syntax.term) =
  fvar_const FStarC_Parser_Const.op_And
let (mk_and :
  FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax ->
    FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax ->
      FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax)
  =
  fun e1 ->
    fun e2 ->
      let uu___ =
        let uu___1 =
          let uu___2 =
            let uu___3 = FStarC_Syntax_Syntax.as_arg e1 in
            let uu___4 =
              let uu___5 = FStarC_Syntax_Syntax.as_arg e2 in [uu___5] in
            uu___3 :: uu___4 in
          {
            FStarC_Syntax_Syntax.hd = b_and;
            FStarC_Syntax_Syntax.args = uu___2
          } in
        FStarC_Syntax_Syntax.Tm_app uu___1 in
      let uu___1 =
        FStarC_Compiler_Range_Ops.union_ranges e1.FStarC_Syntax_Syntax.pos
          e2.FStarC_Syntax_Syntax.pos in
      FStarC_Syntax_Syntax.mk uu___ uu___1
let (mk_and_l :
  FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax Prims.list ->
    FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax)
  =
  fun l ->
    match l with
    | [] -> exp_true_bool
    | hd::tl -> FStarC_Compiler_List.fold_left mk_and hd tl
let (mk_boolean_negation :
  FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax ->
    FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax)
  =
  fun b ->
    let uu___ =
      let uu___1 =
        let uu___2 = fvar_const FStarC_Parser_Const.op_Negation in
        let uu___3 = let uu___4 = FStarC_Syntax_Syntax.as_arg b in [uu___4] in
        {
          FStarC_Syntax_Syntax.hd = uu___2;
          FStarC_Syntax_Syntax.args = uu___3
        } in
      FStarC_Syntax_Syntax.Tm_app uu___1 in
    FStarC_Syntax_Syntax.mk uu___ b.FStarC_Syntax_Syntax.pos
let (mk_residual_comp :
  FStarC_Ident.lident ->
    FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option ->
      FStarC_Syntax_Syntax.cflag Prims.list ->
        FStarC_Syntax_Syntax.residual_comp)
  =
  fun l ->
    fun t ->
      fun f ->
        {
          FStarC_Syntax_Syntax.residual_effect = l;
          FStarC_Syntax_Syntax.residual_typ = t;
          FStarC_Syntax_Syntax.residual_flags = f
        }
let (residual_tot :
  FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax ->
    FStarC_Syntax_Syntax.residual_comp)
  =
  fun t ->
    {
      FStarC_Syntax_Syntax.residual_effect =
        FStarC_Parser_Const.effect_Tot_lid;
      FStarC_Syntax_Syntax.residual_typ = (FStar_Pervasives_Native.Some t);
      FStarC_Syntax_Syntax.residual_flags = [FStarC_Syntax_Syntax.TOTAL]
    }
let (residual_gtot :
  FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax ->
    FStarC_Syntax_Syntax.residual_comp)
  =
  fun t ->
    {
      FStarC_Syntax_Syntax.residual_effect =
        FStarC_Parser_Const.effect_GTot_lid;
      FStarC_Syntax_Syntax.residual_typ = (FStar_Pervasives_Native.Some t);
      FStarC_Syntax_Syntax.residual_flags = [FStarC_Syntax_Syntax.TOTAL]
    }
let (residual_comp_of_comp :
  FStarC_Syntax_Syntax.comp -> FStarC_Syntax_Syntax.residual_comp) =
  fun c ->
    let uu___ =
      FStarC_Compiler_List.filter
        (fun uu___1 ->
           match uu___1 with
           | FStarC_Syntax_Syntax.DECREASES uu___2 -> false
           | uu___2 -> true) (comp_flags c) in
    {
      FStarC_Syntax_Syntax.residual_effect = (comp_effect_name c);
      FStarC_Syntax_Syntax.residual_typ =
        (FStar_Pervasives_Native.Some (comp_result c));
      FStarC_Syntax_Syntax.residual_flags = uu___
    }
let (mk_forall_aux :
  FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax ->
    FStarC_Syntax_Syntax.bv ->
      FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax ->
        FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax)
  =
  fun fa ->
    fun x ->
      fun body ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              let uu___3 =
                FStarC_Syntax_Syntax.iarg x.FStarC_Syntax_Syntax.sort in
              let uu___4 =
                let uu___5 =
                  let uu___6 =
                    let uu___7 =
                      let uu___8 = FStarC_Syntax_Syntax.mk_binder x in
                      [uu___8] in
                    abs uu___7 body
                      (FStar_Pervasives_Native.Some (residual_tot ktype0)) in
                  FStarC_Syntax_Syntax.as_arg uu___6 in
                [uu___5] in
              uu___3 :: uu___4 in
            {
              FStarC_Syntax_Syntax.hd = fa;
              FStarC_Syntax_Syntax.args = uu___2
            } in
          FStarC_Syntax_Syntax.Tm_app uu___1 in
        FStarC_Syntax_Syntax.mk uu___ FStarC_Compiler_Range_Type.dummyRange
let (mk_forall_no_univ :
  FStarC_Syntax_Syntax.bv ->
    FStarC_Syntax_Syntax.typ -> FStarC_Syntax_Syntax.typ)
  = fun x -> fun body -> mk_forall_aux tforall x body
let (mk_forall :
  FStarC_Syntax_Syntax.universe ->
    FStarC_Syntax_Syntax.bv ->
      FStarC_Syntax_Syntax.typ -> FStarC_Syntax_Syntax.typ)
  =
  fun u ->
    fun x ->
      fun body ->
        let tforall1 = FStarC_Syntax_Syntax.mk_Tm_uinst tforall [u] in
        mk_forall_aux tforall1 x body
let (close_forall_no_univs :
  FStarC_Syntax_Syntax.binder Prims.list ->
    FStarC_Syntax_Syntax.typ -> FStarC_Syntax_Syntax.typ)
  =
  fun bs ->
    fun f ->
      FStarC_Compiler_List.fold_right
        (fun b ->
           fun f1 ->
             let uu___ = FStarC_Syntax_Syntax.is_null_binder b in
             if uu___
             then f1
             else mk_forall_no_univ b.FStarC_Syntax_Syntax.binder_bv f1) bs f
let (mk_exists_aux :
  FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax ->
    FStarC_Syntax_Syntax.bv ->
      FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax ->
        FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax)
  =
  fun fa ->
    fun x ->
      fun body ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              let uu___3 =
                FStarC_Syntax_Syntax.iarg x.FStarC_Syntax_Syntax.sort in
              let uu___4 =
                let uu___5 =
                  let uu___6 =
                    let uu___7 =
                      let uu___8 = FStarC_Syntax_Syntax.mk_binder x in
                      [uu___8] in
                    abs uu___7 body
                      (FStar_Pervasives_Native.Some (residual_tot ktype0)) in
                  FStarC_Syntax_Syntax.as_arg uu___6 in
                [uu___5] in
              uu___3 :: uu___4 in
            {
              FStarC_Syntax_Syntax.hd = fa;
              FStarC_Syntax_Syntax.args = uu___2
            } in
          FStarC_Syntax_Syntax.Tm_app uu___1 in
        FStarC_Syntax_Syntax.mk uu___ FStarC_Compiler_Range_Type.dummyRange
let (mk_exists_no_univ :
  FStarC_Syntax_Syntax.bv ->
    FStarC_Syntax_Syntax.typ -> FStarC_Syntax_Syntax.typ)
  = fun x -> fun body -> mk_exists_aux texists x body
let (mk_exists :
  FStarC_Syntax_Syntax.universe ->
    FStarC_Syntax_Syntax.bv ->
      FStarC_Syntax_Syntax.typ -> FStarC_Syntax_Syntax.typ)
  =
  fun u ->
    fun x ->
      fun body ->
        let texists1 = FStarC_Syntax_Syntax.mk_Tm_uinst texists [u] in
        mk_exists_aux texists1 x body
let (close_exists_no_univs :
  FStarC_Syntax_Syntax.binder Prims.list ->
    FStarC_Syntax_Syntax.typ -> FStarC_Syntax_Syntax.typ)
  =
  fun bs ->
    fun f ->
      FStarC_Compiler_List.fold_right
        (fun b ->
           fun f1 ->
             let uu___ = FStarC_Syntax_Syntax.is_null_binder b in
             if uu___
             then f1
             else mk_exists_no_univ b.FStarC_Syntax_Syntax.binder_bv f1) bs f
let (if_then_else :
  FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax ->
    FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax ->
      FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax ->
        FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax)
  =
  fun b ->
    fun t1 ->
      fun t2 ->
        let then_branch =
          let uu___ =
            FStarC_Syntax_Syntax.withinfo
              (FStarC_Syntax_Syntax.Pat_constant
                 (FStarC_Const.Const_bool true)) t1.FStarC_Syntax_Syntax.pos in
          (uu___, FStar_Pervasives_Native.None, t1) in
        let else_branch =
          let uu___ =
            FStarC_Syntax_Syntax.withinfo
              (FStarC_Syntax_Syntax.Pat_constant
                 (FStarC_Const.Const_bool false)) t2.FStarC_Syntax_Syntax.pos in
          (uu___, FStar_Pervasives_Native.None, t2) in
        let uu___ =
          let uu___1 =
            FStarC_Compiler_Range_Ops.union_ranges
              t1.FStarC_Syntax_Syntax.pos t2.FStarC_Syntax_Syntax.pos in
          FStarC_Compiler_Range_Ops.union_ranges b.FStarC_Syntax_Syntax.pos
            uu___1 in
        FStarC_Syntax_Syntax.mk
          (FStarC_Syntax_Syntax.Tm_match
             {
               FStarC_Syntax_Syntax.scrutinee = b;
               FStarC_Syntax_Syntax.ret_opt = FStar_Pervasives_Native.None;
               FStarC_Syntax_Syntax.brs = [then_branch; else_branch];
               FStarC_Syntax_Syntax.rc_opt1 = FStar_Pervasives_Native.None
             }) uu___
let (mk_squash :
  FStarC_Syntax_Syntax.universe ->
    FStarC_Syntax_Syntax.term ->
      FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax)
  =
  fun u ->
    fun p ->
      let sq =
        FStarC_Syntax_Syntax.fvar_with_dd FStarC_Parser_Const.squash_lid
          FStar_Pervasives_Native.None in
      let uu___ = FStarC_Syntax_Syntax.mk_Tm_uinst sq [u] in
      let uu___1 = let uu___2 = FStarC_Syntax_Syntax.as_arg p in [uu___2] in
      mk_app uu___ uu___1
let (mk_auto_squash :
  FStarC_Syntax_Syntax.universe ->
    FStarC_Syntax_Syntax.term ->
      FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax)
  =
  fun u ->
    fun p ->
      let sq =
        FStarC_Syntax_Syntax.fvar_with_dd FStarC_Parser_Const.auto_squash_lid
          FStar_Pervasives_Native.None in
      let uu___ = FStarC_Syntax_Syntax.mk_Tm_uinst sq [u] in
      let uu___1 = let uu___2 = FStarC_Syntax_Syntax.as_arg p in [uu___2] in
      mk_app uu___ uu___1
let (un_squash :
  FStarC_Syntax_Syntax.term ->
    FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option)
  =
  fun t ->
    let uu___ = head_and_args t in
    match uu___ with
    | (head, args) ->
        let head1 = unascribe head in
        let head2 = un_uinst head1 in
        let uu___1 =
          let uu___2 =
            let uu___3 = FStarC_Syntax_Subst.compress head2 in
            uu___3.FStarC_Syntax_Syntax.n in
          (uu___2, args) in
        (match uu___1 with
         | (FStarC_Syntax_Syntax.Tm_fvar fv, (p, uu___2)::[]) when
             FStarC_Syntax_Syntax.fv_eq_lid fv FStarC_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some p
         | (FStarC_Syntax_Syntax.Tm_refine
            { FStarC_Syntax_Syntax.b = b; FStarC_Syntax_Syntax.phi = p;_},
            []) ->
             (match (b.FStarC_Syntax_Syntax.sort).FStarC_Syntax_Syntax.n with
              | FStarC_Syntax_Syntax.Tm_fvar fv when
                  FStarC_Syntax_Syntax.fv_eq_lid fv
                    FStarC_Parser_Const.unit_lid
                  ->
                  let uu___2 =
                    let uu___3 =
                      let uu___4 = FStarC_Syntax_Syntax.mk_binder b in
                      [uu___4] in
                    FStarC_Syntax_Subst.open_term uu___3 p in
                  (match uu___2 with
                   | (bs, p1) ->
                       let b1 =
                         match bs with
                         | b2::[] -> b2
                         | uu___3 -> failwith "impossible" in
                       let uu___3 =
                         let uu___4 = FStarC_Syntax_Free.names p1 in
                         FStarC_Class_Setlike.mem ()
                           (Obj.magic
                              (FStarC_Compiler_FlatSet.setlike_flat_set
                                 FStarC_Syntax_Syntax.ord_bv))
                           b1.FStarC_Syntax_Syntax.binder_bv
                           (Obj.magic uu___4) in
                       if uu___3
                       then FStar_Pervasives_Native.None
                       else FStar_Pervasives_Native.Some p1)
              | uu___2 -> FStar_Pervasives_Native.None)
         | uu___2 -> FStar_Pervasives_Native.None)
let (is_squash :
  FStarC_Syntax_Syntax.term ->
    (FStarC_Syntax_Syntax.universe * FStarC_Syntax_Syntax.term'
      FStarC_Syntax_Syntax.syntax) FStar_Pervasives_Native.option)
  =
  fun t ->
    let uu___ = head_and_args t in
    match uu___ with
    | (head, args) ->
        let uu___1 =
          let uu___2 =
            let uu___3 = FStarC_Syntax_Subst.compress head in
            uu___3.FStarC_Syntax_Syntax.n in
          (uu___2, args) in
        (match uu___1 with
         | (FStarC_Syntax_Syntax.Tm_uinst
            ({ FStarC_Syntax_Syntax.n = FStarC_Syntax_Syntax.Tm_fvar fv;
               FStarC_Syntax_Syntax.pos = uu___2;
               FStarC_Syntax_Syntax.vars = uu___3;
               FStarC_Syntax_Syntax.hash_code = uu___4;_},
             u::[]),
            (t1, uu___5)::[]) when
             FStarC_Syntax_Syntax.fv_eq_lid fv FStarC_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu___2 -> FStar_Pervasives_Native.None)
let (is_auto_squash :
  FStarC_Syntax_Syntax.term ->
    (FStarC_Syntax_Syntax.universe * FStarC_Syntax_Syntax.term'
      FStarC_Syntax_Syntax.syntax) FStar_Pervasives_Native.option)
  =
  fun t ->
    let uu___ = head_and_args t in
    match uu___ with
    | (head, args) ->
        let uu___1 =
          let uu___2 =
            let uu___3 = FStarC_Syntax_Subst.compress head in
            uu___3.FStarC_Syntax_Syntax.n in
          (uu___2, args) in
        (match uu___1 with
         | (FStarC_Syntax_Syntax.Tm_uinst
            ({ FStarC_Syntax_Syntax.n = FStarC_Syntax_Syntax.Tm_fvar fv;
               FStarC_Syntax_Syntax.pos = uu___2;
               FStarC_Syntax_Syntax.vars = uu___3;
               FStarC_Syntax_Syntax.hash_code = uu___4;_},
             u::[]),
            (t1, uu___5)::[]) when
             FStarC_Syntax_Syntax.fv_eq_lid fv
               FStarC_Parser_Const.auto_squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu___2 -> FStar_Pervasives_Native.None)
let (is_sub_singleton : FStarC_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu___ = let uu___1 = unmeta t in head_and_args uu___1 in
    match uu___ with
    | (head, uu___1) ->
        let uu___2 =
          let uu___3 = un_uinst head in uu___3.FStarC_Syntax_Syntax.n in
        (match uu___2 with
         | FStarC_Syntax_Syntax.Tm_fvar fv ->
             (((((((((((((((((FStarC_Syntax_Syntax.fv_eq_lid fv
                                FStarC_Parser_Const.unit_lid)
                               ||
                               (FStarC_Syntax_Syntax.fv_eq_lid fv
                                  FStarC_Parser_Const.squash_lid))
                              ||
                              (FStarC_Syntax_Syntax.fv_eq_lid fv
                                 FStarC_Parser_Const.auto_squash_lid))
                             ||
                             (FStarC_Syntax_Syntax.fv_eq_lid fv
                                FStarC_Parser_Const.and_lid))
                            ||
                            (FStarC_Syntax_Syntax.fv_eq_lid fv
                               FStarC_Parser_Const.or_lid))
                           ||
                           (FStarC_Syntax_Syntax.fv_eq_lid fv
                              FStarC_Parser_Const.not_lid))
                          ||
                          (FStarC_Syntax_Syntax.fv_eq_lid fv
                             FStarC_Parser_Const.imp_lid))
                         ||
                         (FStarC_Syntax_Syntax.fv_eq_lid fv
                            FStarC_Parser_Const.iff_lid))
                        ||
                        (FStarC_Syntax_Syntax.fv_eq_lid fv
                           FStarC_Parser_Const.ite_lid))
                       ||
                       (FStarC_Syntax_Syntax.fv_eq_lid fv
                          FStarC_Parser_Const.exists_lid))
                      ||
                      (FStarC_Syntax_Syntax.fv_eq_lid fv
                         FStarC_Parser_Const.forall_lid))
                     ||
                     (FStarC_Syntax_Syntax.fv_eq_lid fv
                        FStarC_Parser_Const.true_lid))
                    ||
                    (FStarC_Syntax_Syntax.fv_eq_lid fv
                       FStarC_Parser_Const.false_lid))
                   ||
                   (FStarC_Syntax_Syntax.fv_eq_lid fv
                      FStarC_Parser_Const.eq2_lid))
                  ||
                  (FStarC_Syntax_Syntax.fv_eq_lid fv
                     FStarC_Parser_Const.b2t_lid))
                 ||
                 (FStarC_Syntax_Syntax.fv_eq_lid fv
                    FStarC_Parser_Const.haseq_lid))
                ||
                (FStarC_Syntax_Syntax.fv_eq_lid fv
                   FStarC_Parser_Const.has_type_lid))
               ||
               (FStarC_Syntax_Syntax.fv_eq_lid fv
                  FStarC_Parser_Const.precedes_lid)
         | uu___3 -> false)
let (arrow_one_ln :
  FStarC_Syntax_Syntax.typ ->
    (FStarC_Syntax_Syntax.binder * FStarC_Syntax_Syntax.comp)
      FStar_Pervasives_Native.option)
  =
  fun t ->
    let uu___ =
      let uu___1 = FStarC_Syntax_Subst.compress t in
      uu___1.FStarC_Syntax_Syntax.n in
    match uu___ with
    | FStarC_Syntax_Syntax.Tm_arrow
        { FStarC_Syntax_Syntax.bs1 = [];
          FStarC_Syntax_Syntax.comp = uu___1;_}
        -> failwith "fatal: empty binders on arrow?"
    | FStarC_Syntax_Syntax.Tm_arrow
        { FStarC_Syntax_Syntax.bs1 = b::[]; FStarC_Syntax_Syntax.comp = c;_}
        -> FStar_Pervasives_Native.Some (b, c)
    | FStarC_Syntax_Syntax.Tm_arrow
        { FStarC_Syntax_Syntax.bs1 = b::bs; FStarC_Syntax_Syntax.comp = c;_}
        ->
        let rng' =
          FStarC_Compiler_List.fold_left
            (fun a ->
               fun b1 ->
                 FStarC_Compiler_Range_Ops.union_ranges a
                   ((b1.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort).FStarC_Syntax_Syntax.pos)
            c.FStarC_Syntax_Syntax.pos bs in
        let c' =
          let uu___1 =
            FStarC_Syntax_Syntax.mk
              (FStarC_Syntax_Syntax.Tm_arrow
                 {
                   FStarC_Syntax_Syntax.bs1 = bs;
                   FStarC_Syntax_Syntax.comp = c
                 }) rng' in
          FStarC_Syntax_Syntax.mk_Total uu___1 in
        FStar_Pervasives_Native.Some (b, c')
    | uu___1 -> FStar_Pervasives_Native.None
let (arrow_one :
  FStarC_Syntax_Syntax.typ ->
    (FStarC_Syntax_Syntax.binder * FStarC_Syntax_Syntax.comp)
      FStar_Pervasives_Native.option)
  =
  fun t ->
    let uu___ = arrow_one_ln t in
    FStarC_Compiler_Util.bind_opt uu___
      (fun uu___1 ->
         match uu___1 with
         | (b, c) ->
             let uu___2 = FStarC_Syntax_Subst.open_comp [b] c in
             (match uu___2 with
              | (bs, c1) ->
                  let b1 =
                    match bs with
                    | b2::[] -> b2
                    | uu___3 ->
                        failwith
                          "impossible: open_comp returned different amount of binders" in
                  FStar_Pervasives_Native.Some (b1, c1)))
let (abs_one_ln :
  FStarC_Syntax_Syntax.typ ->
    (FStarC_Syntax_Syntax.binder * FStarC_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun t ->
    let uu___ =
      let uu___1 = FStarC_Syntax_Subst.compress t in
      uu___1.FStarC_Syntax_Syntax.n in
    match uu___ with
    | FStarC_Syntax_Syntax.Tm_abs
        { FStarC_Syntax_Syntax.bs = []; FStarC_Syntax_Syntax.body = uu___1;
          FStarC_Syntax_Syntax.rc_opt = uu___2;_}
        -> failwith "fatal: empty binders on abs?"
    | FStarC_Syntax_Syntax.Tm_abs
        { FStarC_Syntax_Syntax.bs = b::[]; FStarC_Syntax_Syntax.body = body;
          FStarC_Syntax_Syntax.rc_opt = uu___1;_}
        -> FStar_Pervasives_Native.Some (b, body)
    | FStarC_Syntax_Syntax.Tm_abs
        { FStarC_Syntax_Syntax.bs = b::bs; FStarC_Syntax_Syntax.body = body;
          FStarC_Syntax_Syntax.rc_opt = rc_opt;_}
        ->
        let uu___1 = let uu___2 = abs bs body rc_opt in (b, uu___2) in
        FStar_Pervasives_Native.Some uu___1
    | uu___1 -> FStar_Pervasives_Native.None
let (is_free_in :
  FStarC_Syntax_Syntax.bv -> FStarC_Syntax_Syntax.term -> Prims.bool) =
  fun bv ->
    fun t ->
      let uu___ = FStarC_Syntax_Free.names t in
      FStarC_Class_Setlike.mem ()
        (Obj.magic
           (FStarC_Compiler_FlatSet.setlike_flat_set
              FStarC_Syntax_Syntax.ord_bv)) bv (Obj.magic uu___)
let (action_as_lb :
  FStarC_Ident.lident ->
    FStarC_Syntax_Syntax.action ->
      FStarC_Compiler_Range_Type.range -> FStarC_Syntax_Syntax.sigelt)
  =
  fun eff_lid ->
    fun a ->
      fun pos ->
        let lb =
          let uu___ =
            let uu___1 =
              FStarC_Syntax_Syntax.lid_and_dd_as_fv
                a.FStarC_Syntax_Syntax.action_name
                FStar_Pervasives_Native.None in
            FStar_Pervasives.Inr uu___1 in
          let uu___1 =
            let uu___2 =
              FStarC_Syntax_Syntax.mk_Total a.FStarC_Syntax_Syntax.action_typ in
            arrow a.FStarC_Syntax_Syntax.action_params uu___2 in
          let uu___2 =
            abs a.FStarC_Syntax_Syntax.action_params
              a.FStarC_Syntax_Syntax.action_defn FStar_Pervasives_Native.None in
          close_univs_and_mk_letbinding FStar_Pervasives_Native.None uu___
            a.FStarC_Syntax_Syntax.action_univs uu___1
            FStarC_Parser_Const.effect_Tot_lid uu___2 [] pos in
        {
          FStarC_Syntax_Syntax.sigel =
            (FStarC_Syntax_Syntax.Sig_let
               {
                 FStarC_Syntax_Syntax.lbs1 = (false, [lb]);
                 FStarC_Syntax_Syntax.lids1 =
                   [a.FStarC_Syntax_Syntax.action_name]
               });
          FStarC_Syntax_Syntax.sigrng =
            ((a.FStarC_Syntax_Syntax.action_defn).FStarC_Syntax_Syntax.pos);
          FStarC_Syntax_Syntax.sigquals =
            [FStarC_Syntax_Syntax.Visible_default;
            FStarC_Syntax_Syntax.Action eff_lid];
          FStarC_Syntax_Syntax.sigmeta = FStarC_Syntax_Syntax.default_sigmeta;
          FStarC_Syntax_Syntax.sigattrs = [];
          FStarC_Syntax_Syntax.sigopens_and_abbrevs = [];
          FStarC_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
        }
let (mk_reify :
  FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax ->
    FStarC_Ident.lident FStar_Pervasives_Native.option ->
      FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax)
  =
  fun t ->
    fun lopt ->
      let reify_ =
        FStarC_Syntax_Syntax.mk
          (FStarC_Syntax_Syntax.Tm_constant (FStarC_Const.Const_reify lopt))
          t.FStarC_Syntax_Syntax.pos in
      let uu___ =
        let uu___1 =
          let uu___2 = let uu___3 = FStarC_Syntax_Syntax.as_arg t in [uu___3] in
          {
            FStarC_Syntax_Syntax.hd = reify_;
            FStarC_Syntax_Syntax.args = uu___2
          } in
        FStarC_Syntax_Syntax.Tm_app uu___1 in
      FStarC_Syntax_Syntax.mk uu___ t.FStarC_Syntax_Syntax.pos
let (mk_reflect :
  FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax ->
    FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax)
  =
  fun t ->
    let reflect_ =
      let uu___ =
        let uu___1 =
          let uu___2 = FStarC_Ident.lid_of_str "Bogus.Effect" in
          FStarC_Const.Const_reflect uu___2 in
        FStarC_Syntax_Syntax.Tm_constant uu___1 in
      FStarC_Syntax_Syntax.mk uu___ t.FStarC_Syntax_Syntax.pos in
    let uu___ =
      let uu___1 =
        let uu___2 = let uu___3 = FStarC_Syntax_Syntax.as_arg t in [uu___3] in
        {
          FStarC_Syntax_Syntax.hd = reflect_;
          FStarC_Syntax_Syntax.args = uu___2
        } in
      FStarC_Syntax_Syntax.Tm_app uu___1 in
    FStarC_Syntax_Syntax.mk uu___ t.FStarC_Syntax_Syntax.pos
let rec (incr_delta_depth :
  FStarC_Syntax_Syntax.delta_depth -> FStarC_Syntax_Syntax.delta_depth) =
  fun d ->
    match d with
    | FStarC_Syntax_Syntax.Delta_constant_at_level i ->
        FStarC_Syntax_Syntax.Delta_constant_at_level (i + Prims.int_one)
    | FStarC_Syntax_Syntax.Delta_equational_at_level i ->
        FStarC_Syntax_Syntax.Delta_equational_at_level (i + Prims.int_one)
    | FStarC_Syntax_Syntax.Delta_abstract d1 -> incr_delta_depth d1
let (is_unknown : FStarC_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu___ =
      let uu___1 = FStarC_Syntax_Subst.compress t in
      uu___1.FStarC_Syntax_Syntax.n in
    match uu___ with
    | FStarC_Syntax_Syntax.Tm_unknown -> true
    | uu___1 -> false
let rec apply_last :
  'uuuuu . ('uuuuu -> 'uuuuu) -> 'uuuuu Prims.list -> 'uuuuu Prims.list =
  fun f ->
    fun l ->
      match l with
      | [] -> failwith "apply_last: got empty list"
      | a::[] -> let uu___ = f a in [uu___]
      | x::xs -> let uu___ = apply_last f xs in x :: uu___
let (dm4f_lid :
  FStarC_Syntax_Syntax.eff_decl -> Prims.string -> FStarC_Ident.lident) =
  fun ed ->
    fun name ->
      let p = FStarC_Ident.path_of_lid ed.FStarC_Syntax_Syntax.mname in
      let p' =
        apply_last
          (fun s ->
             Prims.strcat "_dm4f_" (Prims.strcat s (Prims.strcat "_" name)))
          p in
      FStarC_Ident.lid_of_path p' FStarC_Compiler_Range_Type.dummyRange
let (mk_list :
  FStarC_Syntax_Syntax.term ->
    FStarC_Compiler_Range_Type.range ->
      FStarC_Syntax_Syntax.term Prims.list -> FStarC_Syntax_Syntax.term)
  =
  fun typ ->
    fun rng ->
      fun l ->
        let ctor l1 =
          let uu___ =
            let uu___1 =
              FStarC_Syntax_Syntax.lid_as_fv l1
                (FStar_Pervasives_Native.Some FStarC_Syntax_Syntax.Data_ctor) in
            FStarC_Syntax_Syntax.Tm_fvar uu___1 in
          FStarC_Syntax_Syntax.mk uu___ rng in
        let cons args pos =
          let uu___ =
            let uu___1 = ctor FStarC_Parser_Const.cons_lid in
            FStarC_Syntax_Syntax.mk_Tm_uinst uu___1
              [FStarC_Syntax_Syntax.U_zero] in
          FStarC_Syntax_Syntax.mk_Tm_app uu___ args pos in
        let nil args pos =
          let uu___ =
            let uu___1 = ctor FStarC_Parser_Const.nil_lid in
            FStarC_Syntax_Syntax.mk_Tm_uinst uu___1
              [FStarC_Syntax_Syntax.U_zero] in
          FStarC_Syntax_Syntax.mk_Tm_app uu___ args pos in
        let uu___ =
          let uu___1 = let uu___2 = FStarC_Syntax_Syntax.iarg typ in [uu___2] in
          nil uu___1 rng in
        FStarC_Compiler_List.fold_right
          (fun t ->
             fun a ->
               let uu___1 =
                 let uu___2 = FStarC_Syntax_Syntax.iarg typ in
                 let uu___3 =
                   let uu___4 = FStarC_Syntax_Syntax.as_arg t in
                   let uu___5 =
                     let uu___6 = FStarC_Syntax_Syntax.as_arg a in [uu___6] in
                   uu___4 :: uu___5 in
                 uu___2 :: uu___3 in
               cons uu___1 t.FStarC_Syntax_Syntax.pos) l uu___
let rec eqlist :
  'a .
    ('a -> 'a -> Prims.bool) -> 'a Prims.list -> 'a Prims.list -> Prims.bool
  =
  fun eq ->
    fun xs ->
      fun ys ->
        match (xs, ys) with
        | ([], []) -> true
        | (x::xs1, y::ys1) -> (eq x y) && (eqlist eq xs1 ys1)
        | uu___ -> false
let eqsum :
  'a 'b .
    ('a -> 'a -> Prims.bool) ->
      ('b -> 'b -> Prims.bool) ->
        ('a, 'b) FStar_Pervasives.either ->
          ('a, 'b) FStar_Pervasives.either -> Prims.bool
  =
  fun e1 ->
    fun e2 ->
      fun x ->
        fun y ->
          match (x, y) with
          | (FStar_Pervasives.Inl x1, FStar_Pervasives.Inl y1) -> e1 x1 y1
          | (FStar_Pervasives.Inr x1, FStar_Pervasives.Inr y1) -> e2 x1 y1
          | uu___ -> false
let eqprod :
  'a 'b .
    ('a -> 'a -> Prims.bool) ->
      ('b -> 'b -> Prims.bool) -> ('a * 'b) -> ('a * 'b) -> Prims.bool
  =
  fun e1 ->
    fun e2 ->
      fun x ->
        fun y ->
          match (x, y) with
          | ((x1, x2), (y1, y2)) -> (e1 x1 y1) && (e2 x2 y2)
let eqopt :
  'a .
    ('a -> 'a -> Prims.bool) ->
      'a FStar_Pervasives_Native.option ->
        'a FStar_Pervasives_Native.option -> Prims.bool
  =
  fun e ->
    fun x ->
      fun y ->
        match (x, y) with
        | (FStar_Pervasives_Native.Some x1, FStar_Pervasives_Native.Some y1)
            -> e x1 y1
        | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) ->
            true
        | uu___ -> false
let (debug_term_eq : Prims.bool FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Util.mk_ref false
let (check : Prims.bool -> Prims.string -> Prims.bool -> Prims.bool) =
  fun dbg ->
    fun msg ->
      fun cond ->
        if cond
        then true
        else
          (if dbg
           then FStarC_Compiler_Util.print1 ">>> term_eq failing: %s\n" msg
           else ();
           false)
let (fail : Prims.bool -> Prims.string -> Prims.bool) =
  fun dbg -> fun msg -> check dbg msg false
let rec (term_eq_dbg :
  Prims.bool ->
    FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term -> Prims.bool)
  =
  fun dbg ->
    fun t1 ->
      fun t2 ->
        let t11 = let uu___ = unmeta_safe t1 in canon_app uu___ in
        let t21 = let uu___ = unmeta_safe t2 in canon_app uu___ in
        let check1 = check dbg in
        let fail1 = fail dbg in
        let uu___ =
          let uu___1 =
            let uu___2 =
              let uu___3 = un_uinst t11 in
              FStarC_Syntax_Subst.compress uu___3 in
            uu___2.FStarC_Syntax_Syntax.n in
          let uu___2 =
            let uu___3 =
              let uu___4 = un_uinst t21 in
              FStarC_Syntax_Subst.compress uu___4 in
            uu___3.FStarC_Syntax_Syntax.n in
          (uu___1, uu___2) in
        match uu___ with
        | (FStarC_Syntax_Syntax.Tm_uinst uu___1, uu___2) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu___1, FStarC_Syntax_Syntax.Tm_uinst uu___2) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStarC_Syntax_Syntax.Tm_delayed uu___1, uu___2) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu___1, FStarC_Syntax_Syntax.Tm_delayed uu___2) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStarC_Syntax_Syntax.Tm_ascribed uu___1, uu___2) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu___1, FStarC_Syntax_Syntax.Tm_ascribed uu___2) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStarC_Syntax_Syntax.Tm_bvar x, FStarC_Syntax_Syntax.Tm_bvar y) ->
            check1 "bvar"
              (x.FStarC_Syntax_Syntax.index = y.FStarC_Syntax_Syntax.index)
        | (FStarC_Syntax_Syntax.Tm_name x, FStarC_Syntax_Syntax.Tm_name y) ->
            check1 "name"
              (x.FStarC_Syntax_Syntax.index = y.FStarC_Syntax_Syntax.index)
        | (FStarC_Syntax_Syntax.Tm_fvar x, FStarC_Syntax_Syntax.Tm_fvar y) ->
            let uu___1 = FStarC_Syntax_Syntax.fv_eq x y in
            check1 "fvar" uu___1
        | (FStarC_Syntax_Syntax.Tm_constant c1,
           FStarC_Syntax_Syntax.Tm_constant c2) ->
            let uu___1 = FStarC_Const.eq_const c1 c2 in check1 "const" uu___1
        | (FStarC_Syntax_Syntax.Tm_type uu___1, FStarC_Syntax_Syntax.Tm_type
           uu___2) -> true
        | (FStarC_Syntax_Syntax.Tm_abs
           { FStarC_Syntax_Syntax.bs = b1; FStarC_Syntax_Syntax.body = t12;
             FStarC_Syntax_Syntax.rc_opt = k1;_},
           FStarC_Syntax_Syntax.Tm_abs
           { FStarC_Syntax_Syntax.bs = b2; FStarC_Syntax_Syntax.body = t22;
             FStarC_Syntax_Syntax.rc_opt = k2;_})
            ->
            (let uu___1 = eqlist (binder_eq_dbg dbg) b1 b2 in
             check1 "abs binders" uu___1) &&
              (let uu___1 = term_eq_dbg dbg t12 t22 in
               check1 "abs bodies" uu___1)
        | (FStarC_Syntax_Syntax.Tm_arrow
           { FStarC_Syntax_Syntax.bs1 = b1; FStarC_Syntax_Syntax.comp = c1;_},
           FStarC_Syntax_Syntax.Tm_arrow
           { FStarC_Syntax_Syntax.bs1 = b2; FStarC_Syntax_Syntax.comp = c2;_})
            ->
            (let uu___1 = eqlist (binder_eq_dbg dbg) b1 b2 in
             check1 "arrow binders" uu___1) &&
              (let uu___1 = comp_eq_dbg dbg c1 c2 in
               check1 "arrow comp" uu___1)
        | (FStarC_Syntax_Syntax.Tm_refine
           { FStarC_Syntax_Syntax.b = b1; FStarC_Syntax_Syntax.phi = t12;_},
           FStarC_Syntax_Syntax.Tm_refine
           { FStarC_Syntax_Syntax.b = b2; FStarC_Syntax_Syntax.phi = t22;_})
            ->
            (let uu___1 =
               term_eq_dbg dbg b1.FStarC_Syntax_Syntax.sort
                 b2.FStarC_Syntax_Syntax.sort in
             check1 "refine bv sort" uu___1) &&
              (let uu___1 = term_eq_dbg dbg t12 t22 in
               check1 "refine formula" uu___1)
        | (FStarC_Syntax_Syntax.Tm_app
           { FStarC_Syntax_Syntax.hd = f1; FStarC_Syntax_Syntax.args = a1;_},
           FStarC_Syntax_Syntax.Tm_app
           { FStarC_Syntax_Syntax.hd = f2; FStarC_Syntax_Syntax.args = a2;_})
            ->
            (let uu___1 = term_eq_dbg dbg f1 f2 in check1 "app head" uu___1)
              &&
              (let uu___1 = eqlist (arg_eq_dbg dbg) a1 a2 in
               check1 "app args" uu___1)
        | (FStarC_Syntax_Syntax.Tm_match
           { FStarC_Syntax_Syntax.scrutinee = t12;
             FStarC_Syntax_Syntax.ret_opt = FStar_Pervasives_Native.None;
             FStarC_Syntax_Syntax.brs = bs1;
             FStarC_Syntax_Syntax.rc_opt1 = uu___1;_},
           FStarC_Syntax_Syntax.Tm_match
           { FStarC_Syntax_Syntax.scrutinee = t22;
             FStarC_Syntax_Syntax.ret_opt = FStar_Pervasives_Native.None;
             FStarC_Syntax_Syntax.brs = bs2;
             FStarC_Syntax_Syntax.rc_opt1 = uu___2;_})
            ->
            (let uu___3 = term_eq_dbg dbg t12 t22 in
             check1 "match head" uu___3) &&
              (let uu___3 = eqlist (branch_eq_dbg dbg) bs1 bs2 in
               check1 "match branches" uu___3)
        | (FStarC_Syntax_Syntax.Tm_lazy uu___1, uu___2) ->
            let uu___3 =
              let uu___4 = unlazy t11 in term_eq_dbg dbg uu___4 t21 in
            check1 "lazy_l" uu___3
        | (uu___1, FStarC_Syntax_Syntax.Tm_lazy uu___2) ->
            let uu___3 =
              let uu___4 = unlazy t21 in term_eq_dbg dbg t11 uu___4 in
            check1 "lazy_r" uu___3
        | (FStarC_Syntax_Syntax.Tm_let
           { FStarC_Syntax_Syntax.lbs = (b1, lbs1);
             FStarC_Syntax_Syntax.body1 = t12;_},
           FStarC_Syntax_Syntax.Tm_let
           { FStarC_Syntax_Syntax.lbs = (b2, lbs2);
             FStarC_Syntax_Syntax.body1 = t22;_})
            ->
            ((check1 "let flag" (b1 = b2)) &&
               (let uu___1 = eqlist (letbinding_eq_dbg dbg) lbs1 lbs2 in
                check1 "let lbs" uu___1))
              &&
              (let uu___1 = term_eq_dbg dbg t12 t22 in
               check1 "let body" uu___1)
        | (FStarC_Syntax_Syntax.Tm_uvar (u1, uu___1),
           FStarC_Syntax_Syntax.Tm_uvar (u2, uu___2)) ->
            check1 "uvar"
              (u1.FStarC_Syntax_Syntax.ctx_uvar_head =
                 u2.FStarC_Syntax_Syntax.ctx_uvar_head)
        | (FStarC_Syntax_Syntax.Tm_quoted (qt1, qi1),
           FStarC_Syntax_Syntax.Tm_quoted (qt2, qi2)) ->
            (let uu___1 = quote_info_eq_dbg dbg qi1 qi2 in
             check1 "tm_quoted qi" uu___1) &&
              (let uu___1 = term_eq_dbg dbg qt1 qt2 in
               check1 "tm_quoted payload" uu___1)
        | (FStarC_Syntax_Syntax.Tm_meta
           { FStarC_Syntax_Syntax.tm2 = t12;
             FStarC_Syntax_Syntax.meta = m1;_},
           FStarC_Syntax_Syntax.Tm_meta
           { FStarC_Syntax_Syntax.tm2 = t22;
             FStarC_Syntax_Syntax.meta = m2;_})
            ->
            (match (m1, m2) with
             | (FStarC_Syntax_Syntax.Meta_monadic (n1, ty1),
                FStarC_Syntax_Syntax.Meta_monadic (n2, ty2)) ->
                 (let uu___1 = FStarC_Ident.lid_equals n1 n2 in
                  check1 "meta_monadic lid" uu___1) &&
                   (let uu___1 = term_eq_dbg dbg ty1 ty2 in
                    check1 "meta_monadic type" uu___1)
             | (FStarC_Syntax_Syntax.Meta_monadic_lift (s1, t13, ty1),
                FStarC_Syntax_Syntax.Meta_monadic_lift (s2, t23, ty2)) ->
                 ((let uu___1 = FStarC_Ident.lid_equals s1 s2 in
                   check1 "meta_monadic_lift src" uu___1) &&
                    (let uu___1 = FStarC_Ident.lid_equals t13 t23 in
                     check1 "meta_monadic_lift tgt" uu___1))
                   &&
                   (let uu___1 = term_eq_dbg dbg ty1 ty2 in
                    check1 "meta_monadic_lift type" uu___1)
             | uu___1 -> fail1 "metas")
        | (FStarC_Syntax_Syntax.Tm_unknown, uu___1) -> fail1 "unk"
        | (uu___1, FStarC_Syntax_Syntax.Tm_unknown) -> fail1 "unk"
        | (FStarC_Syntax_Syntax.Tm_bvar uu___1, uu___2) -> fail1 "bottom"
        | (FStarC_Syntax_Syntax.Tm_name uu___1, uu___2) -> fail1 "bottom"
        | (FStarC_Syntax_Syntax.Tm_fvar uu___1, uu___2) -> fail1 "bottom"
        | (FStarC_Syntax_Syntax.Tm_constant uu___1, uu___2) -> fail1 "bottom"
        | (FStarC_Syntax_Syntax.Tm_type uu___1, uu___2) -> fail1 "bottom"
        | (FStarC_Syntax_Syntax.Tm_abs uu___1, uu___2) -> fail1 "bottom"
        | (FStarC_Syntax_Syntax.Tm_arrow uu___1, uu___2) -> fail1 "bottom"
        | (FStarC_Syntax_Syntax.Tm_refine uu___1, uu___2) -> fail1 "bottom"
        | (FStarC_Syntax_Syntax.Tm_app uu___1, uu___2) -> fail1 "bottom"
        | (FStarC_Syntax_Syntax.Tm_match uu___1, uu___2) -> fail1 "bottom"
        | (FStarC_Syntax_Syntax.Tm_let uu___1, uu___2) -> fail1 "bottom"
        | (FStarC_Syntax_Syntax.Tm_uvar uu___1, uu___2) -> fail1 "bottom"
        | (FStarC_Syntax_Syntax.Tm_meta uu___1, uu___2) -> fail1 "bottom"
        | (uu___1, FStarC_Syntax_Syntax.Tm_bvar uu___2) -> fail1 "bottom"
        | (uu___1, FStarC_Syntax_Syntax.Tm_name uu___2) -> fail1 "bottom"
        | (uu___1, FStarC_Syntax_Syntax.Tm_fvar uu___2) -> fail1 "bottom"
        | (uu___1, FStarC_Syntax_Syntax.Tm_constant uu___2) -> fail1 "bottom"
        | (uu___1, FStarC_Syntax_Syntax.Tm_type uu___2) -> fail1 "bottom"
        | (uu___1, FStarC_Syntax_Syntax.Tm_abs uu___2) -> fail1 "bottom"
        | (uu___1, FStarC_Syntax_Syntax.Tm_arrow uu___2) -> fail1 "bottom"
        | (uu___1, FStarC_Syntax_Syntax.Tm_refine uu___2) -> fail1 "bottom"
        | (uu___1, FStarC_Syntax_Syntax.Tm_app uu___2) -> fail1 "bottom"
        | (uu___1, FStarC_Syntax_Syntax.Tm_match uu___2) -> fail1 "bottom"
        | (uu___1, FStarC_Syntax_Syntax.Tm_let uu___2) -> fail1 "bottom"
        | (uu___1, FStarC_Syntax_Syntax.Tm_uvar uu___2) -> fail1 "bottom"
        | (uu___1, FStarC_Syntax_Syntax.Tm_meta uu___2) -> fail1 "bottom"
and (arg_eq_dbg :
  Prims.bool ->
    (FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax *
      FStarC_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) ->
      (FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax *
        FStarC_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) ->
        Prims.bool)
  =
  fun dbg ->
    fun a1 ->
      fun a2 ->
        eqprod
          (fun t1 ->
             fun t2 ->
               let uu___ = term_eq_dbg dbg t1 t2 in check dbg "arg tm" uu___)
          (fun q1 ->
             fun q2 ->
               let uu___ = aqual_eq_dbg dbg q1 q2 in
               check dbg "arg qual" uu___) a1 a2
and (binder_eq_dbg :
  Prims.bool ->
    FStarC_Syntax_Syntax.binder -> FStarC_Syntax_Syntax.binder -> Prims.bool)
  =
  fun dbg ->
    fun b1 ->
      fun b2 ->
        ((let uu___ =
            term_eq_dbg dbg
              (b1.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort
              (b2.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
          check dbg "binder_sort" uu___) &&
           (let uu___ =
              bqual_eq_dbg dbg b1.FStarC_Syntax_Syntax.binder_qual
                b2.FStarC_Syntax_Syntax.binder_qual in
            check dbg "binder qual" uu___))
          &&
          (let uu___ =
             eqlist (term_eq_dbg dbg) b1.FStarC_Syntax_Syntax.binder_attrs
               b2.FStarC_Syntax_Syntax.binder_attrs in
           check dbg "binder attrs" uu___)
and (comp_eq_dbg :
  Prims.bool ->
    FStarC_Syntax_Syntax.comp' FStarC_Syntax_Syntax.syntax ->
      FStarC_Syntax_Syntax.comp' FStarC_Syntax_Syntax.syntax -> Prims.bool)
  =
  fun dbg ->
    fun c1 ->
      fun c2 ->
        let uu___ = comp_eff_name_res_and_args c1 in
        match uu___ with
        | (eff1, res1, args1) ->
            let uu___1 = comp_eff_name_res_and_args c2 in
            (match uu___1 with
             | (eff2, res2, args2) ->
                 ((let uu___2 = FStarC_Ident.lid_equals eff1 eff2 in
                   check dbg "comp eff" uu___2) &&
                    (let uu___2 = term_eq_dbg dbg res1 res2 in
                     check dbg "comp result typ" uu___2))
                   && true)
and (branch_eq_dbg :
  Prims.bool ->
    (FStarC_Syntax_Syntax.pat' FStarC_Syntax_Syntax.withinfo_t *
      FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option * FStarC_Syntax_Syntax.term'
      FStarC_Syntax_Syntax.syntax) ->
      (FStarC_Syntax_Syntax.pat' FStarC_Syntax_Syntax.withinfo_t *
        FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax
        FStar_Pervasives_Native.option * FStarC_Syntax_Syntax.term'
        FStarC_Syntax_Syntax.syntax) -> Prims.bool)
  =
  fun dbg ->
    fun uu___ ->
      fun uu___1 ->
        match (uu___, uu___1) with
        | ((p1, w1, t1), (p2, w2, t2)) ->
            ((let uu___2 = FStarC_Syntax_Syntax.eq_pat p1 p2 in
              check dbg "branch pat" uu___2) &&
               (let uu___2 = term_eq_dbg dbg t1 t2 in
                check dbg "branch body" uu___2))
              &&
              (let uu___2 =
                 match (w1, w2) with
                 | (FStar_Pervasives_Native.Some x,
                    FStar_Pervasives_Native.Some y) -> term_eq_dbg dbg x y
                 | (FStar_Pervasives_Native.None,
                    FStar_Pervasives_Native.None) -> true
                 | uu___3 -> false in
               check dbg "branch when" uu___2)
and (letbinding_eq_dbg :
  Prims.bool ->
    FStarC_Syntax_Syntax.letbinding ->
      FStarC_Syntax_Syntax.letbinding -> Prims.bool)
  =
  fun dbg ->
    fun lb1 ->
      fun lb2 ->
        ((let uu___ =
            eqsum (fun bv1 -> fun bv2 -> true) FStarC_Syntax_Syntax.fv_eq
              lb1.FStarC_Syntax_Syntax.lbname lb2.FStarC_Syntax_Syntax.lbname in
          check dbg "lb bv" uu___) &&
           (let uu___ =
              term_eq_dbg dbg lb1.FStarC_Syntax_Syntax.lbtyp
                lb2.FStarC_Syntax_Syntax.lbtyp in
            check dbg "lb typ" uu___))
          &&
          (let uu___ =
             term_eq_dbg dbg lb1.FStarC_Syntax_Syntax.lbdef
               lb2.FStarC_Syntax_Syntax.lbdef in
           check dbg "lb def" uu___)
and (quote_info_eq_dbg :
  Prims.bool ->
    FStarC_Syntax_Syntax.quoteinfo ->
      FStarC_Syntax_Syntax.quoteinfo -> Prims.bool)
  =
  fun dbg ->
    fun q1 ->
      fun q2 ->
        if q1.FStarC_Syntax_Syntax.qkind <> q2.FStarC_Syntax_Syntax.qkind
        then false
        else
          antiquotations_eq_dbg dbg
            (FStar_Pervasives_Native.snd
               q1.FStarC_Syntax_Syntax.antiquotations)
            (FStar_Pervasives_Native.snd
               q2.FStarC_Syntax_Syntax.antiquotations)
and (antiquotations_eq_dbg :
  Prims.bool ->
    FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax Prims.list ->
      FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax Prims.list ->
        Prims.bool)
  =
  fun dbg ->
    fun a1 ->
      fun a2 ->
        match (a1, a2) with
        | ([], []) -> true
        | ([], uu___) -> false
        | (uu___, []) -> false
        | (t1::a11, t2::a21) ->
            let uu___ =
              let uu___1 = term_eq_dbg dbg t1 t2 in Prims.op_Negation uu___1 in
            if uu___ then false else antiquotations_eq_dbg dbg a11 a21
and (bqual_eq_dbg :
  Prims.bool ->
    FStarC_Syntax_Syntax.binder_qualifier FStar_Pervasives_Native.option ->
      FStarC_Syntax_Syntax.binder_qualifier FStar_Pervasives_Native.option ->
        Prims.bool)
  =
  fun dbg ->
    fun a1 ->
      fun a2 ->
        match (a1, a2) with
        | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) ->
            true
        | (FStar_Pervasives_Native.None, uu___) -> false
        | (uu___, FStar_Pervasives_Native.None) -> false
        | (FStar_Pervasives_Native.Some (FStarC_Syntax_Syntax.Implicit b1),
           FStar_Pervasives_Native.Some (FStarC_Syntax_Syntax.Implicit b2))
            when b1 = b2 -> true
        | (FStar_Pervasives_Native.Some (FStarC_Syntax_Syntax.Meta t1),
           FStar_Pervasives_Native.Some (FStarC_Syntax_Syntax.Meta t2)) ->
            term_eq_dbg dbg t1 t2
        | (FStar_Pervasives_Native.Some (FStarC_Syntax_Syntax.Equality),
           FStar_Pervasives_Native.Some (FStarC_Syntax_Syntax.Equality)) ->
            true
        | uu___ -> false
and (aqual_eq_dbg :
  Prims.bool ->
    FStarC_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
      FStarC_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
        Prims.bool)
  =
  fun dbg ->
    fun a1 ->
      fun a2 ->
        match (a1, a2) with
        | (FStar_Pervasives_Native.Some a11, FStar_Pervasives_Native.Some
           a21) ->
            if
              (a11.FStarC_Syntax_Syntax.aqual_implicit =
                 a21.FStarC_Syntax_Syntax.aqual_implicit)
                &&
                ((FStarC_Compiler_List.length
                    a11.FStarC_Syntax_Syntax.aqual_attributes)
                   =
                   (FStarC_Compiler_List.length
                      a21.FStarC_Syntax_Syntax.aqual_attributes))
            then
              FStarC_Compiler_List.fold_left2
                (fun out ->
                   fun t1 ->
                     fun t2 ->
                       if Prims.op_Negation out
                       then false
                       else term_eq_dbg dbg t1 t2) true
                a11.FStarC_Syntax_Syntax.aqual_attributes
                a21.FStarC_Syntax_Syntax.aqual_attributes
            else false
        | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) ->
            true
        | uu___ -> false
let (eq_aqual :
  FStarC_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
    FStarC_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
      Prims.bool)
  = fun a1 -> fun a2 -> aqual_eq_dbg false a1 a2
let (eq_bqual :
  FStarC_Syntax_Syntax.binder_qualifier FStar_Pervasives_Native.option ->
    FStarC_Syntax_Syntax.binder_qualifier FStar_Pervasives_Native.option ->
      Prims.bool)
  = fun b1 -> fun b2 -> bqual_eq_dbg false b1 b2
let (term_eq :
  FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term -> Prims.bool) =
  fun t1 ->
    fun t2 ->
      let r =
        let uu___ = FStarC_Compiler_Effect.op_Bang debug_term_eq in
        term_eq_dbg uu___ t1 t2 in
      FStarC_Compiler_Effect.op_Colon_Equals debug_term_eq false; r
let rec (sizeof : FStarC_Syntax_Syntax.term -> Prims.int) =
  fun t ->
    match t.FStarC_Syntax_Syntax.n with
    | FStarC_Syntax_Syntax.Tm_delayed uu___ ->
        let uu___1 =
          let uu___2 = FStarC_Syntax_Subst.compress t in sizeof uu___2 in
        Prims.int_one + uu___1
    | FStarC_Syntax_Syntax.Tm_bvar bv ->
        let uu___ = sizeof bv.FStarC_Syntax_Syntax.sort in
        Prims.int_one + uu___
    | FStarC_Syntax_Syntax.Tm_name bv ->
        let uu___ = sizeof bv.FStarC_Syntax_Syntax.sort in
        Prims.int_one + uu___
    | FStarC_Syntax_Syntax.Tm_uinst (t1, us) ->
        let uu___ = sizeof t1 in (FStarC_Compiler_List.length us) + uu___
    | FStarC_Syntax_Syntax.Tm_abs
        { FStarC_Syntax_Syntax.bs = bs; FStarC_Syntax_Syntax.body = t1;
          FStarC_Syntax_Syntax.rc_opt = uu___;_}
        ->
        let uu___1 = sizeof t1 in
        let uu___2 =
          FStarC_Compiler_List.fold_left
            (fun acc ->
               fun b ->
                 let uu___3 =
                   sizeof
                     (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
                 acc + uu___3) Prims.int_zero bs in
        uu___1 + uu___2
    | FStarC_Syntax_Syntax.Tm_app
        { FStarC_Syntax_Syntax.hd = hd; FStarC_Syntax_Syntax.args = args;_}
        ->
        let uu___ = sizeof hd in
        let uu___1 =
          FStarC_Compiler_List.fold_left
            (fun acc ->
               fun uu___2 ->
                 match uu___2 with
                 | (arg, uu___3) -> let uu___4 = sizeof arg in acc + uu___4)
            Prims.int_zero args in
        uu___ + uu___1
    | uu___ -> Prims.int_one
let (is_fvar :
  FStarC_Ident.lident -> FStarC_Syntax_Syntax.term -> Prims.bool) =
  fun lid ->
    fun t ->
      let uu___ = let uu___1 = un_uinst t in uu___1.FStarC_Syntax_Syntax.n in
      match uu___ with
      | FStarC_Syntax_Syntax.Tm_fvar fv ->
          FStarC_Syntax_Syntax.fv_eq_lid fv lid
      | uu___1 -> false
let (is_synth_by_tactic : FStarC_Syntax_Syntax.term -> Prims.bool) =
  fun t -> is_fvar FStarC_Parser_Const.synth_lid t
let (has_attribute :
  FStarC_Syntax_Syntax.attribute Prims.list ->
    FStarC_Ident.lident -> Prims.bool)
  =
  fun attrs -> fun attr -> FStarC_Compiler_Util.for_some (is_fvar attr) attrs
let (get_attribute :
  FStarC_Ident.lident ->
    FStarC_Syntax_Syntax.attribute Prims.list ->
      FStarC_Syntax_Syntax.args FStar_Pervasives_Native.option)
  =
  fun attr ->
    fun attrs ->
      FStarC_Compiler_List.tryPick
        (fun t ->
           let uu___ = head_and_args t in
           match uu___ with
           | (head, args) ->
               let uu___1 =
                 let uu___2 = FStarC_Syntax_Subst.compress head in
                 uu___2.FStarC_Syntax_Syntax.n in
               (match uu___1 with
                | FStarC_Syntax_Syntax.Tm_fvar fv when
                    FStarC_Syntax_Syntax.fv_eq_lid fv attr ->
                    FStar_Pervasives_Native.Some args
                | uu___2 -> FStar_Pervasives_Native.None)) attrs
let (remove_attr :
  FStarC_Ident.lident ->
    FStarC_Syntax_Syntax.attribute Prims.list ->
      FStarC_Syntax_Syntax.attribute Prims.list)
  =
  fun attr ->
    fun attrs ->
      FStarC_Compiler_List.filter
        (fun a -> let uu___ = is_fvar attr a in Prims.op_Negation uu___)
        attrs
let (process_pragma :
  FStarC_Syntax_Syntax.pragma -> FStarC_Compiler_Range_Type.range -> unit) =
  fun p ->
    fun r ->
      FStarC_Errors.set_option_warning_callback_range
        (FStar_Pervasives_Native.Some r);
      (let set_options s =
         let uu___1 = FStarC_Options.set_options s in
         match uu___1 with
         | FStarC_Getopt.Success -> ()
         | FStarC_Getopt.Help ->
             FStarC_Errors.raise_error FStarC_Class_HasRange.hasRange_range r
               FStarC_Errors_Codes.Fatal_FailToProcessPragma ()
               (Obj.magic FStarC_Errors_Msg.is_error_message_string)
               (Obj.magic
                  "Failed to process pragma: use 'fstar --help' to see which options are available")
         | FStarC_Getopt.Error s1 ->
             FStarC_Errors.raise_error FStarC_Class_HasRange.hasRange_range r
               FStarC_Errors_Codes.Fatal_FailToProcessPragma ()
               (Obj.magic FStarC_Errors_Msg.is_error_message_string)
               (Obj.magic (Prims.strcat "Failed to process pragma: " s1)) in
       match p with
       | FStarC_Syntax_Syntax.ShowOptions -> ()
       | FStarC_Syntax_Syntax.SetOptions o -> set_options o
       | FStarC_Syntax_Syntax.ResetOptions sopt ->
           ((let uu___2 = FStarC_Options.restore_cmd_line_options false in ());
            (match sopt with
             | FStar_Pervasives_Native.None -> ()
             | FStar_Pervasives_Native.Some s -> set_options s))
       | FStarC_Syntax_Syntax.PushOptions sopt ->
           (FStarC_Options.internal_push ();
            (match sopt with
             | FStar_Pervasives_Native.None -> ()
             | FStar_Pervasives_Native.Some s -> set_options s))
       | FStarC_Syntax_Syntax.RestartSolver -> ()
       | FStarC_Syntax_Syntax.PopOptions ->
           let uu___1 =
             let uu___2 = FStarC_Options.internal_pop () in
             Prims.op_Negation uu___2 in
           if uu___1
           then
             FStarC_Errors.raise_error FStarC_Class_HasRange.hasRange_range r
               FStarC_Errors_Codes.Fatal_FailToProcessPragma ()
               (Obj.magic FStarC_Errors_Msg.is_error_message_string)
               (Obj.magic "Cannot #pop-options, stack would become empty")
           else ()
       | FStarC_Syntax_Syntax.PrintEffectsGraph -> ())
let rec (unbound_variables :
  FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax ->
    FStarC_Syntax_Syntax.bv Prims.list)
  =
  fun tm ->
    let t = FStarC_Syntax_Subst.compress tm in
    match t.FStarC_Syntax_Syntax.n with
    | FStarC_Syntax_Syntax.Tm_delayed uu___ -> failwith "Impossible"
    | FStarC_Syntax_Syntax.Tm_name x -> []
    | FStarC_Syntax_Syntax.Tm_uvar uu___ -> []
    | FStarC_Syntax_Syntax.Tm_type u -> []
    | FStarC_Syntax_Syntax.Tm_bvar x -> [x]
    | FStarC_Syntax_Syntax.Tm_fvar uu___ -> []
    | FStarC_Syntax_Syntax.Tm_constant uu___ -> []
    | FStarC_Syntax_Syntax.Tm_lazy uu___ -> []
    | FStarC_Syntax_Syntax.Tm_unknown -> []
    | FStarC_Syntax_Syntax.Tm_uinst (t1, us) -> unbound_variables t1
    | FStarC_Syntax_Syntax.Tm_abs
        { FStarC_Syntax_Syntax.bs = bs; FStarC_Syntax_Syntax.body = t1;
          FStarC_Syntax_Syntax.rc_opt = uu___;_}
        ->
        let uu___1 = FStarC_Syntax_Subst.open_term bs t1 in
        (match uu___1 with
         | (bs1, t2) ->
             let uu___2 =
               FStarC_Compiler_List.collect
                 (fun b ->
                    unbound_variables
                      (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort)
                 bs1 in
             let uu___3 = unbound_variables t2 in
             FStarC_Compiler_List.op_At uu___2 uu___3)
    | FStarC_Syntax_Syntax.Tm_arrow
        { FStarC_Syntax_Syntax.bs1 = bs; FStarC_Syntax_Syntax.comp = c;_} ->
        let uu___ = FStarC_Syntax_Subst.open_comp bs c in
        (match uu___ with
         | (bs1, c1) ->
             let uu___1 =
               FStarC_Compiler_List.collect
                 (fun b ->
                    unbound_variables
                      (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort)
                 bs1 in
             let uu___2 = unbound_variables_comp c1 in
             FStarC_Compiler_List.op_At uu___1 uu___2)
    | FStarC_Syntax_Syntax.Tm_refine
        { FStarC_Syntax_Syntax.b = b; FStarC_Syntax_Syntax.phi = t1;_} ->
        let uu___ =
          let uu___1 =
            let uu___2 = FStarC_Syntax_Syntax.mk_binder b in [uu___2] in
          FStarC_Syntax_Subst.open_term uu___1 t1 in
        (match uu___ with
         | (bs, t2) ->
             let uu___1 =
               FStarC_Compiler_List.collect
                 (fun b1 ->
                    unbound_variables
                      (b1.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort)
                 bs in
             let uu___2 = unbound_variables t2 in
             FStarC_Compiler_List.op_At uu___1 uu___2)
    | FStarC_Syntax_Syntax.Tm_app
        { FStarC_Syntax_Syntax.hd = t1; FStarC_Syntax_Syntax.args = args;_}
        ->
        let uu___ =
          FStarC_Compiler_List.collect
            (fun uu___1 ->
               match uu___1 with | (x, uu___2) -> unbound_variables x) args in
        let uu___1 = unbound_variables t1 in
        FStarC_Compiler_List.op_At uu___ uu___1
    | FStarC_Syntax_Syntax.Tm_match
        { FStarC_Syntax_Syntax.scrutinee = t1;
          FStarC_Syntax_Syntax.ret_opt = asc_opt;
          FStarC_Syntax_Syntax.brs = pats;
          FStarC_Syntax_Syntax.rc_opt1 = uu___;_}
        ->
        let uu___1 = unbound_variables t1 in
        let uu___2 =
          let uu___3 =
            match asc_opt with
            | FStar_Pervasives_Native.None -> []
            | FStar_Pervasives_Native.Some (b, asc) ->
                let uu___4 = FStarC_Syntax_Subst.open_ascription [b] asc in
                (match uu___4 with
                 | (bs, asc1) ->
                     let uu___5 =
                       FStarC_Compiler_List.collect
                         (fun b1 ->
                            unbound_variables
                              (b1.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort)
                         bs in
                     let uu___6 = unbound_variables_ascription asc1 in
                     FStarC_Compiler_List.op_At uu___5 uu___6) in
          let uu___4 =
            FStarC_Compiler_List.collect
              (fun br ->
                 let uu___5 = FStarC_Syntax_Subst.open_branch br in
                 match uu___5 with
                 | (p, wopt, t2) ->
                     let uu___6 = unbound_variables t2 in
                     let uu___7 =
                       match wopt with
                       | FStar_Pervasives_Native.None -> []
                       | FStar_Pervasives_Native.Some t3 ->
                           unbound_variables t3 in
                     FStarC_Compiler_List.op_At uu___6 uu___7) pats in
          FStarC_Compiler_List.op_At uu___3 uu___4 in
        FStarC_Compiler_List.op_At uu___1 uu___2
    | FStarC_Syntax_Syntax.Tm_ascribed
        { FStarC_Syntax_Syntax.tm = t1; FStarC_Syntax_Syntax.asc = asc;
          FStarC_Syntax_Syntax.eff_opt = uu___;_}
        ->
        let uu___1 = unbound_variables t1 in
        let uu___2 = unbound_variables_ascription asc in
        FStarC_Compiler_List.op_At uu___1 uu___2
    | FStarC_Syntax_Syntax.Tm_let
        { FStarC_Syntax_Syntax.lbs = (false, lb::[]);
          FStarC_Syntax_Syntax.body1 = t1;_}
        ->
        let uu___ = unbound_variables lb.FStarC_Syntax_Syntax.lbtyp in
        let uu___1 =
          let uu___2 = unbound_variables lb.FStarC_Syntax_Syntax.lbdef in
          let uu___3 =
            match lb.FStarC_Syntax_Syntax.lbname with
            | FStar_Pervasives.Inr uu___4 -> unbound_variables t1
            | FStar_Pervasives.Inl bv ->
                let uu___4 =
                  let uu___5 =
                    let uu___6 = FStarC_Syntax_Syntax.mk_binder bv in
                    [uu___6] in
                  FStarC_Syntax_Subst.open_term uu___5 t1 in
                (match uu___4 with | (uu___5, t2) -> unbound_variables t2) in
          FStarC_Compiler_List.op_At uu___2 uu___3 in
        FStarC_Compiler_List.op_At uu___ uu___1
    | FStarC_Syntax_Syntax.Tm_let
        { FStarC_Syntax_Syntax.lbs = (uu___, lbs);
          FStarC_Syntax_Syntax.body1 = t1;_}
        ->
        let uu___1 = FStarC_Syntax_Subst.open_let_rec lbs t1 in
        (match uu___1 with
         | (lbs1, t2) ->
             let uu___2 = unbound_variables t2 in
             let uu___3 =
               FStarC_Compiler_List.collect
                 (fun lb ->
                    let uu___4 =
                      unbound_variables lb.FStarC_Syntax_Syntax.lbtyp in
                    let uu___5 =
                      unbound_variables lb.FStarC_Syntax_Syntax.lbdef in
                    FStarC_Compiler_List.op_At uu___4 uu___5) lbs1 in
             FStarC_Compiler_List.op_At uu___2 uu___3)
    | FStarC_Syntax_Syntax.Tm_quoted (tm1, qi) ->
        (match qi.FStarC_Syntax_Syntax.qkind with
         | FStarC_Syntax_Syntax.Quote_static -> []
         | FStarC_Syntax_Syntax.Quote_dynamic -> unbound_variables tm1)
    | FStarC_Syntax_Syntax.Tm_meta
        { FStarC_Syntax_Syntax.tm2 = t1; FStarC_Syntax_Syntax.meta = m;_} ->
        let uu___ = unbound_variables t1 in
        let uu___1 =
          match m with
          | FStarC_Syntax_Syntax.Meta_pattern (uu___2, args) ->
              FStarC_Compiler_List.collect
                (FStarC_Compiler_List.collect
                   (fun uu___3 ->
                      match uu___3 with | (a, uu___4) -> unbound_variables a))
                args
          | FStarC_Syntax_Syntax.Meta_monadic_lift (uu___2, uu___3, t') ->
              unbound_variables t'
          | FStarC_Syntax_Syntax.Meta_monadic (uu___2, t') ->
              unbound_variables t'
          | FStarC_Syntax_Syntax.Meta_labeled uu___2 -> []
          | FStarC_Syntax_Syntax.Meta_desugared uu___2 -> []
          | FStarC_Syntax_Syntax.Meta_named uu___2 -> [] in
        FStarC_Compiler_List.op_At uu___ uu___1
and (unbound_variables_ascription :
  ((FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax,
    FStarC_Syntax_Syntax.comp' FStarC_Syntax_Syntax.syntax)
    FStar_Pervasives.either * FStarC_Syntax_Syntax.term'
    FStarC_Syntax_Syntax.syntax FStar_Pervasives_Native.option * Prims.bool)
    -> FStarC_Syntax_Syntax.bv Prims.list)
  =
  fun asc ->
    let uu___ = asc in
    match uu___ with
    | (asc1, topt, uu___1) ->
        let uu___2 =
          match asc1 with
          | FStar_Pervasives.Inl t2 -> unbound_variables t2
          | FStar_Pervasives.Inr c2 -> unbound_variables_comp c2 in
        let uu___3 =
          match topt with
          | FStar_Pervasives_Native.None -> []
          | FStar_Pervasives_Native.Some tac -> unbound_variables tac in
        FStarC_Compiler_List.op_At uu___2 uu___3
and (unbound_variables_comp :
  FStarC_Syntax_Syntax.comp -> FStarC_Syntax_Syntax.bv Prims.list) =
  fun c ->
    match c.FStarC_Syntax_Syntax.n with
    | FStarC_Syntax_Syntax.Total t -> unbound_variables t
    | FStarC_Syntax_Syntax.GTotal t -> unbound_variables t
    | FStarC_Syntax_Syntax.Comp ct ->
        let uu___ = unbound_variables ct.FStarC_Syntax_Syntax.result_typ in
        let uu___1 =
          FStarC_Compiler_List.collect
            (fun uu___2 ->
               match uu___2 with | (a, uu___3) -> unbound_variables a)
            ct.FStarC_Syntax_Syntax.effect_args in
        FStarC_Compiler_List.op_At uu___ uu___1
let (extract_attr' :
  FStarC_Ident.lid ->
    FStarC_Syntax_Syntax.term Prims.list ->
      (FStarC_Syntax_Syntax.term Prims.list * FStarC_Syntax_Syntax.args)
        FStar_Pervasives_Native.option)
  =
  fun attr_lid ->
    fun attrs ->
      let rec aux acc attrs1 =
        match attrs1 with
        | [] -> FStar_Pervasives_Native.None
        | h::t ->
            let uu___ = head_and_args h in
            (match uu___ with
             | (head, args) ->
                 let uu___1 =
                   let uu___2 = FStarC_Syntax_Subst.compress head in
                   uu___2.FStarC_Syntax_Syntax.n in
                 (match uu___1 with
                  | FStarC_Syntax_Syntax.Tm_fvar fv when
                      FStarC_Syntax_Syntax.fv_eq_lid fv attr_lid ->
                      let attrs' = FStarC_Compiler_List.rev_acc acc t in
                      FStar_Pervasives_Native.Some (attrs', args)
                  | uu___2 -> aux (h :: acc) t)) in
      aux [] attrs
let (extract_attr :
  FStarC_Ident.lid ->
    FStarC_Syntax_Syntax.sigelt ->
      (FStarC_Syntax_Syntax.sigelt * FStarC_Syntax_Syntax.args)
        FStar_Pervasives_Native.option)
  =
  fun attr_lid ->
    fun se ->
      let uu___ = extract_attr' attr_lid se.FStarC_Syntax_Syntax.sigattrs in
      match uu___ with
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (attrs', t) ->
          FStar_Pervasives_Native.Some
            ({
               FStarC_Syntax_Syntax.sigel = (se.FStarC_Syntax_Syntax.sigel);
               FStarC_Syntax_Syntax.sigrng = (se.FStarC_Syntax_Syntax.sigrng);
               FStarC_Syntax_Syntax.sigquals =
                 (se.FStarC_Syntax_Syntax.sigquals);
               FStarC_Syntax_Syntax.sigmeta =
                 (se.FStarC_Syntax_Syntax.sigmeta);
               FStarC_Syntax_Syntax.sigattrs = attrs';
               FStarC_Syntax_Syntax.sigopens_and_abbrevs =
                 (se.FStarC_Syntax_Syntax.sigopens_and_abbrevs);
               FStarC_Syntax_Syntax.sigopts =
                 (se.FStarC_Syntax_Syntax.sigopts)
             }, t)
let (is_smt_lemma : FStarC_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu___ =
      let uu___1 = FStarC_Syntax_Subst.compress t in
      uu___1.FStarC_Syntax_Syntax.n in
    match uu___ with
    | FStarC_Syntax_Syntax.Tm_arrow
        { FStarC_Syntax_Syntax.bs1 = uu___1; FStarC_Syntax_Syntax.comp = c;_}
        ->
        (match c.FStarC_Syntax_Syntax.n with
         | FStarC_Syntax_Syntax.Comp ct when
             FStarC_Ident.lid_equals ct.FStarC_Syntax_Syntax.effect_name
               FStarC_Parser_Const.effect_Lemma_lid
             ->
             (match ct.FStarC_Syntax_Syntax.effect_args with
              | _req::_ens::(pats, uu___2)::uu___3 ->
                  let pats' = unmeta pats in
                  let uu___4 = head_and_args pats' in
                  (match uu___4 with
                   | (head, uu___5) ->
                       let uu___6 =
                         let uu___7 = un_uinst head in
                         uu___7.FStarC_Syntax_Syntax.n in
                       (match uu___6 with
                        | FStarC_Syntax_Syntax.Tm_fvar fv ->
                            FStarC_Syntax_Syntax.fv_eq_lid fv
                              FStarC_Parser_Const.cons_lid
                        | uu___7 -> false))
              | uu___2 -> false)
         | uu___2 -> false)
    | uu___1 -> false
let rec (list_elements :
  FStarC_Syntax_Syntax.term ->
    FStarC_Syntax_Syntax.term Prims.list FStar_Pervasives_Native.option)
  =
  fun e ->
    let uu___ = let uu___1 = unmeta e in head_and_args uu___1 in
    match uu___ with
    | (head, args) ->
        let uu___1 =
          let uu___2 =
            let uu___3 = un_uinst head in uu___3.FStarC_Syntax_Syntax.n in
          (uu___2, args) in
        (match uu___1 with
         | (FStarC_Syntax_Syntax.Tm_fvar fv, uu___2) when
             FStarC_Syntax_Syntax.fv_eq_lid fv FStarC_Parser_Const.nil_lid ->
             FStar_Pervasives_Native.Some []
         | (FStarC_Syntax_Syntax.Tm_fvar fv,
            uu___2::(hd, uu___3)::(tl, uu___4)::[]) when
             FStarC_Syntax_Syntax.fv_eq_lid fv FStarC_Parser_Const.cons_lid
             ->
             let uu___5 =
               let uu___6 =
                 let uu___7 = list_elements tl in
                 FStarC_Compiler_Util.must uu___7 in
               hd :: uu___6 in
             FStar_Pervasives_Native.Some uu___5
         | uu___2 -> FStar_Pervasives_Native.None)
let (destruct_lemma_with_smt_patterns :
  FStarC_Syntax_Syntax.term ->
    (FStarC_Syntax_Syntax.binders * FStarC_Syntax_Syntax.term *
      FStarC_Syntax_Syntax.term * FStarC_Syntax_Syntax.arg Prims.list
      Prims.list) FStar_Pervasives_Native.option)
  =
  fun t ->
    let lemma_pats p =
      let smt_pat_or t1 =
        let uu___ = let uu___1 = unmeta t1 in head_and_args uu___1 in
        match uu___ with
        | (head, args) ->
            let uu___1 =
              let uu___2 =
                let uu___3 = un_uinst head in uu___3.FStarC_Syntax_Syntax.n in
              (uu___2, args) in
            (match uu___1 with
             | (FStarC_Syntax_Syntax.Tm_fvar fv, (e, uu___2)::[]) when
                 FStarC_Syntax_Syntax.fv_eq_lid fv
                   FStarC_Parser_Const.smtpatOr_lid
                 -> FStar_Pervasives_Native.Some e
             | uu___2 -> FStar_Pervasives_Native.None) in
      let one_pat p1 =
        let uu___ = let uu___1 = unmeta p1 in head_and_args uu___1 in
        match uu___ with
        | (head, args) ->
            let uu___1 =
              let uu___2 =
                let uu___3 = un_uinst head in uu___3.FStarC_Syntax_Syntax.n in
              (uu___2, args) in
            (match uu___1 with
             | (FStarC_Syntax_Syntax.Tm_fvar fv, (uu___2, uu___3)::arg::[])
                 when
                 FStarC_Syntax_Syntax.fv_eq_lid fv
                   FStarC_Parser_Const.smtpat_lid
                 -> arg
             | uu___2 ->
                 let uu___3 =
                   let uu___4 =
                     let uu___5 =
                       FStarC_Errors_Msg.text "Not an atomic SMT pattern:" in
                     let uu___6 = ttd p1 in
                     FStarC_Pprint.prefix (Prims.of_int (2)) Prims.int_one
                       uu___5 uu___6 in
                   let uu___5 =
                     let uu___6 =
                       FStarC_Errors_Msg.text
                         "Patterns on lemmas must be a list of simple SMTPat's;or a single SMTPatOr containing a list;of lists of patterns." in
                     [uu___6] in
                   uu___4 :: uu___5 in
                 FStarC_Errors.raise_error
                   (FStarC_Syntax_Syntax.has_range_syntax ()) p1
                   FStarC_Errors_Codes.Error_IllSMTPat ()
                   (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
                   (Obj.magic uu___3)) in
      let list_literal_elements e =
        let uu___ = list_elements e in
        match uu___ with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None ->
            (FStarC_Errors.log_issue
               (FStarC_Syntax_Syntax.has_range_syntax ()) e
               FStarC_Errors_Codes.Warning_NonListLiteralSMTPattern ()
               (Obj.magic FStarC_Errors_Msg.is_error_message_string)
               (Obj.magic
                  "SMT pattern is not a list literal; ignoring the pattern");
             []) in
      let elts = list_literal_elements p in
      match elts with
      | t1::[] ->
          let uu___ = smt_pat_or t1 in
          (match uu___ with
           | FStar_Pervasives_Native.Some e ->
               let uu___1 = list_literal_elements e in
               FStarC_Compiler_List.map
                 (fun branch1 ->
                    let uu___2 = list_literal_elements branch1 in
                    FStarC_Compiler_List.map one_pat uu___2) uu___1
           | uu___1 ->
               let uu___2 = FStarC_Compiler_List.map one_pat elts in [uu___2])
      | uu___ ->
          let uu___1 = FStarC_Compiler_List.map one_pat elts in [uu___1] in
    let uu___ =
      let uu___1 = FStarC_Syntax_Subst.compress t in
      uu___1.FStarC_Syntax_Syntax.n in
    match uu___ with
    | FStarC_Syntax_Syntax.Tm_arrow
        { FStarC_Syntax_Syntax.bs1 = binders;
          FStarC_Syntax_Syntax.comp = c;_}
        ->
        let uu___1 = FStarC_Syntax_Subst.open_comp binders c in
        (match uu___1 with
         | (binders1, c1) ->
             (match c1.FStarC_Syntax_Syntax.n with
              | FStarC_Syntax_Syntax.Comp
                  { FStarC_Syntax_Syntax.comp_univs = uu___2;
                    FStarC_Syntax_Syntax.effect_name = uu___3;
                    FStarC_Syntax_Syntax.result_typ = uu___4;
                    FStarC_Syntax_Syntax.effect_args =
                      (pre, uu___5)::(post, uu___6)::(pats, uu___7)::[];
                    FStarC_Syntax_Syntax.flags = uu___8;_}
                  ->
                  let uu___9 =
                    let uu___10 = lemma_pats pats in
                    (binders1, pre, post, uu___10) in
                  FStar_Pervasives_Native.Some uu___9
              | uu___2 -> failwith "impos"))
    | uu___1 -> FStar_Pervasives_Native.None
let (triggers_of_smt_lemma :
  FStarC_Syntax_Syntax.term -> FStarC_Ident.lident Prims.list Prims.list) =
  fun t ->
    let uu___ = destruct_lemma_with_smt_patterns t in
    match uu___ with
    | FStar_Pervasives_Native.None -> []
    | FStar_Pervasives_Native.Some (uu___1, uu___2, uu___3, pats) ->
        FStarC_Compiler_List.map
          (FStarC_Compiler_List.collect
             (fun uu___4 ->
                match uu___4 with
                | (t1, uu___5) ->
                    let uu___6 = FStarC_Syntax_Free.fvars t1 in
                    FStarC_Class_Setlike.elems ()
                      (Obj.magic
                         (FStarC_Compiler_RBSet.setlike_rbset
                            FStarC_Syntax_Syntax.ord_fv)) (Obj.magic uu___6)))
          pats
let (unthunk : FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term) =
  fun t ->
    let uu___ =
      let uu___1 = FStarC_Syntax_Subst.compress t in
      uu___1.FStarC_Syntax_Syntax.n in
    match uu___ with
    | FStarC_Syntax_Syntax.Tm_abs
        { FStarC_Syntax_Syntax.bs = b::[]; FStarC_Syntax_Syntax.body = e;
          FStarC_Syntax_Syntax.rc_opt = uu___1;_}
        ->
        let uu___2 = FStarC_Syntax_Subst.open_term [b] e in
        (match uu___2 with
         | (bs, e1) ->
             let b1 = FStarC_Compiler_List.hd bs in
             let uu___3 = is_free_in b1.FStarC_Syntax_Syntax.binder_bv e1 in
             if uu___3
             then
               let uu___4 =
                 let uu___5 = FStarC_Syntax_Syntax.as_arg exp_unit in
                 [uu___5] in
               mk_app t uu___4
             else e1)
    | uu___1 ->
        let uu___2 =
          let uu___3 = FStarC_Syntax_Syntax.as_arg exp_unit in [uu___3] in
        mk_app t uu___2
let (unthunk_lemma_post :
  FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term) =
  fun t -> unthunk t
let (smt_lemma_as_forall :
  FStarC_Syntax_Syntax.term ->
    (FStarC_Syntax_Syntax.binders -> FStarC_Syntax_Syntax.universe Prims.list)
      -> FStarC_Syntax_Syntax.term)
  =
  fun t ->
    fun universe_of_binders ->
      let uu___ =
        let uu___1 = destruct_lemma_with_smt_patterns t in
        match uu___1 with
        | FStar_Pervasives_Native.None -> failwith "impos"
        | FStar_Pervasives_Native.Some res -> res in
      match uu___ with
      | (binders, pre, post, patterns) ->
          let post1 = unthunk_lemma_post post in
          let body =
            let uu___1 =
              let uu___2 =
                let uu___3 = mk_imp pre post1 in
                let uu___4 =
                  let uu___5 =
                    let uu___6 =
                      FStarC_Syntax_Syntax.binders_to_names binders in
                    (uu___6, patterns) in
                  FStarC_Syntax_Syntax.Meta_pattern uu___5 in
                {
                  FStarC_Syntax_Syntax.tm2 = uu___3;
                  FStarC_Syntax_Syntax.meta = uu___4
                } in
              FStarC_Syntax_Syntax.Tm_meta uu___2 in
            FStarC_Syntax_Syntax.mk uu___1 t.FStarC_Syntax_Syntax.pos in
          let quant =
            let uu___1 = universe_of_binders binders in
            FStarC_Compiler_List.fold_right2
              (fun b ->
                 fun u ->
                   fun out ->
                     mk_forall u b.FStarC_Syntax_Syntax.binder_bv out)
              binders uu___1 body in
          quant
let (effect_sig_ts :
  FStarC_Syntax_Syntax.effect_signature -> FStarC_Syntax_Syntax.tscheme) =
  fun sig1 ->
    match sig1 with
    | FStarC_Syntax_Syntax.Layered_eff_sig (uu___, ts) -> ts
    | FStarC_Syntax_Syntax.WP_eff_sig ts -> ts
let (apply_eff_sig :
  (FStarC_Syntax_Syntax.tscheme -> FStarC_Syntax_Syntax.tscheme) ->
    FStarC_Syntax_Syntax.effect_signature ->
      FStarC_Syntax_Syntax.effect_signature)
  =
  fun f ->
    fun uu___ ->
      match uu___ with
      | FStarC_Syntax_Syntax.Layered_eff_sig (n, ts) ->
          let uu___1 = let uu___2 = f ts in (n, uu___2) in
          FStarC_Syntax_Syntax.Layered_eff_sig uu___1
      | FStarC_Syntax_Syntax.WP_eff_sig ts ->
          let uu___1 = f ts in FStarC_Syntax_Syntax.WP_eff_sig uu___1
let (eff_decl_of_new_effect :
  FStarC_Syntax_Syntax.sigelt -> FStarC_Syntax_Syntax.eff_decl) =
  fun se ->
    match se.FStarC_Syntax_Syntax.sigel with
    | FStarC_Syntax_Syntax.Sig_new_effect ne -> ne
    | uu___ -> failwith "eff_decl_of_new_effect: not a Sig_new_effect"
let (is_layered : FStarC_Syntax_Syntax.eff_decl -> Prims.bool) =
  fun ed ->
    match ed.FStarC_Syntax_Syntax.combinators with
    | FStarC_Syntax_Syntax.Layered_eff uu___ -> true
    | uu___ -> false
let (is_dm4f : FStarC_Syntax_Syntax.eff_decl -> Prims.bool) =
  fun ed ->
    match ed.FStarC_Syntax_Syntax.combinators with
    | FStarC_Syntax_Syntax.DM4F_eff uu___ -> true
    | uu___ -> false
let (apply_wp_eff_combinators :
  (FStarC_Syntax_Syntax.tscheme -> FStarC_Syntax_Syntax.tscheme) ->
    FStarC_Syntax_Syntax.wp_eff_combinators ->
      FStarC_Syntax_Syntax.wp_eff_combinators)
  =
  fun f ->
    fun combs ->
      let uu___ = f combs.FStarC_Syntax_Syntax.ret_wp in
      let uu___1 = f combs.FStarC_Syntax_Syntax.bind_wp in
      let uu___2 = f combs.FStarC_Syntax_Syntax.stronger in
      let uu___3 = f combs.FStarC_Syntax_Syntax.if_then_else in
      let uu___4 = f combs.FStarC_Syntax_Syntax.ite_wp in
      let uu___5 = f combs.FStarC_Syntax_Syntax.close_wp in
      let uu___6 = f combs.FStarC_Syntax_Syntax.trivial in
      let uu___7 =
        FStarC_Compiler_Util.map_option f combs.FStarC_Syntax_Syntax.repr in
      let uu___8 =
        FStarC_Compiler_Util.map_option f
          combs.FStarC_Syntax_Syntax.return_repr in
      let uu___9 =
        FStarC_Compiler_Util.map_option f
          combs.FStarC_Syntax_Syntax.bind_repr in
      {
        FStarC_Syntax_Syntax.ret_wp = uu___;
        FStarC_Syntax_Syntax.bind_wp = uu___1;
        FStarC_Syntax_Syntax.stronger = uu___2;
        FStarC_Syntax_Syntax.if_then_else = uu___3;
        FStarC_Syntax_Syntax.ite_wp = uu___4;
        FStarC_Syntax_Syntax.close_wp = uu___5;
        FStarC_Syntax_Syntax.trivial = uu___6;
        FStarC_Syntax_Syntax.repr = uu___7;
        FStarC_Syntax_Syntax.return_repr = uu___8;
        FStarC_Syntax_Syntax.bind_repr = uu___9
      }
let (apply_layered_eff_combinators :
  (FStarC_Syntax_Syntax.tscheme -> FStarC_Syntax_Syntax.tscheme) ->
    FStarC_Syntax_Syntax.layered_eff_combinators ->
      FStarC_Syntax_Syntax.layered_eff_combinators)
  =
  fun f ->
    fun combs ->
      let map2 uu___ =
        match uu___ with
        | (ts1, ts2) ->
            let uu___1 = f ts1 in let uu___2 = f ts2 in (uu___1, uu___2) in
      let map3 uu___ =
        match uu___ with
        | (ts1, ts2, k) ->
            let uu___1 = f ts1 in let uu___2 = f ts2 in (uu___1, uu___2, k) in
      let uu___ = map2 combs.FStarC_Syntax_Syntax.l_repr in
      let uu___1 = map2 combs.FStarC_Syntax_Syntax.l_return in
      let uu___2 = map3 combs.FStarC_Syntax_Syntax.l_bind in
      let uu___3 = map3 combs.FStarC_Syntax_Syntax.l_subcomp in
      let uu___4 = map3 combs.FStarC_Syntax_Syntax.l_if_then_else in
      let uu___5 =
        FStarC_Compiler_Util.map_option map2
          combs.FStarC_Syntax_Syntax.l_close in
      {
        FStarC_Syntax_Syntax.l_repr = uu___;
        FStarC_Syntax_Syntax.l_return = uu___1;
        FStarC_Syntax_Syntax.l_bind = uu___2;
        FStarC_Syntax_Syntax.l_subcomp = uu___3;
        FStarC_Syntax_Syntax.l_if_then_else = uu___4;
        FStarC_Syntax_Syntax.l_close = uu___5
      }
let (apply_eff_combinators :
  (FStarC_Syntax_Syntax.tscheme -> FStarC_Syntax_Syntax.tscheme) ->
    FStarC_Syntax_Syntax.eff_combinators ->
      FStarC_Syntax_Syntax.eff_combinators)
  =
  fun f ->
    fun combs ->
      match combs with
      | FStarC_Syntax_Syntax.Primitive_eff combs1 ->
          let uu___ = apply_wp_eff_combinators f combs1 in
          FStarC_Syntax_Syntax.Primitive_eff uu___
      | FStarC_Syntax_Syntax.DM4F_eff combs1 ->
          let uu___ = apply_wp_eff_combinators f combs1 in
          FStarC_Syntax_Syntax.DM4F_eff uu___
      | FStarC_Syntax_Syntax.Layered_eff combs1 ->
          let uu___ = apply_layered_eff_combinators f combs1 in
          FStarC_Syntax_Syntax.Layered_eff uu___
let (get_layered_close_combinator :
  FStarC_Syntax_Syntax.eff_decl ->
    FStarC_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed ->
    match ed.FStarC_Syntax_Syntax.combinators with
    | FStarC_Syntax_Syntax.Layered_eff
        { FStarC_Syntax_Syntax.l_repr = uu___;
          FStarC_Syntax_Syntax.l_return = uu___1;
          FStarC_Syntax_Syntax.l_bind = uu___2;
          FStarC_Syntax_Syntax.l_subcomp = uu___3;
          FStarC_Syntax_Syntax.l_if_then_else = uu___4;
          FStarC_Syntax_Syntax.l_close = FStar_Pervasives_Native.None;_}
        -> FStar_Pervasives_Native.None
    | FStarC_Syntax_Syntax.Layered_eff
        { FStarC_Syntax_Syntax.l_repr = uu___;
          FStarC_Syntax_Syntax.l_return = uu___1;
          FStarC_Syntax_Syntax.l_bind = uu___2;
          FStarC_Syntax_Syntax.l_subcomp = uu___3;
          FStarC_Syntax_Syntax.l_if_then_else = uu___4;
          FStarC_Syntax_Syntax.l_close = FStar_Pervasives_Native.Some
            (ts, uu___5);_}
        -> FStar_Pervasives_Native.Some ts
    | uu___ -> FStar_Pervasives_Native.None
let (get_wp_close_combinator :
  FStarC_Syntax_Syntax.eff_decl ->
    FStarC_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed ->
    match ed.FStarC_Syntax_Syntax.combinators with
    | FStarC_Syntax_Syntax.Primitive_eff combs ->
        FStar_Pervasives_Native.Some (combs.FStarC_Syntax_Syntax.close_wp)
    | FStarC_Syntax_Syntax.DM4F_eff combs ->
        FStar_Pervasives_Native.Some (combs.FStarC_Syntax_Syntax.close_wp)
    | uu___ -> FStar_Pervasives_Native.None
let (get_eff_repr :
  FStarC_Syntax_Syntax.eff_decl ->
    FStarC_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed ->
    match ed.FStarC_Syntax_Syntax.combinators with
    | FStarC_Syntax_Syntax.Primitive_eff combs ->
        combs.FStarC_Syntax_Syntax.repr
    | FStarC_Syntax_Syntax.DM4F_eff combs -> combs.FStarC_Syntax_Syntax.repr
    | FStarC_Syntax_Syntax.Layered_eff combs ->
        FStar_Pervasives_Native.Some
          (FStar_Pervasives_Native.fst combs.FStarC_Syntax_Syntax.l_repr)
let (get_bind_vc_combinator :
  FStarC_Syntax_Syntax.eff_decl ->
    (FStarC_Syntax_Syntax.tscheme *
      FStarC_Syntax_Syntax.indexed_effect_combinator_kind
      FStar_Pervasives_Native.option))
  =
  fun ed ->
    match ed.FStarC_Syntax_Syntax.combinators with
    | FStarC_Syntax_Syntax.Primitive_eff combs ->
        ((combs.FStarC_Syntax_Syntax.bind_wp), FStar_Pervasives_Native.None)
    | FStarC_Syntax_Syntax.DM4F_eff combs ->
        ((combs.FStarC_Syntax_Syntax.bind_wp), FStar_Pervasives_Native.None)
    | FStarC_Syntax_Syntax.Layered_eff combs ->
        ((FStar_Pervasives_Native.__proj__Mktuple3__item___2
            combs.FStarC_Syntax_Syntax.l_bind),
          (FStar_Pervasives_Native.__proj__Mktuple3__item___3
             combs.FStarC_Syntax_Syntax.l_bind))
let (get_return_vc_combinator :
  FStarC_Syntax_Syntax.eff_decl -> FStarC_Syntax_Syntax.tscheme) =
  fun ed ->
    match ed.FStarC_Syntax_Syntax.combinators with
    | FStarC_Syntax_Syntax.Primitive_eff combs ->
        combs.FStarC_Syntax_Syntax.ret_wp
    | FStarC_Syntax_Syntax.DM4F_eff combs ->
        combs.FStarC_Syntax_Syntax.ret_wp
    | FStarC_Syntax_Syntax.Layered_eff combs ->
        FStar_Pervasives_Native.snd combs.FStarC_Syntax_Syntax.l_return
let (get_bind_repr :
  FStarC_Syntax_Syntax.eff_decl ->
    FStarC_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed ->
    match ed.FStarC_Syntax_Syntax.combinators with
    | FStarC_Syntax_Syntax.Primitive_eff combs ->
        combs.FStarC_Syntax_Syntax.bind_repr
    | FStarC_Syntax_Syntax.DM4F_eff combs ->
        combs.FStarC_Syntax_Syntax.bind_repr
    | FStarC_Syntax_Syntax.Layered_eff combs ->
        FStar_Pervasives_Native.Some
          (FStar_Pervasives_Native.__proj__Mktuple3__item___1
             combs.FStarC_Syntax_Syntax.l_bind)
let (get_return_repr :
  FStarC_Syntax_Syntax.eff_decl ->
    FStarC_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed ->
    match ed.FStarC_Syntax_Syntax.combinators with
    | FStarC_Syntax_Syntax.Primitive_eff combs ->
        combs.FStarC_Syntax_Syntax.return_repr
    | FStarC_Syntax_Syntax.DM4F_eff combs ->
        combs.FStarC_Syntax_Syntax.return_repr
    | FStarC_Syntax_Syntax.Layered_eff combs ->
        FStar_Pervasives_Native.Some
          (FStar_Pervasives_Native.fst combs.FStarC_Syntax_Syntax.l_return)
let (get_wp_trivial_combinator :
  FStarC_Syntax_Syntax.eff_decl ->
    FStarC_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed ->
    match ed.FStarC_Syntax_Syntax.combinators with
    | FStarC_Syntax_Syntax.Primitive_eff combs ->
        FStar_Pervasives_Native.Some (combs.FStarC_Syntax_Syntax.trivial)
    | FStarC_Syntax_Syntax.DM4F_eff combs ->
        FStar_Pervasives_Native.Some (combs.FStarC_Syntax_Syntax.trivial)
    | uu___ -> FStar_Pervasives_Native.None
let (get_layered_if_then_else_combinator :
  FStarC_Syntax_Syntax.eff_decl ->
    (FStarC_Syntax_Syntax.tscheme *
      FStarC_Syntax_Syntax.indexed_effect_combinator_kind
      FStar_Pervasives_Native.option) FStar_Pervasives_Native.option)
  =
  fun ed ->
    match ed.FStarC_Syntax_Syntax.combinators with
    | FStarC_Syntax_Syntax.Layered_eff combs ->
        FStar_Pervasives_Native.Some
          ((FStar_Pervasives_Native.__proj__Mktuple3__item___1
              combs.FStarC_Syntax_Syntax.l_if_then_else),
            (FStar_Pervasives_Native.__proj__Mktuple3__item___3
               combs.FStarC_Syntax_Syntax.l_if_then_else))
    | uu___ -> FStar_Pervasives_Native.None
let (get_wp_if_then_else_combinator :
  FStarC_Syntax_Syntax.eff_decl ->
    FStarC_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed ->
    match ed.FStarC_Syntax_Syntax.combinators with
    | FStarC_Syntax_Syntax.Primitive_eff combs ->
        FStar_Pervasives_Native.Some
          (combs.FStarC_Syntax_Syntax.if_then_else)
    | FStarC_Syntax_Syntax.DM4F_eff combs ->
        FStar_Pervasives_Native.Some
          (combs.FStarC_Syntax_Syntax.if_then_else)
    | uu___ -> FStar_Pervasives_Native.None
let (get_wp_ite_combinator :
  FStarC_Syntax_Syntax.eff_decl ->
    FStarC_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed ->
    match ed.FStarC_Syntax_Syntax.combinators with
    | FStarC_Syntax_Syntax.Primitive_eff combs ->
        FStar_Pervasives_Native.Some (combs.FStarC_Syntax_Syntax.ite_wp)
    | FStarC_Syntax_Syntax.DM4F_eff combs ->
        FStar_Pervasives_Native.Some (combs.FStarC_Syntax_Syntax.ite_wp)
    | uu___ -> FStar_Pervasives_Native.None
let (get_stronger_vc_combinator :
  FStarC_Syntax_Syntax.eff_decl ->
    (FStarC_Syntax_Syntax.tscheme *
      FStarC_Syntax_Syntax.indexed_effect_combinator_kind
      FStar_Pervasives_Native.option))
  =
  fun ed ->
    match ed.FStarC_Syntax_Syntax.combinators with
    | FStarC_Syntax_Syntax.Primitive_eff combs ->
        ((combs.FStarC_Syntax_Syntax.stronger), FStar_Pervasives_Native.None)
    | FStarC_Syntax_Syntax.DM4F_eff combs ->
        ((combs.FStarC_Syntax_Syntax.stronger), FStar_Pervasives_Native.None)
    | FStarC_Syntax_Syntax.Layered_eff combs ->
        ((FStar_Pervasives_Native.__proj__Mktuple3__item___2
            combs.FStarC_Syntax_Syntax.l_subcomp),
          (FStar_Pervasives_Native.__proj__Mktuple3__item___3
             combs.FStarC_Syntax_Syntax.l_subcomp))
let (get_stronger_repr :
  FStarC_Syntax_Syntax.eff_decl ->
    FStarC_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed ->
    match ed.FStarC_Syntax_Syntax.combinators with
    | FStarC_Syntax_Syntax.Primitive_eff uu___ ->
        FStar_Pervasives_Native.None
    | FStarC_Syntax_Syntax.DM4F_eff uu___ -> FStar_Pervasives_Native.None
    | FStarC_Syntax_Syntax.Layered_eff combs ->
        FStar_Pervasives_Native.Some
          (FStar_Pervasives_Native.__proj__Mktuple3__item___1
             combs.FStarC_Syntax_Syntax.l_subcomp)
let (aqual_is_erasable : FStarC_Syntax_Syntax.aqual -> Prims.bool) =
  fun aq ->
    match aq with
    | FStar_Pervasives_Native.None -> false
    | FStar_Pervasives_Native.Some aq1 ->
        FStarC_Compiler_Util.for_some
          (is_fvar FStarC_Parser_Const.erasable_attr)
          aq1.FStarC_Syntax_Syntax.aqual_attributes
let (is_erased_head :
  FStarC_Syntax_Syntax.term ->
    (FStarC_Syntax_Syntax.universe * FStarC_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun t ->
    let uu___ = head_and_args t in
    match uu___ with
    | (head, args) ->
        (match ((head.FStarC_Syntax_Syntax.n), args) with
         | (FStarC_Syntax_Syntax.Tm_uinst
            ({ FStarC_Syntax_Syntax.n = FStarC_Syntax_Syntax.Tm_fvar fv;
               FStarC_Syntax_Syntax.pos = uu___1;
               FStarC_Syntax_Syntax.vars = uu___2;
               FStarC_Syntax_Syntax.hash_code = uu___3;_},
             u::[]),
            (ty, uu___4)::[]) when
             FStarC_Syntax_Syntax.fv_eq_lid fv FStarC_Parser_Const.erased_lid
             -> FStar_Pervasives_Native.Some (u, ty)
         | uu___1 -> FStar_Pervasives_Native.None)
let (apply_reveal :
  FStarC_Syntax_Syntax.universe ->
    FStarC_Syntax_Syntax.term ->
      FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term)
  =
  fun u ->
    fun ty ->
      fun v ->
        let head =
          let uu___ =
            FStarC_Ident.set_lid_range FStarC_Parser_Const.reveal
              v.FStarC_Syntax_Syntax.pos in
          FStarC_Syntax_Syntax.fvar uu___ FStar_Pervasives_Native.None in
        let uu___ = FStarC_Syntax_Syntax.mk_Tm_uinst head [u] in
        let uu___1 =
          let uu___2 = FStarC_Syntax_Syntax.iarg ty in
          let uu___3 = let uu___4 = FStarC_Syntax_Syntax.as_arg v in [uu___4] in
          uu___2 :: uu___3 in
        FStarC_Syntax_Syntax.mk_Tm_app uu___ uu___1
          v.FStarC_Syntax_Syntax.pos
let (check_mutual_universes :
  FStarC_Syntax_Syntax.letbinding Prims.list -> unit) =
  fun lbs ->
    let uu___ = lbs in
    match uu___ with
    | lb::lbs1 ->
        let expected = lb.FStarC_Syntax_Syntax.lbunivs in
        let expected_len = FStarC_Compiler_List.length expected in
        FStarC_Compiler_List.iter
          (fun lb1 ->
             let uu___1 =
               ((FStarC_Compiler_List.length lb1.FStarC_Syntax_Syntax.lbunivs)
                  <> expected_len)
                 ||
                 (let uu___2 =
                    FStarC_Compiler_List.forall2 FStarC_Ident.ident_equals
                      lb1.FStarC_Syntax_Syntax.lbunivs expected in
                  Prims.op_Negation uu___2) in
             if uu___1
             then
               FStarC_Errors.raise_error FStarC_Class_HasRange.hasRange_range
                 lb1.FStarC_Syntax_Syntax.lbpos
                 FStarC_Errors_Codes.Fatal_IncompatibleUniverse ()
                 (Obj.magic FStarC_Errors_Msg.is_error_message_string)
                 (Obj.magic
                    "Mutually recursive definitions do not abstract over the same universes")
             else ()) lbs1
let (ctx_uvar_should_check :
  FStarC_Syntax_Syntax.ctx_uvar -> FStarC_Syntax_Syntax.should_check_uvar) =
  fun u ->
    let uu___ =
      FStarC_Syntax_Unionfind.find_decoration
        u.FStarC_Syntax_Syntax.ctx_uvar_head in
    uu___.FStarC_Syntax_Syntax.uvar_decoration_should_check
let (ctx_uvar_typ :
  FStarC_Syntax_Syntax.ctx_uvar ->
    FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax)
  =
  fun u ->
    let uu___ =
      FStarC_Syntax_Unionfind.find_decoration
        u.FStarC_Syntax_Syntax.ctx_uvar_head in
    uu___.FStarC_Syntax_Syntax.uvar_decoration_typ
let (ctx_uvar_typedness_deps :
  FStarC_Syntax_Syntax.ctx_uvar -> FStarC_Syntax_Syntax.ctx_uvar Prims.list)
  =
  fun u ->
    let uu___ =
      FStarC_Syntax_Unionfind.find_decoration
        u.FStarC_Syntax_Syntax.ctx_uvar_head in
    uu___.FStarC_Syntax_Syntax.uvar_decoration_typedness_depends_on
let (flatten_refinement :
  FStarC_Syntax_Syntax.term ->
    FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax)
  =
  fun t ->
    let rec aux t1 unascribe1 =
      let t2 = FStarC_Syntax_Subst.compress t1 in
      match t2.FStarC_Syntax_Syntax.n with
      | FStarC_Syntax_Syntax.Tm_ascribed
          { FStarC_Syntax_Syntax.tm = t3; FStarC_Syntax_Syntax.asc = uu___;
            FStarC_Syntax_Syntax.eff_opt = uu___1;_}
          when unascribe1 -> aux t3 true
      | FStarC_Syntax_Syntax.Tm_refine
          { FStarC_Syntax_Syntax.b = x; FStarC_Syntax_Syntax.phi = phi;_} ->
          let t0 = aux x.FStarC_Syntax_Syntax.sort true in
          (match t0.FStarC_Syntax_Syntax.n with
           | FStarC_Syntax_Syntax.Tm_refine
               { FStarC_Syntax_Syntax.b = y;
                 FStarC_Syntax_Syntax.phi = phi1;_}
               ->
               let uu___ =
                 let uu___1 =
                   let uu___2 = mk_conj_simp phi1 phi in
                   {
                     FStarC_Syntax_Syntax.b = y;
                     FStarC_Syntax_Syntax.phi = uu___2
                   } in
                 FStarC_Syntax_Syntax.Tm_refine uu___1 in
               FStarC_Syntax_Syntax.mk uu___ t0.FStarC_Syntax_Syntax.pos
           | uu___ -> t2)
      | uu___ -> t2 in
    aux t false
let (contains_strictly_positive_attribute :
  FStarC_Syntax_Syntax.attribute Prims.list -> Prims.bool) =
  fun attrs ->
    has_attribute attrs FStarC_Parser_Const.binder_strictly_positive_attr
let (contains_unused_attribute :
  FStarC_Syntax_Syntax.attribute Prims.list -> Prims.bool) =
  fun attrs -> has_attribute attrs FStarC_Parser_Const.binder_unused_attr
let (parse_positivity_attributes :
  FStarC_Syntax_Syntax.attribute Prims.list ->
    (FStarC_Syntax_Syntax.positivity_qualifier FStar_Pervasives_Native.option
      * FStarC_Syntax_Syntax.attribute Prims.list))
  =
  fun attrs ->
    let uu___ = contains_unused_attribute attrs in
    if uu___
    then
      ((FStar_Pervasives_Native.Some FStarC_Syntax_Syntax.BinderUnused),
        attrs)
    else
      (let uu___2 = contains_strictly_positive_attribute attrs in
       if uu___2
       then
         ((FStar_Pervasives_Native.Some
             FStarC_Syntax_Syntax.BinderStrictlyPositive), attrs)
       else (FStar_Pervasives_Native.None, attrs))
let (encode_positivity_attributes :
  FStarC_Syntax_Syntax.positivity_qualifier FStar_Pervasives_Native.option ->
    FStarC_Syntax_Syntax.attribute Prims.list ->
      FStarC_Syntax_Syntax.attribute Prims.list)
  =
  fun pqual ->
    fun attrs ->
      match pqual with
      | FStar_Pervasives_Native.None -> attrs
      | FStar_Pervasives_Native.Some
          (FStarC_Syntax_Syntax.BinderStrictlyPositive) ->
          let uu___ = contains_strictly_positive_attribute attrs in
          if uu___
          then attrs
          else
            (let uu___2 =
               let uu___3 =
                 FStarC_Syntax_Syntax.lid_as_fv
                   FStarC_Parser_Const.binder_strictly_positive_attr
                   FStar_Pervasives_Native.None in
               FStarC_Syntax_Syntax.fv_to_tm uu___3 in
             uu___2 :: attrs)
      | FStar_Pervasives_Native.Some (FStarC_Syntax_Syntax.BinderUnused) ->
          let uu___ = contains_unused_attribute attrs in
          if uu___
          then attrs
          else
            (let uu___2 =
               let uu___3 =
                 FStarC_Syntax_Syntax.lid_as_fv
                   FStarC_Parser_Const.binder_unused_attr
                   FStar_Pervasives_Native.None in
               FStarC_Syntax_Syntax.fv_to_tm uu___3 in
             uu___2 :: attrs)
let (is_binder_strictly_positive : FStarC_Syntax_Syntax.binder -> Prims.bool)
  =
  fun b ->
    b.FStarC_Syntax_Syntax.binder_positivity =
      (FStar_Pervasives_Native.Some
         FStarC_Syntax_Syntax.BinderStrictlyPositive)
let (is_binder_unused : FStarC_Syntax_Syntax.binder -> Prims.bool) =
  fun b ->
    b.FStarC_Syntax_Syntax.binder_positivity =
      (FStar_Pervasives_Native.Some FStarC_Syntax_Syntax.BinderUnused)
let (deduplicate_terms :
  FStarC_Syntax_Syntax.term Prims.list ->
    FStarC_Syntax_Syntax.term Prims.list)
  =
  fun l -> FStarC_Compiler_List.deduplicate (fun x -> fun y -> term_eq x y) l
let (eq_binding :
  FStarC_Syntax_Syntax.binding -> FStarC_Syntax_Syntax.binding -> Prims.bool)
  =
  fun b1 ->
    fun b2 ->
      match (b1, b2) with
      | (FStarC_Syntax_Syntax.Binding_var bv1,
         FStarC_Syntax_Syntax.Binding_var bv2) ->
          (FStarC_Syntax_Syntax.bv_eq bv1 bv2) &&
            (term_eq bv1.FStarC_Syntax_Syntax.sort
               bv2.FStarC_Syntax_Syntax.sort)
      | (FStarC_Syntax_Syntax.Binding_lid (lid1, uu___),
         FStarC_Syntax_Syntax.Binding_lid (lid2, uu___1)) ->
          FStarC_Ident.lid_equals lid1 lid2
      | (FStarC_Syntax_Syntax.Binding_univ u1,
         FStarC_Syntax_Syntax.Binding_univ u2) ->
          FStarC_Ident.ident_equals u1 u2
      | uu___ -> false