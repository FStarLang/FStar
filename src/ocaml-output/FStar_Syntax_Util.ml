open Prims
let (tts_f :
  (FStar_Syntax_Syntax.term -> Prims.string) FStar_Pervasives_Native.option
    FStar_ST.ref)
  = FStar_Util.mk_ref FStar_Pervasives_Native.None
let (tts : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t ->
    let uu___ = FStar_ST.op_Bang tts_f in
    match uu___ with
    | FStar_Pervasives_Native.None -> "<<hook unset>>"
    | FStar_Pervasives_Native.Some f -> f t
let (mk_discriminator : FStar_Ident.lident -> FStar_Ident.lident) =
  fun lid ->
    let uu___ =
      let uu___1 = FStar_Ident.ns_of_lid lid in
      let uu___2 =
        let uu___3 =
          let uu___4 =
            let uu___5 =
              let uu___6 =
                let uu___7 =
                  let uu___8 = FStar_Ident.ident_of_lid lid in
                  FStar_Ident.string_of_id uu___8 in
                Prims.op_Hat "is_" uu___7 in
              Prims.op_Hat FStar_Ident.reserved_prefix uu___6 in
            let uu___6 = FStar_Ident.range_of_lid lid in (uu___5, uu___6) in
          FStar_Ident.mk_ident uu___4 in
        [uu___3] in
      FStar_List.append uu___1 uu___2 in
    FStar_Ident.lid_of_ids uu___
let (is_name : FStar_Ident.lident -> Prims.bool) =
  fun lid ->
    let c =
      let uu___ =
        let uu___1 = FStar_Ident.ident_of_lid lid in
        FStar_Ident.string_of_id uu___1 in
      FStar_Util.char_at uu___ Prims.int_zero in
    FStar_Util.is_upper c
let arg_of_non_null_binder :
  'uuuuu .
    (FStar_Syntax_Syntax.bv * 'uuuuu) -> (FStar_Syntax_Syntax.term * 'uuuuu)
  =
  fun uu___ ->
    match uu___ with
    | (b, imp) ->
        let uu___1 = FStar_Syntax_Syntax.bv_to_name b in (uu___1, imp)
let (args_of_non_null_binders :
  FStar_Syntax_Syntax.binders ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list)
  =
  fun binders ->
    FStar_All.pipe_right binders
      (FStar_List.collect
         (fun b ->
            let uu___ = FStar_Syntax_Syntax.is_null_binder b in
            if uu___
            then []
            else (let uu___2 = arg_of_non_null_binder b in [uu___2])))
let (args_of_binders :
  FStar_Syntax_Syntax.binders ->
    (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.args))
  =
  fun binders ->
    let uu___ =
      FStar_All.pipe_right binders
        (FStar_List.map
           (fun b ->
              let uu___1 = FStar_Syntax_Syntax.is_null_binder b in
              if uu___1
              then
                let b1 =
                  let uu___2 =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                  (uu___2, (FStar_Pervasives_Native.snd b)) in
                let uu___2 = arg_of_non_null_binder b1 in (b1, uu___2)
              else (let uu___3 = arg_of_non_null_binder b in (b, uu___3)))) in
    FStar_All.pipe_right uu___ FStar_List.unzip
let (name_binders :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) Prims.list ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list)
  =
  fun binders ->
    FStar_All.pipe_right binders
      (FStar_List.mapi
         (fun i ->
            fun b ->
              let uu___ = FStar_Syntax_Syntax.is_null_binder b in
              if uu___
              then
                let uu___1 = b in
                match uu___1 with
                | (a, imp) ->
                    let b1 =
                      let uu___2 =
                        let uu___3 = FStar_Util.string_of_int i in
                        Prims.op_Hat "_" uu___3 in
                      FStar_Ident.id_of_text uu___2 in
                    let b2 =
                      {
                        FStar_Syntax_Syntax.ppname = b1;
                        FStar_Syntax_Syntax.index = Prims.int_zero;
                        FStar_Syntax_Syntax.sort =
                          (a.FStar_Syntax_Syntax.sort)
                      } in
                    (b2, imp)
              else b))
let (name_function_binders :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_arrow (binders, comp) ->
        let uu___ =
          let uu___1 = let uu___2 = name_binders binders in (uu___2, comp) in
          FStar_Syntax_Syntax.Tm_arrow uu___1 in
        FStar_Syntax_Syntax.mk uu___ t.FStar_Syntax_Syntax.pos
    | uu___ -> t
let (null_binders_of_tks :
  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.aqual) Prims.list ->
    FStar_Syntax_Syntax.binders)
  =
  fun tks ->
    FStar_All.pipe_right tks
      (FStar_List.map
         (fun uu___ ->
            match uu___ with
            | (t, imp) ->
                let uu___1 =
                  let uu___2 = FStar_Syntax_Syntax.null_binder t in
                  FStar_All.pipe_left FStar_Pervasives_Native.fst uu___2 in
                (uu___1, imp)))
let (binders_of_tks :
  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.aqual) Prims.list ->
    FStar_Syntax_Syntax.binders)
  =
  fun tks ->
    FStar_All.pipe_right tks
      (FStar_List.map
         (fun uu___ ->
            match uu___ with
            | (t, imp) ->
                let uu___1 =
                  FStar_Syntax_Syntax.new_bv
                    (FStar_Pervasives_Native.Some (t.FStar_Syntax_Syntax.pos))
                    t in
                (uu___1, imp)))
let (binders_of_freevars :
  FStar_Syntax_Syntax.bv FStar_Util.set ->
    FStar_Syntax_Syntax.binder Prims.list)
  =
  fun fvs ->
    let uu___ = FStar_Util.set_elements fvs in
    FStar_All.pipe_right uu___ (FStar_List.map FStar_Syntax_Syntax.mk_binder)
let mk_subst : 'uuuuu . 'uuuuu -> 'uuuuu Prims.list = fun s -> [s]
let (subst_of_list :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.subst_t)
  =
  fun formals ->
    fun actuals ->
      if (FStar_List.length formals) = (FStar_List.length actuals)
      then
        FStar_List.fold_right2
          (fun f ->
             fun a ->
               fun out ->
                 (FStar_Syntax_Syntax.NT
                    ((FStar_Pervasives_Native.fst f),
                      (FStar_Pervasives_Native.fst a)))
                 :: out) formals actuals []
      else failwith "Ill-formed substitution"
let (rename_binders :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_t)
  =
  fun replace_xs ->
    fun with_ys ->
      if (FStar_List.length replace_xs) = (FStar_List.length with_ys)
      then
        FStar_List.map2
          (fun uu___ ->
             fun uu___1 ->
               match (uu___, uu___1) with
               | ((x, uu___2), (y, uu___3)) ->
                   let uu___4 =
                     let uu___5 = FStar_Syntax_Syntax.bv_to_name y in
                     (x, uu___5) in
                   FStar_Syntax_Syntax.NT uu___4) replace_xs with_ys
      else failwith "Ill-formed substitution"
let rec (unmeta : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun e ->
    let e1 = FStar_Syntax_Subst.compress e in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (e2, uu___) -> unmeta e2
    | FStar_Syntax_Syntax.Tm_ascribed (e2, uu___, uu___1) -> unmeta e2
    | uu___ -> e1
let rec (unmeta_safe : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun e ->
    let e1 = FStar_Syntax_Subst.compress e in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (e', m) ->
        (match m with
         | FStar_Syntax_Syntax.Meta_monadic uu___ -> e1
         | FStar_Syntax_Syntax.Meta_monadic_lift uu___ -> e1
         | uu___ -> unmeta_safe e')
    | FStar_Syntax_Syntax.Tm_ascribed (e2, uu___, uu___1) -> unmeta_safe e2
    | uu___ -> e1
let (unmeta_lift : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t ->
    let uu___ =
      let uu___1 = FStar_Syntax_Subst.compress t in
      uu___1.FStar_Syntax_Syntax.n in
    match uu___ with
    | FStar_Syntax_Syntax.Tm_meta
        (t1, FStar_Syntax_Syntax.Meta_monadic_lift uu___1) -> t1
    | uu___1 -> t
let rec (univ_kernel :
  FStar_Syntax_Syntax.universe -> (FStar_Syntax_Syntax.universe * Prims.int))
  =
  fun u ->
    match u with
    | FStar_Syntax_Syntax.U_unknown -> (u, Prims.int_zero)
    | FStar_Syntax_Syntax.U_name uu___ -> (u, Prims.int_zero)
    | FStar_Syntax_Syntax.U_unif uu___ -> (u, Prims.int_zero)
    | FStar_Syntax_Syntax.U_max uu___ -> (u, Prims.int_zero)
    | FStar_Syntax_Syntax.U_zero -> (u, Prims.int_zero)
    | FStar_Syntax_Syntax.U_succ u1 ->
        let uu___ = univ_kernel u1 in
        (match uu___ with | (k, n) -> (k, (n + Prims.int_one)))
    | FStar_Syntax_Syntax.U_bvar uu___ ->
        failwith "Imposible: univ_kernel (U_bvar _)"
let (constant_univ_as_nat : FStar_Syntax_Syntax.universe -> Prims.int) =
  fun u -> let uu___ = univ_kernel u in FStar_Pervasives_Native.snd uu___
let rec (compare_univs :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe -> Prims.int)
  =
  fun u1 ->
    fun u2 ->
      let rec compare_kernel uk1 uk2 =
        match (uk1, uk2) with
        | (FStar_Syntax_Syntax.U_bvar uu___, uu___1) ->
            failwith "Impossible: compare_kernel bvar"
        | (uu___, FStar_Syntax_Syntax.U_bvar uu___1) ->
            failwith "Impossible: compare_kernel bvar"
        | (FStar_Syntax_Syntax.U_succ uu___, uu___1) ->
            failwith "Impossible: compare_kernel succ"
        | (uu___, FStar_Syntax_Syntax.U_succ uu___1) ->
            failwith "Impossible: compare_kernel succ"
        | (FStar_Syntax_Syntax.U_unknown, FStar_Syntax_Syntax.U_unknown) ->
            Prims.int_zero
        | (FStar_Syntax_Syntax.U_unknown, uu___) -> ~- Prims.int_one
        | (uu___, FStar_Syntax_Syntax.U_unknown) -> Prims.int_one
        | (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero) ->
            Prims.int_zero
        | (FStar_Syntax_Syntax.U_zero, uu___) -> ~- Prims.int_one
        | (uu___, FStar_Syntax_Syntax.U_zero) -> Prims.int_one
        | (FStar_Syntax_Syntax.U_name u11, FStar_Syntax_Syntax.U_name u21) ->
            let uu___ = FStar_Ident.string_of_id u11 in
            let uu___1 = FStar_Ident.string_of_id u21 in
            FStar_String.compare uu___ uu___1
        | (FStar_Syntax_Syntax.U_name uu___, uu___1) -> ~- Prims.int_one
        | (uu___, FStar_Syntax_Syntax.U_name uu___1) -> Prims.int_one
        | (FStar_Syntax_Syntax.U_unif u11, FStar_Syntax_Syntax.U_unif u21) ->
            let uu___ = FStar_Syntax_Unionfind.univ_uvar_id u11 in
            let uu___1 = FStar_Syntax_Unionfind.univ_uvar_id u21 in
            uu___ - uu___1
        | (FStar_Syntax_Syntax.U_unif uu___, uu___1) -> ~- Prims.int_one
        | (uu___, FStar_Syntax_Syntax.U_unif uu___1) -> Prims.int_one
        | (FStar_Syntax_Syntax.U_max us1, FStar_Syntax_Syntax.U_max us2) ->
            let n1 = FStar_List.length us1 in
            let n2 = FStar_List.length us2 in
            if n1 <> n2
            then n1 - n2
            else
              (let copt =
                 let uu___1 = FStar_List.zip us1 us2 in
                 FStar_Util.find_map uu___1
                   (fun uu___2 ->
                      match uu___2 with
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
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe -> Prims.bool)
  =
  fun u1 ->
    fun u2 -> let uu___ = compare_univs u1 u2 in uu___ = Prims.int_zero
let (ml_comp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Range.range -> FStar_Syntax_Syntax.comp)
  =
  fun t ->
    fun r ->
      let uu___ =
        let uu___1 =
          FStar_Ident.set_lid_range FStar_Parser_Const.effect_ML_lid r in
        {
          FStar_Syntax_Syntax.comp_univs = [FStar_Syntax_Syntax.U_zero];
          FStar_Syntax_Syntax.effect_name = uu___1;
          FStar_Syntax_Syntax.result_typ = t;
          FStar_Syntax_Syntax.effect_args = [];
          FStar_Syntax_Syntax.flags = [FStar_Syntax_Syntax.MLEFFECT]
        } in
      FStar_Syntax_Syntax.mk_Comp uu___
let (comp_effect_name :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> FStar_Ident.lident)
  =
  fun c ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 -> c1.FStar_Syntax_Syntax.effect_name
    | FStar_Syntax_Syntax.Total uu___ -> FStar_Parser_Const.effect_Tot_lid
    | FStar_Syntax_Syntax.GTotal uu___ -> FStar_Parser_Const.effect_GTot_lid
let (comp_flags :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun c ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total uu___ -> [FStar_Syntax_Syntax.TOTAL]
    | FStar_Syntax_Syntax.GTotal uu___ -> [FStar_Syntax_Syntax.SOMETRIVIAL]
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.flags
let (comp_to_comp_typ_nouniv :
  FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun c ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 -> c1
    | FStar_Syntax_Syntax.Total (t, u_opt) ->
        let uu___ =
          let uu___1 = FStar_Util.map_opt u_opt (fun x -> [x]) in
          FStar_Util.dflt [] uu___1 in
        {
          FStar_Syntax_Syntax.comp_univs = uu___;
          FStar_Syntax_Syntax.effect_name = (comp_effect_name c);
          FStar_Syntax_Syntax.result_typ = t;
          FStar_Syntax_Syntax.effect_args = [];
          FStar_Syntax_Syntax.flags = (comp_flags c)
        }
    | FStar_Syntax_Syntax.GTotal (t, u_opt) ->
        let uu___ =
          let uu___1 = FStar_Util.map_opt u_opt (fun x -> [x]) in
          FStar_Util.dflt [] uu___1 in
        {
          FStar_Syntax_Syntax.comp_univs = uu___;
          FStar_Syntax_Syntax.effect_name = (comp_effect_name c);
          FStar_Syntax_Syntax.result_typ = t;
          FStar_Syntax_Syntax.effect_args = [];
          FStar_Syntax_Syntax.flags = (comp_flags c)
        }
let (comp_set_flags :
  FStar_Syntax_Syntax.comp ->
    FStar_Syntax_Syntax.cflag Prims.list ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax)
  =
  fun c ->
    fun f ->
      let uu___ = c in
      let uu___1 =
        let uu___2 =
          let uu___3 = comp_to_comp_typ_nouniv c in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___3.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___3.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ =
              (uu___3.FStar_Syntax_Syntax.result_typ);
            FStar_Syntax_Syntax.effect_args =
              (uu___3.FStar_Syntax_Syntax.effect_args);
            FStar_Syntax_Syntax.flags = f
          } in
        FStar_Syntax_Syntax.Comp uu___2 in
      {
        FStar_Syntax_Syntax.n = uu___1;
        FStar_Syntax_Syntax.pos = (uu___.FStar_Syntax_Syntax.pos);
        FStar_Syntax_Syntax.vars = (uu___.FStar_Syntax_Syntax.vars)
      }
let (comp_to_comp_typ :
  FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun c ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 -> c1
    | FStar_Syntax_Syntax.Total (t, FStar_Pervasives_Native.Some u) ->
        {
          FStar_Syntax_Syntax.comp_univs = [u];
          FStar_Syntax_Syntax.effect_name = (comp_effect_name c);
          FStar_Syntax_Syntax.result_typ = t;
          FStar_Syntax_Syntax.effect_args = [];
          FStar_Syntax_Syntax.flags = (comp_flags c)
        }
    | FStar_Syntax_Syntax.GTotal (t, FStar_Pervasives_Native.Some u) ->
        {
          FStar_Syntax_Syntax.comp_univs = [u];
          FStar_Syntax_Syntax.effect_name = (comp_effect_name c);
          FStar_Syntax_Syntax.result_typ = t;
          FStar_Syntax_Syntax.effect_args = [];
          FStar_Syntax_Syntax.flags = (comp_flags c)
        }
    | uu___ -> failwith "Assertion failed: Computation type without universe"
let (effect_indices_from_repr :
  FStar_Syntax_Syntax.term ->
    Prims.bool ->
      FStar_Range.range ->
        Prims.string -> FStar_Syntax_Syntax.term Prims.list)
  =
  fun repr ->
    fun is_layered ->
      fun r ->
        fun err ->
          let err1 uu___ =
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedEffect, err) r in
          let repr1 = FStar_Syntax_Subst.compress repr in
          if is_layered
          then
            match repr1.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_app (uu___, uu___1::is) ->
                FStar_All.pipe_right is
                  (FStar_List.map FStar_Pervasives_Native.fst)
            | uu___ -> err1 ()
          else
            (match repr1.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Tm_arrow (uu___1, c) ->
                 let uu___2 = FStar_All.pipe_right c comp_to_comp_typ in
                 FStar_All.pipe_right uu___2
                   (fun ct ->
                      FStar_All.pipe_right ct.FStar_Syntax_Syntax.effect_args
                        (FStar_List.map FStar_Pervasives_Native.fst))
             | uu___1 -> err1 ())
let (destruct_comp :
  FStar_Syntax_Syntax.comp_typ ->
    (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.typ *
      FStar_Syntax_Syntax.typ))
  =
  fun c ->
    let wp =
      match c.FStar_Syntax_Syntax.effect_args with
      | (wp1, uu___)::[] -> wp1
      | uu___ ->
          let uu___1 =
            let uu___2 =
              FStar_Ident.string_of_lid c.FStar_Syntax_Syntax.effect_name in
            let uu___3 =
              let uu___4 =
                FStar_All.pipe_right c.FStar_Syntax_Syntax.effect_args
                  FStar_List.length in
              FStar_All.pipe_right uu___4 FStar_Util.string_of_int in
            FStar_Util.format2
              "Impossible: Got a computation %s with %s effect args" uu___2
              uu___3 in
          failwith uu___1 in
    let uu___ = FStar_List.hd c.FStar_Syntax_Syntax.comp_univs in
    (uu___, (c.FStar_Syntax_Syntax.result_typ), wp)
let (is_named_tot :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 ->
        FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
          FStar_Parser_Const.effect_Tot_lid
    | FStar_Syntax_Syntax.Total uu___ -> true
    | FStar_Syntax_Syntax.GTotal uu___ -> false
let (is_total_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c ->
    (FStar_Ident.lid_equals (comp_effect_name c)
       FStar_Parser_Const.effect_Tot_lid)
      ||
      (FStar_All.pipe_right (comp_flags c)
         (FStar_Util.for_some
            (fun uu___ ->
               match uu___ with
               | FStar_Syntax_Syntax.TOTAL -> true
               | FStar_Syntax_Syntax.RETURN -> true
               | uu___1 -> false)))
let (is_partial_return :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c ->
    FStar_All.pipe_right (comp_flags c)
      (FStar_Util.for_some
         (fun uu___ ->
            match uu___ with
            | FStar_Syntax_Syntax.RETURN -> true
            | FStar_Syntax_Syntax.PARTIAL_RETURN -> true
            | uu___1 -> false))
let (is_tot_or_gtot_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c ->
    (is_total_comp c) ||
      (FStar_Ident.lid_equals FStar_Parser_Const.effect_GTot_lid
         (comp_effect_name c))
let (is_pure_effect : FStar_Ident.lident -> Prims.bool) =
  fun l ->
    ((FStar_Ident.lid_equals l FStar_Parser_Const.effect_Tot_lid) ||
       (FStar_Ident.lid_equals l FStar_Parser_Const.effect_PURE_lid))
      || (FStar_Ident.lid_equals l FStar_Parser_Const.effect_Pure_lid)
let (is_pure_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total uu___ -> true
    | FStar_Syntax_Syntax.GTotal uu___ -> false
    | FStar_Syntax_Syntax.Comp ct ->
        ((is_total_comp c) ||
           (is_pure_effect ct.FStar_Syntax_Syntax.effect_name))
          ||
          (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
             (FStar_Util.for_some
                (fun uu___ ->
                   match uu___ with
                   | FStar_Syntax_Syntax.LEMMA -> true
                   | uu___1 -> false)))
let (is_ghost_effect : FStar_Ident.lident -> Prims.bool) =
  fun l ->
    ((FStar_Ident.lid_equals FStar_Parser_Const.effect_GTot_lid l) ||
       (FStar_Ident.lid_equals FStar_Parser_Const.effect_GHOST_lid l))
      || (FStar_Ident.lid_equals FStar_Parser_Const.effect_Ghost_lid l)
let (is_div_effect : FStar_Ident.lident -> Prims.bool) =
  fun l ->
    ((FStar_Ident.lid_equals l FStar_Parser_Const.effect_DIV_lid) ||
       (FStar_Ident.lid_equals l FStar_Parser_Const.effect_Div_lid))
      || (FStar_Ident.lid_equals l FStar_Parser_Const.effect_Dv_lid)
let (is_pure_or_ghost_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c -> (is_pure_comp c) || (is_ghost_effect (comp_effect_name c))
let (is_pure_or_ghost_effect : FStar_Ident.lident -> Prims.bool) =
  fun l -> (is_pure_effect l) || (is_ghost_effect l)
let (is_pure_or_ghost_function : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu___ =
      let uu___1 = FStar_Syntax_Subst.compress t in
      uu___1.FStar_Syntax_Syntax.n in
    match uu___ with
    | FStar_Syntax_Syntax.Tm_arrow (uu___1, c) -> is_pure_or_ghost_comp c
    | uu___1 -> true
let (is_lemma_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp ct ->
        FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
          FStar_Parser_Const.effect_Lemma_lid
    | uu___ -> false
let (is_lemma : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu___ =
      let uu___1 = FStar_Syntax_Subst.compress t in
      uu___1.FStar_Syntax_Syntax.n in
    match uu___ with
    | FStar_Syntax_Syntax.Tm_arrow (uu___1, c) -> is_lemma_comp c
    | uu___1 -> false
let rec (head_of : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t ->
    let uu___ =
      let uu___1 = FStar_Syntax_Subst.compress t in
      uu___1.FStar_Syntax_Syntax.n in
    match uu___ with
    | FStar_Syntax_Syntax.Tm_app (t1, uu___1) -> head_of t1
    | FStar_Syntax_Syntax.Tm_match (t1, uu___1) -> head_of t1
    | FStar_Syntax_Syntax.Tm_abs (uu___1, t1, uu___2) -> head_of t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1, uu___1, uu___2) -> head_of t1
    | FStar_Syntax_Syntax.Tm_meta (t1, uu___1) -> head_of t1
    | uu___1 -> t
let (head_and_args :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
      FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
      Prims.list))
  =
  fun t ->
    let t1 = FStar_Syntax_Subst.compress t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_app (head, args) -> (head, args)
    | uu___ -> (t1, [])
let rec (head_and_args_full :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list))
  =
  fun t ->
    let t1 = FStar_Syntax_Subst.compress t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_app (head, args) ->
        let uu___ = head_and_args_full head in
        (match uu___ with
         | (head1, args') -> (head1, (FStar_List.append args' args)))
    | uu___ -> (t1, [])
let (un_uinst : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t ->
    let t1 = FStar_Syntax_Subst.compress t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uinst (t2, uu___) ->
        FStar_Syntax_Subst.compress t2
    | uu___ -> t1
let (is_ml_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 ->
        (FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
           FStar_Parser_Const.effect_ML_lid)
          ||
          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
             (FStar_Util.for_some
                (fun uu___ ->
                   match uu___ with
                   | FStar_Syntax_Syntax.MLEFFECT -> true
                   | uu___1 -> false)))
    | uu___ -> false
let (comp_result :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun c ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t, uu___) -> t
    | FStar_Syntax_Syntax.GTotal (t, uu___) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
let (set_result_typ :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.comp)
  =
  fun c ->
    fun t ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu___ -> FStar_Syntax_Syntax.mk_Total t
      | FStar_Syntax_Syntax.GTotal uu___ -> FStar_Syntax_Syntax.mk_GTotal t
      | FStar_Syntax_Syntax.Comp ct ->
          FStar_Syntax_Syntax.mk_Comp
            (let uu___ = ct in
             {
               FStar_Syntax_Syntax.comp_univs =
                 (uu___.FStar_Syntax_Syntax.comp_univs);
               FStar_Syntax_Syntax.effect_name =
                 (uu___.FStar_Syntax_Syntax.effect_name);
               FStar_Syntax_Syntax.result_typ = t;
               FStar_Syntax_Syntax.effect_args =
                 (uu___.FStar_Syntax_Syntax.effect_args);
               FStar_Syntax_Syntax.flags = (uu___.FStar_Syntax_Syntax.flags)
             })
let (is_trivial_wp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c ->
    FStar_All.pipe_right (comp_flags c)
      (FStar_Util.for_some
         (fun uu___ ->
            match uu___ with
            | FStar_Syntax_Syntax.TOTAL -> true
            | FStar_Syntax_Syntax.RETURN -> true
            | uu___1 -> false))
let (comp_effect_args : FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.args)
  =
  fun c ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total uu___ -> []
    | FStar_Syntax_Syntax.GTotal uu___ -> []
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.effect_args
let (primops : FStar_Ident.lident Prims.list) =
  [FStar_Parser_Const.op_Eq;
  FStar_Parser_Const.op_notEq;
  FStar_Parser_Const.op_LT;
  FStar_Parser_Const.op_LTE;
  FStar_Parser_Const.op_GT;
  FStar_Parser_Const.op_GTE;
  FStar_Parser_Const.op_Subtraction;
  FStar_Parser_Const.op_Minus;
  FStar_Parser_Const.op_Addition;
  FStar_Parser_Const.op_Multiply;
  FStar_Parser_Const.op_Division;
  FStar_Parser_Const.op_Modulus;
  FStar_Parser_Const.op_And;
  FStar_Parser_Const.op_Or;
  FStar_Parser_Const.op_Negation]
let (is_primop_lid : FStar_Ident.lident -> Prims.bool) =
  fun l ->
    FStar_All.pipe_right primops
      (FStar_Util.for_some (FStar_Ident.lid_equals l))
let (is_primop :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun f ->
    match f.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        is_primop_lid (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu___ -> false
let rec (unascribe : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun e ->
    let e1 = FStar_Syntax_Subst.compress e in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_ascribed (e2, uu___, uu___1) -> unascribe e2
    | uu___ -> e1
let rec (ascribe :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    ((FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax) FStar_Util.either
      * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option) ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t ->
    fun k ->
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_ascribed (t', uu___, uu___1) -> ascribe t' k
      | uu___ ->
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (t, k, FStar_Pervasives_Native.None))
            t.FStar_Syntax_Syntax.pos
let (unfold_lazy : FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term)
  =
  fun i ->
    let uu___ =
      let uu___1 = FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser in
      FStar_Util.must uu___1 in
    uu___ i.FStar_Syntax_Syntax.lkind i
let rec (unlazy : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t ->
    let uu___ =
      let uu___1 = FStar_Syntax_Subst.compress t in
      uu___1.FStar_Syntax_Syntax.n in
    match uu___ with
    | FStar_Syntax_Syntax.Tm_lazy i ->
        let uu___1 = unfold_lazy i in FStar_All.pipe_left unlazy uu___1
    | uu___1 -> t
let (unlazy_emb : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t ->
    let uu___ =
      let uu___1 = FStar_Syntax_Subst.compress t in
      uu___1.FStar_Syntax_Syntax.n in
    match uu___ with
    | FStar_Syntax_Syntax.Tm_lazy i ->
        (match i.FStar_Syntax_Syntax.lkind with
         | FStar_Syntax_Syntax.Lazy_embedding uu___1 ->
             let uu___2 = unfold_lazy i in FStar_All.pipe_left unlazy uu___2
         | uu___1 -> t)
    | uu___1 -> t
let (eq_lazy_kind :
  FStar_Syntax_Syntax.lazy_kind ->
    FStar_Syntax_Syntax.lazy_kind -> Prims.bool)
  =
  fun k ->
    fun k' ->
      match (k, k') with
      | (FStar_Syntax_Syntax.BadLazy, FStar_Syntax_Syntax.BadLazy) -> true
      | (FStar_Syntax_Syntax.Lazy_bv, FStar_Syntax_Syntax.Lazy_bv) -> true
      | (FStar_Syntax_Syntax.Lazy_binder, FStar_Syntax_Syntax.Lazy_binder) ->
          true
      | (FStar_Syntax_Syntax.Lazy_optionstate,
         FStar_Syntax_Syntax.Lazy_optionstate) -> true
      | (FStar_Syntax_Syntax.Lazy_fvar, FStar_Syntax_Syntax.Lazy_fvar) ->
          true
      | (FStar_Syntax_Syntax.Lazy_comp, FStar_Syntax_Syntax.Lazy_comp) ->
          true
      | (FStar_Syntax_Syntax.Lazy_env, FStar_Syntax_Syntax.Lazy_env) -> true
      | (FStar_Syntax_Syntax.Lazy_proofstate,
         FStar_Syntax_Syntax.Lazy_proofstate) -> true
      | (FStar_Syntax_Syntax.Lazy_goal, FStar_Syntax_Syntax.Lazy_goal) ->
          true
      | (FStar_Syntax_Syntax.Lazy_sigelt, FStar_Syntax_Syntax.Lazy_sigelt) ->
          true
      | (FStar_Syntax_Syntax.Lazy_uvar, FStar_Syntax_Syntax.Lazy_uvar) ->
          true
      | uu___ -> false
let unlazy_as_t :
  'uuuuu .
    FStar_Syntax_Syntax.lazy_kind -> FStar_Syntax_Syntax.term -> 'uuuuu
  =
  fun k ->
    fun t ->
      let uu___ =
        let uu___1 = FStar_Syntax_Subst.compress t in
        uu___1.FStar_Syntax_Syntax.n in
      match uu___ with
      | FStar_Syntax_Syntax.Tm_lazy
          { FStar_Syntax_Syntax.blob = v; FStar_Syntax_Syntax.lkind = k';
            FStar_Syntax_Syntax.ltyp = uu___1;
            FStar_Syntax_Syntax.rng = uu___2;_}
          when eq_lazy_kind k k' -> FStar_Dyn.undyn v
      | uu___1 -> failwith "Not a Tm_lazy of the expected kind"
let mk_lazy :
  'a .
    'a ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.lazy_kind ->
          FStar_Range.range FStar_Pervasives_Native.option ->
            FStar_Syntax_Syntax.term
  =
  fun t ->
    fun typ ->
      fun k ->
        fun r ->
          let rng =
            match r with
            | FStar_Pervasives_Native.Some r1 -> r1
            | FStar_Pervasives_Native.None -> FStar_Range.dummyRange in
          let i =
            let uu___ = FStar_Dyn.mkdyn t in
            {
              FStar_Syntax_Syntax.blob = uu___;
              FStar_Syntax_Syntax.lkind = k;
              FStar_Syntax_Syntax.ltyp = typ;
              FStar_Syntax_Syntax.rng = rng
            } in
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_lazy i) rng
let (canon_app :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term)
  =
  fun t ->
    let uu___ = let uu___1 = unascribe t in head_and_args_full uu___1 in
    match uu___ with
    | (hd, args) ->
        FStar_Syntax_Syntax.mk_Tm_app hd args t.FStar_Syntax_Syntax.pos
type eq_result =
  | Equal 
  | NotEqual 
  | Unknown 
let (uu___is_Equal : eq_result -> Prims.bool) =
  fun projectee -> match projectee with | Equal -> true | uu___ -> false
let (uu___is_NotEqual : eq_result -> Prims.bool) =
  fun projectee -> match projectee with | NotEqual -> true | uu___ -> false
let (uu___is_Unknown : eq_result -> Prims.bool) =
  fun projectee -> match projectee with | Unknown -> true | uu___ -> false
let (injectives : Prims.string Prims.list) =
  ["FStar.Int8.int_to_t";
  "FStar.Int16.int_to_t";
  "FStar.Int32.int_to_t";
  "FStar.Int64.int_to_t";
  "FStar.UInt8.uint_to_t";
  "FStar.UInt16.uint_to_t";
  "FStar.UInt32.uint_to_t";
  "FStar.UInt64.uint_to_t";
  "FStar.Int8.__int_to_t";
  "FStar.Int16.__int_to_t";
  "FStar.Int32.__int_to_t";
  "FStar.Int64.__int_to_t";
  "FStar.UInt8.__uint_to_t";
  "FStar.UInt16.__uint_to_t";
  "FStar.UInt32.__uint_to_t";
  "FStar.UInt64.__uint_to_t"]
let (eq_inj : eq_result -> eq_result -> eq_result) =
  fun f ->
    fun g ->
      match (f, g) with
      | (Equal, Equal) -> Equal
      | (NotEqual, uu___) -> NotEqual
      | (uu___, NotEqual) -> NotEqual
      | (Unknown, uu___) -> Unknown
      | (uu___, Unknown) -> Unknown
let rec (eq_tm :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> eq_result) =
  fun t1 ->
    fun t2 ->
      let t11 = canon_app t1 in
      let t21 = canon_app t2 in
      let equal_if uu___ = if uu___ then Equal else Unknown in
      let equal_iff uu___ = if uu___ then Equal else NotEqual in
      let eq_and f g = match f with | Equal -> g () | uu___ -> Unknown in
      let equal_data f1 args1 f2 args2 =
        let uu___ = FStar_Syntax_Syntax.fv_eq f1 f2 in
        if uu___
        then
          let uu___2 = FStar_List.zip args1 args2 in
          FStar_All.pipe_left
            (FStar_List.fold_left
               (fun acc ->
                  fun uu___3 ->
                    match uu___3 with
                    | ((a1, q1), (a2, q2)) ->
                        let uu___4 = eq_tm a1 a2 in eq_inj acc uu___4) Equal)
            uu___2
        else NotEqual in
      let qual_is_inj uu___ =
        match uu___ with
        | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor) ->
            true
        | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor
            uu___1) -> true
        | uu___1 -> false in
      let heads_and_args_in_case_both_data =
        let uu___ =
          let uu___1 = FStar_All.pipe_right t11 unmeta in
          FStar_All.pipe_right uu___1 head_and_args in
        match uu___ with
        | (head1, args1) ->
            let uu___1 =
              let uu___2 = FStar_All.pipe_right t21 unmeta in
              FStar_All.pipe_right uu___2 head_and_args in
            (match uu___1 with
             | (head2, args2) ->
                 let uu___2 =
                   let uu___3 =
                     let uu___4 = un_uinst head1 in
                     uu___4.FStar_Syntax_Syntax.n in
                   let uu___4 =
                     let uu___5 = un_uinst head2 in
                     uu___5.FStar_Syntax_Syntax.n in
                   (uu___3, uu___4) in
                 (match uu___2 with
                  | (FStar_Syntax_Syntax.Tm_fvar f,
                     FStar_Syntax_Syntax.Tm_fvar g) when
                      (qual_is_inj f.FStar_Syntax_Syntax.fv_qual) &&
                        (qual_is_inj g.FStar_Syntax_Syntax.fv_qual)
                      -> FStar_Pervasives_Native.Some (f, args1, g, args2)
                  | uu___3 -> FStar_Pervasives_Native.None)) in
      let t12 = unmeta t11 in
      let t22 = unmeta t21 in
      match ((t12.FStar_Syntax_Syntax.n), (t22.FStar_Syntax_Syntax.n)) with
      | (FStar_Syntax_Syntax.Tm_bvar bv1, FStar_Syntax_Syntax.Tm_bvar bv2) ->
          equal_if
            (bv1.FStar_Syntax_Syntax.index = bv2.FStar_Syntax_Syntax.index)
      | (FStar_Syntax_Syntax.Tm_lazy uu___, uu___1) ->
          let uu___2 = unlazy t12 in eq_tm uu___2 t22
      | (uu___, FStar_Syntax_Syntax.Tm_lazy uu___1) ->
          let uu___2 = unlazy t22 in eq_tm t12 uu___2
      | (FStar_Syntax_Syntax.Tm_name a, FStar_Syntax_Syntax.Tm_name b) ->
          let uu___ = FStar_Syntax_Syntax.bv_eq a b in equal_if uu___
      | uu___ when
          FStar_All.pipe_right heads_and_args_in_case_both_data
            FStar_Util.is_some
          ->
          let uu___1 =
            FStar_All.pipe_right heads_and_args_in_case_both_data
              FStar_Util.must in
          FStar_All.pipe_right uu___1
            (fun uu___2 ->
               match uu___2 with
               | (f, args1, g, args2) -> equal_data f args1 g args2)
      | (FStar_Syntax_Syntax.Tm_fvar f, FStar_Syntax_Syntax.Tm_fvar g) ->
          let uu___ = FStar_Syntax_Syntax.fv_eq f g in equal_if uu___
      | (FStar_Syntax_Syntax.Tm_uinst (f, us), FStar_Syntax_Syntax.Tm_uinst
         (g, vs)) ->
          let uu___ = eq_tm f g in
          eq_and uu___
            (fun uu___1 ->
               let uu___2 = eq_univs_list us vs in equal_if uu___2)
      | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range uu___),
         uu___1) -> Unknown
      | (uu___, FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu___1)) -> Unknown
      | (FStar_Syntax_Syntax.Tm_constant c, FStar_Syntax_Syntax.Tm_constant
         d) -> let uu___ = FStar_Const.eq_const c d in equal_iff uu___
      | (FStar_Syntax_Syntax.Tm_uvar (u1, ([], uu___)),
         FStar_Syntax_Syntax.Tm_uvar (u2, ([], uu___1))) ->
          let uu___2 =
            FStar_Syntax_Unionfind.equiv u1.FStar_Syntax_Syntax.ctx_uvar_head
              u2.FStar_Syntax_Syntax.ctx_uvar_head in
          equal_if uu___2
      | (FStar_Syntax_Syntax.Tm_app (h1, args1), FStar_Syntax_Syntax.Tm_app
         (h2, args2)) ->
          let uu___ =
            let uu___1 =
              let uu___2 = un_uinst h1 in uu___2.FStar_Syntax_Syntax.n in
            let uu___2 =
              let uu___3 = un_uinst h2 in uu___3.FStar_Syntax_Syntax.n in
            (uu___1, uu___2) in
          (match uu___ with
           | (FStar_Syntax_Syntax.Tm_fvar f1, FStar_Syntax_Syntax.Tm_fvar f2)
               when
               (FStar_Syntax_Syntax.fv_eq f1 f2) &&
                 (let uu___1 =
                    let uu___2 = FStar_Syntax_Syntax.lid_of_fv f1 in
                    FStar_Ident.string_of_lid uu___2 in
                  FStar_List.mem uu___1 injectives)
               -> equal_data f1 args1 f2 args2
           | uu___1 ->
               let uu___2 = eq_tm h1 h2 in
               eq_and uu___2 (fun uu___3 -> eq_args args1 args2))
      | (FStar_Syntax_Syntax.Tm_match (t13, bs1),
         FStar_Syntax_Syntax.Tm_match (t23, bs2)) ->
          if (FStar_List.length bs1) = (FStar_List.length bs2)
          then
            let uu___ = FStar_List.zip bs1 bs2 in
            let uu___1 = eq_tm t13 t23 in
            FStar_List.fold_right
              (fun uu___2 ->
                 fun a ->
                   match uu___2 with
                   | (b1, b2) ->
                       eq_and a (fun uu___3 -> branch_matches b1 b2)) uu___
              uu___1
          else Unknown
      | (FStar_Syntax_Syntax.Tm_type u, FStar_Syntax_Syntax.Tm_type v) ->
          let uu___ = eq_univs u v in equal_if uu___
      | (FStar_Syntax_Syntax.Tm_quoted (t13, q1),
         FStar_Syntax_Syntax.Tm_quoted (t23, q2)) ->
          let uu___ = eq_quoteinfo q1 q2 in
          eq_and uu___ (fun uu___1 -> eq_tm t13 t23)
      | (FStar_Syntax_Syntax.Tm_refine (t13, phi1),
         FStar_Syntax_Syntax.Tm_refine (t23, phi2)) ->
          let uu___ =
            eq_tm t13.FStar_Syntax_Syntax.sort t23.FStar_Syntax_Syntax.sort in
          eq_and uu___ (fun uu___1 -> eq_tm phi1 phi2)
      | uu___ -> Unknown
and (eq_quoteinfo :
  FStar_Syntax_Syntax.quoteinfo -> FStar_Syntax_Syntax.quoteinfo -> eq_result)
  =
  fun q1 ->
    fun q2 ->
      if q1.FStar_Syntax_Syntax.qkind <> q2.FStar_Syntax_Syntax.qkind
      then NotEqual
      else
        eq_antiquotes q1.FStar_Syntax_Syntax.antiquotes
          q2.FStar_Syntax_Syntax.antiquotes
and (eq_antiquotes :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
    FStar_Syntax_Syntax.syntax) Prims.list ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax) Prims.list -> eq_result)
  =
  fun a1 ->
    fun a2 ->
      match (a1, a2) with
      | ([], []) -> Equal
      | ([], uu___) -> NotEqual
      | (uu___, []) -> NotEqual
      | ((x1, t1)::a11, (x2, t2)::a21) ->
          let uu___ =
            let uu___1 = FStar_Syntax_Syntax.bv_eq x1 x2 in
            Prims.op_Negation uu___1 in
          if uu___
          then NotEqual
          else
            (let uu___2 = eq_tm t1 t2 in
             match uu___2 with
             | NotEqual -> NotEqual
             | Unknown ->
                 let uu___3 = eq_antiquotes a11 a21 in
                 (match uu___3 with
                  | NotEqual -> NotEqual
                  | uu___4 -> Unknown)
             | Equal -> eq_antiquotes a11 a21)
and (branch_matches :
  (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t *
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
    FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term'
    FStar_Syntax_Syntax.syntax) ->
    (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t *
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax) -> eq_result)
  =
  fun b1 ->
    fun b2 ->
      let related_by f o1 o2 =
        match (o1, o2) with
        | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) ->
            true
        | (FStar_Pervasives_Native.Some x, FStar_Pervasives_Native.Some y) ->
            f x y
        | (uu___, uu___1) -> false in
      let uu___ = b1 in
      match uu___ with
      | (p1, w1, t1) ->
          let uu___1 = b2 in
          (match uu___1 with
           | (p2, w2, t2) ->
               let uu___2 = FStar_Syntax_Syntax.eq_pat p1 p2 in
               if uu___2
               then
                 let uu___3 =
                   (let uu___4 = eq_tm t1 t2 in uu___4 = Equal) &&
                     (related_by
                        (fun t11 ->
                           fun t21 ->
                             let uu___4 = eq_tm t11 t21 in uu___4 = Equal) w1
                        w2) in
                 (if uu___3 then Equal else Unknown)
               else Unknown)
and (eq_args :
  FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.args -> eq_result) =
  fun a1 ->
    fun a2 ->
      match (a1, a2) with
      | ([], []) -> Equal
      | ((a, uu___)::a11, (b, uu___1)::b1) ->
          let uu___2 = eq_tm a b in
          (match uu___2 with | Equal -> eq_args a11 b1 | uu___3 -> Unknown)
      | uu___ -> Unknown
and (eq_univs_list :
  FStar_Syntax_Syntax.universes ->
    FStar_Syntax_Syntax.universes -> Prims.bool)
  =
  fun us ->
    fun vs ->
      ((FStar_List.length us) = (FStar_List.length vs)) &&
        (FStar_List.forall2 eq_univs us vs)
let (eq_aqual :
  FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
      eq_result)
  =
  fun a1 ->
    fun a2 ->
      match (a1, a2) with
      | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) -> Equal
      | (FStar_Pervasives_Native.None, uu___) -> NotEqual
      | (uu___, FStar_Pervasives_Native.None) -> NotEqual
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit b1),
         FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit b2)) when
          b1 = b2 -> Equal
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
         (FStar_Syntax_Syntax.Arg_qualifier_meta_tac t1)),
         FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
         (FStar_Syntax_Syntax.Arg_qualifier_meta_tac t2))) -> eq_tm t1 t2
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
         (FStar_Syntax_Syntax.Arg_qualifier_meta_attr t1)),
         FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
         (FStar_Syntax_Syntax.Arg_qualifier_meta_attr t2))) -> eq_tm t1 t2
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality),
         FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality)) ->
          Equal
      | uu___ -> NotEqual
let rec (unrefine : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t ->
    let t1 = FStar_Syntax_Subst.compress t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x, uu___) ->
        unrefine x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2, uu___, uu___1) -> unrefine t2
    | uu___ -> t1
let rec (is_uvar : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu___ =
      let uu___1 = FStar_Syntax_Subst.compress t in
      uu___1.FStar_Syntax_Syntax.n in
    match uu___ with
    | FStar_Syntax_Syntax.Tm_uvar uu___1 -> true
    | FStar_Syntax_Syntax.Tm_uinst (t1, uu___1) -> is_uvar t1
    | FStar_Syntax_Syntax.Tm_app uu___1 ->
        let uu___2 =
          let uu___3 = FStar_All.pipe_right t head_and_args in
          FStar_All.pipe_right uu___3 FStar_Pervasives_Native.fst in
        FStar_All.pipe_right uu___2 is_uvar
    | FStar_Syntax_Syntax.Tm_ascribed (t1, uu___1, uu___2) -> is_uvar t1
    | uu___1 -> false
let rec (is_unit : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu___ = let uu___1 = unrefine t in uu___1.FStar_Syntax_Syntax.n in
    match uu___ with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
          ||
          (FStar_Syntax_Syntax.fv_eq_lid fv
             FStar_Parser_Const.auto_squash_lid)
    | FStar_Syntax_Syntax.Tm_app (head, uu___1) -> is_unit head
    | FStar_Syntax_Syntax.Tm_uinst (t1, uu___1) -> is_unit t1
    | uu___1 -> false
let (is_eqtype_no_unrefine : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu___ =
      let uu___1 = FStar_Syntax_Subst.compress t in
      uu___1.FStar_Syntax_Syntax.n in
    match uu___ with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.eqtype_lid
    | uu___1 -> false
let (is_fun : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e ->
    let uu___ =
      let uu___1 = FStar_Syntax_Subst.compress e in
      uu___1.FStar_Syntax_Syntax.n in
    match uu___ with
    | FStar_Syntax_Syntax.Tm_abs uu___1 -> true
    | uu___1 -> false
let (is_function_typ : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu___ =
      let uu___1 = FStar_Syntax_Subst.compress t in
      uu___1.FStar_Syntax_Syntax.n in
    match uu___ with
    | FStar_Syntax_Syntax.Tm_arrow uu___1 -> true
    | uu___1 -> false
let rec (pre_typ : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t ->
    let t1 = FStar_Syntax_Subst.compress t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x, uu___) ->
        pre_typ x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2, uu___, uu___1) -> pre_typ t2
    | uu___ -> t1
let (destruct :
  FStar_Syntax_Syntax.term ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
        FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
        Prims.list FStar_Pervasives_Native.option)
  =
  fun typ ->
    fun lid ->
      let typ1 = FStar_Syntax_Subst.compress typ in
      let uu___ = let uu___1 = un_uinst typ1 in uu___1.FStar_Syntax_Syntax.n in
      match uu___ with
      | FStar_Syntax_Syntax.Tm_app (head, args) ->
          let head1 = un_uinst head in
          (match head1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_fvar tc when
               FStar_Syntax_Syntax.fv_eq_lid tc lid ->
               FStar_Pervasives_Native.Some args
           | uu___1 -> FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.Tm_fvar tc when
          FStar_Syntax_Syntax.fv_eq_lid tc lid ->
          FStar_Pervasives_Native.Some []
      | uu___1 -> FStar_Pervasives_Native.None
let (lids_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Ident.lident Prims.list) =
  fun se ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let (uu___, lids) -> lids
    | FStar_Syntax_Syntax.Sig_splice (lids, uu___) -> lids
    | FStar_Syntax_Syntax.Sig_bundle (uu___, lids) -> lids
    | FStar_Syntax_Syntax.Sig_inductive_typ
        (lid, uu___, uu___1, uu___2, uu___3, uu___4) -> [lid]
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid, uu___, uu___1, uu___2, uu___3) -> [lid]
    | FStar_Syntax_Syntax.Sig_datacon
        (lid, uu___, uu___1, uu___2, uu___3, uu___4) -> [lid]
    | FStar_Syntax_Syntax.Sig_declare_typ (lid, uu___, uu___1) -> [lid]
    | FStar_Syntax_Syntax.Sig_assume (lid, uu___, uu___1) -> [lid]
    | FStar_Syntax_Syntax.Sig_new_effect n -> [n.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_sub_effect uu___ -> []
    | FStar_Syntax_Syntax.Sig_pragma uu___ -> []
    | FStar_Syntax_Syntax.Sig_fail uu___ -> []
    | FStar_Syntax_Syntax.Sig_polymonadic_bind uu___ -> []
    | FStar_Syntax_Syntax.Sig_polymonadic_subcomp uu___ -> []
let (lid_of_sigelt :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun se ->
    match lids_of_sigelt se with
    | l::[] -> FStar_Pervasives_Native.Some l
    | uu___ -> FStar_Pervasives_Native.None
let (quals_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun x -> x.FStar_Syntax_Syntax.sigquals
let (range_of_sigelt : FStar_Syntax_Syntax.sigelt -> FStar_Range.range) =
  fun x -> x.FStar_Syntax_Syntax.sigrng
let (range_of_lbname :
  (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.fv) FStar_Util.either ->
    FStar_Range.range)
  =
  fun uu___ ->
    match uu___ with
    | FStar_Util.Inl x -> FStar_Syntax_Syntax.range_of_bv x
    | FStar_Util.Inr fv ->
        FStar_Ident.range_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
let range_of_arg :
  'uuuuu 'uuuuu1 .
    ('uuuuu FStar_Syntax_Syntax.syntax * 'uuuuu1) -> FStar_Range.range
  =
  fun uu___ -> match uu___ with | (hd, uu___1) -> hd.FStar_Syntax_Syntax.pos
let range_of_args :
  'uuuuu 'uuuuu1 .
    ('uuuuu FStar_Syntax_Syntax.syntax * 'uuuuu1) Prims.list ->
      FStar_Range.range -> FStar_Range.range
  =
  fun args ->
    fun r ->
      FStar_All.pipe_right args
        (FStar_List.fold_left
           (fun r1 -> fun a -> FStar_Range.union_ranges r1 (range_of_arg a))
           r)
let (mk_app :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
      FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
      Prims.list -> FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun f ->
    fun args ->
      match args with
      | [] -> f
      | uu___ ->
          let r = range_of_args args f.FStar_Syntax_Syntax.pos in
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (f, args)) r
let (mk_app_binders :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun f ->
    fun bs ->
      let uu___ =
        FStar_List.map
          (fun uu___1 ->
             match uu___1 with
             | (bv, aq) ->
                 let uu___2 = FStar_Syntax_Syntax.bv_to_name bv in
                 (uu___2, aq)) bs in
      mk_app f uu___
let (field_projector_prefix : Prims.string) = "__proj__"
let (field_projector_sep : Prims.string) = "__item__"
let (field_projector_contains_constructor : Prims.string -> Prims.bool) =
  fun s -> FStar_Util.starts_with s field_projector_prefix
let (mk_field_projector_name_from_string :
  Prims.string -> Prims.string -> Prims.string) =
  fun constr ->
    fun field ->
      Prims.op_Hat field_projector_prefix
        (Prims.op_Hat constr (Prims.op_Hat field_projector_sep field))
let (mk_field_projector_name_from_ident :
  FStar_Ident.lident -> FStar_Ident.ident -> FStar_Ident.lident) =
  fun lid ->
    fun i ->
      let itext = FStar_Ident.string_of_id i in
      let newi =
        if field_projector_contains_constructor itext
        then i
        else
          (let uu___1 =
             let uu___2 =
               let uu___3 =
                 let uu___4 = FStar_Ident.ident_of_lid lid in
                 FStar_Ident.string_of_id uu___4 in
               mk_field_projector_name_from_string uu___3 itext in
             let uu___3 = FStar_Ident.range_of_id i in (uu___2, uu___3) in
           FStar_Ident.mk_ident uu___1) in
      let uu___ =
        let uu___1 = FStar_Ident.ns_of_lid lid in
        FStar_List.append uu___1 [newi] in
      FStar_Ident.lid_of_ids uu___
let (mk_field_projector_name :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.bv -> Prims.int -> FStar_Ident.lident)
  =
  fun lid ->
    fun x ->
      fun i ->
        let nm =
          let uu___ = FStar_Syntax_Syntax.is_null_bv x in
          if uu___
          then
            let uu___1 =
              let uu___2 =
                let uu___3 = FStar_Util.string_of_int i in
                Prims.op_Hat "_" uu___3 in
              let uu___3 = FStar_Syntax_Syntax.range_of_bv x in
              (uu___2, uu___3) in
            FStar_Ident.mk_ident uu___1
          else x.FStar_Syntax_Syntax.ppname in
        mk_field_projector_name_from_ident lid nm
let (ses_of_sigbundle :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun se ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_bundle (ses, uu___) -> ses
    | uu___ -> failwith "ses_of_sigbundle: not a Sig_bundle"
let (set_uvar : FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> unit)
  =
  fun uv ->
    fun t ->
      let uu___ = FStar_Syntax_Unionfind.find uv in
      match uu___ with
      | FStar_Pervasives_Native.Some uu___1 ->
          let uu___2 =
            let uu___3 =
              let uu___4 = FStar_Syntax_Unionfind.uvar_id uv in
              FStar_All.pipe_left FStar_Util.string_of_int uu___4 in
            FStar_Util.format1 "Changing a fixed uvar! ?%s\n" uu___3 in
          failwith uu___2
      | uu___1 -> FStar_Syntax_Unionfind.change uv t
let (qualifier_equal :
  FStar_Syntax_Syntax.qualifier ->
    FStar_Syntax_Syntax.qualifier -> Prims.bool)
  =
  fun q1 ->
    fun q2 ->
      match (q1, q2) with
      | (FStar_Syntax_Syntax.Discriminator l1,
         FStar_Syntax_Syntax.Discriminator l2) ->
          FStar_Ident.lid_equals l1 l2
      | (FStar_Syntax_Syntax.Projector (l1a, l1b),
         FStar_Syntax_Syntax.Projector (l2a, l2b)) ->
          (FStar_Ident.lid_equals l1a l2a) &&
            (let uu___ = FStar_Ident.string_of_id l1b in
             let uu___1 = FStar_Ident.string_of_id l2b in uu___ = uu___1)
      | (FStar_Syntax_Syntax.RecordType (ns1, f1),
         FStar_Syntax_Syntax.RecordType (ns2, f2)) ->
          ((((FStar_List.length ns1) = (FStar_List.length ns2)) &&
              (FStar_List.forall2
                 (fun x1 ->
                    fun x2 ->
                      let uu___ = FStar_Ident.string_of_id x1 in
                      let uu___1 = FStar_Ident.string_of_id x2 in
                      uu___ = uu___1) f1 f2))
             && ((FStar_List.length f1) = (FStar_List.length f2)))
            &&
            (FStar_List.forall2
               (fun x1 ->
                  fun x2 ->
                    let uu___ = FStar_Ident.string_of_id x1 in
                    let uu___1 = FStar_Ident.string_of_id x2 in
                    uu___ = uu___1) f1 f2)
      | (FStar_Syntax_Syntax.RecordConstructor (ns1, f1),
         FStar_Syntax_Syntax.RecordConstructor (ns2, f2)) ->
          ((((FStar_List.length ns1) = (FStar_List.length ns2)) &&
              (FStar_List.forall2
                 (fun x1 ->
                    fun x2 ->
                      let uu___ = FStar_Ident.string_of_id x1 in
                      let uu___1 = FStar_Ident.string_of_id x2 in
                      uu___ = uu___1) f1 f2))
             && ((FStar_List.length f1) = (FStar_List.length f2)))
            &&
            (FStar_List.forall2
               (fun x1 ->
                  fun x2 ->
                    let uu___ = FStar_Ident.string_of_id x1 in
                    let uu___1 = FStar_Ident.string_of_id x2 in
                    uu___ = uu___1) f1 f2)
      | uu___ -> q1 = q2
let (abs :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun bs ->
    fun t ->
      fun lopt ->
        let close_lopt lopt1 =
          match lopt1 with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some rc ->
              let uu___ =
                let uu___1 = rc in
                let uu___2 =
                  FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                    (FStar_Syntax_Subst.close bs) in
                {
                  FStar_Syntax_Syntax.residual_effect =
                    (uu___1.FStar_Syntax_Syntax.residual_effect);
                  FStar_Syntax_Syntax.residual_typ = uu___2;
                  FStar_Syntax_Syntax.residual_flags =
                    (uu___1.FStar_Syntax_Syntax.residual_flags)
                } in
              FStar_Pervasives_Native.Some uu___ in
        match bs with
        | [] -> t
        | uu___ ->
            let body =
              let uu___1 = FStar_Syntax_Subst.close bs t in
              FStar_Syntax_Subst.compress uu___1 in
            (match body.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Tm_abs (bs', t1, lopt') ->
                 let uu___1 =
                   let uu___2 =
                     let uu___3 =
                       let uu___4 = FStar_Syntax_Subst.close_binders bs in
                       FStar_List.append uu___4 bs' in
                     let uu___4 = close_lopt lopt' in (uu___3, t1, uu___4) in
                   FStar_Syntax_Syntax.Tm_abs uu___2 in
                 FStar_Syntax_Syntax.mk uu___1 t1.FStar_Syntax_Syntax.pos
             | uu___1 ->
                 let uu___2 =
                   let uu___3 =
                     let uu___4 = FStar_Syntax_Subst.close_binders bs in
                     let uu___5 = close_lopt lopt in (uu___4, body, uu___5) in
                   FStar_Syntax_Syntax.Tm_abs uu___3 in
                 FStar_Syntax_Syntax.mk uu___2 t.FStar_Syntax_Syntax.pos)
let (arrow :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) Prims.list ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun bs ->
    fun c ->
      match bs with
      | [] -> comp_result c
      | uu___ ->
          let uu___1 =
            let uu___2 =
              let uu___3 = FStar_Syntax_Subst.close_binders bs in
              let uu___4 = FStar_Syntax_Subst.close_comp bs c in
              (uu___3, uu___4) in
            FStar_Syntax_Syntax.Tm_arrow uu___2 in
          FStar_Syntax_Syntax.mk uu___1 c.FStar_Syntax_Syntax.pos
let (flat_arrow :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) Prims.list ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun bs ->
    fun c ->
      let t = arrow bs c in
      let uu___ =
        let uu___1 = FStar_Syntax_Subst.compress t in
        uu___1.FStar_Syntax_Syntax.n in
      match uu___ with
      | FStar_Syntax_Syntax.Tm_arrow (bs1, c1) ->
          (match c1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (tres, uu___1) ->
               let uu___2 =
                 let uu___3 = FStar_Syntax_Subst.compress tres in
                 uu___3.FStar_Syntax_Syntax.n in
               (match uu___2 with
                | FStar_Syntax_Syntax.Tm_arrow (bs', c') ->
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_arrow
                         ((FStar_List.append bs1 bs'), c'))
                      t.FStar_Syntax_Syntax.pos
                | uu___3 -> t)
           | uu___1 -> t)
      | uu___1 -> t
let rec (canon_arrow :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t ->
    let uu___ =
      let uu___1 = FStar_Syntax_Subst.compress t in
      uu___1.FStar_Syntax_Syntax.n in
    match uu___ with
    | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
        let cn =
          match c.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Total (t1, u) ->
              let uu___1 = let uu___2 = canon_arrow t1 in (uu___2, u) in
              FStar_Syntax_Syntax.Total uu___1
          | uu___1 -> c.FStar_Syntax_Syntax.n in
        let c1 =
          let uu___1 = c in
          {
            FStar_Syntax_Syntax.n = cn;
            FStar_Syntax_Syntax.pos = (uu___1.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars = (uu___1.FStar_Syntax_Syntax.vars)
          } in
        flat_arrow bs c1
    | uu___1 -> t
let (refine :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun b ->
    fun t ->
      let uu___ =
        let uu___1 =
          let uu___2 =
            let uu___3 =
              let uu___4 = FStar_Syntax_Syntax.mk_binder b in [uu___4] in
            FStar_Syntax_Subst.close uu___3 t in
          (b, uu___2) in
        FStar_Syntax_Syntax.Tm_refine uu___1 in
      let uu___1 =
        let uu___2 = FStar_Syntax_Syntax.range_of_bv b in
        FStar_Range.union_ranges uu___2 t.FStar_Syntax_Syntax.pos in
      FStar_Syntax_Syntax.mk uu___ uu___1
let (branch : FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch) =
  fun b -> FStar_Syntax_Subst.close_branch b
let (has_decreases : FStar_Syntax_Syntax.comp -> Prims.bool) =
  fun c ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp ct ->
        let uu___ =
          FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
            (FStar_Util.find_opt
               (fun uu___1 ->
                  match uu___1 with
                  | FStar_Syntax_Syntax.DECREASES uu___2 -> true
                  | uu___2 -> false)) in
        (match uu___ with
         | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.DECREASES d) ->
             true
         | uu___1 -> false)
    | uu___ -> false
let rec (arrow_formals_comp_ln :
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list * FStar_Syntax_Syntax.comp))
  =
  fun k ->
    let k1 = FStar_Syntax_Subst.compress k in
    match k1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
        let uu___ =
          (is_total_comp c) &&
            (let uu___1 = has_decreases c in Prims.op_Negation uu___1) in
        if uu___
        then
          let uu___1 = arrow_formals_comp_ln (comp_result c) in
          (match uu___1 with | (bs', k2) -> ((FStar_List.append bs bs'), k2))
        else (bs, c)
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu___;
           FStar_Syntax_Syntax.index = uu___1;
           FStar_Syntax_Syntax.sort = s;_},
         uu___2)
        ->
        let rec aux s1 k2 =
          let uu___3 =
            let uu___4 = FStar_Syntax_Subst.compress s1 in
            uu___4.FStar_Syntax_Syntax.n in
          match uu___3 with
          | FStar_Syntax_Syntax.Tm_arrow uu___4 -> arrow_formals_comp_ln s1
          | FStar_Syntax_Syntax.Tm_refine
              ({ FStar_Syntax_Syntax.ppname = uu___4;
                 FStar_Syntax_Syntax.index = uu___5;
                 FStar_Syntax_Syntax.sort = s2;_},
               uu___6)
              -> aux s2 k2
          | uu___4 ->
              let uu___5 = FStar_Syntax_Syntax.mk_Total k2 in ([], uu___5) in
        aux s k1
    | uu___ -> let uu___1 = FStar_Syntax_Syntax.mk_Total k1 in ([], uu___1)
let (arrow_formals_comp :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp))
  =
  fun k ->
    let uu___ = arrow_formals_comp_ln k in
    match uu___ with | (bs, c) -> FStar_Syntax_Subst.open_comp bs c
let (arrow_formals_ln :
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax))
  =
  fun k ->
    let uu___ = arrow_formals_comp_ln k in
    match uu___ with | (bs, c) -> (bs, (comp_result c))
let (arrow_formals :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax))
  =
  fun k ->
    let uu___ = arrow_formals_comp k in
    match uu___ with | (bs, c) -> (bs, (comp_result c))
let (let_rec_arity :
  FStar_Syntax_Syntax.letbinding ->
    (Prims.int * Prims.bool Prims.list FStar_Pervasives_Native.option))
  =
  fun lb ->
    let rec arrow_until_decreases k =
      let k1 = FStar_Syntax_Subst.compress k in
      match k1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
          let uu___ = FStar_Syntax_Subst.open_comp bs c in
          (match uu___ with
           | (bs1, c1) ->
               let ct = comp_to_comp_typ c1 in
               let uu___1 =
                 FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                   (FStar_Util.find_opt
                      (fun uu___2 ->
                         match uu___2 with
                         | FStar_Syntax_Syntax.DECREASES uu___3 -> true
                         | uu___3 -> false)) in
               (match uu___1 with
                | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.DECREASES
                    d) -> (bs1, (FStar_Pervasives_Native.Some d))
                | uu___2 ->
                    let uu___3 = is_total_comp c1 in
                    if uu___3
                    then
                      let uu___4 = arrow_until_decreases (comp_result c1) in
                      (match uu___4 with
                       | (bs', d) -> ((FStar_List.append bs1 bs'), d))
                    else (bs1, FStar_Pervasives_Native.None)))
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu___;
             FStar_Syntax_Syntax.index = uu___1;
             FStar_Syntax_Syntax.sort = k2;_},
           uu___2)
          -> arrow_until_decreases k2
      | uu___ -> ([], FStar_Pervasives_Native.None) in
    let uu___ = arrow_until_decreases lb.FStar_Syntax_Syntax.lbtyp in
    match uu___ with
    | (bs, dopt) ->
        let n_univs = FStar_List.length lb.FStar_Syntax_Syntax.lbunivs in
        let uu___1 =
          FStar_Util.map_opt dopt
            (fun d ->
               let d_bvs = FStar_Syntax_Free.names d in
               let uu___2 =
                 FStar_Common.tabulate n_univs (fun uu___3 -> false) in
               let uu___3 =
                 FStar_All.pipe_right bs
                   (FStar_List.map
                      (fun uu___4 ->
                         match uu___4 with
                         | (x, uu___5) -> FStar_Util.set_mem x d_bvs)) in
               FStar_List.append uu___2 uu___3) in
        ((n_univs + (FStar_List.length bs)), uu___1)
let (abs_formals :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term *
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option))
  =
  fun t ->
    let subst_lcomp_opt s l =
      match l with
      | FStar_Pervasives_Native.Some rc ->
          let uu___ =
            let uu___1 = rc in
            let uu___2 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (FStar_Syntax_Subst.subst s) in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___1.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu___2;
              FStar_Syntax_Syntax.residual_flags =
                (uu___1.FStar_Syntax_Syntax.residual_flags)
            } in
          FStar_Pervasives_Native.Some uu___
      | uu___ -> l in
    let rec aux t1 abs_body_lcomp =
      let uu___ =
        let uu___1 =
          let uu___2 = FStar_Syntax_Subst.compress t1 in
          FStar_All.pipe_left unascribe uu___2 in
        uu___1.FStar_Syntax_Syntax.n in
      match uu___ with
      | FStar_Syntax_Syntax.Tm_abs (bs, t2, what) ->
          let uu___1 = aux t2 what in
          (match uu___1 with
           | (bs', t3, what1) -> ((FStar_List.append bs bs'), t3, what1))
      | uu___1 -> ([], t1, abs_body_lcomp) in
    let uu___ = aux t FStar_Pervasives_Native.None in
    match uu___ with
    | (bs, t1, abs_body_lcomp) ->
        let uu___1 = FStar_Syntax_Subst.open_term' bs t1 in
        (match uu___1 with
         | (bs1, t2, opening) ->
             let abs_body_lcomp1 = subst_lcomp_opt opening abs_body_lcomp in
             (bs1, t2, abs_body_lcomp1))
let (remove_inacc : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t ->
    let no_acc uu___ =
      match uu___ with
      | (b, aq) ->
          let aq1 =
            match aq with
            | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
                (true)) ->
                FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Implicit false)
            | uu___1 -> aq in
          (b, aq1) in
    let uu___ = arrow_formals_comp_ln t in
    match uu___ with
    | (bs, c) ->
        (match bs with
         | [] -> t
         | uu___1 ->
             let uu___2 =
               let uu___3 =
                 let uu___4 = FStar_List.map no_acc bs in (uu___4, c) in
               FStar_Syntax_Syntax.Tm_arrow uu___3 in
             FStar_Syntax_Syntax.mk uu___2 t.FStar_Syntax_Syntax.pos)
let (mk_letbinding :
  (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.fv) FStar_Util.either ->
    FStar_Syntax_Syntax.univ_name Prims.list ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Ident.lident ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list
              -> FStar_Range.range -> FStar_Syntax_Syntax.letbinding)
  =
  fun lbname ->
    fun univ_vars ->
      fun typ ->
        fun eff ->
          fun def ->
            fun lbattrs ->
              fun pos ->
                {
                  FStar_Syntax_Syntax.lbname = lbname;
                  FStar_Syntax_Syntax.lbunivs = univ_vars;
                  FStar_Syntax_Syntax.lbtyp = typ;
                  FStar_Syntax_Syntax.lbeff = eff;
                  FStar_Syntax_Syntax.lbdef = def;
                  FStar_Syntax_Syntax.lbattrs = lbattrs;
                  FStar_Syntax_Syntax.lbpos = pos
                }
let (close_univs_and_mk_letbinding :
  FStar_Syntax_Syntax.fv Prims.list FStar_Pervasives_Native.option ->
    (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.fv) FStar_Util.either ->
      FStar_Syntax_Syntax.univ_name Prims.list ->
        FStar_Syntax_Syntax.term ->
          FStar_Ident.lident ->
            FStar_Syntax_Syntax.term ->
              FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list
                -> FStar_Range.range -> FStar_Syntax_Syntax.letbinding)
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
                          FStar_All.pipe_right univ_vars
                            (FStar_List.map
                               (fun uu___1 ->
                                  FStar_Syntax_Syntax.U_name uu___1)) in
                        let inst =
                          FStar_All.pipe_right fvs
                            (FStar_List.map
                               (fun fv ->
                                  (((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v),
                                    universes))) in
                        FStar_Syntax_InstFV.instantiate inst def in
                  let typ1 = FStar_Syntax_Subst.close_univ_vars univ_vars typ in
                  let def2 =
                    FStar_Syntax_Subst.close_univ_vars univ_vars def1 in
                  mk_letbinding lbname univ_vars typ1 eff def2 attrs pos
let (open_univ_vars_binders_and_comp :
  FStar_Syntax_Syntax.univ_names ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
        (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv *
          FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
          Prims.list * FStar_Syntax_Syntax.comp))
  =
  fun uvs ->
    fun binders ->
      fun c ->
        match binders with
        | [] ->
            let uu___ = FStar_Syntax_Subst.open_univ_vars_comp uvs c in
            (match uu___ with | (uvs1, c1) -> (uvs1, [], c1))
        | uu___ ->
            let t' = arrow binders c in
            let uu___1 = FStar_Syntax_Subst.open_univ_vars uvs t' in
            (match uu___1 with
             | (uvs1, t'1) ->
                 let uu___2 =
                   let uu___3 = FStar_Syntax_Subst.compress t'1 in
                   uu___3.FStar_Syntax_Syntax.n in
                 (match uu___2 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders1, c1) ->
                      (uvs1, binders1, c1)
                  | uu___3 -> failwith "Impossible"))
let (is_tuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        let uu___ =
          FStar_Ident.string_of_lid
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        FStar_Parser_Const.is_tuple_constructor_string uu___
    | uu___ -> false
let (is_dtuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_dtuple_constructor_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu___ -> false
let (is_lid_equality : FStar_Ident.lident -> Prims.bool) =
  fun x -> FStar_Ident.lid_equals x FStar_Parser_Const.eq2_lid
let (is_forall : FStar_Ident.lident -> Prims.bool) =
  fun lid -> FStar_Ident.lid_equals lid FStar_Parser_Const.forall_lid
let (is_exists : FStar_Ident.lident -> Prims.bool) =
  fun lid -> FStar_Ident.lid_equals lid FStar_Parser_Const.exists_lid
let (is_qlid : FStar_Ident.lident -> Prims.bool) =
  fun lid -> (is_forall lid) || (is_exists lid)
let (is_equality :
  FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t -> Prims.bool) =
  fun x -> is_lid_equality x.FStar_Syntax_Syntax.v
let (lid_is_connective : FStar_Ident.lident -> Prims.bool) =
  let lst =
    [FStar_Parser_Const.and_lid;
    FStar_Parser_Const.or_lid;
    FStar_Parser_Const.not_lid;
    FStar_Parser_Const.iff_lid;
    FStar_Parser_Const.imp_lid] in
  fun lid -> FStar_Util.for_some (FStar_Ident.lid_equals lid) lst
let (is_constructor :
  FStar_Syntax_Syntax.term -> FStar_Ident.lident -> Prims.bool) =
  fun t ->
    fun lid ->
      let uu___ = let uu___1 = pre_typ t in uu___1.FStar_Syntax_Syntax.n in
      match uu___ with
      | FStar_Syntax_Syntax.Tm_fvar tc ->
          FStar_Ident.lid_equals
            (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v lid
      | uu___1 -> false
let rec (is_constructed_typ :
  FStar_Syntax_Syntax.term -> FStar_Ident.lident -> Prims.bool) =
  fun t ->
    fun lid ->
      let uu___ = let uu___1 = pre_typ t in uu___1.FStar_Syntax_Syntax.n in
      match uu___ with
      | FStar_Syntax_Syntax.Tm_fvar uu___1 -> is_constructor t lid
      | FStar_Syntax_Syntax.Tm_app (t1, uu___1) -> is_constructed_typ t1 lid
      | FStar_Syntax_Syntax.Tm_uinst (t1, uu___1) ->
          is_constructed_typ t1 lid
      | uu___1 -> false
let rec (get_tycon :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun t ->
    let t1 = pre_typ t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar uu___ -> FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_name uu___ -> FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_fvar uu___ -> FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_app (t2, uu___) -> get_tycon t2
    | uu___ -> FStar_Pervasives_Native.None
let (is_fstar_tactics_by_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu___ = let uu___1 = un_uinst t in uu___1.FStar_Syntax_Syntax.n in
    match uu___ with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.by_tactic_lid
    | uu___1 -> false
let (is_builtin_tactic : FStar_Ident.lident -> Prims.bool) =
  fun md ->
    let path = FStar_Ident.path_of_lid md in
    if (FStar_List.length path) > (Prims.of_int (2))
    then
      let uu___ =
        let uu___1 = FStar_List.splitAt (Prims.of_int (2)) path in
        FStar_Pervasives_Native.fst uu___1 in
      match uu___ with
      | "FStar"::"Tactics"::[] -> true
      | "FStar"::"Reflection"::[] -> true
      | uu___1 -> false
    else false
let (ktype : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.mk
    (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
    FStar_Range.dummyRange
let (ktype0 : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.mk
    (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
    FStar_Range.dummyRange
let (type_u :
  unit -> (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.universe)) =
  fun uu___ ->
    let u =
      let uu___1 = FStar_Syntax_Unionfind.univ_fresh FStar_Range.dummyRange in
      FStar_All.pipe_left (fun uu___2 -> FStar_Syntax_Syntax.U_unif uu___2)
        uu___1 in
    let uu___1 =
      FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)
        FStar_Range.dummyRange in
    (uu___1, u)
let (attr_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun a ->
    fun a' ->
      let uu___ = eq_tm a a' in
      match uu___ with | Equal -> true | uu___1 -> false
let (attr_substitute : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  let uu___ =
    let uu___1 =
      let uu___2 =
        FStar_Ident.lid_of_path ["FStar"; "Pervasives"; "Substitute"]
          FStar_Range.dummyRange in
      FStar_Syntax_Syntax.lid_as_fv uu___2 FStar_Syntax_Syntax.delta_constant
        FStar_Pervasives_Native.None in
    FStar_Syntax_Syntax.Tm_fvar uu___1 in
  FStar_Syntax_Syntax.mk uu___ FStar_Range.dummyRange
let (exp_true_bool : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.mk
    (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true))
    FStar_Range.dummyRange
let (exp_false_bool : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.mk
    (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false))
    FStar_Range.dummyRange
let (exp_unit : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.mk
    (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_unit)
    FStar_Range.dummyRange
let (exp_int : Prims.string -> FStar_Syntax_Syntax.term) =
  fun s ->
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant
         (FStar_Const.Const_int (s, FStar_Pervasives_Native.None)))
      FStar_Range.dummyRange
let (exp_char : FStar_BaseTypes.char -> FStar_Syntax_Syntax.term) =
  fun c ->
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c))
      FStar_Range.dummyRange
let (exp_string : Prims.string -> FStar_Syntax_Syntax.term) =
  fun s ->
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant
         (FStar_Const.Const_string (s, FStar_Range.dummyRange)))
      FStar_Range.dummyRange
let (fvar_const : FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun l ->
    FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.delta_constant
      FStar_Pervasives_Native.None
let (tand : FStar_Syntax_Syntax.term) = fvar_const FStar_Parser_Const.and_lid
let (tor : FStar_Syntax_Syntax.term) = fvar_const FStar_Parser_Const.or_lid
let (timp : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.fvar FStar_Parser_Const.imp_lid
    (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_one)
    FStar_Pervasives_Native.None
let (tiff : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.fvar FStar_Parser_Const.iff_lid
    (FStar_Syntax_Syntax.Delta_constant_at_level (Prims.of_int (2)))
    FStar_Pervasives_Native.None
let (t_bool : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.bool_lid
let (b2t_v : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.b2t_lid
let (t_not : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.not_lid
let (t_false : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.false_lid
let (t_true : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.true_lid
let (tac_opaque_attr : FStar_Syntax_Syntax.term) = exp_string "tac_opaque"
let (dm4f_bind_range_attr : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.dm4f_bind_range_attr
let (tcdecltime_attr : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.tcdecltime_attr
let (inline_let_attr : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.inline_let_attr
let (rename_let_attr : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.rename_let_attr
let (t_ctx_uvar_and_sust : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.ctx_uvar_and_subst_lid
let (mk_conj_opt :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
    FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
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
                  let uu___4 = FStar_Syntax_Syntax.as_arg phi11 in
                  let uu___5 =
                    let uu___6 = FStar_Syntax_Syntax.as_arg phi2 in [uu___6] in
                  uu___4 :: uu___5 in
                (tand, uu___3) in
              FStar_Syntax_Syntax.Tm_app uu___2 in
            let uu___2 =
              FStar_Range.union_ranges phi11.FStar_Syntax_Syntax.pos
                phi2.FStar_Syntax_Syntax.pos in
            FStar_Syntax_Syntax.mk uu___1 uu___2 in
          FStar_Pervasives_Native.Some uu___
let (mk_binop :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun op_t ->
    fun phi1 ->
      fun phi2 ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              let uu___3 = FStar_Syntax_Syntax.as_arg phi1 in
              let uu___4 =
                let uu___5 = FStar_Syntax_Syntax.as_arg phi2 in [uu___5] in
              uu___3 :: uu___4 in
            (op_t, uu___2) in
          FStar_Syntax_Syntax.Tm_app uu___1 in
        let uu___1 =
          FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos
            phi2.FStar_Syntax_Syntax.pos in
        FStar_Syntax_Syntax.mk uu___ uu___1
let (mk_neg :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun phi ->
    let uu___ =
      let uu___1 =
        let uu___2 = let uu___3 = FStar_Syntax_Syntax.as_arg phi in [uu___3] in
        (t_not, uu___2) in
      FStar_Syntax_Syntax.Tm_app uu___1 in
    FStar_Syntax_Syntax.mk uu___ phi.FStar_Syntax_Syntax.pos
let (mk_conj :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  = fun phi1 -> fun phi2 -> mk_binop tand phi1 phi2
let (mk_conj_l :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun phi ->
    match phi with
    | [] ->
        FStar_Syntax_Syntax.fvar FStar_Parser_Const.true_lid
          FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
    | hd::tl -> FStar_List.fold_right mk_conj tl hd
let (mk_disj :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  = fun phi1 -> fun phi2 -> mk_binop tor phi1 phi2
let (mk_disj_l :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun phi ->
    match phi with
    | [] -> t_false
    | hd::tl -> FStar_List.fold_right mk_disj tl hd
let (mk_imp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term)
  = fun phi1 -> fun phi2 -> mk_binop timp phi1 phi2
let (mk_iff :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term)
  = fun phi1 -> fun phi2 -> mk_binop tiff phi1 phi2
let (b2t :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun e ->
    let uu___ =
      let uu___1 =
        let uu___2 = let uu___3 = FStar_Syntax_Syntax.as_arg e in [uu___3] in
        (b2t_v, uu___2) in
      FStar_Syntax_Syntax.Tm_app uu___1 in
    FStar_Syntax_Syntax.mk uu___ e.FStar_Syntax_Syntax.pos
let (unb2t :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun e ->
    let uu___ = head_and_args e in
    match uu___ with
    | (hd, args) ->
        let uu___1 =
          let uu___2 =
            let uu___3 = FStar_Syntax_Subst.compress hd in
            uu___3.FStar_Syntax_Syntax.n in
          (uu___2, args) in
        (match uu___1 with
         | (FStar_Syntax_Syntax.Tm_fvar fv, (e1, uu___2)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.b2t_lid ->
             FStar_Pervasives_Native.Some e1
         | uu___2 -> FStar_Pervasives_Native.None)
let (is_t_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu___ = let uu___1 = unmeta t in uu___1.FStar_Syntax_Syntax.n in
    match uu___ with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
    | uu___1 -> false
let (mk_conj_simp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t1 ->
    fun t2 ->
      let uu___ = is_t_true t1 in
      if uu___
      then t2
      else
        (let uu___2 = is_t_true t2 in if uu___2 then t1 else mk_conj t1 t2)
let (mk_disj_simp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t1 ->
    fun t2 ->
      let uu___ = is_t_true t1 in
      if uu___
      then t_true
      else
        (let uu___2 = is_t_true t2 in
         if uu___2 then t_true else mk_disj t1 t2)
let (teq : FStar_Syntax_Syntax.term) = fvar_const FStar_Parser_Const.eq2_lid
let (mk_untyped_eq2 :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun e1 ->
    fun e2 ->
      let uu___ =
        let uu___1 =
          let uu___2 =
            let uu___3 = FStar_Syntax_Syntax.as_arg e1 in
            let uu___4 =
              let uu___5 = FStar_Syntax_Syntax.as_arg e2 in [uu___5] in
            uu___3 :: uu___4 in
          (teq, uu___2) in
        FStar_Syntax_Syntax.Tm_app uu___1 in
      let uu___1 =
        FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
          e2.FStar_Syntax_Syntax.pos in
      FStar_Syntax_Syntax.mk uu___ uu___1
let (mk_eq2 :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun u ->
    fun t ->
      fun e1 ->
        fun e2 ->
          let eq_inst = FStar_Syntax_Syntax.mk_Tm_uinst teq [u] in
          let uu___ =
            let uu___1 =
              let uu___2 =
                let uu___3 = FStar_Syntax_Syntax.iarg t in
                let uu___4 =
                  let uu___5 = FStar_Syntax_Syntax.as_arg e1 in
                  let uu___6 =
                    let uu___7 = FStar_Syntax_Syntax.as_arg e2 in [uu___7] in
                  uu___5 :: uu___6 in
                uu___3 :: uu___4 in
              (eq_inst, uu___2) in
            FStar_Syntax_Syntax.Tm_app uu___1 in
          let uu___1 =
            FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
              e2.FStar_Syntax_Syntax.pos in
          FStar_Syntax_Syntax.mk uu___ uu___1
let (mk_has_type :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t ->
    fun x ->
      fun t' ->
        let t_has_type = fvar_const FStar_Parser_Const.has_type_lid in
        let t_has_type1 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_uinst
               (t_has_type,
                 [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]))
            FStar_Range.dummyRange in
        let uu___ =
          let uu___1 =
            let uu___2 =
              let uu___3 = FStar_Syntax_Syntax.iarg t in
              let uu___4 =
                let uu___5 = FStar_Syntax_Syntax.as_arg x in
                let uu___6 =
                  let uu___7 = FStar_Syntax_Syntax.as_arg t' in [uu___7] in
                uu___5 :: uu___6 in
              uu___3 :: uu___4 in
            (t_has_type1, uu___2) in
          FStar_Syntax_Syntax.Tm_app uu___1 in
        FStar_Syntax_Syntax.mk uu___ FStar_Range.dummyRange
let (mk_with_type :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun u ->
    fun t ->
      fun e ->
        let t_with_type =
          FStar_Syntax_Syntax.fvar FStar_Parser_Const.with_type_lid
            FStar_Syntax_Syntax.delta_equational FStar_Pervasives_Native.None in
        let t_with_type1 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_uinst (t_with_type, [u]))
            FStar_Range.dummyRange in
        let uu___ =
          let uu___1 =
            let uu___2 =
              let uu___3 = FStar_Syntax_Syntax.iarg t in
              let uu___4 =
                let uu___5 = FStar_Syntax_Syntax.as_arg e in [uu___5] in
              uu___3 :: uu___4 in
            (t_with_type1, uu___2) in
          FStar_Syntax_Syntax.Tm_app uu___1 in
        FStar_Syntax_Syntax.mk uu___ FStar_Range.dummyRange
let (lex_t : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.lex_t_lid
let (lex_top : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.fvar FStar_Parser_Const.lextop_lid
    FStar_Syntax_Syntax.delta_constant
    (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
let (lex_pair : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.fvar FStar_Parser_Const.lexcons_lid
    FStar_Syntax_Syntax.delta_constant
    (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
let (tforall : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.fvar FStar_Parser_Const.forall_lid
    (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_one)
    FStar_Pervasives_Native.None
let (t_haseq : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.fvar FStar_Parser_Const.haseq_lid
    FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
let (decidable_eq : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.op_Eq
let (mk_decidable_eq :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t ->
    fun e1 ->
      fun e2 ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              let uu___3 = FStar_Syntax_Syntax.iarg t in
              let uu___4 =
                let uu___5 = FStar_Syntax_Syntax.as_arg e1 in
                let uu___6 =
                  let uu___7 = FStar_Syntax_Syntax.as_arg e2 in [uu___7] in
                uu___5 :: uu___6 in
              uu___3 :: uu___4 in
            (decidable_eq, uu___2) in
          FStar_Syntax_Syntax.Tm_app uu___1 in
        let uu___1 =
          FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
            e2.FStar_Syntax_Syntax.pos in
        FStar_Syntax_Syntax.mk uu___ uu___1
let (b_and : FStar_Syntax_Syntax.term) = fvar_const FStar_Parser_Const.op_And
let (mk_and :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun e1 ->
    fun e2 ->
      let uu___ =
        let uu___1 =
          let uu___2 =
            let uu___3 = FStar_Syntax_Syntax.as_arg e1 in
            let uu___4 =
              let uu___5 = FStar_Syntax_Syntax.as_arg e2 in [uu___5] in
            uu___3 :: uu___4 in
          (b_and, uu___2) in
        FStar_Syntax_Syntax.Tm_app uu___1 in
      let uu___1 =
        FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
          e2.FStar_Syntax_Syntax.pos in
      FStar_Syntax_Syntax.mk uu___ uu___1
let (mk_and_l :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun l ->
    match l with
    | [] -> exp_true_bool
    | hd::tl -> FStar_List.fold_left mk_and hd tl
let (mk_residual_comp :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.cflag Prims.list ->
        FStar_Syntax_Syntax.residual_comp)
  =
  fun l ->
    fun t ->
      fun f ->
        {
          FStar_Syntax_Syntax.residual_effect = l;
          FStar_Syntax_Syntax.residual_typ = t;
          FStar_Syntax_Syntax.residual_flags = f
        }
let (residual_tot :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.residual_comp)
  =
  fun t ->
    {
      FStar_Syntax_Syntax.residual_effect = FStar_Parser_Const.effect_Tot_lid;
      FStar_Syntax_Syntax.residual_typ = (FStar_Pervasives_Native.Some t);
      FStar_Syntax_Syntax.residual_flags = [FStar_Syntax_Syntax.TOTAL]
    }
let (residual_comp_of_comp :
  FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.residual_comp) =
  fun c ->
    {
      FStar_Syntax_Syntax.residual_effect = (comp_effect_name c);
      FStar_Syntax_Syntax.residual_typ =
        (FStar_Pervasives_Native.Some (comp_result c));
      FStar_Syntax_Syntax.residual_flags = (comp_flags c)
    }
let (mk_forall_aux :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.bv ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun fa ->
    fun x ->
      fun body ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              let uu___3 =
                FStar_Syntax_Syntax.iarg x.FStar_Syntax_Syntax.sort in
              let uu___4 =
                let uu___5 =
                  let uu___6 =
                    let uu___7 =
                      let uu___8 = FStar_Syntax_Syntax.mk_binder x in
                      [uu___8] in
                    abs uu___7 body
                      (FStar_Pervasives_Native.Some (residual_tot ktype0)) in
                  FStar_Syntax_Syntax.as_arg uu___6 in
                [uu___5] in
              uu___3 :: uu___4 in
            (fa, uu___2) in
          FStar_Syntax_Syntax.Tm_app uu___1 in
        FStar_Syntax_Syntax.mk uu___ FStar_Range.dummyRange
let (mk_forall_no_univ :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ)
  = fun x -> fun body -> mk_forall_aux tforall x body
let (mk_forall :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.bv ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ)
  =
  fun u ->
    fun x ->
      fun body ->
        let tforall1 = FStar_Syntax_Syntax.mk_Tm_uinst tforall [u] in
        mk_forall_aux tforall1 x body
let (close_forall_no_univs :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) Prims.list ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ)
  =
  fun bs ->
    fun f ->
      FStar_List.fold_right
        (fun b ->
           fun f1 ->
             let uu___ = FStar_Syntax_Syntax.is_null_binder b in
             if uu___
             then f1
             else mk_forall_no_univ (FStar_Pervasives_Native.fst b) f1) bs f
let (is_wild_pat :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t -> Prims.bool) =
  fun p ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu___ -> true
    | uu___ -> false
let (if_then_else :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun b ->
    fun t1 ->
      fun t2 ->
        let then_branch =
          let uu___ =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool true))
              t1.FStar_Syntax_Syntax.pos in
          (uu___, FStar_Pervasives_Native.None, t1) in
        let else_branch =
          let uu___ =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant
                 (FStar_Const.Const_bool false)) t2.FStar_Syntax_Syntax.pos in
          (uu___, FStar_Pervasives_Native.None, t2) in
        let uu___ =
          let uu___1 =
            FStar_Range.union_ranges t1.FStar_Syntax_Syntax.pos
              t2.FStar_Syntax_Syntax.pos in
          FStar_Range.union_ranges b.FStar_Syntax_Syntax.pos uu___1 in
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_match (b, [then_branch; else_branch]))
          uu___
let (mk_squash :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun u ->
    fun p ->
      let sq =
        FStar_Syntax_Syntax.fvar FStar_Parser_Const.squash_lid
          (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_one)
          FStar_Pervasives_Native.None in
      let uu___ = FStar_Syntax_Syntax.mk_Tm_uinst sq [u] in
      let uu___1 = let uu___2 = FStar_Syntax_Syntax.as_arg p in [uu___2] in
      mk_app uu___ uu___1
let (mk_auto_squash :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun u ->
    fun p ->
      let sq =
        FStar_Syntax_Syntax.fvar FStar_Parser_Const.auto_squash_lid
          (FStar_Syntax_Syntax.Delta_constant_at_level (Prims.of_int (2)))
          FStar_Pervasives_Native.None in
      let uu___ = FStar_Syntax_Syntax.mk_Tm_uinst sq [u] in
      let uu___1 = let uu___2 = FStar_Syntax_Syntax.as_arg p in [uu___2] in
      mk_app uu___ uu___1
let (un_squash :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
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
            let uu___3 = FStar_Syntax_Subst.compress head2 in
            uu___3.FStar_Syntax_Syntax.n in
          (uu___2, args) in
        (match uu___1 with
         | (FStar_Syntax_Syntax.Tm_fvar fv, (p, uu___2)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some p
         | (FStar_Syntax_Syntax.Tm_refine (b, p), []) ->
             (match (b.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.unit_lid
                  ->
                  let uu___2 =
                    let uu___3 =
                      let uu___4 = FStar_Syntax_Syntax.mk_binder b in
                      [uu___4] in
                    FStar_Syntax_Subst.open_term uu___3 p in
                  (match uu___2 with
                   | (bs, p1) ->
                       let b1 =
                         match bs with
                         | b2::[] -> b2
                         | uu___3 -> failwith "impossible" in
                       let uu___3 =
                         let uu___4 = FStar_Syntax_Free.names p1 in
                         FStar_Util.set_mem (FStar_Pervasives_Native.fst b1)
                           uu___4 in
                       if uu___3
                       then FStar_Pervasives_Native.None
                       else FStar_Pervasives_Native.Some p1)
              | uu___2 -> FStar_Pervasives_Native.None)
         | uu___2 -> FStar_Pervasives_Native.None)
let (is_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax) FStar_Pervasives_Native.option)
  =
  fun t ->
    let uu___ = head_and_args t in
    match uu___ with
    | (head, args) ->
        let uu___1 =
          let uu___2 =
            let uu___3 = FStar_Syntax_Subst.compress head in
            uu___3.FStar_Syntax_Syntax.n in
          (uu___2, args) in
        (match uu___1 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu___2;
               FStar_Syntax_Syntax.vars = uu___3;_},
             u::[]),
            (t1, uu___4)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu___2 -> FStar_Pervasives_Native.None)
let (is_auto_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax) FStar_Pervasives_Native.option)
  =
  fun t ->
    let uu___ = head_and_args t in
    match uu___ with
    | (head, args) ->
        let uu___1 =
          let uu___2 =
            let uu___3 = FStar_Syntax_Subst.compress head in
            uu___3.FStar_Syntax_Syntax.n in
          (uu___2, args) in
        (match uu___1 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu___2;
               FStar_Syntax_Syntax.vars = uu___3;_},
             u::[]),
            (t1, uu___4)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.auto_squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu___2 -> FStar_Pervasives_Native.None)
let (is_sub_singleton : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu___ = let uu___1 = unmeta t in head_and_args uu___1 in
    match uu___ with
    | (head, uu___1) ->
        let uu___2 =
          let uu___3 = un_uinst head in uu___3.FStar_Syntax_Syntax.n in
        (match uu___2 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             (((((((((((((((((FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.squash_lid)
                               ||
                               (FStar_Syntax_Syntax.fv_eq_lid fv
                                  FStar_Parser_Const.auto_squash_lid))
                              ||
                              (FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.and_lid))
                             ||
                             (FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.or_lid))
                            ||
                            (FStar_Syntax_Syntax.fv_eq_lid fv
                               FStar_Parser_Const.not_lid))
                           ||
                           (FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.imp_lid))
                          ||
                          (FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.iff_lid))
                         ||
                         (FStar_Syntax_Syntax.fv_eq_lid fv
                            FStar_Parser_Const.ite_lid))
                        ||
                        (FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.exists_lid))
                       ||
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.forall_lid))
                      ||
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.true_lid))
                     ||
                     (FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.false_lid))
                    ||
                    (FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.eq2_lid))
                   ||
                   (FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.eq3_lid))
                  ||
                  (FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.b2t_lid))
                 ||
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.haseq_lid))
                ||
                (FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid))
               ||
               (FStar_Syntax_Syntax.fv_eq_lid fv
                  FStar_Parser_Const.precedes_lid)
         | uu___3 -> false)
let (arrow_one_ln :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.option)
  =
  fun t ->
    let uu___ =
      let uu___1 = FStar_Syntax_Subst.compress t in
      uu___1.FStar_Syntax_Syntax.n in
    match uu___ with
    | FStar_Syntax_Syntax.Tm_arrow ([], c) ->
        failwith "fatal: empty binders on arrow?"
    | FStar_Syntax_Syntax.Tm_arrow (b::[], c) ->
        FStar_Pervasives_Native.Some (b, c)
    | FStar_Syntax_Syntax.Tm_arrow (b::bs, c) ->
        let uu___1 =
          let uu___2 =
            let uu___3 = arrow bs c in FStar_Syntax_Syntax.mk_Total uu___3 in
          (b, uu___2) in
        FStar_Pervasives_Native.Some uu___1
    | uu___1 -> FStar_Pervasives_Native.None
let (arrow_one :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.option)
  =
  fun t ->
    let uu___ = arrow_one_ln t in
    FStar_Util.bind_opt uu___
      (fun uu___1 ->
         match uu___1 with
         | (b, c) ->
             let uu___2 = FStar_Syntax_Subst.open_comp [b] c in
             (match uu___2 with
              | (bs, c1) ->
                  let b1 =
                    match bs with
                    | b2::[] -> b2
                    | uu___3 ->
                        failwith
                          "impossible: open_comp returned different amount of binders" in
                  FStar_Pervasives_Native.Some (b1, c1)))
let (is_free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv ->
    fun t ->
      let uu___ = FStar_Syntax_Free.names t in FStar_Util.set_mem bv uu___
type qpats = FStar_Syntax_Syntax.args Prims.list
type connective =
  | QAll of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ) 
  | QEx of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ) 
  | BaseConn of (FStar_Ident.lident * FStar_Syntax_Syntax.args) 
let (uu___is_QAll : connective -> Prims.bool) =
  fun projectee -> match projectee with | QAll _0 -> true | uu___ -> false
let (__proj__QAll__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ))
  = fun projectee -> match projectee with | QAll _0 -> _0
let (uu___is_QEx : connective -> Prims.bool) =
  fun projectee -> match projectee with | QEx _0 -> true | uu___ -> false
let (__proj__QEx__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ))
  = fun projectee -> match projectee with | QEx _0 -> _0
let (uu___is_BaseConn : connective -> Prims.bool) =
  fun projectee ->
    match projectee with | BaseConn _0 -> true | uu___ -> false
let (__proj__BaseConn__item___0 :
  connective -> (FStar_Ident.lident * FStar_Syntax_Syntax.args)) =
  fun projectee -> match projectee with | BaseConn _0 -> _0
let (destruct_base_table :
  (Prims.int * (FStar_Ident.lident * FStar_Ident.lident) Prims.list)
    Prims.list)
  =
  let f x = (x, x) in
  [(Prims.int_zero,
     [f FStar_Parser_Const.true_lid; f FStar_Parser_Const.false_lid]);
  ((Prims.of_int (2)),
    [f FStar_Parser_Const.and_lid;
    f FStar_Parser_Const.or_lid;
    f FStar_Parser_Const.imp_lid;
    f FStar_Parser_Const.iff_lid;
    f FStar_Parser_Const.eq2_lid;
    f FStar_Parser_Const.eq3_lid]);
  (Prims.int_one, [f FStar_Parser_Const.not_lid]);
  ((Prims.of_int (3)),
    [f FStar_Parser_Const.ite_lid; f FStar_Parser_Const.eq2_lid]);
  ((Prims.of_int (4)), [f FStar_Parser_Const.eq3_lid])]
let (destruct_sq_base_table :
  (Prims.int * (FStar_Ident.lident * FStar_Ident.lident) Prims.list)
    Prims.list)
  =
  [((Prims.of_int (2)),
     [(FStar_Parser_Const.c_and_lid, FStar_Parser_Const.and_lid);
     (FStar_Parser_Const.c_or_lid, FStar_Parser_Const.or_lid);
     (FStar_Parser_Const.c_eq2_lid, FStar_Parser_Const.c_eq2_lid);
     (FStar_Parser_Const.c_eq3_lid, FStar_Parser_Const.c_eq3_lid)]);
  ((Prims.of_int (3)),
    [(FStar_Parser_Const.c_eq2_lid, FStar_Parser_Const.c_eq2_lid)]);
  ((Prims.of_int (4)),
    [(FStar_Parser_Const.c_eq3_lid, FStar_Parser_Const.c_eq3_lid)]);
  (Prims.int_zero,
    [(FStar_Parser_Const.c_true_lid, FStar_Parser_Const.true_lid);
    (FStar_Parser_Const.c_false_lid, FStar_Parser_Const.false_lid)])]
let (destruct_typ_as_formula :
  FStar_Syntax_Syntax.term -> connective FStar_Pervasives_Native.option) =
  fun f ->
    let rec unmeta_monadic f1 =
      let f2 = FStar_Syntax_Subst.compress f1 in
      match f2.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta
          (t, FStar_Syntax_Syntax.Meta_monadic uu___) -> unmeta_monadic t
      | FStar_Syntax_Syntax.Tm_meta
          (t, FStar_Syntax_Syntax.Meta_monadic_lift uu___) ->
          unmeta_monadic t
      | uu___ -> f2 in
    let lookup_arity_lid table target_lid args =
      let arg_len = FStar_List.length args in
      let aux uu___ =
        match uu___ with
        | (arity, lids) ->
            if arg_len = arity
            then
              FStar_Util.find_map lids
                (fun uu___1 ->
                   match uu___1 with
                   | (lid, out_lid) ->
                       let uu___2 = FStar_Ident.lid_equals target_lid lid in
                       if uu___2
                       then
                         FStar_Pervasives_Native.Some
                           (BaseConn (out_lid, args))
                       else FStar_Pervasives_Native.None)
            else FStar_Pervasives_Native.None in
      FStar_Util.find_map table aux in
    let destruct_base_conn t =
      let uu___ = head_and_args t in
      match uu___ with
      | (hd, args) ->
          let uu___1 =
            let uu___2 = un_uinst hd in uu___2.FStar_Syntax_Syntax.n in
          (match uu___1 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               lookup_arity_lid destruct_base_table
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v args
           | uu___2 -> FStar_Pervasives_Native.None) in
    let destruct_sq_base_conn t =
      let uu___ = un_squash t in
      FStar_Util.bind_opt uu___
        (fun t1 ->
           let uu___1 = head_and_args_full t1 in
           match uu___1 with
           | (hd, args) ->
               let uu___2 =
                 let uu___3 = un_uinst hd in uu___3.FStar_Syntax_Syntax.n in
               (match uu___2 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    lookup_arity_lid destruct_sq_base_table
                      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      args
                | uu___3 -> FStar_Pervasives_Native.None)) in
    let patterns t =
      let t1 = FStar_Syntax_Subst.compress t in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta
          (t2, FStar_Syntax_Syntax.Meta_pattern (uu___, pats)) ->
          let uu___1 = FStar_Syntax_Subst.compress t2 in (pats, uu___1)
      | uu___ -> ([], t1) in
    let destruct_q_conn t =
      let is_q fa fv =
        if fa
        then is_forall (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
        else is_exists (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
      let flat t1 =
        let uu___ = head_and_args t1 in
        match uu___ with
        | (t2, args) ->
            let uu___1 = un_uinst t2 in
            let uu___2 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu___3 ->
                      match uu___3 with
                      | (t3, imp) ->
                          let uu___4 = unascribe t3 in (uu___4, imp))) in
            (uu___1, uu___2) in
      let rec aux qopt out t1 =
        let uu___ = let uu___1 = flat t1 in (qopt, uu___1) in
        match uu___ with
        | (FStar_Pervasives_Native.Some fa,
           ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
              FStar_Syntax_Syntax.pos = uu___1;
              FStar_Syntax_Syntax.vars = uu___2;_},
            ({
               FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                 (b::[], t2, uu___3);
               FStar_Syntax_Syntax.pos = uu___4;
               FStar_Syntax_Syntax.vars = uu___5;_},
             uu___6)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.Some fa,
           ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
              FStar_Syntax_Syntax.pos = uu___1;
              FStar_Syntax_Syntax.vars = uu___2;_},
            uu___3::({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                         (b::[], t2, uu___4);
                       FStar_Syntax_Syntax.pos = uu___5;
                       FStar_Syntax_Syntax.vars = uu___6;_},
                     uu___7)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.None,
           ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
              FStar_Syntax_Syntax.pos = uu___1;
              FStar_Syntax_Syntax.vars = uu___2;_},
            ({
               FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                 (b::[], t2, uu___3);
               FStar_Syntax_Syntax.pos = uu___4;
               FStar_Syntax_Syntax.vars = uu___5;_},
             uu___6)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu___7 =
              let uu___8 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
              FStar_Pervasives_Native.Some uu___8 in
            aux uu___7 (b :: out) t2
        | (FStar_Pervasives_Native.None,
           ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
              FStar_Syntax_Syntax.pos = uu___1;
              FStar_Syntax_Syntax.vars = uu___2;_},
            uu___3::({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                         (b::[], t2, uu___4);
                       FStar_Syntax_Syntax.pos = uu___5;
                       FStar_Syntax_Syntax.vars = uu___6;_},
                     uu___7)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu___8 =
              let uu___9 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
              FStar_Pervasives_Native.Some uu___9 in
            aux uu___8 (b :: out) t2
        | (FStar_Pervasives_Native.Some b, uu___1) ->
            let bs = FStar_List.rev out in
            let uu___2 = FStar_Syntax_Subst.open_term bs t1 in
            (match uu___2 with
             | (bs1, t2) ->
                 let uu___3 = patterns t2 in
                 (match uu___3 with
                  | (pats, body) ->
                      if b
                      then
                        FStar_Pervasives_Native.Some (QAll (bs1, pats, body))
                      else
                        FStar_Pervasives_Native.Some (QEx (bs1, pats, body))))
        | uu___1 -> FStar_Pervasives_Native.None in
      aux FStar_Pervasives_Native.None [] t in
    let rec destruct_sq_forall t =
      let uu___ = un_squash t in
      FStar_Util.bind_opt uu___
        (fun t1 ->
           let uu___1 = arrow_one t1 in
           match uu___1 with
           | FStar_Pervasives_Native.Some (b, c) ->
               let uu___2 =
                 let uu___3 = is_tot_or_gtot_comp c in
                 Prims.op_Negation uu___3 in
               if uu___2
               then FStar_Pervasives_Native.None
               else
                 (let q =
                    let uu___4 = comp_to_comp_typ_nouniv c in
                    uu___4.FStar_Syntax_Syntax.result_typ in
                  let uu___4 = is_free_in (FStar_Pervasives_Native.fst b) q in
                  if uu___4
                  then
                    let uu___5 = patterns q in
                    match uu___5 with
                    | (pats, q1) ->
                        FStar_All.pipe_left maybe_collect
                          (FStar_Pervasives_Native.Some
                             (QAll ([b], pats, q1)))
                  else
                    (let uu___6 =
                       let uu___7 =
                         let uu___8 =
                           let uu___9 =
                             FStar_Syntax_Syntax.as_arg
                               (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                           let uu___10 =
                             let uu___11 = FStar_Syntax_Syntax.as_arg q in
                             [uu___11] in
                           uu___9 :: uu___10 in
                         (FStar_Parser_Const.imp_lid, uu___8) in
                       BaseConn uu___7 in
                     FStar_Pervasives_Native.Some uu___6))
           | uu___2 -> FStar_Pervasives_Native.None)
    and destruct_sq_exists t =
      let uu___ = un_squash t in
      FStar_Util.bind_opt uu___
        (fun t1 ->
           let uu___1 = head_and_args_full t1 in
           match uu___1 with
           | (hd, args) ->
               let uu___2 =
                 let uu___3 =
                   let uu___4 = un_uinst hd in uu___4.FStar_Syntax_Syntax.n in
                 (uu___3, args) in
               (match uu___2 with
                | (FStar_Syntax_Syntax.Tm_fvar fv,
                   (a1, uu___3)::(a2, uu___4)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.dtuple2_lid
                    ->
                    let uu___5 =
                      let uu___6 = FStar_Syntax_Subst.compress a2 in
                      uu___6.FStar_Syntax_Syntax.n in
                    (match uu___5 with
                     | FStar_Syntax_Syntax.Tm_abs (b::[], q, uu___6) ->
                         let uu___7 = FStar_Syntax_Subst.open_term [b] q in
                         (match uu___7 with
                          | (bs, q1) ->
                              let b1 =
                                match bs with
                                | b2::[] -> b2
                                | uu___8 -> failwith "impossible" in
                              let uu___8 = patterns q1 in
                              (match uu___8 with
                               | (pats, q2) ->
                                   FStar_All.pipe_left maybe_collect
                                     (FStar_Pervasives_Native.Some
                                        (QEx ([b1], pats, q2)))))
                     | uu___6 -> FStar_Pervasives_Native.None)
                | uu___3 -> FStar_Pervasives_Native.None))
    and maybe_collect f1 =
      match f1 with
      | FStar_Pervasives_Native.Some (QAll (bs, pats, phi)) ->
          let uu___ = destruct_sq_forall phi in
          (match uu___ with
           | FStar_Pervasives_Native.Some (QAll (bs', pats', psi)) ->
               FStar_All.pipe_left
                 (fun uu___1 -> FStar_Pervasives_Native.Some uu___1)
                 (QAll
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu___1 -> f1)
      | FStar_Pervasives_Native.Some (QEx (bs, pats, phi)) ->
          let uu___ = destruct_sq_exists phi in
          (match uu___ with
           | FStar_Pervasives_Native.Some (QEx (bs', pats', psi)) ->
               FStar_All.pipe_left
                 (fun uu___1 -> FStar_Pervasives_Native.Some uu___1)
                 (QEx
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu___1 -> f1)
      | uu___ -> f1 in
    let phi = unmeta_monadic f in
    let uu___ = destruct_base_conn phi in
    FStar_Util.catch_opt uu___
      (fun uu___1 ->
         let uu___2 = destruct_q_conn phi in
         FStar_Util.catch_opt uu___2
           (fun uu___3 ->
              let uu___4 = destruct_sq_base_conn phi in
              FStar_Util.catch_opt uu___4
                (fun uu___5 ->
                   let uu___6 = destruct_sq_forall phi in
                   FStar_Util.catch_opt uu___6
                     (fun uu___7 ->
                        let uu___8 = destruct_sq_exists phi in
                        FStar_Util.catch_opt uu___8
                          (fun uu___9 -> FStar_Pervasives_Native.None)))))
let (action_as_lb :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.action ->
      FStar_Range.range -> FStar_Syntax_Syntax.sigelt)
  =
  fun eff_lid ->
    fun a ->
      fun pos ->
        let lb =
          let uu___ =
            let uu___1 =
              FStar_Syntax_Syntax.lid_as_fv a.FStar_Syntax_Syntax.action_name
                FStar_Syntax_Syntax.delta_equational
                FStar_Pervasives_Native.None in
            FStar_Util.Inr uu___1 in
          let uu___1 =
            let uu___2 =
              FStar_Syntax_Syntax.mk_Total a.FStar_Syntax_Syntax.action_typ in
            arrow a.FStar_Syntax_Syntax.action_params uu___2 in
          let uu___2 =
            abs a.FStar_Syntax_Syntax.action_params
              a.FStar_Syntax_Syntax.action_defn FStar_Pervasives_Native.None in
          close_univs_and_mk_letbinding FStar_Pervasives_Native.None uu___
            a.FStar_Syntax_Syntax.action_univs uu___1
            FStar_Parser_Const.effect_Tot_lid uu___2 [] pos in
        {
          FStar_Syntax_Syntax.sigel =
            (FStar_Syntax_Syntax.Sig_let
               ((false, [lb]), [a.FStar_Syntax_Syntax.action_name]));
          FStar_Syntax_Syntax.sigrng =
            ((a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos);
          FStar_Syntax_Syntax.sigquals =
            [FStar_Syntax_Syntax.Visible_default;
            FStar_Syntax_Syntax.Action eff_lid];
          FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta;
          FStar_Syntax_Syntax.sigattrs = [];
          FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
        }
let (mk_reify :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t ->
    let reify_ =
      FStar_Syntax_Syntax.mk
        (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_reify)
        t.FStar_Syntax_Syntax.pos in
    let uu___ =
      let uu___1 =
        let uu___2 = let uu___3 = FStar_Syntax_Syntax.as_arg t in [uu___3] in
        (reify_, uu___2) in
      FStar_Syntax_Syntax.Tm_app uu___1 in
    FStar_Syntax_Syntax.mk uu___ t.FStar_Syntax_Syntax.pos
let (mk_reflect :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t ->
    let reflect_ =
      let uu___ =
        let uu___1 =
          let uu___2 = FStar_Ident.lid_of_str "Bogus.Effect" in
          FStar_Const.Const_reflect uu___2 in
        FStar_Syntax_Syntax.Tm_constant uu___1 in
      FStar_Syntax_Syntax.mk uu___ t.FStar_Syntax_Syntax.pos in
    let uu___ =
      let uu___1 =
        let uu___2 = let uu___3 = FStar_Syntax_Syntax.as_arg t in [uu___3] in
        (reflect_, uu___2) in
      FStar_Syntax_Syntax.Tm_app uu___1 in
    FStar_Syntax_Syntax.mk uu___ t.FStar_Syntax_Syntax.pos
let rec (delta_qualifier :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth) =
  fun t ->
    let t1 = FStar_Syntax_Subst.compress t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu___ -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_lazy i ->
        let uu___ = unfold_lazy i in delta_qualifier uu___
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv.FStar_Syntax_Syntax.fv_delta
    | FStar_Syntax_Syntax.Tm_bvar uu___ ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_name uu___ ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_match uu___ ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_uvar uu___ ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_unknown -> FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_type uu___ -> FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_quoted uu___ ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_constant uu___ ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_arrow uu___ ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_uinst (t2, uu___) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu___;
           FStar_Syntax_Syntax.index = uu___1;
           FStar_Syntax_Syntax.sort = t2;_},
         uu___2)
        -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_meta (t2, uu___) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_ascribed (t2, uu___, uu___1) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_app (t2, uu___) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_abs (uu___, t2, uu___1) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_let (uu___, t2) -> delta_qualifier t2
let rec (incr_delta_depth :
  FStar_Syntax_Syntax.delta_depth -> FStar_Syntax_Syntax.delta_depth) =
  fun d ->
    match d with
    | FStar_Syntax_Syntax.Delta_constant_at_level i ->
        FStar_Syntax_Syntax.Delta_constant_at_level (i + Prims.int_one)
    | FStar_Syntax_Syntax.Delta_equational_at_level i ->
        FStar_Syntax_Syntax.Delta_equational_at_level (i + Prims.int_one)
    | FStar_Syntax_Syntax.Delta_abstract d1 -> incr_delta_depth d1
let (incr_delta_qualifier :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth) =
  fun t -> let uu___ = delta_qualifier t in incr_delta_depth uu___
let (is_unknown : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu___ =
      let uu___1 = FStar_Syntax_Subst.compress t in
      uu___1.FStar_Syntax_Syntax.n in
    match uu___ with
    | FStar_Syntax_Syntax.Tm_unknown -> true
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
  FStar_Syntax_Syntax.eff_decl -> Prims.string -> FStar_Ident.lident) =
  fun ed ->
    fun name ->
      let p = FStar_Ident.path_of_lid ed.FStar_Syntax_Syntax.mname in
      let p' =
        apply_last
          (fun s ->
             Prims.op_Hat "_dm4f_" (Prims.op_Hat s (Prims.op_Hat "_" name)))
          p in
      FStar_Ident.lid_of_path p' FStar_Range.dummyRange
let (mk_list :
  FStar_Syntax_Syntax.term ->
    FStar_Range.range ->
      FStar_Syntax_Syntax.term Prims.list -> FStar_Syntax_Syntax.term)
  =
  fun typ ->
    fun rng ->
      fun l ->
        let ctor l1 =
          let uu___ =
            let uu___1 =
              FStar_Syntax_Syntax.lid_as_fv l1
                FStar_Syntax_Syntax.delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor) in
            FStar_Syntax_Syntax.Tm_fvar uu___1 in
          FStar_Syntax_Syntax.mk uu___ rng in
        let cons args pos =
          let uu___ =
            let uu___1 = ctor FStar_Parser_Const.cons_lid in
            FStar_Syntax_Syntax.mk_Tm_uinst uu___1
              [FStar_Syntax_Syntax.U_zero] in
          FStar_Syntax_Syntax.mk_Tm_app uu___ args pos in
        let nil args pos =
          let uu___ =
            let uu___1 = ctor FStar_Parser_Const.nil_lid in
            FStar_Syntax_Syntax.mk_Tm_uinst uu___1
              [FStar_Syntax_Syntax.U_zero] in
          FStar_Syntax_Syntax.mk_Tm_app uu___ args pos in
        let uu___ =
          let uu___1 = let uu___2 = FStar_Syntax_Syntax.iarg typ in [uu___2] in
          nil uu___1 rng in
        FStar_List.fold_right
          (fun t ->
             fun a ->
               let uu___1 =
                 let uu___2 = FStar_Syntax_Syntax.iarg typ in
                 let uu___3 =
                   let uu___4 = FStar_Syntax_Syntax.as_arg t in
                   let uu___5 =
                     let uu___6 = FStar_Syntax_Syntax.as_arg a in [uu___6] in
                   uu___4 :: uu___5 in
                 uu___2 :: uu___3 in
               cons uu___1 t.FStar_Syntax_Syntax.pos) l uu___
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
        ('a, 'b) FStar_Util.either ->
          ('a, 'b) FStar_Util.either -> Prims.bool
  =
  fun e1 ->
    fun e2 ->
      fun x ->
        fun y ->
          match (x, y) with
          | (FStar_Util.Inl x1, FStar_Util.Inl y1) -> e1 x1 y1
          | (FStar_Util.Inr x1, FStar_Util.Inr y1) -> e2 x1 y1
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
        | uu___ -> false
let (debug_term_eq : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false
let (check : Prims.string -> Prims.bool -> Prims.bool) =
  fun msg ->
    fun cond ->
      if cond
      then true
      else
        ((let uu___2 = FStar_ST.op_Bang debug_term_eq in
          if uu___2
          then FStar_Util.print1 ">>> term_eq failing: %s\n" msg
          else ());
         false)
let (fail : Prims.string -> Prims.bool) = fun msg -> check msg false
let rec (term_eq_dbg :
  Prims.bool ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool)
  =
  fun dbg ->
    fun t1 ->
      fun t2 ->
        let t11 = let uu___ = unmeta_safe t1 in canon_app uu___ in
        let t21 = let uu___ = unmeta_safe t2 in canon_app uu___ in
        let uu___ =
          let uu___1 =
            let uu___2 =
              let uu___3 = un_uinst t11 in FStar_Syntax_Subst.compress uu___3 in
            uu___2.FStar_Syntax_Syntax.n in
          let uu___2 =
            let uu___3 =
              let uu___4 = un_uinst t21 in FStar_Syntax_Subst.compress uu___4 in
            uu___3.FStar_Syntax_Syntax.n in
          (uu___1, uu___2) in
        match uu___ with
        | (FStar_Syntax_Syntax.Tm_uinst uu___1, uu___2) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu___1, FStar_Syntax_Syntax.Tm_uinst uu___2) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_delayed uu___1, uu___2) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu___1, FStar_Syntax_Syntax.Tm_delayed uu___2) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_ascribed uu___1, uu___2) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu___1, FStar_Syntax_Syntax.Tm_ascribed uu___2) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_bvar x, FStar_Syntax_Syntax.Tm_bvar y) ->
            check "bvar"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_name x, FStar_Syntax_Syntax.Tm_name y) ->
            check "name"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_fvar x, FStar_Syntax_Syntax.Tm_fvar y) ->
            let uu___1 = FStar_Syntax_Syntax.fv_eq x y in check "fvar" uu___1
        | (FStar_Syntax_Syntax.Tm_constant c1,
           FStar_Syntax_Syntax.Tm_constant c2) ->
            let uu___1 = FStar_Const.eq_const c1 c2 in check "const" uu___1
        | (FStar_Syntax_Syntax.Tm_type uu___1, FStar_Syntax_Syntax.Tm_type
           uu___2) -> true
        | (FStar_Syntax_Syntax.Tm_abs (b1, t12, k1),
           FStar_Syntax_Syntax.Tm_abs (b2, t22, k2)) ->
            (let uu___1 = eqlist (binder_eq_dbg dbg) b1 b2 in
             check "abs binders" uu___1) &&
              (let uu___1 = term_eq_dbg dbg t12 t22 in
               check "abs bodies" uu___1)
        | (FStar_Syntax_Syntax.Tm_arrow (b1, c1),
           FStar_Syntax_Syntax.Tm_arrow (b2, c2)) ->
            (let uu___1 = eqlist (binder_eq_dbg dbg) b1 b2 in
             check "arrow binders" uu___1) &&
              (let uu___1 = comp_eq_dbg dbg c1 c2 in
               check "arrow comp" uu___1)
        | (FStar_Syntax_Syntax.Tm_refine (b1, t12),
           FStar_Syntax_Syntax.Tm_refine (b2, t22)) ->
            (let uu___1 =
               term_eq_dbg dbg b1.FStar_Syntax_Syntax.sort
                 b2.FStar_Syntax_Syntax.sort in
             check "refine bv sort" uu___1) &&
              (let uu___1 = term_eq_dbg dbg t12 t22 in
               check "refine formula" uu___1)
        | (FStar_Syntax_Syntax.Tm_app (f1, a1), FStar_Syntax_Syntax.Tm_app
           (f2, a2)) ->
            (let uu___1 = term_eq_dbg dbg f1 f2 in check "app head" uu___1)
              &&
              (let uu___1 = eqlist (arg_eq_dbg dbg) a1 a2 in
               check "app args" uu___1)
        | (FStar_Syntax_Syntax.Tm_match (t12, bs1),
           FStar_Syntax_Syntax.Tm_match (t22, bs2)) ->
            (let uu___1 = term_eq_dbg dbg t12 t22 in
             check "match head" uu___1) &&
              (let uu___1 = eqlist (branch_eq_dbg dbg) bs1 bs2 in
               check "match branches" uu___1)
        | (FStar_Syntax_Syntax.Tm_lazy uu___1, uu___2) ->
            let uu___3 =
              let uu___4 = unlazy t11 in term_eq_dbg dbg uu___4 t21 in
            check "lazy_l" uu___3
        | (uu___1, FStar_Syntax_Syntax.Tm_lazy uu___2) ->
            let uu___3 =
              let uu___4 = unlazy t21 in term_eq_dbg dbg t11 uu___4 in
            check "lazy_r" uu___3
        | (FStar_Syntax_Syntax.Tm_let ((b1, lbs1), t12),
           FStar_Syntax_Syntax.Tm_let ((b2, lbs2), t22)) ->
            ((check "let flag" (b1 = b2)) &&
               (let uu___1 = eqlist (letbinding_eq_dbg dbg) lbs1 lbs2 in
                check "let lbs" uu___1))
              &&
              (let uu___1 = term_eq_dbg dbg t12 t22 in
               check "let body" uu___1)
        | (FStar_Syntax_Syntax.Tm_uvar (u1, uu___1),
           FStar_Syntax_Syntax.Tm_uvar (u2, uu___2)) ->
            check "uvar"
              (u1.FStar_Syntax_Syntax.ctx_uvar_head =
                 u2.FStar_Syntax_Syntax.ctx_uvar_head)
        | (FStar_Syntax_Syntax.Tm_quoted (qt1, qi1),
           FStar_Syntax_Syntax.Tm_quoted (qt2, qi2)) ->
            (let uu___1 = let uu___2 = eq_quoteinfo qi1 qi2 in uu___2 = Equal in
             check "tm_quoted qi" uu___1) &&
              (let uu___1 = term_eq_dbg dbg qt1 qt2 in
               check "tm_quoted payload" uu___1)
        | (FStar_Syntax_Syntax.Tm_meta (t12, m1), FStar_Syntax_Syntax.Tm_meta
           (t22, m2)) ->
            (match (m1, m2) with
             | (FStar_Syntax_Syntax.Meta_monadic (n1, ty1),
                FStar_Syntax_Syntax.Meta_monadic (n2, ty2)) ->
                 (let uu___1 = FStar_Ident.lid_equals n1 n2 in
                  check "meta_monadic lid" uu___1) &&
                   (let uu___1 = term_eq_dbg dbg ty1 ty2 in
                    check "meta_monadic type" uu___1)
             | (FStar_Syntax_Syntax.Meta_monadic_lift (s1, t13, ty1),
                FStar_Syntax_Syntax.Meta_monadic_lift (s2, t23, ty2)) ->
                 ((let uu___1 = FStar_Ident.lid_equals s1 s2 in
                   check "meta_monadic_lift src" uu___1) &&
                    (let uu___1 = FStar_Ident.lid_equals t13 t23 in
                     check "meta_monadic_lift tgt" uu___1))
                   &&
                   (let uu___1 = term_eq_dbg dbg ty1 ty2 in
                    check "meta_monadic_lift type" uu___1)
             | uu___1 -> fail "metas")
        | (FStar_Syntax_Syntax.Tm_unknown, uu___1) -> fail "unk"
        | (uu___1, FStar_Syntax_Syntax.Tm_unknown) -> fail "unk"
        | (FStar_Syntax_Syntax.Tm_bvar uu___1, uu___2) -> fail "bottom"
        | (FStar_Syntax_Syntax.Tm_name uu___1, uu___2) -> fail "bottom"
        | (FStar_Syntax_Syntax.Tm_fvar uu___1, uu___2) -> fail "bottom"
        | (FStar_Syntax_Syntax.Tm_constant uu___1, uu___2) -> fail "bottom"
        | (FStar_Syntax_Syntax.Tm_type uu___1, uu___2) -> fail "bottom"
        | (FStar_Syntax_Syntax.Tm_abs uu___1, uu___2) -> fail "bottom"
        | (FStar_Syntax_Syntax.Tm_arrow uu___1, uu___2) -> fail "bottom"
        | (FStar_Syntax_Syntax.Tm_refine uu___1, uu___2) -> fail "bottom"
        | (FStar_Syntax_Syntax.Tm_app uu___1, uu___2) -> fail "bottom"
        | (FStar_Syntax_Syntax.Tm_match uu___1, uu___2) -> fail "bottom"
        | (FStar_Syntax_Syntax.Tm_let uu___1, uu___2) -> fail "bottom"
        | (FStar_Syntax_Syntax.Tm_uvar uu___1, uu___2) -> fail "bottom"
        | (FStar_Syntax_Syntax.Tm_meta uu___1, uu___2) -> fail "bottom"
        | (uu___1, FStar_Syntax_Syntax.Tm_bvar uu___2) -> fail "bottom"
        | (uu___1, FStar_Syntax_Syntax.Tm_name uu___2) -> fail "bottom"
        | (uu___1, FStar_Syntax_Syntax.Tm_fvar uu___2) -> fail "bottom"
        | (uu___1, FStar_Syntax_Syntax.Tm_constant uu___2) -> fail "bottom"
        | (uu___1, FStar_Syntax_Syntax.Tm_type uu___2) -> fail "bottom"
        | (uu___1, FStar_Syntax_Syntax.Tm_abs uu___2) -> fail "bottom"
        | (uu___1, FStar_Syntax_Syntax.Tm_arrow uu___2) -> fail "bottom"
        | (uu___1, FStar_Syntax_Syntax.Tm_refine uu___2) -> fail "bottom"
        | (uu___1, FStar_Syntax_Syntax.Tm_app uu___2) -> fail "bottom"
        | (uu___1, FStar_Syntax_Syntax.Tm_match uu___2) -> fail "bottom"
        | (uu___1, FStar_Syntax_Syntax.Tm_let uu___2) -> fail "bottom"
        | (uu___1, FStar_Syntax_Syntax.Tm_uvar uu___2) -> fail "bottom"
        | (uu___1, FStar_Syntax_Syntax.Tm_meta uu___2) -> fail "bottom"
and (arg_eq_dbg :
  Prims.bool ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
      FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
        FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) ->
        Prims.bool)
  =
  fun dbg ->
    fun a1 ->
      fun a2 ->
        eqprod
          (fun t1 ->
             fun t2 ->
               let uu___ = term_eq_dbg dbg t1 t2 in check "arg tm" uu___)
          (fun q1 ->
             fun q2 ->
               let uu___ = let uu___1 = eq_aqual q1 q2 in uu___1 = Equal in
               check "arg qual" uu___) a1 a2
and (binder_eq_dbg :
  Prims.bool ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) -> Prims.bool)
  =
  fun dbg ->
    fun b1 ->
      fun b2 ->
        eqprod
          (fun b11 ->
             fun b21 ->
               let uu___ =
                 term_eq_dbg dbg b11.FStar_Syntax_Syntax.sort
                   b21.FStar_Syntax_Syntax.sort in
               check "binder sort" uu___)
          (fun q1 ->
             fun q2 ->
               let uu___ = let uu___1 = eq_aqual q1 q2 in uu___1 = Equal in
               check "binder qual" uu___) b1 b2
and (comp_eq_dbg :
  Prims.bool ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool)
  =
  fun dbg ->
    fun c1 ->
      fun c2 ->
        let c11 = comp_to_comp_typ_nouniv c1 in
        let c21 = comp_to_comp_typ_nouniv c2 in
        ((let uu___ =
            FStar_Ident.lid_equals c11.FStar_Syntax_Syntax.effect_name
              c21.FStar_Syntax_Syntax.effect_name in
          check "comp eff" uu___) &&
           (let uu___ =
              term_eq_dbg dbg c11.FStar_Syntax_Syntax.result_typ
                c21.FStar_Syntax_Syntax.result_typ in
            check "comp result typ" uu___))
          && true
and (branch_eq_dbg :
  Prims.bool ->
    (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t *
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax) ->
      (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t *
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
        FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term'
        FStar_Syntax_Syntax.syntax) -> Prims.bool)
  =
  fun dbg ->
    fun uu___ ->
      fun uu___1 ->
        match (uu___, uu___1) with
        | ((p1, w1, t1), (p2, w2, t2)) ->
            ((let uu___2 = FStar_Syntax_Syntax.eq_pat p1 p2 in
              check "branch pat" uu___2) &&
               (let uu___2 = term_eq_dbg dbg t1 t2 in
                check "branch body" uu___2))
              &&
              (let uu___2 =
                 match (w1, w2) with
                 | (FStar_Pervasives_Native.Some x,
                    FStar_Pervasives_Native.Some y) -> term_eq_dbg dbg x y
                 | (FStar_Pervasives_Native.None,
                    FStar_Pervasives_Native.None) -> true
                 | uu___3 -> false in
               check "branch when" uu___2)
and (letbinding_eq_dbg :
  Prims.bool ->
    FStar_Syntax_Syntax.letbinding ->
      FStar_Syntax_Syntax.letbinding -> Prims.bool)
  =
  fun dbg ->
    fun lb1 ->
      fun lb2 ->
        ((let uu___ =
            eqsum (fun bv1 -> fun bv2 -> true) FStar_Syntax_Syntax.fv_eq
              lb1.FStar_Syntax_Syntax.lbname lb2.FStar_Syntax_Syntax.lbname in
          check "lb bv" uu___) &&
           (let uu___ =
              term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbtyp
                lb2.FStar_Syntax_Syntax.lbtyp in
            check "lb typ" uu___))
          &&
          (let uu___ =
             term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbdef
               lb2.FStar_Syntax_Syntax.lbdef in
           check "lb def" uu___)
let (term_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t1 ->
    fun t2 ->
      let r =
        let uu___ = FStar_ST.op_Bang debug_term_eq in term_eq_dbg uu___ t1 t2 in
      FStar_ST.op_Colon_Equals debug_term_eq false; r
let rec (sizeof : FStar_Syntax_Syntax.term -> Prims.int) =
  fun t ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu___ ->
        let uu___1 =
          let uu___2 = FStar_Syntax_Subst.compress t in sizeof uu___2 in
        Prims.int_one + uu___1
    | FStar_Syntax_Syntax.Tm_bvar bv ->
        let uu___ = sizeof bv.FStar_Syntax_Syntax.sort in
        Prims.int_one + uu___
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu___ = sizeof bv.FStar_Syntax_Syntax.sort in
        Prims.int_one + uu___
    | FStar_Syntax_Syntax.Tm_uinst (t1, us) ->
        let uu___ = sizeof t1 in (FStar_List.length us) + uu___
    | FStar_Syntax_Syntax.Tm_abs (bs, t1, uu___) ->
        let uu___1 = sizeof t1 in
        let uu___2 =
          FStar_List.fold_left
            (fun acc ->
               fun uu___3 ->
                 match uu___3 with
                 | (bv, uu___4) ->
                     let uu___5 = sizeof bv.FStar_Syntax_Syntax.sort in
                     acc + uu___5) Prims.int_zero bs in
        uu___1 + uu___2
    | FStar_Syntax_Syntax.Tm_app (hd, args) ->
        let uu___ = sizeof hd in
        let uu___1 =
          FStar_List.fold_left
            (fun acc ->
               fun uu___2 ->
                 match uu___2 with
                 | (arg, uu___3) -> let uu___4 = sizeof arg in acc + uu___4)
            Prims.int_zero args in
        uu___ + uu___1
    | uu___ -> Prims.int_one
let (is_fvar : FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool)
  =
  fun lid ->
    fun t ->
      let uu___ = let uu___1 = un_uinst t in uu___1.FStar_Syntax_Syntax.n in
      match uu___ with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_Syntax_Syntax.fv_eq_lid fv lid
      | uu___1 -> false
let (is_synth_by_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t -> is_fvar FStar_Parser_Const.synth_lid t
let (has_attribute :
  FStar_Syntax_Syntax.attribute Prims.list ->
    FStar_Ident.lident -> Prims.bool)
  = fun attrs -> fun attr -> FStar_Util.for_some (is_fvar attr) attrs
let (get_attribute :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.attribute Prims.list ->
      FStar_Syntax_Syntax.args FStar_Pervasives_Native.option)
  =
  fun attr ->
    fun attrs ->
      FStar_List.tryPick
        (fun t ->
           let uu___ = head_and_args t in
           match uu___ with
           | (head, args) ->
               let uu___1 =
                 let uu___2 = FStar_Syntax_Subst.compress head in
                 uu___2.FStar_Syntax_Syntax.n in
               (match uu___1 with
                | FStar_Syntax_Syntax.Tm_fvar fv when
                    FStar_Syntax_Syntax.fv_eq_lid fv attr ->
                    FStar_Pervasives_Native.Some args
                | uu___2 -> FStar_Pervasives_Native.None)) attrs
let (remove_attr :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.attribute Prims.list ->
      FStar_Syntax_Syntax.attribute Prims.list)
  =
  fun attr ->
    fun attrs ->
      FStar_List.filter
        (fun a -> let uu___ = is_fvar attr a in Prims.op_Negation uu___)
        attrs
let (process_pragma :
  FStar_Syntax_Syntax.pragma -> FStar_Range.range -> unit) =
  fun p ->
    fun r ->
      FStar_Errors.set_option_warning_callback_range
        (FStar_Pervasives_Native.Some r);
      (let set_options s =
         let uu___1 = FStar_Options.set_options s in
         match uu___1 with
         | FStar_Getopt.Success -> ()
         | FStar_Getopt.Help ->
             FStar_Errors.raise_error
               (FStar_Errors.Fatal_FailToProcessPragma,
                 "Failed to process pragma: use 'fstar --help' to see which options are available")
               r
         | FStar_Getopt.Error s1 ->
             FStar_Errors.raise_error
               (FStar_Errors.Fatal_FailToProcessPragma,
                 (Prims.op_Hat "Failed to process pragma: " s1)) r in
       match p with
       | FStar_Syntax_Syntax.LightOff -> FStar_Options.set_ml_ish ()
       | FStar_Syntax_Syntax.SetOptions o -> set_options o
       | FStar_Syntax_Syntax.ResetOptions sopt ->
           ((let uu___2 = FStar_Options.restore_cmd_line_options false in
             FStar_All.pipe_right uu___2 (fun uu___3 -> ()));
            (match sopt with
             | FStar_Pervasives_Native.None -> ()
             | FStar_Pervasives_Native.Some s -> set_options s))
       | FStar_Syntax_Syntax.PushOptions sopt ->
           (FStar_Options.internal_push ();
            (match sopt with
             | FStar_Pervasives_Native.None -> ()
             | FStar_Pervasives_Native.Some s -> set_options s))
       | FStar_Syntax_Syntax.RestartSolver -> ()
       | FStar_Syntax_Syntax.PopOptions ->
           let uu___1 = FStar_Options.internal_pop () in
           if uu___1
           then ()
           else
             FStar_Errors.raise_error
               (FStar_Errors.Fatal_FailToProcessPragma,
                 "Cannot #pop-options, stack would become empty") r)
let rec (unbound_variables :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.bv Prims.list)
  =
  fun tm ->
    let t = FStar_Syntax_Subst.compress tm in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu___ -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name x -> []
    | FStar_Syntax_Syntax.Tm_uvar uu___ -> []
    | FStar_Syntax_Syntax.Tm_type u -> []
    | FStar_Syntax_Syntax.Tm_bvar x -> [x]
    | FStar_Syntax_Syntax.Tm_fvar uu___ -> []
    | FStar_Syntax_Syntax.Tm_constant uu___ -> []
    | FStar_Syntax_Syntax.Tm_lazy uu___ -> []
    | FStar_Syntax_Syntax.Tm_unknown -> []
    | FStar_Syntax_Syntax.Tm_uinst (t1, us) -> unbound_variables t1
    | FStar_Syntax_Syntax.Tm_abs (bs, t1, uu___) ->
        let uu___1 = FStar_Syntax_Subst.open_term bs t1 in
        (match uu___1 with
         | (bs1, t2) ->
             let uu___2 =
               FStar_List.collect
                 (fun uu___3 ->
                    match uu___3 with
                    | (b, uu___4) ->
                        unbound_variables b.FStar_Syntax_Syntax.sort) bs1 in
             let uu___3 = unbound_variables t2 in
             FStar_List.append uu___2 uu___3)
    | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
        let uu___ = FStar_Syntax_Subst.open_comp bs c in
        (match uu___ with
         | (bs1, c1) ->
             let uu___1 =
               FStar_List.collect
                 (fun uu___2 ->
                    match uu___2 with
                    | (b, uu___3) ->
                        unbound_variables b.FStar_Syntax_Syntax.sort) bs1 in
             let uu___2 = unbound_variables_comp c1 in
             FStar_List.append uu___1 uu___2)
    | FStar_Syntax_Syntax.Tm_refine (b, t1) ->
        let uu___ =
          FStar_Syntax_Subst.open_term [(b, FStar_Pervasives_Native.None)] t1 in
        (match uu___ with
         | (bs, t2) ->
             let uu___1 =
               FStar_List.collect
                 (fun uu___2 ->
                    match uu___2 with
                    | (b1, uu___3) ->
                        unbound_variables b1.FStar_Syntax_Syntax.sort) bs in
             let uu___2 = unbound_variables t2 in
             FStar_List.append uu___1 uu___2)
    | FStar_Syntax_Syntax.Tm_app (t1, args) ->
        let uu___ =
          FStar_List.collect
            (fun uu___1 ->
               match uu___1 with | (x, uu___2) -> unbound_variables x) args in
        let uu___1 = unbound_variables t1 in FStar_List.append uu___ uu___1
    | FStar_Syntax_Syntax.Tm_match (t1, pats) ->
        let uu___ = unbound_variables t1 in
        let uu___1 =
          FStar_All.pipe_right pats
            (FStar_List.collect
               (fun br ->
                  let uu___2 = FStar_Syntax_Subst.open_branch br in
                  match uu___2 with
                  | (p, wopt, t2) ->
                      let uu___3 = unbound_variables t2 in
                      let uu___4 =
                        match wopt with
                        | FStar_Pervasives_Native.None -> []
                        | FStar_Pervasives_Native.Some t3 ->
                            unbound_variables t3 in
                      FStar_List.append uu___3 uu___4)) in
        FStar_List.append uu___ uu___1
    | FStar_Syntax_Syntax.Tm_ascribed (t1, asc, uu___) ->
        let uu___1 = unbound_variables t1 in
        let uu___2 =
          let uu___3 =
            match FStar_Pervasives_Native.fst asc with
            | FStar_Util.Inl t2 -> unbound_variables t2
            | FStar_Util.Inr c2 -> unbound_variables_comp c2 in
          let uu___4 =
            match FStar_Pervasives_Native.snd asc with
            | FStar_Pervasives_Native.None -> []
            | FStar_Pervasives_Native.Some tac -> unbound_variables tac in
          FStar_List.append uu___3 uu___4 in
        FStar_List.append uu___1 uu___2
    | FStar_Syntax_Syntax.Tm_let ((false, lb::[]), t1) ->
        let uu___ = unbound_variables lb.FStar_Syntax_Syntax.lbtyp in
        let uu___1 =
          let uu___2 = unbound_variables lb.FStar_Syntax_Syntax.lbdef in
          let uu___3 =
            match lb.FStar_Syntax_Syntax.lbname with
            | FStar_Util.Inr uu___4 -> unbound_variables t1
            | FStar_Util.Inl bv ->
                let uu___4 =
                  FStar_Syntax_Subst.open_term
                    [(bv, FStar_Pervasives_Native.None)] t1 in
                (match uu___4 with | (uu___5, t2) -> unbound_variables t2) in
          FStar_List.append uu___2 uu___3 in
        FStar_List.append uu___ uu___1
    | FStar_Syntax_Syntax.Tm_let ((uu___, lbs), t1) ->
        let uu___1 = FStar_Syntax_Subst.open_let_rec lbs t1 in
        (match uu___1 with
         | (lbs1, t2) ->
             let uu___2 = unbound_variables t2 in
             let uu___3 =
               FStar_List.collect
                 (fun lb ->
                    let uu___4 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbtyp in
                    let uu___5 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbdef in
                    FStar_List.append uu___4 uu___5) lbs1 in
             FStar_List.append uu___2 uu___3)
    | FStar_Syntax_Syntax.Tm_quoted (tm1, qi) ->
        (match qi.FStar_Syntax_Syntax.qkind with
         | FStar_Syntax_Syntax.Quote_static -> []
         | FStar_Syntax_Syntax.Quote_dynamic -> unbound_variables tm1)
    | FStar_Syntax_Syntax.Tm_meta (t1, m) ->
        let uu___ = unbound_variables t1 in
        let uu___1 =
          match m with
          | FStar_Syntax_Syntax.Meta_pattern (uu___2, args) ->
              FStar_List.collect
                (FStar_List.collect
                   (fun uu___3 ->
                      match uu___3 with | (a, uu___4) -> unbound_variables a))
                args
          | FStar_Syntax_Syntax.Meta_monadic_lift (uu___2, uu___3, t') ->
              unbound_variables t'
          | FStar_Syntax_Syntax.Meta_monadic (uu___2, t') ->
              unbound_variables t'
          | FStar_Syntax_Syntax.Meta_labeled uu___2 -> []
          | FStar_Syntax_Syntax.Meta_desugared uu___2 -> []
          | FStar_Syntax_Syntax.Meta_named uu___2 -> [] in
        FStar_List.append uu___ uu___1
and (unbound_variables_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.bv Prims.list)
  =
  fun c ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.GTotal (t, uu___) -> unbound_variables t
    | FStar_Syntax_Syntax.Total (t, uu___) -> unbound_variables t
    | FStar_Syntax_Syntax.Comp ct ->
        let uu___ = unbound_variables ct.FStar_Syntax_Syntax.result_typ in
        let uu___1 =
          FStar_List.collect
            (fun uu___2 ->
               match uu___2 with | (a, uu___3) -> unbound_variables a)
            ct.FStar_Syntax_Syntax.effect_args in
        FStar_List.append uu___ uu___1
let (extract_attr' :
  FStar_Ident.lid ->
    FStar_Syntax_Syntax.term Prims.list ->
      (FStar_Syntax_Syntax.term Prims.list * FStar_Syntax_Syntax.args)
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
                   let uu___2 = FStar_Syntax_Subst.compress head in
                   uu___2.FStar_Syntax_Syntax.n in
                 (match uu___1 with
                  | FStar_Syntax_Syntax.Tm_fvar fv when
                      FStar_Syntax_Syntax.fv_eq_lid fv attr_lid ->
                      let attrs' = FStar_List.rev_acc acc t in
                      FStar_Pervasives_Native.Some (attrs', args)
                  | uu___2 -> aux (h :: acc) t)) in
      aux [] attrs
let (extract_attr :
  FStar_Ident.lid ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.args)
        FStar_Pervasives_Native.option)
  =
  fun attr_lid ->
    fun se ->
      let uu___ = extract_attr' attr_lid se.FStar_Syntax_Syntax.sigattrs in
      match uu___ with
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (attrs', t) ->
          FStar_Pervasives_Native.Some
            ((let uu___1 = se in
              {
                FStar_Syntax_Syntax.sigel =
                  (uu___1.FStar_Syntax_Syntax.sigel);
                FStar_Syntax_Syntax.sigrng =
                  (uu___1.FStar_Syntax_Syntax.sigrng);
                FStar_Syntax_Syntax.sigquals =
                  (uu___1.FStar_Syntax_Syntax.sigquals);
                FStar_Syntax_Syntax.sigmeta =
                  (uu___1.FStar_Syntax_Syntax.sigmeta);
                FStar_Syntax_Syntax.sigattrs = attrs';
                FStar_Syntax_Syntax.sigopts =
                  (uu___1.FStar_Syntax_Syntax.sigopts)
              }), t)
let (is_smt_lemma : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu___ =
      let uu___1 = FStar_Syntax_Subst.compress t in
      uu___1.FStar_Syntax_Syntax.n in
    match uu___ with
    | FStar_Syntax_Syntax.Tm_arrow (uu___1, c) ->
        (match c.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Comp ct when
             FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
               FStar_Parser_Const.effect_Lemma_lid
             ->
             (match ct.FStar_Syntax_Syntax.effect_args with
              | _req::_ens::(pats, uu___2)::uu___3 ->
                  let pats' = unmeta pats in
                  let uu___4 = head_and_args pats' in
                  (match uu___4 with
                   | (head, uu___5) ->
                       let uu___6 =
                         let uu___7 = un_uinst head in
                         uu___7.FStar_Syntax_Syntax.n in
                       (match uu___6 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.cons_lid
                        | uu___7 -> false))
              | uu___2 -> false)
         | uu___2 -> false)
    | uu___1 -> false
let rec (list_elements :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term Prims.list FStar_Pervasives_Native.option)
  =
  fun e ->
    let uu___ = let uu___1 = unmeta e in head_and_args uu___1 in
    match uu___ with
    | (head, args) ->
        let uu___1 =
          let uu___2 =
            let uu___3 = un_uinst head in uu___3.FStar_Syntax_Syntax.n in
          (uu___2, args) in
        (match uu___1 with
         | (FStar_Syntax_Syntax.Tm_fvar fv, uu___2) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
             FStar_Pervasives_Native.Some []
         | (FStar_Syntax_Syntax.Tm_fvar fv,
            uu___2::(hd, uu___3)::(tl, uu___4)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid ->
             let uu___5 =
               let uu___6 =
                 let uu___7 = list_elements tl in FStar_Util.must uu___7 in
               hd :: uu___6 in
             FStar_Pervasives_Native.Some uu___5
         | uu___2 -> FStar_Pervasives_Native.None)
let (unthunk : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t ->
    let uu___ =
      let uu___1 = FStar_Syntax_Subst.compress t in
      uu___1.FStar_Syntax_Syntax.n in
    match uu___ with
    | FStar_Syntax_Syntax.Tm_abs (b::[], e, uu___1) ->
        let uu___2 = FStar_Syntax_Subst.open_term [b] e in
        (match uu___2 with
         | (bs, e1) ->
             let b1 = FStar_List.hd bs in
             let uu___3 = is_free_in (FStar_Pervasives_Native.fst b1) e1 in
             if uu___3
             then
               let uu___4 =
                 let uu___5 = FStar_Syntax_Syntax.as_arg exp_unit in [uu___5] in
               mk_app t uu___4
             else e1)
    | uu___1 ->
        let uu___2 =
          let uu___3 = FStar_Syntax_Syntax.as_arg exp_unit in [uu___3] in
        mk_app t uu___2
let (unthunk_lemma_post :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) = fun t -> unthunk t
let (smt_lemma_as_forall :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.universe Prims.list)
      -> FStar_Syntax_Syntax.term)
  =
  fun t ->
    fun universe_of_binders ->
      let list_elements1 e =
        let uu___ = list_elements e in
        match uu___ with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None ->
            (FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
               (FStar_Errors.Warning_NonListLiteralSMTPattern,
                 "SMT pattern is not a list literal; ignoring the pattern");
             []) in
      let one_pat p =
        let uu___ =
          let uu___1 = unmeta p in FStar_All.pipe_right uu___1 head_and_args in
        match uu___ with
        | (head, args) ->
            let uu___1 =
              let uu___2 =
                let uu___3 = un_uinst head in uu___3.FStar_Syntax_Syntax.n in
              (uu___2, args) in
            (match uu___1 with
             | (FStar_Syntax_Syntax.Tm_fvar fv, (uu___2, uu___3)::arg::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> arg
             | uu___2 ->
                 let uu___3 =
                   let uu___4 =
                     let uu___5 = tts p in
                     FStar_Util.format1
                       "Not an atomic SMT pattern: %s; patterns on lemmas must be a list of simple SMTPat's or a single SMTPatOr containing a list of lists of patterns"
                       uu___5 in
                   (FStar_Errors.Error_IllSMTPat, uu___4) in
                 FStar_Errors.raise_error uu___3 p.FStar_Syntax_Syntax.pos) in
      let lemma_pats p =
        let elts = list_elements1 p in
        let smt_pat_or t1 =
          let uu___ =
            let uu___1 = unmeta t1 in
            FStar_All.pipe_right uu___1 head_and_args in
          match uu___ with
          | (head, args) ->
              let uu___1 =
                let uu___2 =
                  let uu___3 = un_uinst head in uu___3.FStar_Syntax_Syntax.n in
                (uu___2, args) in
              (match uu___1 with
               | (FStar_Syntax_Syntax.Tm_fvar fv, (e, uu___2)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu___2 -> FStar_Pervasives_Native.None) in
        match elts with
        | t1::[] ->
            let uu___ = smt_pat_or t1 in
            (match uu___ with
             | FStar_Pervasives_Native.Some e ->
                 let uu___1 = list_elements1 e in
                 FStar_All.pipe_right uu___1
                   (FStar_List.map
                      (fun branch1 ->
                         let uu___2 = list_elements1 branch1 in
                         FStar_All.pipe_right uu___2 (FStar_List.map one_pat)))
             | uu___1 ->
                 let uu___2 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat) in
                 [uu___2])
        | uu___ ->
            let uu___1 = FStar_All.pipe_right elts (FStar_List.map one_pat) in
            [uu___1] in
      let uu___ =
        let uu___1 =
          let uu___2 = FStar_Syntax_Subst.compress t in
          uu___2.FStar_Syntax_Syntax.n in
        match uu___1 with
        | FStar_Syntax_Syntax.Tm_arrow (binders, c) ->
            let uu___2 = FStar_Syntax_Subst.open_comp binders c in
            (match uu___2 with
             | (binders1, c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu___3;
                        FStar_Syntax_Syntax.effect_name = uu___4;
                        FStar_Syntax_Syntax.result_typ = uu___5;
                        FStar_Syntax_Syntax.effect_args =
                          (pre, uu___6)::(post, uu___7)::(pats, uu___8)::[];
                        FStar_Syntax_Syntax.flags = uu___9;_}
                      ->
                      let uu___10 = lemma_pats pats in
                      (binders1, pre, post, uu___10)
                  | uu___3 -> failwith "impos"))
        | uu___2 -> failwith "Impos" in
      match uu___ with
      | (binders, pre, post, patterns) ->
          let post1 = unthunk_lemma_post post in
          let body =
            let uu___1 =
              let uu___2 =
                let uu___3 = mk_imp pre post1 in
                let uu___4 =
                  let uu___5 =
                    let uu___6 = FStar_Syntax_Syntax.binders_to_names binders in
                    (uu___6, patterns) in
                  FStar_Syntax_Syntax.Meta_pattern uu___5 in
                (uu___3, uu___4) in
              FStar_Syntax_Syntax.Tm_meta uu___2 in
            FStar_Syntax_Syntax.mk uu___1 t.FStar_Syntax_Syntax.pos in
          let quant =
            let uu___1 = universe_of_binders binders in
            FStar_List.fold_right2
              (fun b ->
                 fun u ->
                   fun out -> mk_forall u (FStar_Pervasives_Native.fst b) out)
              binders uu___1 body in
          quant
let (eff_decl_of_new_effect :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.eff_decl) =
  fun se ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne -> ne
    | uu___ -> failwith "eff_decl_of_new_effect: not a Sig_new_effect"
let (is_layered : FStar_Syntax_Syntax.eff_decl -> Prims.bool) =
  fun ed ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Layered_eff uu___ -> true
    | uu___ -> false
let (is_dm4f : FStar_Syntax_Syntax.eff_decl -> Prims.bool) =
  fun ed ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.DM4F_eff uu___ -> true
    | uu___ -> false
let (apply_wp_eff_combinators :
  (FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme) ->
    FStar_Syntax_Syntax.wp_eff_combinators ->
      FStar_Syntax_Syntax.wp_eff_combinators)
  =
  fun f ->
    fun combs ->
      let uu___ = f combs.FStar_Syntax_Syntax.ret_wp in
      let uu___1 = f combs.FStar_Syntax_Syntax.bind_wp in
      let uu___2 = f combs.FStar_Syntax_Syntax.stronger in
      let uu___3 = f combs.FStar_Syntax_Syntax.if_then_else in
      let uu___4 = f combs.FStar_Syntax_Syntax.ite_wp in
      let uu___5 = f combs.FStar_Syntax_Syntax.close_wp in
      let uu___6 = f combs.FStar_Syntax_Syntax.trivial in
      let uu___7 = FStar_Util.map_option f combs.FStar_Syntax_Syntax.repr in
      let uu___8 =
        FStar_Util.map_option f combs.FStar_Syntax_Syntax.return_repr in
      let uu___9 =
        FStar_Util.map_option f combs.FStar_Syntax_Syntax.bind_repr in
      {
        FStar_Syntax_Syntax.ret_wp = uu___;
        FStar_Syntax_Syntax.bind_wp = uu___1;
        FStar_Syntax_Syntax.stronger = uu___2;
        FStar_Syntax_Syntax.if_then_else = uu___3;
        FStar_Syntax_Syntax.ite_wp = uu___4;
        FStar_Syntax_Syntax.close_wp = uu___5;
        FStar_Syntax_Syntax.trivial = uu___6;
        FStar_Syntax_Syntax.repr = uu___7;
        FStar_Syntax_Syntax.return_repr = uu___8;
        FStar_Syntax_Syntax.bind_repr = uu___9
      }
let (apply_layered_eff_combinators :
  (FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme) ->
    FStar_Syntax_Syntax.layered_eff_combinators ->
      FStar_Syntax_Syntax.layered_eff_combinators)
  =
  fun f ->
    fun combs ->
      let map_tuple uu___ =
        match uu___ with
        | (ts1, ts2) ->
            let uu___1 = f ts1 in let uu___2 = f ts2 in (uu___1, uu___2) in
      let uu___ = map_tuple combs.FStar_Syntax_Syntax.l_repr in
      let uu___1 = map_tuple combs.FStar_Syntax_Syntax.l_return in
      let uu___2 = map_tuple combs.FStar_Syntax_Syntax.l_bind in
      let uu___3 = map_tuple combs.FStar_Syntax_Syntax.l_subcomp in
      let uu___4 = map_tuple combs.FStar_Syntax_Syntax.l_if_then_else in
      {
        FStar_Syntax_Syntax.l_repr = uu___;
        FStar_Syntax_Syntax.l_return = uu___1;
        FStar_Syntax_Syntax.l_bind = uu___2;
        FStar_Syntax_Syntax.l_subcomp = uu___3;
        FStar_Syntax_Syntax.l_if_then_else = uu___4
      }
let (apply_eff_combinators :
  (FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme) ->
    FStar_Syntax_Syntax.eff_combinators ->
      FStar_Syntax_Syntax.eff_combinators)
  =
  fun f ->
    fun combs ->
      match combs with
      | FStar_Syntax_Syntax.Primitive_eff combs1 ->
          let uu___ = apply_wp_eff_combinators f combs1 in
          FStar_Syntax_Syntax.Primitive_eff uu___
      | FStar_Syntax_Syntax.DM4F_eff combs1 ->
          let uu___ = apply_wp_eff_combinators f combs1 in
          FStar_Syntax_Syntax.DM4F_eff uu___
      | FStar_Syntax_Syntax.Layered_eff combs1 ->
          let uu___ = apply_layered_eff_combinators f combs1 in
          FStar_Syntax_Syntax.Layered_eff uu___
let (get_wp_close_combinator :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Primitive_eff combs ->
        FStar_Pervasives_Native.Some (combs.FStar_Syntax_Syntax.close_wp)
    | FStar_Syntax_Syntax.DM4F_eff combs ->
        FStar_Pervasives_Native.Some (combs.FStar_Syntax_Syntax.close_wp)
    | uu___ -> FStar_Pervasives_Native.None
let (get_eff_repr :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Primitive_eff combs ->
        combs.FStar_Syntax_Syntax.repr
    | FStar_Syntax_Syntax.DM4F_eff combs -> combs.FStar_Syntax_Syntax.repr
    | FStar_Syntax_Syntax.Layered_eff combs ->
        let uu___ =
          FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_repr
            FStar_Pervasives_Native.fst in
        FStar_All.pipe_right uu___
          (fun uu___1 -> FStar_Pervasives_Native.Some uu___1)
let (get_bind_vc_combinator :
  FStar_Syntax_Syntax.eff_decl -> FStar_Syntax_Syntax.tscheme) =
  fun ed ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Primitive_eff combs ->
        combs.FStar_Syntax_Syntax.bind_wp
    | FStar_Syntax_Syntax.DM4F_eff combs -> combs.FStar_Syntax_Syntax.bind_wp
    | FStar_Syntax_Syntax.Layered_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_bind
          FStar_Pervasives_Native.snd
let (get_return_vc_combinator :
  FStar_Syntax_Syntax.eff_decl -> FStar_Syntax_Syntax.tscheme) =
  fun ed ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Primitive_eff combs ->
        combs.FStar_Syntax_Syntax.ret_wp
    | FStar_Syntax_Syntax.DM4F_eff combs -> combs.FStar_Syntax_Syntax.ret_wp
    | FStar_Syntax_Syntax.Layered_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_return
          FStar_Pervasives_Native.snd
let (get_bind_repr :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Primitive_eff combs ->
        combs.FStar_Syntax_Syntax.bind_repr
    | FStar_Syntax_Syntax.DM4F_eff combs ->
        combs.FStar_Syntax_Syntax.bind_repr
    | FStar_Syntax_Syntax.Layered_eff combs ->
        let uu___ =
          FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_bind
            FStar_Pervasives_Native.fst in
        FStar_All.pipe_right uu___
          (fun uu___1 -> FStar_Pervasives_Native.Some uu___1)
let (get_return_repr :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Primitive_eff combs ->
        combs.FStar_Syntax_Syntax.return_repr
    | FStar_Syntax_Syntax.DM4F_eff combs ->
        combs.FStar_Syntax_Syntax.return_repr
    | FStar_Syntax_Syntax.Layered_eff combs ->
        let uu___ =
          FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_return
            FStar_Pervasives_Native.fst in
        FStar_All.pipe_right uu___
          (fun uu___1 -> FStar_Pervasives_Native.Some uu___1)
let (get_wp_trivial_combinator :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Primitive_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.trivial
          (fun uu___ -> FStar_Pervasives_Native.Some uu___)
    | FStar_Syntax_Syntax.DM4F_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.trivial
          (fun uu___ -> FStar_Pervasives_Native.Some uu___)
    | uu___ -> FStar_Pervasives_Native.None
let (get_layered_if_then_else_combinator :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Layered_eff combs ->
        let uu___ =
          FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_if_then_else
            FStar_Pervasives_Native.fst in
        FStar_All.pipe_right uu___
          (fun uu___1 -> FStar_Pervasives_Native.Some uu___1)
    | uu___ -> FStar_Pervasives_Native.None
let (get_wp_if_then_else_combinator :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Primitive_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.if_then_else
          (fun uu___ -> FStar_Pervasives_Native.Some uu___)
    | FStar_Syntax_Syntax.DM4F_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.if_then_else
          (fun uu___ -> FStar_Pervasives_Native.Some uu___)
    | uu___ -> FStar_Pervasives_Native.None
let (get_wp_ite_combinator :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Primitive_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.ite_wp
          (fun uu___ -> FStar_Pervasives_Native.Some uu___)
    | FStar_Syntax_Syntax.DM4F_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.ite_wp
          (fun uu___ -> FStar_Pervasives_Native.Some uu___)
    | uu___ -> FStar_Pervasives_Native.None
let (get_stronger_vc_combinator :
  FStar_Syntax_Syntax.eff_decl -> FStar_Syntax_Syntax.tscheme) =
  fun ed ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Primitive_eff combs ->
        combs.FStar_Syntax_Syntax.stronger
    | FStar_Syntax_Syntax.DM4F_eff combs ->
        combs.FStar_Syntax_Syntax.stronger
    | FStar_Syntax_Syntax.Layered_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_subcomp
          FStar_Pervasives_Native.snd
let (get_stronger_repr :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Primitive_eff uu___ -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.DM4F_eff uu___ -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Layered_eff combs ->
        let uu___ =
          FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_subcomp
            FStar_Pervasives_Native.fst in
        FStar_All.pipe_right uu___
          (fun uu___1 -> FStar_Pervasives_Native.Some uu___1)