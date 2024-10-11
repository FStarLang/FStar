open Prims
let (sli : FStarC_Ident.lident -> Prims.string) =
  fun l ->
    let uu___ = FStarC_Options.print_real_names () in
    if uu___
    then FStarC_Ident.string_of_lid l
    else
      (let uu___2 = FStarC_Ident.ident_of_lid l in
       FStarC_Ident.string_of_id uu___2)
let (lid_to_string : FStarC_Ident.lid -> Prims.string) = fun l -> sli l
let (fv_to_string : FStarC_Syntax_Syntax.fv -> Prims.string) =
  fun fv ->
    lid_to_string (fv.FStarC_Syntax_Syntax.fv_name).FStarC_Syntax_Syntax.v
let (bv_to_string : FStarC_Syntax_Syntax.bv -> Prims.string) =
  fun bv ->
    let uu___ = FStarC_Ident.string_of_id bv.FStarC_Syntax_Syntax.ppname in
    let uu___1 =
      let uu___2 =
        FStarC_Compiler_Util.string_of_int bv.FStarC_Syntax_Syntax.index in
      Prims.strcat "#" uu___2 in
    Prims.strcat uu___ uu___1
let (nm_to_string : FStarC_Syntax_Syntax.bv -> Prims.string) =
  fun bv ->
    let uu___ = FStarC_Options.print_real_names () in
    if uu___
    then bv_to_string bv
    else FStarC_Ident.string_of_id bv.FStarC_Syntax_Syntax.ppname
let (db_to_string : FStarC_Syntax_Syntax.bv -> Prims.string) =
  fun bv ->
    let uu___ = FStarC_Ident.string_of_id bv.FStarC_Syntax_Syntax.ppname in
    let uu___1 =
      let uu___2 =
        FStarC_Compiler_Util.string_of_int bv.FStarC_Syntax_Syntax.index in
      Prims.strcat "@" uu___2 in
    Prims.strcat uu___ uu___1
let (filter_imp :
  FStarC_Syntax_Syntax.binder_qualifier FStar_Pervasives_Native.option ->
    Prims.bool)
  =
  fun aq ->
    match aq with
    | FStar_Pervasives_Native.Some (FStarC_Syntax_Syntax.Meta t) when
        FStarC_Syntax_Util.is_fvar FStarC_Parser_Const.tcresolve_lid t ->
        true
    | FStar_Pervasives_Native.Some (FStarC_Syntax_Syntax.Implicit uu___) ->
        false
    | FStar_Pervasives_Native.Some (FStarC_Syntax_Syntax.Meta uu___) -> false
    | uu___ -> true
let filter_imp_args :
  'uuuuu .
    ('uuuuu * FStarC_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list ->
      ('uuuuu * FStarC_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list
  =
  fun args ->
    FStarC_Compiler_List.filter
      (fun uu___ ->
         match uu___ with
         | (uu___1, FStar_Pervasives_Native.None) -> true
         | (uu___1, FStar_Pervasives_Native.Some a) ->
             Prims.op_Negation a.FStarC_Syntax_Syntax.aqual_implicit) args
let (filter_imp_binders :
  FStarC_Syntax_Syntax.binder Prims.list ->
    FStarC_Syntax_Syntax.binder Prims.list)
  =
  fun bs ->
    FStarC_Compiler_List.filter
      (fun b -> filter_imp b.FStarC_Syntax_Syntax.binder_qual) bs
let (const_to_string : FStarC_Const.sconst -> Prims.string) =
  FStarC_Parser_Const.const_to_string
let (lbname_to_string :
  (FStarC_Syntax_Syntax.bv, FStarC_Syntax_Syntax.fv) FStar_Pervasives.either
    -> Prims.string)
  =
  fun uu___ ->
    match uu___ with
    | FStar_Pervasives.Inl l -> bv_to_string l
    | FStar_Pervasives.Inr l ->
        lid_to_string (l.FStarC_Syntax_Syntax.fv_name).FStarC_Syntax_Syntax.v
let (uvar_to_string : FStarC_Syntax_Syntax.uvar -> Prims.string) =
  fun u ->
    let uu___ = FStarC_Options.hide_uvar_nums () in
    if uu___
    then "?"
    else
      (let uu___2 =
         let uu___3 = FStarC_Syntax_Unionfind.uvar_id u in
         FStarC_Compiler_Util.string_of_int uu___3 in
       Prims.strcat "?" uu___2)
let (version_to_string : FStarC_Syntax_Syntax.version -> Prims.string) =
  fun v ->
    let uu___ =
      FStarC_Compiler_Util.string_of_int v.FStarC_Syntax_Syntax.major in
    let uu___1 =
      FStarC_Compiler_Util.string_of_int v.FStarC_Syntax_Syntax.minor in
    FStarC_Compiler_Util.format2 "%s.%s" uu___ uu___1
let (univ_uvar_to_string :
  (FStarC_Syntax_Syntax.universe FStar_Pervasives_Native.option
    FStarC_Unionfind.p_uvar * FStarC_Syntax_Syntax.version *
    FStarC_Compiler_Range_Type.range) -> Prims.string)
  =
  fun u ->
    let uu___ = FStarC_Options.hide_uvar_nums () in
    if uu___
    then "?"
    else
      (let uu___2 =
         let uu___3 =
           let uu___4 = FStarC_Syntax_Unionfind.univ_uvar_id u in
           FStarC_Compiler_Util.string_of_int uu___4 in
         let uu___4 =
           let uu___5 =
             match u with | (uu___6, u1, uu___7) -> version_to_string u1 in
           Prims.strcat ":" uu___5 in
         Prims.strcat uu___3 uu___4 in
       Prims.strcat "?" uu___2)
let rec (int_of_univ :
  Prims.int ->
    FStarC_Syntax_Syntax.universe ->
      (Prims.int * FStarC_Syntax_Syntax.universe
        FStar_Pervasives_Native.option))
  =
  fun n ->
    fun u ->
      let uu___ = FStarC_Syntax_Subst.compress_univ u in
      match uu___ with
      | FStarC_Syntax_Syntax.U_zero -> (n, FStar_Pervasives_Native.None)
      | FStarC_Syntax_Syntax.U_succ u1 -> int_of_univ (n + Prims.int_one) u1
      | uu___1 -> (n, (FStar_Pervasives_Native.Some u))
let rec (univ_to_string : FStarC_Syntax_Syntax.universe -> Prims.string) =
  fun u ->
    FStarC_Errors.with_ctx "While printing universe"
      (fun uu___ ->
         let uu___1 = FStarC_Syntax_Subst.compress_univ u in
         match uu___1 with
         | FStarC_Syntax_Syntax.U_unif u1 ->
             let uu___2 = univ_uvar_to_string u1 in
             Prims.strcat "U_unif " uu___2
         | FStarC_Syntax_Syntax.U_name x ->
             let uu___2 = FStarC_Ident.string_of_id x in
             Prims.strcat "U_name " uu___2
         | FStarC_Syntax_Syntax.U_bvar x ->
             let uu___2 = FStarC_Compiler_Util.string_of_int x in
             Prims.strcat "@" uu___2
         | FStarC_Syntax_Syntax.U_zero -> "0"
         | FStarC_Syntax_Syntax.U_succ u1 ->
             let uu___2 = int_of_univ Prims.int_one u1 in
             (match uu___2 with
              | (n, FStar_Pervasives_Native.None) ->
                  FStarC_Compiler_Util.string_of_int n
              | (n, FStar_Pervasives_Native.Some u2) ->
                  let uu___3 = univ_to_string u2 in
                  let uu___4 = FStarC_Compiler_Util.string_of_int n in
                  FStarC_Compiler_Util.format2 "(%s + %s)" uu___3 uu___4)
         | FStarC_Syntax_Syntax.U_max us ->
             let uu___2 =
               let uu___3 = FStarC_Compiler_List.map univ_to_string us in
               FStarC_Compiler_String.concat ", " uu___3 in
             FStarC_Compiler_Util.format1 "(max %s)" uu___2
         | FStarC_Syntax_Syntax.U_unknown -> "unknown")
let (univs_to_string :
  FStarC_Syntax_Syntax.universe Prims.list -> Prims.string) =
  fun us ->
    let uu___ = FStarC_Compiler_List.map univ_to_string us in
    FStarC_Compiler_String.concat ", " uu___
let (univ_names_to_string : FStarC_Ident.ident Prims.list -> Prims.string) =
  fun us ->
    let uu___ =
      FStarC_Compiler_List.map (fun x -> FStarC_Ident.string_of_id x) us in
    FStarC_Compiler_String.concat ", " uu___
let (qual_to_string : FStarC_Syntax_Syntax.qualifier -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | FStarC_Syntax_Syntax.Assumption -> "assume"
    | FStarC_Syntax_Syntax.InternalAssumption -> "internal_assume"
    | FStarC_Syntax_Syntax.New -> "new"
    | FStarC_Syntax_Syntax.Private -> "private"
    | FStarC_Syntax_Syntax.Unfold_for_unification_and_vcgen -> "unfold"
    | FStarC_Syntax_Syntax.Inline_for_extraction -> "inline_for_extraction"
    | FStarC_Syntax_Syntax.NoExtract -> "noextract"
    | FStarC_Syntax_Syntax.Visible_default -> "visible"
    | FStarC_Syntax_Syntax.Irreducible -> "irreducible"
    | FStarC_Syntax_Syntax.Noeq -> "noeq"
    | FStarC_Syntax_Syntax.Unopteq -> "unopteq"
    | FStarC_Syntax_Syntax.Logic -> "logic"
    | FStarC_Syntax_Syntax.TotalEffect -> "total"
    | FStarC_Syntax_Syntax.Discriminator l ->
        let uu___1 = lid_to_string l in
        FStarC_Compiler_Util.format1 "(Discriminator %s)" uu___1
    | FStarC_Syntax_Syntax.Projector (l, x) ->
        let uu___1 = lid_to_string l in
        let uu___2 = FStarC_Ident.string_of_id x in
        FStarC_Compiler_Util.format2 "(Projector %s %s)" uu___1 uu___2
    | FStarC_Syntax_Syntax.RecordType (ns, fns) ->
        let uu___1 =
          let uu___2 = FStarC_Ident.path_of_ns ns in
          FStarC_Ident.text_of_path uu___2 in
        let uu___2 =
          let uu___3 = FStarC_Compiler_List.map FStarC_Ident.string_of_id fns in
          FStarC_Compiler_String.concat ", " uu___3 in
        FStarC_Compiler_Util.format2 "(RecordType %s %s)" uu___1 uu___2
    | FStarC_Syntax_Syntax.RecordConstructor (ns, fns) ->
        let uu___1 =
          let uu___2 = FStarC_Ident.path_of_ns ns in
          FStarC_Ident.text_of_path uu___2 in
        let uu___2 =
          let uu___3 = FStarC_Compiler_List.map FStarC_Ident.string_of_id fns in
          FStarC_Compiler_String.concat ", " uu___3 in
        FStarC_Compiler_Util.format2 "(RecordConstructor %s %s)" uu___1
          uu___2
    | FStarC_Syntax_Syntax.Action eff_lid ->
        let uu___1 = lid_to_string eff_lid in
        FStarC_Compiler_Util.format1 "(Action %s)" uu___1
    | FStarC_Syntax_Syntax.ExceptionConstructor -> "ExceptionConstructor"
    | FStarC_Syntax_Syntax.HasMaskedEffect -> "HasMaskedEffect"
    | FStarC_Syntax_Syntax.Effect -> "Effect"
    | FStarC_Syntax_Syntax.Reifiable -> "reify"
    | FStarC_Syntax_Syntax.Reflectable l ->
        let uu___1 = FStarC_Ident.string_of_lid l in
        FStarC_Compiler_Util.format1 "(reflect %s)" uu___1
    | FStarC_Syntax_Syntax.OnlyName -> "OnlyName"
let (quals_to_string :
  FStarC_Syntax_Syntax.qualifier Prims.list -> Prims.string) =
  fun quals ->
    match quals with
    | [] -> ""
    | uu___ ->
        let uu___1 = FStarC_Compiler_List.map qual_to_string quals in
        FStarC_Compiler_String.concat " " uu___1
let (quals_to_string' :
  FStarC_Syntax_Syntax.qualifier Prims.list -> Prims.string) =
  fun quals ->
    match quals with
    | [] -> ""
    | uu___ -> let uu___1 = quals_to_string quals in Prims.strcat uu___1 " "
let (paren : Prims.string -> Prims.string) =
  fun s -> Prims.strcat "(" (Prims.strcat s ")")
let rec (term_to_string : FStarC_Syntax_Syntax.term -> Prims.string) =
  fun x ->
    FStarC_Errors.with_ctx "While ugly-printing a term"
      (fun uu___ ->
         let x1 = FStarC_Syntax_Subst.compress x in
         let x2 =
           let uu___1 = FStarC_Options.print_implicits () in
           if uu___1 then x1 else FStarC_Syntax_Util.unmeta x1 in
         match x2.FStarC_Syntax_Syntax.n with
         | FStarC_Syntax_Syntax.Tm_delayed uu___1 -> failwith "impossible"
         | FStarC_Syntax_Syntax.Tm_app
             { FStarC_Syntax_Syntax.hd = uu___1;
               FStarC_Syntax_Syntax.args = [];_}
             -> failwith "Empty args!"
         | FStarC_Syntax_Syntax.Tm_lazy
             { FStarC_Syntax_Syntax.blob = b;
               FStarC_Syntax_Syntax.lkind =
                 FStarC_Syntax_Syntax.Lazy_embedding (uu___1, thunk);
               FStarC_Syntax_Syntax.ltyp = uu___2;
               FStarC_Syntax_Syntax.rng = uu___3;_}
             ->
             let uu___4 =
               let uu___5 =
                 let uu___6 = FStarC_Thunk.force thunk in
                 term_to_string uu___6 in
               Prims.strcat uu___5 "]" in
             Prims.strcat "[LAZYEMB:" uu___4
         | FStarC_Syntax_Syntax.Tm_lazy i ->
             let uu___1 =
               let uu___2 =
                 let uu___3 =
                   let uu___4 =
                     let uu___5 =
                       FStarC_Compiler_Effect.op_Bang
                         FStarC_Syntax_Syntax.lazy_chooser in
                     FStarC_Compiler_Util.must uu___5 in
                   uu___4 i.FStarC_Syntax_Syntax.lkind i in
                 term_to_string uu___3 in
               Prims.strcat uu___2 "]" in
             Prims.strcat "[lazy:" uu___1
         | FStarC_Syntax_Syntax.Tm_quoted (tm, qi) ->
             (match qi.FStarC_Syntax_Syntax.qkind with
              | FStarC_Syntax_Syntax.Quote_static ->
                  let uu___1 = term_to_string tm in
                  let uu___2 =
                    (FStarC_Common.string_of_list ()) term_to_string
                      (FStar_Pervasives_Native.snd
                         qi.FStarC_Syntax_Syntax.antiquotations) in
                  FStarC_Compiler_Util.format2 "`(%s)%s" uu___1 uu___2
              | FStarC_Syntax_Syntax.Quote_dynamic ->
                  let uu___1 = term_to_string tm in
                  FStarC_Compiler_Util.format1 "quote (%s)" uu___1)
         | FStarC_Syntax_Syntax.Tm_meta
             { FStarC_Syntax_Syntax.tm2 = t;
               FStarC_Syntax_Syntax.meta = FStarC_Syntax_Syntax.Meta_pattern
                 (uu___1, ps);_}
             ->
             let pats =
               let uu___2 =
                 FStarC_Compiler_List.map
                   (fun args ->
                      let uu___3 =
                        FStarC_Compiler_List.map
                          (fun uu___4 ->
                             match uu___4 with
                             | (t1, uu___5) -> term_to_string t1) args in
                      FStarC_Compiler_String.concat "; " uu___3) ps in
               FStarC_Compiler_String.concat "\\/" uu___2 in
             let uu___2 = term_to_string t in
             FStarC_Compiler_Util.format2 "{:pattern %s} %s" pats uu___2
         | FStarC_Syntax_Syntax.Tm_meta
             { FStarC_Syntax_Syntax.tm2 = t;
               FStarC_Syntax_Syntax.meta = FStarC_Syntax_Syntax.Meta_monadic
                 (m, t');_}
             ->
             let uu___1 = sli m in
             let uu___2 = term_to_string t' in
             let uu___3 =
               FStarC_Class_Tagged.tag_of FStarC_Syntax_Syntax.tagged_term t in
             let uu___4 = term_to_string t in
             FStarC_Compiler_Util.format4 "(MetaMonadic-{%s %s} (%s) %s)"
               uu___1 uu___2 uu___3 uu___4
         | FStarC_Syntax_Syntax.Tm_meta
             { FStarC_Syntax_Syntax.tm2 = t;
               FStarC_Syntax_Syntax.meta =
                 FStarC_Syntax_Syntax.Meta_monadic_lift (m0, m1, t');_}
             ->
             let uu___1 = term_to_string t' in
             let uu___2 = sli m0 in
             let uu___3 = sli m1 in
             let uu___4 = term_to_string t in
             FStarC_Compiler_Util.format4
               "(MetaMonadicLift-{%s : %s -> %s} %s)" uu___1 uu___2 uu___3
               uu___4
         | FStarC_Syntax_Syntax.Tm_meta
             { FStarC_Syntax_Syntax.tm2 = t;
               FStarC_Syntax_Syntax.meta = FStarC_Syntax_Syntax.Meta_labeled
                 (l, r, b);_}
             ->
             let uu___1 = FStarC_Errors_Msg.rendermsg l in
             let uu___2 = FStarC_Compiler_Range_Ops.string_of_range r in
             let uu___3 = term_to_string t in
             FStarC_Compiler_Util.format3 "Meta_labeled(%s, %s){%s}" uu___1
               uu___2 uu___3
         | FStarC_Syntax_Syntax.Tm_meta
             { FStarC_Syntax_Syntax.tm2 = t;
               FStarC_Syntax_Syntax.meta = FStarC_Syntax_Syntax.Meta_named l;_}
             ->
             let uu___1 = lid_to_string l in
             let uu___2 =
               FStarC_Compiler_Range_Ops.string_of_range
                 t.FStarC_Syntax_Syntax.pos in
             let uu___3 = term_to_string t in
             FStarC_Compiler_Util.format3 "Meta_named(%s, %s){%s}" uu___1
               uu___2 uu___3
         | FStarC_Syntax_Syntax.Tm_meta
             { FStarC_Syntax_Syntax.tm2 = t;
               FStarC_Syntax_Syntax.meta =
                 FStarC_Syntax_Syntax.Meta_desugared uu___1;_}
             ->
             let uu___2 = term_to_string t in
             FStarC_Compiler_Util.format1 "Meta_desugared{%s}" uu___2
         | FStarC_Syntax_Syntax.Tm_bvar x3 ->
             let uu___1 = db_to_string x3 in
             let uu___2 =
               let uu___3 =
                 let uu___4 =
                   FStarC_Class_Tagged.tag_of
                     FStarC_Syntax_Syntax.tagged_term
                     x3.FStarC_Syntax_Syntax.sort in
                 Prims.strcat uu___4 ")" in
               Prims.strcat ":(" uu___3 in
             Prims.strcat uu___1 uu___2
         | FStarC_Syntax_Syntax.Tm_name x3 -> nm_to_string x3
         | FStarC_Syntax_Syntax.Tm_fvar f ->
             let pref =
               match f.FStarC_Syntax_Syntax.fv_qual with
               | FStar_Pervasives_Native.Some
                   (FStarC_Syntax_Syntax.Unresolved_projector uu___1) ->
                   "(Unresolved_projector)"
               | FStar_Pervasives_Native.Some
                   (FStarC_Syntax_Syntax.Unresolved_constructor uu___1) ->
                   "(Unresolved_constructor)"
               | uu___1 -> "" in
             let uu___1 = fv_to_string f in Prims.strcat pref uu___1
         | FStarC_Syntax_Syntax.Tm_uvar (u, ([], uu___1)) ->
             let uu___2 =
               (FStarC_Options.print_bound_var_types ()) &&
                 (FStarC_Options.print_effect_args ()) in
             if uu___2
             then ctx_uvar_to_string_aux true u
             else
               (let uu___4 =
                  let uu___5 =
                    FStarC_Syntax_Unionfind.uvar_id
                      u.FStarC_Syntax_Syntax.ctx_uvar_head in
                  FStarC_Compiler_Util.string_of_int uu___5 in
                Prims.strcat "?" uu___4)
         | FStarC_Syntax_Syntax.Tm_uvar (u, s) ->
             let uu___1 =
               (FStarC_Options.print_bound_var_types ()) &&
                 (FStarC_Options.print_effect_args ()) in
             if uu___1
             then
               let uu___2 = ctx_uvar_to_string_aux true u in
               let uu___3 =
                 let uu___4 =
                   FStarC_Compiler_List.map subst_to_string
                     (FStar_Pervasives_Native.fst s) in
                 FStarC_Compiler_String.concat "; " uu___4 in
               FStarC_Compiler_Util.format2 "(%s @ %s)" uu___2 uu___3
             else
               (let uu___3 =
                  let uu___4 =
                    FStarC_Syntax_Unionfind.uvar_id
                      u.FStarC_Syntax_Syntax.ctx_uvar_head in
                  FStarC_Compiler_Util.string_of_int uu___4 in
                Prims.strcat "?" uu___3)
         | FStarC_Syntax_Syntax.Tm_constant c -> const_to_string c
         | FStarC_Syntax_Syntax.Tm_type u ->
             let uu___1 = FStarC_Options.print_universes () in
             if uu___1
             then
               let uu___2 = univ_to_string u in
               FStarC_Compiler_Util.format1 "Type u#(%s)" uu___2
             else "Type"
         | FStarC_Syntax_Syntax.Tm_arrow
             { FStarC_Syntax_Syntax.bs1 = bs;
               FStarC_Syntax_Syntax.comp = c;_}
             ->
             let uu___1 = binders_to_string " -> " bs in
             let uu___2 = comp_to_string c in
             FStarC_Compiler_Util.format2 "(%s -> %s)" uu___1 uu___2
         | FStarC_Syntax_Syntax.Tm_abs
             { FStarC_Syntax_Syntax.bs = bs; FStarC_Syntax_Syntax.body = t2;
               FStarC_Syntax_Syntax.rc_opt = lc;_}
             ->
             (match lc with
              | FStar_Pervasives_Native.Some rc when
                  FStarC_Options.print_implicits () ->
                  let uu___1 = binders_to_string " " bs in
                  let uu___2 = term_to_string t2 in
                  let uu___3 =
                    FStarC_Ident.string_of_lid
                      rc.FStarC_Syntax_Syntax.residual_effect in
                  let uu___4 =
                    if
                      FStarC_Compiler_Option.isNone
                        rc.FStarC_Syntax_Syntax.residual_typ
                    then "None"
                    else
                      (let uu___6 =
                         FStarC_Compiler_Option.get
                           rc.FStarC_Syntax_Syntax.residual_typ in
                       term_to_string uu___6) in
                  FStarC_Compiler_Util.format4
                    "(fun %s -> (%s $$ (residual) %s %s))" uu___1 uu___2
                    uu___3 uu___4
              | uu___1 ->
                  let uu___2 = binders_to_string " " bs in
                  let uu___3 = term_to_string t2 in
                  FStarC_Compiler_Util.format2 "(fun %s -> %s)" uu___2 uu___3)
         | FStarC_Syntax_Syntax.Tm_refine
             { FStarC_Syntax_Syntax.b = xt; FStarC_Syntax_Syntax.phi = f;_}
             ->
             let uu___1 = bv_to_string xt in
             let uu___2 = term_to_string xt.FStarC_Syntax_Syntax.sort in
             let uu___3 = formula_to_string f in
             FStarC_Compiler_Util.format3 "(%s:%s{%s})" uu___1 uu___2 uu___3
         | FStarC_Syntax_Syntax.Tm_app
             { FStarC_Syntax_Syntax.hd = t;
               FStarC_Syntax_Syntax.args = args;_}
             ->
             let uu___1 = term_to_string t in
             let uu___2 = args_to_string args in
             FStarC_Compiler_Util.format2 "(%s %s)" uu___1 uu___2
         | FStarC_Syntax_Syntax.Tm_let
             { FStarC_Syntax_Syntax.lbs = lbs;
               FStarC_Syntax_Syntax.body1 = e;_}
             ->
             let uu___1 = lbs_to_string [] lbs in
             let uu___2 = term_to_string e in
             FStarC_Compiler_Util.format2 "%s\nin\n%s" uu___1 uu___2
         | FStarC_Syntax_Syntax.Tm_ascribed
             { FStarC_Syntax_Syntax.tm = e;
               FStarC_Syntax_Syntax.asc = (annot, topt, b);
               FStarC_Syntax_Syntax.eff_opt = eff_name;_}
             ->
             let annot1 =
               match annot with
               | FStar_Pervasives.Inl t ->
                   let uu___1 =
                     let uu___2 =
                       FStarC_Compiler_Util.map_opt eff_name
                         FStarC_Ident.string_of_lid in
                     FStarC_Compiler_Util.dflt "default" uu___2 in
                   let uu___2 = term_to_string t in
                   FStarC_Compiler_Util.format2 "[%s] %s" uu___1 uu___2
               | FStar_Pervasives.Inr c -> comp_to_string c in
             let topt1 =
               match topt with
               | FStar_Pervasives_Native.None -> ""
               | FStar_Pervasives_Native.Some t ->
                   let uu___1 = term_to_string t in
                   FStarC_Compiler_Util.format1 "by %s" uu___1 in
             let s = if b then "ascribed_eq" else "ascribed" in
             let uu___1 = term_to_string e in
             FStarC_Compiler_Util.format4 "(%s <%s: %s %s)" uu___1 s annot1
               topt1
         | FStarC_Syntax_Syntax.Tm_match
             { FStarC_Syntax_Syntax.scrutinee = head;
               FStarC_Syntax_Syntax.ret_opt = asc_opt;
               FStarC_Syntax_Syntax.brs = branches;
               FStarC_Syntax_Syntax.rc_opt1 = lc;_}
             ->
             let lc_str =
               match lc with
               | FStar_Pervasives_Native.Some lc1 when
                   FStarC_Options.print_implicits () ->
                   let uu___1 =
                     if
                       FStarC_Compiler_Option.isNone
                         lc1.FStarC_Syntax_Syntax.residual_typ
                     then "None"
                     else
                       (let uu___3 =
                          FStarC_Compiler_Option.get
                            lc1.FStarC_Syntax_Syntax.residual_typ in
                        term_to_string uu___3) in
                   FStarC_Compiler_Util.format1 " (residual_comp:%s)" uu___1
               | uu___1 -> "" in
             let uu___1 = term_to_string head in
             let uu___2 =
               match asc_opt with
               | FStar_Pervasives_Native.None -> ""
               | FStar_Pervasives_Native.Some (b, (asc, tacopt, use_eq)) ->
                   let s = if use_eq then "returns$" else "returns" in
                   let uu___3 = binder_to_string b in
                   let uu___4 =
                     match asc with
                     | FStar_Pervasives.Inl t -> term_to_string t
                     | FStar_Pervasives.Inr c -> comp_to_string c in
                   let uu___5 =
                     match tacopt with
                     | FStar_Pervasives_Native.None -> ""
                     | FStar_Pervasives_Native.Some tac ->
                         let uu___6 = term_to_string tac in
                         FStarC_Compiler_Util.format1 " by %s" uu___6 in
                   FStarC_Compiler_Util.format4 "as %s %s %s%s " uu___3 s
                     uu___4 uu___5 in
             let uu___3 =
               let uu___4 =
                 FStarC_Compiler_List.map branch_to_string branches in
               FStarC_Compiler_Util.concat_l "\n\t|" uu___4 in
             FStarC_Compiler_Util.format4 "(match %s %swith\n\t| %s%s)"
               uu___1 uu___2 uu___3 lc_str
         | FStarC_Syntax_Syntax.Tm_uinst (t, us) ->
             let uu___1 = FStarC_Options.print_universes () in
             if uu___1
             then
               let uu___2 = term_to_string t in
               let uu___3 = univs_to_string us in
               FStarC_Compiler_Util.format2 "%s<%s>" uu___2 uu___3
             else term_to_string t
         | FStarC_Syntax_Syntax.Tm_unknown -> "_")
and (branch_to_string : FStarC_Syntax_Syntax.branch -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | (p, wopt, e) ->
        let uu___1 = pat_to_string p in
        let uu___2 =
          match wopt with
          | FStar_Pervasives_Native.None -> ""
          | FStar_Pervasives_Native.Some w ->
              let uu___3 = term_to_string w in
              FStarC_Compiler_Util.format1 "when %s" uu___3 in
        let uu___3 = term_to_string e in
        FStarC_Compiler_Util.format3 "%s %s -> %s" uu___1 uu___2 uu___3
and (ctx_uvar_to_string_aux :
  Prims.bool -> FStarC_Syntax_Syntax.ctx_uvar -> Prims.string) =
  fun print_reason ->
    fun ctx_uvar ->
      let reason_string =
        if print_reason
        then
          FStarC_Compiler_Util.format1 "(* %s *)\n"
            ctx_uvar.FStarC_Syntax_Syntax.ctx_uvar_reason
        else
          (let uu___1 =
             let uu___2 =
               FStarC_Compiler_Range_Ops.start_of_range
                 ctx_uvar.FStarC_Syntax_Syntax.ctx_uvar_range in
             FStarC_Compiler_Range_Ops.string_of_pos uu___2 in
           let uu___2 =
             let uu___3 =
               FStarC_Compiler_Range_Ops.end_of_range
                 ctx_uvar.FStarC_Syntax_Syntax.ctx_uvar_range in
             FStarC_Compiler_Range_Ops.string_of_pos uu___3 in
           FStarC_Compiler_Util.format2 "(%s-%s) " uu___1 uu___2) in
      let uu___ =
        binders_to_string ", " ctx_uvar.FStarC_Syntax_Syntax.ctx_uvar_binders in
      let uu___1 = uvar_to_string ctx_uvar.FStarC_Syntax_Syntax.ctx_uvar_head in
      let uu___2 =
        let uu___3 = FStarC_Syntax_Util.ctx_uvar_typ ctx_uvar in
        term_to_string uu___3 in
      let uu___3 =
        let uu___4 = FStarC_Syntax_Util.ctx_uvar_should_check ctx_uvar in
        match uu___4 with
        | FStarC_Syntax_Syntax.Allow_unresolved s ->
            Prims.strcat "Allow_unresolved " s
        | FStarC_Syntax_Syntax.Allow_untyped s ->
            Prims.strcat "Allow_untyped " s
        | FStarC_Syntax_Syntax.Allow_ghost s -> Prims.strcat "Allow_ghost " s
        | FStarC_Syntax_Syntax.Strict -> "Strict"
        | FStarC_Syntax_Syntax.Already_checked -> "Already_checked" in
      FStarC_Compiler_Util.format5 "%s(%s |- %s : %s) %s" reason_string uu___
        uu___1 uu___2 uu___3
and (subst_elt_to_string : FStarC_Syntax_Syntax.subst_elt -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | FStarC_Syntax_Syntax.DB (i, x) ->
        let uu___1 = FStarC_Compiler_Util.string_of_int i in
        let uu___2 = bv_to_string x in
        FStarC_Compiler_Util.format2 "DB (%s, %s)" uu___1 uu___2
    | FStarC_Syntax_Syntax.DT (i, t) ->
        let uu___1 = FStarC_Compiler_Util.string_of_int i in
        let uu___2 = term_to_string t in
        FStarC_Compiler_Util.format2 "DT (%s, %s)" uu___1 uu___2
    | FStarC_Syntax_Syntax.NM (x, i) ->
        let uu___1 = bv_to_string x in
        let uu___2 = FStarC_Compiler_Util.string_of_int i in
        FStarC_Compiler_Util.format2 "NM (%s, %s)" uu___1 uu___2
    | FStarC_Syntax_Syntax.NT (x, t) ->
        let uu___1 = bv_to_string x in
        let uu___2 = term_to_string t in
        FStarC_Compiler_Util.format2 "NT (%s, %s)" uu___1 uu___2
    | FStarC_Syntax_Syntax.UN (i, u) ->
        let uu___1 = FStarC_Compiler_Util.string_of_int i in
        let uu___2 = univ_to_string u in
        FStarC_Compiler_Util.format2 "UN (%s, %s)" uu___1 uu___2
    | FStarC_Syntax_Syntax.UD (u, i) ->
        let uu___1 = FStarC_Ident.string_of_id u in
        let uu___2 = FStarC_Compiler_Util.string_of_int i in
        FStarC_Compiler_Util.format2 "UD (%s, %s)" uu___1 uu___2
and (subst_to_string :
  FStarC_Syntax_Syntax.subst_elt Prims.list -> Prims.string) =
  fun s ->
    let uu___ = FStarC_Compiler_List.map subst_elt_to_string s in
    FStarC_Compiler_String.concat "; " uu___
and (pat_to_string : FStarC_Syntax_Syntax.pat -> Prims.string) =
  fun x ->
    match x.FStarC_Syntax_Syntax.v with
    | FStarC_Syntax_Syntax.Pat_cons (l, us_opt, pats) ->
        let uu___ = fv_to_string l in
        let uu___1 =
          let uu___2 =
            let uu___3 = FStarC_Options.print_universes () in
            Prims.op_Negation uu___3 in
          if uu___2
          then " "
          else
            (match us_opt with
             | FStar_Pervasives_Native.None -> " "
             | FStar_Pervasives_Native.Some us ->
                 let uu___4 =
                   let uu___5 = FStarC_Compiler_List.map univ_to_string us in
                   FStarC_Compiler_String.concat " " uu___5 in
                 FStarC_Compiler_Util.format1 " %s " uu___4) in
        let uu___2 =
          let uu___3 =
            FStarC_Compiler_List.map
              (fun uu___4 ->
                 match uu___4 with
                 | (x1, b) ->
                     let p = pat_to_string x1 in
                     if b then Prims.strcat "#" p else p) pats in
          FStarC_Compiler_String.concat " " uu___3 in
        FStarC_Compiler_Util.format3 "(%s%s%s)" uu___ uu___1 uu___2
    | FStarC_Syntax_Syntax.Pat_dot_term topt ->
        let uu___ = FStarC_Options.print_bound_var_types () in
        if uu___
        then
          let uu___1 =
            if topt = FStar_Pervasives_Native.None
            then "_"
            else
              (let uu___3 = FStarC_Compiler_Util.must topt in
               term_to_string uu___3) in
          FStarC_Compiler_Util.format1 ".%s" uu___1
        else "._"
    | FStarC_Syntax_Syntax.Pat_var x1 ->
        let uu___ = FStarC_Options.print_bound_var_types () in
        if uu___
        then
          let uu___1 = bv_to_string x1 in
          let uu___2 = term_to_string x1.FStarC_Syntax_Syntax.sort in
          FStarC_Compiler_Util.format2 "%s:%s" uu___1 uu___2
        else bv_to_string x1
    | FStarC_Syntax_Syntax.Pat_constant c -> const_to_string c
and (lbs_to_string :
  FStarC_Syntax_Syntax.qualifier Prims.list ->
    (Prims.bool * FStarC_Syntax_Syntax.letbinding Prims.list) -> Prims.string)
  =
  fun quals ->
    fun lbs ->
      let uu___ = quals_to_string' quals in
      let uu___1 =
        let uu___2 =
          FStarC_Compiler_List.map
            (fun lb ->
               let uu___3 = attrs_to_string lb.FStarC_Syntax_Syntax.lbattrs in
               let uu___4 = lbname_to_string lb.FStarC_Syntax_Syntax.lbname in
               let uu___5 =
                 let uu___6 = FStarC_Options.print_universes () in
                 if uu___6
                 then
                   let uu___7 =
                     let uu___8 =
                       univ_names_to_string lb.FStarC_Syntax_Syntax.lbunivs in
                     Prims.strcat uu___8 ">" in
                   Prims.strcat "<" uu___7
                 else "" in
               let uu___6 = term_to_string lb.FStarC_Syntax_Syntax.lbtyp in
               let uu___7 = term_to_string lb.FStarC_Syntax_Syntax.lbdef in
               FStarC_Compiler_Util.format5 "%s%s %s : %s = %s" uu___3 uu___4
                 uu___5 uu___6 uu___7) (FStar_Pervasives_Native.snd lbs) in
        FStarC_Compiler_Util.concat_l "\n and " uu___2 in
      FStarC_Compiler_Util.format3 "%slet %s %s" uu___
        (if FStar_Pervasives_Native.fst lbs then "rec" else "") uu___1
and (attrs_to_string :
  FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax Prims.list ->
    Prims.string)
  =
  fun uu___ ->
    match uu___ with
    | [] -> ""
    | tms ->
        let uu___1 =
          let uu___2 =
            FStarC_Compiler_List.map
              (fun t -> let uu___3 = term_to_string t in paren uu___3) tms in
          FStarC_Compiler_String.concat "; " uu___2 in
        FStarC_Compiler_Util.format1 "[@ %s]" uu___1
and (binder_attrs_to_string :
  FStarC_Syntax_Syntax.term Prims.list -> Prims.string) =
  fun uu___ ->
    if FStarC_Options.any_dump_module ()
    then ""
    else
      (match uu___ with
       | [] -> ""
       | tms ->
           let uu___1 =
             let uu___2 =
               FStarC_Compiler_List.map
                 (fun t -> let uu___3 = term_to_string t in paren uu___3) tms in
             FStarC_Compiler_String.concat "; " uu___2 in
           FStarC_Compiler_Util.format1 "[@@@ %s]" uu___1)
and (bqual_to_string' :
  Prims.string ->
    FStarC_Syntax_Syntax.binder_qualifier FStar_Pervasives_Native.option ->
      Prims.string)
  =
  fun s ->
    fun uu___ ->
      match uu___ with
      | FStar_Pervasives_Native.Some (FStarC_Syntax_Syntax.Implicit (false))
          -> Prims.strcat "#" s
      | FStar_Pervasives_Native.Some (FStarC_Syntax_Syntax.Implicit (true))
          -> Prims.strcat "#." s
      | FStar_Pervasives_Native.Some (FStarC_Syntax_Syntax.Equality) ->
          Prims.strcat "$" s
      | FStar_Pervasives_Native.Some (FStarC_Syntax_Syntax.Meta t) when
          FStarC_Syntax_Util.is_fvar FStarC_Parser_Const.tcresolve_lid t ->
          Prims.strcat "{|" (Prims.strcat s "|}")
      | FStar_Pervasives_Native.Some (FStarC_Syntax_Syntax.Meta t) ->
          let uu___1 =
            let uu___2 = term_to_string t in
            Prims.strcat uu___2 (Prims.strcat "]" s) in
          Prims.strcat "#[" uu___1
      | FStar_Pervasives_Native.None -> s
and (aqual_to_string' :
  Prims.string ->
    FStarC_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
      Prims.string)
  =
  fun s ->
    fun uu___ ->
      match uu___ with
      | FStar_Pervasives_Native.Some
          { FStarC_Syntax_Syntax.aqual_implicit = true;
            FStarC_Syntax_Syntax.aqual_attributes = uu___1;_}
          -> Prims.strcat "#" s
      | uu___1 -> s
and (binder_to_string' :
  Prims.bool -> FStarC_Syntax_Syntax.binder -> Prims.string) =
  fun is_arrow ->
    fun b ->
      let attrs = binder_attrs_to_string b.FStarC_Syntax_Syntax.binder_attrs in
      let uu___ = FStarC_Syntax_Syntax.is_null_binder b in
      if uu___
      then
        let uu___1 =
          let uu___2 =
            term_to_string
              (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
          Prims.strcat "_:" uu___2 in
        Prims.strcat attrs uu___1
      else
        (let uu___2 =
           (Prims.op_Negation is_arrow) &&
             (let uu___3 = FStarC_Options.print_bound_var_types () in
              Prims.op_Negation uu___3) in
         if uu___2
         then
           let uu___3 =
             let uu___4 = nm_to_string b.FStarC_Syntax_Syntax.binder_bv in
             Prims.strcat attrs uu___4 in
           bqual_to_string' uu___3 b.FStarC_Syntax_Syntax.binder_qual
         else
           (let uu___4 =
              let uu___5 =
                let uu___6 = nm_to_string b.FStarC_Syntax_Syntax.binder_bv in
                let uu___7 =
                  let uu___8 =
                    term_to_string
                      (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
                  Prims.strcat ":" uu___8 in
                Prims.strcat uu___6 uu___7 in
              Prims.strcat attrs uu___5 in
            bqual_to_string' uu___4 b.FStarC_Syntax_Syntax.binder_qual))
and (binder_to_string : FStarC_Syntax_Syntax.binder -> Prims.string) =
  fun b -> binder_to_string' false b
and (arrow_binder_to_string : FStarC_Syntax_Syntax.binder -> Prims.string) =
  fun b -> binder_to_string' true b
and (binders_to_string :
  Prims.string -> FStarC_Syntax_Syntax.binder Prims.list -> Prims.string) =
  fun sep ->
    fun bs ->
      let bs1 =
        let uu___ = FStarC_Options.print_implicits () in
        if uu___ then bs else filter_imp_binders bs in
      if sep = " -> "
      then
        let uu___ = FStarC_Compiler_List.map arrow_binder_to_string bs1 in
        FStarC_Compiler_String.concat sep uu___
      else
        (let uu___1 = FStarC_Compiler_List.map binder_to_string bs1 in
         FStarC_Compiler_String.concat sep uu___1)
and (arg_to_string :
  (FStarC_Syntax_Syntax.term * FStarC_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) -> Prims.string)
  =
  fun uu___ ->
    match uu___ with
    | (a, imp) ->
        let uu___1 = term_to_string a in aqual_to_string' uu___1 imp
and (args_to_string :
  (FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax *
    FStarC_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
    Prims.list -> Prims.string)
  =
  fun args ->
    let args1 =
      let uu___ = FStarC_Options.print_implicits () in
      if uu___ then args else filter_imp_args args in
    let uu___ = FStarC_Compiler_List.map arg_to_string args1 in
    FStarC_Compiler_String.concat " " uu___
and (comp_to_string : FStarC_Syntax_Syntax.comp -> Prims.string) =
  fun c ->
    FStarC_Errors.with_ctx "While ugly-printing a computation"
      (fun uu___ ->
         match c.FStarC_Syntax_Syntax.n with
         | FStarC_Syntax_Syntax.Total t ->
             let uu___1 =
               let uu___2 = FStarC_Syntax_Subst.compress t in
               uu___2.FStarC_Syntax_Syntax.n in
             (match uu___1 with
              | FStarC_Syntax_Syntax.Tm_type uu___2 when
                  let uu___3 =
                    (FStarC_Options.print_implicits ()) ||
                      (FStarC_Options.print_universes ()) in
                  Prims.op_Negation uu___3 -> term_to_string t
              | uu___2 ->
                  let uu___3 = term_to_string t in
                  FStarC_Compiler_Util.format1 "Tot %s" uu___3)
         | FStarC_Syntax_Syntax.GTotal t ->
             let uu___1 =
               let uu___2 = FStarC_Syntax_Subst.compress t in
               uu___2.FStarC_Syntax_Syntax.n in
             (match uu___1 with
              | FStarC_Syntax_Syntax.Tm_type uu___2 when
                  let uu___3 =
                    (FStarC_Options.print_implicits ()) ||
                      (FStarC_Options.print_universes ()) in
                  Prims.op_Negation uu___3 -> term_to_string t
              | uu___2 ->
                  let uu___3 = term_to_string t in
                  FStarC_Compiler_Util.format1 "GTot %s" uu___3)
         | FStarC_Syntax_Syntax.Comp c1 ->
             let basic =
               let uu___1 = FStarC_Options.print_effect_args () in
               if uu___1
               then
                 let uu___2 = sli c1.FStarC_Syntax_Syntax.effect_name in
                 let uu___3 =
                   let uu___4 =
                     FStarC_Compiler_List.map univ_to_string
                       c1.FStarC_Syntax_Syntax.comp_univs in
                   FStarC_Compiler_String.concat ", " uu___4 in
                 let uu___4 =
                   term_to_string c1.FStarC_Syntax_Syntax.result_typ in
                 let uu___5 =
                   let uu___6 =
                     FStarC_Compiler_List.map arg_to_string
                       c1.FStarC_Syntax_Syntax.effect_args in
                   FStarC_Compiler_String.concat ", " uu___6 in
                 let uu___6 = cflags_to_string c1.FStarC_Syntax_Syntax.flags in
                 FStarC_Compiler_Util.format5
                   "%s<%s> (%s) %s (attributes %s)" uu___2 uu___3 uu___4
                   uu___5 uu___6
               else
                 (let uu___3 =
                    (FStarC_Compiler_Util.for_some
                       (fun uu___4 ->
                          match uu___4 with
                          | FStarC_Syntax_Syntax.TOTAL -> true
                          | uu___5 -> false) c1.FStarC_Syntax_Syntax.flags)
                      &&
                      (let uu___4 = FStarC_Options.print_effect_args () in
                       Prims.op_Negation uu___4) in
                  if uu___3
                  then
                    let uu___4 =
                      term_to_string c1.FStarC_Syntax_Syntax.result_typ in
                    FStarC_Compiler_Util.format1 "Tot %s" uu___4
                  else
                    (let uu___5 =
                       ((let uu___6 = FStarC_Options.print_effect_args () in
                         Prims.op_Negation uu___6) &&
                          (let uu___6 = FStarC_Options.print_implicits () in
                           Prims.op_Negation uu___6))
                         &&
                         (let uu___6 = FStarC_Parser_Const.effect_ML_lid () in
                          FStarC_Ident.lid_equals
                            c1.FStarC_Syntax_Syntax.effect_name uu___6) in
                     if uu___5
                     then term_to_string c1.FStarC_Syntax_Syntax.result_typ
                     else
                       (let uu___7 =
                          (let uu___8 = FStarC_Options.print_effect_args () in
                           Prims.op_Negation uu___8) &&
                            (FStarC_Compiler_Util.for_some
                               (fun uu___8 ->
                                  match uu___8 with
                                  | FStarC_Syntax_Syntax.MLEFFECT -> true
                                  | uu___9 -> false)
                               c1.FStarC_Syntax_Syntax.flags) in
                        if uu___7
                        then
                          let uu___8 =
                            term_to_string c1.FStarC_Syntax_Syntax.result_typ in
                          FStarC_Compiler_Util.format1 "ALL %s" uu___8
                        else
                          (let uu___9 =
                             sli c1.FStarC_Syntax_Syntax.effect_name in
                           let uu___10 =
                             term_to_string
                               c1.FStarC_Syntax_Syntax.result_typ in
                           FStarC_Compiler_Util.format2 "%s (%s)" uu___9
                             uu___10)))) in
             let dec =
               let uu___1 =
                 FStarC_Compiler_List.collect
                   (fun uu___2 ->
                      match uu___2 with
                      | FStarC_Syntax_Syntax.DECREASES dec_order ->
                          (match dec_order with
                           | FStarC_Syntax_Syntax.Decreases_lex l ->
                               let uu___3 =
                                 let uu___4 =
                                   match l with
                                   | [] -> ""
                                   | hd::tl ->
                                       let uu___5 = term_to_string hd in
                                       FStarC_Compiler_List.fold_left
                                         (fun s ->
                                            fun t ->
                                              let uu___6 =
                                                let uu___7 = term_to_string t in
                                                Prims.strcat ";" uu___7 in
                                              Prims.strcat s uu___6) uu___5
                                         tl in
                                 FStarC_Compiler_Util.format1
                                   " (decreases [%s])" uu___4 in
                               [uu___3]
                           | FStarC_Syntax_Syntax.Decreases_wf (rel, e) ->
                               let uu___3 =
                                 let uu___4 = term_to_string rel in
                                 let uu___5 = term_to_string e in
                                 FStarC_Compiler_Util.format2
                                   "(decreases {:well-founded %s %s})" uu___4
                                   uu___5 in
                               [uu___3])
                      | uu___3 -> []) c1.FStarC_Syntax_Syntax.flags in
               FStarC_Compiler_String.concat " " uu___1 in
             FStarC_Compiler_Util.format2 "%s%s" basic dec)
and (cflag_to_string : FStarC_Syntax_Syntax.cflag -> Prims.string) =
  fun c ->
    match c with
    | FStarC_Syntax_Syntax.TOTAL -> "total"
    | FStarC_Syntax_Syntax.MLEFFECT -> "ml"
    | FStarC_Syntax_Syntax.RETURN -> "return"
    | FStarC_Syntax_Syntax.PARTIAL_RETURN -> "partial_return"
    | FStarC_Syntax_Syntax.SOMETRIVIAL -> "sometrivial"
    | FStarC_Syntax_Syntax.TRIVIAL_POSTCONDITION -> "trivial_postcondition"
    | FStarC_Syntax_Syntax.SHOULD_NOT_INLINE -> "should_not_inline"
    | FStarC_Syntax_Syntax.LEMMA -> "lemma"
    | FStarC_Syntax_Syntax.CPS -> "cps"
    | FStarC_Syntax_Syntax.DECREASES uu___ -> ""
and (cflags_to_string :
  FStarC_Syntax_Syntax.cflag Prims.list -> Prims.string) =
  fun fs -> (FStarC_Common.string_of_list ()) cflag_to_string fs
and (formula_to_string :
  FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax -> Prims.string) =
  fun phi -> term_to_string phi
let (aqual_to_string :
  FStarC_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
    Prims.string)
  = fun aq -> aqual_to_string' "" aq
let (bqual_to_string :
  FStarC_Syntax_Syntax.binder_qualifier FStar_Pervasives_Native.option ->
    Prims.string)
  = fun bq -> bqual_to_string' "" bq
let (lb_to_string : FStarC_Syntax_Syntax.letbinding -> Prims.string) =
  fun lb -> lbs_to_string [] (false, [lb])
let comp_to_string' :
  'uuuuu . 'uuuuu -> FStarC_Syntax_Syntax.comp -> Prims.string =
  fun env -> fun c -> comp_to_string c
let term_to_string' :
  'uuuuu . 'uuuuu -> FStarC_Syntax_Syntax.term -> Prims.string =
  fun env -> fun x -> term_to_string x
let (enclose_universes : Prims.string -> Prims.string) =
  fun s ->
    let uu___ = FStarC_Options.print_universes () in
    if uu___ then Prims.strcat "<" (Prims.strcat s ">") else ""
let (tscheme_to_string : FStarC_Syntax_Syntax.tscheme -> Prims.string) =
  fun s ->
    let uu___ = s in
    match uu___ with
    | (us, t) ->
        let uu___1 =
          let uu___2 = univ_names_to_string us in enclose_universes uu___2 in
        let uu___2 = term_to_string t in
        FStarC_Compiler_Util.format2 "%s%s" uu___1 uu___2
let (action_to_string : FStarC_Syntax_Syntax.action -> Prims.string) =
  fun a ->
    let uu___ = sli a.FStarC_Syntax_Syntax.action_name in
    let uu___1 = binders_to_string " " a.FStarC_Syntax_Syntax.action_params in
    let uu___2 =
      let uu___3 = univ_names_to_string a.FStarC_Syntax_Syntax.action_univs in
      enclose_universes uu___3 in
    let uu___3 = term_to_string a.FStarC_Syntax_Syntax.action_typ in
    let uu___4 = term_to_string a.FStarC_Syntax_Syntax.action_defn in
    FStarC_Compiler_Util.format5 "%s%s %s : %s = %s" uu___ uu___1 uu___2
      uu___3 uu___4
let (wp_eff_combinators_to_string :
  FStarC_Syntax_Syntax.wp_eff_combinators -> Prims.string) =
  fun combs ->
    let tscheme_opt_to_string uu___ =
      match uu___ with
      | FStar_Pervasives_Native.Some ts -> tscheme_to_string ts
      | FStar_Pervasives_Native.None -> "None" in
    let uu___ =
      let uu___1 = tscheme_to_string combs.FStarC_Syntax_Syntax.ret_wp in
      let uu___2 =
        let uu___3 = tscheme_to_string combs.FStarC_Syntax_Syntax.bind_wp in
        let uu___4 =
          let uu___5 = tscheme_to_string combs.FStarC_Syntax_Syntax.stronger in
          let uu___6 =
            let uu___7 =
              tscheme_to_string combs.FStarC_Syntax_Syntax.if_then_else in
            let uu___8 =
              let uu___9 =
                tscheme_to_string combs.FStarC_Syntax_Syntax.ite_wp in
              let uu___10 =
                let uu___11 =
                  tscheme_to_string combs.FStarC_Syntax_Syntax.close_wp in
                let uu___12 =
                  let uu___13 =
                    tscheme_to_string combs.FStarC_Syntax_Syntax.trivial in
                  let uu___14 =
                    let uu___15 =
                      tscheme_opt_to_string combs.FStarC_Syntax_Syntax.repr in
                    let uu___16 =
                      let uu___17 =
                        tscheme_opt_to_string
                          combs.FStarC_Syntax_Syntax.return_repr in
                      let uu___18 =
                        let uu___19 =
                          tscheme_opt_to_string
                            combs.FStarC_Syntax_Syntax.bind_repr in
                        [uu___19] in
                      uu___17 :: uu___18 in
                    uu___15 :: uu___16 in
                  uu___13 :: uu___14 in
                uu___11 :: uu___12 in
              uu___9 :: uu___10 in
            uu___7 :: uu___8 in
          uu___5 :: uu___6 in
        uu___3 :: uu___4 in
      uu___1 :: uu___2 in
    FStarC_Compiler_Util.format
      "{\nret_wp       = %s\n; bind_wp      = %s\n; stronger     = %s\n; if_then_else = %s\n; ite_wp       = %s\n; close_wp     = %s\n; trivial      = %s\n; repr         = %s\n; return_repr  = %s\n; bind_repr    = %s\n}\n"
      uu___
let (sub_eff_to_string : FStarC_Syntax_Syntax.sub_eff -> Prims.string) =
  fun se ->
    let tsopt_to_string ts_opt =
      if FStarC_Compiler_Util.is_some ts_opt
      then
        let uu___ = FStarC_Compiler_Util.must ts_opt in
        tscheme_to_string uu___
      else "<None>" in
    let uu___ = lid_to_string se.FStarC_Syntax_Syntax.source in
    let uu___1 = lid_to_string se.FStarC_Syntax_Syntax.target in
    let uu___2 = tsopt_to_string se.FStarC_Syntax_Syntax.lift in
    let uu___3 = tsopt_to_string se.FStarC_Syntax_Syntax.lift_wp in
    FStarC_Compiler_Util.format4
      "sub_effect %s ~> %s : lift = %s ;; lift_wp = %s" uu___ uu___1 uu___2
      uu___3
let (layered_eff_combinators_to_string :
  FStarC_Syntax_Syntax.layered_eff_combinators -> Prims.string) =
  fun combs ->
    let to_str uu___ =
      match uu___ with
      | (ts_t, ts_ty, kopt) ->
          let uu___1 = tscheme_to_string ts_t in
          let uu___2 = tscheme_to_string ts_ty in
          let uu___3 =
            FStarC_Class_Show.show
              (FStarC_Class_Show.show_option
                 FStarC_Syntax_Syntax.showable_indexed_effect_combinator_kind)
              kopt in
          FStarC_Compiler_Util.format3 "(%s) : (%s)<%s>" uu___1 uu___2 uu___3 in
    let to_str2 uu___ =
      match uu___ with
      | (ts_t, ts_ty) ->
          let uu___1 = tscheme_to_string ts_t in
          let uu___2 = tscheme_to_string ts_ty in
          FStarC_Compiler_Util.format2 "(%s) : (%s)" uu___1 uu___2 in
    let uu___ =
      let uu___1 = to_str2 combs.FStarC_Syntax_Syntax.l_repr in
      let uu___2 =
        let uu___3 = to_str2 combs.FStarC_Syntax_Syntax.l_return in
        let uu___4 =
          let uu___5 = to_str combs.FStarC_Syntax_Syntax.l_bind in
          let uu___6 =
            let uu___7 = to_str combs.FStarC_Syntax_Syntax.l_subcomp in
            let uu___8 =
              let uu___9 = to_str combs.FStarC_Syntax_Syntax.l_if_then_else in
              let uu___10 =
                let uu___11 =
                  if
                    FStar_Pervasives_Native.uu___is_None
                      combs.FStarC_Syntax_Syntax.l_close
                  then ""
                  else
                    (let uu___13 =
                       let uu___14 =
                         FStarC_Compiler_Util.must
                           combs.FStarC_Syntax_Syntax.l_close in
                       to_str2 uu___14 in
                     FStarC_Compiler_Util.format1 "; l_close = %s\n" uu___13) in
                [uu___11] in
              uu___9 :: uu___10 in
            uu___7 :: uu___8 in
          uu___5 :: uu___6 in
        uu___3 :: uu___4 in
      uu___1 :: uu___2 in
    FStarC_Compiler_Util.format
      "{\n; l_repr = %s\n; l_return = %s\n; l_bind = %s\n; l_subcomp = %s\n; l_if_then_else = %s\n\n  %s\n  }\n"
      uu___
let (eff_combinators_to_string :
  FStarC_Syntax_Syntax.eff_combinators -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | FStarC_Syntax_Syntax.Primitive_eff combs ->
        wp_eff_combinators_to_string combs
    | FStarC_Syntax_Syntax.DM4F_eff combs ->
        wp_eff_combinators_to_string combs
    | FStarC_Syntax_Syntax.Layered_eff combs ->
        layered_eff_combinators_to_string combs
let (eff_extraction_mode_to_string :
  FStarC_Syntax_Syntax.eff_extraction_mode -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | FStarC_Syntax_Syntax.Extract_none s ->
        FStarC_Compiler_Util.format1 "none (%s)" s
    | FStarC_Syntax_Syntax.Extract_reify -> "reify"
    | FStarC_Syntax_Syntax.Extract_primitive -> "primitive"
let (eff_decl_to_string : FStarC_Syntax_Syntax.eff_decl -> Prims.string) =
  fun ed ->
    let actions_to_string actions =
      let uu___ = FStarC_Compiler_List.map action_to_string actions in
      FStarC_Compiler_String.concat ",\n\t" uu___ in
    let eff_name =
      let uu___ = FStarC_Syntax_Util.is_layered ed in
      if uu___ then "layered_effect" else "new_effect" in
    let uu___ =
      let uu___1 =
        let uu___2 =
          let uu___3 = lid_to_string ed.FStarC_Syntax_Syntax.mname in
          let uu___4 =
            let uu___5 =
              let uu___6 = univ_names_to_string ed.FStarC_Syntax_Syntax.univs in
              enclose_universes uu___6 in
            let uu___6 =
              let uu___7 =
                binders_to_string " " ed.FStarC_Syntax_Syntax.binders in
              let uu___8 =
                let uu___9 =
                  let uu___10 =
                    FStarC_Syntax_Util.effect_sig_ts
                      ed.FStarC_Syntax_Syntax.signature in
                  tscheme_to_string uu___10 in
                let uu___10 =
                  let uu___11 =
                    eff_combinators_to_string
                      ed.FStarC_Syntax_Syntax.combinators in
                  let uu___12 =
                    let uu___13 =
                      actions_to_string ed.FStarC_Syntax_Syntax.actions in
                    [uu___13] in
                  uu___11 :: uu___12 in
                uu___9 :: uu___10 in
              uu___7 :: uu___8 in
            uu___5 :: uu___6 in
          uu___3 :: uu___4 in
        "" :: uu___2 in
      eff_name :: uu___1 in
    FStarC_Compiler_Util.format
      "%s%s { %s%s %s : %s \n  %s\nand effect_actions\n\t%s\n}\n" uu___
let rec (sigelt_to_string : FStarC_Syntax_Syntax.sigelt -> Prims.string) =
  fun x ->
    let basic =
      match x.FStarC_Syntax_Syntax.sigel with
      | FStarC_Syntax_Syntax.Sig_pragma p ->
          FStarC_Class_Show.show FStarC_Syntax_Syntax.showable_pragma p
      | FStarC_Syntax_Syntax.Sig_inductive_typ
          { FStarC_Syntax_Syntax.lid = lid; FStarC_Syntax_Syntax.us = univs;
            FStarC_Syntax_Syntax.params = tps;
            FStarC_Syntax_Syntax.num_uniform_params = uu___;
            FStarC_Syntax_Syntax.t = k;
            FStarC_Syntax_Syntax.mutuals = uu___1;
            FStarC_Syntax_Syntax.ds = uu___2;
            FStarC_Syntax_Syntax.injective_type_params = uu___3;_}
          ->
          let quals_str = quals_to_string' x.FStarC_Syntax_Syntax.sigquals in
          let binders_str = binders_to_string " " tps in
          let term_str = term_to_string k in
          let uu___4 = FStarC_Options.print_universes () in
          if uu___4
          then
            let uu___5 = FStarC_Ident.string_of_lid lid in
            let uu___6 = univ_names_to_string univs in
            FStarC_Compiler_Util.format5 "%stype %s<%s> %s : %s" quals_str
              uu___5 uu___6 binders_str term_str
          else
            (let uu___6 = FStarC_Ident.string_of_lid lid in
             FStarC_Compiler_Util.format4 "%stype %s %s : %s" quals_str
               uu___6 binders_str term_str)
      | FStarC_Syntax_Syntax.Sig_datacon
          { FStarC_Syntax_Syntax.lid1 = lid;
            FStarC_Syntax_Syntax.us1 = univs; FStarC_Syntax_Syntax.t1 = t;
            FStarC_Syntax_Syntax.ty_lid = uu___;
            FStarC_Syntax_Syntax.num_ty_params = uu___1;
            FStarC_Syntax_Syntax.mutuals1 = uu___2;
            FStarC_Syntax_Syntax.injective_type_params1 = uu___3;_}
          ->
          let uu___4 = FStarC_Options.print_universes () in
          if uu___4
          then
            let uu___5 = univ_names_to_string univs in
            let uu___6 = FStarC_Ident.string_of_lid lid in
            let uu___7 = term_to_string t in
            FStarC_Compiler_Util.format3 "datacon<%s> %s : %s" uu___5 uu___6
              uu___7
          else
            (let uu___6 = FStarC_Ident.string_of_lid lid in
             let uu___7 = term_to_string t in
             FStarC_Compiler_Util.format2 "datacon %s : %s" uu___6 uu___7)
      | FStarC_Syntax_Syntax.Sig_declare_typ
          { FStarC_Syntax_Syntax.lid2 = lid;
            FStarC_Syntax_Syntax.us2 = univs; FStarC_Syntax_Syntax.t2 = t;_}
          ->
          let uu___ = quals_to_string' x.FStarC_Syntax_Syntax.sigquals in
          let uu___1 = FStarC_Ident.string_of_lid lid in
          let uu___2 =
            let uu___3 = FStarC_Options.print_universes () in
            if uu___3
            then
              let uu___4 = univ_names_to_string univs in
              FStarC_Compiler_Util.format1 "<%s>" uu___4
            else "" in
          let uu___3 = term_to_string t in
          FStarC_Compiler_Util.format4 "%sval %s %s : %s" uu___ uu___1 uu___2
            uu___3
      | FStarC_Syntax_Syntax.Sig_assume
          { FStarC_Syntax_Syntax.lid3 = lid; FStarC_Syntax_Syntax.us3 = us;
            FStarC_Syntax_Syntax.phi1 = f;_}
          ->
          let uu___ = FStarC_Options.print_universes () in
          if uu___
          then
            let uu___1 = FStarC_Ident.string_of_lid lid in
            let uu___2 = univ_names_to_string us in
            let uu___3 = term_to_string f in
            FStarC_Compiler_Util.format3 "assume %s<%s> : %s" uu___1 uu___2
              uu___3
          else
            (let uu___2 = FStarC_Ident.string_of_lid lid in
             let uu___3 = term_to_string f in
             FStarC_Compiler_Util.format2 "assume %s : %s" uu___2 uu___3)
      | FStarC_Syntax_Syntax.Sig_let
          { FStarC_Syntax_Syntax.lbs1 = lbs;
            FStarC_Syntax_Syntax.lids1 = uu___;_}
          ->
          let lbs1 =
            let uu___1 =
              FStarC_Compiler_List.map
                (fun lb ->
                   {
                     FStarC_Syntax_Syntax.lbname =
                       (lb.FStarC_Syntax_Syntax.lbname);
                     FStarC_Syntax_Syntax.lbunivs =
                       (lb.FStarC_Syntax_Syntax.lbunivs);
                     FStarC_Syntax_Syntax.lbtyp =
                       (lb.FStarC_Syntax_Syntax.lbtyp);
                     FStarC_Syntax_Syntax.lbeff =
                       (lb.FStarC_Syntax_Syntax.lbeff);
                     FStarC_Syntax_Syntax.lbdef =
                       (lb.FStarC_Syntax_Syntax.lbdef);
                     FStarC_Syntax_Syntax.lbattrs = [];
                     FStarC_Syntax_Syntax.lbpos =
                       (lb.FStarC_Syntax_Syntax.lbpos)
                   }) (FStar_Pervasives_Native.snd lbs) in
            ((FStar_Pervasives_Native.fst lbs), uu___1) in
          lbs_to_string x.FStarC_Syntax_Syntax.sigquals lbs1
      | FStarC_Syntax_Syntax.Sig_bundle
          { FStarC_Syntax_Syntax.ses = ses;
            FStarC_Syntax_Syntax.lids = uu___;_}
          ->
          let uu___1 =
            let uu___2 = FStarC_Compiler_List.map sigelt_to_string ses in
            FStarC_Compiler_String.concat "\n" uu___2 in
          Prims.strcat "(* Sig_bundle *)" uu___1
      | FStarC_Syntax_Syntax.Sig_fail
          { FStarC_Syntax_Syntax.errs = errs;
            FStarC_Syntax_Syntax.fail_in_lax = lax;
            FStarC_Syntax_Syntax.ses1 = ses;_}
          ->
          let uu___ = FStarC_Compiler_Util.string_of_bool lax in
          let uu___1 =
            (FStarC_Common.string_of_list ())
              FStarC_Compiler_Util.string_of_int errs in
          let uu___2 =
            let uu___3 = FStarC_Compiler_List.map sigelt_to_string ses in
            FStarC_Compiler_String.concat "\n" uu___3 in
          FStarC_Compiler_Util.format3
            "(* Sig_fail %s %s *)\n%s\n(* / Sig_fail*)\n" uu___ uu___1 uu___2
      | FStarC_Syntax_Syntax.Sig_new_effect ed ->
          let uu___ =
            let uu___1 = FStarC_Syntax_Util.is_dm4f ed in
            if uu___1 then "(* DM4F *)" else "" in
          let uu___1 =
            let uu___2 = quals_to_string' x.FStarC_Syntax_Syntax.sigquals in
            let uu___3 = eff_decl_to_string ed in Prims.strcat uu___2 uu___3 in
          Prims.strcat uu___ uu___1
      | FStarC_Syntax_Syntax.Sig_sub_effect se -> sub_eff_to_string se
      | FStarC_Syntax_Syntax.Sig_effect_abbrev
          { FStarC_Syntax_Syntax.lid4 = l; FStarC_Syntax_Syntax.us4 = univs;
            FStarC_Syntax_Syntax.bs2 = tps; FStarC_Syntax_Syntax.comp1 = c;
            FStarC_Syntax_Syntax.cflags = flags;_}
          ->
          let uu___ = FStarC_Options.print_universes () in
          if uu___
          then
            let uu___1 =
              let uu___2 =
                FStarC_Syntax_Syntax.mk
                  (FStarC_Syntax_Syntax.Tm_arrow
                     {
                       FStarC_Syntax_Syntax.bs1 = tps;
                       FStarC_Syntax_Syntax.comp = c
                     }) FStarC_Compiler_Range_Type.dummyRange in
              FStarC_Syntax_Subst.open_univ_vars univs uu___2 in
            (match uu___1 with
             | (univs1, t) ->
                 let uu___2 =
                   let uu___3 =
                     let uu___4 = FStarC_Syntax_Subst.compress t in
                     uu___4.FStarC_Syntax_Syntax.n in
                   match uu___3 with
                   | FStarC_Syntax_Syntax.Tm_arrow
                       { FStarC_Syntax_Syntax.bs1 = bs;
                         FStarC_Syntax_Syntax.comp = c1;_}
                       -> (bs, c1)
                   | uu___4 -> failwith "impossible" in
                 (match uu___2 with
                  | (tps1, c1) ->
                      let uu___3 = sli l in
                      let uu___4 = univ_names_to_string univs1 in
                      let uu___5 = binders_to_string " " tps1 in
                      let uu___6 = comp_to_string c1 in
                      FStarC_Compiler_Util.format4 "effect %s<%s> %s = %s"
                        uu___3 uu___4 uu___5 uu___6))
          else
            (let uu___2 = sli l in
             let uu___3 = binders_to_string " " tps in
             let uu___4 = comp_to_string c in
             FStarC_Compiler_Util.format3 "effect %s %s = %s" uu___2 uu___3
               uu___4)
      | FStarC_Syntax_Syntax.Sig_splice
          { FStarC_Syntax_Syntax.is_typed = is_typed;
            FStarC_Syntax_Syntax.lids2 = lids;
            FStarC_Syntax_Syntax.tac = t;_}
          ->
          let uu___ =
            let uu___1 =
              FStarC_Compiler_List.map
                (FStarC_Class_Show.show FStarC_Ident.showable_lident) lids in
            FStarC_Compiler_String.concat "; " uu___1 in
          let uu___1 = term_to_string t in
          FStarC_Compiler_Util.format3 "splice%s[%s] (%s)"
            (if is_typed then "_t" else "") uu___ uu___1
      | FStarC_Syntax_Syntax.Sig_polymonadic_bind
          { FStarC_Syntax_Syntax.m_lid = m; FStarC_Syntax_Syntax.n_lid = n;
            FStarC_Syntax_Syntax.p_lid = p; FStarC_Syntax_Syntax.tm3 = t;
            FStarC_Syntax_Syntax.typ = ty; FStarC_Syntax_Syntax.kind1 = k;_}
          ->
          let uu___ = FStarC_Class_Show.show FStarC_Ident.showable_lident m in
          let uu___1 = FStarC_Class_Show.show FStarC_Ident.showable_lident n in
          let uu___2 = FStarC_Class_Show.show FStarC_Ident.showable_lident p in
          let uu___3 = tscheme_to_string t in
          let uu___4 = tscheme_to_string ty in
          let uu___5 =
            FStarC_Class_Show.show
              (FStarC_Class_Show.show_option
                 FStarC_Syntax_Syntax.showable_indexed_effect_combinator_kind)
              k in
          FStarC_Compiler_Util.format6
            "polymonadic_bind (%s, %s) |> %s = (%s, %s)<%s>" uu___ uu___1
            uu___2 uu___3 uu___4 uu___5
      | FStarC_Syntax_Syntax.Sig_polymonadic_subcomp
          { FStarC_Syntax_Syntax.m_lid1 = m; FStarC_Syntax_Syntax.n_lid1 = n;
            FStarC_Syntax_Syntax.tm4 = t; FStarC_Syntax_Syntax.typ1 = ty;
            FStarC_Syntax_Syntax.kind2 = k;_}
          ->
          let uu___ = FStarC_Class_Show.show FStarC_Ident.showable_lident m in
          let uu___1 = FStarC_Class_Show.show FStarC_Ident.showable_lident n in
          let uu___2 = tscheme_to_string t in
          let uu___3 = tscheme_to_string ty in
          let uu___4 =
            FStarC_Class_Show.show
              (FStarC_Class_Show.show_option
                 FStarC_Syntax_Syntax.showable_indexed_effect_combinator_kind)
              k in
          FStarC_Compiler_Util.format5
            "polymonadic_subcomp %s <: %s = (%s, %s)<%s>" uu___ uu___1 uu___2
            uu___3 uu___4 in
    match x.FStarC_Syntax_Syntax.sigattrs with
    | [] -> Prims.strcat "[@ ]" (Prims.strcat "\n" basic)
    | uu___ ->
        let uu___1 = attrs_to_string x.FStarC_Syntax_Syntax.sigattrs in
        Prims.strcat uu___1 (Prims.strcat "\n" basic)