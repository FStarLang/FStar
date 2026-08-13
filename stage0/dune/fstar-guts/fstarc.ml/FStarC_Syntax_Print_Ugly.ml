open Prims
let sli (l : FStarC_Ident.lident) : Prims.string=
  let uu___ = FStarC_Options.print_real_names () in
  if uu___
  then FStarC_Ident.string_of_lid l
  else FStarC_Ident.string_of_id (FStarC_Ident.ident_of_lid l)
let lid_to_string (l : FStarC_Ident.lid) : Prims.string= sli l
let fv_to_string (fv : FStarC_Syntax_Syntax.fv) : Prims.string=
  lid_to_string fv.FStarC_Syntax_Syntax.fv_name
let bv_to_string (bv : FStarC_Syntax_Syntax.bv) : Prims.string=
  let uu___ =
    let uu___1 =
      FStarC_Class_Show.show FStarC_Class_Show.showable_int
        bv.FStarC_Syntax_Syntax.index in
    Prims.strcat "#" uu___1 in
  Prims.strcat (FStarC_Ident.string_of_id bv.FStarC_Syntax_Syntax.ppname)
    uu___
let nm_to_string (bv : FStarC_Syntax_Syntax.bv) : Prims.string=
  let uu___ = FStarC_Options.print_real_names () in
  if uu___
  then bv_to_string bv
  else FStarC_Ident.string_of_id bv.FStarC_Syntax_Syntax.ppname
let db_to_string (bv : FStarC_Syntax_Syntax.bv) : Prims.string=
  let uu___ =
    let uu___1 =
      FStarC_Class_Show.show FStarC_Class_Show.showable_int
        bv.FStarC_Syntax_Syntax.index in
    Prims.strcat "@" uu___1 in
  Prims.strcat (FStarC_Ident.string_of_id bv.FStarC_Syntax_Syntax.ppname)
    uu___
let filter_imp
  (aq : FStarC_Syntax_Syntax.binder_qualifier FStar_Pervasives_Native.option)
  : Prims.bool=
  match aq with
  | FStar_Pervasives_Native.Some (FStarC_Syntax_Syntax.Meta t) when
      FStarC_Syntax_Util.is_fvar FStarC_Parser_Const.tcresolve_lid t -> true
  | FStar_Pervasives_Native.Some (FStarC_Syntax_Syntax.Implicit uu___) ->
      false
  | FStar_Pervasives_Native.Some (FStarC_Syntax_Syntax.Meta uu___) -> false
  | uu___ -> true
let filter_imp_args
  (args :
    (FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax *
      FStarC_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
      Prims.list)
  : FStarC_Syntax_Syntax.arg Prims.list=
  FStarC_List.filter
    (fun uu___ ->
       match uu___ with
       | (uu___1, FStar_Pervasives_Native.None) -> true
       | (uu___1, FStar_Pervasives_Native.Some a) ->
           Prims.op_Negation a.FStarC_Syntax_Syntax.aqual_implicit) args
let filter_imp_binders (bs : FStarC_Syntax_Syntax.binder Prims.list) :
  FStarC_Syntax_Syntax.binder Prims.list=
  FStarC_List.filter (fun b -> filter_imp b.FStarC_Syntax_Syntax.binder_qual)
    bs
let const_to_string : FStarC_Const.sconst -> Prims.string=
  FStarC_Parser_Const.const_to_string
let lbname_to_string (x : FStarC_Syntax_Syntax.lbname) : Prims.string=
  match x with
  | FStar_Pervasives.Inl l -> bv_to_string l
  | FStar_Pervasives.Inr l -> lid_to_string l.FStarC_Syntax_Syntax.fv_name
let uvar_to_string (u : FStarC_Syntax_Syntax.uvar) : Prims.string=
  let uu___ = FStarC_Options.hide_uvar_nums () in
  if uu___
  then "?"
  else
    (let uu___1 =
       let uu___2 = FStarC_Syntax_Unionfind.uvar_id u in
       FStarC_Class_Show.show FStarC_Class_Show.showable_int uu___2 in
     Prims.strcat "?" uu___1)
let version_to_string (v : FStarC_Syntax_Syntax.version) : Prims.string=
  let uu___ =
    FStarC_Class_Show.show FStarC_Class_Show.showable_int
      v.FStarC_Syntax_Syntax.major in
  let uu___1 =
    FStarC_Class_Show.show FStarC_Class_Show.showable_int
      v.FStarC_Syntax_Syntax.minor in
  FStarC_Format.fmt2 "%s.%s" uu___ uu___1
let univ_uvar_to_string
  (u :
    (FStarC_Syntax_Syntax.universe FStar_Pervasives_Native.option
      FStarC_Unionfind.p_uvar * FStarC_Syntax_Syntax.version *
      FStarC_Range_Type.range))
  : Prims.string=
  let uu___ = FStarC_Options.hide_uvar_nums () in
  if uu___
  then "?"
  else
    (let uu___1 =
       let uu___2 =
         let uu___3 = FStarC_Syntax_Unionfind.univ_uvar_id u in
         FStarC_Class_Show.show FStarC_Class_Show.showable_int uu___3 in
       let uu___3 =
         let uu___4 =
           match u with | (uu___5, u1, uu___6) -> version_to_string u1 in
         Prims.strcat ":" uu___4 in
       Prims.strcat uu___2 uu___3 in
     Prims.strcat "?" uu___1)
let rec int_of_univ (n : Prims.int) (u : FStarC_Syntax_Syntax.universe) :
  (Prims.int * FStarC_Syntax_Syntax.universe FStar_Pervasives_Native.option)=
  let uu___ = FStarC_Syntax_Subst.compress_univ u in
  match uu___ with
  | FStarC_Syntax_Syntax.U_zero -> (n, FStar_Pervasives_Native.None)
  | FStarC_Syntax_Syntax.U_succ u1 -> int_of_univ (n + Prims.int_one) u1
  | uu___1 -> (n, (FStar_Pervasives_Native.Some u))
let rec univ_to_string (u : FStarC_Syntax_Syntax.universe) : Prims.string=
  FStarC_Errors.with_ctx "While printing universe"
    (fun uu___ ->
       let uu___1 = FStarC_Syntax_Subst.compress_univ u in
       match uu___1 with
       | FStarC_Syntax_Syntax.U_unif u1 ->
           let uu___2 = univ_uvar_to_string u1 in
           Prims.strcat "U_unif " uu___2
       | FStarC_Syntax_Syntax.U_name x ->
           Prims.strcat "U_name " (FStarC_Ident.string_of_id x)
       | FStarC_Syntax_Syntax.U_bvar x ->
           let uu___2 =
             FStarC_Class_Show.show FStarC_Class_Show.showable_int x in
           Prims.strcat "@" uu___2
       | FStarC_Syntax_Syntax.U_zero -> "0"
       | FStarC_Syntax_Syntax.U_succ u1 ->
           let uu___2 = int_of_univ Prims.int_one u1 in
           (match uu___2 with
            | (n, FStar_Pervasives_Native.None) ->
                FStarC_Class_Show.show FStarC_Class_Show.showable_int n
            | (n, FStar_Pervasives_Native.Some u2) ->
                let uu___3 = univ_to_string u2 in
                let uu___4 =
                  FStarC_Class_Show.show FStarC_Class_Show.showable_int n in
                FStarC_Format.fmt2 "(%s + %s)" uu___3 uu___4)
       | FStarC_Syntax_Syntax.U_max us ->
           let uu___2 =
             let uu___3 = FStarC_List.map univ_to_string us in
             FStarC_String.concat ", " uu___3 in
           FStarC_Format.fmt1 "(max %s)" uu___2
       | FStarC_Syntax_Syntax.U_unknown -> "unknown")
let univs_to_string (us : FStarC_Syntax_Syntax.universe Prims.list) :
  Prims.string=
  let uu___ = FStarC_List.map univ_to_string us in
  FStarC_String.concat ", " uu___
let univ_names_to_string (us : FStarC_Ident.ident Prims.list) : Prims.string=
  let uu___ = FStarC_List.map (fun x -> FStarC_Ident.string_of_id x) us in
  FStarC_String.concat ", " uu___
let qual_to_string (x : FStarC_Syntax_Syntax.qualifier) : Prims.string=
  match x with
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
      let uu___ = lid_to_string l in
      FStarC_Format.fmt1 "(Discriminator %s)" uu___
  | FStarC_Syntax_Syntax.Projector (l, x1) ->
      let uu___ = lid_to_string l in
      FStarC_Format.fmt2 "(Projector %s %s)" uu___
        (FStarC_Ident.string_of_id x1)
  | FStarC_Syntax_Syntax.RecordType (ns, fns) ->
      let uu___ =
        let uu___1 = FStarC_Ident.path_of_ns ns in
        FStarC_Ident.text_of_path uu___1 in
      let uu___1 =
        let uu___2 = FStarC_List.map FStarC_Ident.string_of_id fns in
        FStarC_String.concat ", " uu___2 in
      FStarC_Format.fmt2 "(RecordType %s %s)" uu___ uu___1
  | FStarC_Syntax_Syntax.RecordConstructor (ns, fns) ->
      let uu___ =
        let uu___1 = FStarC_Ident.path_of_ns ns in
        FStarC_Ident.text_of_path uu___1 in
      let uu___1 =
        let uu___2 = FStarC_List.map FStarC_Ident.string_of_id fns in
        FStarC_String.concat ", " uu___2 in
      FStarC_Format.fmt2 "(RecordConstructor %s %s)" uu___ uu___1
  | FStarC_Syntax_Syntax.Action eff_lid ->
      let uu___ = lid_to_string eff_lid in
      FStarC_Format.fmt1 "(Action %s)" uu___
  | FStarC_Syntax_Syntax.ExceptionConstructor -> "ExceptionConstructor"
  | FStarC_Syntax_Syntax.HasMaskedEffect -> "HasMaskedEffect"
  | FStarC_Syntax_Syntax.Effect -> "Effect"
  | FStarC_Syntax_Syntax.Reifiable -> "reify"
  | FStarC_Syntax_Syntax.Reflectable l ->
      FStarC_Format.fmt1 "(reflect %s)" (FStarC_Ident.string_of_lid l)
  | FStarC_Syntax_Syntax.OnlyName -> "OnlyName"
let quals_to_string (quals : FStarC_Syntax_Syntax.qualifier Prims.list) :
  Prims.string=
  match quals with
  | [] -> ""
  | uu___ ->
      let uu___1 = FStarC_List.map qual_to_string quals in
      FStarC_String.concat " " uu___1
let quals_to_string' (quals : FStarC_Syntax_Syntax.qualifier Prims.list) :
  Prims.string=
  match quals with
  | [] -> ""
  | uu___ -> let uu___1 = quals_to_string quals in Prims.strcat uu___1 " "
let paren (s : Prims.string) : Prims.string=
  Prims.strcat "(" (Prims.strcat s ")")
let rec term_to_string (x : FStarC_Syntax_Syntax.term) : Prims.string=
  FStarC_Errors.with_ctx "While ugly-printing a term"
    (fun uu___ ->
       let x1 = FStarC_Syntax_Subst.compress x in
       let x2 =
         let uu___1 = FStarC_Options.print_implicits () in
         if uu___1 then x1 else FStarC_Syntax_Util.unmeta x1 in
       match x2.FStarC_Syntax_Syntax.n with
       | FStarC_Syntax_Syntax.Tm_delayed uu___1 ->
           FStarC_Effect.failwith "impossible"
       | FStarC_Syntax_Syntax.Tm_lazy
           { FStarC_Syntax_Syntax.blob = b;
             FStarC_Syntax_Syntax.lkind = FStarC_Syntax_Syntax.Lazy_embedding
               (uu___1, thunk);
             FStarC_Syntax_Syntax.ltyp = uu___2;
             FStarC_Syntax_Syntax.rng = uu___3;_}
           ->
           let uu___4 =
             let uu___5 =
               let uu___6 = FStarC_Thunk.force thunk in term_to_string uu___6 in
             Prims.strcat uu___5 "]" in
           Prims.strcat "[LAZYEMB:" uu___4
       | FStarC_Syntax_Syntax.Tm_lazy i ->
           let uu___1 =
             let uu___2 =
               let uu___3 =
                 let uu___4 =
                   let uu___5 =
                     FStarC_Effect.op_Bang FStarC_Syntax_Syntax.lazy_chooser in
                   FStarC_Option.must uu___5 in
                 uu___4 i.FStarC_Syntax_Syntax.lkind i in
               term_to_string uu___3 in
             Prims.strcat uu___2 "]" in
           Prims.strcat "[lazy:" uu___1
       | FStarC_Syntax_Syntax.Tm_quoted (tm, qi) ->
           (match qi.FStarC_Syntax_Syntax.qkind with
            | FStarC_Syntax_Syntax.Quote_static ->
                let uu___1 = term_to_string tm in
                let uu___2 =
                  FStarC_Common.string_of_list term_to_string
                    (FStar_Pervasives_Native.snd
                       qi.FStarC_Syntax_Syntax.antiquotations) in
                FStarC_Format.fmt2 "`(%s)%s" uu___1 uu___2
            | FStarC_Syntax_Syntax.Quote_dynamic ->
                let uu___1 = term_to_string tm in
                FStarC_Format.fmt1 "quote (%s)" uu___1)
       | FStarC_Syntax_Syntax.Tm_meta
           { FStarC_Syntax_Syntax.tm2 = t;
             FStarC_Syntax_Syntax.meta = FStarC_Syntax_Syntax.Meta_pattern
               (uu___1, ps);_}
           ->
           let pats =
             let uu___2 =
               FStarC_List.map
                 (fun args ->
                    let uu___3 =
                      FStarC_List.map
                        (fun uu___4 ->
                           match uu___4 with
                           | (t1, uu___5) -> term_to_string t1) args in
                    FStarC_String.concat "; " uu___3) ps in
             FStarC_String.concat "\\/" uu___2 in
           let uu___2 = term_to_string t in
           FStarC_Format.fmt2 "{:pattern %s} %s" pats uu___2
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
           FStarC_Format.fmt4 "(MetaMonadic-{%s %s} (%s) %s)" uu___1 uu___2
             uu___3 uu___4
       | FStarC_Syntax_Syntax.Tm_meta
           { FStarC_Syntax_Syntax.tm2 = t;
             FStarC_Syntax_Syntax.meta =
               FStarC_Syntax_Syntax.Meta_monadic_lift (m0, m1, t');_}
           ->
           let uu___1 = term_to_string t' in
           let uu___2 = sli m0 in
           let uu___3 = sli m1 in
           let uu___4 = term_to_string t in
           FStarC_Format.fmt4 "(MetaMonadicLift-{%s : %s -> %s} %s)" uu___1
             uu___2 uu___3 uu___4
       | FStarC_Syntax_Syntax.Tm_meta
           { FStarC_Syntax_Syntax.tm2 = t;
             FStarC_Syntax_Syntax.meta = FStarC_Syntax_Syntax.Meta_labeled
               (l, r, b);_}
           ->
           let uu___1 = FStarC_Errors_Msg.rendermsg l in
           let uu___2 = FStarC_Range_Ops.string_of_range r in
           let uu___3 = term_to_string t in
           FStarC_Format.fmt3 "Meta_labeled(%s, %s){%s}" uu___1 uu___2 uu___3
       | FStarC_Syntax_Syntax.Tm_meta
           { FStarC_Syntax_Syntax.tm2 = t;
             FStarC_Syntax_Syntax.meta = FStarC_Syntax_Syntax.Meta_named l;_}
           ->
           let uu___1 = lid_to_string l in
           let uu___2 =
             FStarC_Range_Ops.string_of_range t.FStarC_Syntax_Syntax.pos in
           let uu___3 = term_to_string t in
           FStarC_Format.fmt3 "Meta_named(%s, %s){%s}" uu___1 uu___2 uu___3
       | FStarC_Syntax_Syntax.Tm_meta
           { FStarC_Syntax_Syntax.tm2 = t;
             FStarC_Syntax_Syntax.meta = FStarC_Syntax_Syntax.Meta_desugared
               uu___1;_}
           ->
           let uu___2 = term_to_string t in
           FStarC_Format.fmt1 "Meta_desugared{%s}" uu___2
       | FStarC_Syntax_Syntax.Tm_bvar x3 ->
           let uu___1 = db_to_string x3 in
           let uu___2 =
             let uu___3 =
               let uu___4 =
                 FStarC_Class_Tagged.tag_of FStarC_Syntax_Syntax.tagged_term
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
             let uu___3 = FStarC_Options.print_bound_var_types () in
             if uu___3 then FStarC_Options.print_effect_args () else false in
           if uu___2
           then ctx_uvar_to_string_aux true u
           else
             (let uu___3 =
                let uu___4 =
                  FStarC_Syntax_Unionfind.uvar_id
                    u.FStarC_Syntax_Syntax.ctx_uvar_head in
                FStarC_Class_Show.show FStarC_Class_Show.showable_int uu___4 in
              Prims.strcat "?" uu___3)
       | FStarC_Syntax_Syntax.Tm_uvar (u, s) ->
           let uu___1 =
             let uu___2 = FStarC_Options.print_bound_var_types () in
             if uu___2 then FStarC_Options.print_effect_args () else false in
           if uu___1
           then
             let uu___2 = ctx_uvar_to_string_aux true u in
             let uu___3 =
               let uu___4 =
                 FStarC_List.map subst_to_string
                   (FStar_Pervasives_Native.fst s) in
               FStarC_String.concat "; " uu___4 in
             FStarC_Format.fmt2 "(%s @ %s)" uu___2 uu___3
           else
             (let uu___2 =
                let uu___3 =
                  FStarC_Syntax_Unionfind.uvar_id
                    u.FStarC_Syntax_Syntax.ctx_uvar_head in
                FStarC_Class_Show.show FStarC_Class_Show.showable_int uu___3 in
              Prims.strcat "?" uu___2)
       | FStarC_Syntax_Syntax.Tm_constant c -> const_to_string c
       | FStarC_Syntax_Syntax.Tm_type u ->
           let uu___1 = FStarC_Options.print_universes () in
           if uu___1
           then
             let uu___2 = univ_to_string u in
             FStarC_Format.fmt1 "Type u#(%s)" uu___2
           else "Type"
       | FStarC_Syntax_Syntax.Tm_arrow uu___1 ->
           let uu___2 = FStarC_Syntax_Util.arrow_formals_comp_ln_strict x2 in
           (match uu___2 with
            | (bs, c) ->
                let uu___3 = binders_to_string " -> " bs in
                let uu___4 = comp_to_string c in
                FStarC_Format.fmt2 "(%s -> %s)" uu___3 uu___4)
       | FStarC_Syntax_Syntax.Tm_abs uu___1 ->
           let uu___2 = FStarC_Syntax_Util.abs_formals_ln x2 in
           (match uu___2 with
            | (bs, t2, lc) ->
                (match lc with
                 | FStar_Pervasives_Native.Some rc when
                     FStarC_Options.print_implicits () ->
                     let uu___3 = binders_to_string " " bs in
                     let uu___4 = term_to_string t2 in
                     let uu___5 =
                       if
                         FStar_Pervasives_Native.uu___is_None
                           rc.FStarC_Syntax_Syntax.residual_typ
                       then "None"
                       else
                         (let uu___6 =
                            FStarC_Option.must
                              rc.FStarC_Syntax_Syntax.residual_typ in
                          term_to_string uu___6) in
                     FStarC_Format.fmt4
                       "(fun %s -> (%s $$ (residual) %s %s))" uu___3 uu___4
                       (FStarC_Ident.string_of_lid
                          rc.FStarC_Syntax_Syntax.residual_effect) uu___5
                 | uu___3 ->
                     let uu___4 = binders_to_string " " bs in
                     let uu___5 = term_to_string t2 in
                     FStarC_Format.fmt2 "(fun %s -> %s)" uu___4 uu___5))
       | FStarC_Syntax_Syntax.Tm_refine
           { FStarC_Syntax_Syntax.b2 = xt; FStarC_Syntax_Syntax.phi = f;_} ->
           let uu___1 = bv_to_string xt in
           let uu___2 = term_to_string xt.FStarC_Syntax_Syntax.sort in
           let uu___3 = formula_to_string f in
           FStarC_Format.fmt3 "(%s:%s{%s})" uu___1 uu___2 uu___3
       | FStarC_Syntax_Syntax.Tm_app uu___1 ->
           let uu___2 = FStarC_Syntax_Util.head_and_args_full x2 in
           (match uu___2 with
            | (t, args) ->
                let uu___3 = term_to_string t in
                let uu___4 = args_to_string args in
                FStarC_Format.fmt2 "(%s %s)" uu___3 uu___4)
       | FStarC_Syntax_Syntax.Tm_let
           { FStarC_Syntax_Syntax.lbs = lbs;
             FStarC_Syntax_Syntax.body1 = e;_}
           ->
           let uu___1 = lbs_to_string [] lbs in
           let uu___2 = term_to_string e in
           FStarC_Format.fmt2 "%s\nin\n%s" uu___1 uu___2
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
                     FStarC_Option.map FStarC_Ident.string_of_lid eff_name in
                   FStarC_Option.dflt "default" uu___2 in
                 let uu___2 = term_to_string t in
                 FStarC_Format.fmt2 "[%s] %s" uu___1 uu___2
             | FStar_Pervasives.Inr c -> comp_to_string c in
           let topt1 =
             match topt with
             | FStar_Pervasives_Native.None -> ""
             | FStar_Pervasives_Native.Some t ->
                 let uu___1 = term_to_string t in
                 FStarC_Format.fmt1 "by %s" uu___1 in
           let s = if b then "ascribed_eq" else "ascribed" in
           let uu___1 = term_to_string e in
           FStarC_Format.fmt4 "(%s <%s: %s %s)" uu___1 s annot1 topt1
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
                     FStar_Pervasives_Native.uu___is_None
                       lc1.FStarC_Syntax_Syntax.residual_typ
                   then "None"
                   else
                     (let uu___2 =
                        FStarC_Option.must
                          lc1.FStarC_Syntax_Syntax.residual_typ in
                      term_to_string uu___2) in
                 FStarC_Format.fmt1 " (residual_comp:%s)" uu___1
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
                       FStarC_Format.fmt1 " by %s" uu___6 in
                 FStarC_Format.fmt4 "as %s %s %s%s " uu___3 s uu___4 uu___5 in
           let uu___3 =
             let uu___4 = FStarC_List.map branch_to_string branches in
             FStarC_Util.concat_l "\n\t|" uu___4 in
           FStarC_Format.fmt4 "(match %s %swith\n\t| %s%s)" uu___1 uu___2
             uu___3 lc_str
       | FStarC_Syntax_Syntax.Tm_uinst (t, us) ->
           let uu___1 = FStarC_Options.print_universes () in
           if uu___1
           then
             let uu___2 = term_to_string t in
             let uu___3 = univs_to_string us in
             FStarC_Format.fmt2 "%s<%s>" uu___2 uu___3
           else term_to_string t
       | FStarC_Syntax_Syntax.Tm_unknown -> "_")
and branch_to_string (x : FStarC_Syntax_Syntax.branch) : Prims.string=
  let uu___ = x in
  match uu___ with
  | (p, wopt, e) ->
      let uu___1 = pat_to_string p in
      let uu___2 =
        match wopt with
        | FStar_Pervasives_Native.None -> ""
        | FStar_Pervasives_Native.Some w ->
            let uu___3 = term_to_string w in
            FStarC_Format.fmt1 "when %s" uu___3 in
      let uu___3 = term_to_string e in
      FStarC_Format.fmt3 "%s %s -> %s" uu___1 uu___2 uu___3
and ctx_uvar_to_string_aux (print_reason : Prims.bool)
  (ctx_uvar : FStarC_Syntax_Syntax.ctx_uvar) : Prims.string=
  let reason_string =
    if print_reason
    then
      FStarC_Format.fmt1 "(* %s *)\n"
        ctx_uvar.FStarC_Syntax_Syntax.ctx_uvar_reason
    else
      (let uu___ =
         FStarC_Range_Ops.string_of_pos
           (FStarC_Range_Ops.start_of_range
              ctx_uvar.FStarC_Syntax_Syntax.ctx_uvar_range) in
       let uu___1 =
         FStarC_Range_Ops.string_of_pos
           (FStarC_Range_Ops.end_of_range
              ctx_uvar.FStarC_Syntax_Syntax.ctx_uvar_range) in
       FStarC_Format.fmt2 "(%s-%s) " uu___ uu___1) in
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
    | FStarC_Syntax_Syntax.Allow_untyped s -> Prims.strcat "Allow_untyped " s
    | FStarC_Syntax_Syntax.Allow_ghost s -> Prims.strcat "Allow_ghost " s
    | FStarC_Syntax_Syntax.Strict -> "Strict"
    | FStarC_Syntax_Syntax.Already_checked -> "Already_checked" in
  FStarC_Format.fmt5 "%s(%s |- %s : %s) %s" reason_string uu___ uu___1 uu___2
    uu___3
and subst_elt_to_string (x : FStarC_Syntax_Syntax.subst_elt) : Prims.string=
  match x with
  | FStarC_Syntax_Syntax.DB (i, x1) ->
      let uu___ = FStarC_Class_Show.show FStarC_Class_Show.showable_int i in
      let uu___1 = bv_to_string x1 in
      FStarC_Format.fmt2 "DB (%s, %s)" uu___ uu___1
  | FStarC_Syntax_Syntax.DT (i, t) ->
      let uu___ = FStarC_Class_Show.show FStarC_Class_Show.showable_int i in
      let uu___1 = term_to_string t in
      FStarC_Format.fmt2 "DT (%s, %s)" uu___ uu___1
  | FStarC_Syntax_Syntax.NM (x1, i) ->
      let uu___ = bv_to_string x1 in
      let uu___1 = FStarC_Class_Show.show FStarC_Class_Show.showable_int i in
      FStarC_Format.fmt2 "NM (%s, %s)" uu___ uu___1
  | FStarC_Syntax_Syntax.NT (x1, t) ->
      let uu___ = bv_to_string x1 in
      let uu___1 = term_to_string t in
      FStarC_Format.fmt2 "NT (%s, %s)" uu___ uu___1
  | FStarC_Syntax_Syntax.UN (i, u) ->
      let uu___ = FStarC_Class_Show.show FStarC_Class_Show.showable_int i in
      let uu___1 = univ_to_string u in
      FStarC_Format.fmt2 "UN (%s, %s)" uu___ uu___1
  | FStarC_Syntax_Syntax.UD (u, i) ->
      let uu___ = FStarC_Class_Show.show FStarC_Class_Show.showable_int i in
      FStarC_Format.fmt2 "UD (%s, %s)" (FStarC_Ident.string_of_id u) uu___
and subst_to_string (s : FStarC_Syntax_Syntax.subst_elt Prims.list) :
  Prims.string=
  let uu___ = FStarC_List.map subst_elt_to_string s in
  FStarC_String.concat "; " uu___
and pat_to_string (x : FStarC_Syntax_Syntax.pat) : Prims.string=
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
               let uu___3 =
                 let uu___4 = FStarC_List.map univ_to_string us in
                 FStarC_String.concat " " uu___4 in
               FStarC_Format.fmt1 " %s " uu___3) in
      let uu___2 =
        let uu___3 =
          FStarC_List.map
            (fun uu___4 ->
               match uu___4 with
               | (x1, b) ->
                   let p = pat_to_string x1 in
                   if b then Prims.strcat "#" p else p) pats in
        FStarC_String.concat " " uu___3 in
      FStarC_Format.fmt3 "(%s%s%s)" uu___ uu___1 uu___2
  | FStarC_Syntax_Syntax.Pat_dot_term topt ->
      let uu___ = FStarC_Options.print_bound_var_types () in
      if uu___
      then
        let uu___1 =
          if topt = FStar_Pervasives_Native.None
          then "_"
          else
            (let uu___2 = FStarC_Option.must topt in term_to_string uu___2) in
        FStarC_Format.fmt1 ".%s" uu___1
      else "._"
  | FStarC_Syntax_Syntax.Pat_var x1 ->
      let uu___ = FStarC_Options.print_bound_var_types () in
      if uu___
      then
        let uu___1 = bv_to_string x1 in
        let uu___2 = term_to_string x1.FStarC_Syntax_Syntax.sort in
        FStarC_Format.fmt2 "%s:%s" uu___1 uu___2
      else bv_to_string x1
  | FStarC_Syntax_Syntax.Pat_constant c -> const_to_string c
and lbs_to_string (quals : FStarC_Syntax_Syntax.qualifier Prims.list)
  (lbs : (Prims.bool * FStarC_Syntax_Syntax.letbinding Prims.list)) :
  Prims.string=
  let uu___ = quals_to_string' quals in
  let uu___1 =
    let uu___2 =
      FStarC_List.map
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
           FStarC_Format.fmt5 "%s%s %s : %s = %s" uu___3 uu___4 uu___5 uu___6
             uu___7) (FStar_Pervasives_Native.snd lbs) in
    FStarC_Util.concat_l "\n and " uu___2 in
  FStarC_Format.fmt3 "%slet %s %s" uu___
    (if FStar_Pervasives_Native.fst lbs then "rec" else "") uu___1
and attrs_to_string (l : FStarC_Syntax_Syntax.term Prims.list) :
  Prims.string=
  match l with
  | [] -> ""
  | tms ->
      let uu___ =
        let uu___1 =
          FStarC_List.map
            (fun t -> let uu___2 = term_to_string t in paren uu___2) tms in
        FStarC_String.concat "; " uu___1 in
      FStarC_Format.fmt1 "[@ %s]" uu___
and binder_attrs_to_string (l : FStarC_Syntax_Syntax.term Prims.list) :
  Prims.string=
  if FStarC_Options.any_dump_module ()
  then ""
  else
    (match l with
     | [] -> ""
     | tms ->
         let uu___ =
           let uu___1 =
             FStarC_List.map
               (fun t -> let uu___2 = term_to_string t in paren uu___2) tms in
           FStarC_String.concat "; " uu___1 in
         FStarC_Format.fmt1 "[@@@ %s]" uu___)
and bqual_to_string' (s : Prims.string) (q : FStarC_Syntax_Syntax.bqual) :
  Prims.string=
  match q with
  | FStar_Pervasives_Native.Some (FStarC_Syntax_Syntax.Implicit false) ->
      Prims.strcat "#" s
  | FStar_Pervasives_Native.Some (FStarC_Syntax_Syntax.Implicit true) ->
      Prims.strcat "#." s
  | FStar_Pervasives_Native.Some (FStarC_Syntax_Syntax.Equality) ->
      Prims.strcat "$" s
  | FStar_Pervasives_Native.Some (FStarC_Syntax_Syntax.Meta t) when
      FStarC_Syntax_Util.is_fvar FStarC_Parser_Const.tcresolve_lid t ->
      Prims.strcat "{|" (Prims.strcat s "|}")
  | FStar_Pervasives_Native.Some (FStarC_Syntax_Syntax.Meta t) ->
      let uu___ =
        let uu___1 = term_to_string t in
        Prims.strcat uu___1 (Prims.strcat "]" s) in
      Prims.strcat "#[" uu___
  | FStar_Pervasives_Native.None -> s
and aqual_to_string' (s : Prims.string) (q : FStarC_Syntax_Syntax.aqual) :
  Prims.string=
  match q with
  | FStar_Pervasives_Native.Some
      { FStarC_Syntax_Syntax.aqual_implicit = true;
        FStarC_Syntax_Syntax.aqual_attributes = uu___;_}
      -> Prims.strcat "#" s
  | uu___ -> s
and binder_to_string' (is_arrow : Prims.bool)
  (b : FStarC_Syntax_Syntax.binder) : Prims.string=
  let attrs = binder_attrs_to_string b.FStarC_Syntax_Syntax.binder_attrs in
  if FStarC_Syntax_Syntax.is_null_binder b
  then
    let uu___ =
      let uu___1 =
        term_to_string
          (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
      Prims.strcat "_:" uu___1 in
    Prims.strcat attrs uu___
  else
    (let uu___ =
       if Prims.op_Negation is_arrow
       then
         let uu___1 = FStarC_Options.print_bound_var_types () in
         Prims.op_Negation uu___1
       else false in
     if uu___
     then
       let uu___1 =
         let uu___2 = nm_to_string b.FStarC_Syntax_Syntax.binder_bv in
         Prims.strcat attrs uu___2 in
       bqual_to_string' uu___1 b.FStarC_Syntax_Syntax.binder_qual
     else
       (let uu___1 =
          let uu___2 =
            let uu___3 = nm_to_string b.FStarC_Syntax_Syntax.binder_bv in
            let uu___4 =
              let uu___5 =
                term_to_string
                  (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
              Prims.strcat ":" uu___5 in
            Prims.strcat uu___3 uu___4 in
          Prims.strcat attrs uu___2 in
        bqual_to_string' uu___1 b.FStarC_Syntax_Syntax.binder_qual))
and binder_to_string (b : FStarC_Syntax_Syntax.binder) : Prims.string=
  binder_to_string' false b
and arrow_binder_to_string (b : FStarC_Syntax_Syntax.binder) : Prims.string=
  binder_to_string' true b
and binders_to_string (sep : Prims.string)
  (bs : FStarC_Syntax_Syntax.binders) : Prims.string=
  let bs1 =
    let uu___ = FStarC_Options.print_implicits () in
    if uu___ then bs else filter_imp_binders bs in
  if sep = " -> "
  then
    let uu___ = FStarC_List.map arrow_binder_to_string bs1 in
    FStarC_String.concat sep uu___
  else
    (let uu___ = FStarC_List.map binder_to_string bs1 in
     FStarC_String.concat sep uu___)
and arg_to_string (x : FStarC_Syntax_Syntax.arg) : Prims.string=
  match x with
  | (a, imp) -> let uu___ = term_to_string a in aqual_to_string' uu___ imp
and args_to_string (args : FStarC_Syntax_Syntax.args) : Prims.string=
  let args1 =
    let uu___ = FStarC_Options.print_implicits () in
    if uu___ then args else filter_imp_args args in
  let uu___ = FStarC_List.map arg_to_string args1 in
  FStarC_String.concat " " uu___
and comp_to_string (c : FStarC_Syntax_Syntax.comp) : Prims.string=
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
                  let uu___4 = FStarC_Options.print_implicits () in
                  if uu___4 then true else FStarC_Options.print_universes () in
                Prims.op_Negation uu___3 -> term_to_string t
            | uu___2 ->
                let uu___3 = term_to_string t in
                FStarC_Format.fmt1 "Tot %s" uu___3)
       | FStarC_Syntax_Syntax.GTotal t ->
           let uu___1 =
             let uu___2 = FStarC_Syntax_Subst.compress t in
             uu___2.FStarC_Syntax_Syntax.n in
           (match uu___1 with
            | FStarC_Syntax_Syntax.Tm_type uu___2 when
                let uu___3 =
                  let uu___4 = FStarC_Options.print_implicits () in
                  if uu___4 then true else FStarC_Options.print_universes () in
                Prims.op_Negation uu___3 -> term_to_string t
            | uu___2 ->
                let uu___3 = term_to_string t in
                FStarC_Format.fmt1 "GTot %s" uu___3)
       | FStarC_Syntax_Syntax.Comp c1 ->
           let basic =
             let uu___1 = FStarC_Options.print_effect_args () in
             if uu___1
             then
               let uu___2 =
                 let uu___3 = sli c1.FStarC_Syntax_Syntax.effect_name in
                 let uu___4 =
                   let uu___5 =
                     let uu___6 =
                       FStarC_List.map univ_to_string
                         c1.FStarC_Syntax_Syntax.comp_univs in
                     FStarC_String.concat ", " uu___6 in
                   let uu___6 =
                     let uu___7 =
                       term_to_string c1.FStarC_Syntax_Syntax.result_typ in
                     let uu___8 =
                       let uu___9 =
                         term_to_string c1.FStarC_Syntax_Syntax.comp_pre in
                       let uu___10 =
                         let uu___11 =
                           term_to_string c1.FStarC_Syntax_Syntax.comp_post in
                         let uu___12 =
                           let uu___13 =
                             cflags_to_string c1.FStarC_Syntax_Syntax.flags in
                           [uu___13] in
                         uu___11 :: uu___12 in
                       uu___9 :: uu___10 in
                     uu___7 :: uu___8 in
                   uu___5 :: uu___6 in
                 uu___3 :: uu___4 in
               FStarC_Format.fmt
                 "%s<%s> (%s) (requires %s) (ensures %s) (attributes %s)"
                 uu___2
             else
               (let uu___2 =
                  let uu___3 =
                    FStarC_Util.for_some
                      (fun uu___4 ->
                         match uu___4 with
                         | FStarC_Syntax_Syntax.TOTAL -> true
                         | uu___5 -> false) c1.FStarC_Syntax_Syntax.flags in
                  if uu___3
                  then
                    let uu___4 = FStarC_Options.print_effect_args () in
                    Prims.op_Negation uu___4
                  else false in
                if uu___2
                then
                  let uu___3 =
                    term_to_string c1.FStarC_Syntax_Syntax.result_typ in
                  FStarC_Format.fmt1 "Tot %s" uu___3
                else
                  (let uu___3 =
                     let uu___4 =
                       let uu___5 =
                         let uu___6 = FStarC_Options.print_effect_args () in
                         Prims.op_Negation uu___6 in
                       if uu___5
                       then
                         let uu___6 = FStarC_Options.print_implicits () in
                         Prims.op_Negation uu___6
                       else false in
                     if uu___4
                     then
                       let uu___5 = FStarC_Parser_Const.effect_ML_lid () in
                       FStarC_Ident.lid_equals
                         c1.FStarC_Syntax_Syntax.effect_name uu___5
                     else false in
                   if uu___3
                   then term_to_string c1.FStarC_Syntax_Syntax.result_typ
                   else
                     (let uu___4 =
                        let uu___5 =
                          let uu___6 = FStarC_Options.print_effect_args () in
                          Prims.op_Negation uu___6 in
                        if uu___5
                        then
                          FStarC_Util.for_some
                            (fun uu___6 ->
                               match uu___6 with
                               | FStarC_Syntax_Syntax.MLEFFECT -> true
                               | uu___7 -> false)
                            c1.FStarC_Syntax_Syntax.flags
                        else false in
                      if uu___4
                      then
                        let uu___5 =
                          term_to_string c1.FStarC_Syntax_Syntax.result_typ in
                        FStarC_Format.fmt1 "ALL %s" uu___5
                      else
                        (let uu___5 = sli c1.FStarC_Syntax_Syntax.effect_name in
                         let uu___6 =
                           term_to_string c1.FStarC_Syntax_Syntax.result_typ in
                         FStarC_Format.fmt2 "%s (%s)" uu___5 uu___6)))) in
           let dec =
             let uu___1 =
               FStarC_List.collect
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
                                     FStarC_List.fold_left
                                       (fun s t ->
                                          let uu___6 =
                                            let uu___7 = term_to_string t in
                                            Prims.strcat ";" uu___7 in
                                          Prims.strcat s uu___6) uu___5 tl in
                               FStarC_Format.fmt1 " (decreases [%s])" uu___4 in
                             [uu___3]
                         | FStarC_Syntax_Syntax.Decreases_wf (rel, e) ->
                             let uu___3 =
                               let uu___4 = term_to_string rel in
                               let uu___5 = term_to_string e in
                               FStarC_Format.fmt2
                                 "(decreases {:well-founded %s %s})" uu___4
                                 uu___5 in
                             [uu___3])
                    | uu___3 -> []) c1.FStarC_Syntax_Syntax.flags in
             FStarC_String.concat " " uu___1 in
           FStarC_Format.fmt2 "%s%s" basic dec)
and cflag_to_string (c : FStarC_Syntax_Syntax.cflag) : Prims.string=
  match c with
  | FStarC_Syntax_Syntax.TOTAL -> "total"
  | FStarC_Syntax_Syntax.MLEFFECT -> "ml"
  | FStarC_Syntax_Syntax.SMTPAT p ->
      let uu___ = term_to_string p in Prims.strcat "smtpat " uu___
  | FStarC_Syntax_Syntax.LEMMA -> "lemma"
  | FStarC_Syntax_Syntax.DECREASES uu___ -> ""
and cflags_to_string (fs : FStarC_Syntax_Syntax.cflag Prims.list) :
  Prims.string= FStarC_Common.string_of_list cflag_to_string fs
and formula_to_string
  (phi : FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax) :
  Prims.string= term_to_string phi
let aqual_to_string (aq : FStarC_Syntax_Syntax.aqual) : Prims.string=
  aqual_to_string' "" aq
let bqual_to_string (bq : FStarC_Syntax_Syntax.bqual) : Prims.string=
  bqual_to_string' "" bq
let lb_to_string (lb : FStarC_Syntax_Syntax.letbinding) : Prims.string=
  lbs_to_string [] (false, [lb])
let comp_to_string' (env : 'uuuuu) (c : FStarC_Syntax_Syntax.comp) :
  Prims.string= comp_to_string c
let term_to_string' (env : 'uuuuu) (x : FStarC_Syntax_Syntax.term) :
  Prims.string= term_to_string x
let enclose_universes (s : Prims.string) : Prims.string=
  let uu___ = FStarC_Options.print_universes () in
  if uu___ then Prims.strcat "<" (Prims.strcat s ">") else ""
let tscheme_to_string (s : FStarC_Syntax_Syntax.tscheme) : Prims.string=
  let uu___ = s in
  match uu___ with
  | (us, t) ->
      let uu___1 =
        let uu___2 = univ_names_to_string us in enclose_universes uu___2 in
      let uu___2 = term_to_string t in
      FStarC_Format.fmt2 "%s%s" uu___1 uu___2
let sub_eff_to_string (se : FStarC_Syntax_Syntax.sub_eff) : Prims.string=
  let uu___ = lid_to_string se.FStarC_Syntax_Syntax.source in
  let uu___1 = lid_to_string se.FStarC_Syntax_Syntax.target in
  let uu___2 =
    match se.FStarC_Syntax_Syntax.lift with
    | FStar_Pervasives_Native.None -> ""
    | FStar_Pervasives_Native.Some ts ->
        let uu___3 = tscheme_to_string ts in Prims.strcat " = " uu___3 in
  FStarC_Format.fmt3 "sub_effect %s ~> %s%s" uu___ uu___1 uu___2
let eff_extraction_mode_to_string
  (x : FStarC_Syntax_Syntax.eff_extraction_mode) : Prims.string=
  match x with
  | FStarC_Syntax_Syntax.Extract_none s -> FStarC_Format.fmt1 "none (%s)" s
  | FStarC_Syntax_Syntax.Extract_reify -> "reify"
  | FStarC_Syntax_Syntax.Extract_primitive -> "primitive"
let eff_decl_to_string (ed : FStarC_Syntax_Syntax.eff_decl) : Prims.string=
  match ed.FStarC_Syntax_Syntax.combinators with
  | FStar_Pervasives_Native.None ->
      let uu___ = lid_to_string ed.FStarC_Syntax_Syntax.mname in
      let uu___1 =
        let uu___2 = univ_names_to_string ed.FStarC_Syntax_Syntax.univs in
        enclose_universes uu___2 in
      let uu___2 = binders_to_string " " ed.FStarC_Syntax_Syntax.binders in
      FStarC_Format.fmt3 "assume effect %s%s%s\n" uu___ uu___1 uu___2
  | FStar_Pervasives_Native.Some c ->
      let uu___ = lid_to_string ed.FStarC_Syntax_Syntax.mname in
      let uu___1 =
        let uu___2 = univ_names_to_string ed.FStarC_Syntax_Syntax.univs in
        enclose_universes uu___2 in
      let uu___2 = binders_to_string " " ed.FStarC_Syntax_Syntax.binders in
      let uu___3 = tscheme_to_string c.FStarC_Syntax_Syntax.repr in
      let uu___4 = tscheme_to_string c.FStarC_Syntax_Syntax.return_repr in
      let uu___5 = tscheme_to_string c.FStarC_Syntax_Syntax.bind_repr in
      FStarC_Format.fmt6
        "effect { %s%s%s with { repr = %s; return = %s; bind = %s } }\n"
        uu___ uu___1 uu___2 uu___3 uu___4 uu___5
let rec sigelt_to_string (x : FStarC_Syntax_Syntax.sigelt) : Prims.string=
  let basic =
    match x.FStarC_Syntax_Syntax.sigel with
    | FStarC_Syntax_Syntax.Sig_pragma p ->
        FStarC_Class_Show.show FStarC_Syntax_Syntax.showable_pragma p
    | FStarC_Syntax_Syntax.Sig_inductive_typ
        { FStarC_Syntax_Syntax.lid = lid; FStarC_Syntax_Syntax.us = univs;
          FStarC_Syntax_Syntax.params = tps;
          FStarC_Syntax_Syntax.num_uniform_params = uu___;
          FStarC_Syntax_Syntax.t = k; FStarC_Syntax_Syntax.mutuals = uu___1;
          FStarC_Syntax_Syntax.ds = uu___2;
          FStarC_Syntax_Syntax.injective_type_params = uu___3;_}
        ->
        let quals_str = quals_to_string' x.FStarC_Syntax_Syntax.sigquals in
        let binders_str = binders_to_string " " tps in
        let term_str = term_to_string k in
        let uu___4 = FStarC_Options.print_universes () in
        if uu___4
        then
          let uu___5 = univ_names_to_string univs in
          FStarC_Format.fmt5 "%stype %s<%s> %s : %s" quals_str
            (FStarC_Ident.string_of_lid lid) uu___5 binders_str term_str
        else
          FStarC_Format.fmt4 "%stype %s %s : %s" quals_str
            (FStarC_Ident.string_of_lid lid) binders_str term_str
    | FStarC_Syntax_Syntax.Sig_datacon
        { FStarC_Syntax_Syntax.lid1 = lid; FStarC_Syntax_Syntax.us1 = univs;
          FStarC_Syntax_Syntax.t1 = t; FStarC_Syntax_Syntax.ty_lid = uu___;
          FStarC_Syntax_Syntax.num_ty_params = uu___1;
          FStarC_Syntax_Syntax.mutuals1 = uu___2;
          FStarC_Syntax_Syntax.injective_type_params1 = uu___3;
          FStarC_Syntax_Syntax.proj_disc_lids = uu___4;_}
        ->
        let uu___5 = FStarC_Options.print_universes () in
        if uu___5
        then
          let uu___6 = univ_names_to_string univs in
          let uu___7 = term_to_string t in
          FStarC_Format.fmt3 "datacon<%s> %s : %s" uu___6
            (FStarC_Ident.string_of_lid lid) uu___7
        else
          (let uu___6 = term_to_string t in
           FStarC_Format.fmt2 "datacon %s : %s"
             (FStarC_Ident.string_of_lid lid) uu___6)
    | FStarC_Syntax_Syntax.Sig_declare_typ
        { FStarC_Syntax_Syntax.lid2 = lid; FStarC_Syntax_Syntax.us2 = univs;
          FStarC_Syntax_Syntax.t2 = t;_}
        ->
        let uu___ = quals_to_string' x.FStarC_Syntax_Syntax.sigquals in
        let uu___1 =
          let uu___2 = FStarC_Options.print_universes () in
          if uu___2
          then
            let uu___3 = univ_names_to_string univs in
            FStarC_Format.fmt1 "<%s>" uu___3
          else "" in
        let uu___2 = term_to_string t in
        FStarC_Format.fmt4 "%sval %s %s : %s" uu___
          (FStarC_Ident.string_of_lid lid) uu___1 uu___2
    | FStarC_Syntax_Syntax.Sig_assume
        { FStarC_Syntax_Syntax.lid3 = lid; FStarC_Syntax_Syntax.us3 = us;
          FStarC_Syntax_Syntax.phi1 = f;_}
        ->
        let uu___ = FStarC_Options.print_universes () in
        if uu___
        then
          let uu___1 = univ_names_to_string us in
          let uu___2 = term_to_string f in
          FStarC_Format.fmt3 "assume %s<%s> : %s"
            (FStarC_Ident.string_of_lid lid) uu___1 uu___2
        else
          (let uu___1 = term_to_string f in
           FStarC_Format.fmt2 "assume %s : %s"
             (FStarC_Ident.string_of_lid lid) uu___1)
    | FStarC_Syntax_Syntax.Sig_let
        { FStarC_Syntax_Syntax.lbs1 = lbs;
          FStarC_Syntax_Syntax.lids1 = uu___;_}
        ->
        let lbs1 =
          let uu___1 =
            FStarC_List.map
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
          let uu___2 = FStarC_List.map sigelt_to_string ses in
          FStarC_String.concat "\n" uu___2 in
        Prims.strcat "(* Sig_bundle *)" uu___1
    | FStarC_Syntax_Syntax.Sig_fail
        { FStarC_Syntax_Syntax.errs = errs;
          FStarC_Syntax_Syntax.rng1 = uu___;
          FStarC_Syntax_Syntax.fail_in_lax = lax;
          FStarC_Syntax_Syntax.ses1 = ses;_}
        ->
        let uu___1 =
          FStarC_Class_Show.show FStarC_Class_Show.showable_bool lax in
        let uu___2 =
          FStarC_Class_Show.show
            (FStarC_Class_Show.show_list FStarC_Class_Show.showable_int) errs in
        let uu___3 =
          let uu___4 = FStarC_List.map sigelt_to_string ses in
          FStarC_String.concat "\n" uu___4 in
        FStarC_Format.fmt3 "(* Sig_fail %s %s *)\n%s\n(* / Sig_fail*)\n"
          uu___1 uu___2 uu___3
    | FStarC_Syntax_Syntax.Sig_new_effect ed ->
        let uu___ = quals_to_string' x.FStarC_Syntax_Syntax.sigquals in
        let uu___1 = eff_decl_to_string ed in Prims.strcat uu___ uu___1
    | FStarC_Syntax_Syntax.Sig_sub_effect se -> sub_eff_to_string se
    | FStarC_Syntax_Syntax.Sig_effect_abbrev
        { FStarC_Syntax_Syntax.lid4 = l; FStarC_Syntax_Syntax.us4 = univs;
          FStarC_Syntax_Syntax.bs = tps; FStarC_Syntax_Syntax.comp1 = c;
          FStarC_Syntax_Syntax.cflags = flags;_}
        ->
        let uu___ = FStarC_Options.print_universes () in
        if uu___
        then
          let uu___1 =
            let uu___2 =
              FStarC_Syntax_Syntax.mk_Tm_arrow tps c
                FStarC_Range_Type.dummyRange in
            FStarC_Syntax_Subst.open_univ_vars univs uu___2 in
          (match uu___1 with
           | (univs1, t) ->
               let uu___2 = FStarC_Syntax_Util.arrow_formals_comp_ln_strict t in
               (match uu___2 with
                | (tps1, c1) ->
                    let uu___3 = sli l in
                    let uu___4 = univ_names_to_string univs1 in
                    let uu___5 = binders_to_string " " tps1 in
                    let uu___6 = comp_to_string c1 in
                    FStarC_Format.fmt4 "effect %s<%s> %s = %s" uu___3 uu___4
                      uu___5 uu___6))
        else
          (let uu___1 = sli l in
           let uu___2 = binders_to_string " " tps in
           let uu___3 = comp_to_string c in
           FStarC_Format.fmt3 "effect %s %s = %s" uu___1 uu___2 uu___3)
    | FStarC_Syntax_Syntax.Sig_splice
        { FStarC_Syntax_Syntax.is_typed = is_typed;
          FStarC_Syntax_Syntax.lids2 = lids; FStarC_Syntax_Syntax.tac = t;_}
        ->
        let uu___ =
          let uu___1 =
            FStarC_List.map
              (FStarC_Class_Show.show FStarC_Ident.showable_lident) lids in
          FStarC_String.concat "; " uu___1 in
        let uu___1 = term_to_string t in
        FStarC_Format.fmt3 "splice%s[%s] (%s)"
          (if is_typed then "_t" else "") uu___ uu___1 in
  match x.FStarC_Syntax_Syntax.sigattrs with
  | [] -> Prims.strcat "[@ ]" (Prims.strcat "\n" basic)
  | uu___ ->
      let uu___1 = attrs_to_string x.FStarC_Syntax_Syntax.sigattrs in
      Prims.strcat uu___1 (Prims.strcat "\n" basic)
