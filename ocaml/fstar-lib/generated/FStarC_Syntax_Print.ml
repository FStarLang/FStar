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
    let uu___ = FStarC_Options.print_real_names () in
    if uu___
    then
      let uu___1 =
        FStarC_Class_Show.show FStarC_Ident.showable_ident
          bv.FStarC_Syntax_Syntax.ppname in
      let uu___2 =
        let uu___3 =
          FStarC_Class_Show.show FStarC_Class_Show.showable_int
            bv.FStarC_Syntax_Syntax.index in
        Prims.strcat "#" uu___3 in
      Prims.strcat uu___1 uu___2
    else
      FStarC_Class_Show.show FStarC_Ident.showable_ident
        bv.FStarC_Syntax_Syntax.ppname
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
let (lkind_to_string : FStarC_Syntax_Syntax.lazy_kind -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | FStarC_Syntax_Syntax.BadLazy -> "BadLazy"
    | FStarC_Syntax_Syntax.Lazy_bv -> "Lazy_bv"
    | FStarC_Syntax_Syntax.Lazy_namedv -> "Lazy_namedv"
    | FStarC_Syntax_Syntax.Lazy_binder -> "Lazy_binder"
    | FStarC_Syntax_Syntax.Lazy_optionstate -> "Lazy_optionstate"
    | FStarC_Syntax_Syntax.Lazy_fvar -> "Lazy_fvar"
    | FStarC_Syntax_Syntax.Lazy_comp -> "Lazy_comp"
    | FStarC_Syntax_Syntax.Lazy_env -> "Lazy_env"
    | FStarC_Syntax_Syntax.Lazy_proofstate -> "Lazy_proofstate"
    | FStarC_Syntax_Syntax.Lazy_goal -> "Lazy_goal"
    | FStarC_Syntax_Syntax.Lazy_sigelt -> "Lazy_sigelt"
    | FStarC_Syntax_Syntax.Lazy_uvar -> "Lazy_uvar"
    | FStarC_Syntax_Syntax.Lazy_letbinding -> "Lazy_letbinding"
    | FStarC_Syntax_Syntax.Lazy_embedding (e, uu___1) ->
        let uu___2 =
          let uu___3 =
            FStarC_Class_Show.show FStarC_Syntax_Syntax.showable_emb_typ e in
          Prims.strcat uu___3 ")" in
        Prims.strcat "Lazy_embedding(" uu___2
    | FStarC_Syntax_Syntax.Lazy_universe -> "Lazy_universe"
    | FStarC_Syntax_Syntax.Lazy_universe_uvar -> "Lazy_universe_uvar"
    | FStarC_Syntax_Syntax.Lazy_issue -> "Lazy_issue"
    | FStarC_Syntax_Syntax.Lazy_ident -> "Lazy_ident"
    | FStarC_Syntax_Syntax.Lazy_doc -> "Lazy_doc"
    | FStarC_Syntax_Syntax.Lazy_extension s ->
        Prims.strcat "Lazy_extension:" s
let (term_to_string : FStarC_Syntax_Syntax.term -> Prims.string) =
  fun x ->
    let uu___ = FStarC_Options.ugly () in
    if uu___
    then FStarC_Syntax_Print_Ugly.term_to_string x
    else FStarC_Syntax_Print_Pretty.term_to_string x
let (term_to_string' :
  FStarC_Syntax_DsEnv.env -> FStarC_Syntax_Syntax.term -> Prims.string) =
  fun env ->
    fun x ->
      let uu___ = FStarC_Options.ugly () in
      if uu___
      then FStarC_Syntax_Print_Ugly.term_to_string x
      else FStarC_Syntax_Print_Pretty.term_to_string' env x
let (comp_to_string : FStarC_Syntax_Syntax.comp -> Prims.string) =
  fun c ->
    let uu___ = FStarC_Options.ugly () in
    if uu___
    then FStarC_Syntax_Print_Ugly.comp_to_string c
    else FStarC_Syntax_Print_Pretty.comp_to_string c
let (comp_to_string' :
  FStarC_Syntax_DsEnv.env -> FStarC_Syntax_Syntax.comp -> Prims.string) =
  fun env ->
    fun c ->
      let uu___ = FStarC_Options.ugly () in
      if uu___
      then FStarC_Syntax_Print_Ugly.comp_to_string c
      else FStarC_Syntax_Print_Pretty.comp_to_string' env c
let (sigelt_to_string : FStarC_Syntax_Syntax.sigelt -> Prims.string) =
  fun x ->
    let uu___ = FStarC_Options.ugly () in
    if uu___
    then FStarC_Syntax_Print_Ugly.sigelt_to_string x
    else FStarC_Syntax_Print_Pretty.sigelt_to_string x
let (sigelt_to_string' :
  FStarC_Syntax_DsEnv.env -> FStarC_Syntax_Syntax.sigelt -> Prims.string) =
  fun env ->
    fun x ->
      let uu___ = FStarC_Options.ugly () in
      if uu___
      then FStarC_Syntax_Print_Ugly.sigelt_to_string x
      else FStarC_Syntax_Print_Pretty.sigelt_to_string' env x
let (pat_to_string : FStarC_Syntax_Syntax.pat -> Prims.string) =
  fun x ->
    let uu___ = FStarC_Options.ugly () in
    if uu___
    then FStarC_Syntax_Print_Ugly.pat_to_string x
    else FStarC_Syntax_Print_Pretty.pat_to_string x
let (term_to_doc' :
  FStarC_Syntax_DsEnv.env ->
    FStarC_Syntax_Syntax.term -> FStarC_Pprint.document)
  =
  fun dsenv ->
    fun t ->
      let uu___ = FStarC_Options.ugly () in
      if uu___
      then
        let uu___1 = FStarC_Syntax_Print_Ugly.term_to_string t in
        FStarC_Pprint.arbitrary_string uu___1
      else FStarC_Syntax_Print_Pretty.term_to_doc' dsenv t
let (univ_to_doc' :
  FStarC_Syntax_DsEnv.env ->
    FStarC_Syntax_Syntax.universe -> FStarC_Pprint.document)
  =
  fun dsenv ->
    fun t ->
      let uu___ = FStarC_Options.ugly () in
      if uu___
      then
        let uu___1 = FStarC_Syntax_Print_Ugly.univ_to_string t in
        FStarC_Pprint.arbitrary_string uu___1
      else FStarC_Syntax_Print_Pretty.univ_to_doc' dsenv t
let (comp_to_doc' :
  FStarC_Syntax_DsEnv.env ->
    FStarC_Syntax_Syntax.comp -> FStarC_Pprint.document)
  =
  fun dsenv ->
    fun t ->
      let uu___ = FStarC_Options.ugly () in
      if uu___
      then
        let uu___1 = FStarC_Syntax_Print_Ugly.comp_to_string t in
        FStarC_Pprint.arbitrary_string uu___1
      else FStarC_Syntax_Print_Pretty.comp_to_doc' dsenv t
let (sigelt_to_doc' :
  FStarC_Syntax_DsEnv.env ->
    FStarC_Syntax_Syntax.sigelt -> FStarC_Pprint.document)
  =
  fun dsenv ->
    fun t ->
      let uu___ = FStarC_Options.ugly () in
      if uu___
      then
        let uu___1 = FStarC_Syntax_Print_Ugly.sigelt_to_string t in
        FStarC_Pprint.arbitrary_string uu___1
      else FStarC_Syntax_Print_Pretty.sigelt_to_doc' dsenv t
let (term_to_doc : FStarC_Syntax_Syntax.term -> FStarC_Pprint.document) =
  fun t ->
    let uu___ = FStarC_Options.ugly () in
    if uu___
    then
      let uu___1 = FStarC_Syntax_Print_Ugly.term_to_string t in
      FStarC_Pprint.arbitrary_string uu___1
    else FStarC_Syntax_Print_Pretty.term_to_doc t
let (univ_to_doc : FStarC_Syntax_Syntax.universe -> FStarC_Pprint.document) =
  fun t ->
    let uu___ = FStarC_Options.ugly () in
    if uu___
    then
      let uu___1 = FStarC_Syntax_Print_Ugly.univ_to_string t in
      FStarC_Pprint.arbitrary_string uu___1
    else FStarC_Syntax_Print_Pretty.univ_to_doc t
let (comp_to_doc : FStarC_Syntax_Syntax.comp -> FStarC_Pprint.document) =
  fun t ->
    let uu___ = FStarC_Options.ugly () in
    if uu___
    then
      let uu___1 = FStarC_Syntax_Print_Ugly.comp_to_string t in
      FStarC_Pprint.arbitrary_string uu___1
    else FStarC_Syntax_Print_Pretty.comp_to_doc t
let (sigelt_to_doc : FStarC_Syntax_Syntax.sigelt -> FStarC_Pprint.document) =
  fun t ->
    let uu___ = FStarC_Options.ugly () in
    if uu___
    then
      let uu___1 = FStarC_Syntax_Print_Ugly.sigelt_to_string t in
      FStarC_Pprint.arbitrary_string uu___1
    else FStarC_Syntax_Print_Pretty.sigelt_to_doc t
let (binder_to_string : FStarC_Syntax_Syntax.binder -> Prims.string) =
  fun b ->
    let uu___ = FStarC_Options.ugly () in
    if uu___
    then FStarC_Syntax_Print_Pretty.binder_to_string' false b
    else FStarC_Syntax_Print_Ugly.binder_to_string b
let (aqual_to_string : FStarC_Syntax_Syntax.aqual -> Prims.string) =
  fun q ->
    match q with
    | FStar_Pervasives_Native.Some
        { FStarC_Syntax_Syntax.aqual_implicit = true;
          FStarC_Syntax_Syntax.aqual_attributes = uu___;_}
        -> "#"
    | uu___ -> ""
let (bqual_to_string' :
  Prims.string -> FStarC_Syntax_Syntax.bqual -> Prims.string) =
  fun s ->
    fun b ->
      match b with
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
          let uu___ =
            let uu___1 = term_to_string t in
            Prims.strcat uu___1 (Prims.strcat "]" s) in
          Prims.strcat "#[" uu___
      | FStar_Pervasives_Native.None -> s
let (bqual_to_string : FStarC_Syntax_Syntax.bqual -> Prims.string) =
  fun q -> bqual_to_string' "" q
let (subst_elt_to_string : FStarC_Syntax_Syntax.subst_elt -> Prims.string) =
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
let (modul_to_string : FStarC_Syntax_Syntax.modul -> Prims.string) =
  fun m ->
    let uu___ =
      FStarC_Class_Show.show FStarC_Ident.showable_lident
        m.FStarC_Syntax_Syntax.name in
    let uu___1 =
      let uu___2 =
        FStarC_Compiler_List.map sigelt_to_string
          m.FStarC_Syntax_Syntax.declarations in
      FStarC_Compiler_String.concat "\n" uu___2 in
    FStarC_Compiler_Util.format2 "module %s\nDeclarations: [\n%s\n]\n" uu___
      uu___1
let (metadata_to_string : FStarC_Syntax_Syntax.metadata -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | FStarC_Syntax_Syntax.Meta_pattern (uu___1, ps) ->
        let pats =
          let uu___2 =
            FStarC_Compiler_List.map
              (fun args ->
                 let uu___3 =
                   FStarC_Compiler_List.map
                     (fun uu___4 ->
                        match uu___4 with | (t, uu___5) -> term_to_string t)
                     args in
                 FStarC_Compiler_String.concat "; " uu___3) ps in
          FStarC_Compiler_String.concat "\\/" uu___2 in
        FStarC_Compiler_Util.format1 "{Meta_pattern %s}" pats
    | FStarC_Syntax_Syntax.Meta_named lid ->
        let uu___1 = sli lid in
        FStarC_Compiler_Util.format1 "{Meta_named %s}" uu___1
    | FStarC_Syntax_Syntax.Meta_labeled (l, r, uu___1) ->
        let uu___2 = FStarC_Errors_Msg.rendermsg l in
        let uu___3 = FStarC_Compiler_Range_Ops.string_of_range r in
        FStarC_Compiler_Util.format2 "{Meta_labeled (%s, %s)}" uu___2 uu___3
    | FStarC_Syntax_Syntax.Meta_desugared msi -> "{Meta_desugared}"
    | FStarC_Syntax_Syntax.Meta_monadic (m, t) ->
        let uu___1 = sli m in
        let uu___2 = term_to_string t in
        FStarC_Compiler_Util.format2 "{Meta_monadic(%s @ %s)}" uu___1 uu___2
    | FStarC_Syntax_Syntax.Meta_monadic_lift (m, m', t) ->
        let uu___1 = sli m in
        let uu___2 = sli m' in
        let uu___3 = term_to_string t in
        FStarC_Compiler_Util.format3 "{Meta_monadic_lift(%s -> %s @ %s)}"
          uu___1 uu___2 uu___3
let (showable_term : FStarC_Syntax_Syntax.term FStarC_Class_Show.showable) =
  { FStarC_Class_Show.show = term_to_string }
let (showable_univ :
  FStarC_Syntax_Syntax.universe FStarC_Class_Show.showable) =
  { FStarC_Class_Show.show = univ_to_string }
let (showable_comp : FStarC_Syntax_Syntax.comp FStarC_Class_Show.showable) =
  { FStarC_Class_Show.show = comp_to_string }
let (showable_sigelt :
  FStarC_Syntax_Syntax.sigelt FStarC_Class_Show.showable) =
  { FStarC_Class_Show.show = sigelt_to_string }
let (showable_bv : FStarC_Syntax_Syntax.bv FStarC_Class_Show.showable) =
  { FStarC_Class_Show.show = bv_to_string }
let (showable_fv : FStarC_Syntax_Syntax.fv FStarC_Class_Show.showable) =
  { FStarC_Class_Show.show = fv_to_string }
let (showable_binder :
  FStarC_Syntax_Syntax.binder FStarC_Class_Show.showable) =
  { FStarC_Class_Show.show = binder_to_string }
let (showable_uvar : FStarC_Syntax_Syntax.uvar FStarC_Class_Show.showable) =
  { FStarC_Class_Show.show = uvar_to_string }
let (ctx_uvar_to_string : FStarC_Syntax_Syntax.ctx_uvar -> Prims.string) =
  fun ctx_uvar ->
    let reason_string =
      FStarC_Compiler_Util.format1 "(* %s *)\n"
        ctx_uvar.FStarC_Syntax_Syntax.ctx_uvar_reason in
    let uu___ =
      let uu___1 =
        FStarC_Compiler_List.map (FStarC_Class_Show.show showable_binder)
          ctx_uvar.FStarC_Syntax_Syntax.ctx_uvar_binders in
      FStarC_Compiler_String.concat ", " uu___1 in
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
let (showable_ctxu :
  FStarC_Syntax_Syntax.ctx_uvar FStarC_Class_Show.showable) =
  { FStarC_Class_Show.show = ctx_uvar_to_string }
let (showable_binding :
  FStarC_Syntax_Syntax.binding FStarC_Class_Show.showable) =
  {
    FStarC_Class_Show.show =
      (fun uu___ ->
         match uu___ with
         | FStarC_Syntax_Syntax.Binding_var x ->
             let uu___1 = FStarC_Class_Show.show showable_bv x in
             Prims.strcat "Binding_var " uu___1
         | FStarC_Syntax_Syntax.Binding_lid x ->
             let uu___1 =
               FStarC_Class_Show.show
                 (FStarC_Class_Show.show_tuple2 FStarC_Ident.showable_lident
                    (FStarC_Class_Show.show_tuple2
                       (FStarC_Class_Show.show_list
                          FStarC_Ident.showable_ident) showable_term)) x in
             Prims.strcat "Binding_lid " uu___1
         | FStarC_Syntax_Syntax.Binding_univ x ->
             let uu___1 =
               FStarC_Class_Show.show FStarC_Ident.showable_ident x in
             Prims.strcat "Binding_univ " uu___1)
  }
let (showable_subst_elt :
  FStarC_Syntax_Syntax.subst_elt FStarC_Class_Show.showable) =
  { FStarC_Class_Show.show = subst_elt_to_string }
let (showable_branch :
  FStarC_Syntax_Syntax.branch FStarC_Class_Show.showable) =
  { FStarC_Class_Show.show = FStarC_Syntax_Print_Ugly.branch_to_string }
let (showable_qualifier :
  FStarC_Syntax_Syntax.qualifier FStarC_Class_Show.showable) =
  { FStarC_Class_Show.show = qual_to_string }
let (showable_pat : FStarC_Syntax_Syntax.pat FStarC_Class_Show.showable) =
  { FStarC_Class_Show.show = pat_to_string }
let (showable_const : FStarC_Const.sconst FStarC_Class_Show.showable) =
  { FStarC_Class_Show.show = const_to_string }
let (showable_letbinding :
  FStarC_Syntax_Syntax.letbinding FStarC_Class_Show.showable) =
  { FStarC_Class_Show.show = FStarC_Syntax_Print_Ugly.lb_to_string }
let (showable_modul : FStarC_Syntax_Syntax.modul FStarC_Class_Show.showable)
  = { FStarC_Class_Show.show = modul_to_string }
let (showable_metadata :
  FStarC_Syntax_Syntax.metadata FStarC_Class_Show.showable) =
  { FStarC_Class_Show.show = metadata_to_string }
let (showable_ctx_uvar_meta :
  FStarC_Syntax_Syntax.ctx_uvar_meta_t FStarC_Class_Show.showable) =
  {
    FStarC_Class_Show.show =
      (fun uu___ ->
         match uu___ with
         | FStarC_Syntax_Syntax.Ctx_uvar_meta_attr attr ->
             let uu___1 = FStarC_Class_Show.show showable_term attr in
             Prims.strcat "Ctx_uvar_meta_attr " uu___1
         | FStarC_Syntax_Syntax.Ctx_uvar_meta_tac r ->
             let uu___1 = FStarC_Class_Show.show showable_term r in
             Prims.strcat "Ctx_uvar_meta_tac " uu___1)
  }
let (showable_aqual : FStarC_Syntax_Syntax.aqual FStarC_Class_Show.showable)
  = { FStarC_Class_Show.show = aqual_to_string }
let (tscheme_to_string : FStarC_Syntax_Syntax.tscheme -> Prims.string) =
  fun ts ->
    let uu___ = FStarC_Options.ugly () in
    if uu___
    then FStarC_Syntax_Print_Ugly.tscheme_to_string ts
    else FStarC_Syntax_Print_Pretty.tscheme_to_string ts
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
let (showable_sub_eff :
  FStarC_Syntax_Syntax.sub_eff FStarC_Class_Show.showable) =
  { FStarC_Class_Show.show = sub_eff_to_string }
let (pretty_term : FStarC_Syntax_Syntax.term FStarC_Class_PP.pretty) =
  { FStarC_Class_PP.pp = term_to_doc }
let (pretty_univ : FStarC_Syntax_Syntax.universe FStarC_Class_PP.pretty) =
  { FStarC_Class_PP.pp = univ_to_doc }
let (pretty_sigelt : FStarC_Syntax_Syntax.sigelt FStarC_Class_PP.pretty) =
  { FStarC_Class_PP.pp = sigelt_to_doc }
let (pretty_comp : FStarC_Syntax_Syntax.comp FStarC_Class_PP.pretty) =
  { FStarC_Class_PP.pp = comp_to_doc }
let (pretty_ctxu : FStarC_Syntax_Syntax.ctx_uvar FStarC_Class_PP.pretty) =
  {
    FStarC_Class_PP.pp =
      (fun x ->
         let uu___ = FStarC_Class_Show.show showable_ctxu x in
         FStarC_Pprint.doc_of_string uu___)
  }
let (pretty_uvar : FStarC_Syntax_Syntax.uvar FStarC_Class_PP.pretty) =
  {
    FStarC_Class_PP.pp =
      (fun x ->
         let uu___ = FStarC_Class_Show.show showable_uvar x in
         FStarC_Pprint.doc_of_string uu___)
  }
let (pretty_binder : FStarC_Syntax_Syntax.binder FStarC_Class_PP.pretty) =
  {
    FStarC_Class_PP.pp =
      (fun x ->
         let uu___ = FStarC_Class_Show.show showable_binder x in
         FStarC_Pprint.doc_of_string uu___)
  }
let (pretty_bv : FStarC_Syntax_Syntax.bv FStarC_Class_PP.pretty) =
  {
    FStarC_Class_PP.pp =
      (fun x ->
         let uu___ = FStarC_Class_Show.show showable_bv x in
         FStarC_Pprint.doc_of_string uu___)
  }
let (pretty_binding : FStarC_Syntax_Syntax.binding FStarC_Class_PP.pretty) =
  {
    FStarC_Class_PP.pp =
      (fun uu___ ->
         match uu___ with
         | FStarC_Syntax_Syntax.Binding_var bv ->
             FStarC_Class_PP.pp pretty_bv bv
         | FStarC_Syntax_Syntax.Binding_lid (l, (us, t)) ->
             let uu___1 = FStarC_Class_PP.pp FStarC_Ident.pretty_lident l in
             let uu___2 =
               let uu___3 = FStarC_Class_PP.pp pretty_term t in
               FStarC_Pprint.op_Hat_Hat FStarC_Pprint.colon uu___3 in
             FStarC_Pprint.op_Hat_Hat uu___1 uu___2
         | FStarC_Syntax_Syntax.Binding_univ u ->
             FStarC_Class_PP.pp FStarC_Ident.pretty_ident u)
  }
let rec (sigelt_to_string_short :
  FStarC_Syntax_Syntax.sigelt -> Prims.string) =
  fun x ->
    match x.FStarC_Syntax_Syntax.sigel with
    | FStarC_Syntax_Syntax.Sig_pragma p ->
        FStarC_Class_Show.show FStarC_Syntax_Syntax.showable_pragma p
    | FStarC_Syntax_Syntax.Sig_let
        {
          FStarC_Syntax_Syntax.lbs1 =
            (false,
             { FStarC_Syntax_Syntax.lbname = lb;
               FStarC_Syntax_Syntax.lbunivs = uu___;
               FStarC_Syntax_Syntax.lbtyp = uu___1;
               FStarC_Syntax_Syntax.lbeff = uu___2;
               FStarC_Syntax_Syntax.lbdef = uu___3;
               FStarC_Syntax_Syntax.lbattrs = uu___4;
               FStarC_Syntax_Syntax.lbpos = uu___5;_}::[]);
          FStarC_Syntax_Syntax.lids1 = uu___6;_}
        ->
        let uu___7 = lbname_to_string lb in
        FStarC_Compiler_Util.format1 "let %s" uu___7
    | FStarC_Syntax_Syntax.Sig_let
        {
          FStarC_Syntax_Syntax.lbs1 =
            (true,
             { FStarC_Syntax_Syntax.lbname = lb;
               FStarC_Syntax_Syntax.lbunivs = uu___;
               FStarC_Syntax_Syntax.lbtyp = uu___1;
               FStarC_Syntax_Syntax.lbeff = uu___2;
               FStarC_Syntax_Syntax.lbdef = uu___3;
               FStarC_Syntax_Syntax.lbattrs = uu___4;
               FStarC_Syntax_Syntax.lbpos = uu___5;_}::[]);
          FStarC_Syntax_Syntax.lids1 = uu___6;_}
        ->
        let uu___7 = lbname_to_string lb in
        FStarC_Compiler_Util.format1 "let rec %s" uu___7
    | FStarC_Syntax_Syntax.Sig_let
        { FStarC_Syntax_Syntax.lbs1 = (true, lbs);
          FStarC_Syntax_Syntax.lids1 = uu___;_}
        ->
        let uu___1 =
          let uu___2 =
            FStarC_Compiler_List.map
              (fun lb -> lbname_to_string lb.FStarC_Syntax_Syntax.lbname) lbs in
          FStarC_Compiler_String.concat " and " uu___2 in
        FStarC_Compiler_Util.format1 "let rec %s" uu___1
    | FStarC_Syntax_Syntax.Sig_let uu___ ->
        failwith "Impossible: sigelt_to_string_short, ill-formed let"
    | FStarC_Syntax_Syntax.Sig_declare_typ
        { FStarC_Syntax_Syntax.lid2 = lid; FStarC_Syntax_Syntax.us2 = uu___;
          FStarC_Syntax_Syntax.t2 = uu___1;_}
        ->
        let uu___2 = FStarC_Ident.string_of_lid lid in
        FStarC_Compiler_Util.format1 "val %s" uu___2
    | FStarC_Syntax_Syntax.Sig_inductive_typ
        { FStarC_Syntax_Syntax.lid = lid; FStarC_Syntax_Syntax.us = uu___;
          FStarC_Syntax_Syntax.params = uu___1;
          FStarC_Syntax_Syntax.num_uniform_params = uu___2;
          FStarC_Syntax_Syntax.t = uu___3;
          FStarC_Syntax_Syntax.mutuals = uu___4;
          FStarC_Syntax_Syntax.ds = uu___5;
          FStarC_Syntax_Syntax.injective_type_params = uu___6;_}
        ->
        let uu___7 = FStarC_Ident.string_of_lid lid in
        FStarC_Compiler_Util.format1 "type %s" uu___7
    | FStarC_Syntax_Syntax.Sig_datacon
        { FStarC_Syntax_Syntax.lid1 = lid; FStarC_Syntax_Syntax.us1 = uu___;
          FStarC_Syntax_Syntax.t1 = uu___1;
          FStarC_Syntax_Syntax.ty_lid = t_lid;
          FStarC_Syntax_Syntax.num_ty_params = uu___2;
          FStarC_Syntax_Syntax.mutuals1 = uu___3;
          FStarC_Syntax_Syntax.injective_type_params1 = uu___4;_}
        ->
        let uu___5 = FStarC_Ident.string_of_lid lid in
        let uu___6 = FStarC_Ident.string_of_lid t_lid in
        FStarC_Compiler_Util.format2 "datacon %s for type %s" uu___5 uu___6
    | FStarC_Syntax_Syntax.Sig_assume
        { FStarC_Syntax_Syntax.lid3 = lid; FStarC_Syntax_Syntax.us3 = uu___;
          FStarC_Syntax_Syntax.phi1 = uu___1;_}
        ->
        let uu___2 = FStarC_Ident.string_of_lid lid in
        FStarC_Compiler_Util.format1 "assume %s" uu___2
    | FStarC_Syntax_Syntax.Sig_bundle
        { FStarC_Syntax_Syntax.ses = ses;
          FStarC_Syntax_Syntax.lids = uu___;_}
        ->
        let uu___1 = FStarC_Compiler_List.hd ses in
        sigelt_to_string_short uu___1
    | FStarC_Syntax_Syntax.Sig_fail
        { FStarC_Syntax_Syntax.errs = uu___;
          FStarC_Syntax_Syntax.fail_in_lax = uu___1;
          FStarC_Syntax_Syntax.ses1 = ses;_}
        ->
        let uu___2 =
          let uu___3 = FStarC_Compiler_List.hd ses in
          sigelt_to_string_short uu___3 in
        FStarC_Compiler_Util.format1 "[@@expect_failure] %s" uu___2
    | FStarC_Syntax_Syntax.Sig_new_effect ed ->
        let kw =
          let uu___ = FStarC_Syntax_Util.is_layered ed in
          if uu___
          then "layered_effect"
          else
            (let uu___2 = FStarC_Syntax_Util.is_dm4f ed in
             if uu___2 then "new_effect_for_free" else "new_effect") in
        let uu___ = lid_to_string ed.FStarC_Syntax_Syntax.mname in
        FStarC_Compiler_Util.format2 "%s { %s ... }" kw uu___
    | FStarC_Syntax_Syntax.Sig_sub_effect se ->
        let uu___ = lid_to_string se.FStarC_Syntax_Syntax.source in
        let uu___1 = lid_to_string se.FStarC_Syntax_Syntax.target in
        FStarC_Compiler_Util.format2 "sub_effect %s ~> %s" uu___ uu___1
    | FStarC_Syntax_Syntax.Sig_effect_abbrev
        { FStarC_Syntax_Syntax.lid4 = l; FStarC_Syntax_Syntax.us4 = uu___;
          FStarC_Syntax_Syntax.bs2 = tps; FStarC_Syntax_Syntax.comp1 = c;
          FStarC_Syntax_Syntax.cflags = uu___1;_}
        ->
        let uu___2 = sli l in
        let uu___3 =
          let uu___4 =
            FStarC_Compiler_List.map (FStarC_Class_Show.show showable_binder)
              tps in
          FStarC_Compiler_String.concat " " uu___4 in
        let uu___4 = FStarC_Class_Show.show showable_comp c in
        FStarC_Compiler_Util.format3 "effect %s %s = %s" uu___2 uu___3 uu___4
    | FStarC_Syntax_Syntax.Sig_splice
        { FStarC_Syntax_Syntax.is_typed = is_typed;
          FStarC_Syntax_Syntax.lids2 = lids;
          FStarC_Syntax_Syntax.tac = uu___;_}
        ->
        let uu___1 =
          let uu___2 =
            FStarC_Compiler_List.map FStarC_Ident.string_of_lid lids in
          FStarC_Compiler_String.concat "; " uu___2 in
        FStarC_Compiler_Util.format3 "%splice%s[%s] (...)" "%s"
          (if is_typed then "_t" else "") uu___1
    | FStarC_Syntax_Syntax.Sig_polymonadic_bind
        { FStarC_Syntax_Syntax.m_lid = m; FStarC_Syntax_Syntax.n_lid = n;
          FStarC_Syntax_Syntax.p_lid = p; FStarC_Syntax_Syntax.tm3 = uu___;
          FStarC_Syntax_Syntax.typ = uu___1;
          FStarC_Syntax_Syntax.kind1 = uu___2;_}
        ->
        let uu___3 = FStarC_Ident.string_of_lid m in
        let uu___4 = FStarC_Ident.string_of_lid n in
        let uu___5 = FStarC_Ident.string_of_lid p in
        FStarC_Compiler_Util.format3 "polymonadic_bind (%s, %s) |> %s" uu___3
          uu___4 uu___5
    | FStarC_Syntax_Syntax.Sig_polymonadic_subcomp
        { FStarC_Syntax_Syntax.m_lid1 = m; FStarC_Syntax_Syntax.n_lid1 = n;
          FStarC_Syntax_Syntax.tm4 = uu___;
          FStarC_Syntax_Syntax.typ1 = uu___1;
          FStarC_Syntax_Syntax.kind2 = uu___2;_}
        ->
        let uu___3 = FStarC_Ident.string_of_lid m in
        let uu___4 = FStarC_Ident.string_of_lid n in
        FStarC_Compiler_Util.format2 "polymonadic_subcomp %s <: %s" uu___3
          uu___4
let (binder_to_json :
  FStarC_Syntax_DsEnv.env -> FStarC_Syntax_Syntax.binder -> FStarC_Json.json)
  =
  fun env ->
    fun b ->
      let n =
        let uu___ =
          let uu___1 = nm_to_string b.FStarC_Syntax_Syntax.binder_bv in
          bqual_to_string' uu___1 b.FStarC_Syntax_Syntax.binder_qual in
        FStarC_Json.JsonStr uu___ in
      let t =
        let uu___ =
          term_to_string' env
            (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
        FStarC_Json.JsonStr uu___ in
      FStarC_Json.JsonAssoc [("name", n); ("type", t)]
let (binders_to_json :
  FStarC_Syntax_DsEnv.env -> FStarC_Syntax_Syntax.binders -> FStarC_Json.json)
  =
  fun env ->
    fun bs ->
      let uu___ = FStarC_Compiler_List.map (binder_to_json env) bs in
      FStarC_Json.JsonList uu___
let (eff_decl_to_string : FStarC_Syntax_Syntax.eff_decl -> Prims.string) =
  fun ed ->
    let uu___ = FStarC_Options.ugly () in
    if uu___
    then FStarC_Syntax_Print_Ugly.eff_decl_to_string ed
    else FStarC_Syntax_Print_Pretty.eff_decl_to_string ed
let (showable_eff_decl :
  FStarC_Syntax_Syntax.eff_decl FStarC_Class_Show.showable) =
  { FStarC_Class_Show.show = eff_decl_to_string }
let (args_to_string : FStarC_Syntax_Syntax.args -> Prims.string) =
  fun args ->
    let uu___ =
      FStarC_Compiler_List.map
        (fun uu___1 ->
           match uu___1 with
           | (a, q) ->
               let uu___2 = aqual_to_string q in
               let uu___3 = term_to_string a in Prims.strcat uu___2 uu___3)
        args in
    FStarC_Compiler_String.concat " " uu___
let (showable_decreases_order :
  FStarC_Syntax_Syntax.decreases_order FStarC_Class_Show.showable) =
  {
    FStarC_Class_Show.show =
      (fun uu___ ->
         match uu___ with
         | FStarC_Syntax_Syntax.Decreases_lex l ->
             let uu___1 =
               FStarC_Class_Show.show
                 (FStarC_Class_Show.show_list showable_term) l in
             Prims.strcat "Decreases_lex " uu___1
         | FStarC_Syntax_Syntax.Decreases_wf l ->
             let uu___1 =
               FStarC_Class_Show.show
                 (FStarC_Class_Show.show_tuple2 showable_term showable_term)
                 l in
             Prims.strcat "Decreases_wf " uu___1)
  }
let (cflag_to_string : FStarC_Syntax_Syntax.cflag -> Prims.string) =
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
    | FStarC_Syntax_Syntax.DECREASES do1 ->
        let uu___ = FStarC_Class_Show.show showable_decreases_order do1 in
        Prims.strcat "decreases " uu___
let (showable_cflag : FStarC_Syntax_Syntax.cflag FStarC_Class_Show.showable)
  = { FStarC_Class_Show.show = cflag_to_string }
let (binder_to_string_with_type :
  FStarC_Syntax_Syntax.binder -> Prims.string) =
  fun b ->
    let uu___ = FStarC_Options.ugly () in
    if uu___
    then
      let attrs =
        match b.FStarC_Syntax_Syntax.binder_attrs with
        | [] -> ""
        | ts ->
            let uu___1 =
              let uu___2 =
                let uu___3 =
                  FStarC_Compiler_List.map
                    (FStarC_Class_Show.show showable_term) ts in
                FStarC_Compiler_String.concat ", " uu___3 in
              Prims.strcat uu___2 "] " in
            Prims.strcat "[@@@" uu___1 in
      let uu___1 = FStarC_Syntax_Syntax.is_null_binder b in
      (if uu___1
       then
         let uu___2 =
           let uu___3 =
             term_to_string
               (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
           Prims.strcat "_:" uu___3 in
         Prims.strcat attrs uu___2
       else
         (let uu___3 =
            let uu___4 =
              let uu___5 = nm_to_string b.FStarC_Syntax_Syntax.binder_bv in
              let uu___6 =
                let uu___7 =
                  term_to_string
                    (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
                Prims.strcat ": " uu___7 in
              Prims.strcat uu___5 uu___6 in
            Prims.strcat attrs uu___4 in
          bqual_to_string' uu___3 b.FStarC_Syntax_Syntax.binder_qual))
    else FStarC_Syntax_Print_Pretty.binder_to_string' false b