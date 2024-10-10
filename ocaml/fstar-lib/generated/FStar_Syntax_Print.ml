open Prims
let (sli : FStar_Ident.lident -> Prims.string) =
  fun l ->
    let uu___ = FStar_Options.print_real_names () in
    if uu___
    then FStar_Ident.string_of_lid l
    else
      (let uu___2 = FStar_Ident.ident_of_lid l in
       FStar_Ident.string_of_id uu___2)
let (lid_to_string : FStar_Ident.lid -> Prims.string) = fun l -> sli l
let (fv_to_string : FStar_Syntax_Syntax.fv -> Prims.string) =
  fun fv ->
    lid_to_string (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
let (bv_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv ->
    let uu___ = FStar_Options.print_real_names () in
    if uu___
    then
      let uu___1 =
        FStar_Class_Show.show FStar_Ident.showable_ident
          bv.FStar_Syntax_Syntax.ppname in
      let uu___2 =
        let uu___3 =
          FStar_Class_Show.show
            (FStar_Class_Show.printableshow
               FStar_Class_Printable.printable_int)
            bv.FStar_Syntax_Syntax.index in
        Prims.strcat "#" uu___3 in
      Prims.strcat uu___1 uu___2
    else
      FStar_Class_Show.show FStar_Ident.showable_ident
        bv.FStar_Syntax_Syntax.ppname
let (nm_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv ->
    let uu___ = FStar_Options.print_real_names () in
    if uu___
    then bv_to_string bv
    else FStar_Ident.string_of_id bv.FStar_Syntax_Syntax.ppname
let (db_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv ->
    let uu___ = FStar_Ident.string_of_id bv.FStar_Syntax_Syntax.ppname in
    let uu___1 =
      let uu___2 =
        FStar_Compiler_Util.string_of_int bv.FStar_Syntax_Syntax.index in
      Prims.strcat "@" uu___2 in
    Prims.strcat uu___ uu___1
let (filter_imp :
  FStar_Syntax_Syntax.binder_qualifier FStar_Pervasives_Native.option ->
    Prims.bool)
  =
  fun aq ->
    match aq with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t) when
        FStar_Syntax_Util.is_fvar FStar_Parser_Const.tcresolve_lid t -> true
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit uu___) ->
        false
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta uu___) -> false
    | uu___ -> true
let filter_imp_args :
  'uuuuu .
    ('uuuuu * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list ->
      ('uuuuu * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list
  =
  fun args ->
    FStar_Compiler_List.filter
      (fun uu___ ->
         match uu___ with
         | (uu___1, FStar_Pervasives_Native.None) -> true
         | (uu___1, FStar_Pervasives_Native.Some a) ->
             Prims.op_Negation a.FStar_Syntax_Syntax.aqual_implicit) args
let (filter_imp_binders :
  FStar_Syntax_Syntax.binder Prims.list ->
    FStar_Syntax_Syntax.binder Prims.list)
  =
  fun bs ->
    FStar_Compiler_List.filter
      (fun b -> filter_imp b.FStar_Syntax_Syntax.binder_qual) bs
let (const_to_string : FStar_Const.sconst -> Prims.string) =
  FStar_Parser_Const.const_to_string
let (lbname_to_string :
  (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.fv) FStar_Pervasives.either ->
    Prims.string)
  =
  fun uu___ ->
    match uu___ with
    | FStar_Pervasives.Inl l -> bv_to_string l
    | FStar_Pervasives.Inr l ->
        lid_to_string (l.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
let (uvar_to_string : FStar_Syntax_Syntax.uvar -> Prims.string) =
  fun u ->
    let uu___ = FStar_Options.hide_uvar_nums () in
    if uu___
    then "?"
    else
      (let uu___2 =
         let uu___3 = FStar_Syntax_Unionfind.uvar_id u in
         FStar_Compiler_Util.string_of_int uu___3 in
       Prims.strcat "?" uu___2)
let (version_to_string : FStar_Syntax_Syntax.version -> Prims.string) =
  fun v ->
    let uu___ = FStar_Compiler_Util.string_of_int v.FStar_Syntax_Syntax.major in
    let uu___1 =
      FStar_Compiler_Util.string_of_int v.FStar_Syntax_Syntax.minor in
    FStar_Compiler_Util.format2 "%s.%s" uu___ uu___1
let (univ_uvar_to_string :
  (FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
    FStar_Unionfind.p_uvar * FStar_Syntax_Syntax.version *
    FStar_Compiler_Range_Type.range) -> Prims.string)
  =
  fun u ->
    let uu___ = FStar_Options.hide_uvar_nums () in
    if uu___
    then "?"
    else
      (let uu___2 =
         let uu___3 =
           let uu___4 = FStar_Syntax_Unionfind.univ_uvar_id u in
           FStar_Compiler_Util.string_of_int uu___4 in
         let uu___4 =
           let uu___5 =
             match u with | (uu___6, u1, uu___7) -> version_to_string u1 in
           Prims.strcat ":" uu___5 in
         Prims.strcat uu___3 uu___4 in
       Prims.strcat "?" uu___2)
let rec (int_of_univ :
  Prims.int ->
    FStar_Syntax_Syntax.universe ->
      (Prims.int * FStar_Syntax_Syntax.universe
        FStar_Pervasives_Native.option))
  =
  fun n ->
    fun u ->
      let uu___ = FStar_Syntax_Subst.compress_univ u in
      match uu___ with
      | FStar_Syntax_Syntax.U_zero -> (n, FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.U_succ u1 -> int_of_univ (n + Prims.int_one) u1
      | uu___1 -> (n, (FStar_Pervasives_Native.Some u))
let rec (univ_to_string : FStar_Syntax_Syntax.universe -> Prims.string) =
  fun u ->
    FStar_Errors.with_ctx "While printing universe"
      (fun uu___ ->
         let uu___1 = FStar_Syntax_Subst.compress_univ u in
         match uu___1 with
         | FStar_Syntax_Syntax.U_unif u1 ->
             let uu___2 = univ_uvar_to_string u1 in
             Prims.strcat "U_unif " uu___2
         | FStar_Syntax_Syntax.U_name x ->
             let uu___2 = FStar_Ident.string_of_id x in
             Prims.strcat "U_name " uu___2
         | FStar_Syntax_Syntax.U_bvar x ->
             let uu___2 = FStar_Compiler_Util.string_of_int x in
             Prims.strcat "@" uu___2
         | FStar_Syntax_Syntax.U_zero -> "0"
         | FStar_Syntax_Syntax.U_succ u1 ->
             let uu___2 = int_of_univ Prims.int_one u1 in
             (match uu___2 with
              | (n, FStar_Pervasives_Native.None) ->
                  FStar_Compiler_Util.string_of_int n
              | (n, FStar_Pervasives_Native.Some u2) ->
                  let uu___3 = univ_to_string u2 in
                  let uu___4 = FStar_Compiler_Util.string_of_int n in
                  FStar_Compiler_Util.format2 "(%s + %s)" uu___3 uu___4)
         | FStar_Syntax_Syntax.U_max us ->
             let uu___2 =
               let uu___3 = FStar_Compiler_List.map univ_to_string us in
               FStar_Compiler_String.concat ", " uu___3 in
             FStar_Compiler_Util.format1 "(max %s)" uu___2
         | FStar_Syntax_Syntax.U_unknown -> "unknown")
let (univs_to_string :
  FStar_Syntax_Syntax.universe Prims.list -> Prims.string) =
  fun us ->
    let uu___ = FStar_Compiler_List.map univ_to_string us in
    FStar_Compiler_String.concat ", " uu___
let (qual_to_string : FStar_Syntax_Syntax.qualifier -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | FStar_Syntax_Syntax.Assumption -> "assume"
    | FStar_Syntax_Syntax.InternalAssumption -> "internal_assume"
    | FStar_Syntax_Syntax.New -> "new"
    | FStar_Syntax_Syntax.Private -> "private"
    | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen -> "unfold"
    | FStar_Syntax_Syntax.Inline_for_extraction -> "inline_for_extraction"
    | FStar_Syntax_Syntax.NoExtract -> "noextract"
    | FStar_Syntax_Syntax.Visible_default -> "visible"
    | FStar_Syntax_Syntax.Irreducible -> "irreducible"
    | FStar_Syntax_Syntax.Noeq -> "noeq"
    | FStar_Syntax_Syntax.Unopteq -> "unopteq"
    | FStar_Syntax_Syntax.Logic -> "logic"
    | FStar_Syntax_Syntax.TotalEffect -> "total"
    | FStar_Syntax_Syntax.Discriminator l ->
        let uu___1 = lid_to_string l in
        FStar_Compiler_Util.format1 "(Discriminator %s)" uu___1
    | FStar_Syntax_Syntax.Projector (l, x) ->
        let uu___1 = lid_to_string l in
        let uu___2 = FStar_Ident.string_of_id x in
        FStar_Compiler_Util.format2 "(Projector %s %s)" uu___1 uu___2
    | FStar_Syntax_Syntax.RecordType (ns, fns) ->
        let uu___1 =
          let uu___2 = FStar_Ident.path_of_ns ns in
          FStar_Ident.text_of_path uu___2 in
        let uu___2 =
          let uu___3 = FStar_Compiler_List.map FStar_Ident.string_of_id fns in
          FStar_Compiler_String.concat ", " uu___3 in
        FStar_Compiler_Util.format2 "(RecordType %s %s)" uu___1 uu___2
    | FStar_Syntax_Syntax.RecordConstructor (ns, fns) ->
        let uu___1 =
          let uu___2 = FStar_Ident.path_of_ns ns in
          FStar_Ident.text_of_path uu___2 in
        let uu___2 =
          let uu___3 = FStar_Compiler_List.map FStar_Ident.string_of_id fns in
          FStar_Compiler_String.concat ", " uu___3 in
        FStar_Compiler_Util.format2 "(RecordConstructor %s %s)" uu___1 uu___2
    | FStar_Syntax_Syntax.Action eff_lid ->
        let uu___1 = lid_to_string eff_lid in
        FStar_Compiler_Util.format1 "(Action %s)" uu___1
    | FStar_Syntax_Syntax.ExceptionConstructor -> "ExceptionConstructor"
    | FStar_Syntax_Syntax.HasMaskedEffect -> "HasMaskedEffect"
    | FStar_Syntax_Syntax.Effect -> "Effect"
    | FStar_Syntax_Syntax.Reifiable -> "reify"
    | FStar_Syntax_Syntax.Reflectable l ->
        let uu___1 = FStar_Ident.string_of_lid l in
        FStar_Compiler_Util.format1 "(reflect %s)" uu___1
    | FStar_Syntax_Syntax.OnlyName -> "OnlyName"
let (quals_to_string :
  FStar_Syntax_Syntax.qualifier Prims.list -> Prims.string) =
  fun quals ->
    match quals with
    | [] -> ""
    | uu___ ->
        let uu___1 = FStar_Compiler_List.map qual_to_string quals in
        FStar_Compiler_String.concat " " uu___1
let (quals_to_string' :
  FStar_Syntax_Syntax.qualifier Prims.list -> Prims.string) =
  fun quals ->
    match quals with
    | [] -> ""
    | uu___ -> let uu___1 = quals_to_string quals in Prims.strcat uu___1 " "
let (paren : Prims.string -> Prims.string) =
  fun s -> Prims.strcat "(" (Prims.strcat s ")")
let (lkind_to_string : FStar_Syntax_Syntax.lazy_kind -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | FStar_Syntax_Syntax.BadLazy -> "BadLazy"
    | FStar_Syntax_Syntax.Lazy_bv -> "Lazy_bv"
    | FStar_Syntax_Syntax.Lazy_namedv -> "Lazy_namedv"
    | FStar_Syntax_Syntax.Lazy_binder -> "Lazy_binder"
    | FStar_Syntax_Syntax.Lazy_optionstate -> "Lazy_optionstate"
    | FStar_Syntax_Syntax.Lazy_fvar -> "Lazy_fvar"
    | FStar_Syntax_Syntax.Lazy_comp -> "Lazy_comp"
    | FStar_Syntax_Syntax.Lazy_env -> "Lazy_env"
    | FStar_Syntax_Syntax.Lazy_proofstate -> "Lazy_proofstate"
    | FStar_Syntax_Syntax.Lazy_goal -> "Lazy_goal"
    | FStar_Syntax_Syntax.Lazy_sigelt -> "Lazy_sigelt"
    | FStar_Syntax_Syntax.Lazy_uvar -> "Lazy_uvar"
    | FStar_Syntax_Syntax.Lazy_letbinding -> "Lazy_letbinding"
    | FStar_Syntax_Syntax.Lazy_embedding (e, uu___1) ->
        let uu___2 =
          let uu___3 =
            FStar_Class_Show.show FStar_Syntax_Syntax.showable_emb_typ e in
          Prims.strcat uu___3 ")" in
        Prims.strcat "Lazy_embedding(" uu___2
    | FStar_Syntax_Syntax.Lazy_universe -> "Lazy_universe"
    | FStar_Syntax_Syntax.Lazy_universe_uvar -> "Lazy_universe_uvar"
    | FStar_Syntax_Syntax.Lazy_issue -> "Lazy_issue"
    | FStar_Syntax_Syntax.Lazy_ident -> "Lazy_ident"
    | FStar_Syntax_Syntax.Lazy_doc -> "Lazy_doc"
    | FStar_Syntax_Syntax.Lazy_extension s ->
        Prims.strcat "Lazy_extension:" s
let (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun x ->
    let uu___ = FStar_Options.ugly () in
    if uu___
    then FStar_Syntax_Print_Ugly.term_to_string x
    else FStar_Syntax_Print_Pretty.term_to_string x
let (term_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun env ->
    fun x ->
      let uu___ = FStar_Options.ugly () in
      if uu___
      then FStar_Syntax_Print_Ugly.term_to_string x
      else FStar_Syntax_Print_Pretty.term_to_string' env x
let (comp_to_string : FStar_Syntax_Syntax.comp -> Prims.string) =
  fun c ->
    let uu___ = FStar_Options.ugly () in
    if uu___
    then FStar_Syntax_Print_Ugly.comp_to_string c
    else FStar_Syntax_Print_Pretty.comp_to_string c
let (comp_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env ->
    fun c ->
      let uu___ = FStar_Options.ugly () in
      if uu___
      then FStar_Syntax_Print_Ugly.comp_to_string c
      else FStar_Syntax_Print_Pretty.comp_to_string' env c
let (sigelt_to_string : FStar_Syntax_Syntax.sigelt -> Prims.string) =
  fun x ->
    let uu___ = FStar_Options.ugly () in
    if uu___
    then FStar_Syntax_Print_Ugly.sigelt_to_string x
    else FStar_Syntax_Print_Pretty.sigelt_to_string x
let (sigelt_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.sigelt -> Prims.string) =
  fun env ->
    fun x ->
      let uu___ = FStar_Options.ugly () in
      if uu___
      then FStar_Syntax_Print_Ugly.sigelt_to_string x
      else FStar_Syntax_Print_Pretty.sigelt_to_string' env x
let (pat_to_string : FStar_Syntax_Syntax.pat -> Prims.string) =
  fun x ->
    let uu___ = FStar_Options.ugly () in
    if uu___
    then FStar_Syntax_Print_Ugly.pat_to_string x
    else FStar_Syntax_Print_Pretty.pat_to_string x
let (term_to_doc' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.term -> FStar_Pprint.document)
  =
  fun dsenv ->
    fun t ->
      let uu___ = FStar_Options.ugly () in
      if uu___
      then
        let uu___1 = FStar_Syntax_Print_Ugly.term_to_string t in
        FStar_Pprint.arbitrary_string uu___1
      else FStar_Syntax_Print_Pretty.term_to_doc' dsenv t
let (univ_to_doc' :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.universe -> FStar_Pprint.document)
  =
  fun dsenv ->
    fun t ->
      let uu___ = FStar_Options.ugly () in
      if uu___
      then
        let uu___1 = FStar_Syntax_Print_Ugly.univ_to_string t in
        FStar_Pprint.arbitrary_string uu___1
      else FStar_Syntax_Print_Pretty.univ_to_doc' dsenv t
let (comp_to_doc' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.comp -> FStar_Pprint.document)
  =
  fun dsenv ->
    fun t ->
      let uu___ = FStar_Options.ugly () in
      if uu___
      then
        let uu___1 = FStar_Syntax_Print_Ugly.comp_to_string t in
        FStar_Pprint.arbitrary_string uu___1
      else FStar_Syntax_Print_Pretty.comp_to_doc' dsenv t
let (sigelt_to_doc' :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Pprint.document)
  =
  fun dsenv ->
    fun t ->
      let uu___ = FStar_Options.ugly () in
      if uu___
      then
        let uu___1 = FStar_Syntax_Print_Ugly.sigelt_to_string t in
        FStar_Pprint.arbitrary_string uu___1
      else FStar_Syntax_Print_Pretty.sigelt_to_doc' dsenv t
let (term_to_doc : FStar_Syntax_Syntax.term -> FStar_Pprint.document) =
  fun t ->
    let uu___ = FStar_Options.ugly () in
    if uu___
    then
      let uu___1 = FStar_Syntax_Print_Ugly.term_to_string t in
      FStar_Pprint.arbitrary_string uu___1
    else FStar_Syntax_Print_Pretty.term_to_doc t
let (univ_to_doc : FStar_Syntax_Syntax.universe -> FStar_Pprint.document) =
  fun t ->
    let uu___ = FStar_Options.ugly () in
    if uu___
    then
      let uu___1 = FStar_Syntax_Print_Ugly.univ_to_string t in
      FStar_Pprint.arbitrary_string uu___1
    else FStar_Syntax_Print_Pretty.univ_to_doc t
let (comp_to_doc : FStar_Syntax_Syntax.comp -> FStar_Pprint.document) =
  fun t ->
    let uu___ = FStar_Options.ugly () in
    if uu___
    then
      let uu___1 = FStar_Syntax_Print_Ugly.comp_to_string t in
      FStar_Pprint.arbitrary_string uu___1
    else FStar_Syntax_Print_Pretty.comp_to_doc t
let (sigelt_to_doc : FStar_Syntax_Syntax.sigelt -> FStar_Pprint.document) =
  fun t ->
    let uu___ = FStar_Options.ugly () in
    if uu___
    then
      let uu___1 = FStar_Syntax_Print_Ugly.sigelt_to_string t in
      FStar_Pprint.arbitrary_string uu___1
    else FStar_Syntax_Print_Pretty.sigelt_to_doc t
let (binder_to_string : FStar_Syntax_Syntax.binder -> Prims.string) =
  fun b ->
    let uu___ = FStar_Options.ugly () in
    if uu___
    then FStar_Syntax_Print_Pretty.binder_to_string' false b
    else FStar_Syntax_Print_Ugly.binder_to_string b
let (aqual_to_string : FStar_Syntax_Syntax.aqual -> Prims.string) =
  fun q ->
    match q with
    | FStar_Pervasives_Native.Some
        { FStar_Syntax_Syntax.aqual_implicit = true;
          FStar_Syntax_Syntax.aqual_attributes = uu___;_}
        -> "#"
    | uu___ -> ""
let (bqual_to_string' :
  Prims.string -> FStar_Syntax_Syntax.bqual -> Prims.string) =
  fun s ->
    fun b ->
      match b with
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (false))
          -> Prims.strcat "#" s
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true)) ->
          Prims.strcat "#." s
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality) ->
          Prims.strcat "$" s
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t) when
          FStar_Syntax_Util.is_fvar FStar_Parser_Const.tcresolve_lid t ->
          Prims.strcat "{|" (Prims.strcat s "|}")
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t) ->
          let uu___ =
            let uu___1 = term_to_string t in
            Prims.strcat uu___1 (Prims.strcat "]" s) in
          Prims.strcat "#[" uu___
      | FStar_Pervasives_Native.None -> s
let (bqual_to_string : FStar_Syntax_Syntax.bqual -> Prims.string) =
  fun q -> bqual_to_string' "" q
let (subst_elt_to_string : FStar_Syntax_Syntax.subst_elt -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | FStar_Syntax_Syntax.DB (i, x) ->
        let uu___1 = FStar_Compiler_Util.string_of_int i in
        let uu___2 = bv_to_string x in
        FStar_Compiler_Util.format2 "DB (%s, %s)" uu___1 uu___2
    | FStar_Syntax_Syntax.DT (i, t) ->
        let uu___1 = FStar_Compiler_Util.string_of_int i in
        let uu___2 = term_to_string t in
        FStar_Compiler_Util.format2 "DT (%s, %s)" uu___1 uu___2
    | FStar_Syntax_Syntax.NM (x, i) ->
        let uu___1 = bv_to_string x in
        let uu___2 = FStar_Compiler_Util.string_of_int i in
        FStar_Compiler_Util.format2 "NM (%s, %s)" uu___1 uu___2
    | FStar_Syntax_Syntax.NT (x, t) ->
        let uu___1 = bv_to_string x in
        let uu___2 = term_to_string t in
        FStar_Compiler_Util.format2 "NT (%s, %s)" uu___1 uu___2
    | FStar_Syntax_Syntax.UN (i, u) ->
        let uu___1 = FStar_Compiler_Util.string_of_int i in
        let uu___2 = univ_to_string u in
        FStar_Compiler_Util.format2 "UN (%s, %s)" uu___1 uu___2
    | FStar_Syntax_Syntax.UD (u, i) ->
        let uu___1 = FStar_Ident.string_of_id u in
        let uu___2 = FStar_Compiler_Util.string_of_int i in
        FStar_Compiler_Util.format2 "UD (%s, %s)" uu___1 uu___2
let (modul_to_string : FStar_Syntax_Syntax.modul -> Prims.string) =
  fun m ->
    let uu___ =
      FStar_Class_Show.show FStar_Ident.showable_lident
        m.FStar_Syntax_Syntax.name in
    let uu___1 =
      let uu___2 =
        FStar_Compiler_List.map sigelt_to_string
          m.FStar_Syntax_Syntax.declarations in
      FStar_Compiler_String.concat "\n" uu___2 in
    FStar_Compiler_Util.format2 "module %s\nDeclarations: [\n%s\n]\n" uu___
      uu___1
let (metadata_to_string : FStar_Syntax_Syntax.metadata -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | FStar_Syntax_Syntax.Meta_pattern (uu___1, ps) ->
        let pats =
          let uu___2 =
            FStar_Compiler_List.map
              (fun args ->
                 let uu___3 =
                   FStar_Compiler_List.map
                     (fun uu___4 ->
                        match uu___4 with | (t, uu___5) -> term_to_string t)
                     args in
                 FStar_Compiler_String.concat "; " uu___3) ps in
          FStar_Compiler_String.concat "\\/" uu___2 in
        FStar_Compiler_Util.format1 "{Meta_pattern %s}" pats
    | FStar_Syntax_Syntax.Meta_named lid ->
        let uu___1 = sli lid in
        FStar_Compiler_Util.format1 "{Meta_named %s}" uu___1
    | FStar_Syntax_Syntax.Meta_labeled (l, r, uu___1) ->
        let uu___2 = FStar_Errors_Msg.rendermsg l in
        let uu___3 = FStar_Compiler_Range_Ops.string_of_range r in
        FStar_Compiler_Util.format2 "{Meta_labeled (%s, %s)}" uu___2 uu___3
    | FStar_Syntax_Syntax.Meta_desugared msi -> "{Meta_desugared}"
    | FStar_Syntax_Syntax.Meta_monadic (m, t) ->
        let uu___1 = sli m in
        let uu___2 = term_to_string t in
        FStar_Compiler_Util.format2 "{Meta_monadic(%s @ %s)}" uu___1 uu___2
    | FStar_Syntax_Syntax.Meta_monadic_lift (m, m', t) ->
        let uu___1 = sli m in
        let uu___2 = sli m' in
        let uu___3 = term_to_string t in
        FStar_Compiler_Util.format3 "{Meta_monadic_lift(%s -> %s @ %s)}"
          uu___1 uu___2 uu___3
let (showable_term : FStar_Syntax_Syntax.term FStar_Class_Show.showable) =
  { FStar_Class_Show.show = term_to_string }
let (showable_univ : FStar_Syntax_Syntax.universe FStar_Class_Show.showable)
  = { FStar_Class_Show.show = univ_to_string }
let (showable_comp : FStar_Syntax_Syntax.comp FStar_Class_Show.showable) =
  { FStar_Class_Show.show = comp_to_string }
let (showable_sigelt : FStar_Syntax_Syntax.sigelt FStar_Class_Show.showable)
  = { FStar_Class_Show.show = sigelt_to_string }
let (showable_bv : FStar_Syntax_Syntax.bv FStar_Class_Show.showable) =
  { FStar_Class_Show.show = bv_to_string }
let (showable_fv : FStar_Syntax_Syntax.fv FStar_Class_Show.showable) =
  { FStar_Class_Show.show = fv_to_string }
let (showable_binder : FStar_Syntax_Syntax.binder FStar_Class_Show.showable)
  = { FStar_Class_Show.show = binder_to_string }
let (showable_uvar : FStar_Syntax_Syntax.uvar FStar_Class_Show.showable) =
  { FStar_Class_Show.show = uvar_to_string }
let (ctx_uvar_to_string : FStar_Syntax_Syntax.ctx_uvar -> Prims.string) =
  fun ctx_uvar ->
    let reason_string =
      FStar_Compiler_Util.format1 "(* %s *)\n"
        ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_reason in
    let uu___ =
      let uu___1 =
        FStar_Compiler_List.map (FStar_Class_Show.show showable_binder)
          ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_binders in
      FStar_Compiler_String.concat ", " uu___1 in
    let uu___1 = uvar_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head in
    let uu___2 =
      let uu___3 = FStar_Syntax_Util.ctx_uvar_typ ctx_uvar in
      term_to_string uu___3 in
    let uu___3 =
      let uu___4 = FStar_Syntax_Util.ctx_uvar_should_check ctx_uvar in
      match uu___4 with
      | FStar_Syntax_Syntax.Allow_unresolved s ->
          Prims.strcat "Allow_unresolved " s
      | FStar_Syntax_Syntax.Allow_untyped s ->
          Prims.strcat "Allow_untyped " s
      | FStar_Syntax_Syntax.Allow_ghost s -> Prims.strcat "Allow_ghost " s
      | FStar_Syntax_Syntax.Strict -> "Strict"
      | FStar_Syntax_Syntax.Already_checked -> "Already_checked" in
    FStar_Compiler_Util.format5 "%s(%s |- %s : %s) %s" reason_string uu___
      uu___1 uu___2 uu___3
let (showable_ctxu : FStar_Syntax_Syntax.ctx_uvar FStar_Class_Show.showable)
  = { FStar_Class_Show.show = ctx_uvar_to_string }
let (showable_binding :
  FStar_Syntax_Syntax.binding FStar_Class_Show.showable) =
  {
    FStar_Class_Show.show =
      (fun uu___ ->
         match uu___ with
         | FStar_Syntax_Syntax.Binding_var x ->
             let uu___1 = FStar_Class_Show.show showable_bv x in
             Prims.strcat "Binding_var " uu___1
         | FStar_Syntax_Syntax.Binding_lid x ->
             let uu___1 =
               FStar_Class_Show.show
                 (FStar_Class_Show.show_tuple2 FStar_Ident.showable_lident
                    (FStar_Class_Show.show_tuple2
                       (FStar_Class_Show.show_list FStar_Ident.showable_ident)
                       showable_term)) x in
             Prims.strcat "Binding_lid " uu___1
         | FStar_Syntax_Syntax.Binding_univ x ->
             let uu___1 = FStar_Class_Show.show FStar_Ident.showable_ident x in
             Prims.strcat "Binding_univ " uu___1)
  }
let (showable_subst_elt :
  FStar_Syntax_Syntax.subst_elt FStar_Class_Show.showable) =
  { FStar_Class_Show.show = subst_elt_to_string }
let (showable_branch : FStar_Syntax_Syntax.branch FStar_Class_Show.showable)
  = { FStar_Class_Show.show = FStar_Syntax_Print_Ugly.branch_to_string }
let (showable_qualifier :
  FStar_Syntax_Syntax.qualifier FStar_Class_Show.showable) =
  { FStar_Class_Show.show = qual_to_string }
let (showable_pat : FStar_Syntax_Syntax.pat FStar_Class_Show.showable) =
  { FStar_Class_Show.show = pat_to_string }
let (showable_const : FStar_Const.sconst FStar_Class_Show.showable) =
  { FStar_Class_Show.show = const_to_string }
let (showable_letbinding :
  FStar_Syntax_Syntax.letbinding FStar_Class_Show.showable) =
  { FStar_Class_Show.show = FStar_Syntax_Print_Ugly.lb_to_string }
let (showable_modul : FStar_Syntax_Syntax.modul FStar_Class_Show.showable) =
  { FStar_Class_Show.show = modul_to_string }
let (showable_metadata :
  FStar_Syntax_Syntax.metadata FStar_Class_Show.showable) =
  { FStar_Class_Show.show = metadata_to_string }
let (showable_ctx_uvar_meta :
  FStar_Syntax_Syntax.ctx_uvar_meta_t FStar_Class_Show.showable) =
  {
    FStar_Class_Show.show =
      (fun uu___ ->
         match uu___ with
         | FStar_Syntax_Syntax.Ctx_uvar_meta_attr attr ->
             let uu___1 = FStar_Class_Show.show showable_term attr in
             Prims.strcat "Ctx_uvar_meta_attr " uu___1
         | FStar_Syntax_Syntax.Ctx_uvar_meta_tac r ->
             let uu___1 = FStar_Class_Show.show showable_term r in
             Prims.strcat "Ctx_uvar_meta_tac " uu___1)
  }
let (showable_aqual : FStar_Syntax_Syntax.aqual FStar_Class_Show.showable) =
  { FStar_Class_Show.show = aqual_to_string }
let (tscheme_to_string : FStar_Syntax_Syntax.tscheme -> Prims.string) =
  fun ts ->
    let uu___ = FStar_Options.ugly () in
    if uu___
    then FStar_Syntax_Print_Ugly.tscheme_to_string ts
    else FStar_Syntax_Print_Pretty.tscheme_to_string ts
let (sub_eff_to_string : FStar_Syntax_Syntax.sub_eff -> Prims.string) =
  fun se ->
    let tsopt_to_string ts_opt =
      if FStar_Compiler_Util.is_some ts_opt
      then
        let uu___ = FStar_Compiler_Util.must ts_opt in
        tscheme_to_string uu___
      else "<None>" in
    let uu___ = lid_to_string se.FStar_Syntax_Syntax.source in
    let uu___1 = lid_to_string se.FStar_Syntax_Syntax.target in
    let uu___2 = tsopt_to_string se.FStar_Syntax_Syntax.lift in
    let uu___3 = tsopt_to_string se.FStar_Syntax_Syntax.lift_wp in
    FStar_Compiler_Util.format4
      "sub_effect %s ~> %s : lift = %s ;; lift_wp = %s" uu___ uu___1 uu___2
      uu___3
let (showable_sub_eff :
  FStar_Syntax_Syntax.sub_eff FStar_Class_Show.showable) =
  { FStar_Class_Show.show = sub_eff_to_string }
let (pretty_term : FStar_Syntax_Syntax.term FStar_Class_PP.pretty) =
  { FStar_Class_PP.pp = term_to_doc }
let (pretty_univ : FStar_Syntax_Syntax.universe FStar_Class_PP.pretty) =
  { FStar_Class_PP.pp = univ_to_doc }
let (pretty_sigelt : FStar_Syntax_Syntax.sigelt FStar_Class_PP.pretty) =
  { FStar_Class_PP.pp = sigelt_to_doc }
let (pretty_comp : FStar_Syntax_Syntax.comp FStar_Class_PP.pretty) =
  { FStar_Class_PP.pp = comp_to_doc }
let (pretty_ctxu : FStar_Syntax_Syntax.ctx_uvar FStar_Class_PP.pretty) =
  {
    FStar_Class_PP.pp =
      (fun x ->
         let uu___ = FStar_Class_Show.show showable_ctxu x in
         FStar_Pprint.doc_of_string uu___)
  }
let (pretty_uvar : FStar_Syntax_Syntax.uvar FStar_Class_PP.pretty) =
  {
    FStar_Class_PP.pp =
      (fun x ->
         let uu___ = FStar_Class_Show.show showable_uvar x in
         FStar_Pprint.doc_of_string uu___)
  }
let (pretty_binder : FStar_Syntax_Syntax.binder FStar_Class_PP.pretty) =
  {
    FStar_Class_PP.pp =
      (fun x ->
         let uu___ = FStar_Class_Show.show showable_binder x in
         FStar_Pprint.doc_of_string uu___)
  }
let (pretty_bv : FStar_Syntax_Syntax.bv FStar_Class_PP.pretty) =
  {
    FStar_Class_PP.pp =
      (fun x ->
         let uu___ = FStar_Class_Show.show showable_bv x in
         FStar_Pprint.doc_of_string uu___)
  }
let (pretty_binding : FStar_Syntax_Syntax.binding FStar_Class_PP.pretty) =
  {
    FStar_Class_PP.pp =
      (fun uu___ ->
         match uu___ with
         | FStar_Syntax_Syntax.Binding_var bv ->
             FStar_Class_PP.pp pretty_bv bv
         | FStar_Syntax_Syntax.Binding_lid (l, (us, t)) ->
             let uu___1 = FStar_Class_PP.pp FStar_Ident.pretty_lident l in
             let uu___2 =
               let uu___3 = FStar_Class_PP.pp pretty_term t in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu___3 in
             FStar_Pprint.op_Hat_Hat uu___1 uu___2
         | FStar_Syntax_Syntax.Binding_univ u ->
             FStar_Class_PP.pp FStar_Ident.pretty_ident u)
  }
let rec (sigelt_to_string_short : FStar_Syntax_Syntax.sigelt -> Prims.string)
  =
  fun x ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_pragma p ->
        FStar_Class_Show.show FStar_Syntax_Syntax.showable_pragma p
    | FStar_Syntax_Syntax.Sig_let
        {
          FStar_Syntax_Syntax.lbs1 =
            (false,
             { FStar_Syntax_Syntax.lbname = lb;
               FStar_Syntax_Syntax.lbunivs = uu___;
               FStar_Syntax_Syntax.lbtyp = uu___1;
               FStar_Syntax_Syntax.lbeff = uu___2;
               FStar_Syntax_Syntax.lbdef = uu___3;
               FStar_Syntax_Syntax.lbattrs = uu___4;
               FStar_Syntax_Syntax.lbpos = uu___5;_}::[]);
          FStar_Syntax_Syntax.lids1 = uu___6;_}
        ->
        let uu___7 = lbname_to_string lb in
        FStar_Compiler_Util.format1 "let %s" uu___7
    | FStar_Syntax_Syntax.Sig_let
        {
          FStar_Syntax_Syntax.lbs1 =
            (true,
             { FStar_Syntax_Syntax.lbname = lb;
               FStar_Syntax_Syntax.lbunivs = uu___;
               FStar_Syntax_Syntax.lbtyp = uu___1;
               FStar_Syntax_Syntax.lbeff = uu___2;
               FStar_Syntax_Syntax.lbdef = uu___3;
               FStar_Syntax_Syntax.lbattrs = uu___4;
               FStar_Syntax_Syntax.lbpos = uu___5;_}::[]);
          FStar_Syntax_Syntax.lids1 = uu___6;_}
        ->
        let uu___7 = lbname_to_string lb in
        FStar_Compiler_Util.format1 "let rec %s" uu___7
    | FStar_Syntax_Syntax.Sig_let
        { FStar_Syntax_Syntax.lbs1 = (true, lbs);
          FStar_Syntax_Syntax.lids1 = uu___;_}
        ->
        let uu___1 =
          let uu___2 =
            FStar_Compiler_List.map
              (fun lb -> lbname_to_string lb.FStar_Syntax_Syntax.lbname) lbs in
          FStar_Compiler_String.concat " and " uu___2 in
        FStar_Compiler_Util.format1 "let rec %s" uu___1
    | FStar_Syntax_Syntax.Sig_let uu___ ->
        failwith "Impossible: sigelt_to_string_short, ill-formed let"
    | FStar_Syntax_Syntax.Sig_declare_typ
        { FStar_Syntax_Syntax.lid2 = lid; FStar_Syntax_Syntax.us2 = uu___;
          FStar_Syntax_Syntax.t2 = uu___1;_}
        ->
        let uu___2 = FStar_Ident.string_of_lid lid in
        FStar_Compiler_Util.format1 "val %s" uu___2
    | FStar_Syntax_Syntax.Sig_inductive_typ
        { FStar_Syntax_Syntax.lid = lid; FStar_Syntax_Syntax.us = uu___;
          FStar_Syntax_Syntax.params = uu___1;
          FStar_Syntax_Syntax.num_uniform_params = uu___2;
          FStar_Syntax_Syntax.t = uu___3;
          FStar_Syntax_Syntax.mutuals = uu___4;
          FStar_Syntax_Syntax.ds = uu___5;
          FStar_Syntax_Syntax.injective_type_params = uu___6;_}
        ->
        let uu___7 = FStar_Ident.string_of_lid lid in
        FStar_Compiler_Util.format1 "type %s" uu___7
    | FStar_Syntax_Syntax.Sig_datacon
        { FStar_Syntax_Syntax.lid1 = lid; FStar_Syntax_Syntax.us1 = uu___;
          FStar_Syntax_Syntax.t1 = uu___1;
          FStar_Syntax_Syntax.ty_lid = t_lid;
          FStar_Syntax_Syntax.num_ty_params = uu___2;
          FStar_Syntax_Syntax.mutuals1 = uu___3;
          FStar_Syntax_Syntax.injective_type_params1 = uu___4;_}
        ->
        let uu___5 = FStar_Ident.string_of_lid lid in
        let uu___6 = FStar_Ident.string_of_lid t_lid in
        FStar_Compiler_Util.format2 "datacon %s for type %s" uu___5 uu___6
    | FStar_Syntax_Syntax.Sig_assume
        { FStar_Syntax_Syntax.lid3 = lid; FStar_Syntax_Syntax.us3 = uu___;
          FStar_Syntax_Syntax.phi1 = uu___1;_}
        ->
        let uu___2 = FStar_Ident.string_of_lid lid in
        FStar_Compiler_Util.format1 "assume %s" uu___2
    | FStar_Syntax_Syntax.Sig_bundle
        { FStar_Syntax_Syntax.ses = ses; FStar_Syntax_Syntax.lids = uu___;_}
        ->
        let uu___1 = FStar_Compiler_List.hd ses in
        sigelt_to_string_short uu___1
    | FStar_Syntax_Syntax.Sig_fail
        { FStar_Syntax_Syntax.errs = uu___;
          FStar_Syntax_Syntax.fail_in_lax = uu___1;
          FStar_Syntax_Syntax.ses1 = ses;_}
        ->
        let uu___2 =
          let uu___3 = FStar_Compiler_List.hd ses in
          sigelt_to_string_short uu___3 in
        FStar_Compiler_Util.format1 "[@@expect_failure] %s" uu___2
    | FStar_Syntax_Syntax.Sig_new_effect ed ->
        let kw =
          let uu___ = FStar_Syntax_Util.is_layered ed in
          if uu___
          then "layered_effect"
          else
            (let uu___2 = FStar_Syntax_Util.is_dm4f ed in
             if uu___2 then "new_effect_for_free" else "new_effect") in
        let uu___ = lid_to_string ed.FStar_Syntax_Syntax.mname in
        FStar_Compiler_Util.format2 "%s { %s ... }" kw uu___
    | FStar_Syntax_Syntax.Sig_sub_effect se ->
        let uu___ = lid_to_string se.FStar_Syntax_Syntax.source in
        let uu___1 = lid_to_string se.FStar_Syntax_Syntax.target in
        FStar_Compiler_Util.format2 "sub_effect %s ~> %s" uu___ uu___1
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        { FStar_Syntax_Syntax.lid4 = l; FStar_Syntax_Syntax.us4 = uu___;
          FStar_Syntax_Syntax.bs2 = tps; FStar_Syntax_Syntax.comp1 = c;
          FStar_Syntax_Syntax.cflags = uu___1;_}
        ->
        let uu___2 = sli l in
        let uu___3 =
          let uu___4 =
            FStar_Compiler_List.map (FStar_Class_Show.show showable_binder)
              tps in
          FStar_Compiler_String.concat " " uu___4 in
        let uu___4 = FStar_Class_Show.show showable_comp c in
        FStar_Compiler_Util.format3 "effect %s %s = %s" uu___2 uu___3 uu___4
    | FStar_Syntax_Syntax.Sig_splice
        { FStar_Syntax_Syntax.is_typed = is_typed;
          FStar_Syntax_Syntax.lids2 = lids;
          FStar_Syntax_Syntax.tac = uu___;_}
        ->
        let uu___1 =
          let uu___2 = FStar_Compiler_List.map FStar_Ident.string_of_lid lids in
          FStar_Compiler_String.concat "; " uu___2 in
        FStar_Compiler_Util.format3 "%splice%s[%s] (...)" "%s"
          (if is_typed then "_t" else "") uu___1
    | FStar_Syntax_Syntax.Sig_polymonadic_bind
        { FStar_Syntax_Syntax.m_lid = m; FStar_Syntax_Syntax.n_lid = n;
          FStar_Syntax_Syntax.p_lid = p; FStar_Syntax_Syntax.tm3 = uu___;
          FStar_Syntax_Syntax.typ = uu___1;
          FStar_Syntax_Syntax.kind1 = uu___2;_}
        ->
        let uu___3 = FStar_Ident.string_of_lid m in
        let uu___4 = FStar_Ident.string_of_lid n in
        let uu___5 = FStar_Ident.string_of_lid p in
        FStar_Compiler_Util.format3 "polymonadic_bind (%s, %s) |> %s" uu___3
          uu___4 uu___5
    | FStar_Syntax_Syntax.Sig_polymonadic_subcomp
        { FStar_Syntax_Syntax.m_lid1 = m; FStar_Syntax_Syntax.n_lid1 = n;
          FStar_Syntax_Syntax.tm4 = uu___; FStar_Syntax_Syntax.typ1 = uu___1;
          FStar_Syntax_Syntax.kind2 = uu___2;_}
        ->
        let uu___3 = FStar_Ident.string_of_lid m in
        let uu___4 = FStar_Ident.string_of_lid n in
        FStar_Compiler_Util.format2 "polymonadic_subcomp %s <: %s" uu___3
          uu___4
let (binder_to_json :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.binder -> FStar_Json.json) =
  fun env ->
    fun b ->
      let n =
        let uu___ =
          let uu___1 = nm_to_string b.FStar_Syntax_Syntax.binder_bv in
          bqual_to_string' uu___1 b.FStar_Syntax_Syntax.binder_qual in
        FStar_Json.JsonStr uu___ in
      let t =
        let uu___ =
          term_to_string' env
            (b.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort in
        FStar_Json.JsonStr uu___ in
      FStar_Json.JsonAssoc [("name", n); ("type", t)]
let (binders_to_json :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.binders -> FStar_Json.json) =
  fun env ->
    fun bs ->
      let uu___ = FStar_Compiler_List.map (binder_to_json env) bs in
      FStar_Json.JsonList uu___
let (eff_decl_to_string : FStar_Syntax_Syntax.eff_decl -> Prims.string) =
  fun ed ->
    let uu___ = FStar_Options.ugly () in
    if uu___
    then FStar_Syntax_Print_Ugly.eff_decl_to_string ed
    else FStar_Syntax_Print_Pretty.eff_decl_to_string ed
let (showable_eff_decl :
  FStar_Syntax_Syntax.eff_decl FStar_Class_Show.showable) =
  { FStar_Class_Show.show = eff_decl_to_string }
let (args_to_string : FStar_Syntax_Syntax.args -> Prims.string) =
  fun args ->
    let uu___ =
      FStar_Compiler_List.map
        (fun uu___1 ->
           match uu___1 with
           | (a, q) ->
               let uu___2 = aqual_to_string q in
               let uu___3 = term_to_string a in Prims.strcat uu___2 uu___3)
        args in
    FStar_Compiler_String.concat " " uu___
let (showable_decreases_order :
  FStar_Syntax_Syntax.decreases_order FStar_Class_Show.showable) =
  {
    FStar_Class_Show.show =
      (fun uu___ ->
         match uu___ with
         | FStar_Syntax_Syntax.Decreases_lex l ->
             let uu___1 =
               FStar_Class_Show.show
                 (FStar_Class_Show.show_list showable_term) l in
             Prims.strcat "Decreases_lex " uu___1
         | FStar_Syntax_Syntax.Decreases_wf l ->
             let uu___1 =
               FStar_Class_Show.show
                 (FStar_Class_Show.show_tuple2 showable_term showable_term) l in
             Prims.strcat "Decreases_wf " uu___1)
  }
let (cflag_to_string : FStar_Syntax_Syntax.cflag -> Prims.string) =
  fun c ->
    match c with
    | FStar_Syntax_Syntax.TOTAL -> "total"
    | FStar_Syntax_Syntax.MLEFFECT -> "ml"
    | FStar_Syntax_Syntax.RETURN -> "return"
    | FStar_Syntax_Syntax.PARTIAL_RETURN -> "partial_return"
    | FStar_Syntax_Syntax.SOMETRIVIAL -> "sometrivial"
    | FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION -> "trivial_postcondition"
    | FStar_Syntax_Syntax.SHOULD_NOT_INLINE -> "should_not_inline"
    | FStar_Syntax_Syntax.LEMMA -> "lemma"
    | FStar_Syntax_Syntax.CPS -> "cps"
    | FStar_Syntax_Syntax.DECREASES do1 ->
        let uu___ = FStar_Class_Show.show showable_decreases_order do1 in
        Prims.strcat "decreases " uu___
let (showable_cflag : FStar_Syntax_Syntax.cflag FStar_Class_Show.showable) =
  { FStar_Class_Show.show = cflag_to_string }
let (binder_to_string_with_type : FStar_Syntax_Syntax.binder -> Prims.string)
  =
  fun b ->
    let uu___ = FStar_Options.ugly () in
    if uu___
    then
      let attrs =
        match b.FStar_Syntax_Syntax.binder_attrs with
        | [] -> ""
        | ts ->
            let uu___1 =
              let uu___2 =
                let uu___3 =
                  FStar_Compiler_List.map
                    (FStar_Class_Show.show showable_term) ts in
                FStar_Compiler_String.concat ", " uu___3 in
              Prims.strcat uu___2 "] " in
            Prims.strcat "[@@@" uu___1 in
      let uu___1 = FStar_Syntax_Syntax.is_null_binder b in
      (if uu___1
       then
         let uu___2 =
           let uu___3 =
             term_to_string
               (b.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort in
           Prims.strcat "_:" uu___3 in
         Prims.strcat attrs uu___2
       else
         (let uu___3 =
            let uu___4 =
              let uu___5 = nm_to_string b.FStar_Syntax_Syntax.binder_bv in
              let uu___6 =
                let uu___7 =
                  term_to_string
                    (b.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort in
                Prims.strcat ": " uu___7 in
              Prims.strcat uu___5 uu___6 in
            Prims.strcat attrs uu___4 in
          bqual_to_string' uu___3 b.FStar_Syntax_Syntax.binder_qual))
    else FStar_Syntax_Print_Pretty.binder_to_string' false b