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
    let uu___ = FStar_Ident.string_of_id bv.FStar_Syntax_Syntax.ppname in
    let uu___1 =
      let uu___2 =
        FStar_Compiler_Util.string_of_int bv.FStar_Syntax_Syntax.index in
      Prims.strcat "#" uu___2 in
    Prims.strcat uu___ uu___1
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
    FStar_Compiler_Effect.op_Bar_Greater args
      (FStar_Compiler_List.filter
         (fun uu___ ->
            match uu___ with
            | (uu___1, FStar_Pervasives_Native.None) -> true
            | (uu___1, FStar_Pervasives_Native.Some a) ->
                Prims.op_Negation a.FStar_Syntax_Syntax.aqual_implicit))
let (filter_imp_binders :
  FStar_Syntax_Syntax.binder Prims.list ->
    FStar_Syntax_Syntax.binder Prims.list)
  =
  fun bs ->
    FStar_Compiler_Effect.op_Bar_Greater bs
      (FStar_Compiler_List.filter
         (fun b ->
            FStar_Compiler_Effect.op_Bar_Greater
              b.FStar_Syntax_Syntax.binder_qual filter_imp))
let (const_to_string : FStar_Const.sconst -> Prims.string) =
  FStar_Parser_Const.const_to_string
let (lbname_to_string : FStar_Syntax_Syntax.lbname -> Prims.string) =
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
         FStar_Compiler_Effect.op_Bar_Greater uu___3
           FStar_Compiler_Util.string_of_int in
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
           FStar_Compiler_Effect.op_Bar_Greater uu___4
             FStar_Compiler_Util.string_of_int in
         let uu___4 =
           let uu___5 =
             FStar_Compiler_Effect.op_Bar_Greater u
               (fun uu___6 ->
                  match uu___6 with
                  | (uu___7, u1, uu___8) -> version_to_string u1) in
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
               FStar_Compiler_Effect.op_Bar_Greater uu___3
                 (FStar_Compiler_String.concat ", ") in
             FStar_Compiler_Util.format1 "(max %s)" uu___2
         | FStar_Syntax_Syntax.U_unknown -> "unknown")
let (univs_to_string : FStar_Syntax_Syntax.universes -> Prims.string) =
  fun us ->
    let uu___ = FStar_Compiler_List.map univ_to_string us in
    FStar_Compiler_Effect.op_Bar_Greater uu___
      (FStar_Compiler_String.concat ", ")
let (univ_names_to_string : FStar_Syntax_Syntax.univ_names -> Prims.string) =
  fun us ->
    let uu___ =
      FStar_Compiler_List.map (fun x -> FStar_Ident.string_of_id x) us in
    FStar_Compiler_Effect.op_Bar_Greater uu___
      (FStar_Compiler_String.concat ", ")
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
          let uu___3 =
            FStar_Compiler_Effect.op_Bar_Greater fns
              (FStar_Compiler_List.map FStar_Ident.string_of_id) in
          FStar_Compiler_Effect.op_Bar_Greater uu___3
            (FStar_Compiler_String.concat ", ") in
        FStar_Compiler_Util.format2 "(RecordType %s %s)" uu___1 uu___2
    | FStar_Syntax_Syntax.RecordConstructor (ns, fns) ->
        let uu___1 =
          let uu___2 = FStar_Ident.path_of_ns ns in
          FStar_Ident.text_of_path uu___2 in
        let uu___2 =
          let uu___3 =
            FStar_Compiler_Effect.op_Bar_Greater fns
              (FStar_Compiler_List.map FStar_Ident.string_of_id) in
          FStar_Compiler_Effect.op_Bar_Greater uu___3
            (FStar_Compiler_String.concat ", ") in
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
        let uu___1 =
          FStar_Compiler_Effect.op_Bar_Greater quals
            (FStar_Compiler_List.map qual_to_string) in
        FStar_Compiler_Effect.op_Bar_Greater uu___1
          (FStar_Compiler_String.concat " ")
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
let rec (tag_of_term : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let uu___ = db_to_string x in Prims.strcat "Tm_bvar: " uu___
    | FStar_Syntax_Syntax.Tm_name x ->
        let uu___ = nm_to_string x in Prims.strcat "Tm_name: " uu___
    | FStar_Syntax_Syntax.Tm_fvar x ->
        let uu___ =
          lid_to_string (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        Prims.strcat "Tm_fvar: " uu___
    | FStar_Syntax_Syntax.Tm_uinst uu___ -> "Tm_uinst"
    | FStar_Syntax_Syntax.Tm_constant uu___ -> "Tm_constant"
    | FStar_Syntax_Syntax.Tm_type uu___ -> "Tm_type"
    | FStar_Syntax_Syntax.Tm_quoted
        (uu___,
         { FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static;
           FStar_Syntax_Syntax.antiquotations = uu___1;_})
        -> "Tm_quoted (static)"
    | FStar_Syntax_Syntax.Tm_quoted
        (uu___,
         { FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic;
           FStar_Syntax_Syntax.antiquotations = uu___1;_})
        -> "Tm_quoted (dynamic)"
    | FStar_Syntax_Syntax.Tm_abs uu___ -> "Tm_abs"
    | FStar_Syntax_Syntax.Tm_arrow uu___ -> "Tm_arrow"
    | FStar_Syntax_Syntax.Tm_refine uu___ -> "Tm_refine"
    | FStar_Syntax_Syntax.Tm_app uu___ -> "Tm_app"
    | FStar_Syntax_Syntax.Tm_match uu___ -> "Tm_match"
    | FStar_Syntax_Syntax.Tm_ascribed uu___ -> "Tm_ascribed"
    | FStar_Syntax_Syntax.Tm_let uu___ -> "Tm_let"
    | FStar_Syntax_Syntax.Tm_uvar uu___ -> "Tm_uvar"
    | FStar_Syntax_Syntax.Tm_delayed uu___ -> "Tm_delayed"
    | FStar_Syntax_Syntax.Tm_meta
        { FStar_Syntax_Syntax.tm2 = uu___; FStar_Syntax_Syntax.meta = m;_} ->
        let uu___1 = metadata_to_string m in Prims.strcat "Tm_meta:" uu___1
    | FStar_Syntax_Syntax.Tm_unknown -> "Tm_unknown"
    | FStar_Syntax_Syntax.Tm_lazy li ->
        let uu___ =
          let uu___1 = lkind_to_string li.FStar_Syntax_Syntax.lkind in
          Prims.strcat uu___1 ")" in
        Prims.strcat "Tm_lazy(" uu___
and (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun x ->
    let uu___ =
      let uu___1 = FStar_Options.ugly () in Prims.op_Negation uu___1 in
    if uu___
    then FStar_Syntax_Print_Pretty.term_to_string x
    else
      FStar_Errors.with_ctx "While ugly-printing a term"
        (fun uu___2 ->
           let x1 = FStar_Syntax_Subst.compress x in
           let x2 =
             let uu___3 = FStar_Options.print_implicits () in
             if uu___3 then x1 else FStar_Syntax_Util.unmeta x1 in
           match x2.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_delayed uu___3 -> failwith "impossible"
           | FStar_Syntax_Syntax.Tm_app
               { FStar_Syntax_Syntax.hd = uu___3;
                 FStar_Syntax_Syntax.args = [];_}
               -> failwith "Empty args!"
           | FStar_Syntax_Syntax.Tm_lazy
               { FStar_Syntax_Syntax.blob = b;
                 FStar_Syntax_Syntax.lkind =
                   FStar_Syntax_Syntax.Lazy_embedding (uu___3, thunk);
                 FStar_Syntax_Syntax.ltyp = uu___4;
                 FStar_Syntax_Syntax.rng = uu___5;_}
               ->
               let uu___6 =
                 let uu___7 =
                   let uu___8 = FStar_Thunk.force thunk in
                   term_to_string uu___8 in
                 Prims.strcat uu___7 "]" in
               Prims.strcat "[LAZYEMB:" uu___6
           | FStar_Syntax_Syntax.Tm_lazy i ->
               let uu___3 =
                 let uu___4 =
                   let uu___5 =
                     let uu___6 =
                       let uu___7 =
                         FStar_Compiler_Effect.op_Bang
                           FStar_Syntax_Syntax.lazy_chooser in
                       FStar_Compiler_Util.must uu___7 in
                     uu___6 i.FStar_Syntax_Syntax.lkind i in
                   term_to_string uu___5 in
                 Prims.strcat uu___4 "]" in
               Prims.strcat "[lazy:" uu___3
           | FStar_Syntax_Syntax.Tm_quoted (tm, qi) ->
               (match qi.FStar_Syntax_Syntax.qkind with
                | FStar_Syntax_Syntax.Quote_static ->
                    let uu___3 = term_to_string tm in
                    let uu___4 =
                      (FStar_Common.string_of_list ()) term_to_string
                        (FStar_Pervasives_Native.snd
                           qi.FStar_Syntax_Syntax.antiquotations) in
                    FStar_Compiler_Util.format2 "`(%s)%s" uu___3 uu___4
                | FStar_Syntax_Syntax.Quote_dynamic ->
                    let uu___3 = term_to_string tm in
                    FStar_Compiler_Util.format1 "quote (%s)" uu___3)
           | FStar_Syntax_Syntax.Tm_meta
               { FStar_Syntax_Syntax.tm2 = t;
                 FStar_Syntax_Syntax.meta = FStar_Syntax_Syntax.Meta_pattern
                   (uu___3, ps);_}
               ->
               let pats =
                 let uu___4 =
                   FStar_Compiler_Effect.op_Bar_Greater ps
                     (FStar_Compiler_List.map
                        (fun args ->
                           let uu___5 =
                             FStar_Compiler_Effect.op_Bar_Greater args
                               (FStar_Compiler_List.map
                                  (fun uu___6 ->
                                     match uu___6 with
                                     | (t1, uu___7) -> term_to_string t1)) in
                           FStar_Compiler_Effect.op_Bar_Greater uu___5
                             (FStar_Compiler_String.concat "; "))) in
                 FStar_Compiler_Effect.op_Bar_Greater uu___4
                   (FStar_Compiler_String.concat "\\/") in
               let uu___4 = term_to_string t in
               FStar_Compiler_Util.format2 "{:pattern %s} %s" pats uu___4
           | FStar_Syntax_Syntax.Tm_meta
               { FStar_Syntax_Syntax.tm2 = t;
                 FStar_Syntax_Syntax.meta = FStar_Syntax_Syntax.Meta_monadic
                   (m, t');_}
               ->
               let uu___3 = sli m in
               let uu___4 = term_to_string t' in
               let uu___5 = tag_of_term t in
               let uu___6 = term_to_string t in
               FStar_Compiler_Util.format4 "(MetaMonadic-{%s %s} (%s) %s)"
                 uu___3 uu___4 uu___5 uu___6
           | FStar_Syntax_Syntax.Tm_meta
               { FStar_Syntax_Syntax.tm2 = t;
                 FStar_Syntax_Syntax.meta =
                   FStar_Syntax_Syntax.Meta_monadic_lift (m0, m1, t');_}
               ->
               let uu___3 = term_to_string t' in
               let uu___4 = sli m0 in
               let uu___5 = sli m1 in
               let uu___6 = term_to_string t in
               FStar_Compiler_Util.format4
                 "(MetaMonadicLift-{%s : %s -> %s} %s)" uu___3 uu___4 uu___5
                 uu___6
           | FStar_Syntax_Syntax.Tm_meta
               { FStar_Syntax_Syntax.tm2 = t;
                 FStar_Syntax_Syntax.meta = FStar_Syntax_Syntax.Meta_labeled
                   (l, r, b);_}
               ->
               let uu___3 = FStar_Compiler_Range_Ops.string_of_range r in
               let uu___4 = term_to_string t in
               FStar_Compiler_Util.format3 "Meta_labeled(%s, %s){%s}" l
                 uu___3 uu___4
           | FStar_Syntax_Syntax.Tm_meta
               { FStar_Syntax_Syntax.tm2 = t;
                 FStar_Syntax_Syntax.meta = FStar_Syntax_Syntax.Meta_named l;_}
               ->
               let uu___3 = lid_to_string l in
               let uu___4 =
                 FStar_Compiler_Range_Ops.string_of_range
                   t.FStar_Syntax_Syntax.pos in
               let uu___5 = term_to_string t in
               FStar_Compiler_Util.format3 "Meta_named(%s, %s){%s}" uu___3
                 uu___4 uu___5
           | FStar_Syntax_Syntax.Tm_meta
               { FStar_Syntax_Syntax.tm2 = t;
                 FStar_Syntax_Syntax.meta =
                   FStar_Syntax_Syntax.Meta_desugared uu___3;_}
               ->
               let uu___4 = term_to_string t in
               FStar_Compiler_Util.format1 "Meta_desugared{%s}" uu___4
           | FStar_Syntax_Syntax.Tm_bvar x3 ->
               let uu___3 = db_to_string x3 in
               let uu___4 =
                 let uu___5 =
                   let uu___6 = tag_of_term x3.FStar_Syntax_Syntax.sort in
                   Prims.strcat uu___6 ")" in
                 Prims.strcat ":(" uu___5 in
               Prims.strcat uu___3 uu___4
           | FStar_Syntax_Syntax.Tm_name x3 -> nm_to_string x3
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let pref =
                 match f.FStar_Syntax_Syntax.fv_qual with
                 | FStar_Pervasives_Native.Some
                     (FStar_Syntax_Syntax.Unresolved_projector uu___3) ->
                     "(Unresolved_projector)"
                 | FStar_Pervasives_Native.Some
                     (FStar_Syntax_Syntax.Unresolved_constructor uu___3) ->
                     "(Unresolved_constructor)"
                 | uu___3 -> "" in
               let uu___3 = fv_to_string f in Prims.strcat pref uu___3
           | FStar_Syntax_Syntax.Tm_uvar (u, ([], uu___3)) ->
               let uu___4 =
                 (FStar_Options.print_bound_var_types ()) &&
                   (FStar_Options.print_effect_args ()) in
               if uu___4
               then ctx_uvar_to_string_aux true u
               else
                 (let uu___6 =
                    let uu___7 =
                      FStar_Syntax_Unionfind.uvar_id
                        u.FStar_Syntax_Syntax.ctx_uvar_head in
                    FStar_Compiler_Effect.op_Less_Bar
                      FStar_Compiler_Util.string_of_int uu___7 in
                  Prims.strcat "?" uu___6)
           | FStar_Syntax_Syntax.Tm_uvar (u, s) ->
               let uu___3 =
                 (FStar_Options.print_bound_var_types ()) &&
                   (FStar_Options.print_effect_args ()) in
               if uu___3
               then
                 let uu___4 = ctx_uvar_to_string_aux true u in
                 let uu___5 =
                   let uu___6 =
                     FStar_Compiler_List.map subst_to_string
                       (FStar_Pervasives_Native.fst s) in
                   FStar_Compiler_Effect.op_Bar_Greater uu___6
                     (FStar_Compiler_String.concat "; ") in
                 FStar_Compiler_Util.format2 "(%s @ %s)" uu___4 uu___5
               else
                 (let uu___5 =
                    let uu___6 =
                      FStar_Syntax_Unionfind.uvar_id
                        u.FStar_Syntax_Syntax.ctx_uvar_head in
                    FStar_Compiler_Effect.op_Less_Bar
                      FStar_Compiler_Util.string_of_int uu___6 in
                  Prims.strcat "?" uu___5)
           | FStar_Syntax_Syntax.Tm_constant c -> const_to_string c
           | FStar_Syntax_Syntax.Tm_type u ->
               let uu___3 = FStar_Options.print_universes () in
               if uu___3
               then
                 let uu___4 = univ_to_string u in
                 FStar_Compiler_Util.format1 "Type u#(%s)" uu___4
               else "Type"
           | FStar_Syntax_Syntax.Tm_arrow
               { FStar_Syntax_Syntax.bs1 = bs;
                 FStar_Syntax_Syntax.comp = c;_}
               ->
               let uu___3 = binders_to_string " -> " bs in
               let uu___4 = comp_to_string c in
               FStar_Compiler_Util.format2 "(%s -> %s)" uu___3 uu___4
           | FStar_Syntax_Syntax.Tm_abs
               { FStar_Syntax_Syntax.bs = bs; FStar_Syntax_Syntax.body = t2;
                 FStar_Syntax_Syntax.rc_opt = lc;_}
               ->
               (match lc with
                | FStar_Pervasives_Native.Some rc when
                    FStar_Options.print_implicits () ->
                    let uu___3 = binders_to_string " " bs in
                    let uu___4 = term_to_string t2 in
                    let uu___5 =
                      FStar_Ident.string_of_lid
                        rc.FStar_Syntax_Syntax.residual_effect in
                    let uu___6 =
                      if
                        FStar_Compiler_Option.isNone
                          rc.FStar_Syntax_Syntax.residual_typ
                      then "None"
                      else
                        (let uu___8 =
                           FStar_Compiler_Option.get
                             rc.FStar_Syntax_Syntax.residual_typ in
                         term_to_string uu___8) in
                    FStar_Compiler_Util.format4
                      "(fun %s -> (%s $$ (residual) %s %s))" uu___3 uu___4
                      uu___5 uu___6
                | uu___3 ->
                    let uu___4 = binders_to_string " " bs in
                    let uu___5 = term_to_string t2 in
                    FStar_Compiler_Util.format2 "(fun %s -> %s)" uu___4
                      uu___5)
           | FStar_Syntax_Syntax.Tm_refine
               { FStar_Syntax_Syntax.b = xt; FStar_Syntax_Syntax.phi = f;_}
               ->
               let uu___3 = bv_to_string xt in
               let uu___4 =
                 FStar_Compiler_Effect.op_Bar_Greater
                   xt.FStar_Syntax_Syntax.sort term_to_string in
               let uu___5 =
                 FStar_Compiler_Effect.op_Bar_Greater f formula_to_string in
               FStar_Compiler_Util.format3 "(%s:%s{%s})" uu___3 uu___4 uu___5
           | FStar_Syntax_Syntax.Tm_app
               { FStar_Syntax_Syntax.hd = t;
                 FStar_Syntax_Syntax.args = args;_}
               ->
               let uu___3 = term_to_string t in
               let uu___4 = args_to_string args in
               FStar_Compiler_Util.format2 "(%s %s)" uu___3 uu___4
           | FStar_Syntax_Syntax.Tm_let
               { FStar_Syntax_Syntax.lbs = lbs;
                 FStar_Syntax_Syntax.body1 = e;_}
               ->
               let uu___3 = lbs_to_string [] lbs in
               let uu___4 = term_to_string e in
               FStar_Compiler_Util.format2 "%s\nin\n%s" uu___3 uu___4
           | FStar_Syntax_Syntax.Tm_ascribed
               { FStar_Syntax_Syntax.tm = e;
                 FStar_Syntax_Syntax.asc = (annot, topt, b);
                 FStar_Syntax_Syntax.eff_opt = eff_name;_}
               ->
               let annot1 =
                 match annot with
                 | FStar_Pervasives.Inl t ->
                     let uu___3 =
                       let uu___4 =
                         FStar_Compiler_Util.map_opt eff_name
                           FStar_Ident.string_of_lid in
                       FStar_Compiler_Effect.op_Bar_Greater uu___4
                         (FStar_Compiler_Util.dflt "default") in
                     let uu___4 = term_to_string t in
                     FStar_Compiler_Util.format2 "[%s] %s" uu___3 uu___4
                 | FStar_Pervasives.Inr c -> comp_to_string c in
               let topt1 =
                 match topt with
                 | FStar_Pervasives_Native.None -> ""
                 | FStar_Pervasives_Native.Some t ->
                     let uu___3 = term_to_string t in
                     FStar_Compiler_Util.format1 "by %s" uu___3 in
               let s = if b then "ascribed_eq" else "ascribed" in
               let uu___3 = term_to_string e in
               FStar_Compiler_Util.format4 "(%s <%s: %s %s)" uu___3 s annot1
                 topt1
           | FStar_Syntax_Syntax.Tm_match
               { FStar_Syntax_Syntax.scrutinee = head;
                 FStar_Syntax_Syntax.ret_opt = asc_opt;
                 FStar_Syntax_Syntax.brs = branches;
                 FStar_Syntax_Syntax.rc_opt1 = lc;_}
               ->
               let lc_str =
                 match lc with
                 | FStar_Pervasives_Native.Some lc1 when
                     FStar_Options.print_implicits () ->
                     let uu___3 =
                       if
                         FStar_Compiler_Option.isNone
                           lc1.FStar_Syntax_Syntax.residual_typ
                       then "None"
                       else
                         (let uu___5 =
                            FStar_Compiler_Option.get
                              lc1.FStar_Syntax_Syntax.residual_typ in
                          term_to_string uu___5) in
                     FStar_Compiler_Util.format1 " (residual_comp:%s)" uu___3
                 | uu___3 -> "" in
               let uu___3 = term_to_string head in
               let uu___4 =
                 match asc_opt with
                 | FStar_Pervasives_Native.None -> ""
                 | FStar_Pervasives_Native.Some (b, (asc, tacopt, use_eq)) ->
                     let s = if use_eq then "returns$" else "returns" in
                     let uu___5 = binder_to_string b in
                     let uu___6 =
                       match asc with
                       | FStar_Pervasives.Inl t -> term_to_string t
                       | FStar_Pervasives.Inr c -> comp_to_string c in
                     let uu___7 =
                       match tacopt with
                       | FStar_Pervasives_Native.None -> ""
                       | FStar_Pervasives_Native.Some tac ->
                           let uu___8 = term_to_string tac in
                           FStar_Compiler_Util.format1 " by %s" uu___8 in
                     FStar_Compiler_Util.format4 "as %s %s %s%s " uu___5 s
                       uu___6 uu___7 in
               let uu___5 =
                 let uu___6 =
                   FStar_Compiler_Effect.op_Bar_Greater branches
                     (FStar_Compiler_List.map branch_to_string) in
                 FStar_Compiler_Util.concat_l "\n\t|" uu___6 in
               FStar_Compiler_Util.format4 "(match %s %swith\n\t| %s%s)"
                 uu___3 uu___4 uu___5 lc_str
           | FStar_Syntax_Syntax.Tm_uinst (t, us) ->
               let uu___3 = FStar_Options.print_universes () in
               if uu___3
               then
                 let uu___4 = term_to_string t in
                 let uu___5 = univs_to_string us in
                 FStar_Compiler_Util.format2 "%s<%s>" uu___4 uu___5
               else term_to_string t
           | FStar_Syntax_Syntax.Tm_unknown -> "_")
and (branch_to_string : FStar_Syntax_Syntax.branch -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | (p, wopt, e) ->
        let uu___1 = FStar_Compiler_Effect.op_Bar_Greater p pat_to_string in
        let uu___2 =
          match wopt with
          | FStar_Pervasives_Native.None -> ""
          | FStar_Pervasives_Native.Some w ->
              let uu___3 =
                FStar_Compiler_Effect.op_Bar_Greater w term_to_string in
              FStar_Compiler_Util.format1 "when %s" uu___3 in
        let uu___3 = FStar_Compiler_Effect.op_Bar_Greater e term_to_string in
        FStar_Compiler_Util.format3 "%s %s -> %s" uu___1 uu___2 uu___3
and (ctx_uvar_to_string_aux :
  Prims.bool -> FStar_Syntax_Syntax.ctx_uvar -> Prims.string) =
  fun print_reason ->
    fun ctx_uvar ->
      let reason_string =
        if print_reason
        then
          FStar_Compiler_Util.format1 "(* %s *)\n"
            ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_reason
        else
          (let uu___1 =
             let uu___2 =
               FStar_Compiler_Range_Ops.start_of_range
                 ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_range in
             FStar_Compiler_Range_Ops.string_of_pos uu___2 in
           let uu___2 =
             let uu___3 =
               FStar_Compiler_Range_Ops.end_of_range
                 ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_range in
             FStar_Compiler_Range_Ops.string_of_pos uu___3 in
           FStar_Compiler_Util.format2 "(%s-%s) " uu___1 uu___2) in
      let uu___ =
        binders_to_string ", " ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_binders in
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
and (subst_elt_to_string : FStar_Syntax_Syntax.subst_elt -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | FStar_Syntax_Syntax.DB (i, x) ->
        let uu___1 = FStar_Compiler_Util.string_of_int i in
        let uu___2 = bv_to_string x in
        FStar_Compiler_Util.format2 "DB (%s, %s)" uu___1 uu___2
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
and (subst_to_string : FStar_Syntax_Syntax.subst_t -> Prims.string) =
  fun s ->
    let uu___ =
      FStar_Compiler_Effect.op_Bar_Greater s
        (FStar_Compiler_List.map subst_elt_to_string) in
    FStar_Compiler_Effect.op_Bar_Greater uu___
      (FStar_Compiler_String.concat "; ")
and (pat_to_string : FStar_Syntax_Syntax.pat -> Prims.string) =
  fun x ->
    let uu___ =
      let uu___1 = FStar_Options.ugly () in Prims.op_Negation uu___1 in
    if uu___
    then FStar_Syntax_Print_Pretty.pat_to_string x
    else
      (match x.FStar_Syntax_Syntax.v with
       | FStar_Syntax_Syntax.Pat_cons (l, us_opt, pats) ->
           let uu___2 = fv_to_string l in
           let uu___3 =
             let uu___4 =
               let uu___5 = FStar_Options.print_universes () in
               Prims.op_Negation uu___5 in
             if uu___4
             then " "
             else
               (match us_opt with
                | FStar_Pervasives_Native.None -> " "
                | FStar_Pervasives_Native.Some us ->
                    let uu___6 =
                      let uu___7 = FStar_Compiler_List.map univ_to_string us in
                      FStar_Compiler_Effect.op_Bar_Greater uu___7
                        (FStar_Compiler_String.concat " ") in
                    FStar_Compiler_Util.format1 " %s " uu___6) in
           let uu___4 =
             let uu___5 =
               FStar_Compiler_List.map
                 (fun uu___6 ->
                    match uu___6 with
                    | (x1, b) ->
                        let p = pat_to_string x1 in
                        if b then Prims.strcat "#" p else p) pats in
             FStar_Compiler_Effect.op_Bar_Greater uu___5
               (FStar_Compiler_String.concat " ") in
           FStar_Compiler_Util.format3 "(%s%s%s)" uu___2 uu___3 uu___4
       | FStar_Syntax_Syntax.Pat_dot_term topt ->
           let uu___2 = FStar_Options.print_bound_var_types () in
           if uu___2
           then
             let uu___3 =
               if topt = FStar_Pervasives_Native.None
               then "_"
               else
                 (let uu___5 =
                    FStar_Compiler_Effect.op_Bar_Greater topt
                      FStar_Compiler_Util.must in
                  FStar_Compiler_Effect.op_Bar_Greater uu___5 term_to_string) in
             FStar_Compiler_Util.format1 ".%s" uu___3
           else "._"
       | FStar_Syntax_Syntax.Pat_var x1 ->
           let uu___2 = FStar_Options.print_bound_var_types () in
           if uu___2
           then
             let uu___3 = bv_to_string x1 in
             let uu___4 = term_to_string x1.FStar_Syntax_Syntax.sort in
             FStar_Compiler_Util.format2 "%s:%s" uu___3 uu___4
           else bv_to_string x1
       | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c)
and (lbs_to_string :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    FStar_Syntax_Syntax.letbindings -> Prims.string)
  =
  fun quals ->
    fun lbs ->
      let uu___ = quals_to_string' quals in
      let uu___1 =
        let uu___2 =
          FStar_Compiler_Effect.op_Bar_Greater
            (FStar_Pervasives_Native.snd lbs)
            (FStar_Compiler_List.map
               (fun lb ->
                  let uu___3 = attrs_to_string lb.FStar_Syntax_Syntax.lbattrs in
                  let uu___4 = lbname_to_string lb.FStar_Syntax_Syntax.lbname in
                  let uu___5 =
                    let uu___6 = FStar_Options.print_universes () in
                    if uu___6
                    then
                      let uu___7 =
                        let uu___8 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs in
                        Prims.strcat uu___8 ">" in
                      Prims.strcat "<" uu___7
                    else "" in
                  let uu___6 = term_to_string lb.FStar_Syntax_Syntax.lbtyp in
                  let uu___7 =
                    FStar_Compiler_Effect.op_Bar_Greater
                      lb.FStar_Syntax_Syntax.lbdef term_to_string in
                  FStar_Compiler_Util.format5 "%s%s %s : %s = %s" uu___3
                    uu___4 uu___5 uu___6 uu___7)) in
        FStar_Compiler_Util.concat_l "\n and " uu___2 in
      FStar_Compiler_Util.format3 "%slet %s %s" uu___
        (if FStar_Pervasives_Native.fst lbs then "rec" else "") uu___1
and (attrs_to_string :
  FStar_Syntax_Syntax.attribute Prims.list -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | [] -> ""
    | tms ->
        let uu___1 =
          let uu___2 =
            FStar_Compiler_List.map
              (fun t -> let uu___3 = term_to_string t in paren uu___3) tms in
          FStar_Compiler_Effect.op_Bar_Greater uu___2
            (FStar_Compiler_String.concat "; ") in
        FStar_Compiler_Util.format1 "[@ %s]" uu___1
and (bqual_to_string' :
  Prims.string ->
    FStar_Syntax_Syntax.binder_qualifier FStar_Pervasives_Native.option ->
      Prims.string)
  =
  fun s ->
    fun uu___ ->
      match uu___ with
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
          let uu___1 =
            let uu___2 = term_to_string t in
            Prims.strcat uu___2 (Prims.strcat "]" s) in
          Prims.strcat "#[" uu___1
      | FStar_Pervasives_Native.None -> s
and (aqual_to_string' :
  Prims.string ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
      Prims.string)
  =
  fun s ->
    fun uu___ ->
      match uu___ with
      | FStar_Pervasives_Native.Some
          { FStar_Syntax_Syntax.aqual_implicit = true;
            FStar_Syntax_Syntax.aqual_attributes = uu___1;_}
          -> Prims.strcat "#" s
      | uu___1 -> s
and (binder_to_string' :
  Prims.bool -> FStar_Syntax_Syntax.binder -> Prims.string) =
  fun is_arrow ->
    fun b ->
      let uu___ =
        let uu___1 = FStar_Options.ugly () in Prims.op_Negation uu___1 in
      if uu___
      then FStar_Syntax_Print_Pretty.binder_to_string' is_arrow b
      else
        (let attrs = attrs_to_string b.FStar_Syntax_Syntax.binder_attrs in
         let uu___2 = FStar_Syntax_Syntax.is_null_binder b in
         if uu___2
         then
           let uu___3 =
             let uu___4 =
               term_to_string
                 (b.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort in
             Prims.strcat "_:" uu___4 in
           Prims.strcat attrs uu___3
         else
           (let uu___4 =
              (Prims.op_Negation is_arrow) &&
                (let uu___5 = FStar_Options.print_bound_var_types () in
                 Prims.op_Negation uu___5) in
            if uu___4
            then
              let uu___5 =
                let uu___6 = nm_to_string b.FStar_Syntax_Syntax.binder_bv in
                Prims.strcat attrs uu___6 in
              bqual_to_string' uu___5 b.FStar_Syntax_Syntax.binder_qual
            else
              (let uu___6 =
                 let uu___7 =
                   let uu___8 = nm_to_string b.FStar_Syntax_Syntax.binder_bv in
                   let uu___9 =
                     let uu___10 =
                       term_to_string
                         (b.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort in
                     Prims.strcat ":" uu___10 in
                   Prims.strcat uu___8 uu___9 in
                 Prims.strcat attrs uu___7 in
               bqual_to_string' uu___6 b.FStar_Syntax_Syntax.binder_qual)))
and (binder_to_string : FStar_Syntax_Syntax.binder -> Prims.string) =
  fun b -> binder_to_string' false b
and (arrow_binder_to_string : FStar_Syntax_Syntax.binder -> Prims.string) =
  fun b -> binder_to_string' true b
and (binders_to_string :
  Prims.string -> FStar_Syntax_Syntax.binders -> Prims.string) =
  fun sep ->
    fun bs ->
      let bs1 =
        let uu___ = FStar_Options.print_implicits () in
        if uu___ then bs else filter_imp_binders bs in
      if sep = " -> "
      then
        let uu___ =
          FStar_Compiler_Effect.op_Bar_Greater bs1
            (FStar_Compiler_List.map arrow_binder_to_string) in
        FStar_Compiler_Effect.op_Bar_Greater uu___
          (FStar_Compiler_String.concat sep)
      else
        (let uu___1 =
           FStar_Compiler_Effect.op_Bar_Greater bs1
             (FStar_Compiler_List.map binder_to_string) in
         FStar_Compiler_Effect.op_Bar_Greater uu___1
           (FStar_Compiler_String.concat sep))
and (arg_to_string :
  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) -> Prims.string)
  =
  fun uu___ ->
    match uu___ with
    | (a, imp) ->
        let uu___1 = term_to_string a in aqual_to_string' uu___1 imp
and (args_to_string : FStar_Syntax_Syntax.args -> Prims.string) =
  fun args ->
    let args1 =
      let uu___ = FStar_Options.print_implicits () in
      if uu___ then args else filter_imp_args args in
    let uu___ =
      FStar_Compiler_Effect.op_Bar_Greater args1
        (FStar_Compiler_List.map arg_to_string) in
    FStar_Compiler_Effect.op_Bar_Greater uu___
      (FStar_Compiler_String.concat " ")
and (comp_to_string : FStar_Syntax_Syntax.comp -> Prims.string) =
  fun c ->
    let uu___ =
      let uu___1 = FStar_Options.ugly () in Prims.op_Negation uu___1 in
    if uu___
    then FStar_Syntax_Print_Pretty.comp_to_string c
    else
      FStar_Errors.with_ctx "While ugly-printing a computation"
        (fun uu___2 ->
           match c.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total t ->
               let uu___3 =
                 let uu___4 = FStar_Syntax_Subst.compress t in
                 uu___4.FStar_Syntax_Syntax.n in
               (match uu___3 with
                | FStar_Syntax_Syntax.Tm_type uu___4 when
                    let uu___5 =
                      (FStar_Options.print_implicits ()) ||
                        (FStar_Options.print_universes ()) in
                    Prims.op_Negation uu___5 -> term_to_string t
                | uu___4 ->
                    let uu___5 = term_to_string t in
                    FStar_Compiler_Util.format1 "Tot %s" uu___5)
           | FStar_Syntax_Syntax.GTotal t ->
               let uu___3 =
                 let uu___4 = FStar_Syntax_Subst.compress t in
                 uu___4.FStar_Syntax_Syntax.n in
               (match uu___3 with
                | FStar_Syntax_Syntax.Tm_type uu___4 when
                    let uu___5 =
                      (FStar_Options.print_implicits ()) ||
                        (FStar_Options.print_universes ()) in
                    Prims.op_Negation uu___5 -> term_to_string t
                | uu___4 ->
                    let uu___5 = term_to_string t in
                    FStar_Compiler_Util.format1 "GTot %s" uu___5)
           | FStar_Syntax_Syntax.Comp c1 ->
               let basic =
                 let uu___3 = FStar_Options.print_effect_args () in
                 if uu___3
                 then
                   let uu___4 = sli c1.FStar_Syntax_Syntax.effect_name in
                   let uu___5 =
                     let uu___6 =
                       FStar_Compiler_Effect.op_Bar_Greater
                         c1.FStar_Syntax_Syntax.comp_univs
                         (FStar_Compiler_List.map univ_to_string) in
                     FStar_Compiler_Effect.op_Bar_Greater uu___6
                       (FStar_Compiler_String.concat ", ") in
                   let uu___6 =
                     term_to_string c1.FStar_Syntax_Syntax.result_typ in
                   let uu___7 =
                     let uu___8 =
                       FStar_Compiler_Effect.op_Bar_Greater
                         c1.FStar_Syntax_Syntax.effect_args
                         (FStar_Compiler_List.map arg_to_string) in
                     FStar_Compiler_Effect.op_Bar_Greater uu___8
                       (FStar_Compiler_String.concat ", ") in
                   let uu___8 = cflags_to_string c1.FStar_Syntax_Syntax.flags in
                   FStar_Compiler_Util.format5
                     "%s<%s> (%s) %s (attributes %s)" uu___4 uu___5 uu___6
                     uu___7 uu___8
                 else
                   (let uu___5 =
                      (FStar_Compiler_Effect.op_Bar_Greater
                         c1.FStar_Syntax_Syntax.flags
                         (FStar_Compiler_Util.for_some
                            (fun uu___6 ->
                               match uu___6 with
                               | FStar_Syntax_Syntax.TOTAL -> true
                               | uu___7 -> false)))
                        &&
                        (let uu___6 = FStar_Options.print_effect_args () in
                         Prims.op_Negation uu___6) in
                    if uu___5
                    then
                      let uu___6 =
                        term_to_string c1.FStar_Syntax_Syntax.result_typ in
                      FStar_Compiler_Util.format1 "Tot %s" uu___6
                    else
                      (let uu___7 =
                         ((let uu___8 = FStar_Options.print_effect_args () in
                           Prims.op_Negation uu___8) &&
                            (let uu___8 = FStar_Options.print_implicits () in
                             Prims.op_Negation uu___8))
                           &&
                           (let uu___8 = FStar_Parser_Const.effect_ML_lid () in
                            FStar_Ident.lid_equals
                              c1.FStar_Syntax_Syntax.effect_name uu___8) in
                       if uu___7
                       then term_to_string c1.FStar_Syntax_Syntax.result_typ
                       else
                         (let uu___9 =
                            (let uu___10 = FStar_Options.print_effect_args () in
                             Prims.op_Negation uu___10) &&
                              (FStar_Compiler_Effect.op_Bar_Greater
                                 c1.FStar_Syntax_Syntax.flags
                                 (FStar_Compiler_Util.for_some
                                    (fun uu___10 ->
                                       match uu___10 with
                                       | FStar_Syntax_Syntax.MLEFFECT -> true
                                       | uu___11 -> false))) in
                          if uu___9
                          then
                            let uu___10 =
                              term_to_string
                                c1.FStar_Syntax_Syntax.result_typ in
                            FStar_Compiler_Util.format1 "ALL %s" uu___10
                          else
                            (let uu___11 =
                               sli c1.FStar_Syntax_Syntax.effect_name in
                             let uu___12 =
                               term_to_string
                                 c1.FStar_Syntax_Syntax.result_typ in
                             FStar_Compiler_Util.format2 "%s (%s)" uu___11
                               uu___12)))) in
               let dec =
                 let uu___3 =
                   FStar_Compiler_Effect.op_Bar_Greater
                     c1.FStar_Syntax_Syntax.flags
                     (FStar_Compiler_List.collect
                        (fun uu___4 ->
                           match uu___4 with
                           | FStar_Syntax_Syntax.DECREASES dec_order ->
                               (match dec_order with
                                | FStar_Syntax_Syntax.Decreases_lex l ->
                                    let uu___5 =
                                      let uu___6 =
                                        match l with
                                        | [] -> ""
                                        | hd::tl ->
                                            let uu___7 =
                                              let uu___8 = term_to_string hd in
                                              FStar_Compiler_List.fold_left
                                                (fun s ->
                                                   fun t ->
                                                     let uu___9 =
                                                       let uu___10 =
                                                         term_to_string t in
                                                       Prims.strcat ";"
                                                         uu___10 in
                                                     Prims.strcat s uu___9)
                                                uu___8 in
                                            FStar_Compiler_Effect.op_Bar_Greater
                                              tl uu___7 in
                                      FStar_Compiler_Util.format1
                                        " (decreases [%s])" uu___6 in
                                    [uu___5]
                                | FStar_Syntax_Syntax.Decreases_wf (rel, e)
                                    ->
                                    let uu___5 =
                                      let uu___6 = term_to_string rel in
                                      let uu___7 = term_to_string e in
                                      FStar_Compiler_Util.format2
                                        "(decreases {:well-founded %s %s})"
                                        uu___6 uu___7 in
                                    [uu___5])
                           | uu___5 -> [])) in
                 FStar_Compiler_Effect.op_Bar_Greater uu___3
                   (FStar_Compiler_String.concat " ") in
               FStar_Compiler_Util.format2 "%s%s" basic dec)
and (cflag_to_string : FStar_Syntax_Syntax.cflag -> Prims.string) =
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
    | FStar_Syntax_Syntax.DECREASES uu___ -> ""
and (cflags_to_string : FStar_Syntax_Syntax.cflag Prims.list -> Prims.string)
  = fun fs -> (FStar_Common.string_of_list ()) cflag_to_string fs
and (formula_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun phi -> term_to_string phi
and (metadata_to_string : FStar_Syntax_Syntax.metadata -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | FStar_Syntax_Syntax.Meta_pattern (uu___1, ps) ->
        let pats =
          let uu___2 =
            FStar_Compiler_Effect.op_Bar_Greater ps
              (FStar_Compiler_List.map
                 (fun args ->
                    let uu___3 =
                      FStar_Compiler_Effect.op_Bar_Greater args
                        (FStar_Compiler_List.map
                           (fun uu___4 ->
                              match uu___4 with
                              | (t, uu___5) -> term_to_string t)) in
                    FStar_Compiler_Effect.op_Bar_Greater uu___3
                      (FStar_Compiler_String.concat "; "))) in
          FStar_Compiler_Effect.op_Bar_Greater uu___2
            (FStar_Compiler_String.concat "\\/") in
        FStar_Compiler_Util.format1 "{Meta_pattern %s}" pats
    | FStar_Syntax_Syntax.Meta_named lid ->
        let uu___1 = sli lid in
        FStar_Compiler_Util.format1 "{Meta_named %s}" uu___1
    | FStar_Syntax_Syntax.Meta_labeled (l, r, uu___1) ->
        let uu___2 = FStar_Compiler_Range_Ops.string_of_range r in
        FStar_Compiler_Util.format2 "{Meta_labeled (%s, %s)}" l uu___2
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
let (aqual_to_string : FStar_Syntax_Syntax.aqual -> Prims.string) =
  fun aq -> aqual_to_string' "" aq
let (bqual_to_string : FStar_Syntax_Syntax.bqual -> Prims.string) =
  fun bq -> bqual_to_string' "" bq
let (comp_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env ->
    fun c ->
      let uu___ = FStar_Options.ugly () in
      if uu___
      then comp_to_string c
      else FStar_Syntax_Print_Pretty.comp_to_string' env c
let (term_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun env ->
    fun x ->
      let uu___ = FStar_Options.ugly () in
      if uu___
      then term_to_string x
      else FStar_Syntax_Print_Pretty.term_to_string' env x
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
let (enclose_universes : Prims.string -> Prims.string) =
  fun s ->
    let uu___ = FStar_Options.print_universes () in
    if uu___ then Prims.strcat "<" (Prims.strcat s ">") else ""
let (tscheme_to_string : FStar_Syntax_Syntax.tscheme -> Prims.string) =
  fun s ->
    let uu___ =
      let uu___1 = FStar_Options.ugly () in Prims.op_Negation uu___1 in
    if uu___
    then FStar_Syntax_Print_Pretty.tscheme_to_string s
    else
      (let uu___2 = s in
       match uu___2 with
       | (us, t) ->
           let uu___3 =
             let uu___4 = univ_names_to_string us in
             FStar_Compiler_Effect.op_Less_Bar enclose_universes uu___4 in
           let uu___4 = term_to_string t in
           FStar_Compiler_Util.format2 "%s%s" uu___3 uu___4)
let (action_to_string : FStar_Syntax_Syntax.action -> Prims.string) =
  fun a ->
    let uu___ = sli a.FStar_Syntax_Syntax.action_name in
    let uu___1 = binders_to_string " " a.FStar_Syntax_Syntax.action_params in
    let uu___2 =
      let uu___3 = univ_names_to_string a.FStar_Syntax_Syntax.action_univs in
      FStar_Compiler_Effect.op_Less_Bar enclose_universes uu___3 in
    let uu___3 = term_to_string a.FStar_Syntax_Syntax.action_typ in
    let uu___4 = term_to_string a.FStar_Syntax_Syntax.action_defn in
    FStar_Compiler_Util.format5 "%s%s %s : %s = %s" uu___ uu___1 uu___2
      uu___3 uu___4
let (wp_eff_combinators_to_string :
  FStar_Syntax_Syntax.wp_eff_combinators -> Prims.string) =
  fun combs ->
    let tscheme_opt_to_string uu___ =
      match uu___ with
      | FStar_Pervasives_Native.Some ts -> tscheme_to_string ts
      | FStar_Pervasives_Native.None -> "None" in
    let uu___ =
      let uu___1 = tscheme_to_string combs.FStar_Syntax_Syntax.ret_wp in
      let uu___2 =
        let uu___3 = tscheme_to_string combs.FStar_Syntax_Syntax.bind_wp in
        let uu___4 =
          let uu___5 = tscheme_to_string combs.FStar_Syntax_Syntax.stronger in
          let uu___6 =
            let uu___7 =
              tscheme_to_string combs.FStar_Syntax_Syntax.if_then_else in
            let uu___8 =
              let uu___9 = tscheme_to_string combs.FStar_Syntax_Syntax.ite_wp in
              let uu___10 =
                let uu___11 =
                  tscheme_to_string combs.FStar_Syntax_Syntax.close_wp in
                let uu___12 =
                  let uu___13 =
                    tscheme_to_string combs.FStar_Syntax_Syntax.trivial in
                  let uu___14 =
                    let uu___15 =
                      tscheme_opt_to_string combs.FStar_Syntax_Syntax.repr in
                    let uu___16 =
                      let uu___17 =
                        tscheme_opt_to_string
                          combs.FStar_Syntax_Syntax.return_repr in
                      let uu___18 =
                        let uu___19 =
                          tscheme_opt_to_string
                            combs.FStar_Syntax_Syntax.bind_repr in
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
    FStar_Compiler_Util.format
      "{\nret_wp       = %s\n; bind_wp      = %s\n; stronger     = %s\n; if_then_else = %s\n; ite_wp       = %s\n; close_wp     = %s\n; trivial      = %s\n; repr         = %s\n; return_repr  = %s\n; bind_repr    = %s\n}\n"
      uu___
let (indexed_effect_binder_kind_to_string :
  FStar_Syntax_Syntax.indexed_effect_binder_kind -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | FStar_Syntax_Syntax.Type_binder -> "type_binder"
    | FStar_Syntax_Syntax.Substitutive_binder -> "subst_binder"
    | FStar_Syntax_Syntax.BindCont_no_abstraction_binder ->
        "bind_g_no_abs_binder"
    | FStar_Syntax_Syntax.Range_binder -> "range_binder"
    | FStar_Syntax_Syntax.Repr_binder -> "repr_binder"
    | FStar_Syntax_Syntax.Ad_hoc_binder -> "ad_hoc_binder"
let (indexed_effect_combinator_kind_to_string :
  FStar_Syntax_Syntax.indexed_effect_combinator_kind -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | FStar_Syntax_Syntax.Substitutive_combinator l ->
        let uu___1 =
          (FStar_Common.string_of_list' ())
            indexed_effect_binder_kind_to_string l in
        FStar_Compiler_Util.format1 "standard_combinator (%s)" uu___1
    | FStar_Syntax_Syntax.Substitutive_invariant_combinator ->
        "substitutive_invariant"
    | FStar_Syntax_Syntax.Ad_hoc_combinator -> "ad_hoc_combinator"
let (indexed_effect_combinator_kind_opt_to_string :
  FStar_Syntax_Syntax.indexed_effect_combinator_kind
    FStar_Pervasives_Native.option -> Prims.string)
  =
  fun k ->
    match k with
    | FStar_Pervasives_Native.None -> "kind not set"
    | FStar_Pervasives_Native.Some k1 ->
        indexed_effect_combinator_kind_to_string k1
let (layered_eff_combinators_to_string :
  FStar_Syntax_Syntax.layered_eff_combinators -> Prims.string) =
  fun combs ->
    let to_str uu___ =
      match uu___ with
      | (ts_t, ts_ty, kopt) ->
          let uu___1 = tscheme_to_string ts_t in
          let uu___2 = tscheme_to_string ts_ty in
          let uu___3 = indexed_effect_combinator_kind_opt_to_string kopt in
          FStar_Compiler_Util.format3 "(%s) : (%s)<%s>" uu___1 uu___2 uu___3 in
    let to_str2 uu___ =
      match uu___ with
      | (ts_t, ts_ty) ->
          let uu___1 = tscheme_to_string ts_t in
          let uu___2 = tscheme_to_string ts_ty in
          FStar_Compiler_Util.format2 "(%s) : (%s)" uu___1 uu___2 in
    let uu___ =
      let uu___1 = to_str2 combs.FStar_Syntax_Syntax.l_repr in
      let uu___2 =
        let uu___3 = to_str2 combs.FStar_Syntax_Syntax.l_return in
        let uu___4 =
          let uu___5 = to_str combs.FStar_Syntax_Syntax.l_bind in
          let uu___6 =
            let uu___7 = to_str combs.FStar_Syntax_Syntax.l_subcomp in
            let uu___8 =
              let uu___9 = to_str combs.FStar_Syntax_Syntax.l_if_then_else in
              let uu___10 =
                let uu___11 =
                  if
                    FStar_Pervasives_Native.uu___is_None
                      combs.FStar_Syntax_Syntax.l_close
                  then ""
                  else
                    (let uu___13 =
                       let uu___14 =
                         FStar_Compiler_Effect.op_Bar_Greater
                           combs.FStar_Syntax_Syntax.l_close
                           FStar_Compiler_Util.must in
                       FStar_Compiler_Effect.op_Bar_Greater uu___14 to_str2 in
                     FStar_Compiler_Util.format1 "; l_close = %s\n" uu___13) in
                [uu___11] in
              uu___9 :: uu___10 in
            uu___7 :: uu___8 in
          uu___5 :: uu___6 in
        uu___3 :: uu___4 in
      uu___1 :: uu___2 in
    FStar_Compiler_Util.format
      "{\n; l_repr = %s\n; l_return = %s\n; l_bind = %s\n; l_subcomp = %s\n; l_if_then_else = %s\n\n  %s\n  }\n"
      uu___
let (eff_combinators_to_string :
  FStar_Syntax_Syntax.eff_combinators -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | FStar_Syntax_Syntax.Primitive_eff combs ->
        wp_eff_combinators_to_string combs
    | FStar_Syntax_Syntax.DM4F_eff combs ->
        wp_eff_combinators_to_string combs
    | FStar_Syntax_Syntax.Layered_eff combs ->
        layered_eff_combinators_to_string combs
let (eff_extraction_mode_to_string :
  FStar_Syntax_Syntax.eff_extraction_mode -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | FStar_Syntax_Syntax.Extract_none s ->
        FStar_Compiler_Util.format1 "none (%s)" s
    | FStar_Syntax_Syntax.Extract_reify -> "reify"
    | FStar_Syntax_Syntax.Extract_primitive -> "primitive"
let (eff_decl_to_string' :
  Prims.bool ->
    FStar_Compiler_Range_Type.range ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Syntax_Syntax.eff_decl -> Prims.string)
  =
  fun for_free ->
    fun r ->
      fun q ->
        fun ed ->
          let uu___ =
            let uu___1 = FStar_Options.ugly () in Prims.op_Negation uu___1 in
          if uu___
          then FStar_Syntax_Print_Pretty.eff_decl_to_string' for_free r q ed
          else
            (let actions_to_string actions =
               let uu___2 =
                 FStar_Compiler_Effect.op_Bar_Greater actions
                   (FStar_Compiler_List.map action_to_string) in
               FStar_Compiler_Effect.op_Bar_Greater uu___2
                 (FStar_Compiler_String.concat ",\n\t") in
             let eff_name =
               let uu___2 = FStar_Syntax_Util.is_layered ed in
               if uu___2 then "layered_effect" else "new_effect" in
             let uu___2 =
               let uu___3 =
                 let uu___4 =
                   let uu___5 = lid_to_string ed.FStar_Syntax_Syntax.mname in
                   let uu___6 =
                     let uu___7 =
                       let uu___8 =
                         univ_names_to_string ed.FStar_Syntax_Syntax.univs in
                       FStar_Compiler_Effect.op_Less_Bar enclose_universes
                         uu___8 in
                     let uu___8 =
                       let uu___9 =
                         binders_to_string " " ed.FStar_Syntax_Syntax.binders in
                       let uu___10 =
                         let uu___11 =
                           let uu___12 =
                             FStar_Compiler_Effect.op_Bar_Greater
                               ed.FStar_Syntax_Syntax.signature
                               FStar_Syntax_Util.effect_sig_ts in
                           FStar_Compiler_Effect.op_Bar_Greater uu___12
                             tscheme_to_string in
                         let uu___12 =
                           let uu___13 =
                             eff_combinators_to_string
                               ed.FStar_Syntax_Syntax.combinators in
                           let uu___14 =
                             let uu___15 =
                               actions_to_string
                                 ed.FStar_Syntax_Syntax.actions in
                             [uu___15] in
                           uu___13 :: uu___14 in
                         uu___11 :: uu___12 in
                       uu___9 :: uu___10 in
                     uu___7 :: uu___8 in
                   uu___5 :: uu___6 in
                 (if for_free then "_for_free " else "") :: uu___4 in
               eff_name :: uu___3 in
             FStar_Compiler_Util.format
               "%s%s { %s%s %s : %s \n  %s\nand effect_actions\n\t%s\n}\n"
               uu___2)
let (eff_decl_to_string :
  Prims.bool -> FStar_Syntax_Syntax.eff_decl -> Prims.string) =
  fun for_free ->
    fun ed ->
      eff_decl_to_string' for_free FStar_Compiler_Range_Type.dummyRange [] ed
let (sub_eff_to_string : FStar_Syntax_Syntax.sub_eff -> Prims.string) =
  fun se ->
    let tsopt_to_string ts_opt =
      if FStar_Compiler_Util.is_some ts_opt
      then
        let uu___ =
          FStar_Compiler_Effect.op_Bar_Greater ts_opt
            FStar_Compiler_Util.must in
        FStar_Compiler_Effect.op_Bar_Greater uu___ tscheme_to_string
      else "<None>" in
    let uu___ = lid_to_string se.FStar_Syntax_Syntax.source in
    let uu___1 = lid_to_string se.FStar_Syntax_Syntax.target in
    let uu___2 = tsopt_to_string se.FStar_Syntax_Syntax.lift in
    let uu___3 = tsopt_to_string se.FStar_Syntax_Syntax.lift_wp in
    FStar_Compiler_Util.format4
      "sub_effect %s ~> %s : lift = %s ;; lift_wp = %s" uu___ uu___1 uu___2
      uu___3
let (pragma_to_string : FStar_Syntax_Syntax.pragma -> Prims.string) =
  fun p ->
    match p with
    | FStar_Syntax_Syntax.ResetOptions (FStar_Pervasives_Native.None) ->
        "#reset-options"
    | FStar_Syntax_Syntax.ResetOptions (FStar_Pervasives_Native.Some s) ->
        FStar_Compiler_Util.format1 "#reset-options \"%s\"" s
    | FStar_Syntax_Syntax.SetOptions s ->
        FStar_Compiler_Util.format1 "#set-options \"%s\"" s
    | FStar_Syntax_Syntax.PushOptions (FStar_Pervasives_Native.None) ->
        "#push-options"
    | FStar_Syntax_Syntax.PushOptions (FStar_Pervasives_Native.Some s) ->
        FStar_Compiler_Util.format1 "#push-options \"%s\"" s
    | FStar_Syntax_Syntax.RestartSolver -> "#restart-solver"
    | FStar_Syntax_Syntax.PrintEffectsGraph -> "#print-effects-graph"
    | FStar_Syntax_Syntax.PopOptions -> "#pop-options"
let rec (sigelt_to_string : FStar_Syntax_Syntax.sigelt -> Prims.string) =
  fun x ->
    let uu___ =
      let uu___1 = FStar_Options.ugly () in Prims.op_Negation uu___1 in
    if uu___
    then FStar_Syntax_Print_Pretty.sigelt_to_string x
    else
      (let basic =
         match x.FStar_Syntax_Syntax.sigel with
         | FStar_Syntax_Syntax.Sig_pragma p -> pragma_to_string p
         | FStar_Syntax_Syntax.Sig_inductive_typ
             { FStar_Syntax_Syntax.lid = lid; FStar_Syntax_Syntax.us = univs;
               FStar_Syntax_Syntax.params = tps;
               FStar_Syntax_Syntax.num_uniform_params = uu___2;
               FStar_Syntax_Syntax.t = k;
               FStar_Syntax_Syntax.mutuals = uu___3;
               FStar_Syntax_Syntax.ds = uu___4;_}
             ->
             let quals_str = quals_to_string' x.FStar_Syntax_Syntax.sigquals in
             let binders_str = binders_to_string " " tps in
             let term_str = term_to_string k in
             let uu___5 = FStar_Options.print_universes () in
             if uu___5
             then
               let uu___6 = FStar_Ident.string_of_lid lid in
               let uu___7 = univ_names_to_string univs in
               FStar_Compiler_Util.format5 "%stype %s<%s> %s : %s" quals_str
                 uu___6 uu___7 binders_str term_str
             else
               (let uu___7 = FStar_Ident.string_of_lid lid in
                FStar_Compiler_Util.format4 "%stype %s %s : %s" quals_str
                  uu___7 binders_str term_str)
         | FStar_Syntax_Syntax.Sig_datacon
             { FStar_Syntax_Syntax.lid1 = lid;
               FStar_Syntax_Syntax.us1 = univs; FStar_Syntax_Syntax.t1 = t;
               FStar_Syntax_Syntax.ty_lid = uu___2;
               FStar_Syntax_Syntax.num_ty_params = uu___3;
               FStar_Syntax_Syntax.mutuals1 = uu___4;_}
             ->
             let uu___5 = FStar_Options.print_universes () in
             if uu___5
             then
               let uu___6 = univ_names_to_string univs in
               let uu___7 = FStar_Ident.string_of_lid lid in
               let uu___8 = term_to_string t in
               FStar_Compiler_Util.format3 "datacon<%s> %s : %s" uu___6
                 uu___7 uu___8
             else
               (let uu___7 = FStar_Ident.string_of_lid lid in
                let uu___8 = term_to_string t in
                FStar_Compiler_Util.format2 "datacon %s : %s" uu___7 uu___8)
         | FStar_Syntax_Syntax.Sig_declare_typ
             { FStar_Syntax_Syntax.lid2 = lid;
               FStar_Syntax_Syntax.us2 = univs; FStar_Syntax_Syntax.t2 = t;_}
             ->
             let uu___2 = quals_to_string' x.FStar_Syntax_Syntax.sigquals in
             let uu___3 = FStar_Ident.string_of_lid lid in
             let uu___4 =
               let uu___5 = FStar_Options.print_universes () in
               if uu___5
               then
                 let uu___6 = univ_names_to_string univs in
                 FStar_Compiler_Util.format1 "<%s>" uu___6
               else "" in
             let uu___5 = term_to_string t in
             FStar_Compiler_Util.format4 "%sval %s %s : %s" uu___2 uu___3
               uu___4 uu___5
         | FStar_Syntax_Syntax.Sig_assume
             { FStar_Syntax_Syntax.lid3 = lid; FStar_Syntax_Syntax.us3 = us;
               FStar_Syntax_Syntax.phi1 = f;_}
             ->
             let uu___2 = FStar_Options.print_universes () in
             if uu___2
             then
               let uu___3 = FStar_Ident.string_of_lid lid in
               let uu___4 = univ_names_to_string us in
               let uu___5 = term_to_string f in
               FStar_Compiler_Util.format3 "assume %s<%s> : %s" uu___3 uu___4
                 uu___5
             else
               (let uu___4 = FStar_Ident.string_of_lid lid in
                let uu___5 = term_to_string f in
                FStar_Compiler_Util.format2 "assume %s : %s" uu___4 uu___5)
         | FStar_Syntax_Syntax.Sig_let
             { FStar_Syntax_Syntax.lbs1 = lbs;
               FStar_Syntax_Syntax.lids1 = uu___2;_}
             ->
             let lbs1 =
               let uu___3 =
                 FStar_Compiler_List.map
                   (fun lb ->
                      {
                        FStar_Syntax_Syntax.lbname =
                          (lb.FStar_Syntax_Syntax.lbname);
                        FStar_Syntax_Syntax.lbunivs =
                          (lb.FStar_Syntax_Syntax.lbunivs);
                        FStar_Syntax_Syntax.lbtyp =
                          (lb.FStar_Syntax_Syntax.lbtyp);
                        FStar_Syntax_Syntax.lbeff =
                          (lb.FStar_Syntax_Syntax.lbeff);
                        FStar_Syntax_Syntax.lbdef =
                          (lb.FStar_Syntax_Syntax.lbdef);
                        FStar_Syntax_Syntax.lbattrs = [];
                        FStar_Syntax_Syntax.lbpos =
                          (lb.FStar_Syntax_Syntax.lbpos)
                      }) (FStar_Pervasives_Native.snd lbs) in
               ((FStar_Pervasives_Native.fst lbs), uu___3) in
             lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs1
         | FStar_Syntax_Syntax.Sig_bundle
             { FStar_Syntax_Syntax.ses = ses;
               FStar_Syntax_Syntax.lids = uu___2;_}
             ->
             let uu___3 =
               let uu___4 = FStar_Compiler_List.map sigelt_to_string ses in
               FStar_Compiler_Effect.op_Bar_Greater uu___4
                 (FStar_Compiler_String.concat "\n") in
             Prims.strcat "(* Sig_bundle *)" uu___3
         | FStar_Syntax_Syntax.Sig_fail
             { FStar_Syntax_Syntax.errs = errs;
               FStar_Syntax_Syntax.fail_in_lax = lax;
               FStar_Syntax_Syntax.ses1 = ses;_}
             ->
             let uu___2 = FStar_Compiler_Util.string_of_bool lax in
             let uu___3 =
               (FStar_Common.string_of_list ())
                 FStar_Compiler_Util.string_of_int errs in
             let uu___4 =
               let uu___5 = FStar_Compiler_List.map sigelt_to_string ses in
               FStar_Compiler_Effect.op_Bar_Greater uu___5
                 (FStar_Compiler_String.concat "\n") in
             FStar_Compiler_Util.format3
               "(* Sig_fail %s %s *)\n%s\n(* / Sig_fail*)\n" uu___2 uu___3
               uu___4
         | FStar_Syntax_Syntax.Sig_new_effect ed ->
             let uu___2 = FStar_Syntax_Util.is_dm4f ed in
             eff_decl_to_string' uu___2 x.FStar_Syntax_Syntax.sigrng
               x.FStar_Syntax_Syntax.sigquals ed
         | FStar_Syntax_Syntax.Sig_sub_effect se -> sub_eff_to_string se
         | FStar_Syntax_Syntax.Sig_effect_abbrev
             { FStar_Syntax_Syntax.lid4 = l; FStar_Syntax_Syntax.us4 = univs;
               FStar_Syntax_Syntax.bs2 = tps; FStar_Syntax_Syntax.comp1 = c;
               FStar_Syntax_Syntax.cflags = flags;_}
             ->
             let uu___2 = FStar_Options.print_universes () in
             if uu___2
             then
               let uu___3 =
                 let uu___4 =
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_arrow
                        {
                          FStar_Syntax_Syntax.bs1 = tps;
                          FStar_Syntax_Syntax.comp = c
                        }) FStar_Compiler_Range_Type.dummyRange in
                 FStar_Syntax_Subst.open_univ_vars univs uu___4 in
               (match uu___3 with
                | (univs1, t) ->
                    let uu___4 =
                      let uu___5 =
                        let uu___6 = FStar_Syntax_Subst.compress t in
                        uu___6.FStar_Syntax_Syntax.n in
                      match uu___5 with
                      | FStar_Syntax_Syntax.Tm_arrow
                          { FStar_Syntax_Syntax.bs1 = bs;
                            FStar_Syntax_Syntax.comp = c1;_}
                          -> (bs, c1)
                      | uu___6 -> failwith "impossible" in
                    (match uu___4 with
                     | (tps1, c1) ->
                         let uu___5 = sli l in
                         let uu___6 = univ_names_to_string univs1 in
                         let uu___7 = binders_to_string " " tps1 in
                         let uu___8 = comp_to_string c1 in
                         FStar_Compiler_Util.format4 "effect %s<%s> %s = %s"
                           uu___5 uu___6 uu___7 uu___8))
             else
               (let uu___4 = sli l in
                let uu___5 = binders_to_string " " tps in
                let uu___6 = comp_to_string c in
                FStar_Compiler_Util.format3 "effect %s %s = %s" uu___4 uu___5
                  uu___6)
         | FStar_Syntax_Syntax.Sig_splice
             { FStar_Syntax_Syntax.is_typed = is_typed;
               FStar_Syntax_Syntax.lids2 = lids;
               FStar_Syntax_Syntax.tac = t;_}
             ->
             let uu___2 =
               let uu___3 =
                 FStar_Compiler_List.map FStar_Ident.string_of_lid lids in
               FStar_Compiler_Effect.op_Less_Bar
                 (FStar_Compiler_String.concat "; ") uu___3 in
             let uu___3 = term_to_string t in
             FStar_Compiler_Util.format3 "splice%s[%s] (%s)"
               (if is_typed then "_t" else "") uu___2 uu___3
         | FStar_Syntax_Syntax.Sig_polymonadic_bind
             { FStar_Syntax_Syntax.m_lid = m; FStar_Syntax_Syntax.n_lid = n;
               FStar_Syntax_Syntax.p_lid = p; FStar_Syntax_Syntax.tm3 = t;
               FStar_Syntax_Syntax.typ = ty; FStar_Syntax_Syntax.kind1 = k;_}
             ->
             let uu___2 = FStar_Ident.string_of_lid m in
             let uu___3 = FStar_Ident.string_of_lid n in
             let uu___4 = FStar_Ident.string_of_lid p in
             let uu___5 = tscheme_to_string t in
             let uu___6 = tscheme_to_string ty in
             let uu___7 = indexed_effect_combinator_kind_opt_to_string k in
             FStar_Compiler_Util.format6
               "polymonadic_bind (%s, %s) |> %s = (%s, %s)<%s>" uu___2 uu___3
               uu___4 uu___5 uu___6 uu___7
         | FStar_Syntax_Syntax.Sig_polymonadic_subcomp
             { FStar_Syntax_Syntax.m_lid1 = m;
               FStar_Syntax_Syntax.n_lid1 = n; FStar_Syntax_Syntax.tm4 = t;
               FStar_Syntax_Syntax.typ1 = ty;
               FStar_Syntax_Syntax.kind2 = k;_}
             ->
             let uu___2 = FStar_Ident.string_of_lid m in
             let uu___3 = FStar_Ident.string_of_lid n in
             let uu___4 = tscheme_to_string t in
             let uu___5 = tscheme_to_string ty in
             let uu___6 = indexed_effect_combinator_kind_opt_to_string k in
             FStar_Compiler_Util.format5
               "polymonadic_subcomp %s <: %s = (%s, %s)<%s>" uu___2 uu___3
               uu___4 uu___5 uu___6 in
       match x.FStar_Syntax_Syntax.sigattrs with
       | [] -> Prims.strcat "[@ ]" (Prims.strcat "\n" basic)
       | uu___2 ->
           let uu___3 = attrs_to_string x.FStar_Syntax_Syntax.sigattrs in
           Prims.strcat uu___3 (Prims.strcat "\n" basic))
let (sigelt_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.sigelt -> Prims.string) =
  fun env ->
    fun x ->
      let uu___ = FStar_Options.ugly () in
      if uu___
      then sigelt_to_string x
      else FStar_Syntax_Print_Pretty.sigelt_to_string' env x
let rec (sigelt_to_string_short : FStar_Syntax_Syntax.sigelt -> Prims.string)
  =
  fun x ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_pragma p -> pragma_to_string p
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
          FStar_Syntax_Syntax.ds = uu___5;_}
        ->
        let uu___6 = FStar_Ident.string_of_lid lid in
        FStar_Compiler_Util.format1 "type %s" uu___6
    | FStar_Syntax_Syntax.Sig_datacon
        { FStar_Syntax_Syntax.lid1 = lid; FStar_Syntax_Syntax.us1 = uu___;
          FStar_Syntax_Syntax.t1 = uu___1;
          FStar_Syntax_Syntax.ty_lid = t_lid;
          FStar_Syntax_Syntax.num_ty_params = uu___2;
          FStar_Syntax_Syntax.mutuals1 = uu___3;_}
        ->
        let uu___4 = FStar_Ident.string_of_lid lid in
        let uu___5 = FStar_Ident.string_of_lid t_lid in
        FStar_Compiler_Util.format2 "datacon %s for type %s" uu___4 uu___5
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
        FStar_Compiler_Effect.op_Bar_Greater uu___1 sigelt_to_string_short
    | FStar_Syntax_Syntax.Sig_fail
        { FStar_Syntax_Syntax.errs = uu___;
          FStar_Syntax_Syntax.fail_in_lax = uu___1;
          FStar_Syntax_Syntax.ses1 = ses;_}
        ->
        let uu___2 =
          let uu___3 =
            FStar_Compiler_Effect.op_Bar_Greater ses FStar_Compiler_List.hd in
          FStar_Compiler_Effect.op_Bar_Greater uu___3 sigelt_to_string_short in
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
        let uu___3 = binders_to_string " " tps in
        let uu___4 = comp_to_string c in
        FStar_Compiler_Util.format3 "effect %s %s = %s" uu___2 uu___3 uu___4
    | FStar_Syntax_Syntax.Sig_splice
        { FStar_Syntax_Syntax.is_typed = is_typed;
          FStar_Syntax_Syntax.lids2 = lids;
          FStar_Syntax_Syntax.tac = uu___;_}
        ->
        let uu___1 =
          let uu___2 = FStar_Compiler_List.map FStar_Ident.string_of_lid lids in
          FStar_Compiler_Effect.op_Less_Bar
            (FStar_Compiler_String.concat "; ") uu___2 in
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
let (tag_of_sigelt : FStar_Syntax_Syntax.sigelt -> Prims.string) =
  fun se ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_inductive_typ uu___ -> "Sig_inductive_typ"
    | FStar_Syntax_Syntax.Sig_bundle uu___ -> "Sig_bundle"
    | FStar_Syntax_Syntax.Sig_datacon uu___ -> "Sig_datacon"
    | FStar_Syntax_Syntax.Sig_declare_typ uu___ -> "Sig_declare_typ"
    | FStar_Syntax_Syntax.Sig_let uu___ -> "Sig_let"
    | FStar_Syntax_Syntax.Sig_assume uu___ -> "Sig_assume"
    | FStar_Syntax_Syntax.Sig_new_effect uu___ -> "Sig_new_effect"
    | FStar_Syntax_Syntax.Sig_sub_effect uu___ -> "Sig_sub_effect"
    | FStar_Syntax_Syntax.Sig_effect_abbrev uu___ -> "Sig_effect_abbrev"
    | FStar_Syntax_Syntax.Sig_pragma uu___ -> "Sig_pragma"
    | FStar_Syntax_Syntax.Sig_splice uu___ -> "Sig_splice"
    | FStar_Syntax_Syntax.Sig_polymonadic_bind uu___ ->
        "Sig_polymonadic_bind"
    | FStar_Syntax_Syntax.Sig_polymonadic_subcomp uu___ ->
        "Sig_polymonadic_subcomp"
    | FStar_Syntax_Syntax.Sig_fail uu___ -> "Sig_fail"
let (modul_to_string : FStar_Syntax_Syntax.modul -> Prims.string) =
  fun m ->
    let uu___ = sli m.FStar_Syntax_Syntax.name in
    let uu___1 =
      let uu___2 =
        FStar_Compiler_List.map sigelt_to_string
          m.FStar_Syntax_Syntax.declarations in
      FStar_Compiler_Effect.op_Bar_Greater uu___2
        (FStar_Compiler_String.concat "\n") in
    let uu___2 =
      let uu___3 =
        FStar_Compiler_List.map sigelt_to_string
          m.FStar_Syntax_Syntax.declarations in
      FStar_Compiler_Effect.op_Bar_Greater uu___3
        (FStar_Compiler_String.concat "\n") in
    FStar_Compiler_Util.format3
      "module %s\nDeclarations: [\n%s\n]\nExports: [\n%s\n]\n" uu___ uu___1
      uu___2
let (bvs_to_string :
  Prims.string -> FStar_Syntax_Syntax.bv Prims.list -> Prims.string) =
  fun sep ->
    fun bvs ->
      let uu___ = FStar_Compiler_List.map FStar_Syntax_Syntax.mk_binder bvs in
      binders_to_string sep uu___
let (ctx_uvar_to_string : FStar_Syntax_Syntax.ctx_uvar -> Prims.string) =
  fun ctx_uvar -> ctx_uvar_to_string_aux true ctx_uvar
let (ctx_uvar_to_string_no_reason :
  FStar_Syntax_Syntax.ctx_uvar -> Prims.string) =
  fun ctx_uvar -> ctx_uvar_to_string_aux false ctx_uvar
let (fv_qual_to_string : FStar_Syntax_Syntax.fv_qual -> Prims.string) =
  fun fvq ->
    match fvq with
    | FStar_Syntax_Syntax.Data_ctor -> "Data_ctor"
    | FStar_Syntax_Syntax.Record_projector uu___ -> "Record_projector _"
    | FStar_Syntax_Syntax.Record_ctor uu___ -> "Record_ctor _"
    | FStar_Syntax_Syntax.Unresolved_projector uu___ ->
        "Unresolved_projector _"
    | FStar_Syntax_Syntax.Unresolved_constructor uu___ ->
        "Unresolved_constructor _"
let (term_to_doc' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.term -> FStar_Pprint.document)
  =
  fun dsenv ->
    fun t ->
      let uu___ = FStar_Options.ugly () in
      if uu___
      then
        let uu___1 = term_to_string t in FStar_Pprint.arbitrary_string uu___1
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
        let uu___1 = univ_to_string t in FStar_Pprint.arbitrary_string uu___1
      else FStar_Syntax_Print_Pretty.univ_to_doc' dsenv t
let (comp_to_doc' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.comp -> FStar_Pprint.document)
  =
  fun dsenv ->
    fun t ->
      let uu___ = FStar_Options.ugly () in
      if uu___
      then
        let uu___1 = comp_to_string t in FStar_Pprint.arbitrary_string uu___1
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
        let uu___1 = sigelt_to_string t in
        FStar_Pprint.arbitrary_string uu___1
      else FStar_Syntax_Print_Pretty.sigelt_to_doc' dsenv t
let (term_to_doc : FStar_Syntax_Syntax.term -> FStar_Pprint.document) =
  fun t ->
    let uu___ = FStar_Options.ugly () in
    if uu___
    then
      let uu___1 = term_to_string t in FStar_Pprint.arbitrary_string uu___1
    else FStar_Syntax_Print_Pretty.term_to_doc t
let (univ_to_doc : FStar_Syntax_Syntax.universe -> FStar_Pprint.document) =
  fun t ->
    let uu___ = FStar_Options.ugly () in
    if uu___
    then
      let uu___1 = univ_to_string t in FStar_Pprint.arbitrary_string uu___1
    else FStar_Syntax_Print_Pretty.univ_to_doc t
let (comp_to_doc : FStar_Syntax_Syntax.comp -> FStar_Pprint.document) =
  fun t ->
    let uu___ = FStar_Options.ugly () in
    if uu___
    then
      let uu___1 = comp_to_string t in FStar_Pprint.arbitrary_string uu___1
    else FStar_Syntax_Print_Pretty.comp_to_doc t
let (sigelt_to_doc : FStar_Syntax_Syntax.sigelt -> FStar_Pprint.document) =
  fun t ->
    let uu___ = FStar_Options.ugly () in
    if uu___
    then
      let uu___1 = sigelt_to_string t in FStar_Pprint.arbitrary_string uu___1
    else FStar_Syntax_Print_Pretty.sigelt_to_doc t
let (pretty_term : FStar_Syntax_Syntax.term FStar_Class_PP.pretty) =
  { FStar_Class_PP.pp = term_to_doc }
let (pretty_univ : FStar_Syntax_Syntax.universe FStar_Class_PP.pretty) =
  { FStar_Class_PP.pp = univ_to_doc }
let (pretty_sigelt : FStar_Syntax_Syntax.sigelt FStar_Class_PP.pretty) =
  { FStar_Class_PP.pp = sigelt_to_doc }
let (pretty_comp : FStar_Syntax_Syntax.comp FStar_Class_PP.pretty) =
  { FStar_Class_PP.pp = comp_to_doc }
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
let (showable_binder : FStar_Syntax_Syntax.binder FStar_Class_Show.showable)
  = { FStar_Class_Show.show = binder_to_string }
let (showable_uvar : FStar_Syntax_Syntax.uvar FStar_Class_Show.showable) =
  { FStar_Class_Show.show = uvar_to_string }
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
let (showable_pragma : FStar_Syntax_Syntax.pragma FStar_Class_Show.showable)
  = { FStar_Class_Show.show = pragma_to_string }