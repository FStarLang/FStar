open Prims
let (check_sigelt_quals_pre :
  FStarC_TypeChecker_Env.env -> FStarC_Syntax_Syntax.sigelt -> unit) =
  fun env ->
    fun se ->
      let visibility uu___ =
        match uu___ with
        | FStarC_Syntax_Syntax.Private -> true
        | uu___1 -> false in
      let reducibility uu___ =
        match uu___ with
        | FStarC_Syntax_Syntax.Irreducible -> true
        | FStarC_Syntax_Syntax.Unfold_for_unification_and_vcgen -> true
        | FStarC_Syntax_Syntax.Visible_default -> true
        | FStarC_Syntax_Syntax.Inline_for_extraction -> true
        | uu___1 -> false in
      let assumption uu___ =
        match uu___ with
        | FStarC_Syntax_Syntax.Assumption -> true
        | FStarC_Syntax_Syntax.New -> true
        | uu___1 -> false in
      let reification uu___ =
        match uu___ with
        | FStarC_Syntax_Syntax.Reifiable -> true
        | FStarC_Syntax_Syntax.Reflectable uu___1 -> true
        | uu___1 -> false in
      let inferred uu___ =
        match uu___ with
        | FStarC_Syntax_Syntax.Discriminator uu___1 -> true
        | FStarC_Syntax_Syntax.Projector uu___1 -> true
        | FStarC_Syntax_Syntax.RecordType uu___1 -> true
        | FStarC_Syntax_Syntax.RecordConstructor uu___1 -> true
        | FStarC_Syntax_Syntax.ExceptionConstructor -> true
        | FStarC_Syntax_Syntax.HasMaskedEffect -> true
        | FStarC_Syntax_Syntax.Effect -> true
        | uu___1 -> false in
      let has_eq uu___ =
        match uu___ with
        | FStarC_Syntax_Syntax.Noeq -> true
        | FStarC_Syntax_Syntax.Unopteq -> true
        | uu___1 -> false in
      let quals_combo_ok quals q =
        match q with
        | FStarC_Syntax_Syntax.Assumption ->
            FStarC_Compiler_List.for_all
              (fun x ->
                 ((((((x = q) || (x = FStarC_Syntax_Syntax.Logic)) ||
                       (inferred x))
                      || (visibility x))
                     || (assumption x))
                    ||
                    (env.FStarC_TypeChecker_Env.is_iface &&
                       (x = FStarC_Syntax_Syntax.Inline_for_extraction)))
                   || (x = FStarC_Syntax_Syntax.NoExtract)) quals
        | FStarC_Syntax_Syntax.New ->
            FStarC_Compiler_List.for_all
              (fun x ->
                 (((x = q) || (inferred x)) || (visibility x)) ||
                   (assumption x)) quals
        | FStarC_Syntax_Syntax.Inline_for_extraction ->
            FStarC_Compiler_List.for_all
              (fun x ->
                 ((((((((x = q) || (x = FStarC_Syntax_Syntax.Logic)) ||
                         (visibility x))
                        || (reducibility x))
                       || (reification x))
                      || (inferred x))
                     || (has_eq x))
                    ||
                    (env.FStarC_TypeChecker_Env.is_iface &&
                       (x = FStarC_Syntax_Syntax.Assumption)))
                   || (x = FStarC_Syntax_Syntax.NoExtract)) quals
        | FStarC_Syntax_Syntax.Unfold_for_unification_and_vcgen ->
            FStarC_Compiler_List.for_all
              (fun x ->
                 (((((((x = q) || (x = FStarC_Syntax_Syntax.Logic)) ||
                        (x = FStarC_Syntax_Syntax.Inline_for_extraction))
                       || (x = FStarC_Syntax_Syntax.NoExtract))
                      || (has_eq x))
                     || (inferred x))
                    || (visibility x))
                   || (reification x)) quals
        | FStarC_Syntax_Syntax.Visible_default ->
            FStarC_Compiler_List.for_all
              (fun x ->
                 (((((((x = q) || (x = FStarC_Syntax_Syntax.Logic)) ||
                        (x = FStarC_Syntax_Syntax.Inline_for_extraction))
                       || (x = FStarC_Syntax_Syntax.NoExtract))
                      || (has_eq x))
                     || (inferred x))
                    || (visibility x))
                   || (reification x)) quals
        | FStarC_Syntax_Syntax.Irreducible ->
            FStarC_Compiler_List.for_all
              (fun x ->
                 (((((((x = q) || (x = FStarC_Syntax_Syntax.Logic)) ||
                        (x = FStarC_Syntax_Syntax.Inline_for_extraction))
                       || (x = FStarC_Syntax_Syntax.NoExtract))
                      || (has_eq x))
                     || (inferred x))
                    || (visibility x))
                   || (reification x)) quals
        | FStarC_Syntax_Syntax.Noeq ->
            FStarC_Compiler_List.for_all
              (fun x ->
                 (((((((x = q) || (x = FStarC_Syntax_Syntax.Logic)) ||
                        (x = FStarC_Syntax_Syntax.Inline_for_extraction))
                       || (x = FStarC_Syntax_Syntax.NoExtract))
                      || (has_eq x))
                     || (inferred x))
                    || (visibility x))
                   || (reification x)) quals
        | FStarC_Syntax_Syntax.Unopteq ->
            FStarC_Compiler_List.for_all
              (fun x ->
                 (((((((x = q) || (x = FStarC_Syntax_Syntax.Logic)) ||
                        (x = FStarC_Syntax_Syntax.Inline_for_extraction))
                       || (x = FStarC_Syntax_Syntax.NoExtract))
                      || (has_eq x))
                     || (inferred x))
                    || (visibility x))
                   || (reification x)) quals
        | FStarC_Syntax_Syntax.TotalEffect ->
            FStarC_Compiler_List.for_all
              (fun x ->
                 (((x = q) || (inferred x)) || (visibility x)) ||
                   (reification x)) quals
        | FStarC_Syntax_Syntax.Logic ->
            FStarC_Compiler_List.for_all
              (fun x ->
                 ((((x = q) || (x = FStarC_Syntax_Syntax.Assumption)) ||
                     (inferred x))
                    || (visibility x))
                   || (reducibility x)) quals
        | FStarC_Syntax_Syntax.Reifiable ->
            FStarC_Compiler_List.for_all
              (fun x ->
                 ((((reification x) || (inferred x)) || (visibility x)) ||
                    (x = FStarC_Syntax_Syntax.TotalEffect))
                   || (x = FStarC_Syntax_Syntax.Visible_default)) quals
        | FStarC_Syntax_Syntax.Reflectable uu___ ->
            FStarC_Compiler_List.for_all
              (fun x ->
                 ((((reification x) || (inferred x)) || (visibility x)) ||
                    (x = FStarC_Syntax_Syntax.TotalEffect))
                   || (x = FStarC_Syntax_Syntax.Visible_default)) quals
        | FStarC_Syntax_Syntax.Private -> true
        | uu___ -> true in
      let check_no_subtyping_attribute se1 =
        let uu___ =
          (FStarC_Syntax_Util.has_attribute se1.FStarC_Syntax_Syntax.sigattrs
             FStarC_Parser_Const.no_subtping_attr_lid)
            &&
            (match se1.FStarC_Syntax_Syntax.sigel with
             | FStarC_Syntax_Syntax.Sig_let uu___1 -> false
             | uu___1 -> true) in
        if uu___
        then
          let uu___1 =
            let uu___2 =
              FStarC_Errors_Msg.text
                "Illegal attribute: the `no_subtyping` attribute is allowed only on let-bindings." in
            [uu___2] in
          FStarC_Errors.raise_error FStarC_Syntax_Syntax.has_range_sigelt se1
            FStarC_Errors_Codes.Fatal_InconsistentQualifierAnnotation ()
            (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
            (Obj.magic uu___1)
        else () in
      check_no_subtyping_attribute se;
      (let quals =
         FStarC_Compiler_List.filter
           (fun x -> Prims.op_Negation (x = FStarC_Syntax_Syntax.Logic))
           (FStarC_Syntax_Util.quals_of_sigelt se) in
       let uu___1 =
         let uu___2 =
           FStarC_Compiler_Util.for_some
             (fun uu___3 ->
                match uu___3 with
                | FStarC_Syntax_Syntax.OnlyName -> true
                | uu___4 -> false) quals in
         Prims.op_Negation uu___2 in
       if uu___1
       then
         let r = FStarC_Syntax_Util.range_of_sigelt se in
         let no_dup_quals =
           FStarC_Compiler_Util.remove_dups (fun x -> fun y -> x = y) quals in
         let err msg =
           let uu___2 =
             let uu___3 =
               let uu___4 =
                 let uu___5 = FStarC_Errors_Msg.text "The qualifier list" in
                 let uu___6 =
                   let uu___7 =
                     let uu___8 =
                       FStarC_Class_Show.show
                         (FStarC_Class_Show.show_list
                            FStarC_Syntax_Print.showable_qualifier) quals in
                     FStarC_Pprint.doc_of_string uu___8 in
                   let uu___8 =
                     FStarC_Errors_Msg.text
                       "is not permissible for this element" in
                   FStarC_Pprint.op_Hat_Slash_Hat uu___7 uu___8 in
                 FStarC_Pprint.op_Hat_Slash_Hat uu___5 uu___6 in
               [uu___4] in
             FStar_List_Tot_Base.append uu___3 msg in
           FStarC_Errors.raise_error FStarC_Class_HasRange.hasRange_range r
             FStarC_Errors_Codes.Fatal_QulifierListNotPermitted ()
             (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
             (Obj.magic uu___2) in
         (if
            (FStarC_Compiler_List.length quals) <>
              (FStarC_Compiler_List.length no_dup_quals)
          then
            (let uu___3 =
               let uu___4 = FStarC_Errors_Msg.text "Duplicate qualifiers." in
               [uu___4] in
             err uu___3)
          else ();
          (let uu___4 =
             let uu___5 =
               FStarC_Compiler_List.for_all (quals_combo_ok quals) quals in
             Prims.op_Negation uu___5 in
           if uu___4
           then
             let uu___5 =
               let uu___6 = FStarC_Errors_Msg.text "Ill-formed combination." in
               [uu___6] in
             err uu___5
           else ());
          (match se.FStarC_Syntax_Syntax.sigel with
           | FStarC_Syntax_Syntax.Sig_let
               { FStarC_Syntax_Syntax.lbs1 = (is_rec, uu___4);
                 FStarC_Syntax_Syntax.lids1 = uu___5;_}
               ->
               (if
                  is_rec &&
                    (FStarC_Compiler_List.contains
                       FStarC_Syntax_Syntax.Unfold_for_unification_and_vcgen
                       quals)
                then
                  (let uu___7 =
                     let uu___8 =
                       FStarC_Errors_Msg.text
                         "Recursive definitions cannot be marked inline." in
                     [uu___8] in
                   err uu___7)
                else ();
                (let uu___7 =
                   FStarC_Compiler_Util.for_some
                     (fun x -> (assumption x) || (has_eq x)) quals in
                 if uu___7
                 then
                   let uu___8 =
                     let uu___9 =
                       FStarC_Errors_Msg.text
                         "Definitions cannot be assumed or marked with equality qualifiers." in
                     [uu___9] in
                   err uu___8
                 else ()))
           | FStarC_Syntax_Syntax.Sig_bundle uu___4 ->
               ((let uu___6 =
                   let uu___7 =
                     FStarC_Compiler_Util.for_all
                       (fun x ->
                          ((((x = FStarC_Syntax_Syntax.Inline_for_extraction)
                               || (x = FStarC_Syntax_Syntax.NoExtract))
                              || (inferred x))
                             || (visibility x))
                            || (has_eq x)) quals in
                   Prims.op_Negation uu___7 in
                 if uu___6 then err [] else ());
                (let uu___6 =
                   (FStarC_Compiler_List.existsb
                      (fun uu___7 ->
                         match uu___7 with
                         | FStarC_Syntax_Syntax.Unopteq -> true
                         | uu___8 -> false) quals)
                     &&
                     (FStarC_Syntax_Util.has_attribute
                        se.FStarC_Syntax_Syntax.sigattrs
                        FStarC_Parser_Const.erasable_attr) in
                 if uu___6
                 then
                   let uu___7 =
                     let uu___8 =
                       FStarC_Errors_Msg.text
                         "The `unopteq` qualifier is not allowed on erasable inductives since they don't have decidable equality." in
                     [uu___8] in
                   err uu___7
                 else ()))
           | FStarC_Syntax_Syntax.Sig_declare_typ uu___4 ->
               let uu___5 = FStarC_Compiler_Util.for_some has_eq quals in
               if uu___5 then err [] else ()
           | FStarC_Syntax_Syntax.Sig_assume uu___4 ->
               let uu___5 =
                 let uu___6 =
                   FStarC_Compiler_Util.for_all
                     (fun x ->
                        ((visibility x) ||
                           (x = FStarC_Syntax_Syntax.Assumption))
                          || (x = FStarC_Syntax_Syntax.InternalAssumption))
                     quals in
                 Prims.op_Negation uu___6 in
               if uu___5 then err [] else ()
           | FStarC_Syntax_Syntax.Sig_new_effect uu___4 ->
               let uu___5 =
                 let uu___6 =
                   FStarC_Compiler_Util.for_all
                     (fun x ->
                        (((x = FStarC_Syntax_Syntax.TotalEffect) ||
                            (inferred x))
                           || (visibility x))
                          || (reification x)) quals in
                 Prims.op_Negation uu___6 in
               if uu___5 then err [] else ()
           | FStarC_Syntax_Syntax.Sig_effect_abbrev uu___4 ->
               let uu___5 =
                 let uu___6 =
                   FStarC_Compiler_Util.for_all
                     (fun x -> (inferred x) || (visibility x)) quals in
                 Prims.op_Negation uu___6 in
               if uu___5 then err [] else ()
           | uu___4 -> ()))
       else ())
let (check_erasable :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.qualifier Prims.list ->
      FStarC_Compiler_Range_Type.range -> FStarC_Syntax_Syntax.sigelt -> unit)
  =
  fun env ->
    fun quals ->
      fun r ->
        fun se ->
          let lids = FStarC_Syntax_Util.lids_of_sigelt se in
          let val_exists =
            FStarC_Compiler_Util.for_some
              (fun l ->
                 let uu___ = FStarC_TypeChecker_Env.try_lookup_val_decl env l in
                 FStarC_Compiler_Option.isSome uu___) lids in
          let val_has_erasable_attr =
            FStarC_Compiler_Util.for_some
              (fun l ->
                 let attrs_opt =
                   FStarC_TypeChecker_Env.lookup_attrs_of_lid env l in
                 (FStarC_Compiler_Option.isSome attrs_opt) &&
                   (let uu___ = FStarC_Compiler_Option.get attrs_opt in
                    FStarC_Syntax_Util.has_attribute uu___
                      FStarC_Parser_Const.erasable_attr)) lids in
          let se_has_erasable_attr =
            FStarC_Syntax_Util.has_attribute se.FStarC_Syntax_Syntax.sigattrs
              FStarC_Parser_Const.erasable_attr in
          if
            (val_exists && val_has_erasable_attr) &&
              (Prims.op_Negation se_has_erasable_attr)
          then
            (let uu___1 =
               let uu___2 =
                 FStarC_Errors_Msg.text
                   "Mismatch of attributes between declaration and definition." in
               let uu___3 =
                 let uu___4 =
                   FStarC_Errors_Msg.text
                     "Declaration is marked `erasable` but the definition is not." in
                 [uu___4] in
               uu___2 :: uu___3 in
             FStarC_Errors.raise_error FStarC_Class_HasRange.hasRange_range r
               FStarC_Errors_Codes.Fatal_QulifierListNotPermitted ()
               (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
               (Obj.magic uu___1))
          else ();
          if
            (val_exists && (Prims.op_Negation val_has_erasable_attr)) &&
              se_has_erasable_attr
          then
            (let uu___2 =
               let uu___3 =
                 FStarC_Errors_Msg.text
                   "Mismatch of attributes between declaration and definition." in
               let uu___4 =
                 let uu___5 =
                   FStarC_Errors_Msg.text
                     "Definition is marked `erasable` but the declaration is not." in
                 [uu___5] in
               uu___3 :: uu___4 in
             FStarC_Errors.raise_error FStarC_Class_HasRange.hasRange_range r
               FStarC_Errors_Codes.Fatal_QulifierListNotPermitted ()
               (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
               (Obj.magic uu___2))
          else ();
          if se_has_erasable_attr
          then
            (match se.FStarC_Syntax_Syntax.sigel with
             | FStarC_Syntax_Syntax.Sig_bundle uu___2 ->
                 let uu___3 =
                   let uu___4 =
                     FStarC_Compiler_Util.for_some
                       (fun uu___5 ->
                          match uu___5 with
                          | FStarC_Syntax_Syntax.Noeq -> true
                          | uu___6 -> false) quals in
                   Prims.op_Negation uu___4 in
                 if uu___3
                 then
                   let uu___4 =
                     let uu___5 =
                       FStarC_Errors_Msg.text
                         "Incompatible attributes and qualifiers: erasable types do not support decidable equality and must be marked `noeq`." in
                     [uu___5] in
                   FStarC_Errors.raise_error
                     FStarC_Class_HasRange.hasRange_range r
                     FStarC_Errors_Codes.Fatal_QulifierListNotPermitted ()
                     (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
                     (Obj.magic uu___4)
                 else ()
             | FStarC_Syntax_Syntax.Sig_declare_typ uu___2 -> ()
             | FStarC_Syntax_Syntax.Sig_fail uu___2 -> ()
             | FStarC_Syntax_Syntax.Sig_let
                 { FStarC_Syntax_Syntax.lbs1 = (false, lb::[]);
                   FStarC_Syntax_Syntax.lids1 = uu___2;_}
                 ->
                 let uu___3 =
                   FStarC_Syntax_Util.abs_formals
                     lb.FStarC_Syntax_Syntax.lbdef in
                 (match uu___3 with
                  | (uu___4, body, uu___5) ->
                      let uu___6 =
                        let uu___7 =
                          FStarC_TypeChecker_Normalize.non_info_norm env body in
                        Prims.op_Negation uu___7 in
                      if uu___6
                      then
                        let uu___7 =
                          let uu___8 =
                            FStarC_Errors_Msg.text
                              "Illegal attribute: the `erasable` attribute is only permitted on inductive type definitions and abbreviations for non-informative types." in
                          let uu___9 =
                            let uu___10 =
                              let uu___11 = FStarC_Errors_Msg.text "The term" in
                              let uu___12 =
                                let uu___13 =
                                  FStarC_Class_PP.pp
                                    FStarC_Syntax_Print.pretty_term body in
                                let uu___14 =
                                  FStarC_Errors_Msg.text
                                    "is considered informative." in
                                FStarC_Pprint.op_Hat_Slash_Hat uu___13
                                  uu___14 in
                              FStarC_Pprint.op_Hat_Slash_Hat uu___11 uu___12 in
                            [uu___10] in
                          uu___8 :: uu___9 in
                        FStarC_Errors.raise_error
                          (FStarC_Syntax_Syntax.has_range_syntax ()) body
                          FStarC_Errors_Codes.Fatal_QulifierListNotPermitted
                          ()
                          (Obj.magic
                             FStarC_Errors_Msg.is_error_message_list_doc)
                          (Obj.magic uu___7)
                      else ())
             | FStarC_Syntax_Syntax.Sig_new_effect
                 { FStarC_Syntax_Syntax.mname = eff_name;
                   FStarC_Syntax_Syntax.cattributes = uu___2;
                   FStarC_Syntax_Syntax.univs = uu___3;
                   FStarC_Syntax_Syntax.binders = uu___4;
                   FStarC_Syntax_Syntax.signature = uu___5;
                   FStarC_Syntax_Syntax.combinators = uu___6;
                   FStarC_Syntax_Syntax.actions = uu___7;
                   FStarC_Syntax_Syntax.eff_attrs = uu___8;
                   FStarC_Syntax_Syntax.extraction_mode = uu___9;_}
                 ->
                 if
                   Prims.op_Negation
                     (FStarC_Compiler_List.contains
                        FStarC_Syntax_Syntax.TotalEffect quals)
                 then
                   let uu___10 =
                     let uu___11 =
                       let uu___12 = FStarC_Errors_Msg.text "Effect" in
                       let uu___13 =
                         let uu___14 =
                           FStarC_Class_PP.pp FStarC_Ident.pretty_lident
                             eff_name in
                         let uu___15 =
                           FStarC_Errors_Msg.text
                             "is marked erasable but only total effects are allowed to be erasable." in
                         FStarC_Pprint.op_Hat_Slash_Hat uu___14 uu___15 in
                       FStarC_Pprint.op_Hat_Slash_Hat uu___12 uu___13 in
                     [uu___11] in
                   FStarC_Errors.raise_error
                     FStarC_Class_HasRange.hasRange_range r
                     FStarC_Errors_Codes.Fatal_QulifierListNotPermitted ()
                     (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
                     (Obj.magic uu___10)
                 else ()
             | uu___2 ->
                 let uu___3 =
                   let uu___4 =
                     FStarC_Errors_Msg.text
                       "Illegal attribute: the `erasable` attribute is only permitted on inductive type definitions and abbreviations for non-informative types." in
                   [uu___4] in
                 FStarC_Errors.raise_error
                   FStarC_Class_HasRange.hasRange_range r
                   FStarC_Errors_Codes.Fatal_QulifierListNotPermitted ()
                   (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
                   (Obj.magic uu___3))
          else ()
let (check_must_erase_attribute :
  FStarC_TypeChecker_Env.env -> FStarC_Syntax_Syntax.sigelt -> unit) =
  fun env ->
    fun se ->
      let uu___ = FStarC_Options.ide () in
      if uu___
      then ()
      else
        (match se.FStarC_Syntax_Syntax.sigel with
         | FStarC_Syntax_Syntax.Sig_let
             { FStarC_Syntax_Syntax.lbs1 = lbs;
               FStarC_Syntax_Syntax.lids1 = l;_}
             ->
             let uu___2 =
               let uu___3 = FStarC_TypeChecker_Env.dsenv env in
               let uu___4 = FStarC_TypeChecker_Env.current_module env in
               FStarC_Syntax_DsEnv.iface_decls uu___3 uu___4 in
             (match uu___2 with
              | FStar_Pervasives_Native.None -> ()
              | FStar_Pervasives_Native.Some iface_decls ->
                  FStarC_Compiler_List.iter
                    (fun lb ->
                       let lbname =
                         FStarC_Compiler_Util.right
                           lb.FStarC_Syntax_Syntax.lbname in
                       let has_iface_val =
                         let uu___3 =
                           let uu___4 =
                             FStarC_Ident.ident_of_lid
                               (lbname.FStarC_Syntax_Syntax.fv_name).FStarC_Syntax_Syntax.v in
                           FStarC_Parser_AST.decl_is_val uu___4 in
                         FStarC_Compiler_Util.for_some uu___3 iface_decls in
                       if has_iface_val
                       then
                         let must_erase =
                           FStarC_TypeChecker_Util.must_erase_for_extraction
                             env lb.FStarC_Syntax_Syntax.lbdef in
                         let has_attr =
                           FStarC_TypeChecker_Env.fv_has_attr env lbname
                             FStarC_Parser_Const.must_erase_for_extraction_attr in
                         (if must_erase && (Prims.op_Negation has_attr)
                          then
                            let uu___3 =
                              let uu___4 =
                                let uu___5 =
                                  let uu___6 =
                                    FStarC_Class_Show.show
                                      FStarC_Syntax_Print.showable_fv lbname in
                                  let uu___7 =
                                    FStarC_Class_Show.show
                                      FStarC_Syntax_Print.showable_fv lbname in
                                  FStarC_Compiler_Util.format2
                                    "Values of type `%s` will be erased during extraction, but its interface hides this fact. Add the `must_erase_for_extraction` attribute to the `val %s` declaration for this symbol in the interface"
                                    uu___6 uu___7 in
                                FStarC_Errors_Msg.text uu___5 in
                              [uu___4] in
                            FStarC_Errors.log_issue
                              FStarC_Syntax_Syntax.hasRange_fv lbname
                              FStarC_Errors_Codes.Error_MustEraseMissing ()
                              (Obj.magic
                                 FStarC_Errors_Msg.is_error_message_list_doc)
                              (Obj.magic uu___3)
                          else
                            if has_attr && (Prims.op_Negation must_erase)
                            then
                              (let uu___4 =
                                 let uu___5 =
                                   let uu___6 =
                                     let uu___7 =
                                       FStarC_Class_Show.show
                                         FStarC_Syntax_Print.showable_fv
                                         lbname in
                                     FStarC_Compiler_Util.format1
                                       "Values of type `%s` cannot be erased during extraction, but the `must_erase_for_extraction` attribute claims that it can. Please remove the attribute."
                                       uu___7 in
                                   FStarC_Errors_Msg.text uu___6 in
                                 [uu___5] in
                               FStarC_Errors.log_issue
                                 FStarC_Syntax_Syntax.hasRange_fv lbname
                                 FStarC_Errors_Codes.Error_MustEraseMissing
                                 ()
                                 (Obj.magic
                                    FStarC_Errors_Msg.is_error_message_list_doc)
                                 (Obj.magic uu___4))
                            else ())
                       else ()) (FStar_Pervasives_Native.snd lbs))
         | uu___2 -> ())
let (check_typeclass_instance_attribute :
  FStarC_TypeChecker_Env.env ->
    FStarC_Compiler_Range_Type.range -> FStarC_Syntax_Syntax.sigelt -> unit)
  =
  fun env ->
    fun rng ->
      fun se ->
        let is_tc_instance =
          FStarC_Compiler_Util.for_some
            (fun t ->
               match t.FStarC_Syntax_Syntax.n with
               | FStarC_Syntax_Syntax.Tm_fvar fv ->
                   FStarC_Syntax_Syntax.fv_eq_lid fv
                     FStarC_Parser_Const.tcinstance_lid
               | uu___ -> false) se.FStarC_Syntax_Syntax.sigattrs in
        let check_instance_typ ty =
          let uu___ = FStarC_Syntax_Util.arrow_formals_comp ty in
          match uu___ with
          | (uu___1, res) ->
              ((let uu___3 =
                  let uu___4 = FStarC_Syntax_Util.is_total_comp res in
                  Prims.op_Negation uu___4 in
                if uu___3
                then
                  let uu___4 =
                    let uu___5 =
                      FStarC_Errors_Msg.text
                        "Instances are expected to be total." in
                    let uu___6 =
                      let uu___7 =
                        let uu___8 =
                          FStarC_Errors_Msg.text "This instance has effect" in
                        let uu___9 =
                          FStarC_Class_PP.pp FStarC_Ident.pretty_lident
                            (FStarC_Syntax_Util.comp_effect_name res) in
                        FStarC_Pprint.op_Hat_Hat uu___8 uu___9 in
                      [uu___7] in
                    uu___5 :: uu___6 in
                  FStarC_Errors.log_issue
                    FStarC_Class_HasRange.hasRange_range rng
                    FStarC_Errors_Codes.Error_UnexpectedTypeclassInstance ()
                    (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
                    (Obj.magic uu___4)
                else ());
               (let t = FStarC_Syntax_Util.comp_result res in
                let uu___3 = FStarC_Syntax_Util.head_and_args t in
                match uu___3 with
                | (head, uu___4) ->
                    let err uu___5 =
                      let uu___6 =
                        let uu___7 =
                          FStarC_Errors_Msg.text
                            "Instances must define instances of `class` types." in
                        let uu___8 =
                          let uu___9 =
                            let uu___10 = FStarC_Errors_Msg.text "Type" in
                            let uu___11 =
                              let uu___12 =
                                FStarC_Class_PP.pp
                                  FStarC_Syntax_Print.pretty_term t in
                              let uu___13 =
                                FStarC_Errors_Msg.text "is not a class." in
                              FStarC_Pprint.op_Hat_Slash_Hat uu___12 uu___13 in
                            FStarC_Pprint.op_Hat_Slash_Hat uu___10 uu___11 in
                          [uu___9] in
                        uu___7 :: uu___8 in
                      FStarC_Errors.log_issue
                        FStarC_Class_HasRange.hasRange_range rng
                        FStarC_Errors_Codes.Error_UnexpectedTypeclassInstance
                        ()
                        (Obj.magic
                           FStarC_Errors_Msg.is_error_message_list_doc)
                        (Obj.magic uu___6) in
                    let uu___5 =
                      let uu___6 = FStarC_Syntax_Util.un_uinst head in
                      uu___6.FStarC_Syntax_Syntax.n in
                    (match uu___5 with
                     | FStarC_Syntax_Syntax.Tm_fvar fv ->
                         let uu___6 =
                           let uu___7 =
                             FStarC_TypeChecker_Env.fv_has_attr env fv
                               FStarC_Parser_Const.tcclass_lid in
                           Prims.op_Negation uu___7 in
                         if uu___6 then err () else ()
                     | uu___6 -> err ()))) in
        if is_tc_instance
        then
          match se.FStarC_Syntax_Syntax.sigel with
          | FStarC_Syntax_Syntax.Sig_let
              { FStarC_Syntax_Syntax.lbs1 = (false, lb::[]);
                FStarC_Syntax_Syntax.lids1 = uu___;_}
              -> check_instance_typ lb.FStarC_Syntax_Syntax.lbtyp
          | FStarC_Syntax_Syntax.Sig_let uu___ ->
              let uu___1 =
                let uu___2 =
                  FStarC_Errors_Msg.text
                    "An `instance` definition is expected to be non-recursive and of a type that is a `class`." in
                [uu___2] in
              FStarC_Errors.log_issue FStarC_Class_HasRange.hasRange_range
                rng FStarC_Errors_Codes.Error_UnexpectedTypeclassInstance ()
                (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
                (Obj.magic uu___1)
          | FStarC_Syntax_Syntax.Sig_declare_typ
              { FStarC_Syntax_Syntax.lid2 = uu___;
                FStarC_Syntax_Syntax.us2 = uu___1;
                FStarC_Syntax_Syntax.t2 = t;_}
              -> check_instance_typ t
          | uu___ ->
              let uu___1 =
                let uu___2 =
                  FStarC_Errors_Msg.text
                    "The `instance` attribute is only allowed on `let` and `val` declarations." in
                let uu___3 =
                  let uu___4 =
                    let uu___5 =
                      FStarC_Errors_Msg.text "It is not allowed for" in
                    let uu___6 =
                      let uu___7 =
                        let uu___8 =
                          FStarC_Syntax_Print.sigelt_to_string_short se in
                        FStarC_Pprint.arbitrary_string uu___8 in
                      FStarC_Pprint.squotes uu___7 in
                    FStarC_Pprint.op_Hat_Slash_Hat uu___5 uu___6 in
                  [uu___4] in
                uu___2 :: uu___3 in
              FStarC_Errors.log_issue FStarC_Class_HasRange.hasRange_range
                rng FStarC_Errors_Codes.Error_UnexpectedTypeclassInstance ()
                (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
                (Obj.magic uu___1)
        else ()
let (check_sigelt_quals_post :
  FStarC_TypeChecker_Env.env -> FStarC_Syntax_Syntax.sigelt -> unit) =
  fun env ->
    fun se ->
      let quals = se.FStarC_Syntax_Syntax.sigquals in
      let r = se.FStarC_Syntax_Syntax.sigrng in
      check_erasable env quals r se;
      check_must_erase_attribute env se;
      check_typeclass_instance_attribute env r se