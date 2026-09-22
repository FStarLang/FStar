open Prims
let entrypoints_of_file (f : Prims.string) : Prims.string Prims.list=
  if Prims.not (FStarC_Filepath.file_exists f)
  then
    FStarC_Errors.raise_error0 FStarC_Errors_Codes.Error_CustardEntryNotFound
      () (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
      (Obj.magic
         [FStarC_Errors_Msg.text
            (Prims.strcat "Custard cannot read the entry-point file "
               (Prims.strcat f "."))])
  else
    (let uu___ = FStarC_Util.file_get_lines f in
     FStarC_List.collect
       (fun line ->
          let line1 =
            FStarC_Util.trim_string
              (FStarC_List.hd (FStarC_Util.split line "#")) in
          if line1 = "" then [] else [line1]) uu___)
let entrypoints (uu___ : unit) : FStarC_Ident.lident Prims.list=
  let uu___1 =
    let uu___2 =
      let uu___3 = FStarC_Options.custard_entrypoint_files () in
      FStarC_List.collect entrypoints_of_file uu___3 in
    let uu___3 = FStarC_Options.custard_entries () in
    FStarC_List.op_At uu___2 uu___3 in
  FStarC_List.map FStarC_Ident.lid_of_str uu___1
let main_entry (uu___ : unit) :
  FStarC_Ident.lident FStar_Pervasives_Native.option=
  let uu___1 = FStarC_Options.custard_main () in
  match uu___1 with
  | FStar_Pervasives_Native.Some s ->
      let uu___2 = FStarC_Ident.lid_of_str s in
      FStar_Pervasives_Native.Some uu___2
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let lost_cast (e : FStarC_Custard_Syntax.expr)
  (t : FStarC_Custard_Syntax.cty) : Prims.bool=
  match ((e.FStarC_Custard_Syntax.ty), t) with
  | (FStarC_Custard_Syntax.TAny, uu___) -> false
  | (uu___, FStarC_Custard_Syntax.TAny) -> false
  | uu___ -> true
let warn_any (prog : FStarC_Custard_Syntax.program) : unit=
  let sites = FStarC_Effect.mk_ref [] in
  let note s =
    let uu___ = let uu___1 = FStarC_Effect.op_Bang sites in s :: uu___1 in
    FStarC_Effect.op_Colon_Equals sites uu___ in
  let rec any_cty c =
    match c with
    | FStarC_Custard_Syntax.TAny -> true
    | FStarC_Custard_Syntax.TArrow (a, uu___, b) ->
        let uu___1 = any_cty a in if uu___1 then true else any_cty b
    | FStarC_Custard_Syntax.TApp (uu___, args) ->
        FStarC_List.existsb any_cty args
    | FStarC_Custard_Syntax.TTuple cs -> FStarC_List.existsb any_cty cs
    | FStarC_Custard_Syntax.TBuf c1 -> any_cty c1
    | FStarC_Custard_Syntax.TRef c1 -> any_cty c1
    | FStarC_Custard_Syntax.TInline c1 -> any_cty c1
    | FStarC_Custard_Syntax.TVar uu___ -> false
    | FStarC_Custard_Syntax.TInt uu___ -> false
    | FStarC_Custard_Syntax.TFloat uu___ -> false
    | FStarC_Custard_Syntax.TUnit -> false
    | FStarC_Custard_Syntax.TExn -> false
    | FStarC_Custard_Syntax.TConst uu___ -> false in
  let at where c =
    let uu___ = any_cty c in
    if uu___
    then
      let uu___1 =
        let uu___2 =
          let uu___3 =
            let uu___4 =
              FStarC_Class_Show.show FStarC_Custard_Syntax.showable_cty c in
            Prims.strcat " has type " uu___4 in
          Prims.strcat where uu___3 in
        Prims.strcat "the " uu___2 in
      note uu___1
    else () in
  let rec go x =
    (match x.FStarC_Custard_Syntax.e with
     | FStarC_Custard_Syntax.ECoerce (e1, t) when lost_cast e1 t ->
         let uu___1 =
           let uu___2 =
             let uu___3 =
               FStarC_Class_Show.show FStarC_Custard_Syntax.showable_cty
                 e1.FStarC_Custard_Syntax.ty in
             let uu___4 =
               let uu___5 =
                 FStarC_Class_Show.show FStarC_Custard_Syntax.showable_cty t in
               Prims.strcat " to " uu___5 in
             Prims.strcat uu___3 uu___4 in
           Prims.strcat "a coercion from " uu___2 in
         note uu___1
     | uu___1 -> ());
    (let sub es = FStarC_List.iter go es in
     match x.FStarC_Custard_Syntax.e with
     | FStarC_Custard_Syntax.EConst uu___1 -> ()
     | FStarC_Custard_Syntax.EVar uu___1 -> ()
     | FStarC_Custard_Syntax.EQual uu___1 -> ()
     | FStarC_Custard_Syntax.EAny -> ()
     | FStarC_Custard_Syntax.EAbort uu___1 -> ()
     | FStarC_Custard_Syntax.ELet (v, t, e1, e2) ->
         (at (Prims.strcat "binding of '" (Prims.strcat v "'")) t;
          sub [e1; e2])
     | FStarC_Custard_Syntax.EApp (h, es) -> sub (h :: es)
     | FStarC_Custard_Syntax.EFun (bs, b) ->
         (FStarC_List.iter
            (fun b1 ->
               at
                 (Prims.strcat "binder '"
                    (Prims.strcat b1.FStarC_Custard_Syntax.b_name "'"))
                 b1.FStarC_Custard_Syntax.b_ty) bs;
          go b)
     | FStarC_Custard_Syntax.EMatch (sc, brs) ->
         (go sc; FStarC_List.iter go_branch brs)
     | FStarC_Custard_Syntax.ETry (e, brs) ->
         (go e; FStarC_List.iter go_branch brs)
     | FStarC_Custard_Syntax.EIf (c, a, b) -> sub [c; a; b]
     | FStarC_Custard_Syntax.ESeq (a, b) -> sub [a; b]
     | FStarC_Custard_Syntax.ECtor (uu___1, es) -> sub es
     | FStarC_Custard_Syntax.ETuple es -> sub es
     | FStarC_Custard_Syntax.EOp (uu___1, es) -> sub es
     | FStarC_Custard_Syntax.ERaise e1 -> go e1
     | FStarC_Custard_Syntax.ERecord (uu___1, fs) ->
         let uu___2 = FStarC_List.map FStar_Pervasives_Native.snd fs in
         sub uu___2
     | FStarC_Custard_Syntax.EProj (e, uu___1, uu___2) -> go e
     | FStarC_Custard_Syntax.EDiscrim (e, uu___1) -> go e
     | FStarC_Custard_Syntax.ECast (e, uu___1) -> go e
     | FStarC_Custard_Syntax.ECoerce (e, uu___1) -> go e
     | FStarC_Custard_Syntax.EWhile (c, b) -> sub [c; b])
  and go_branch br =
    let uu___ = br in
    match uu___ with
    | (uu___1, g, b) ->
        ((match g with
          | FStar_Pervasives_Native.Some g1 -> go g1
          | FStar_Pervasives_Native.None -> ());
         go b) in
  FStarC_List.iter
    (fun d ->
       FStarC_Effect.op_Colon_Equals sites [];
       (match d with
        | FStarC_Custard_Syntax.DLet l ->
            (FStarC_List.iter
               (fun b ->
                  at
                    (Prims.strcat "binder '"
                       (Prims.strcat b.FStarC_Custard_Syntax.b_name "'"))
                    b.FStarC_Custard_Syntax.b_ty)
               l.FStarC_Custard_Syntax.dl_binders;
             at "result" l.FStarC_Custard_Syntax.dl_ret;
             go l.FStarC_Custard_Syntax.dl_body)
        | FStarC_Custard_Syntax.DType t ->
            let fields owner fs =
              FStarC_List.iter
                (fun uu___2 ->
                   match uu___2 with
                   | (f, c) ->
                       at
                         (Prims.strcat "field '"
                            (Prims.strcat owner
                               (Prims.strcat "." (Prims.strcat f "'")))) c)
                fs in
            (match t.FStarC_Custard_Syntax.dt_body with
             | FStarC_Custard_Syntax.TAbbrev c -> at "definition" c
             | FStarC_Custard_Syntax.TRecord fs ->
                 let uu___2 =
                   FStarC_Custard_Syntax.string_of_name
                     t.FStarC_Custard_Syntax.dt_name in
                 fields uu___2 fs
             | FStarC_Custard_Syntax.TVariant cs ->
                 FStarC_List.iter
                   (fun uu___2 ->
                      match uu___2 with
                      | (cn, fs) ->
                          let uu___3 =
                            FStarC_Custard_Syntax.string_of_name cn in
                          fields uu___3 fs) cs
             | FStarC_Custard_Syntax.TAbstract -> ())
        | FStarC_Custard_Syntax.DExternal x ->
            at "declaration" x.FStarC_Custard_Syntax.dx_ty
        | FStarC_Custard_Syntax.DExn e ->
            FStarC_List.iter (at "exception argument")
              e.FStarC_Custard_Syntax.de_args);
       (let extra =
          match d with
          | FStarC_Custard_Syntax.DExternal x when
              match x.FStarC_Custard_Syntax.dx_typars with
              | hd::tl -> true
              | uu___2 -> false ->
              let uu___2 =
                let uu___3 =
                  let uu___4 =
                    let uu___5 =
                      FStarC_Custard_Syntax.string_of_name
                        x.FStarC_Custard_Syntax.dx_name in
                    let uu___6 =
                      let uu___7 =
                        let uu___8 =
                          FStarC_Class_Show.show
                            FStarC_Class_Show.showable_nat
                            (FStarC_List.length
                               x.FStarC_Custard_Syntax.dx_typars) in
                        Prims.strcat uu___8
                          (Prims.strcat " type parameter(s): "
                             (Prims.strcat
                                (FStarC_String.concat ", "
                                   x.FStarC_Custard_Syntax.dx_typars) ".")) in
                      Prims.strcat "' is external and polymorphic, in "
                        uu___7 in
                    Prims.strcat uu___5 uu___6 in
                  Prims.strcat "'" uu___4 in
                FStarC_Errors_Msg.text uu___3 in
              [uu___2;
              FStarC_Errors_Msg.text
                "Specialization does not rescue this.  Even where the type parameters are substituted -- under --custard_monomorphize_types they are -- an external's C declaration is a single fixed symbol with a single prototype, so several instantiations collide rather than becoming separate copies (error 384).  Without that flag each type parameter simply becomes [any], which is this warning.";
              FStarC_Errors_Msg.text
                "Give the parameter a concrete type.  If the C target really does accept several types -- a variadic macro, say -- declare one external per type vector, all with the same [@@custard_extern] target name, and give each one [@@custard_c_header \"...\"] as well.  The header is not optional: it is what makes Custard emit no prototype of its own, and without it the several declarations of one symbol are what error 384 refuses."]
          | uu___2 -> [] in
        let uu___2 =
          let uu___3 = FStarC_Effect.op_Bang sites in FStarC_List.rev uu___3 in
        match uu___2 with
        | [] -> ()
        | ss ->
            let uu___3 =
              let uu___4 =
                let uu___5 =
                  let uu___6 =
                    let uu___7 =
                      let uu___8 =
                        FStarC_Class_Show.show FStarC_Class_Show.showable_nat
                          (FStarC_List.length ss) in
                      let uu___9 =
                        let uu___10 =
                          let uu___11 =
                            FStarC_Custard_Syntax.string_of_name
                              (FStarC_Custard_Syntax.name_of_decl d) in
                          Prims.strcat uu___11 "':" in
                        Prims.strcat " value(s) in '" uu___10 in
                      Prims.strcat uu___8 uu___9 in
                    Prims.strcat "Custard lost the representation of " uu___7 in
                  FStarC_Errors_Msg.text uu___6 in
                let uu___6 =
                  FStarC_List.map
                    (fun s -> FStarC_Errors_Msg.text (Prims.strcat "- " s))
                    ss in
                uu___5 :: uu___6 in
              FStarC_List.op_At uu___4
                (FStarC_List.op_At extra
                   [FStarC_Errors_Msg.text
                      "A whole, monomorphic program mostly should not need these: each one is a place where the code generated to cross into and out of it is unchecked -- an Obj.magic in OCaml, a reinterpretation in C. Some are unavoidable, notably a class over a type constructor, which no OCaml type can name."]) in
            FStarC_Errors.log_issue0
              FStarC_Errors_Codes.Warning_CustardLostRepresentation ()
              (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
              (Obj.magic uu___3))) prog
let check_entrypoints (deps : FStarC_Parser_Dep.deps)
  (env : FStarC_TypeChecker_Env.env) (roots : FStarC_Ident.lident Prims.list)
  : unit=
  FStarC_List.iter
    (fun l ->
       let uu___ =
         FStarC_Custard_Loader.module_is_loaded deps env
           (FStarC_Ident.string_of_lid l) in
       if uu___
       then ()
       else
         (let m =
            match FStarC_Ident.ns_of_lid l with
            | [] -> ""
            | ns ->
                let uu___1 = FStarC_Ident.lid_of_ids ns in
                FStarC_Ident.string_of_lid uu___1 in
          let uu___1 =
            if m = ""
            then true
            else FStarC_Custard_Loader.module_is_loaded deps env m in
          if uu___1
          then
            let uu___2 = FStarC_TypeChecker_Env.lookup_sigelt env l in
            match uu___2 with
            | FStar_Pervasives_Native.Some uu___3 -> ()
            | FStar_Pervasives_Native.None ->
                FStarC_Errors.log_issue0
                  FStarC_Errors_Codes.Error_CustardEntryNotFound ()
                  (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
                  (Obj.magic
                     [FStarC_Errors_Msg.text
                        (Prims.strcat "Custard entry point "
                           (Prims.strcat (FStarC_Ident.string_of_lid l)
                              " is not in scope."));
                     FStarC_Errors_Msg.text
                       "Make sure the module defining it is among the input files."])
          else ())) roots
let imported_type_infos
  (imports :
    (FStarC_Custard_Syntax.decl * FStarC_Custard_Syntax.type_info
      FStar_Pervasives_Native.option) Prims.list)
  :
  (FStarC_Custard_Syntax.dtype * FStarC_Custard_Syntax.type_info) Prims.list=
  FStarC_List.collect
    (fun uu___ ->
       match uu___ with
       | (d, ti) ->
           (match (d, ti) with
            | (FStarC_Custard_Syntax.DType dt, FStar_Pervasives_Native.Some
               ti1) -> [(dt, ti1)]
            | uu___1 -> [])) imports
let imported_decls
  (imports :
    (FStarC_Custard_Syntax.decl * FStarC_Custard_Syntax.type_info
      FStar_Pervasives_Native.option) Prims.list)
  : FStarC_Custard_Syntax.decl Prims.list=
  FStarC_List.map FStar_Pervasives_Native.fst imports
let unit_entries (keys : (Prims.string * Prims.string) Prims.list)
  (homes : Prims.string FStarC_SMap.t) (prog : FStarC_Custard_Syntax.program)
  (infos :
    (FStarC_Custard_Syntax.name * FStarC_Custard_Syntax.type_info) Prims.list)
  : FStarC_Custard_Unit.entry Prims.list=
  let key_map = FStarC_SMap.create (Prims.of_int 100) in
  FStarC_List.iter
    (fun uu___1 ->
       match uu___1 with
       | (n', k) ->
           let uu___2 =
             let uu___3 = FStarC_SMap.try_find key_map n' in
             match uu___3 with
             | FStar_Pervasives_Native.None -> true
             | uu___4 -> false in
           if uu___2 then FStarC_SMap.add key_map n' k else ()) keys;
  (let info_map = FStarC_SMap.create (Prims.of_int 100) in
   FStarC_List.iter
     (fun uu___2 ->
        match uu___2 with
        | (n', ti) ->
            let k = FStarC_Custard_Syntax.string_of_name n' in
            let uu___3 =
              let uu___4 = FStarC_SMap.try_find info_map k in
              match uu___4 with
              | FStar_Pervasives_Native.None -> true
              | uu___5 -> false in
            if uu___3 then FStarC_SMap.add info_map k ti else ()) infos;
   (let key_of n =
      let uu___2 = FStarC_Custard_Syntax.string_of_name n in
      FStarC_SMap.try_find key_map uu___2 in
    let info_of n =
      let uu___2 = FStarC_Custard_Syntax.string_of_name n in
      FStarC_SMap.try_find info_map uu___2 in
    FStarC_List.collect
      (fun d ->
         let uu___2 =
           let uu___3 =
             FStarC_Custard_Syntax.has_flag
               (FStarC_Custard_Syntax.decl_flags d)
               FStarC_Custard_Syntax.Inline in
           if uu___3
           then true
           else
             (let uu___4 = FStarC_Custard_Syntax.imported_unit d in
              match uu___4 with
              | FStar_Pervasives_Native.Some v -> true
              | uu___5 -> false) in
         if uu___2
         then []
         else
           if
             (match d with
              | FStarC_Custard_Syntax.DExternal _0 -> true
              | uu___3 -> false)
           then []
           else
             (let uu___3 =
                let uu___4 =
                  let uu___5 = FStarC_Options.custard_backend () in
                  uu___5 = "C" in
                if uu___4
                then
                  match d with
                  | FStarC_Custard_Syntax.DLet dl ->
                      let uu___5 = FStarC_Custard_PrintC.is_public dl in
                      Prims.not uu___5
                  | uu___5 -> false
                else false in
              if uu___3
              then []
              else
                (let uu___4 =
                   match d with
                   | FStarC_Custard_Syntax.DLet dl ->
                       ((FStarC_Custard_Syntax.DLet
                           {
                             FStarC_Custard_Syntax.dl_name =
                               (dl.FStarC_Custard_Syntax.dl_name);
                             FStarC_Custard_Syntax.dl_typars =
                               (dl.FStarC_Custard_Syntax.dl_typars);
                             FStarC_Custard_Syntax.dl_binders =
                               (dl.FStarC_Custard_Syntax.dl_binders);
                             FStarC_Custard_Syntax.dl_ret =
                               (dl.FStarC_Custard_Syntax.dl_ret);
                             FStarC_Custard_Syntax.dl_eff =
                               (dl.FStarC_Custard_Syntax.dl_eff);
                             FStarC_Custard_Syntax.dl_body =
                               FStarC_Custard_Syntax.unit_expr;
                             FStarC_Custard_Syntax.dl_flags =
                               (dl.FStarC_Custard_Syntax.dl_flags)
                           }), FStar_Pervasives_Native.None)
                   | FStarC_Custard_Syntax.DType dt ->
                       let uu___5 = info_of dt.FStarC_Custard_Syntax.dt_name in
                       (d, uu___5)
                   | uu___5 -> (d, FStar_Pervasives_Native.None) in
                 match uu___4 with
                 | (d1, ti) ->
                     let key_of1 n =
                       let uu___5 = let uu___6 = key_of n in (uu___6, d1) in
                       match uu___5 with
                       | (FStar_Pervasives_Native.None,
                          FStarC_Custard_Syntax.DType uu___6) ->
                           let uu___7 = FStarC_Custard_Unit.type_key n in
                           FStar_Pervasives_Native.Some uu___7
                       | (k, uu___6) -> k in
                     let uu___5 =
                       key_of1 (FStarC_Custard_Syntax.name_of_decl d1) in
                     (match uu___5 with
                      | FStar_Pervasives_Native.None -> []
                      | FStar_Pervasives_Native.Some k ->
                          let uu___6 =
                            let uu___7 =
                              let uu___8 =
                                FStarC_Custard_Syntax.string_of_name
                                  (FStarC_Custard_Syntax.name_of_decl d1) in
                              FStarC_SMap.try_find homes uu___8 in
                            {
                              FStarC_Custard_Unit.ue_key = k;
                              FStarC_Custard_Unit.ue_decl = d1;
                              FStarC_Custard_Unit.ue_type = ti;
                              FStarC_Custard_Unit.ue_home = uu___7
                            } in
                          [uu___6])))) prog))
let write_unit_iface (st : FStarC_Custard_Extract.state)
  (homes : Prims.string FStarC_SMap.t)
  (hdr_file : Prims.string FStar_Pervasives_Native.option)
  (init : Prims.string FStar_Pervasives_Native.option)
  (prog : FStarC_Custard_Syntax.program)
  (infos :
    (FStarC_Custard_Syntax.name * FStarC_Custard_Syntax.type_info) Prims.list)
  : unit=
  let uu___ = FStarC_Options.custard_unit () in
  match uu___ with
  | FStar_Pervasives_Native.None -> ()
  | FStar_Pervasives_Native.Some u ->
      let i =
        let uu___1 =
          let uu___2 = FStarC_Options.custard_backend () in
          let uu___3 = FStarC_Custard_Unit.layout_options () in
          let uu___4 =
            let uu___5 =
              let uu___6 = FStarC_Custard_Extract.loaded_digests st in
              let uu___7 =
                let uu___8 = FStarC_Options.file_list () in
                FStarC_List.map
                  (fun f ->
                     let uu___9 = FStarC_Util.digest_of_file f in (f, uu___9))
                  uu___8 in
              FStarC_List.op_At uu___6 uu___7 in
            FStarC_List.map
              (fun uu___6 ->
                 match uu___6 with
                 | (f, d) ->
                     let uu___7 = FStarC_Filepath.normalize_file_path f in
                     (uu___7, d)) uu___5 in
          let uu___5 = FStarC_Options.custard_c_no_prefix () in
          {
            FStarC_Custard_Unit.uh_version =
              FStarC_Custard_Unit.current_version;
            FStarC_Custard_Unit.uh_name = u;
            FStarC_Custard_Unit.uh_backend = uu___2;
            FStarC_Custard_Unit.uh_options = uu___3;
            FStarC_Custard_Unit.uh_digests = uu___4;
            FStarC_Custard_Unit.uh_no_prefix = uu___5;
            FStarC_Custard_Unit.uh_header = hdr_file;
            FStarC_Custard_Unit.uh_init = init
          } in
        let uu___2 =
          let uu___3 = FStarC_Custard_Extract.exported_keys st in
          unit_entries uu___3 homes prog infos in
        {
          FStarC_Custard_Unit.ui_header = uu___1;
          FStarC_Custard_Unit.ui_entries = uu___2
        } in
      ((let uu___2 = FStarC_Options.custard_dump_cui () in
        if uu___2
        then
          let uu___3 = FStarC_Custard_Unit.iface_to_string i in
          FStarC_Format.print_string uu___3
        else ());
       (let uu___2 = FStarC_Find.prepend_output_dir (Prims.strcat u ".cui") in
        FStarC_Custard_Unit.write_iface uu___2 i))
let phase (name : Prims.string) (f : unit -> 'a) : 'a=
  FStarC_Custard_Prof.timed name f
let run_phases (deps : FStarC_Parser_Dep.deps)
  (env : FStarC_TypeChecker_Env.env) : unit=
  let main = main_entry () in
  let roots =
    let uu___ = entrypoints () in
    FStarC_List.op_At uu___
      (match main with
       | FStar_Pervasives_Native.Some l -> [l]
       | FStar_Pervasives_Native.None -> []) in
  (let uu___1 =
     if match roots with | [] -> true | uu___2 -> false
     then
       let uu___2 = FStarC_Options.custard_entry_modules () in
       match uu___2 with | [] -> true | uu___3 -> false
     else false in
   if uu___1
   then
     FStarC_Errors.raise_error0
       FStarC_Errors_Codes.Fatal_OptionsNotCompatible ()
       (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
       (Obj.magic
          [FStarC_Errors_Msg.text
             "--codegen Custard requires at least one --custard_entry, --custard_entry_module or --custard_main.";
          FStarC_Errors_Msg.text
            "Custard is a whole-program compiler: it extracts exactly the definitions reachable from the entry points."])
   else ());
  phase "entrypoints" (fun uu___2 -> check_entrypoints deps env roots);
  (let uu___3 =
     let uu___4 =
       let uu___5 =
         let uu___6 = FStarC_Options.custard_unit () in
         match uu___6 with
         | FStar_Pervasives_Native.Some v -> true
         | uu___7 -> false in
       if uu___5
       then true
       else
         (let uu___6 = FStarC_Options.custard_links () in
          match uu___6 with | hd::tl -> true | uu___7 -> false) in
     if uu___4 then FStarC_Options.custard_backend_krml () else false in
   if uu___3
   then
     FStarC_Errors.raise_error0
       FStarC_Errors_Codes.Fatal_OptionsNotCompatible ()
       (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
       (Obj.magic
          [FStarC_Errors_Msg.text
             "Separate compilation (--custard_unit, --custard_link) is not implemented for the karamel backends.";
          FStarC_Errors_Msg.text
            "Use --custard_backend OCaml or --custard_backend C, or compile the whole program at once."])
   else ());
  (let st = FStarC_Custard_Extract.init deps env in
   FStarC_Custard_Extract.install_chain_reporter st;
   (let prog =
      phase "extract"
        (fun uu___4 ->
           FStarC_Syntax_Unionfind.with_uf_enabled
             (fun uu___5 ->
                let requested =
                  let uu___6 =
                    let uu___7 = FStarC_Options.custard_entry_modules () in
                    FStarC_List.map FStarC_Ident.lid_of_str uu___7 in
                  FStarC_List.op_At roots uu___6 in
                FStarC_Custard_Extract.run st roots main
                  (FStarC_Custard_RegEmb.handle_module st requested))) in
    let imports = FStarC_Custard_Extract.imports st in
    let prog1 = phase "anf" (fun uu___4 -> FStarC_Custard_Simplify.anf prog) in
    let prog2 =
      let uu___4 = FStarC_Options.custard_monomorphize_types () in
      if uu___4
      then
        phase "monomorphize"
          (fun uu___5 -> FStarC_Custard_Monomorphize.run prog1)
      else prog1 in
    let prog3 =
      phase "adopt"
        (fun uu___4 -> FStarC_Custard_Extract.adopt_type_clones st prog2) in
    let imports1 = FStarC_Custard_Extract.imports st in
    let uu___4 =
      phase "layout"
        (fun uu___5 ->
           let uu___6 = imported_type_infos imports1 in
           FStarC_Custard_Layout.run uu___6 prog3) in
    match uu___4 with
    | (prog4, infos, vd) ->
        let prog5 =
          phase "simplify"
            (fun uu___5 ->
               let uu___6 = imported_decls imports1 in
               FStarC_Custard_Simplify.run uu___6 vd prog4) in
        let uu___5 =
          phase "rename"
            (fun uu___6 -> FStarC_Custard_Rename.run infos prog5) in
        (match uu___5 with
         | (prog6, infos1) ->
             let split_backends = ["OCaml"; "KrmlC"; "KrmlRust"] in
             let files =
               let uu___6 =
                 let uu___7 = FStarC_Options.custard_split () in
                 if uu___7
                 then
                   let uu___8 = FStarC_Options.custard_backend () in
                   FStarC_List.mem uu___8 split_backends
                 else false in
               if uu___6
               then
                 let uu___7 =
                   phase "split"
                     (fun uu___8 ->
                        let uu___9 = FStarC_Custard_Extract.link_homes st in
                        let uu___10 =
                          let uu___11 =
                            FStarC_List.map FStar_Pervasives_Native.fst
                              imports1 in
                          FStarC_List.op_At uu___11 prog6 in
                        FStarC_Custard_Split.run deps uu___9 uu___10) in
                 FStar_Pervasives_Native.Some uu___7
               else FStar_Pervasives_Native.None in
             let homes = FStarC_SMap.create (Prims.of_int 100) in
             ((match files with
               | FStar_Pervasives_Native.None -> ()
               | FStar_Pervasives_Native.Some fs ->
                   FStarC_List.iter
                     (fun uu___7 ->
                        match uu___7 with
                        | (m, ds) ->
                            FStarC_List.iter
                              (fun d ->
                                 let uu___8 =
                                   FStarC_Custard_Syntax.string_of_name
                                     (FStarC_Custard_Syntax.name_of_decl d) in
                                 FStarC_SMap.add homes uu___8 m) ds) fs);
              (let backend = FStarC_Options.custard_backend () in
               (let uu___8 =
                  let uu___9 = FStarC_Options.custard_sizet_32 () in
                  if uu___9 then backend <> "C" else false in
                if uu___8
                then
                  FStarC_Errors.raise_error0
                    FStarC_Errors_Codes.Fatal_OptionsNotCompatible ()
                    (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
                    (Obj.magic
                       [FStarC_Errors_Msg.text
                          (Prims.strcat
                             "--custard_sizet_width 32 is a direct-to-C option, but this run uses --custard_backend "
                             (Prims.strcat backend "."));
                       FStarC_Errors_Msg.text
                         "karamel decides the width of size_t for itself, and the OCaml backend has no say in it at all."])
                else ());
               (let uu___9 =
                  if backend = "FSharp"
                  then FStarC_Options.custard_split ()
                  else false in
                if uu___9
                then
                  FStarC_Errors.raise_error0
                    FStarC_Errors_Codes.Fatal_OptionsNotCompatible ()
                    (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
                    (Obj.magic
                       [FStarC_Errors_Msg.text
                          "--custard_split is not implemented for --custard_backend FSharp.";
                       FStarC_Errors_Msg.text
                         "F# compilation is order-sensitive in the same way OCaml's is, so a split output would also need a generated project listing its files in link order; the whole-program single file is what this backend emits today (section 122.12)."])
                else ());
               (let uu___10 =
                  if backend = "FSharp"
                  then
                    let uu___11 = FStarC_Options.custard_unit () in
                    match uu___11 with
                    | FStar_Pervasives_Native.Some v -> true
                    | uu___12 -> false
                  else false in
                if uu___10
                then
                  FStarC_Errors.raise_error0
                    FStarC_Errors_Codes.Fatal_OptionsNotCompatible ()
                    (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
                    (Obj.magic
                       [FStarC_Errors_Msg.text
                          "--custard_unit is not implemented for --custard_backend FSharp.";
                       FStarC_Errors_Msg.text
                         "Linking two separately extracted units means one .NET assembly referencing another, which the generated project would have to express; the F# backend compiles one whole program today (section 122.12)."])
                else ());
               (let ofile =
                  let uu___10 = FStarC_Options.output_to () in
                  match uu___10 with
                  | FStar_Pervasives_Native.Some fn -> fn
                  | FStar_Pervasives_Native.None ->
                      let base =
                        let uu___11 = FStarC_Options.custard_unit () in
                        match uu___11 with
                        | FStar_Pervasives_Native.Some u ->
                            if backend = "C"
                            then u
                            else
                              FStarC_Custard_PrintOCaml.module_name_of_unit u
                        | FStar_Pervasives_Native.None -> "Custard" in
                      let uu___11 =
                        let uu___12 = FStarC_Options.custard_backend_krml () in
                        if uu___12
                        then Prims.strcat base ".krml"
                        else
                          (match backend with
                           | "C" -> Prims.strcat base ".c"
                           | "FSharp" -> Prims.strcat base ".fs"
                           | uu___13 -> Prims.strcat base ".ml") in
                      FStarC_Find.prepend_output_dir uu___11 in
                let stem =
                  let b = FStarC_Filepath.basename ofile in
                  let parts = FStarC_String.split [46] b in
                  if (FStarC_List.length parts) <= Prims.int_one
                  then b
                  else
                    FStarC_String.concat "."
                      (FStarC_List.rev
                         (FStarC_List.tl (FStarC_List.rev parts))) in
                let cu =
                  if backend <> "C"
                  then FStarC_Custard_PrintC.no_unit
                  else
                    (let uu___10 = FStarC_Options.custard_unit () in
                     let uu___11 = FStarC_Custard_Extract.link_headers st in
                     let uu___12 = FStarC_Custard_Extract.link_inits st in
                     let uu___13 = FStarC_Custard_Extract.link_no_prefix st in
                     {
                       FStarC_Custard_PrintC.cu_name = uu___10;
                       FStarC_Custard_PrintC.cu_headers = uu___11;
                       FStarC_Custard_PrintC.cu_inits = uu___12;
                       FStarC_Custard_PrintC.cu_no_prefix = uu___13
                     }) in
                if backend = "OCaml"
                then
                  (let uu___11 = FStarC_Options.custard_unit () in
                   match uu___11 with
                   | FStar_Pervasives_Native.Some u when
                       let uu___12 =
                         FStarC_Custard_PrintOCaml.module_name_of_unit u in
                       let uu___13 =
                         FStarC_Custard_PrintOCaml.module_name_of_unit stem in
                       uu___12 <> uu___13 ->
                       let uu___12 =
                         let uu___13 =
                           let uu___14 =
                             let uu___15 =
                               let uu___16 =
                                 let uu___17 =
                                   let uu___18 =
                                     FStarC_Custard_PrintOCaml.module_name_of_unit
                                       u in
                                   let uu___19 =
                                     let uu___20 =
                                       let uu___21 =
                                         let uu___22 =
                                           let uu___23 =
                                             FStarC_Custard_PrintOCaml.module_name_of_unit
                                               stem in
                                           Prims.strcat uu___23 "." in
                                         Prims.strcat " defines the module "
                                           uu___22 in
                                       Prims.strcat ofile uu___21 in
                                     Prims.strcat ", but the output file "
                                       uu___20 in
                                   Prims.strcat uu___18 uu___19 in
                                 Prims.strcat " names the OCaml module "
                                   uu___17 in
                               Prims.strcat u uu___16 in
                             Prims.strcat "Custard: --custard_unit " uu___15 in
                           FStarC_Errors_Msg.text uu___14 in
                         let uu___14 =
                           let uu___15 =
                             let uu___16 =
                               let uu___17 =
                                 let uu___18 =
                                   let uu___19 =
                                     FStarC_Custard_PrintOCaml.module_name_of_unit
                                       u in
                                   Prims.strcat uu___19
                                     (Prims.strcat
                                        ".ml, or pass --custard_unit "
                                        (Prims.strcat stem ".")) in
                                 Prims.strcat "Write it to " uu___18 in
                               FStarC_Errors_Msg.text uu___17 in
                             [uu___16] in
                           (FStarC_Errors_Msg.text
                              "A unit that links against this one qualifies its imports by the unit name, so the two have to agree.")
                             :: uu___15 in
                         uu___13 :: uu___14 in
                       FStarC_Errors.raise_error0
                         FStarC_Errors_Codes.Fatal_OptionsNotCompatible ()
                         (Obj.magic
                            FStarC_Errors_Msg.is_error_message_list_doc)
                         (Obj.magic uu___12)
                   | uu___12 -> ())
                else ();
                phase "iface"
                  (fun uu___12 ->
                     let uu___13 =
                       if backend = "C"
                       then
                         let uu___14 =
                           let uu___15 =
                             let uu___16 =
                               FStarC_List.map FStar_Pervasives_Native.fst
                                 imports1 in
                             FStarC_List.op_At uu___16 prog6 in
                           FStarC_Custard_PrintC.init_globals_name cu uu___15 in
                         ((FStar_Pervasives_Native.Some
                             (Prims.strcat stem ".h")), uu___14)
                       else
                         (FStar_Pervasives_Native.None,
                           FStar_Pervasives_Native.None) in
                     match uu___13 with
                     | (hdr_file, init) ->
                         write_unit_iface st homes hdr_file init prog6 infos1);
                (let uu___13 = FStarC_Options.custard_dump_ir () in
                 if uu___13
                 then
                   let uu___14 =
                     let uu___15 =
                       FStarC_Custard_Syntax.program_to_string prog6 in
                     Prims.strcat uu___15 "\n" in
                   FStarC_Format.print_string uu___14
                 else ());
                (let uu___14 = FStarC_Options.custard_warn_any () in
                 if uu___14 then warn_any prog6 else ());
                (match backend with
                 | "OCaml" when
                     match files with
                     | FStar_Pervasives_Native.Some v -> true
                     | uu___14 -> false ->
                     phase "print"
                       (fun uu___14 ->
                          let uu___15 =
                            FStarC_Custard_PrintOCaml.print_split
                              (match files with
                               | FStar_Pervasives_Native.Some v -> v) in
                          FStarC_List.iter
                            (fun uu___16 ->
                               match uu___16 with
                               | (m, src) ->
                                   let uu___17 =
                                     FStarC_Find.prepend_output_dir
                                       (Prims.strcat m ".ml") in
                                   FStarC_Util.write_file uu___17 src)
                            uu___15)
                 | "KrmlC" when
                     match files with
                     | FStar_Pervasives_Native.Some v -> true
                     | uu___14 -> false ->
                     phase "print"
                       (fun uu___14 ->
                          let uu___15 =
                            FStarC_Custard_PrintKrml.print_split
                              (match files with
                               | FStar_Pervasives_Native.Some v -> v) in
                          FStarC_Custard_PrintKrml.write_files ofile uu___15)
                 | "KrmlRust" when
                     match files with
                     | FStar_Pervasives_Native.Some v -> true
                     | uu___14 -> false ->
                     phase "print"
                       (fun uu___14 ->
                          let uu___15 =
                            FStarC_Custard_PrintKrml.print_split
                              (match files with
                               | FStar_Pervasives_Native.Some v -> v) in
                          FStarC_Custard_PrintKrml.write_files ofile uu___15)
                 | "KrmlC" ->
                     FStarC_Custard_PrintKrml.write_program ofile prog6
                 | "KrmlRust" ->
                     FStarC_Custard_PrintKrml.write_program ofile prog6
                 | "C" ->
                     let uu___14 =
                       let uu___15 =
                         let uu___16 =
                           FStarC_List.map FStar_Pervasives_Native.fst
                             imports1 in
                         FStarC_List.op_At uu___16 prog6 in
                       FStarC_Custard_PrintC.print_program stem cu uu___15 in
                     (match uu___14 with
                      | (hdr, src) ->
                          (FStarC_Util.write_file
                             (FStarC_Filepath.join_paths
                                (FStarC_Filepath.dirname ofile)
                                (Prims.strcat stem ".h")) hdr;
                           FStarC_Util.write_file ofile src))
                 | "OCaml" ->
                     let uu___14 =
                       let uu___15 =
                         let uu___16 =
                           FStarC_List.map FStar_Pervasives_Native.fst
                             imports1 in
                         FStarC_List.op_At uu___16 prog6 in
                       FStarC_Custard_PrintOCaml.print_program uu___15 in
                     FStarC_Util.write_file ofile uu___14
                 | "FSharp" ->
                     let p =
                       let uu___14 =
                         FStarC_List.map FStar_Pervasives_Native.fst imports1 in
                       FStarC_List.op_At uu___14 prog6 in
                     ((let uu___15 =
                         FStarC_Custard_PrintFSharp.print_program stem p in
                       FStarC_Util.write_file ofile uu___15);
                      (let uu___15 =
                         FStarC_Custard_PrintFSharp.project_files stem p in
                       FStarC_List.iter
                         (fun uu___16 ->
                            match uu___16 with
                            | (f, src) ->
                                FStarC_Util.write_file
                                  (FStarC_Filepath.join_paths
                                     (FStarC_Filepath.dirname ofile) f) src)
                         uu___15))
                 | b ->
                     FStarC_Errors.raise_error0
                       FStarC_Errors_Codes.Fatal_OptionsNotCompatible ()
                       (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
                       (Obj.magic
                          [FStarC_Errors_Msg.text
                             (Prims.strcat "Unknown --custard_backend "
                                (Prims.strcat b "."));
                          FStarC_Errors_Msg.text
                            "The backends are OCaml (the default), FSharp, KrmlC, KrmlRust and C."]))))))))
let run (deps : FStarC_Parser_Dep.deps) (env : FStarC_TypeChecker_Env.env) :
  unit=
  try
    (fun uu___ ->
       match () with
       | () ->
           (phase "driver" (fun uu___2 -> run_phases deps env);
            FStarC_Custard_Prof.report ())) ()
  with | uu___ -> (FStarC_Custard_Prof.report (); FStarC_Effect.raise uu___)
