open Fstarcompiler
open Prims
exception NotFound 
let uu___is_NotFound (projectee : Prims.exn) : Prims.bool=
  match projectee with | NotFound -> true | uu___ -> false
let debug (f : unit -> (Prims.string, unit) FStar_Tactics_Effect.tac_repr) :
  (unit, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = FStarC_Tactics_V2_Builtins.debugging () ps in
    if x
    then let x1 = f () ps in FStarC_Tactics_V2_Builtins.print x1 ps
    else ()
let mk_one_projector (unf : Prims.string Prims.list) (np : Prims.nat)
  (i : Prims.nat) : (unit, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    debug
      (fun uu___ ps1 ->
         FStarC_Tactics_V2_Builtins.dump "ENTRY mk_one_projector" ps1; "") ps;
    (let x1 = FStarC_Tactics_V2_Builtins.intros np ps in
     let x2 = FStarC_Tactics_V2_Builtins.intro () ps in
     let x3 =
       FStarC_Tactics_V2_Builtins.t_destruct
         (FStar_Tactics_V2_SyntaxCoercions.binding_to_term x2) ps in
     match x3 with
     | (cons, arity)::[] ->
         (if i >= arity
          then
            FStar_Tactics_V2_Derived.fail
              "proj: bad index in mk_one_projector" ps
          else ();
          (let x5 = FStarC_Tactics_V2_Builtins.intros i ps in
           let x6 = FStarC_Tactics_V2_Builtins.intro () ps in
           let x7 =
             FStarC_Tactics_V2_Builtins.intros ((arity - i) - Prims.int_one)
               ps in
           let x8 = FStarC_Tactics_V2_Builtins.intro () ps in
           FStarC_Tactics_V2_Builtins.rewrite x8 ps;
           FStarC_Tactics_V2_Builtins.norm
             [Fstarcompiler.FStarC_NormSteps.iota;
             Fstarcompiler.FStarC_NormSteps.delta_only unf;
             Fstarcompiler.FStarC_NormSteps.zeta_full] ps;
           FStar_Tactics_V2_Derived.exact
             (FStar_Tactics_V2_SyntaxCoercions.binding_to_term x6) ps))
     | uu___ -> FStar_Tactics_V2_Derived.fail "proj: more than one case?" ps)
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.MkProjectors.mk_one_projector" (Prims.of_int (4))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_3
               "FStar.Tactics.MkProjectors.mk_one_projector (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_3
                  mk_one_projector)
               (Fstarcompiler.FStarC_Syntax_Embeddings.e_list
                  Fstarcompiler.FStarC_Syntax_Embeddings.e_string)
               Fstarcompiler.FStarC_Syntax_Embeddings.e_int
               Fstarcompiler.FStarC_Syntax_Embeddings.e_int
               Fstarcompiler.FStarC_Syntax_Embeddings.e_unit psc ncb us args)
let mk_one_method (proj : Prims.string) (np : Prims.nat) :
  (unit, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    debug
      (fun uu___ ps1 ->
         FStarC_Tactics_V2_Builtins.dump "ENTRY mk_one_method" ps1; "") ps;
    (let x1 = FStarC_Reflection_V2_Builtins.explode_qn proj in
     let x2 =
       FStar_Tactics_Util.repeatn np
         (fun uu___ ps1 ->
            let x3 = FStarC_Tactics_V2_Builtins.intro () ps1 in
            ((FStar_Tactics_V2_SyntaxCoercions.binding_to_term x3),
              FStarC_Reflection_V2_Data.Q_Implicit)) ps in
     let x3 = FStarC_Tactics_V2_Builtins.intro () ps in
     let x4 =
       FStar_Tactics_NamedView.pack
         (FStar_Tactics_NamedView.Tv_FVar
            (FStarC_Reflection_V2_Builtins.pack_fv x1)) in
     FStar_Tactics_V2_Derived.exact
       (FStar_Reflection_V2_Derived.mk_app x4
          (FStar_List_Tot_Base.op_At x2
             [((FStar_Tactics_V2_SyntaxCoercions.binding_to_term x3),
                FStarC_Reflection_V2_Data.Q_Explicit)])) ps)
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.MkProjectors.mk_one_method" (Prims.of_int (3))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_2
               "FStar.Tactics.MkProjectors.mk_one_method (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_2
                  mk_one_method)
               Fstarcompiler.FStarC_Syntax_Embeddings.e_string
               Fstarcompiler.FStarC_Syntax_Embeddings.e_int
               Fstarcompiler.FStarC_Syntax_Embeddings.e_unit psc ncb us args)
let subst_map
  (uu___2 :
    (FStar_Tactics_NamedView.namedv * FStarC_Reflection_Types.fv) Prims.list)
  (uu___1 : FStar_Tactics_NamedView.term)
  (uu___ : FStar_Tactics_NamedView.term) :
  (FStar_Tactics_NamedView.term, unit) FStar_Tactics_Effect.tac_repr=
  (fun ss r t ->
     Obj.magic
       (fun uu___ ->
          FStarC_Reflection_V2_Builtins.subst_term
            (FStar_List_Tot_Base.map
               (fun uu___1 ->
                  match uu___1 with
                  | (x, fv) ->
                      FStarC_Syntax_Syntax.NT
                        ((FStarC_Reflection_V2_Builtins.pack_namedv x),
                          (FStar_Reflection_V2_Derived.mk_e_app
                             (FStar_Tactics_NamedView.pack
                                (FStar_Tactics_NamedView.Tv_FVar fv)) 
                             [r]))) ss) t)) uu___2 uu___1 uu___
let binder_mk_implicit (b : FStar_Tactics_NamedView.binder) :
  FStar_Tactics_NamedView.binder=
  let q =
    match b.FStar_Tactics_NamedView.qual with
    | FStarC_Reflection_V2_Data.Q_Explicit ->
        FStarC_Reflection_V2_Data.Q_Implicit
    | q1 -> q1 in
  {
    FStar_Tactics_NamedView.uniq = (b.FStar_Tactics_NamedView.uniq);
    FStar_Tactics_NamedView.ppname = (b.FStar_Tactics_NamedView.ppname);
    FStar_Tactics_NamedView.sort = (b.FStar_Tactics_NamedView.sort);
    FStar_Tactics_NamedView.qual = q;
    FStar_Tactics_NamedView.attrs = (b.FStar_Tactics_NamedView.attrs)
  }
let binder_to_term (b : FStar_Tactics_NamedView.binder) :
  FStar_Tactics_NamedView.term=
  FStar_Tactics_NamedView.pack
    (FStar_Tactics_NamedView.Tv_Var
       (FStar_Tactics_V2_SyntaxCoercions.binder_to_namedv b))
let binder_argv (b : FStar_Tactics_NamedView.binder) :
  FStarC_Reflection_V2_Data.argv=
  let q =
    match b.FStar_Tactics_NamedView.qual with
    | FStarC_Reflection_V2_Data.Q_Meta uu___ ->
        FStarC_Reflection_V2_Data.Q_Implicit
    | q1 -> q1 in
  ((binder_to_term b), q)
let rec list_last :
  'a . 'a Prims.list -> ('a, unit) FStar_Tactics_Effect.tac_repr =
  fun uu___ ->
    (fun xs ->
       match xs with
       | [] ->
           Obj.magic
             (Obj.repr (FStar_Tactics_V2_Derived.fail "list_last: empty"))
       | x::[] ->
           Obj.magic
             (Obj.repr (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> x)))
       | uu___::xs1 -> Obj.magic (Obj.repr (list_last xs1))) uu___
let embed_int (i : Prims.int) : FStar_Tactics_NamedView.term=
  FStarC_Reflection_V2_Builtins.pack_ln
    (FStarC_Reflection_V2_Data.Tv_Const (FStarC_Reflection_V2_Data.C_Int i))
let embed_string (s : Prims.string) : FStar_Tactics_NamedView.term=
  FStarC_Reflection_V2_Builtins.pack_ln
    (FStarC_Reflection_V2_Data.Tv_Const
       (FStarC_Reflection_V2_Data.C_String s))
let substitute_attr : FStar_Tactics_NamedView.term=
  FStarC_Reflection_V2_Builtins.pack_ln
    (FStarC_Reflection_V2_Data.Tv_FVar
       (FStarC_Reflection_V2_Builtins.pack_fv
          ["FStar"; "Attributes"; "Substitute"]))
let mk_proj_decl (is_method : Prims.bool)
  (tyqn : FStarC_Reflection_Types.name) (ctorname : Prims.string Prims.list)
  (univs : FStar_Tactics_NamedView.univ_name Prims.list)
  (params : FStar_Tactics_NamedView.binder Prims.list) (idx : Prims.nat)
  (field : FStar_Tactics_NamedView.binder)
  (unfold_names_tm : FStar_Tactics_NamedView.term)
  (smap :
    (FStar_Tactics_NamedView.namedv * FStarC_Reflection_Types.fv) Prims.list)
  :
  ((FStarC_Reflection_Types.sigelt Prims.list * FStarC_Reflection_Types.fv),
    unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    debug
      (fun uu___ ps1 ->
         let x1 =
           FStarC_Tactics_Unseal.unseal field.FStar_Tactics_NamedView.ppname
             ps1 in
         Prims.strcat "Processing field " x1) ps;
    debug
      (fun uu___ ps1 ->
         let x2 =
           FStarC_Tactics_V2_Builtins.term_to_string
             field.FStar_Tactics_NamedView.sort ps1 in
         Prims.strcat "Field typ = " x2) ps;
    (let x2 = FStar_List_Tot_Base.length params in
     let x3 = FStarC_Reflection_V2_Builtins.pack_fv tyqn in
     let x4 =
       let x5 = FStar_Tactics_V2_Derived.cur_module () ps in
       let x6 =
         let x7 =
           let x8 =
             let x9 = list_last ctorname ps in
             let x10 =
               let x11 =
                 FStarC_Tactics_Unseal.unseal
                   field.FStar_Tactics_NamedView.ppname ps in
               Prims.strcat "__item__" x11 in
             Prims.strcat x9 x10 in
           Prims.strcat "__proj__" x8 in
         [x7] in
       FStar_List_Tot_Base.op_At x5 x6 in
     let x5 = FStarC_Reflection_V2_Builtins.pack_fv x4 in
     let x6 =
       FStar_Reflection_V2_Derived.mk_app
         (FStar_Tactics_NamedView.pack
            (FStar_Tactics_NamedView.Tv_UInst
               (x3,
                 (FStar_List_Tot_Base.map
                    (fun un ->
                       FStar_Tactics_NamedView.pack_universe
                         (FStar_Tactics_NamedView.Uv_Name un)) univs))))
         (FStar_List_Tot_Base.map binder_argv params) in
     let x7 = FStar_Tactics_V2_Derived.fresh_binder x6 ps in
     let x8 =
       let x9 =
         subst_map smap (binder_to_term x7)
           field.FStar_Tactics_NamedView.sort ps in
       FStar_Tactics_V2_SyntaxHelpers.mk_tot_arr
         (FStar_List_Tot_Base.op_At
            (FStar_List_Tot_Base.map binder_mk_implicit params) [x7]) x9 ps in
     debug
       (fun uu___ ps1 ->
          let x10 = FStarC_Tactics_V2_Builtins.term_to_string x8 ps1 in
          Prims.strcat "Proj typ = " x10) ps;
     (let x10 =
        FStar_Tactics_NamedView.pack_sigelt
          (FStar_Tactics_NamedView.Sg_Let
             {
               FStar_Tactics_NamedView.isrec = false;
               FStar_Tactics_NamedView.lbs =
                 [{
                    FStar_Tactics_NamedView.lb_fv = x5;
                    FStar_Tactics_NamedView.lb_us = univs;
                    FStar_Tactics_NamedView.lb_typ = x8;
                    FStar_Tactics_NamedView.lb_def =
                      (FStarC_Reflection_V2_Builtins.pack_ln
                         (FStarC_Reflection_V2_Data.Tv_App
                            ((FStarC_Reflection_V2_Builtins.pack_ln
                                (FStarC_Reflection_V2_Data.Tv_FVar
                                   (FStarC_Reflection_V2_Builtins.pack_fv
                                      ["FStar";
                                      "Tactics";
                                      "Effect";
                                      "synth_by_tactic"]))),
                              ((FStarC_Reflection_V2_Builtins.pack_ln
                                  (FStarC_Reflection_V2_Data.Tv_Abs
                                     ((FStarC_Reflection_V2_Builtins.pack_binder
                                         {
                                           FStarC_Reflection_V2_Data.sort2 =
                                             (FStarC_Reflection_V2_Builtins.pack_ln
                                                FStarC_Reflection_V2_Data.Tv_Unknown);
                                           FStarC_Reflection_V2_Data.qual =
                                             FStarC_Reflection_V2_Data.Q_Explicit;
                                           FStarC_Reflection_V2_Data.attrs =
                                             [];
                                           FStarC_Reflection_V2_Data.ppname2
                                             = (FStar_Sealed.seal "uu___")
                                         }),
                                       (FStarC_Reflection_V2_Builtins.pack_ln
                                          (FStarC_Reflection_V2_Data.Tv_App
                                             ((FStarC_Reflection_V2_Builtins.pack_ln
                                                 (FStarC_Reflection_V2_Data.Tv_App
                                                    ((FStarC_Reflection_V2_Builtins.pack_ln
                                                        (FStarC_Reflection_V2_Data.Tv_App
                                                           ((FStarC_Reflection_V2_Builtins.pack_ln
                                                               (FStarC_Reflection_V2_Data.Tv_FVar
                                                                  (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "MkProjectors";
                                                                    "mk_one_projector"]))),
                                                             (unfold_names_tm,
                                                               FStarC_Reflection_V2_Data.Q_Explicit)))),
                                                      ((embed_int x2),
                                                        FStarC_Reflection_V2_Data.Q_Explicit)))),
                                               ((embed_int idx),
                                                 FStarC_Reflection_V2_Data.Q_Explicit))))))),
                                FStarC_Reflection_V2_Data.Q_Explicit))))
                  }]
             }) ps in
      let x11 =
        if Prims.op_Negation is_method
        then []
        else
          if
            FStar_List_Tot_Base.existsb
              (FStar_Reflection_TermEq_Simple.term_eq
                 (FStarC_Reflection_V2_Builtins.pack_ln
                    (FStarC_Reflection_V2_Data.Tv_FVar
                       (FStarC_Reflection_V2_Builtins.pack_fv
                          ["FStar"; "Tactics"; "Typeclasses"; "no_method"]))))
              field.FStar_Tactics_NamedView.attrs
          then []
          else
            (let x12 =
               let x13 =
                 let x14 = FStar_Tactics_V2_Derived.cur_module () ps in
                 let x15 =
                   let x16 =
                     FStarC_Tactics_Unseal.unseal
                       field.FStar_Tactics_NamedView.ppname ps in
                   [x16] in
                 FStar_List_Tot_Base.op_At x14 x15 in
               FStarC_Reflection_V2_Builtins.pack_fv x13 in
             let x13 =
               {
                 FStar_Tactics_NamedView.uniq =
                   (x7.FStar_Tactics_NamedView.uniq);
                 FStar_Tactics_NamedView.ppname =
                   (x7.FStar_Tactics_NamedView.ppname);
                 FStar_Tactics_NamedView.sort =
                   (x7.FStar_Tactics_NamedView.sort);
                 FStar_Tactics_NamedView.qual =
                   (FStarC_Reflection_V2_Data.Q_Meta
                      (FStarC_Reflection_V2_Builtins.pack_ln
                         (FStarC_Reflection_V2_Data.Tv_FVar
                            (FStarC_Reflection_V2_Builtins.pack_fv
                               ["FStar";
                               "Tactics";
                               "Typeclasses";
                               "tcresolve"]))));
                 FStar_Tactics_NamedView.attrs =
                   (x7.FStar_Tactics_NamedView.attrs)
               } in
             let x14 =
               let x15 =
                 subst_map smap (binder_to_term x13)
                   field.FStar_Tactics_NamedView.sort ps in
               FStar_Tactics_V2_SyntaxHelpers.mk_tot_arr
                 (FStar_List_Tot_Base.op_At
                    (FStar_List_Tot_Base.map binder_mk_implicit params) 
                    [x13]) x15 ps in
             let x15 =
               FStarC_Reflection_V2_Builtins.pack_ln
                 (FStarC_Reflection_V2_Data.Tv_App
                    ((FStarC_Reflection_V2_Builtins.pack_ln
                        (FStarC_Reflection_V2_Data.Tv_FVar
                           (FStarC_Reflection_V2_Builtins.pack_fv
                              ["FStar";
                              "Tactics";
                              "Effect";
                              "synth_by_tactic"]))),
                      ((FStarC_Reflection_V2_Builtins.pack_ln
                          (FStarC_Reflection_V2_Data.Tv_Abs
                             ((FStarC_Reflection_V2_Builtins.pack_binder
                                 {
                                   FStarC_Reflection_V2_Data.sort2 =
                                     (FStarC_Reflection_V2_Builtins.pack_ln
                                        FStarC_Reflection_V2_Data.Tv_Unknown);
                                   FStarC_Reflection_V2_Data.qual =
                                     FStarC_Reflection_V2_Data.Q_Explicit;
                                   FStarC_Reflection_V2_Data.attrs = [];
                                   FStarC_Reflection_V2_Data.ppname2 =
                                     (FStar_Sealed.seal "uu___")
                                 }),
                               (FStarC_Reflection_V2_Builtins.pack_ln
                                  (FStarC_Reflection_V2_Data.Tv_App
                                     ((FStarC_Reflection_V2_Builtins.pack_ln
                                         (FStarC_Reflection_V2_Data.Tv_App
                                            ((FStarC_Reflection_V2_Builtins.pack_ln
                                                (FStarC_Reflection_V2_Data.Tv_FVar
                                                   (FStarC_Reflection_V2_Builtins.pack_fv
                                                      ["FStar";
                                                      "Tactics";
                                                      "MkProjectors";
                                                      "mk_one_method"]))),
                                              ((embed_string
                                                  (FStarC_Reflection_V2_Builtins.implode_qn
                                                     x4)),
                                                FStarC_Reflection_V2_Data.Q_Explicit)))),
                                       ((embed_int x2),
                                         FStarC_Reflection_V2_Data.Q_Explicit))))))),
                        FStarC_Reflection_V2_Data.Q_Explicit))) in
             let x16 =
               FStar_Tactics_NamedView.pack_sigelt
                 (FStar_Tactics_NamedView.Sg_Let
                    {
                      FStar_Tactics_NamedView.isrec = false;
                      FStar_Tactics_NamedView.lbs =
                        [{
                           FStar_Tactics_NamedView.lb_fv = x12;
                           FStar_Tactics_NamedView.lb_us = univs;
                           FStar_Tactics_NamedView.lb_typ = x14;
                           FStar_Tactics_NamedView.lb_def = x15
                         }]
                    }) ps in
             [x16]) in
      (((FStarC_Reflection_V2_Builtins.set_sigelt_attrs
           (FStar_List_Tot_Base.op_At (substitute_attr ::
              (field.FStar_Tactics_NamedView.attrs))
              (FStarC_Reflection_V2_Builtins.sigelt_attrs x10)) x10) :: x11),
        x5)))
let mk_projs (is_class : Prims.bool) (tyname : Prims.string) :
  (FStarC_Reflection_Types.sigelt Prims.list, unit)
    FStar_Tactics_Effect.tac_repr=
  fun ps ->
    debug
      (fun uu___ ->
         (fun uu___ ->
            Obj.magic
              (fun uu___1 ->
                 Prims.strcat "!! mk_projs tactic called on: " tyname)) uu___)
      ps;
    (let x1 = FStarC_Reflection_V2_Builtins.explode_qn tyname in
     let x2 =
       let x3 = FStarC_Tactics_V2_Builtins.top_env () ps in
       FStarC_Reflection_V2_Builtins.lookup_typ x3 x1 in
     match x2 with
     | FStar_Pervasives_Native.None ->
         Obj.magic
           (Obj.repr (FStarC_Tactics_V2_Builtins.raise_core NotFound ps))
     | FStar_Pervasives_Native.Some se ->
         Obj.magic
           (Obj.repr
              (let x3 = FStar_Tactics_NamedView.inspect_sigelt se ps in
               match x3 with
               | FStar_Tactics_NamedView.Sg_Inductive
                   { FStar_Tactics_NamedView.nm = nm;
                     FStar_Tactics_NamedView.univs1 = univs;
                     FStar_Tactics_NamedView.params = params;
                     FStar_Tactics_NamedView.typ = typ;
                     FStar_Tactics_NamedView.ctors = ctors;_}
                   ->
                   (if (FStar_List_Tot_Base.length ctors) <> Prims.int_one
                    then
                      FStar_Tactics_V2_Derived.fail
                        "Expected an inductive with one constructor" ps
                    else ();
                    (let x5 =
                       let x6 =
                         FStar_Tactics_V2_SyntaxHelpers.collect_arr_bs typ ps in
                       FStar_Pervasives_Native.fst x6 in
                     if Prims.uu___is_Cons x5
                     then
                       FStar_Tactics_V2_Derived.fail
                         "Inductive indices nonempty?" ps
                     else ();
                     (let x7 = ctors in
                      match x7 with
                      | (ctorname, ctor_t)::[] ->
                          let x8 =
                            FStar_Tactics_V2_SyntaxHelpers.collect_arr_bs
                              ctor_t ps in
                          (match x8 with
                           | (fields, uu___) ->
                               let x9 =
                                 FStarC_Reflection_V2_Builtins.pack_ln
                                   (FStarC_Reflection_V2_Data.Tv_App
                                      ((FStarC_Reflection_V2_Builtins.pack_ln
                                          (FStarC_Reflection_V2_Data.Tv_UInst
                                             ((FStarC_Reflection_V2_Builtins.pack_fv
                                                 ["Prims"; "Nil"]),
                                               [FStarC_Reflection_V2_Builtins.pack_universe
                                                  FStarC_Reflection_V2_Data.Uv_Zero]))),
                                        ((FStarC_Reflection_V2_Builtins.pack_ln
                                            (FStarC_Reflection_V2_Data.Tv_FVar
                                               (FStarC_Reflection_V2_Builtins.pack_fv
                                                  ["Prims"; "string"]))),
                                          FStarC_Reflection_V2_Data.Q_Implicit))) in
                               let x10 =
                                 FStar_Tactics_Util.fold_left
                                   (fun uu___1 field ->
                                      match uu___1 with
                                      | (decls, smap, unfold_names_tm, idx)
                                          ->
                                          FStar_Tactics_Effect.tac_bind
                                            (Obj.magic
                                               (mk_proj_decl is_class x1
                                                  ctorname univs params idx
                                                  field unfold_names_tm smap))
                                            (fun uu___2 uu___3 ->
                                               match uu___2 with
                                               | (ds, fv) ->
                                                   ((FStar_List_Tot_Base.op_At
                                                       decls ds),
                                                     (((FStar_Tactics_V2_SyntaxCoercions.binder_to_namedv
                                                          field), fv) ::
                                                     smap),
                                                     (FStarC_Reflection_V2_Builtins.pack_ln
                                                        (FStarC_Reflection_V2_Data.Tv_App
                                                           ((FStarC_Reflection_V2_Builtins.pack_ln
                                                               (FStarC_Reflection_V2_Data.Tv_App
                                                                  ((FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_App
                                                                    ((FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_UInst
                                                                    ((FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["Prims";
                                                                    "Cons"]),
                                                                    [
                                                                    FStarC_Reflection_V2_Builtins.pack_universe
                                                                    FStarC_Reflection_V2_Data.Uv_Zero]))),
                                                                    ((FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["Prims";
                                                                    "string"]))),
                                                                    FStarC_Reflection_V2_Data.Q_Implicit)))),
                                                                    ((embed_string
                                                                    (FStarC_Reflection_V2_Builtins.implode_qn
                                                                    (FStarC_Reflection_V2_Builtins.inspect_fv
                                                                    fv))),
                                                                    FStarC_Reflection_V2_Data.Q_Explicit)))),
                                                             (unfold_names_tm,
                                                               FStarC_Reflection_V2_Data.Q_Explicit)))),
                                                     (idx + Prims.int_one))))
                                   ([], [], x9, Prims.int_zero) fields ps in
                               (match x10 with
                                | (decls, uu___1, uu___2, uu___3) -> decls)))))
               | uu___ -> FStar_Tactics_V2_Derived.fail "not an inductive" ps)))
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.MkProjectors.mk_projs" (Prims.of_int (3))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_2
               "FStar.Tactics.MkProjectors.mk_projs (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_2 mk_projs)
               Fstarcompiler.FStarC_Syntax_Embeddings.e_bool
               Fstarcompiler.FStarC_Syntax_Embeddings.e_string
               (Fstarcompiler.FStarC_Syntax_Embeddings.e_list
                  Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_sigelt) psc
               ncb us args)
