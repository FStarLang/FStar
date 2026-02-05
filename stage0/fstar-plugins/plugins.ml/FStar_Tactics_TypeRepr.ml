open Fstarcompiler
open Prims
let empty_elim (uu___1 : Prims.empty) (uu___ : unit) : Obj.t=
  (fun e a -> Obj.magic (failwith "unreachable")) uu___1 uu___
let add_suffix (s : Prims.string) (nm : FStarC_Reflection_Types.name) :
  FStarC_Reflection_Types.name=
  FStarC_Reflection_V2_Builtins.explode_qn
    (Prims.strcat (FStarC_Reflection_V2_Builtins.implode_qn nm) s)
let unitv_ : FStar_Tactics_NamedView.term=
  FStarC_Reflection_V2_Builtins.pack_ln
    (FStarC_Reflection_V2_Data.Tv_Const FStarC_Reflection_V2_Data.C_Unit)
let unitt_ : FStar_Tactics_NamedView.term=
  FStarC_Reflection_V2_Builtins.pack_ln
    (FStarC_Reflection_V2_Data.Tv_FVar
       (FStarC_Reflection_V2_Builtins.pack_fv ["Prims"; "unit"]))
let empty_ : FStar_Tactics_NamedView.term=
  FStarC_Reflection_V2_Builtins.pack_ln
    (FStarC_Reflection_V2_Data.Tv_FVar
       (FStarC_Reflection_V2_Builtins.pack_fv ["Prims"; "empty"]))
let either_ (a : FStar_Tactics_NamedView.term)
  (b : FStar_Tactics_NamedView.term) : FStar_Tactics_NamedView.term=
  FStarC_Reflection_V2_Builtins.pack_ln
    (FStarC_Reflection_V2_Data.Tv_App
       ((FStarC_Reflection_V2_Builtins.pack_ln
           (FStarC_Reflection_V2_Data.Tv_App
              ((FStarC_Reflection_V2_Builtins.pack_ln
                  (FStarC_Reflection_V2_Data.Tv_FVar
                     (FStarC_Reflection_V2_Builtins.pack_fv
                        ["FStar"; "Pervasives"; "either"]))),
                (a, FStarC_Reflection_V2_Data.Q_Explicit)))),
         (b, FStarC_Reflection_V2_Data.Q_Explicit)))
let tuple2_ (a : FStar_Tactics_NamedView.term)
  (b : FStar_Tactics_NamedView.term) : FStar_Tactics_NamedView.term=
  FStarC_Reflection_V2_Builtins.pack_ln
    (FStarC_Reflection_V2_Data.Tv_App
       ((FStarC_Reflection_V2_Builtins.pack_ln
           (FStarC_Reflection_V2_Data.Tv_App
              ((FStarC_Reflection_V2_Builtins.pack_ln
                  (FStarC_Reflection_V2_Data.Tv_FVar
                     (FStarC_Reflection_V2_Builtins.pack_fv
                        ["FStar"; "Pervasives"; "Native"; "tuple2"]))),
                (a, FStarC_Reflection_V2_Data.Q_Explicit)))),
         (b, FStarC_Reflection_V2_Data.Q_Explicit)))
let mktuple2_ (a : FStar_Tactics_NamedView.term)
  (b : FStar_Tactics_NamedView.term) : FStar_Tactics_NamedView.term=
  FStarC_Reflection_V2_Builtins.pack_ln
    (FStarC_Reflection_V2_Data.Tv_App
       ((FStarC_Reflection_V2_Builtins.pack_ln
           (FStarC_Reflection_V2_Data.Tv_App
              ((FStarC_Reflection_V2_Builtins.pack_ln
                  (FStarC_Reflection_V2_Data.Tv_FVar
                     (FStarC_Reflection_V2_Builtins.pack_fv
                        ["FStar"; "Pervasives"; "Native"; "Mktuple2"]))),
                (a, FStarC_Reflection_V2_Data.Q_Explicit)))),
         (b, FStarC_Reflection_V2_Data.Q_Explicit)))
let get_inductive_typ (nm : Prims.string) :
  (FStar_Tactics_NamedView.sigelt_view, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = FStarC_Tactics_V2_Builtins.top_env () ps in
    let x1 =
      FStarC_Reflection_V2_Builtins.lookup_typ x
        (FStarC_Reflection_V2_Builtins.explode_qn nm) in
    match x1 with
    | FStar_Pervasives_Native.None ->
        FStar_Tactics_V2_Derived.fail "ctors_of_typ: type not found" ps
    | FStar_Pervasives_Native.Some se ->
        let x2 = FStar_Tactics_NamedView.inspect_sigelt se ps in
        if FStar_Tactics_NamedView.uu___is_Sg_Inductive x2
        then x2
        else
          FStar_Tactics_V2_Derived.fail "ctors_of_typ: not an inductive type"
            ps
let alg_ctor (ty : FStarC_Reflection_Types.typ) :
  (FStarC_Reflection_Types.typ, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = FStar_Tactics_V2_SyntaxHelpers.collect_arr ty ps in
    match x with
    | (tys, c) ->
        FStar_Tactics_Util.fold_right
          (fun uu___1 uu___ ->
             (fun ty1 acc -> Obj.magic (fun uu___ -> tuple2_ ty1 acc)) uu___1
               uu___) tys unitt_ ps
let generate_repr_typ (params : FStar_Tactics_NamedView.binders)
  (ctors : FStarC_Reflection_V2_Data.ctor Prims.list) :
  (FStarC_Reflection_Types.typ, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x =
      FStar_Tactics_Util.map
        (fun uu___ -> match uu___ with | (uu___1, ty) -> alg_ctor ty) ctors
        ps in
    let x1 =
      FStar_Tactics_Util.fold_right
        (fun uu___1 uu___ ->
           (fun ty acc -> Obj.magic (fun uu___ -> either_ ty acc)) uu___1
             uu___) x empty_ ps in
    x1
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.TypeRepr.generate_repr_typ" (Prims.of_int (3))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_2
               "FStar.Tactics.TypeRepr.generate_repr_typ (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_2
                  generate_repr_typ)
               (Fstarcompiler.FStarC_Syntax_Embeddings.e_list
                  FStar_Tactics_NamedView.e_binder)
               (Fstarcompiler.FStarC_Syntax_Embeddings.e_list
                  (Fstarcompiler.FStarC_Syntax_Embeddings.e_tuple2
                     (Fstarcompiler.FStarC_Syntax_Embeddings.e_list
                        Fstarcompiler.FStarC_Syntax_Embeddings.e_string)
                     Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term))
               Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term psc ncb
               us args)
let generate_down (uu___ : unit) :
  (unit, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = FStarC_Tactics_V2_Builtins.intro () ps in
    let x1 =
      FStarC_Tactics_V2_Builtins.t_destruct
        (FStar_Tactics_V2_SyntaxCoercions.binding_to_term x) ps in
    FStar_Tactics_Util.iteri
      (fun i uu___1 ->
         match uu___1 with
         | (c, n) ->
             FStar_Tactics_Effect.tac_bind
               (Obj.magic
                  (FStar_Tactics_Util.repeatn n
                     (fun uu___2 -> FStarC_Tactics_V2_Builtins.intro ())))
               (fun uu___2 ->
                  (fun bs ->
                     Obj.magic
                       (fun ps1 ->
                          let x2 = FStarC_Tactics_V2_Builtins.intro () ps1 in
                          let x3 =
                            FStar_Tactics_Util.fold_right
                              (fun uu___3 uu___2 ->
                                 (fun b acc ->
                                    Obj.magic
                                      (fun uu___2 ->
                                         mktuple2_
                                           (FStar_Tactics_V2_SyntaxCoercions.binding_to_term
                                              b) acc)) uu___3 uu___2) bs
                              unitv_ ps1 in
                          let x4 =
                            FStar_Tactics_Util.repeatn i
                              (fun uu___2 ->
                                 FStar_Tactics_V2_Derived.apply
                                   (FStarC_Reflection_V2_Builtins.pack_ln
                                      (FStarC_Reflection_V2_Data.Tv_FVar
                                         (FStarC_Reflection_V2_Builtins.pack_fv
                                            ["FStar"; "Pervasives"; "Inr"]))))
                              ps1 in
                          FStar_Tactics_V2_Derived.apply
                            (FStarC_Reflection_V2_Builtins.pack_ln
                               (FStarC_Reflection_V2_Data.Tv_FVar
                                  (FStarC_Reflection_V2_Builtins.pack_fv
                                     ["FStar"; "Pervasives"; "Inl"]))) ps1;
                          FStar_Tactics_V2_Derived.exact x3 ps1)) uu___2)) x1
      ps
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.TypeRepr.generate_down" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.TypeRepr.generate_down (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_1
                  generate_down)
               Fstarcompiler.FStarC_Syntax_Embeddings.e_unit
               Fstarcompiler.FStarC_Syntax_Embeddings.e_unit psc ncb us args)
let rec get_apply_tuple (b : FStar_Tactics_NamedView.binding) :
  (FStar_Tactics_NamedView.binding Prims.list, unit)
    FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x =
      FStar_Tactics_V2_SyntaxHelpers.collect_app
        b.FStarC_Reflection_V2_Data.sort3 ps in
    match x with
    | (hd, args) ->
        let x1 = let x2 = FStar_Tactics_NamedView.inspect hd ps in (x2, args) in
        (match x1 with
         | (FStar_Tactics_NamedView.Tv_UInst (fv, uu___), b1::b2::[]) ->
             if
               (FStarC_Reflection_V2_Builtins.inspect_fv fv) =
                 ["FStar"; "Pervasives"; "Native"; "tuple2"]
             then
               let x2 =
                 FStarC_Tactics_V2_Builtins.t_destruct
                   (FStar_Tactics_V2_SyntaxCoercions.binding_to_term b) ps in
               (FStar_Tactics_V2_Derived.guard
                  ((((FStar_List_Tot_Base.length x2) = Prims.int_one) &&
                      ((FStarC_Reflection_V2_Builtins.inspect_fv
                          (FStar_Pervasives_Native.fst
                             (FStar_List_Tot_Base.hd x2)))
                         = ["FStar"; "Pervasives"; "Native"; "Mktuple2"]))
                     &&
                     ((FStar_Pervasives_Native.snd
                         (FStar_List_Tot_Base.hd x2))
                        = (Prims.of_int (2)))) ps;
                (let x4 = FStarC_Tactics_V2_Builtins.intro () ps in
                 let x5 = FStarC_Tactics_V2_Builtins.intro () ps in
                 let x6 = FStarC_Tactics_V2_Builtins.intro () ps in
                 let x7 = get_apply_tuple x5 ps in x4 :: x7))
             else
               (let x2 =
                  let x3 =
                    FStarC_Tactics_V2_Builtins.term_to_string
                      b.FStarC_Reflection_V2_Data.sort3 ps in
                  Prims.strcat "unexpected term in apply_tuple: " x3 in
                FStar_Tactics_V2_Derived.fail x2 ps)
         | (FStar_Tactics_NamedView.Tv_FVar fv, b1::b2::[]) ->
             if
               (FStarC_Reflection_V2_Builtins.inspect_fv fv) =
                 ["FStar"; "Pervasives"; "Native"; "tuple2"]
             then
               let x2 =
                 FStarC_Tactics_V2_Builtins.t_destruct
                   (FStar_Tactics_V2_SyntaxCoercions.binding_to_term b) ps in
               (FStar_Tactics_V2_Derived.guard
                  ((((FStar_List_Tot_Base.length x2) = Prims.int_one) &&
                      ((FStarC_Reflection_V2_Builtins.inspect_fv
                          (FStar_Pervasives_Native.fst
                             (FStar_List_Tot_Base.hd x2)))
                         = ["FStar"; "Pervasives"; "Native"; "Mktuple2"]))
                     &&
                     ((FStar_Pervasives_Native.snd
                         (FStar_List_Tot_Base.hd x2))
                        = (Prims.of_int (2)))) ps;
                (let x4 = FStarC_Tactics_V2_Builtins.intro () ps in
                 let x5 = FStarC_Tactics_V2_Builtins.intro () ps in
                 let x6 = FStarC_Tactics_V2_Builtins.intro () ps in
                 let x7 = get_apply_tuple x5 ps in x4 :: x7))
             else
               (let x2 =
                  let x3 =
                    FStarC_Tactics_V2_Builtins.term_to_string
                      b.FStarC_Reflection_V2_Data.sort3 ps in
                  Prims.strcat "unexpected term in apply_tuple: " x3 in
                FStar_Tactics_V2_Derived.fail x2 ps)
         | (FStar_Tactics_NamedView.Tv_FVar fv, []) ->
             if
               (FStarC_Reflection_V2_Builtins.inspect_fv fv) =
                 ["Prims"; "unit"]
             then []
             else
               (let x2 =
                  let x3 =
                    FStarC_Tactics_V2_Builtins.term_to_string
                      b.FStarC_Reflection_V2_Data.sort3 ps in
                  Prims.strcat "unexpected term in apply_tuple: " x3 in
                FStar_Tactics_V2_Derived.fail x2 ps)
         | uu___ ->
             let x2 =
               let x3 =
                 FStarC_Tactics_V2_Builtins.term_to_string
                   b.FStarC_Reflection_V2_Data.sort3 ps in
               Prims.strcat "unexpected term in apply_tuple: " x3 in
             FStar_Tactics_V2_Derived.fail x2 ps)
let rec generate_up_aux (ctors : FStarC_Reflection_V2_Data.ctor Prims.list)
  (b : FStar_Tactics_NamedView.binding) :
  (unit, unit) FStar_Tactics_Effect.tac_repr=
  match ctors with
  | [] ->
      (fun ps ->
         FStar_Tactics_V2_Derived.apply
           (FStarC_Reflection_V2_Builtins.pack_ln
              (FStarC_Reflection_V2_Data.Tv_FVar
                 (FStarC_Reflection_V2_Builtins.pack_fv
                    ["FStar"; "Tactics"; "TypeRepr"; "empty_elim"]))) ps;
         FStar_Tactics_V2_Derived.exact
           (FStar_Tactics_V2_SyntaxCoercions.binding_to_term b) ps)
  | c::cs ->
      FStar_Tactics_Effect.tac_bind
        (Obj.magic
           (FStarC_Tactics_V2_Builtins.t_destruct
              (FStar_Tactics_V2_SyntaxCoercions.binding_to_term b)))
        (fun uu___ ->
           (fun cases ->
              Obj.magic
                (fun ps ->
                   if
                     (FStar_List_Tot_Base.length cases) <> (Prims.of_int (2))
                   then
                     FStar_Tactics_V2_Derived.fail
                       "generate_up_aux: expected Inl/Inr???" ps
                   else ();
                   FStar_Tactics_V2_Derived.focus
                     (fun uu___ ps1 ->
                        let x2 = FStarC_Tactics_V2_Builtins.intro () ps1 in
                        let x3 = FStarC_Tactics_V2_Builtins.intro () ps1 in
                        let x4 = FStar_Pervasives_Native.fst c in
                        let x5 = get_apply_tuple x2 ps1 in
                        FStar_Tactics_V2_Derived.apply
                          (FStar_Tactics_NamedView.pack
                             (FStar_Tactics_NamedView.Tv_FVar
                                (FStarC_Reflection_V2_Builtins.pack_fv x4)))
                          ps1;
                        FStar_Tactics_Util.iter
                          (fun b1 ->
                             FStar_Tactics_V2_Derived.exact
                               (FStar_Tactics_V2_SyntaxCoercions.binding_to_term
                                  b1)) x5 ps1;
                        FStar_Tactics_V2_Derived.qed () ps1) ps;
                   (let x2 = FStarC_Tactics_V2_Builtins.intro () ps in
                    let x3 = FStarC_Tactics_V2_Builtins.intro () ps in
                    generate_up_aux cs x2 ps))) uu___)
let generate_up (nm : Prims.string) (uu___ : unit) :
  (unit, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = get_inductive_typ nm ps in
    match x with
    | FStar_Tactics_NamedView.Sg_Inductive
        { FStar_Tactics_NamedView.nm = uu___1;
          FStar_Tactics_NamedView.univs1 = uu___2;
          FStar_Tactics_NamedView.params = uu___3;
          FStar_Tactics_NamedView.typ = uu___4;
          FStar_Tactics_NamedView.ctors = ctors;_}
        ->
        let x1 = FStarC_Tactics_V2_Builtins.intro () ps in
        generate_up_aux ctors x1 ps
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.TypeRepr.generate_up" (Prims.of_int (3))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_2
               "FStar.Tactics.TypeRepr.generate_up (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_2 generate_up)
               Fstarcompiler.FStarC_Syntax_Embeddings.e_string
               Fstarcompiler.FStarC_Syntax_Embeddings.e_unit
               Fstarcompiler.FStarC_Syntax_Embeddings.e_unit psc ncb us args)
let make_implicits (bs : FStar_Tactics_NamedView.binders) :
  FStar_Tactics_NamedView.binders=
  FStar_List_Tot_Base.map
    (fun b ->
       match b.FStar_Tactics_NamedView.qual with
       | FStarC_Reflection_V2_Data.Q_Explicit ->
           {
             FStar_Tactics_NamedView.uniq = (b.FStar_Tactics_NamedView.uniq);
             FStar_Tactics_NamedView.ppname =
               (b.FStar_Tactics_NamedView.ppname);
             FStar_Tactics_NamedView.sort = (b.FStar_Tactics_NamedView.sort);
             FStar_Tactics_NamedView.qual =
               FStarC_Reflection_V2_Data.Q_Implicit;
             FStar_Tactics_NamedView.attrs =
               (b.FStar_Tactics_NamedView.attrs)
           }
       | uu___ -> b) bs
let binder_to_argv (b : FStar_Tactics_NamedView.binder) :
  FStarC_Reflection_V2_Data.argv=
  ((FStar_Tactics_V2_SyntaxCoercions.binder_to_term b),
    (b.FStar_Tactics_NamedView.qual))
let generate_all (nm : FStarC_Reflection_Types.name)
  (params : FStar_Tactics_NamedView.binders)
  (ctors : FStarC_Reflection_V2_Data.ctor Prims.list) :
  (FStarC_Reflection_Types.decls, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = make_implicits params in
    let x1 =
      FStar_Reflection_V2_Derived.mk_app
        (FStar_Tactics_NamedView.pack
           (FStar_Tactics_NamedView.Tv_FVar
              (FStarC_Reflection_V2_Builtins.pack_fv nm)))
        (FStar_List_Tot_Base.map binder_to_argv params) in
    let x2 = generate_repr_typ params ctors ps in
    let x3 =
      let x4 =
        let x5 =
          let x6 =
            let x7 =
              let x8 =
                FStar_Tactics_V2_SyntaxHelpers.mk_arr params
                  (FStarC_Reflection_V2_Data.C_Total
                     (FStarC_Reflection_V2_Builtins.pack_ln
                        (FStarC_Reflection_V2_Data.Tv_Type
                           (FStarC_Reflection_V2_Builtins.pack_universe
                              FStarC_Reflection_V2_Data.Uv_Unk)))) ps in
              let x9 = FStar_Tactics_V2_Derived.mk_abs params x2 ps in
              {
                FStar_Tactics_NamedView.lb_fv =
                  (FStarC_Reflection_V2_Builtins.pack_fv
                     (add_suffix "_repr" nm));
                FStar_Tactics_NamedView.lb_us = [];
                FStar_Tactics_NamedView.lb_typ = x8;
                FStar_Tactics_NamedView.lb_def = x9
              } in
            [x7] in
          {
            FStar_Tactics_NamedView.isrec = false;
            FStar_Tactics_NamedView.lbs = x6
          } in
        FStar_Tactics_NamedView.Sg_Let x5 in
      FStar_Tactics_NamedView.pack_sigelt x4 ps in
    let x4 =
      FStarC_Reflection_V2_Builtins.pack_ln
        (FStarC_Reflection_V2_Data.Tv_App
           ((FStarC_Reflection_V2_Builtins.pack_ln
               (FStarC_Reflection_V2_Data.Tv_FVar
                  (FStarC_Reflection_V2_Builtins.pack_fv
                     ["FStar"; "Tactics"; "Effect"; "synth_by_tactic"]))),
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
                                (FStarC_Reflection_V2_Data.Tv_FVar
                                   (FStarC_Reflection_V2_Builtins.pack_fv
                                      ["FStar";
                                      "Tactics";
                                      "TypeRepr";
                                      "generate_down"]))),
                              ((FStarC_Reflection_V2_Builtins.pack_ln
                                  (FStarC_Reflection_V2_Data.Tv_Const
                                     FStarC_Reflection_V2_Data.C_Unit)),
                                FStarC_Reflection_V2_Data.Q_Explicit))))))),
               FStarC_Reflection_V2_Data.Q_Explicit))) in
    let x5 = FStar_Tactics_V2_Derived.mk_abs x x4 ps in
    let x6 =
      let x7 = FStar_Tactics_V2_Derived.fresh_binder x1 ps in
      let x8 =
        let x9 =
          let x10 =
            let x11 =
              let x12 =
                FStar_Tactics_V2_SyntaxHelpers.mk_tot_arr x
                  (FStar_Tactics_NamedView.pack
                     (FStar_Tactics_NamedView.Tv_Arrow
                        (x7, (FStarC_Reflection_V2_Data.C_Total x2)))) ps in
              {
                FStar_Tactics_NamedView.lb_fv =
                  (FStarC_Reflection_V2_Builtins.pack_fv
                     (add_suffix "_down" nm));
                FStar_Tactics_NamedView.lb_us = [];
                FStar_Tactics_NamedView.lb_typ = x12;
                FStar_Tactics_NamedView.lb_def = x5
              } in
            [x11] in
          {
            FStar_Tactics_NamedView.isrec = false;
            FStar_Tactics_NamedView.lbs = x10
          } in
        FStar_Tactics_NamedView.Sg_Let x9 in
      FStar_Tactics_NamedView.pack_sigelt x8 ps in
    let x7 =
      FStarC_Reflection_V2_Builtins.pack_ln
        (FStarC_Reflection_V2_Data.Tv_App
           ((FStarC_Reflection_V2_Builtins.pack_ln
               (FStarC_Reflection_V2_Data.Tv_FVar
                  (FStarC_Reflection_V2_Builtins.pack_fv
                     ["FStar"; "Tactics"; "Effect"; "synth_by_tactic"]))),
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
                                             "TypeRepr";
                                             "generate_up"]))),
                                     ((FStar_Tactics_NamedView.pack
                                         (FStar_Tactics_NamedView.Tv_Const
                                            (FStarC_Reflection_V2_Data.C_String
                                               (FStarC_Reflection_V2_Builtins.implode_qn
                                                  nm)))),
                                       FStarC_Reflection_V2_Data.Q_Explicit)))),
                              ((FStarC_Reflection_V2_Builtins.pack_ln
                                  (FStarC_Reflection_V2_Data.Tv_Const
                                     FStarC_Reflection_V2_Data.C_Unit)),
                                FStarC_Reflection_V2_Data.Q_Explicit))))))),
               FStarC_Reflection_V2_Data.Q_Explicit))) in
    let x8 = FStar_Tactics_V2_Derived.mk_abs x x7 ps in
    let x9 =
      let x10 = FStar_Tactics_V2_Derived.fresh_binder x2 ps in
      let x11 =
        let x12 =
          let x13 =
            let x14 =
              let x15 =
                FStar_Tactics_V2_SyntaxHelpers.mk_tot_arr x
                  (FStar_Tactics_NamedView.pack
                     (FStar_Tactics_NamedView.Tv_Arrow
                        (x10, (FStarC_Reflection_V2_Data.C_Total x1)))) ps in
              {
                FStar_Tactics_NamedView.lb_fv =
                  (FStarC_Reflection_V2_Builtins.pack_fv
                     (add_suffix "_up" nm));
                FStar_Tactics_NamedView.lb_us = [];
                FStar_Tactics_NamedView.lb_typ = x15;
                FStar_Tactics_NamedView.lb_def = x8
              } in
            [x14] in
          {
            FStar_Tactics_NamedView.isrec = false;
            FStar_Tactics_NamedView.lbs = x13
          } in
        FStar_Tactics_NamedView.Sg_Let x12 in
      FStar_Tactics_NamedView.pack_sigelt x11 ps in
    [x3; x6; x9]
let entry (nm : Prims.string) :
  (FStarC_Reflection_Types.decls, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = get_inductive_typ nm ps in
    match x with
    | FStar_Tactics_NamedView.Sg_Inductive
        { FStar_Tactics_NamedView.nm = nm1;
          FStar_Tactics_NamedView.univs1 = uu___;
          FStar_Tactics_NamedView.params = params;
          FStar_Tactics_NamedView.typ = uu___1;
          FStar_Tactics_NamedView.ctors = ctors;_}
        -> generate_all nm1 params ctors ps
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.TypeRepr.entry" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.TypeRepr.entry (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_1 entry)
               Fstarcompiler.FStarC_Syntax_Embeddings.e_string
               (Fstarcompiler.FStarC_Syntax_Embeddings.e_list
                  Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_sigelt) psc
               ncb us args)
