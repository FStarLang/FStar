open Fstarcompiler
open Prims
let namedv_view_to_string (x : FStarC_Reflection_V2_Data.namedv_view) :
  (Prims.string, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x1 =
      FStarC_Tactics_Unseal.unseal x.FStarC_Reflection_V2_Data.ppname ps in
    Prims.strcat x1
      (Prims.strcat "#"
         (Prims.string_of_int x.FStarC_Reflection_V2_Data.uniq))
let namedv_to_string (x : FStarC_Reflection_Types.namedv) :
  (Prims.string, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x1 = FStarC_Reflection_V2_Builtins.inspect_namedv x in
    namedv_view_to_string x1 ps
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.Print.namedv_to_string" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.Print.namedv_to_string (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_1
                  namedv_to_string)
               Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_namedv
               Fstarcompiler.FStarC_Syntax_Embeddings.e_string psc ncb us
               args)
let paren (s : Prims.string) : Prims.string=
  Prims.strcat "(" (Prims.strcat s ")")
let rec print_list_aux :
  'a .
    ('a -> (Prims.string, unit) FStar_Tactics_Effect.tac_repr) ->
      'a Prims.list -> (Prims.string, unit) FStar_Tactics_Effect.tac_repr
  =
  fun uu___1 uu___ ->
    (fun f xs ->
       match xs with
       | [] -> Obj.magic (Obj.repr (fun uu___ -> ""))
       | x::[] -> Obj.magic (Obj.repr (f x))
       | x::xs1 ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind (Obj.magic (f x))
                   (fun uu___ ->
                      (fun uu___ ->
                         Obj.magic
                           (fun ps ->
                              let x1 =
                                let x2 = print_list_aux f xs1 ps in
                                Prims.strcat "; " x2 in
                              Prims.strcat uu___ x1)) uu___)))) uu___1 uu___
let print_list (f : 'a -> (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  (l : 'a Prims.list) : (Prims.string, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = let x1 = print_list_aux f l ps in Prims.strcat x1 "]" in
    Prims.strcat "[" x
let rec universe_to_ast_string (u : FStar_Tactics_NamedView.universe) :
  (Prims.string, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = FStar_Tactics_NamedView.inspect_universe u ps in
    match x with
    | FStar_Tactics_NamedView.Uv_Zero -> "Uv_Zero"
    | FStar_Tactics_NamedView.Uv_Succ u1 ->
        let x1 = let x2 = universe_to_ast_string u1 ps in paren x2 in
        Prims.strcat "Uv_Succ" x1
    | FStar_Tactics_NamedView.Uv_Max us ->
        let x1 = print_list universe_to_ast_string us ps in
        Prims.strcat "Uv_Max" x1
    | FStar_Tactics_NamedView.Uv_BVar n ->
        Prims.strcat "Uv_BVar" (paren (Prims.string_of_int n))
    | FStar_Tactics_NamedView.Uv_Name i ->
        Prims.strcat "Uv_Name" (paren (FStar_Pervasives_Native.fst i))
    | FStar_Tactics_NamedView.Uv_Unif uu___ -> "Uv_Unif"
    | FStar_Tactics_NamedView.Uv_Unk -> "Uv_Unk"
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.Print.universe_to_ast_string" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.Print.universe_to_ast_string (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_1
                  universe_to_ast_string)
               Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_universe
               Fstarcompiler.FStarC_Syntax_Embeddings.e_string psc ncb us
               args)
let universes_to_ast_string (us : FStarC_Reflection_V2_Data.universes) :
  (Prims.string, unit) FStar_Tactics_Effect.tac_repr=
  print_list universe_to_ast_string us
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.Print.universes_to_ast_string" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.Print.universes_to_ast_string (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_1
                  universes_to_ast_string)
               (Fstarcompiler.FStarC_Syntax_Embeddings.e_list
                  Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_universe)
               Fstarcompiler.FStarC_Syntax_Embeddings.e_string psc ncb us
               args)
let rec term_to_ast_string (t : FStar_Tactics_NamedView.term) :
  (Prims.string, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = FStar_Tactics_NamedView.inspect t ps in
    match x with
    | FStar_Tactics_NamedView.Tv_Var bv ->
        let x1 = namedv_view_to_string bv ps in Prims.strcat "Tv_Var " x1
    | FStar_Tactics_NamedView.Tv_BVar bv ->
        let x1 = FStar_Tactics_V2_Derived.bv_to_string bv ps in
        Prims.strcat "Tv_BVar " x1
    | FStar_Tactics_NamedView.Tv_FVar fv ->
        Prims.strcat "Tv_FVar " (FStar_Reflection_V2_Derived.fv_to_string fv)
    | FStar_Tactics_NamedView.Tv_UInst (fv, us) ->
        let x1 =
          let x2 =
            let x3 =
              let x4 = universes_to_ast_string us ps in Prims.strcat ", " x4 in
            Prims.strcat (FStar_Reflection_V2_Derived.fv_to_string fv) x3 in
          paren x2 in
        Prims.strcat "Tv_UInst" x1
    | FStar_Tactics_NamedView.Tv_App (hd, (a, uu___)) ->
        let x1 =
          let x2 =
            let x3 = term_to_ast_string hd ps in
            let x4 = let x5 = term_to_ast_string a ps in Prims.strcat ", " x5 in
            Prims.strcat x3 x4 in
          paren x2 in
        Prims.strcat "Tv_App " x1
    | FStar_Tactics_NamedView.Tv_Abs (x1, e) ->
        let x2 =
          let x3 =
            let x4 = FStar_Tactics_V2_Derived.binder_to_string x1 ps in
            let x5 = let x6 = term_to_ast_string e ps in Prims.strcat ", " x6 in
            Prims.strcat x4 x5 in
          paren x3 in
        Prims.strcat "Tv_Abs " x2
    | FStar_Tactics_NamedView.Tv_Arrow (x1, c) ->
        let x2 =
          let x3 =
            let x4 = FStar_Tactics_V2_Derived.binder_to_string x1 ps in
            let x5 = let x6 = comp_to_ast_string c ps in Prims.strcat ", " x6 in
            Prims.strcat x4 x5 in
          paren x3 in
        Prims.strcat "Tv_Arrow " x2
    | FStar_Tactics_NamedView.Tv_Type u ->
        let x1 = let x2 = universe_to_ast_string u ps in paren x2 in
        Prims.strcat "Type" x1
    | FStar_Tactics_NamedView.Tv_Refine (x1, e) ->
        let x2 =
          let x3 =
            let x4 = FStar_Tactics_V2_Derived.binder_to_string x1 ps in
            let x5 = let x6 = term_to_ast_string e ps in Prims.strcat ", " x6 in
            Prims.strcat x4 x5 in
          paren x3 in
        Prims.strcat "Tv_Refine " x2
    | FStar_Tactics_NamedView.Tv_Const c -> const_to_ast_string c ps
    | FStar_Tactics_NamedView.Tv_Uvar (i, uu___) ->
        Prims.strcat "Tv_Uvar " (Prims.string_of_int i)
    | FStar_Tactics_NamedView.Tv_Let (recf, uu___, x1, e1, e2) ->
        let x2 =
          let x3 =
            let x4 =
              let x5 =
                let x6 = FStar_Tactics_V2_Derived.binder_to_string x1 ps in
                let x7 =
                  let x8 =
                    let x9 = term_to_ast_string e1 ps in
                    let x10 =
                      let x11 = term_to_ast_string e2 ps in
                      Prims.strcat ", " x11 in
                    Prims.strcat x9 x10 in
                  Prims.strcat ", " x8 in
                Prims.strcat x6 x7 in
              Prims.strcat ", " x5 in
            Prims.strcat (Prims.string_of_bool recf) x4 in
          paren x3 in
        Prims.strcat "Tv_Let " x2
    | FStar_Tactics_NamedView.Tv_Match (e, ret_opt, brs) ->
        let x1 =
          let x2 =
            let x3 = term_to_ast_string e ps in
            let x4 =
              let x5 =
                let x6 = match_returns_to_string ret_opt ps in
                let x7 =
                  let x8 = branches_to_ast_string brs ps in
                  Prims.strcat ", " x8 in
                Prims.strcat x6 x7 in
              Prims.strcat ", " x5 in
            Prims.strcat x3 x4 in
          paren x2 in
        Prims.strcat "Tv_Match " x1
    | FStar_Tactics_NamedView.Tv_AscribedT (e, t1, uu___, use_eq) ->
        let x1 =
          let x2 =
            let x3 = term_to_ast_string e ps in
            let x4 =
              let x5 =
                let x6 = term_to_ast_string t1 ps in
                Prims.strcat x6
                  (Prims.strcat ", " (Prims.string_of_bool use_eq)) in
              Prims.strcat ", " x5 in
            Prims.strcat x3 x4 in
          paren x2 in
        Prims.strcat "Tv_AscribedT " x1
    | FStar_Tactics_NamedView.Tv_AscribedC (e, c, uu___, use_eq) ->
        let x1 =
          let x2 =
            let x3 = term_to_ast_string e ps in
            let x4 =
              let x5 =
                let x6 = comp_to_ast_string c ps in
                Prims.strcat x6
                  (Prims.strcat ", " (Prims.string_of_bool use_eq)) in
              Prims.strcat ", " x5 in
            Prims.strcat x3 x4 in
          paren x2 in
        Prims.strcat "Tv_AscribedC " x1
    | FStar_Tactics_NamedView.Tv_Unknown -> "_"
    | FStar_Tactics_NamedView.Tv_Unsupp -> "<Tv_Unsupp>"
and match_returns_to_string
  (ret_opt :
    FStar_Tactics_NamedView.match_returns_ascription
      FStar_Pervasives_Native.option)
  : (Prims.string, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x uu___ =
      (fun tacopt ->
         match tacopt with
         | FStar_Pervasives_Native.None ->
             Obj.magic (Obj.repr (fun uu___ -> ""))
         | FStar_Pervasives_Native.Some tac ->
             Obj.magic
               (Obj.repr
                  (FStar_Tactics_Effect.tac_bind
                     (Obj.magic (term_to_ast_string tac))
                     (fun uu___ uu___1 -> Prims.strcat " by " uu___)))) uu___ in
    match ret_opt with
    | FStar_Pervasives_Native.None -> ""
    | FStar_Pervasives_Native.Some (b, asc) ->
        let x1 =
          let x2 = FStar_Tactics_V2_Derived.binder_to_string b ps in
          Prims.strcat x2 " " in
        let x2 =
          match asc with
          | (Fstarcompiler.FStar_Pervasives.Inl t, tacopt, uu___) ->
              let x3 = term_to_ast_string t ps in
              let x4 = x tacopt ps in Prims.strcat x3 x4
          | (Fstarcompiler.FStar_Pervasives.Inr c, tacopt, uu___) ->
              let x3 = comp_to_ast_string c ps in
              let x4 = x tacopt ps in Prims.strcat x3 x4 in
        Prims.strcat x1 x2
and branches_to_ast_string (brs : FStar_Tactics_NamedView.branch Prims.list)
  : (Prims.string, unit) FStar_Tactics_Effect.tac_repr=
  print_list branch_to_ast_string brs
and branch_to_ast_string (b : FStar_Tactics_NamedView.branch) :
  (Prims.string, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = b in
    match x with
    | (p, e) ->
        let x1 = let x2 = term_to_ast_string e ps in Prims.strcat "_pat, " x2 in
        paren x1
and comp_to_ast_string (c : FStar_Tactics_NamedView.comp) :
  (Prims.string, unit) FStar_Tactics_Effect.tac_repr=
  match FStar_Tactics_NamedView.inspect_comp c with
  | FStarC_Reflection_V2_Data.C_Total t ->
      FStar_Tactics_Effect.tac_bind (Obj.magic (term_to_ast_string t))
        (fun uu___ uu___1 -> Prims.strcat "Tot " uu___)
  | FStarC_Reflection_V2_Data.C_GTotal t ->
      FStar_Tactics_Effect.tac_bind (Obj.magic (term_to_ast_string t))
        (fun uu___ uu___1 -> Prims.strcat "GTot " uu___)
  | FStarC_Reflection_V2_Data.C_Lemma (pre, post, uu___) ->
      FStar_Tactics_Effect.tac_bind
        (Obj.magic
           (FStar_Tactics_Effect.tac_bind
              (Obj.magic (term_to_ast_string pre))
              (fun uu___1 ->
                 (fun uu___1 ->
                    Obj.magic
                      (fun ps ->
                         let x =
                           let x1 = term_to_ast_string post ps in
                           Prims.strcat " " x1 in
                         Prims.strcat uu___1 x)) uu___1)))
        (fun uu___1 uu___2 -> Prims.strcat "Lemma " uu___1)
  | FStarC_Reflection_V2_Data.C_Eff (us, eff, res, uu___, uu___1) ->
      FStar_Tactics_Effect.tac_bind
        (Obj.magic
           (FStar_Tactics_Effect.tac_bind
              (Obj.magic
                 (FStar_Tactics_Effect.tac_bind
                    (Obj.magic (universes_to_ast_string us))
                    (fun uu___2 ->
                       (fun uu___2 ->
                          Obj.magic
                            (fun ps ->
                               let x =
                                 let x1 =
                                   let x2 =
                                     let x3 =
                                       let x4 = term_to_ast_string res ps in
                                       Prims.strcat ", " x4 in
                                     Prims.strcat
                                       (FStarC_Reflection_V2_Builtins.implode_qn
                                          eff) x3 in
                                   paren x2 in
                                 Prims.strcat "> " x1 in
                               Prims.strcat uu___2 x)) uu___2)))
              (fun uu___2 uu___3 -> Prims.strcat "<" uu___2)))
        (fun uu___2 uu___3 -> Prims.strcat "Effect" uu___2)
and const_to_ast_string (uu___ : FStarC_Reflection_V2_Data.vconst) :
  (Prims.string, unit) FStar_Tactics_Effect.tac_repr=
  (fun c ->
     Obj.magic
       (fun uu___ ->
          match c with
          | FStarC_Reflection_V2_Data.C_Unit -> "C_Unit"
          | FStarC_Reflection_V2_Data.C_Int i ->
              Prims.strcat "C_Int " (Prims.string_of_int i)
          | FStarC_Reflection_V2_Data.C_True -> "C_True"
          | FStarC_Reflection_V2_Data.C_False -> "C_False"
          | FStarC_Reflection_V2_Data.C_String s ->
              Prims.strcat "C_String " s
          | FStarC_Reflection_V2_Data.C_Range uu___1 -> "C_Range _"
          | FStarC_Reflection_V2_Data.C_Reify -> "C_Reify"
          | FStarC_Reflection_V2_Data.C_Reflect name ->
              Prims.strcat "C_Reflect "
                (FStarC_Reflection_V2_Builtins.implode_qn name)
          | FStarC_Reflection_V2_Data.C_Real r ->
              Prims.strcat "C_Real \"" (Prims.strcat r "\"")
          | FStarC_Reflection_V2_Data.C_Char c1 ->
              Prims.strcat "C_Char '"
                (Prims.strcat (FStar_String.make Prims.int_one c1) "'")))
    uu___
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.Print.term_to_ast_string" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.Print.term_to_ast_string (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_1
                  term_to_ast_string)
               Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term
               Fstarcompiler.FStarC_Syntax_Embeddings.e_string psc ncb us
               args)
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.Print.match_returns_to_string" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.Print.match_returns_to_string (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_1
                  match_returns_to_string)
               (Fstarcompiler.FStarC_Syntax_Embeddings.e_option
                  (Fstarcompiler.FStarC_Syntax_Embeddings.e_tuple2
                     FStar_Tactics_NamedView.e_binder
                     (Fstarcompiler.FStarC_Syntax_Embeddings.e_tuple3
                        (Fstarcompiler.FStarC_Syntax_Embeddings.e_either
                           Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term
                           Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_comp_view)
                        (Fstarcompiler.FStarC_Syntax_Embeddings.e_option
                           Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term)
                        Fstarcompiler.FStarC_Syntax_Embeddings.e_bool)))
               Fstarcompiler.FStarC_Syntax_Embeddings.e_string psc ncb us
               args)
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.Print.branches_to_ast_string" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.Print.branches_to_ast_string (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_1
                  branches_to_ast_string)
               (Fstarcompiler.FStarC_Syntax_Embeddings.e_list
                  (Fstarcompiler.FStarC_Syntax_Embeddings.e_tuple2
                     FStar_Tactics_NamedView.e_pattern
                     Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term))
               Fstarcompiler.FStarC_Syntax_Embeddings.e_string psc ncb us
               args)
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.Print.branch_to_ast_string" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.Print.branch_to_ast_string (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_1
                  branch_to_ast_string)
               (Fstarcompiler.FStarC_Syntax_Embeddings.e_tuple2
                  FStar_Tactics_NamedView.e_pattern
                  Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term)
               Fstarcompiler.FStarC_Syntax_Embeddings.e_string psc ncb us
               args)
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.Print.comp_to_ast_string" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.Print.comp_to_ast_string (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_1
                  comp_to_ast_string)
               Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_comp_view
               Fstarcompiler.FStarC_Syntax_Embeddings.e_string psc ncb us
               args)
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.Print.const_to_ast_string" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.Print.const_to_ast_string (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_1
                  const_to_ast_string)
               Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_vconst
               Fstarcompiler.FStarC_Syntax_Embeddings.e_string psc ncb us
               args)
