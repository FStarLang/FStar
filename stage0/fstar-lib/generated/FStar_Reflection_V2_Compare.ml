open Prims
let (compare_name :
  FStarC_Reflection_Types.name ->
    FStarC_Reflection_Types.name -> FStar_Order.order)
  =
  fun n1 ->
    fun n2 ->
      FStar_Order.compare_list n1 n2
        (fun s1 ->
           fun s2 ->
             FStar_Order.order_from_int
               (FStarC_Reflection_V2_Builtins.compare_string s1 s2))
let _ =
  FStarC_Tactics_Native.register_plugin
    "FStar.Reflection.V2.Compare.compare_name" (Prims.of_int (2))
    (fun _psc ->
       fun cb ->
         fun us ->
           fun args ->
             FStarC_Syntax_Embeddings.debug_wrap
               "FStar.Reflection.V2.Compare.compare_name"
               (fun _ ->
                  (FStarC_Syntax_Embeddings.arrow_as_prim_step_2
                     (FStarC_Syntax_Embeddings.e_list
                        FStarC_Syntax_Embeddings.e_string)
                     (FStarC_Syntax_Embeddings.e_list
                        FStarC_Syntax_Embeddings.e_string)
                     FStar_Order.e_order compare_name
                     (FStarC_Ident.lid_of_str
                        "FStar.Reflection.V2.Compare.compare_name") cb us)
                    args))
    (fun cb ->
       fun us ->
         fun args ->
           FStarC_Syntax_Embeddings.debug_wrap
             "FStar.Reflection.V2.Compare.compare_name"
             (fun _ ->
                (FStarC_TypeChecker_NBETerm.arrow_as_prim_step_2
                   (FStarC_TypeChecker_NBETerm.e_list
                      FStarC_TypeChecker_NBETerm.e_string)
                   (FStarC_TypeChecker_NBETerm.e_list
                      FStarC_TypeChecker_NBETerm.e_string)
                   (FStarC_TypeChecker_NBETerm.e_unsupported ()) compare_name
                   (FStarC_Ident.lid_of_str
                      "FStar.Reflection.V2.Compare.compare_name") cb us) args))
let (compare_fv :
  FStarC_Reflection_Types.fv ->
    FStarC_Reflection_Types.fv -> FStar_Order.order)
  =
  fun f1 ->
    fun f2 ->
      compare_name (FStarC_Reflection_V2_Builtins.inspect_fv f1)
        (FStarC_Reflection_V2_Builtins.inspect_fv f2)
let _ =
  FStarC_Tactics_Native.register_plugin
    "FStar.Reflection.V2.Compare.compare_fv" (Prims.of_int (2))
    (fun _psc ->
       fun cb ->
         fun us ->
           fun args ->
             FStarC_Syntax_Embeddings.debug_wrap
               "FStar.Reflection.V2.Compare.compare_fv"
               (fun _ ->
                  (FStarC_Syntax_Embeddings.arrow_as_prim_step_2
                     FStarC_Reflection_V2_Embeddings.e_fv
                     FStarC_Reflection_V2_Embeddings.e_fv FStar_Order.e_order
                     compare_fv
                     (FStarC_Ident.lid_of_str
                        "FStar.Reflection.V2.Compare.compare_fv") cb us) args))
    (fun cb ->
       fun us ->
         fun args ->
           FStarC_Syntax_Embeddings.debug_wrap
             "FStar.Reflection.V2.Compare.compare_fv"
             (fun _ ->
                (FStarC_TypeChecker_NBETerm.arrow_as_prim_step_2
                   FStarC_Reflection_V2_NBEEmbeddings.e_fv
                   FStarC_Reflection_V2_NBEEmbeddings.e_fv
                   (FStarC_TypeChecker_NBETerm.e_unsupported ()) compare_fv
                   (FStarC_Ident.lid_of_str
                      "FStar.Reflection.V2.Compare.compare_fv") cb us) args))
let (compare_const :
  FStarC_Reflection_V2_Data.vconst ->
    FStarC_Reflection_V2_Data.vconst -> FStar_Order.order)
  =
  fun c1 ->
    fun c2 ->
      match (c1, c2) with
      | (FStarC_Reflection_V2_Data.C_Unit, FStarC_Reflection_V2_Data.C_Unit)
          -> FStar_Order.Eq
      | (FStarC_Reflection_V2_Data.C_Int i, FStarC_Reflection_V2_Data.C_Int
         j) -> FStar_Order.order_from_int (i - j)
      | (FStarC_Reflection_V2_Data.C_True, FStarC_Reflection_V2_Data.C_True)
          -> FStar_Order.Eq
      | (FStarC_Reflection_V2_Data.C_False,
         FStarC_Reflection_V2_Data.C_False) -> FStar_Order.Eq
      | (FStarC_Reflection_V2_Data.C_String s1,
         FStarC_Reflection_V2_Data.C_String s2) ->
          FStar_Order.order_from_int
            (FStarC_Reflection_V2_Builtins.compare_string s1 s2)
      | (FStarC_Reflection_V2_Data.C_Range r1,
         FStarC_Reflection_V2_Data.C_Range r2) -> FStar_Order.Eq
      | (FStarC_Reflection_V2_Data.C_Reify,
         FStarC_Reflection_V2_Data.C_Reify) -> FStar_Order.Eq
      | (FStarC_Reflection_V2_Data.C_Reflect l1,
         FStarC_Reflection_V2_Data.C_Reflect l2) -> compare_name l1 l2
      | (FStarC_Reflection_V2_Data.C_Real r1,
         FStarC_Reflection_V2_Data.C_Real r2) ->
          FStar_Order.order_from_int
            (FStarC_Reflection_V2_Builtins.compare_string r1 r2)
      | (FStarC_Reflection_V2_Data.C_Unit, uu___) -> FStar_Order.Lt
      | (uu___, FStarC_Reflection_V2_Data.C_Unit) -> FStar_Order.Gt
      | (FStarC_Reflection_V2_Data.C_Int uu___, uu___1) -> FStar_Order.Lt
      | (uu___, FStarC_Reflection_V2_Data.C_Int uu___1) -> FStar_Order.Gt
      | (FStarC_Reflection_V2_Data.C_True, uu___) -> FStar_Order.Lt
      | (uu___, FStarC_Reflection_V2_Data.C_True) -> FStar_Order.Gt
      | (FStarC_Reflection_V2_Data.C_False, uu___) -> FStar_Order.Lt
      | (uu___, FStarC_Reflection_V2_Data.C_False) -> FStar_Order.Gt
      | (FStarC_Reflection_V2_Data.C_String uu___, uu___1) -> FStar_Order.Lt
      | (uu___, FStarC_Reflection_V2_Data.C_String uu___1) -> FStar_Order.Gt
      | (FStarC_Reflection_V2_Data.C_Range uu___, uu___1) -> FStar_Order.Lt
      | (uu___, FStarC_Reflection_V2_Data.C_Range uu___1) -> FStar_Order.Gt
      | (FStarC_Reflection_V2_Data.C_Reify, uu___) -> FStar_Order.Lt
      | (uu___, FStarC_Reflection_V2_Data.C_Reify) -> FStar_Order.Gt
      | (FStarC_Reflection_V2_Data.C_Reflect uu___, uu___1) -> FStar_Order.Lt
      | (uu___, FStarC_Reflection_V2_Data.C_Reflect uu___1) -> FStar_Order.Gt
      | (FStarC_Reflection_V2_Data.C_Real uu___, uu___1) -> FStar_Order.Lt
      | (uu___, FStarC_Reflection_V2_Data.C_Real uu___1) -> FStar_Order.Gt
let _ =
  FStarC_Tactics_Native.register_plugin
    "FStar.Reflection.V2.Compare.compare_const" (Prims.of_int (2))
    (fun _psc ->
       fun cb ->
         fun us ->
           fun args ->
             FStarC_Syntax_Embeddings.debug_wrap
               "FStar.Reflection.V2.Compare.compare_const"
               (fun _ ->
                  (FStarC_Syntax_Embeddings.arrow_as_prim_step_2
                     FStarC_Reflection_V2_Embeddings.e_vconst
                     FStarC_Reflection_V2_Embeddings.e_vconst
                     FStar_Order.e_order compare_const
                     (FStarC_Ident.lid_of_str
                        "FStar.Reflection.V2.Compare.compare_const") cb us)
                    args))
    (fun cb ->
       fun us ->
         fun args ->
           FStarC_Syntax_Embeddings.debug_wrap
             "FStar.Reflection.V2.Compare.compare_const"
             (fun _ ->
                (FStarC_TypeChecker_NBETerm.arrow_as_prim_step_2
                   FStarC_Reflection_V2_NBEEmbeddings.e_vconst
                   FStarC_Reflection_V2_NBEEmbeddings.e_vconst
                   (FStarC_TypeChecker_NBETerm.e_unsupported ())
                   compare_const
                   (FStarC_Ident.lid_of_str
                      "FStar.Reflection.V2.Compare.compare_const") cb us)
                  args))
let (compare_ident :
  FStarC_Reflection_Types.ident ->
    FStarC_Reflection_Types.ident -> FStar_Order.order)
  =
  fun i1 ->
    fun i2 ->
      let uu___ = FStarC_Reflection_V2_Builtins.inspect_ident i1 in
      match uu___ with
      | (nm1, uu___1) ->
          let uu___2 = FStarC_Reflection_V2_Builtins.inspect_ident i2 in
          (match uu___2 with
           | (nm2, uu___3) ->
               FStar_Order.order_from_int
                 (FStarC_Reflection_V2_Builtins.compare_string nm1 nm2))
let _ =
  FStarC_Tactics_Native.register_plugin
    "FStar.Reflection.V2.Compare.compare_ident" (Prims.of_int (2))
    (fun _psc ->
       fun cb ->
         fun us ->
           fun args ->
             FStarC_Syntax_Embeddings.debug_wrap
               "FStar.Reflection.V2.Compare.compare_ident"
               (fun _ ->
                  (FStarC_Syntax_Embeddings.arrow_as_prim_step_2
                     FStarC_Reflection_V2_Embeddings.e_ident
                     FStarC_Reflection_V2_Embeddings.e_ident
                     FStar_Order.e_order compare_ident
                     (FStarC_Ident.lid_of_str
                        "FStar.Reflection.V2.Compare.compare_ident") cb us)
                    args))
    (fun cb ->
       fun us ->
         fun args ->
           FStarC_Syntax_Embeddings.debug_wrap
             "FStar.Reflection.V2.Compare.compare_ident"
             (fun _ ->
                (FStarC_TypeChecker_NBETerm.arrow_as_prim_step_2
                   FStarC_Reflection_V2_NBEEmbeddings.e_ident
                   FStarC_Reflection_V2_NBEEmbeddings.e_ident
                   (FStarC_TypeChecker_NBETerm.e_unsupported ())
                   compare_ident
                   (FStarC_Ident.lid_of_str
                      "FStar.Reflection.V2.Compare.compare_ident") cb us)
                  args))
let rec (compare_universe :
  FStarC_Reflection_Types.universe ->
    FStarC_Reflection_Types.universe -> FStar_Order.order)
  =
  fun u1 ->
    fun u2 ->
      match ((FStarC_Reflection_V2_Builtins.inspect_universe u1),
              (FStarC_Reflection_V2_Builtins.inspect_universe u2))
      with
      | (FStarC_Reflection_V2_Data.Uv_Zero,
         FStarC_Reflection_V2_Data.Uv_Zero) -> FStar_Order.Eq
      | (FStarC_Reflection_V2_Data.Uv_Succ u11,
         FStarC_Reflection_V2_Data.Uv_Succ u21) -> compare_universe u11 u21
      | (FStarC_Reflection_V2_Data.Uv_Max us1,
         FStarC_Reflection_V2_Data.Uv_Max us2) ->
          FStar_Order.compare_list us1 us2
            (fun x -> fun y -> compare_universe x y)
      | (FStarC_Reflection_V2_Data.Uv_BVar n1,
         FStarC_Reflection_V2_Data.Uv_BVar n2) ->
          FStar_Order.compare_int n1 n2
      | (FStarC_Reflection_V2_Data.Uv_Name i1,
         FStarC_Reflection_V2_Data.Uv_Name i2) -> compare_ident i1 i2
      | (FStarC_Reflection_V2_Data.Uv_Unif u11,
         FStarC_Reflection_V2_Data.Uv_Unif u21) -> FStar_Order.Eq
      | (FStarC_Reflection_V2_Data.Uv_Unk, FStarC_Reflection_V2_Data.Uv_Unk)
          -> FStar_Order.Eq
      | (FStarC_Reflection_V2_Data.Uv_Zero, uu___) -> FStar_Order.Lt
      | (uu___, FStarC_Reflection_V2_Data.Uv_Zero) -> FStar_Order.Gt
      | (FStarC_Reflection_V2_Data.Uv_Succ uu___, uu___1) -> FStar_Order.Lt
      | (uu___, FStarC_Reflection_V2_Data.Uv_Succ uu___1) -> FStar_Order.Gt
      | (FStarC_Reflection_V2_Data.Uv_Max uu___, uu___1) -> FStar_Order.Lt
      | (uu___, FStarC_Reflection_V2_Data.Uv_Max uu___1) -> FStar_Order.Gt
      | (FStarC_Reflection_V2_Data.Uv_BVar uu___, uu___1) -> FStar_Order.Lt
      | (uu___, FStarC_Reflection_V2_Data.Uv_BVar uu___1) -> FStar_Order.Gt
      | (FStarC_Reflection_V2_Data.Uv_Name uu___, uu___1) -> FStar_Order.Lt
      | (uu___, FStarC_Reflection_V2_Data.Uv_Name uu___1) -> FStar_Order.Gt
      | (FStarC_Reflection_V2_Data.Uv_Unif uu___, uu___1) -> FStar_Order.Lt
      | (uu___, FStarC_Reflection_V2_Data.Uv_Unif uu___1) -> FStar_Order.Gt
      | (FStarC_Reflection_V2_Data.Uv_Unk, uu___) -> FStar_Order.Lt
let _ =
  FStarC_Tactics_Native.register_plugin
    "FStar.Reflection.V2.Compare.compare_universe" (Prims.of_int (2))
    (fun _psc ->
       fun cb ->
         fun us ->
           fun args ->
             FStarC_Syntax_Embeddings.debug_wrap
               "FStar.Reflection.V2.Compare.compare_universe"
               (fun _ ->
                  (FStarC_Syntax_Embeddings.arrow_as_prim_step_2
                     FStarC_Reflection_V2_Embeddings.e_universe
                     FStarC_Reflection_V2_Embeddings.e_universe
                     FStar_Order.e_order compare_universe
                     (FStarC_Ident.lid_of_str
                        "FStar.Reflection.V2.Compare.compare_universe") cb us)
                    args))
    (fun cb ->
       fun us ->
         fun args ->
           FStarC_Syntax_Embeddings.debug_wrap
             "FStar.Reflection.V2.Compare.compare_universe"
             (fun _ ->
                (FStarC_TypeChecker_NBETerm.arrow_as_prim_step_2
                   FStarC_Reflection_V2_NBEEmbeddings.e_universe
                   FStarC_Reflection_V2_NBEEmbeddings.e_universe
                   (FStarC_TypeChecker_NBETerm.e_unsupported ())
                   compare_universe
                   (FStarC_Ident.lid_of_str
                      "FStar.Reflection.V2.Compare.compare_universe") cb us)
                  args))
let (compare_universes :
  FStarC_Reflection_V2_Data.universes ->
    FStarC_Reflection_V2_Data.universes -> FStar_Order.order)
  = fun us1 -> fun us2 -> FStar_Order.compare_list us1 us2 compare_universe
let _ =
  FStarC_Tactics_Native.register_plugin
    "FStar.Reflection.V2.Compare.compare_universes" (Prims.of_int (2))
    (fun _psc ->
       fun cb ->
         fun us ->
           fun args ->
             FStarC_Syntax_Embeddings.debug_wrap
               "FStar.Reflection.V2.Compare.compare_universes"
               (fun _ ->
                  (FStarC_Syntax_Embeddings.arrow_as_prim_step_2
                     (FStarC_Syntax_Embeddings.e_list
                        FStarC_Reflection_V2_Embeddings.e_universe)
                     (FStarC_Syntax_Embeddings.e_list
                        FStarC_Reflection_V2_Embeddings.e_universe)
                     FStar_Order.e_order compare_universes
                     (FStarC_Ident.lid_of_str
                        "FStar.Reflection.V2.Compare.compare_universes") cb
                     us) args))
    (fun cb ->
       fun us ->
         fun args ->
           FStarC_Syntax_Embeddings.debug_wrap
             "FStar.Reflection.V2.Compare.compare_universes"
             (fun _ ->
                (FStarC_TypeChecker_NBETerm.arrow_as_prim_step_2
                   (FStarC_TypeChecker_NBETerm.e_list
                      FStarC_Reflection_V2_NBEEmbeddings.e_universe)
                   (FStarC_TypeChecker_NBETerm.e_list
                      FStarC_Reflection_V2_NBEEmbeddings.e_universe)
                   (FStarC_TypeChecker_NBETerm.e_unsupported ())
                   compare_universes
                   (FStarC_Ident.lid_of_str
                      "FStar.Reflection.V2.Compare.compare_universes") cb us)
                  args))
let rec (__compare_term :
  FStarC_Reflection_Types.term ->
    FStarC_Reflection_Types.term -> FStar_Order.order)
  =
  fun s ->
    fun t ->
      match ((FStarC_Reflection_V2_Builtins.inspect_ln s),
              (FStarC_Reflection_V2_Builtins.inspect_ln t))
      with
      | (FStarC_Reflection_V2_Data.Tv_Var sv,
         FStarC_Reflection_V2_Data.Tv_Var tv) ->
          FStar_Reflection_V2_Derived.compare_namedv sv tv
      | (FStarC_Reflection_V2_Data.Tv_BVar sv,
         FStarC_Reflection_V2_Data.Tv_BVar tv) ->
          FStar_Reflection_V2_Derived.compare_bv sv tv
      | (FStarC_Reflection_V2_Data.Tv_FVar sv,
         FStarC_Reflection_V2_Data.Tv_FVar tv) -> compare_fv sv tv
      | (FStarC_Reflection_V2_Data.Tv_UInst (sv, sus),
         FStarC_Reflection_V2_Data.Tv_UInst (tv, tus)) ->
          FStar_Order.lex (compare_fv sv tv)
            (fun uu___ -> compare_universes sus tus)
      | (FStarC_Reflection_V2_Data.Tv_App (uu___, uu___1),
         FStarC_Reflection_V2_Data.Tv_App (uu___2, uu___3)) ->
          let uu___4 = FStar_Reflection_V2_Derived_Lemmas.collect_app_ref s in
          (match uu___4 with
           | (h1, aa1) ->
               let uu___5 =
                 FStar_Reflection_V2_Derived_Lemmas.collect_app_ref t in
               (match uu___5 with
                | (h2, aa2) ->
                    FStar_Order.lex (__compare_term h1 h2)
                      (fun uu___6 -> compare_argv_list () () aa1 aa2)))
      | (FStarC_Reflection_V2_Data.Tv_Abs (b1, e1),
         FStarC_Reflection_V2_Data.Tv_Abs (b2, e2)) ->
          FStar_Order.lex (__compare_binder b1 b2)
            (fun uu___ -> __compare_term e1 e2)
      | (FStarC_Reflection_V2_Data.Tv_Refine (b1, e1),
         FStarC_Reflection_V2_Data.Tv_Refine (b2, e2)) ->
          FStar_Order.lex (__compare_binder b1 b2)
            (fun uu___ -> __compare_term e1 e2)
      | (FStarC_Reflection_V2_Data.Tv_Arrow (b1, e1),
         FStarC_Reflection_V2_Data.Tv_Arrow (b2, e2)) ->
          FStar_Order.lex (__compare_binder b1 b2)
            (fun uu___ -> __compare_comp e1 e2)
      | (FStarC_Reflection_V2_Data.Tv_Type su,
         FStarC_Reflection_V2_Data.Tv_Type tu) -> compare_universe su tu
      | (FStarC_Reflection_V2_Data.Tv_Const c1,
         FStarC_Reflection_V2_Data.Tv_Const c2) -> compare_const c1 c2
      | (FStarC_Reflection_V2_Data.Tv_Uvar (u1, uu___),
         FStarC_Reflection_V2_Data.Tv_Uvar (u2, uu___1)) ->
          FStar_Order.compare_int u1 u2
      | (FStarC_Reflection_V2_Data.Tv_Let (_r1, _attrs1, b1, t1, t1'),
         FStarC_Reflection_V2_Data.Tv_Let (_r2, _attrs2, b2, t2, t2')) ->
          FStar_Order.lex (__compare_binder b1 b2)
            (fun uu___ ->
               FStar_Order.lex (__compare_term t1 t2)
                 (fun uu___1 -> __compare_term t1' t2'))
      | (FStarC_Reflection_V2_Data.Tv_Match (uu___, uu___1, uu___2),
         FStarC_Reflection_V2_Data.Tv_Match (uu___3, uu___4, uu___5)) ->
          FStar_Order.Eq
      | (FStarC_Reflection_V2_Data.Tv_AscribedT (e1, t1, tac1, uu___),
         FStarC_Reflection_V2_Data.Tv_AscribedT (e2, t2, tac2, uu___1)) ->
          FStar_Order.lex (__compare_term e1 e2)
            (fun uu___2 ->
               FStar_Order.lex (__compare_term t1 t2)
                 (fun uu___3 ->
                    match (tac1, tac2) with
                    | (FStar_Pervasives_Native.None,
                       FStar_Pervasives_Native.None) -> FStar_Order.Eq
                    | (FStar_Pervasives_Native.None, uu___4) ->
                        FStar_Order.Lt
                    | (uu___4, FStar_Pervasives_Native.None) ->
                        FStar_Order.Gt
                    | (FStar_Pervasives_Native.Some e11,
                       FStar_Pervasives_Native.Some e21) ->
                        __compare_term e11 e21))
      | (FStarC_Reflection_V2_Data.Tv_AscribedC (e1, c1, tac1, uu___),
         FStarC_Reflection_V2_Data.Tv_AscribedC (e2, c2, tac2, uu___1)) ->
          FStar_Order.lex (__compare_term e1 e2)
            (fun uu___2 ->
               FStar_Order.lex (__compare_comp c1 c2)
                 (fun uu___3 ->
                    match (tac1, tac2) with
                    | (FStar_Pervasives_Native.None,
                       FStar_Pervasives_Native.None) -> FStar_Order.Eq
                    | (FStar_Pervasives_Native.None, uu___4) ->
                        FStar_Order.Lt
                    | (uu___4, FStar_Pervasives_Native.None) ->
                        FStar_Order.Gt
                    | (FStar_Pervasives_Native.Some e11,
                       FStar_Pervasives_Native.Some e21) ->
                        __compare_term e11 e21))
      | (FStarC_Reflection_V2_Data.Tv_Unknown,
         FStarC_Reflection_V2_Data.Tv_Unknown) -> FStar_Order.Eq
      | (FStarC_Reflection_V2_Data.Tv_Unsupp,
         FStarC_Reflection_V2_Data.Tv_Unsupp) -> FStar_Order.Eq
      | (FStarC_Reflection_V2_Data.Tv_Var uu___, uu___1) -> FStar_Order.Lt
      | (uu___, FStarC_Reflection_V2_Data.Tv_Var uu___1) -> FStar_Order.Gt
      | (FStarC_Reflection_V2_Data.Tv_BVar uu___, uu___1) -> FStar_Order.Lt
      | (uu___, FStarC_Reflection_V2_Data.Tv_BVar uu___1) -> FStar_Order.Gt
      | (FStarC_Reflection_V2_Data.Tv_FVar uu___, uu___1) -> FStar_Order.Lt
      | (uu___, FStarC_Reflection_V2_Data.Tv_FVar uu___1) -> FStar_Order.Gt
      | (FStarC_Reflection_V2_Data.Tv_UInst (uu___, uu___1), uu___2) ->
          FStar_Order.Lt
      | (uu___, FStarC_Reflection_V2_Data.Tv_UInst (uu___1, uu___2)) ->
          FStar_Order.Gt
      | (FStarC_Reflection_V2_Data.Tv_App (uu___, uu___1), uu___2) ->
          FStar_Order.Lt
      | (uu___, FStarC_Reflection_V2_Data.Tv_App (uu___1, uu___2)) ->
          FStar_Order.Gt
      | (FStarC_Reflection_V2_Data.Tv_Abs (uu___, uu___1), uu___2) ->
          FStar_Order.Lt
      | (uu___, FStarC_Reflection_V2_Data.Tv_Abs (uu___1, uu___2)) ->
          FStar_Order.Gt
      | (FStarC_Reflection_V2_Data.Tv_Arrow (uu___, uu___1), uu___2) ->
          FStar_Order.Lt
      | (uu___, FStarC_Reflection_V2_Data.Tv_Arrow (uu___1, uu___2)) ->
          FStar_Order.Gt
      | (FStarC_Reflection_V2_Data.Tv_Type uu___, uu___1) -> FStar_Order.Lt
      | (uu___, FStarC_Reflection_V2_Data.Tv_Type uu___1) -> FStar_Order.Gt
      | (FStarC_Reflection_V2_Data.Tv_Refine (uu___, uu___1), uu___2) ->
          FStar_Order.Lt
      | (uu___, FStarC_Reflection_V2_Data.Tv_Refine (uu___1, uu___2)) ->
          FStar_Order.Gt
      | (FStarC_Reflection_V2_Data.Tv_Const uu___, uu___1) -> FStar_Order.Lt
      | (uu___, FStarC_Reflection_V2_Data.Tv_Const uu___1) -> FStar_Order.Gt
      | (FStarC_Reflection_V2_Data.Tv_Uvar (uu___, uu___1), uu___2) ->
          FStar_Order.Lt
      | (uu___, FStarC_Reflection_V2_Data.Tv_Uvar (uu___1, uu___2)) ->
          FStar_Order.Gt
      | (FStarC_Reflection_V2_Data.Tv_Let
         (uu___, uu___1, uu___2, uu___3, uu___4), uu___5) -> FStar_Order.Lt
      | (uu___, FStarC_Reflection_V2_Data.Tv_Let
         (uu___1, uu___2, uu___3, uu___4, uu___5)) -> FStar_Order.Gt
      | (FStarC_Reflection_V2_Data.Tv_Match (uu___, uu___1, uu___2), uu___3)
          -> FStar_Order.Lt
      | (uu___, FStarC_Reflection_V2_Data.Tv_Match (uu___1, uu___2, uu___3))
          -> FStar_Order.Gt
      | (FStarC_Reflection_V2_Data.Tv_AscribedT
         (uu___, uu___1, uu___2, uu___3), uu___4) -> FStar_Order.Lt
      | (uu___, FStarC_Reflection_V2_Data.Tv_AscribedT
         (uu___1, uu___2, uu___3, uu___4)) -> FStar_Order.Gt
      | (FStarC_Reflection_V2_Data.Tv_AscribedC
         (uu___, uu___1, uu___2, uu___3), uu___4) -> FStar_Order.Lt
      | (uu___, FStarC_Reflection_V2_Data.Tv_AscribedC
         (uu___1, uu___2, uu___3, uu___4)) -> FStar_Order.Gt
      | (FStarC_Reflection_V2_Data.Tv_Unknown, uu___) -> FStar_Order.Lt
      | (uu___, FStarC_Reflection_V2_Data.Tv_Unknown) -> FStar_Order.Gt
      | (FStarC_Reflection_V2_Data.Tv_Unsupp, uu___) -> FStar_Order.Lt
      | (uu___, FStarC_Reflection_V2_Data.Tv_Unsupp) -> FStar_Order.Gt
and (__compare_term_list :
  FStarC_Reflection_Types.term Prims.list ->
    FStarC_Reflection_Types.term Prims.list -> FStar_Order.order)
  =
  fun l1 ->
    fun l2 ->
      match (l1, l2) with
      | ([], []) -> FStar_Order.Eq
      | ([], uu___) -> FStar_Order.Lt
      | (uu___, []) -> FStar_Order.Gt
      | (hd1::tl1, hd2::tl2) ->
          FStar_Order.lex (__compare_term hd1 hd2)
            (fun uu___ -> __compare_term_list tl1 tl2)
and (compare_argv :
  unit ->
    unit ->
      FStarC_Reflection_V2_Data.argv ->
        FStarC_Reflection_V2_Data.argv -> FStar_Order.order)
  =
  fun b1 ->
    fun b2 ->
      fun a1 ->
        fun a2 ->
          let uu___ = a1 in
          match uu___ with
          | (t1, q1) ->
              let uu___1 = a2 in
              (match uu___1 with
               | (t2, q2) ->
                   (match (q1, q2) with
                    | (FStarC_Reflection_V2_Data.Q_Implicit,
                       FStarC_Reflection_V2_Data.Q_Explicit) ->
                        FStar_Order.Lt
                    | (FStarC_Reflection_V2_Data.Q_Explicit,
                       FStarC_Reflection_V2_Data.Q_Implicit) ->
                        FStar_Order.Gt
                    | (uu___2, uu___3) -> __compare_term t1 t2))
and (compare_argv_list :
  unit ->
    unit ->
      FStarC_Reflection_V2_Data.argv Prims.list ->
        FStarC_Reflection_V2_Data.argv Prims.list -> FStar_Order.order)
  =
  fun b1 ->
    fun b2 ->
      fun l1 ->
        fun l2 ->
          match (l1, l2) with
          | ([], []) -> FStar_Order.Eq
          | ([], uu___) -> FStar_Order.Lt
          | (uu___, []) -> FStar_Order.Gt
          | (hd1::tl1, hd2::tl2) ->
              FStar_Order.lex (compare_argv () () hd1 hd2)
                (fun uu___ -> compare_argv_list () () tl1 tl2)
and (__compare_comp :
  FStarC_Reflection_Types.comp ->
    FStarC_Reflection_Types.comp -> FStar_Order.order)
  =
  fun c1 ->
    fun c2 ->
      let cv1 = FStarC_Reflection_V2_Builtins.inspect_comp c1 in
      let cv2 = FStarC_Reflection_V2_Builtins.inspect_comp c2 in
      match (cv1, cv2) with
      | (FStarC_Reflection_V2_Data.C_Total t1,
         FStarC_Reflection_V2_Data.C_Total t2) -> __compare_term t1 t2
      | (FStarC_Reflection_V2_Data.C_GTotal t1,
         FStarC_Reflection_V2_Data.C_GTotal t2) -> __compare_term t1 t2
      | (FStarC_Reflection_V2_Data.C_Lemma (p1, q1, s1),
         FStarC_Reflection_V2_Data.C_Lemma (p2, q2, s2)) ->
          FStar_Order.lex (__compare_term p1 p2)
            (fun uu___ ->
               FStar_Order.lex (__compare_term q1 q2)
                 (fun uu___1 -> __compare_term s1 s2))
      | (FStarC_Reflection_V2_Data.C_Eff (us1, eff1, res1, args1, _decrs1),
         FStarC_Reflection_V2_Data.C_Eff (us2, eff2, res2, args2, _decrs2))
          ->
          FStar_Order.lex (compare_universes us1 us2)
            (fun uu___ ->
               FStar_Order.lex (compare_name eff1 eff2)
                 (fun uu___1 -> __compare_term res1 res2))
      | (FStarC_Reflection_V2_Data.C_Total uu___, uu___1) -> FStar_Order.Lt
      | (uu___, FStarC_Reflection_V2_Data.C_Total uu___1) -> FStar_Order.Gt
      | (FStarC_Reflection_V2_Data.C_GTotal uu___, uu___1) -> FStar_Order.Lt
      | (uu___, FStarC_Reflection_V2_Data.C_GTotal uu___1) -> FStar_Order.Gt
      | (FStarC_Reflection_V2_Data.C_Lemma (uu___, uu___1, uu___2), uu___3)
          -> FStar_Order.Lt
      | (uu___, FStarC_Reflection_V2_Data.C_Lemma (uu___1, uu___2, uu___3))
          -> FStar_Order.Gt
      | (FStarC_Reflection_V2_Data.C_Eff
         (uu___, uu___1, uu___2, uu___3, uu___4), uu___5) -> FStar_Order.Lt
      | (uu___, FStarC_Reflection_V2_Data.C_Eff
         (uu___1, uu___2, uu___3, uu___4, uu___5)) -> FStar_Order.Gt
and (__compare_binder :
  FStarC_Reflection_Types.binder ->
    FStarC_Reflection_Types.binder -> FStar_Order.order)
  =
  fun b1 ->
    fun b2 ->
      let bview1 = FStarC_Reflection_V2_Builtins.inspect_binder b1 in
      let bview2 = FStarC_Reflection_V2_Builtins.inspect_binder b2 in
      __compare_term bview1.FStarC_Reflection_V2_Data.sort2
        bview2.FStarC_Reflection_V2_Data.sort2
let (compare_term :
  FStarC_Reflection_Types.term ->
    FStarC_Reflection_Types.term -> FStar_Order.order)
  = __compare_term
let _ =
  FStarC_Tactics_Native.register_plugin
    "FStar.Reflection.V2.Compare.compare_term" (Prims.of_int (2))
    (fun _psc ->
       fun cb ->
         fun us ->
           fun args ->
             FStarC_Syntax_Embeddings.debug_wrap
               "FStar.Reflection.V2.Compare.compare_term"
               (fun _ ->
                  (FStarC_Syntax_Embeddings.arrow_as_prim_step_2
                     FStarC_Reflection_V2_Embeddings.e_term
                     FStarC_Reflection_V2_Embeddings.e_term
                     FStar_Order.e_order compare_term
                     (FStarC_Ident.lid_of_str
                        "FStar.Reflection.V2.Compare.compare_term") cb us)
                    args))
    (fun cb ->
       fun us ->
         fun args ->
           FStarC_Syntax_Embeddings.debug_wrap
             "FStar.Reflection.V2.Compare.compare_term"
             (fun _ ->
                (FStarC_TypeChecker_NBETerm.arrow_as_prim_step_2
                   FStarC_Reflection_V2_NBEEmbeddings.e_term
                   FStarC_Reflection_V2_NBEEmbeddings.e_term
                   (FStarC_TypeChecker_NBETerm.e_unsupported ()) compare_term
                   (FStarC_Ident.lid_of_str
                      "FStar.Reflection.V2.Compare.compare_term") cb us) args))
let (compare_comp :
  FStarC_Reflection_Types.comp ->
    FStarC_Reflection_Types.comp -> FStar_Order.order)
  = __compare_comp
let _ =
  FStarC_Tactics_Native.register_plugin
    "FStar.Reflection.V2.Compare.compare_comp" (Prims.of_int (2))
    (fun _psc ->
       fun cb ->
         fun us ->
           fun args ->
             FStarC_Syntax_Embeddings.debug_wrap
               "FStar.Reflection.V2.Compare.compare_comp"
               (fun _ ->
                  (FStarC_Syntax_Embeddings.arrow_as_prim_step_2
                     FStarC_Reflection_V2_Embeddings.e_comp
                     FStarC_Reflection_V2_Embeddings.e_comp
                     FStar_Order.e_order compare_comp
                     (FStarC_Ident.lid_of_str
                        "FStar.Reflection.V2.Compare.compare_comp") cb us)
                    args))
    (fun cb ->
       fun us ->
         fun args ->
           FStarC_Syntax_Embeddings.debug_wrap
             "FStar.Reflection.V2.Compare.compare_comp"
             (fun _ ->
                (FStarC_TypeChecker_NBETerm.arrow_as_prim_step_2
                   FStarC_Reflection_V2_NBEEmbeddings.e_comp
                   FStarC_Reflection_V2_NBEEmbeddings.e_comp
                   (FStarC_TypeChecker_NBETerm.e_unsupported ()) compare_comp
                   (FStarC_Ident.lid_of_str
                      "FStar.Reflection.V2.Compare.compare_comp") cb us) args))
let (compare_binder :
  FStarC_Reflection_Types.binder ->
    FStarC_Reflection_Types.binder -> FStar_Order.order)
  = __compare_binder
let _ =
  FStarC_Tactics_Native.register_plugin
    "FStar.Reflection.V2.Compare.compare_binder" (Prims.of_int (2))
    (fun _psc ->
       fun cb ->
         fun us ->
           fun args ->
             FStarC_Syntax_Embeddings.debug_wrap
               "FStar.Reflection.V2.Compare.compare_binder"
               (fun _ ->
                  (FStarC_Syntax_Embeddings.arrow_as_prim_step_2
                     FStarC_Reflection_V2_Embeddings.e_binder
                     FStarC_Reflection_V2_Embeddings.e_binder
                     FStar_Order.e_order compare_binder
                     (FStarC_Ident.lid_of_str
                        "FStar.Reflection.V2.Compare.compare_binder") cb us)
                    args))
    (fun cb ->
       fun us ->
         fun args ->
           FStarC_Syntax_Embeddings.debug_wrap
             "FStar.Reflection.V2.Compare.compare_binder"
             (fun _ ->
                (FStarC_TypeChecker_NBETerm.arrow_as_prim_step_2
                   FStarC_Reflection_V2_NBEEmbeddings.e_binder
                   FStarC_Reflection_V2_NBEEmbeddings.e_binder
                   (FStarC_TypeChecker_NBETerm.e_unsupported ())
                   compare_binder
                   (FStarC_Ident.lid_of_str
                      "FStar.Reflection.V2.Compare.compare_binder") cb us)
                  args))