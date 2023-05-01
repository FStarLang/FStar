open Prims
let (compare_name :
  FStar_Reflection_Types.name ->
    FStar_Reflection_Types.name -> FStar_Order.order)
  =
  fun n1 ->
    fun n2 ->
      FStar_Order.compare_list n1 n2
        (fun s1 ->
           fun s2 ->
             FStar_Order.order_from_int
               (FStar_Reflection_Builtins.compare_string s1 s2))
let (compare_fv :
  FStar_Reflection_Types.fv -> FStar_Reflection_Types.fv -> FStar_Order.order)
  =
  fun f1 ->
    fun f2 ->
      compare_name (FStar_Reflection_Builtins.inspect_fv f1)
        (FStar_Reflection_Builtins.inspect_fv f2)
let (compare_const :
  FStar_Reflection_Data.vconst ->
    FStar_Reflection_Data.vconst -> FStar_Order.order)
  =
  fun c1 ->
    fun c2 ->
      match (c1, c2) with
      | (FStar_Reflection_Data.C_Unit, FStar_Reflection_Data.C_Unit) ->
          FStar_Order.Eq
      | (FStar_Reflection_Data.C_Int i, FStar_Reflection_Data.C_Int j) ->
          FStar_Order.order_from_int (i - j)
      | (FStar_Reflection_Data.C_True, FStar_Reflection_Data.C_True) ->
          FStar_Order.Eq
      | (FStar_Reflection_Data.C_False, FStar_Reflection_Data.C_False) ->
          FStar_Order.Eq
      | (FStar_Reflection_Data.C_String s1, FStar_Reflection_Data.C_String
         s2) ->
          FStar_Order.order_from_int
            (FStar_Reflection_Builtins.compare_string s1 s2)
      | (FStar_Reflection_Data.C_Range r1, FStar_Reflection_Data.C_Range r2)
          -> FStar_Order.Eq
      | (FStar_Reflection_Data.C_Reify, FStar_Reflection_Data.C_Reify) ->
          FStar_Order.Eq
      | (FStar_Reflection_Data.C_Reflect l1, FStar_Reflection_Data.C_Reflect
         l2) -> compare_name l1 l2
      | (FStar_Reflection_Data.C_Unit, uu___) -> FStar_Order.Lt
      | (uu___, FStar_Reflection_Data.C_Unit) -> FStar_Order.Gt
      | (FStar_Reflection_Data.C_Int uu___, uu___1) -> FStar_Order.Lt
      | (uu___, FStar_Reflection_Data.C_Int uu___1) -> FStar_Order.Gt
      | (FStar_Reflection_Data.C_True, uu___) -> FStar_Order.Lt
      | (uu___, FStar_Reflection_Data.C_True) -> FStar_Order.Gt
      | (FStar_Reflection_Data.C_False, uu___) -> FStar_Order.Lt
      | (uu___, FStar_Reflection_Data.C_False) -> FStar_Order.Gt
      | (FStar_Reflection_Data.C_String uu___, uu___1) -> FStar_Order.Lt
      | (uu___, FStar_Reflection_Data.C_String uu___1) -> FStar_Order.Gt
      | (FStar_Reflection_Data.C_Range uu___, uu___1) -> FStar_Order.Lt
      | (uu___, FStar_Reflection_Data.C_Range uu___1) -> FStar_Order.Gt
      | (FStar_Reflection_Data.C_Reify, uu___) -> FStar_Order.Lt
      | (uu___, FStar_Reflection_Data.C_Reify) -> FStar_Order.Gt
      | (FStar_Reflection_Data.C_Reflect uu___, uu___1) -> FStar_Order.Lt
      | (uu___, FStar_Reflection_Data.C_Reflect uu___1) -> FStar_Order.Gt
let (compare_binder :
  FStar_Reflection_Types.binder ->
    FStar_Reflection_Types.binder -> FStar_Order.order)
  =
  fun b1 ->
    fun b2 ->
      let bview1 = FStar_Reflection_Builtins.inspect_binder b1 in
      let bview2 = FStar_Reflection_Builtins.inspect_binder b2 in
      FStar_Reflection_Builtins.compare_bv
        bview1.FStar_Reflection_Data.binder_bv
        bview2.FStar_Reflection_Data.binder_bv
let (compare_ident :
  FStar_Reflection_Types.ident ->
    FStar_Reflection_Types.ident -> FStar_Order.order)
  =
  fun i1 ->
    fun i2 ->
      FStar_Order.order_from_int
        (FStar_Reflection_Builtins.compare_string
           (FStar_Pervasives_Native.fst i1) (FStar_Pervasives_Native.fst i2))
let rec (compare_universe :
  FStar_Reflection_Types.universe ->
    FStar_Reflection_Types.universe -> FStar_Order.order)
  =
  fun u1 ->
    fun u2 ->
      match ((FStar_Reflection_Builtins.inspect_universe u1),
              (FStar_Reflection_Builtins.inspect_universe u2))
      with
      | (FStar_Reflection_Data.Uv_Zero, FStar_Reflection_Data.Uv_Zero) ->
          FStar_Order.Eq
      | (FStar_Reflection_Data.Uv_Succ u11, FStar_Reflection_Data.Uv_Succ
         u21) -> compare_universe u11 u21
      | (FStar_Reflection_Data.Uv_Max us1, FStar_Reflection_Data.Uv_Max us2)
          ->
          FStar_Order.compare_list us1 us2
            (fun x -> fun y -> compare_universe x y)
      | (FStar_Reflection_Data.Uv_BVar n1, FStar_Reflection_Data.Uv_BVar n2)
          -> FStar_Order.compare_int n1 n2
      | (FStar_Reflection_Data.Uv_Name i1, FStar_Reflection_Data.Uv_Name i2)
          -> compare_ident i1 i2
      | (FStar_Reflection_Data.Uv_Unif u11, FStar_Reflection_Data.Uv_Unif
         u21) -> FStar_Order.Eq
      | (FStar_Reflection_Data.Uv_Unk, FStar_Reflection_Data.Uv_Unk) ->
          FStar_Order.Eq
      | (FStar_Reflection_Data.Uv_Zero, uu___) -> FStar_Order.Lt
      | (uu___, FStar_Reflection_Data.Uv_Zero) -> FStar_Order.Gt
      | (FStar_Reflection_Data.Uv_Succ uu___, uu___1) -> FStar_Order.Lt
      | (uu___, FStar_Reflection_Data.Uv_Succ uu___1) -> FStar_Order.Gt
      | (FStar_Reflection_Data.Uv_Max uu___, uu___1) -> FStar_Order.Lt
      | (uu___, FStar_Reflection_Data.Uv_Max uu___1) -> FStar_Order.Gt
      | (FStar_Reflection_Data.Uv_BVar uu___, uu___1) -> FStar_Order.Lt
      | (uu___, FStar_Reflection_Data.Uv_BVar uu___1) -> FStar_Order.Gt
      | (FStar_Reflection_Data.Uv_Name uu___, uu___1) -> FStar_Order.Lt
      | (uu___, FStar_Reflection_Data.Uv_Name uu___1) -> FStar_Order.Gt
      | (FStar_Reflection_Data.Uv_Unif uu___, uu___1) -> FStar_Order.Lt
      | (uu___, FStar_Reflection_Data.Uv_Unif uu___1) -> FStar_Order.Gt
      | (FStar_Reflection_Data.Uv_Unk, uu___) -> FStar_Order.Lt
let (compare_universes :
  FStar_Reflection_Data.universes ->
    FStar_Reflection_Data.universes -> FStar_Order.order)
  = fun us1 -> fun us2 -> FStar_Order.compare_list us1 us2 compare_universe
let rec (compare_term :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term -> FStar_Order.order)
  =
  fun s ->
    fun t ->
      match ((FStar_Reflection_Builtins.inspect_ln s),
              (FStar_Reflection_Builtins.inspect_ln t))
      with
      | (FStar_Reflection_Data.Tv_Var sv, FStar_Reflection_Data.Tv_Var tv) ->
          FStar_Reflection_Builtins.compare_bv sv tv
      | (FStar_Reflection_Data.Tv_BVar sv, FStar_Reflection_Data.Tv_BVar tv)
          -> FStar_Reflection_Builtins.compare_bv sv tv
      | (FStar_Reflection_Data.Tv_FVar sv, FStar_Reflection_Data.Tv_FVar tv)
          -> compare_fv sv tv
      | (FStar_Reflection_Data.Tv_UInst (sv, sus),
         FStar_Reflection_Data.Tv_UInst (tv, tus)) ->
          FStar_Order.lex (compare_fv sv tv)
            (fun uu___ -> compare_universes sus tus)
      | (FStar_Reflection_Data.Tv_App (h1, a1), FStar_Reflection_Data.Tv_App
         (h2, a2)) ->
          FStar_Order.lex (compare_term h1 h2)
            (fun uu___ -> compare_argv a1 a2)
      | (FStar_Reflection_Data.Tv_Abs (b1, e1), FStar_Reflection_Data.Tv_Abs
         (b2, e2)) ->
          FStar_Order.lex (compare_binder b1 b2)
            (fun uu___ -> compare_term e1 e2)
      | (FStar_Reflection_Data.Tv_Refine (bv1, sort1, e1),
         FStar_Reflection_Data.Tv_Refine (bv2, sort2, e2)) ->
          FStar_Order.lex (FStar_Reflection_Builtins.compare_bv bv1 bv2)
            (fun uu___ ->
               FStar_Order.lex (compare_term sort1 sort2)
                 (fun uu___1 -> compare_term e1 e2))
      | (FStar_Reflection_Data.Tv_Arrow (b1, e1),
         FStar_Reflection_Data.Tv_Arrow (b2, e2)) ->
          FStar_Order.lex (compare_binder b1 b2)
            (fun uu___ -> compare_comp e1 e2)
      | (FStar_Reflection_Data.Tv_Type su, FStar_Reflection_Data.Tv_Type tu)
          -> compare_universe su tu
      | (FStar_Reflection_Data.Tv_Const c1, FStar_Reflection_Data.Tv_Const
         c2) -> compare_const c1 c2
      | (FStar_Reflection_Data.Tv_Uvar (u1, uu___),
         FStar_Reflection_Data.Tv_Uvar (u2, uu___1)) ->
          FStar_Order.compare_int u1 u2
      | (FStar_Reflection_Data.Tv_Let (_r1, _attrs1, bv1, ty1, t1, t1'),
         FStar_Reflection_Data.Tv_Let (_r2, _attrs2, bv2, ty2, t2, t2')) ->
          FStar_Order.lex (FStar_Reflection_Builtins.compare_bv bv1 bv2)
            (fun uu___ ->
               FStar_Order.lex (compare_term ty1 ty2)
                 (fun uu___1 ->
                    FStar_Order.lex (compare_term t1 t2)
                      (fun uu___2 -> compare_term t1' t2')))
      | (FStar_Reflection_Data.Tv_Match (uu___, uu___1, uu___2),
         FStar_Reflection_Data.Tv_Match (uu___3, uu___4, uu___5)) ->
          FStar_Order.Eq
      | (FStar_Reflection_Data.Tv_AscribedT (e1, t1, tac1, uu___),
         FStar_Reflection_Data.Tv_AscribedT (e2, t2, tac2, uu___1)) ->
          FStar_Order.lex (compare_term e1 e2)
            (fun uu___2 ->
               FStar_Order.lex (compare_term t1 t2)
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
                        compare_term e11 e21))
      | (FStar_Reflection_Data.Tv_AscribedC (e1, c1, tac1, uu___),
         FStar_Reflection_Data.Tv_AscribedC (e2, c2, tac2, uu___1)) ->
          FStar_Order.lex (compare_term e1 e2)
            (fun uu___2 ->
               FStar_Order.lex (compare_comp c1 c2)
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
                        compare_term e11 e21))
      | (FStar_Reflection_Data.Tv_Unknown, FStar_Reflection_Data.Tv_Unknown)
          -> FStar_Order.Eq
      | (FStar_Reflection_Data.Tv_Var uu___, uu___1) -> FStar_Order.Lt
      | (uu___, FStar_Reflection_Data.Tv_Var uu___1) -> FStar_Order.Gt
      | (FStar_Reflection_Data.Tv_BVar uu___, uu___1) -> FStar_Order.Lt
      | (uu___, FStar_Reflection_Data.Tv_BVar uu___1) -> FStar_Order.Gt
      | (FStar_Reflection_Data.Tv_FVar uu___, uu___1) -> FStar_Order.Lt
      | (uu___, FStar_Reflection_Data.Tv_FVar uu___1) -> FStar_Order.Gt
      | (FStar_Reflection_Data.Tv_UInst (uu___, uu___1), uu___2) ->
          FStar_Order.Lt
      | (uu___, FStar_Reflection_Data.Tv_UInst (uu___1, uu___2)) ->
          FStar_Order.Gt
      | (FStar_Reflection_Data.Tv_App (uu___, uu___1), uu___2) ->
          FStar_Order.Lt
      | (uu___, FStar_Reflection_Data.Tv_App (uu___1, uu___2)) ->
          FStar_Order.Gt
      | (FStar_Reflection_Data.Tv_Abs (uu___, uu___1), uu___2) ->
          FStar_Order.Lt
      | (uu___, FStar_Reflection_Data.Tv_Abs (uu___1, uu___2)) ->
          FStar_Order.Gt
      | (FStar_Reflection_Data.Tv_Arrow (uu___, uu___1), uu___2) ->
          FStar_Order.Lt
      | (uu___, FStar_Reflection_Data.Tv_Arrow (uu___1, uu___2)) ->
          FStar_Order.Gt
      | (FStar_Reflection_Data.Tv_Type uu___, uu___1) -> FStar_Order.Lt
      | (uu___, FStar_Reflection_Data.Tv_Type uu___1) -> FStar_Order.Gt
      | (FStar_Reflection_Data.Tv_Refine (uu___, uu___1, uu___2), uu___3) ->
          FStar_Order.Lt
      | (uu___, FStar_Reflection_Data.Tv_Refine (uu___1, uu___2, uu___3)) ->
          FStar_Order.Gt
      | (FStar_Reflection_Data.Tv_Const uu___, uu___1) -> FStar_Order.Lt
      | (uu___, FStar_Reflection_Data.Tv_Const uu___1) -> FStar_Order.Gt
      | (FStar_Reflection_Data.Tv_Uvar (uu___, uu___1), uu___2) ->
          FStar_Order.Lt
      | (uu___, FStar_Reflection_Data.Tv_Uvar (uu___1, uu___2)) ->
          FStar_Order.Gt
      | (FStar_Reflection_Data.Tv_Let
         (uu___, uu___1, uu___2, uu___3, uu___4, uu___5), uu___6) ->
          FStar_Order.Lt
      | (uu___, FStar_Reflection_Data.Tv_Let
         (uu___1, uu___2, uu___3, uu___4, uu___5, uu___6)) -> FStar_Order.Gt
      | (FStar_Reflection_Data.Tv_Match (uu___, uu___1, uu___2), uu___3) ->
          FStar_Order.Lt
      | (uu___, FStar_Reflection_Data.Tv_Match (uu___1, uu___2, uu___3)) ->
          FStar_Order.Gt
      | (FStar_Reflection_Data.Tv_AscribedT (uu___, uu___1, uu___2, uu___3),
         uu___4) -> FStar_Order.Lt
      | (uu___, FStar_Reflection_Data.Tv_AscribedT
         (uu___1, uu___2, uu___3, uu___4)) -> FStar_Order.Gt
      | (FStar_Reflection_Data.Tv_AscribedC (uu___, uu___1, uu___2, uu___3),
         uu___4) -> FStar_Order.Lt
      | (uu___, FStar_Reflection_Data.Tv_AscribedC
         (uu___1, uu___2, uu___3, uu___4)) -> FStar_Order.Gt
      | (FStar_Reflection_Data.Tv_Unknown, uu___) -> FStar_Order.Lt
      | (uu___, FStar_Reflection_Data.Tv_Unknown) -> FStar_Order.Gt
and (compare_term_list :
  FStar_Reflection_Types.term Prims.list ->
    FStar_Reflection_Types.term Prims.list -> FStar_Order.order)
  =
  fun l1 ->
    fun l2 ->
      match (l1, l2) with
      | ([], []) -> FStar_Order.Eq
      | ([], uu___) -> FStar_Order.Lt
      | (uu___, []) -> FStar_Order.Gt
      | (hd1::tl1, hd2::tl2) ->
          FStar_Order.lex (compare_term hd1 hd2)
            (fun uu___ -> compare_term_list tl1 tl2)
and (compare_argv :
  FStar_Reflection_Data.argv ->
    FStar_Reflection_Data.argv -> FStar_Order.order)
  =
  fun a1 ->
    fun a2 ->
      let uu___ = a1 in
      match uu___ with
      | (a11, q1) ->
          let uu___1 = a2 in
          (match uu___1 with
           | (a21, q2) ->
               (match (q1, q2) with
                | (FStar_Reflection_Data.Q_Implicit,
                   FStar_Reflection_Data.Q_Explicit) -> FStar_Order.Lt
                | (FStar_Reflection_Data.Q_Explicit,
                   FStar_Reflection_Data.Q_Implicit) -> FStar_Order.Gt
                | (uu___2, uu___3) -> compare_term a11 a21))
and (compare_comp :
  FStar_Reflection_Types.comp ->
    FStar_Reflection_Types.comp -> FStar_Order.order)
  =
  fun c1 ->
    fun c2 ->
      let cv1 = FStar_Reflection_Builtins.inspect_comp c1 in
      let cv2 = FStar_Reflection_Builtins.inspect_comp c2 in
      match (cv1, cv2) with
      | (FStar_Reflection_Data.C_Total t1, FStar_Reflection_Data.C_Total t2)
          -> compare_term t1 t2
      | (FStar_Reflection_Data.C_GTotal t1, FStar_Reflection_Data.C_GTotal
         t2) -> compare_term t1 t2
      | (FStar_Reflection_Data.C_Lemma (p1, q1, s1),
         FStar_Reflection_Data.C_Lemma (p2, q2, s2)) ->
          FStar_Order.lex (compare_term p1 p2)
            (fun uu___ ->
               FStar_Order.lex (compare_term q1 q2)
                 (fun uu___1 -> compare_term s1 s2))
      | (FStar_Reflection_Data.C_Eff (us1, eff1, res1, args1, _decrs1),
         FStar_Reflection_Data.C_Eff (us2, eff2, res2, args2, _decrs2)) ->
          FStar_Order.lex (compare_universes us1 us2)
            (fun uu___ ->
               FStar_Order.lex (compare_name eff1 eff2)
                 (fun uu___1 -> compare_term res1 res2))
      | (FStar_Reflection_Data.C_Total uu___, uu___1) -> FStar_Order.Lt
      | (uu___, FStar_Reflection_Data.C_Total uu___1) -> FStar_Order.Gt
      | (FStar_Reflection_Data.C_GTotal uu___, uu___1) -> FStar_Order.Lt
      | (uu___, FStar_Reflection_Data.C_GTotal uu___1) -> FStar_Order.Gt
      | (FStar_Reflection_Data.C_Lemma (uu___, uu___1, uu___2), uu___3) ->
          FStar_Order.Lt
      | (uu___, FStar_Reflection_Data.C_Lemma (uu___1, uu___2, uu___3)) ->
          FStar_Order.Gt
      | (FStar_Reflection_Data.C_Eff (uu___, uu___1, uu___2, uu___3, uu___4),
         uu___5) -> FStar_Order.Lt
      | (uu___, FStar_Reflection_Data.C_Eff
         (uu___1, uu___2, uu___3, uu___4, uu___5)) -> FStar_Order.Gt
