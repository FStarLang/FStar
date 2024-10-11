open Prims
type ('a, 'pred, 'l) allP0 = Obj.t
type ('a, 'b, 'top, 'pred, 'l) allP = Obj.t
type ('a, 'pred, 'o) optP0 = Obj.t
type ('a, 'b, 'top, 'pred, 'o) optP = Obj.t
type 'u faithful_univ = Obj.t
type 'c faithful_const = unit
type 't faithful = Obj.t
type 'a faithful_arg = Obj.t
type 'q faithful_qual = Obj.t
type 'b faithful_binder = Obj.t
type 'b faithful_branch = Obj.t
type 'p faithful_pattern = Obj.t
type 'pb faithful_pattern_arg = Obj.t
type 'ats faithful_attrs = Obj.t
type 'c faithful_comp = Obj.t
type faithful_term = FStarC_Reflection_Types.term
type faithful_universe = FStarC_Reflection_Types.universe
type _cmpres =
  | Eq 
  | Neq 
  | Unknown 
let (uu___is_Eq : _cmpres -> Prims.bool) =
  fun projectee -> match projectee with | Eq -> true | uu___ -> false
let (uu___is_Neq : _cmpres -> Prims.bool) =
  fun projectee -> match projectee with | Neq -> true | uu___ -> false
let (uu___is_Unknown : _cmpres -> Prims.bool) =
  fun projectee -> match projectee with | Unknown -> true | uu___ -> false
type ('t, 'c, 'x, 'y) valid = Obj.t
type ('t, 'x, 'y) cmpres = _cmpres
type 't comparator_for = 't -> 't -> ('t, unit, unit) cmpres
let op_Amp_Amp_Amp :
  's 't .
    's ->
      's ->
        't ->
          't ->
            ('s, unit, unit) cmpres ->
              ('t, unit, unit) cmpres -> (('s * 't), unit, unit) cmpres
  =
  fun x ->
    fun y ->
      fun w ->
        fun z ->
          fun c1 ->
            fun c2 ->
              match (c1, c2) with
              | (Eq, Eq) -> Eq
              | (Neq, uu___) -> Neq
              | (uu___, Neq) -> Neq
              | uu___ -> Unknown
let (bv_cmp : FStarC_Reflection_Types.bv comparator_for) =
  fun x1 ->
    fun x2 ->
      let v1 = FStarC_Reflection_V2_Builtins.inspect_bv x1 in
      let v2 = FStarC_Reflection_V2_Builtins.inspect_bv x2 in
      if
        v1.FStarC_Reflection_V2_Data.index =
          v2.FStarC_Reflection_V2_Data.index
      then Eq
      else Neq
let (namedv_cmp : FStarC_Reflection_Types.namedv comparator_for) =
  fun x1 ->
    fun x2 ->
      let v1 = FStarC_Reflection_V2_Builtins.inspect_namedv x1 in
      let v2 = FStarC_Reflection_V2_Builtins.inspect_namedv x2 in
      if
        v1.FStarC_Reflection_V2_Data.uniq = v2.FStarC_Reflection_V2_Data.uniq
      then Eq
      else Neq
let (fv_cmp : FStarC_Reflection_Types.fv comparator_for) =
  fun f1 ->
    fun f2 ->
      let n1 = FStarC_Reflection_V2_Builtins.inspect_fv f1 in
      let n2 = FStarC_Reflection_V2_Builtins.inspect_fv f2 in
      if n1 = n2 then Eq else Neq
let opt_cmp :
  'a . 'a comparator_for -> 'a FStar_Pervasives_Native.option comparator_for
  =
  fun cmp ->
    fun o1 ->
      fun o2 ->
        match (o1, o2) with
        | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) -> Eq
        | (FStar_Pervasives_Native.Some x, FStar_Pervasives_Native.Some y) ->
            cmp x y
        | uu___ -> Neq
let either_cmp :
  'a 'b .
    'a comparator_for ->
      'b comparator_for -> ('a, 'b) FStar_Pervasives.either comparator_for
  =
  fun uu___1 ->
    fun uu___ ->
      (fun cmpa ->
         fun cmpb ->
           fun e1 ->
             fun e2 ->
               match (e1, e2) with
               | (FStar_Pervasives.Inl x, FStar_Pervasives.Inl y) ->
                   Obj.magic (Obj.repr (cmpa x y))
               | (FStar_Pervasives.Inr x, FStar_Pervasives.Inr y) ->
                   Obj.magic (Obj.repr (cmpb x y))
               | uu___ -> Obj.magic (Obj.repr Neq)) uu___1 uu___
let pair_cmp :
  'a 'b . 'a comparator_for -> 'b comparator_for -> ('a * 'b) comparator_for
  =
  fun cmpa ->
    fun cmpb ->
      fun uu___ ->
        fun uu___1 ->
          match (uu___, uu___1) with
          | ((a1, b1), (a2, b2)) ->
              op_Amp_Amp_Amp a1 a2 b1 b2 (cmpa a1 a2) (cmpb b1 b2)
let rec list_cmp : 'a . 'a comparator_for -> 'a Prims.list comparator_for =
  fun cmp ->
    fun l1 ->
      fun l2 ->
        match (l1, l2) with
        | ([], []) -> Eq
        | (x::xs, y::ys) ->
            op_Amp_Amp_Amp x y xs ys (cmp x y) (list_cmp cmp xs ys)
        | uu___ -> Neq
let rec list_dec_cmp :
  'a 'uuuuu .
    'uuuuu ->
      'uuuuu ->
        ('a -> 'a -> ('a, unit, unit) cmpres) ->
          'a Prims.list ->
            'a Prims.list -> ('a Prims.list, unit, unit) cmpres
  =
  fun top1 ->
    fun top2 ->
      fun cmp ->
        fun l1 ->
          fun l2 ->
            match (l1, l2) with
            | ([], []) -> Eq
            | (x::xs, y::ys) ->
                op_Amp_Amp_Amp x y xs ys (cmp x y)
                  (list_dec_cmp top1 top2 cmp xs ys)
            | uu___ -> Neq
let opt_dec_cmp :
  'a 'b .
    'b ->
      'b ->
        ('a -> 'a -> ('a, unit, unit) cmpres) ->
          'a FStar_Pervasives_Native.option ->
            'a FStar_Pervasives_Native.option ->
              ('a FStar_Pervasives_Native.option, unit, unit) cmpres
  =
  fun top1 ->
    fun top2 ->
      fun cmp ->
        fun o1 ->
          fun o2 ->
            match (o1, o2) with
            | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) ->
                Eq
            | (FStar_Pervasives_Native.Some x, FStar_Pervasives_Native.Some
               y) -> cmp x y
            | uu___ -> Neq
let either_dec_cmp :
  'a 'b 'c .
    'c ->
      'c ->
        ('a -> 'a -> ('a, unit, unit) cmpres) ->
          ('b -> 'b -> ('b, unit, unit) cmpres) ->
            ('a, 'b) FStar_Pervasives.either ->
              ('a, 'b) FStar_Pervasives.either ->
                (('a, 'b) FStar_Pervasives.either, unit, unit) cmpres
  =
  fun uu___5 ->
    fun uu___4 ->
      fun uu___3 ->
        fun uu___2 ->
          fun uu___1 ->
            fun uu___ ->
              (fun top1 ->
                 fun top2 ->
                   fun cmpa ->
                     fun cmpb ->
                       fun e1 ->
                         fun e2 ->
                           match (e1, e2) with
                           | (FStar_Pervasives.Inl x, FStar_Pervasives.Inl y)
                               -> Obj.magic (Obj.repr (cmpa x y))
                           | (FStar_Pervasives.Inr x, FStar_Pervasives.Inr y)
                               -> Obj.magic (Obj.repr (cmpb x y))
                           | uu___ -> Obj.magic (Obj.repr Neq)) uu___5 uu___4
                uu___3 uu___2 uu___1 uu___
let eq_cmp : 'uuuuu . 'uuuuu comparator_for =
  fun x -> fun y -> if x = y then Eq else Neq
let (range_cmp : FStar_Range.range comparator_for) = fun r1 -> fun r2 -> Eq
let (ident_cmp : FStarC_Reflection_Types.ident comparator_for) =
  fun i1 ->
    fun i2 ->
      let iv1 = FStarC_Reflection_V2_Builtins.inspect_ident i1 in
      let iv2 = FStarC_Reflection_V2_Builtins.inspect_ident i2 in
      Obj.magic
        (eq_cmp (FStar_Pervasives_Native.fst iv1)
           (FStar_Pervasives_Native.fst iv2))
let rec (univ_cmp : FStarC_Reflection_Types.universe comparator_for) =
  fun u1 ->
    fun u2 ->
      let uv1 = FStarC_Reflection_V2_Builtins.inspect_universe u1 in
      let uv2 = FStarC_Reflection_V2_Builtins.inspect_universe u2 in
      match (uv1, uv2) with
      | (FStarC_Reflection_V2_Data.Uv_Zero,
         FStarC_Reflection_V2_Data.Uv_Zero) -> Obj.magic (Obj.repr Eq)
      | (FStarC_Reflection_V2_Data.Uv_Succ u11,
         FStarC_Reflection_V2_Data.Uv_Succ u21) ->
          Obj.magic (Obj.repr (univ_cmp u11 u21))
      | (FStarC_Reflection_V2_Data.Uv_Max us1,
         FStarC_Reflection_V2_Data.Uv_Max us2) ->
          Obj.magic (Obj.repr (list_dec_cmp u1 u2 univ_cmp us1 us2))
      | (FStarC_Reflection_V2_Data.Uv_BVar v1,
         FStarC_Reflection_V2_Data.Uv_BVar v2) ->
          Obj.magic (Obj.repr (eq_cmp v1 v2))
      | (FStarC_Reflection_V2_Data.Uv_Name n1,
         FStarC_Reflection_V2_Data.Uv_Name n2) ->
          Obj.magic (Obj.repr (ident_cmp n1 n2))
      | (FStarC_Reflection_V2_Data.Uv_Unif u11,
         FStarC_Reflection_V2_Data.Uv_Unif u21) ->
          Obj.magic (Obj.repr Unknown)
      | (FStarC_Reflection_V2_Data.Uv_Unk, FStarC_Reflection_V2_Data.Uv_Unk)
          -> Obj.magic (Obj.repr Eq)
      | uu___ -> Obj.magic (Obj.repr Neq)
let (const_cmp : FStarC_Reflection_V2_Data.vconst comparator_for) =
  fun c1 ->
    fun c2 ->
      match (c1, c2) with
      | (FStarC_Reflection_V2_Data.C_Unit, FStarC_Reflection_V2_Data.C_Unit)
          -> Obj.magic (Obj.repr Eq)
      | (FStarC_Reflection_V2_Data.C_Int i1, FStarC_Reflection_V2_Data.C_Int
         i2) -> Obj.magic (Obj.repr (eq_cmp i1 i2))
      | (FStarC_Reflection_V2_Data.C_True, FStarC_Reflection_V2_Data.C_True)
          -> Obj.magic (Obj.repr Eq)
      | (FStarC_Reflection_V2_Data.C_False,
         FStarC_Reflection_V2_Data.C_False) -> Obj.magic (Obj.repr Eq)
      | (FStarC_Reflection_V2_Data.C_String s1,
         FStarC_Reflection_V2_Data.C_String s2) ->
          Obj.magic (Obj.repr (eq_cmp s1 s2))
      | (FStarC_Reflection_V2_Data.C_Range r1,
         FStarC_Reflection_V2_Data.C_Range r2) ->
          Obj.magic (Obj.repr (range_cmp r1 r2))
      | (FStarC_Reflection_V2_Data.C_Reify,
         FStarC_Reflection_V2_Data.C_Reify) -> Obj.magic (Obj.repr Eq)
      | (FStarC_Reflection_V2_Data.C_Reflect n1,
         FStarC_Reflection_V2_Data.C_Reflect n2) ->
          Obj.magic (Obj.repr (eq_cmp n1 n2))
      | (FStarC_Reflection_V2_Data.C_Real s1,
         FStarC_Reflection_V2_Data.C_Real s2) ->
          Obj.magic (Obj.repr (eq_cmp s1 s2))
      | uu___ -> Obj.magic (Obj.repr Neq)
let (ctxu_cmp : FStarC_Reflection_Types.ctx_uvar_and_subst comparator_for) =
  fun uu___ -> fun uu___1 -> Unknown
let rec (term_cmp : FStarC_Reflection_Types.term comparator_for) =
  fun t1 ->
    fun t2 ->
      let tv1 = FStarC_Reflection_V2_Builtins.inspect_ln t1 in
      let tv2 = FStarC_Reflection_V2_Builtins.inspect_ln t2 in
      match (tv1, tv2) with
      | (FStarC_Reflection_V2_Data.Tv_Unsupp, uu___) ->
          Obj.magic (Obj.repr Unknown)
      | (uu___, FStarC_Reflection_V2_Data.Tv_Unsupp) ->
          Obj.magic (Obj.repr Unknown)
      | (FStarC_Reflection_V2_Data.Tv_Var v1,
         FStarC_Reflection_V2_Data.Tv_Var v2) ->
          Obj.magic (Obj.repr (namedv_cmp v1 v2))
      | (FStarC_Reflection_V2_Data.Tv_BVar v1,
         FStarC_Reflection_V2_Data.Tv_BVar v2) ->
          Obj.magic (Obj.repr (bv_cmp v1 v2))
      | (FStarC_Reflection_V2_Data.Tv_FVar f1,
         FStarC_Reflection_V2_Data.Tv_FVar f2) ->
          Obj.magic (Obj.repr (fv_cmp f1 f2))
      | (FStarC_Reflection_V2_Data.Tv_UInst (f1, u1),
         FStarC_Reflection_V2_Data.Tv_UInst (f2, u2)) ->
          Obj.magic
            (Obj.repr
               (op_Amp_Amp_Amp f1 f2 u1 u2 (fv_cmp f1 f2)
                  (list_dec_cmp t1 t2 univ_cmp u1 u2)))
      | (FStarC_Reflection_V2_Data.Tv_App (h1, a1),
         FStarC_Reflection_V2_Data.Tv_App (h2, a2)) ->
          Obj.magic
            (Obj.repr
               (op_Amp_Amp_Amp h1 h2 a1 a2 (term_cmp h1 h2) (arg_cmp a1 a2)))
      | (FStarC_Reflection_V2_Data.Tv_Abs (b1, e1),
         FStarC_Reflection_V2_Data.Tv_Abs (b2, e2)) ->
          Obj.magic
            (Obj.repr
               (op_Amp_Amp_Amp b1 b2 e1 e2 (binder_cmp b1 b2)
                  (term_cmp e1 e2)))
      | (FStarC_Reflection_V2_Data.Tv_Arrow (b1, c1),
         FStarC_Reflection_V2_Data.Tv_Arrow (b2, c2)) ->
          Obj.magic
            (Obj.repr
               (op_Amp_Amp_Amp b1 b2 c1 c2 (binder_cmp b1 b2)
                  (comp_cmp c1 c2)))
      | (FStarC_Reflection_V2_Data.Tv_Type u1,
         FStarC_Reflection_V2_Data.Tv_Type u2) ->
          Obj.magic (Obj.repr (univ_cmp u1 u2))
      | (FStarC_Reflection_V2_Data.Tv_Refine (sb1, r1),
         FStarC_Reflection_V2_Data.Tv_Refine (sb2, r2)) ->
          Obj.magic
            (Obj.repr
               (op_Amp_Amp_Amp sb1 sb2 r1 r2 (binder_cmp sb1 sb2)
                  (term_cmp r1 r2)))
      | (FStarC_Reflection_V2_Data.Tv_Const c1,
         FStarC_Reflection_V2_Data.Tv_Const c2) ->
          Obj.magic (Obj.repr (const_cmp c1 c2))
      | (FStarC_Reflection_V2_Data.Tv_Uvar (n1, u1),
         FStarC_Reflection_V2_Data.Tv_Uvar (n2, u2)) ->
          Obj.magic
            (Obj.repr
               (op_Amp_Amp_Amp n1 n2 u1 u2 (eq_cmp n1 n2) (ctxu_cmp u1 u2)))
      | (FStarC_Reflection_V2_Data.Tv_Let (r1, attrs1, sb1, e1, b1),
         FStarC_Reflection_V2_Data.Tv_Let (r2, attrs2, sb2, e2, b2)) ->
          Obj.magic
            (Obj.repr
               (op_Amp_Amp_Amp (((r1, attrs1), sb1), e1)
                  (((r2, attrs2), sb2), e2) b1 b2
                  (op_Amp_Amp_Amp ((r1, attrs1), sb1) ((r2, attrs2), sb2) e1
                     e2
                     (op_Amp_Amp_Amp (r1, attrs1) (r2, attrs2) sb1 sb2
                        (op_Amp_Amp_Amp r1 r2 attrs1 attrs2 (eq_cmp r1 r2)
                           (list_dec_cmp t1 t2 term_cmp attrs1 attrs2))
                        (binder_cmp sb1 sb2)) (term_cmp e1 e2))
                  (term_cmp b1 b2)))
      | (FStarC_Reflection_V2_Data.Tv_Match (sc1, o1, brs1),
         FStarC_Reflection_V2_Data.Tv_Match (sc2, o2, brs2)) ->
          Obj.magic
            (Obj.repr
               (op_Amp_Amp_Amp (sc1, o1) (sc2, o2) brs1 brs2
                  (op_Amp_Amp_Amp sc1 sc2 o1 o2 (term_cmp sc1 sc2)
                     (opt_dec_cmp t1 t2 match_returns_ascription_cmp o1 o2))
                  (list_dec_cmp t1 t2 br_cmp brs1 brs2)))
      | (FStarC_Reflection_V2_Data.Tv_AscribedT (e1, ta1, tacopt1, eq1),
         FStarC_Reflection_V2_Data.Tv_AscribedT (e2, ta2, tacopt2, eq2)) ->
          Obj.magic
            (Obj.repr
               (op_Amp_Amp_Amp ((e1, ta1), tacopt1) ((e2, ta2), tacopt2) eq1
                  eq2
                  (op_Amp_Amp_Amp (e1, ta1) (e2, ta2) tacopt1 tacopt2
                     (op_Amp_Amp_Amp e1 e2 ta1 ta2 (term_cmp e1 e2)
                        (term_cmp ta1 ta2))
                     (opt_dec_cmp t1 t2 term_cmp tacopt1 tacopt2))
                  (eq_cmp eq1 eq2)))
      | (FStarC_Reflection_V2_Data.Tv_AscribedC (e1, c1, tacopt1, eq1),
         FStarC_Reflection_V2_Data.Tv_AscribedC (e2, c2, tacopt2, eq2)) ->
          Obj.magic
            (Obj.repr
               (op_Amp_Amp_Amp ((e1, c1), tacopt1) ((e2, c2), tacopt2) eq1
                  eq2
                  (op_Amp_Amp_Amp (e1, c1) (e2, c2) tacopt1 tacopt2
                     (op_Amp_Amp_Amp e1 e2 c1 c2 (term_cmp e1 e2)
                        (comp_cmp c1 c2))
                     (opt_dec_cmp t1 t2 term_cmp tacopt1 tacopt2))
                  (eq_cmp eq1 eq2)))
      | (FStarC_Reflection_V2_Data.Tv_Unknown,
         FStarC_Reflection_V2_Data.Tv_Unknown) -> Obj.magic (Obj.repr Eq)
      | uu___ -> Obj.magic (Obj.repr Neq)
and (arg_cmp : FStarC_Reflection_V2_Data.argv comparator_for) =
  fun uu___ ->
    fun uu___1 ->
      match (uu___, uu___1) with
      | ((a1, q1), (a2, q2)) ->
          op_Amp_Amp_Amp a1 a2 q1 q2 (term_cmp a1 a2) (aqual_cmp q1 q2)
and (aqual_cmp : FStarC_Reflection_V2_Data.aqualv comparator_for) =
  fun a1 ->
    fun a2 ->
      match (a1, a2) with
      | (FStarC_Reflection_V2_Data.Q_Implicit,
         FStarC_Reflection_V2_Data.Q_Implicit) -> Eq
      | (FStarC_Reflection_V2_Data.Q_Explicit,
         FStarC_Reflection_V2_Data.Q_Explicit) -> Eq
      | (FStarC_Reflection_V2_Data.Q_Equality,
         FStarC_Reflection_V2_Data.Q_Equality) -> Eq
      | (FStarC_Reflection_V2_Data.Q_Meta m1,
         FStarC_Reflection_V2_Data.Q_Meta m2) -> term_cmp m1 m2
      | uu___ -> Neq
and (match_returns_ascription_cmp :
  FStarC_Syntax_Syntax.match_returns_ascription comparator_for) =
  fun asc1 ->
    fun asc2 ->
      let uu___ = asc1 in
      match uu___ with
      | (b1, (tc1, tacopt1, eq1)) ->
          let uu___1 = asc2 in
          (match uu___1 with
           | (b2, (tc2, tacopt2, eq2)) ->
               Obj.magic
                 (op_Amp_Amp_Amp ((b1, tc1), tacopt1) ((b2, tc2), tacopt2)
                    eq1 eq2
                    (op_Amp_Amp_Amp (b1, tc1) (b2, tc2) tacopt1 tacopt2
                       (op_Amp_Amp_Amp b1 b2 tc1 tc2 (binder_cmp b1 b2)
                          (either_dec_cmp asc1 asc2 term_cmp comp_cmp tc1 tc2))
                       (opt_dec_cmp asc1 asc2 term_cmp tacopt1 tacopt2))
                    (eq_cmp eq1 eq2)))
and (binder_cmp : FStarC_Reflection_Types.binder comparator_for) =
  fun b1 ->
    fun b2 ->
      let bv1 = FStarC_Reflection_V2_Builtins.inspect_binder b1 in
      let bv2 = FStarC_Reflection_V2_Builtins.inspect_binder b2 in
      Obj.magic
        (op_Amp_Amp_Amp
           ((bv1.FStarC_Reflection_V2_Data.sort2),
             (bv1.FStarC_Reflection_V2_Data.qual))
           ((bv2.FStarC_Reflection_V2_Data.sort2),
             (bv2.FStarC_Reflection_V2_Data.qual))
           bv1.FStarC_Reflection_V2_Data.attrs
           bv2.FStarC_Reflection_V2_Data.attrs
           (op_Amp_Amp_Amp bv1.FStarC_Reflection_V2_Data.sort2
              bv2.FStarC_Reflection_V2_Data.sort2
              bv1.FStarC_Reflection_V2_Data.qual
              bv2.FStarC_Reflection_V2_Data.qual
              (term_cmp bv1.FStarC_Reflection_V2_Data.sort2
                 bv2.FStarC_Reflection_V2_Data.sort2)
              (aqual_cmp bv1.FStarC_Reflection_V2_Data.qual
                 bv2.FStarC_Reflection_V2_Data.qual))
           (list_dec_cmp b1 b2 term_cmp bv1.FStarC_Reflection_V2_Data.attrs
              bv2.FStarC_Reflection_V2_Data.attrs))
and (comp_cmp : FStarC_Reflection_Types.comp comparator_for) =
  fun c1 ->
    fun c2 ->
      let cv1 = FStarC_Reflection_V2_Builtins.inspect_comp c1 in
      let cv2 = FStarC_Reflection_V2_Builtins.inspect_comp c2 in
      match (cv1, cv2) with
      | (FStarC_Reflection_V2_Data.C_Total t1,
         FStarC_Reflection_V2_Data.C_Total t2) ->
          Obj.magic (Obj.repr (term_cmp t1 t2))
      | (FStarC_Reflection_V2_Data.C_GTotal t1,
         FStarC_Reflection_V2_Data.C_GTotal t2) ->
          Obj.magic (Obj.repr (term_cmp t1 t2))
      | (FStarC_Reflection_V2_Data.C_Lemma (pre1, post1, pat1),
         FStarC_Reflection_V2_Data.C_Lemma (pre2, post2, pat2)) ->
          Obj.magic
            (Obj.repr
               (op_Amp_Amp_Amp (pre1, post1) (pre2, post2) pat1 pat2
                  (op_Amp_Amp_Amp pre1 pre2 post1 post2 (term_cmp pre1 pre2)
                     (term_cmp post1 post2)) (term_cmp pat1 pat2)))
      | (FStarC_Reflection_V2_Data.C_Eff (us1, ef1, t1, args1, dec1),
         FStarC_Reflection_V2_Data.C_Eff (us2, ef2, t2, args2, dec2)) ->
          Obj.magic
            (Obj.repr
               (op_Amp_Amp_Amp (((us1, ef1), t1), args1)
                  (((us2, ef2), t2), args2) dec1 dec2
                  (op_Amp_Amp_Amp ((us1, ef1), t1) ((us2, ef2), t2) args1
                     args2
                     (op_Amp_Amp_Amp (us1, ef1) (us2, ef2) t1 t2
                        (op_Amp_Amp_Amp us1 us2 ef1 ef2
                           (list_dec_cmp c1 c2 univ_cmp us1 us2)
                           (eq_cmp ef1 ef2)) (term_cmp t1 t2))
                     (list_dec_cmp c1 c2 arg_cmp args1 args2))
                  (list_dec_cmp c1 c2 term_cmp dec1 dec2)))
      | uu___ -> Obj.magic (Obj.repr Neq)
and (br_cmp : FStarC_Reflection_V2_Data.branch comparator_for) =
  fun br1 ->
    fun br2 ->
      op_Amp_Amp_Amp (FStar_Pervasives_Native.fst br1)
        (FStar_Pervasives_Native.fst br2) (FStar_Pervasives_Native.snd br1)
        (FStar_Pervasives_Native.snd br2)
        (pat_cmp (FStar_Pervasives_Native.fst br1)
           (FStar_Pervasives_Native.fst br2))
        (term_cmp (FStar_Pervasives_Native.snd br1)
           (FStar_Pervasives_Native.snd br2))
and (pat_cmp : FStarC_Reflection_V2_Data.pattern comparator_for) =
  fun p1 ->
    fun p2 ->
      match (p1, p2) with
      | (FStarC_Reflection_V2_Data.Pat_Var (x1, s1),
         FStarC_Reflection_V2_Data.Pat_Var (x2, s2)) ->
          Obj.magic (Obj.repr Eq)
      | (FStarC_Reflection_V2_Data.Pat_Constant x1,
         FStarC_Reflection_V2_Data.Pat_Constant x2) ->
          Obj.magic (Obj.repr (const_cmp x1 x2))
      | (FStarC_Reflection_V2_Data.Pat_Dot_Term x1,
         FStarC_Reflection_V2_Data.Pat_Dot_Term x2) ->
          Obj.magic (Obj.repr (opt_dec_cmp p1 p2 term_cmp x1 x2))
      | (FStarC_Reflection_V2_Data.Pat_Cons (head1, us1, subpats1),
         FStarC_Reflection_V2_Data.Pat_Cons (head2, us2, subpats2)) ->
          Obj.magic
            (Obj.repr
               (op_Amp_Amp_Amp (head1, us1) (head2, us2) subpats1 subpats2
                  (op_Amp_Amp_Amp head1 head2 us1 us2 (fv_cmp head1 head2)
                     (opt_dec_cmp p1 p2 (list_dec_cmp p1 p2 univ_cmp) us1 us2))
                  (list_dec_cmp p1 p2 pat_arg_cmp subpats1 subpats2)))
      | uu___ -> Obj.magic (Obj.repr Neq)
and (pat_arg_cmp :
  (FStarC_Reflection_V2_Data.pattern * Prims.bool) comparator_for) =
  fun uu___ ->
    fun uu___1 ->
      match (uu___, uu___1) with
      | ((p1, b1), (p2, b2)) ->
          op_Amp_Amp_Amp p1 p2 b1 b2 (pat_cmp p1 p2) (eq_cmp b1 b2)
type 'r defined = unit
type ('uuuuu, 'uuuuu1, 'f, 'l1, 'l2) def2 = unit
let (term_eq :
  FStarC_Reflection_Types.term -> FStarC_Reflection_Types.term -> Prims.bool)
  = fun t1 -> fun t2 -> uu___is_Eq (term_cmp t1 t2)
let _ =
  FStarC_Tactics_Native.register_plugin "FStar.Reflection.TermEq.term_eq"
    (Prims.of_int (2))
    (fun _psc ->
       fun cb ->
         fun us ->
           fun args ->
             FStarC_Syntax_Embeddings.debug_wrap
               "FStar.Reflection.TermEq.term_eq"
               (fun _ ->
                  (FStarC_Syntax_Embeddings.arrow_as_prim_step_2
                     FStarC_Reflection_V2_Embeddings.e_term
                     FStarC_Reflection_V2_Embeddings.e_term
                     FStarC_Syntax_Embeddings.e_bool term_eq
                     (FStarC_Ident.lid_of_str
                        "FStar.Reflection.TermEq.term_eq") cb us) args))
    (fun cb ->
       fun us ->
         fun args ->
           FStarC_Syntax_Embeddings.debug_wrap
             "FStar.Reflection.TermEq.term_eq"
             (fun _ ->
                (FStarC_TypeChecker_NBETerm.arrow_as_prim_step_2
                   FStarC_Reflection_V2_NBEEmbeddings.e_term
                   FStarC_Reflection_V2_NBEEmbeddings.e_term
                   FStarC_TypeChecker_NBETerm.e_bool term_eq
                   (FStarC_Ident.lid_of_str "FStar.Reflection.TermEq.term_eq")
                   cb us) args))
let (term_eq_dec : faithful_term -> faithful_term -> Prims.bool) =
  fun t1 -> fun t2 -> uu___is_Eq (term_cmp t1 t2)
let _ =
  FStarC_Tactics_Native.register_plugin "FStar.Reflection.TermEq.term_eq_dec"
    (Prims.of_int (2))
    (fun _psc ->
       fun cb ->
         fun us ->
           fun args ->
             FStarC_Syntax_Embeddings.debug_wrap
               "FStar.Reflection.TermEq.term_eq_dec"
               (fun _ ->
                  (FStarC_Syntax_Embeddings.arrow_as_prim_step_2
                     FStarC_Reflection_V2_Embeddings.e_term
                     FStarC_Reflection_V2_Embeddings.e_term
                     FStarC_Syntax_Embeddings.e_bool term_eq_dec
                     (FStarC_Ident.lid_of_str
                        "FStar.Reflection.TermEq.term_eq_dec") cb us) args))
    (fun cb ->
       fun us ->
         fun args ->
           FStarC_Syntax_Embeddings.debug_wrap
             "FStar.Reflection.TermEq.term_eq_dec"
             (fun _ ->
                (FStarC_TypeChecker_NBETerm.arrow_as_prim_step_2
                   FStarC_Reflection_V2_NBEEmbeddings.e_term
                   FStarC_Reflection_V2_NBEEmbeddings.e_term
                   FStarC_TypeChecker_NBETerm.e_bool term_eq_dec
                   (FStarC_Ident.lid_of_str
                      "FStar.Reflection.TermEq.term_eq_dec") cb us) args))
let (univ_eq :
  FStarC_Reflection_Types.universe ->
    FStarC_Reflection_Types.universe -> Prims.bool)
  = fun u1 -> fun u2 -> uu___is_Eq (univ_cmp u1 u2)
let _ =
  FStarC_Tactics_Native.register_plugin "FStar.Reflection.TermEq.univ_eq"
    (Prims.of_int (2))
    (fun _psc ->
       fun cb ->
         fun us ->
           fun args ->
             FStarC_Syntax_Embeddings.debug_wrap
               "FStar.Reflection.TermEq.univ_eq"
               (fun _ ->
                  (FStarC_Syntax_Embeddings.arrow_as_prim_step_2
                     FStarC_Reflection_V2_Embeddings.e_universe
                     FStarC_Reflection_V2_Embeddings.e_universe
                     FStarC_Syntax_Embeddings.e_bool univ_eq
                     (FStarC_Ident.lid_of_str
                        "FStar.Reflection.TermEq.univ_eq") cb us) args))
    (fun cb ->
       fun us ->
         fun args ->
           FStarC_Syntax_Embeddings.debug_wrap
             "FStar.Reflection.TermEq.univ_eq"
             (fun _ ->
                (FStarC_TypeChecker_NBETerm.arrow_as_prim_step_2
                   FStarC_Reflection_V2_NBEEmbeddings.e_universe
                   FStarC_Reflection_V2_NBEEmbeddings.e_universe
                   FStarC_TypeChecker_NBETerm.e_bool univ_eq
                   (FStarC_Ident.lid_of_str "FStar.Reflection.TermEq.univ_eq")
                   cb us) args))
let (univ_eq_dec : faithful_universe -> faithful_universe -> Prims.bool) =
  fun u1 -> fun u2 -> uu___is_Eq (univ_cmp u1 u2)
let _ =
  FStarC_Tactics_Native.register_plugin "FStar.Reflection.TermEq.univ_eq_dec"
    (Prims.of_int (2))
    (fun _psc ->
       fun cb ->
         fun us ->
           fun args ->
             FStarC_Syntax_Embeddings.debug_wrap
               "FStar.Reflection.TermEq.univ_eq_dec"
               (fun _ ->
                  (FStarC_Syntax_Embeddings.arrow_as_prim_step_2
                     FStarC_Reflection_V2_Embeddings.e_universe
                     FStarC_Reflection_V2_Embeddings.e_universe
                     FStarC_Syntax_Embeddings.e_bool univ_eq_dec
                     (FStarC_Ident.lid_of_str
                        "FStar.Reflection.TermEq.univ_eq_dec") cb us) args))
    (fun cb ->
       fun us ->
         fun args ->
           FStarC_Syntax_Embeddings.debug_wrap
             "FStar.Reflection.TermEq.univ_eq_dec"
             (fun _ ->
                (FStarC_TypeChecker_NBETerm.arrow_as_prim_step_2
                   FStarC_Reflection_V2_NBEEmbeddings.e_universe
                   FStarC_Reflection_V2_NBEEmbeddings.e_universe
                   FStarC_TypeChecker_NBETerm.e_bool univ_eq_dec
                   (FStarC_Ident.lid_of_str
                      "FStar.Reflection.TermEq.univ_eq_dec") cb us) args))