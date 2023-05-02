open Prims
type ('a, 'pred, 'l) allP0 = Obj.t
type ('a, 'b, 'top, 'pred, 'l) allP = Obj.t
type ('a, 'pred, 'o) optP0 = Obj.t
type ('a, 'b, 'top, 'pred, 'o) optP = Obj.t
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
let (bv_eq : FStar_Reflection_Types.bv comparator_for) =
  fun x1 ->
    fun x2 ->
      let v1 = FStar_Reflection_Builtins.inspect_bv x1 in
      let v2 = FStar_Reflection_Builtins.inspect_bv x2 in
      if
        v1.FStar_Reflection_Data.bv_index = v2.FStar_Reflection_Data.bv_index
      then Eq
      else Neq
let (fv_eq : FStar_Reflection_Types.fv comparator_for) =
  fun f1 ->
    fun f2 ->
      let n1 = FStar_Reflection_Builtins.inspect_fv f1 in
      let n2 = FStar_Reflection_Builtins.inspect_fv f2 in
      if n1 = n2 then Eq else Neq
let opt_eq :
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
let either_eq :
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
let pair_eq :
  'a 'b . 'a comparator_for -> 'b comparator_for -> ('a * 'b) comparator_for
  =
  fun cmpa ->
    fun cmpb ->
      fun uu___ ->
        fun uu___1 ->
          match (uu___, uu___1) with
          | ((a1, b1), (a2, b2)) ->
              op_Amp_Amp_Amp a1 a2 b1 b2 (cmpa a1 a2) (cmpb b1 b2)
let rec list_eq : 'a . 'a comparator_for -> 'a Prims.list comparator_for =
  fun cmp ->
    fun l1 ->
      fun l2 ->
        match (l1, l2) with
        | ([], []) -> Eq
        | (x::xs, y::ys) ->
            op_Amp_Amp_Amp x y xs ys (cmp x y) (list_eq cmp xs ys)
        | uu___ -> Neq
let rec list_dec_eq :
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
                  (list_dec_eq top1 top2 cmp xs ys)
            | uu___ -> Neq
let opt_dec_eq :
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
let either_dec_eq :
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
let eq_eq : 'uuuuu . 'uuuuu comparator_for =
  fun x -> fun y -> if x = y then Eq else Neq
let (range_eq : FStar_Range.range comparator_for) = fun r1 -> fun r2 -> Eq
let (ident_eq : FStar_Reflection_Types.ident comparator_for) =
  fun i1 ->
    fun i2 ->
      Obj.magic
        (eq_eq (FStar_Pervasives_Native.fst i1)
           (FStar_Pervasives_Native.fst i2))
let rec (univ_eq : FStar_Reflection_Types.universe comparator_for) =
  fun u1 ->
    fun u2 ->
      let uv1 = FStar_Reflection_Builtins.inspect_universe u1 in
      let uv2 = FStar_Reflection_Builtins.inspect_universe u2 in
      match (uv1, uv2) with
      | (FStar_Reflection_Data.Uv_Zero, FStar_Reflection_Data.Uv_Zero) ->
          Obj.magic (Obj.repr Eq)
      | (FStar_Reflection_Data.Uv_Succ u11, FStar_Reflection_Data.Uv_Succ
         u21) -> Obj.magic (Obj.repr (univ_eq u11 u21))
      | (FStar_Reflection_Data.Uv_Max us1, FStar_Reflection_Data.Uv_Max us2)
          -> Obj.magic (Obj.repr (list_dec_eq u1 u2 univ_eq us1 us2))
      | (FStar_Reflection_Data.Uv_BVar v1, FStar_Reflection_Data.Uv_BVar v2)
          -> Obj.magic (Obj.repr (eq_eq v1 v2))
      | (FStar_Reflection_Data.Uv_Name n1, FStar_Reflection_Data.Uv_Name n2)
          -> Obj.magic (Obj.repr (ident_eq n1 n2))
      | (FStar_Reflection_Data.Uv_Unif u11, FStar_Reflection_Data.Uv_Unif
         u21) -> Obj.magic (Obj.repr Unknown)
      | (FStar_Reflection_Data.Uv_Unk, FStar_Reflection_Data.Uv_Unk) ->
          Obj.magic (Obj.repr Eq)
      | uu___ -> Obj.magic (Obj.repr Neq)
let (const_eq : FStar_Reflection_Data.vconst comparator_for) =
  fun c1 ->
    fun c2 ->
      match (c1, c2) with
      | (FStar_Reflection_Data.C_Unit, FStar_Reflection_Data.C_Unit) ->
          Obj.magic (Obj.repr Eq)
      | (FStar_Reflection_Data.C_Int i1, FStar_Reflection_Data.C_Int i2) ->
          Obj.magic (Obj.repr (eq_eq i1 i2))
      | (FStar_Reflection_Data.C_True, FStar_Reflection_Data.C_True) ->
          Obj.magic (Obj.repr Eq)
      | (FStar_Reflection_Data.C_False, FStar_Reflection_Data.C_False) ->
          Obj.magic (Obj.repr Eq)
      | (FStar_Reflection_Data.C_String s1, FStar_Reflection_Data.C_String
         s2) -> Obj.magic (Obj.repr (eq_eq s1 s2))
      | (FStar_Reflection_Data.C_Range r1, FStar_Reflection_Data.C_Range r2)
          -> Obj.magic (Obj.repr (range_eq r1 r2))
      | (FStar_Reflection_Data.C_Reify, FStar_Reflection_Data.C_Reify) ->
          Obj.magic (Obj.repr Eq)
      | (FStar_Reflection_Data.C_Reflect n1, FStar_Reflection_Data.C_Reflect
         n2) -> Obj.magic (Obj.repr (eq_eq n1 n2))
      | uu___ -> Obj.magic (Obj.repr Neq)
let (ctxu_eq : FStar_Reflection_Types.ctx_uvar_and_subst comparator_for) =
  fun uu___ -> fun uu___1 -> Unknown
let rec (term_eq : FStar_Reflection_Types.term comparator_for) =
  fun t1 ->
    fun t2 ->
      let tv1 = FStar_Reflection_Builtins.inspect_ln t1 in
      let tv2 = FStar_Reflection_Builtins.inspect_ln t2 in
      match (tv1, tv2) with
      | (FStar_Reflection_Data.Tv_Unsupp, uu___) ->
          Obj.magic (Obj.repr Unknown)
      | (uu___, FStar_Reflection_Data.Tv_Unsupp) ->
          Obj.magic (Obj.repr Unknown)
      | (FStar_Reflection_Data.Tv_Var v1, FStar_Reflection_Data.Tv_Var v2) ->
          Obj.magic (Obj.repr (bv_eq v1 v2))
      | (FStar_Reflection_Data.Tv_BVar v1, FStar_Reflection_Data.Tv_BVar v2)
          -> Obj.magic (Obj.repr (bv_eq v1 v2))
      | (FStar_Reflection_Data.Tv_FVar f1, FStar_Reflection_Data.Tv_FVar f2)
          -> Obj.magic (Obj.repr (fv_eq f1 f2))
      | (FStar_Reflection_Data.Tv_UInst (f1, u1),
         FStar_Reflection_Data.Tv_UInst (f2, u2)) ->
          Obj.magic
            (Obj.repr
               (op_Amp_Amp_Amp f1 f2 u1 u2 (fv_eq f1 f2)
                  (list_dec_eq t1 t2 univ_eq u1 u2)))
      | (FStar_Reflection_Data.Tv_App (h1, a1), FStar_Reflection_Data.Tv_App
         (h2, a2)) ->
          Obj.magic
            (Obj.repr
               (op_Amp_Amp_Amp h1 h2 a1 a2 (term_eq h1 h2) (arg_eq a1 a2)))
      | (FStar_Reflection_Data.Tv_Abs (b1, e1), FStar_Reflection_Data.Tv_Abs
         (b2, e2)) ->
          Obj.magic
            (Obj.repr
               (op_Amp_Amp_Amp b1 b2 e1 e2 (binder_eq b1 b2) (term_eq e1 e2)))
      | (FStar_Reflection_Data.Tv_Arrow (b1, c1),
         FStar_Reflection_Data.Tv_Arrow (b2, c2)) ->
          Obj.magic
            (Obj.repr
               (op_Amp_Amp_Amp b1 b2 c1 c2 (binder_eq b1 b2) (comp_eq c1 c2)))
      | (FStar_Reflection_Data.Tv_Type u1, FStar_Reflection_Data.Tv_Type u2)
          -> Obj.magic (Obj.repr (univ_eq u1 u2))
      | (FStar_Reflection_Data.Tv_Refine (v1, sort1, r1),
         FStar_Reflection_Data.Tv_Refine (v2, sort2, r2)) ->
          Obj.magic
            (Obj.repr
               (op_Amp_Amp_Amp (v1, sort1) (v2, sort2) r1 r2
                  (op_Amp_Amp_Amp v1 v2 sort1 sort2 (binding_bv_eq v1 v2)
                     (term_eq sort1 sort2)) (term_eq r1 r2)))
      | (FStar_Reflection_Data.Tv_Const c1, FStar_Reflection_Data.Tv_Const
         c2) -> Obj.magic (Obj.repr (const_eq c1 c2))
      | (FStar_Reflection_Data.Tv_Uvar (n1, u1),
         FStar_Reflection_Data.Tv_Uvar (n2, u2)) ->
          Obj.magic
            (Obj.repr
               (op_Amp_Amp_Amp n1 n2 u1 u2 (eq_eq n1 n2) (ctxu_eq u1 u2)))
      | (FStar_Reflection_Data.Tv_Let (r1, attrs1, bv1, ty1, e1, b1),
         FStar_Reflection_Data.Tv_Let (r2, attrs2, bv2, ty2, e2, b2)) ->
          Obj.magic
            (Obj.repr
               (op_Amp_Amp_Amp ((((r1, attrs1), bv1), ty1), e1)
                  ((((r2, attrs2), bv2), ty2), e2) b1 b2
                  (op_Amp_Amp_Amp (((r1, attrs1), bv1), ty1)
                     (((r2, attrs2), bv2), ty2) e1 e2
                     (op_Amp_Amp_Amp ((r1, attrs1), bv1) ((r2, attrs2), bv2)
                        ty1 ty2
                        (op_Amp_Amp_Amp (r1, attrs1) (r2, attrs2) bv1 bv2
                           (op_Amp_Amp_Amp r1 r2 attrs1 attrs2 (eq_eq r1 r2)
                              (list_dec_eq t1 t2 term_eq attrs1 attrs2))
                           (binding_bv_eq bv1 bv2)) (term_eq ty1 ty2))
                     (term_eq e1 e2)) (term_eq b1 b2)))
      | (FStar_Reflection_Data.Tv_Match (sc1, o1, brs1),
         FStar_Reflection_Data.Tv_Match (sc2, o2, brs2)) ->
          Obj.magic
            (Obj.repr
               (op_Amp_Amp_Amp (sc1, o1) (sc2, o2) brs1 brs2
                  (op_Amp_Amp_Amp sc1 sc2 o1 o2 (term_eq sc1 sc2)
                     (opt_dec_eq t1 t2 match_returns_ascription_eq o1 o2))
                  (list_dec_eq t1 t2 br_eq brs1 brs2)))
      | (FStar_Reflection_Data.Tv_AscribedT (e1, ta1, tacopt1, eq1),
         FStar_Reflection_Data.Tv_AscribedT (e2, ta2, tacopt2, eq2)) ->
          Obj.magic
            (Obj.repr
               (op_Amp_Amp_Amp ((e1, ta1), tacopt1) ((e2, ta2), tacopt2) eq1
                  eq2
                  (op_Amp_Amp_Amp (e1, ta1) (e2, ta2) tacopt1 tacopt2
                     (op_Amp_Amp_Amp e1 e2 ta1 ta2 (term_eq e1 e2)
                        (term_eq ta1 ta2))
                     (opt_dec_eq t1 t2 term_eq tacopt1 tacopt2))
                  (eq_eq eq1 eq2)))
      | (FStar_Reflection_Data.Tv_AscribedC (e1, c1, tacopt1, eq1),
         FStar_Reflection_Data.Tv_AscribedC (e2, c2, tacopt2, eq2)) ->
          Obj.magic
            (Obj.repr
               (op_Amp_Amp_Amp ((e1, c1), tacopt1) ((e2, c2), tacopt2) eq1
                  eq2
                  (op_Amp_Amp_Amp (e1, c1) (e2, c2) tacopt1 tacopt2
                     (op_Amp_Amp_Amp e1 e2 c1 c2 (term_eq e1 e2)
                        (comp_eq c1 c2))
                     (opt_dec_eq t1 t2 term_eq tacopt1 tacopt2))
                  (eq_eq eq1 eq2)))
      | (FStar_Reflection_Data.Tv_Unknown, FStar_Reflection_Data.Tv_Unknown)
          -> Obj.magic (Obj.repr Eq)
      | uu___ -> Obj.magic (Obj.repr Neq)
and (arg_eq : FStar_Reflection_Data.argv comparator_for) =
  fun uu___ ->
    fun uu___1 ->
      match (uu___, uu___1) with
      | ((a1, q1), (a2, q2)) ->
          op_Amp_Amp_Amp a1 a2 q1 q2 (term_eq a1 a2) (aqual_eq q1 q2)
and (aqual_eq : FStar_Reflection_Data.aqualv comparator_for) =
  fun a1 ->
    fun a2 ->
      match (a1, a2) with
      | (FStar_Reflection_Data.Q_Implicit, FStar_Reflection_Data.Q_Implicit)
          -> Eq
      | (FStar_Reflection_Data.Q_Explicit, FStar_Reflection_Data.Q_Explicit)
          -> Eq
      | (FStar_Reflection_Data.Q_Meta m1, FStar_Reflection_Data.Q_Meta m2) ->
          term_eq m1 m2
      | uu___ -> Neq
and (binding_bv_eq : FStar_Reflection_Types.bv comparator_for) =
  fun x1 ->
    fun x2 ->
      let v1 = FStar_Reflection_Builtins.inspect_bv x1 in
      let v2 = FStar_Reflection_Builtins.inspect_bv x2 in
      if
        v1.FStar_Reflection_Data.bv_index = v2.FStar_Reflection_Data.bv_index
      then Eq
      else Neq
and (match_returns_ascription_eq :
  FStar_Reflection_Types.match_returns_ascription comparator_for) =
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
                       (op_Amp_Amp_Amp b1 b2 tc1 tc2 (binder_eq b1 b2)
                          (either_dec_eq asc1 asc2 term_eq comp_eq tc1 tc2))
                       (opt_dec_eq asc1 asc2 term_eq tacopt1 tacopt2))
                    (eq_eq eq1 eq2)))
and (binder_eq : FStar_Reflection_Types.binder comparator_for) =
  fun b1 ->
    fun b2 ->
      let bv1 = FStar_Reflection_Builtins.inspect_binder b1 in
      let bv2 = FStar_Reflection_Builtins.inspect_binder b2 in
      Obj.magic
        (op_Amp_Amp_Amp
           (((bv1.FStar_Reflection_Data.binder_bv),
              (bv1.FStar_Reflection_Data.binder_sort)),
             (bv1.FStar_Reflection_Data.binder_qual))
           (((bv2.FStar_Reflection_Data.binder_bv),
              (bv2.FStar_Reflection_Data.binder_sort)),
             (bv2.FStar_Reflection_Data.binder_qual))
           bv1.FStar_Reflection_Data.binder_attrs
           bv2.FStar_Reflection_Data.binder_attrs
           (op_Amp_Amp_Amp
              ((bv1.FStar_Reflection_Data.binder_bv),
                (bv1.FStar_Reflection_Data.binder_sort))
              ((bv2.FStar_Reflection_Data.binder_bv),
                (bv2.FStar_Reflection_Data.binder_sort))
              bv1.FStar_Reflection_Data.binder_qual
              bv2.FStar_Reflection_Data.binder_qual
              (op_Amp_Amp_Amp bv1.FStar_Reflection_Data.binder_bv
                 bv2.FStar_Reflection_Data.binder_bv
                 bv1.FStar_Reflection_Data.binder_sort
                 bv2.FStar_Reflection_Data.binder_sort
                 (binding_bv_eq bv1.FStar_Reflection_Data.binder_bv
                    bv2.FStar_Reflection_Data.binder_bv)
                 (term_eq bv1.FStar_Reflection_Data.binder_sort
                    bv2.FStar_Reflection_Data.binder_sort))
              (aqual_eq bv1.FStar_Reflection_Data.binder_qual
                 bv2.FStar_Reflection_Data.binder_qual))
           (list_dec_eq b1 b2 term_eq bv1.FStar_Reflection_Data.binder_attrs
              bv2.FStar_Reflection_Data.binder_attrs))
and (comp_eq : FStar_Reflection_Types.comp comparator_for) =
  fun c1 ->
    fun c2 ->
      let cv1 = FStar_Reflection_Builtins.inspect_comp c1 in
      let cv2 = FStar_Reflection_Builtins.inspect_comp c2 in
      match (cv1, cv2) with
      | (FStar_Reflection_Data.C_Total t1, FStar_Reflection_Data.C_Total t2)
          -> Obj.magic (Obj.repr (term_eq t1 t2))
      | (FStar_Reflection_Data.C_GTotal t1, FStar_Reflection_Data.C_GTotal
         t2) -> Obj.magic (Obj.repr (term_eq t1 t2))
      | (FStar_Reflection_Data.C_Lemma (pre1, post1, pat1),
         FStar_Reflection_Data.C_Lemma (pre2, post2, pat2)) ->
          Obj.magic
            (Obj.repr
               (op_Amp_Amp_Amp (pre1, post1) (pre2, post2) pat1 pat2
                  (op_Amp_Amp_Amp pre1 pre2 post1 post2 (term_eq pre1 pre2)
                     (term_eq post1 post2)) (term_eq pat1 pat2)))
      | (FStar_Reflection_Data.C_Eff (us1, ef1, t1, args1, dec1),
         FStar_Reflection_Data.C_Eff (us2, ef2, t2, args2, dec2)) ->
          Obj.magic
            (Obj.repr
               (op_Amp_Amp_Amp (((us1, ef1), t1), args1)
                  (((us2, ef2), t2), args2) dec1 dec2
                  (op_Amp_Amp_Amp ((us1, ef1), t1) ((us2, ef2), t2) args1
                     args2
                     (op_Amp_Amp_Amp (us1, ef1) (us2, ef2) t1 t2
                        (op_Amp_Amp_Amp us1 us2 ef1 ef2
                           (list_dec_eq c1 c2 univ_eq us1 us2)
                           (eq_eq ef1 ef2)) (term_eq t1 t2))
                     (list_dec_eq c1 c2 arg_eq args1 args2))
                  (list_dec_eq c1 c2 term_eq dec1 dec2)))
      | uu___ -> Obj.magic (Obj.repr Neq)
and (br_eq : FStar_Reflection_Data.branch comparator_for) =
  fun br1 ->
    fun br2 ->
      op_Amp_Amp_Amp (FStar_Pervasives_Native.fst br1)
        (FStar_Pervasives_Native.fst br2) (FStar_Pervasives_Native.snd br1)
        (FStar_Pervasives_Native.snd br2)
        (pat_eq (FStar_Pervasives_Native.fst br1)
           (FStar_Pervasives_Native.fst br2))
        (term_eq (FStar_Pervasives_Native.snd br1)
           (FStar_Pervasives_Native.snd br2))
and (pat_eq : FStar_Reflection_Data.pattern comparator_for) =
  fun p1 ->
    fun p2 ->
      match (p1, p2) with
      | (FStar_Reflection_Data.Pat_Var (v1, st1),
         FStar_Reflection_Data.Pat_Var (v2, st2)) ->
          Obj.magic (Obj.repr (bv_eq v1 v2))
      | (FStar_Reflection_Data.Pat_Constant c1,
         FStar_Reflection_Data.Pat_Constant c2) ->
          Obj.magic (Obj.repr (const_eq c1 c2))
      | (FStar_Reflection_Data.Pat_Dot_Term t1,
         FStar_Reflection_Data.Pat_Dot_Term t2) ->
          Obj.magic (Obj.repr (opt_dec_eq p1 p2 term_eq t1 t2))
      | (FStar_Reflection_Data.Pat_Cons (f1, us1, args1),
         FStar_Reflection_Data.Pat_Cons (f2, us2, args2)) ->
          Obj.magic
            (Obj.repr
               (op_Amp_Amp_Amp (f1, us1) (f2, us2) args1 args2
                  (op_Amp_Amp_Amp f1 f2 us1 us2 (fv_eq f1 f2)
                     (opt_dec_eq p1 p2 (list_dec_eq p1 p2 univ_eq) us1 us2))
                  (list_dec_eq p1 p2 pat_arg_eq args1 args2)))
      | uu___ -> Obj.magic (Obj.repr Neq)
and (pat_arg_eq :
  (FStar_Reflection_Data.pattern * Prims.bool) comparator_for) =
  fun uu___ ->
    fun uu___1 ->
      match (uu___, uu___1) with
      | ((p1, b1), (p2, b2)) ->
          op_Amp_Amp_Amp p1 p2 b1 b2 (pat_eq p1 p2) (eq_eq b1 b2)
type 'r defined = unit
type ('uuuuu, 'uuuuu1, 'f, 'l1, 'l2) def2 = unit
type 'u faithful_univ = Obj.t
type 't faithful = Obj.t
type 'a faithful_arg = Obj.t
type 'q faithful_qual = Obj.t
type 'b faithful_binder = Obj.t
type 'b faithful_branch = Obj.t
type 'p faithful_pattern = Obj.t
type 'pb faithful_pattern_arg = Obj.t
type 'ats faithful_attrs = Obj.t
type 'c faithful_comp = Obj.t
type faithful_term = FStar_Reflection_Types.term
let (term_eq_dec : faithful_term -> faithful_term -> Prims.bool) =
  fun t1 -> fun t2 -> match term_eq t1 t2 with | Eq -> true | Neq -> false
