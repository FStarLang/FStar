open Fstarcompiler
open Prims
type 't comparator_for =
  't -> 't -> (Prims.bool, unit) FStar_Tactics_Effect.tac_repr
let opt_eq (uu___ : 'a comparator_for) :
  'a FStar_Pervasives_Native.option comparator_for=
  (fun cmp o1 o2 ->
     match (o1, o2) with
     | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) ->
         Obj.magic (Obj.repr (fun uu___ -> true))
     | (FStar_Pervasives_Native.Some x, FStar_Pervasives_Native.Some y) ->
         Obj.magic (Obj.repr (cmp x y))
     | uu___ ->
         Obj.magic
           (Obj.repr
              (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> false))))
    uu___
let either_eq (uu___1 : 'a comparator_for) (uu___ : 'b comparator_for) :
  ('a, 'b) Fstarcompiler.FStar_Pervasives.either comparator_for=
  (fun cmpa cmpb e1 e2 ->
     match (e1, e2) with
     | (Fstarcompiler.FStar_Pervasives.Inl x,
        Fstarcompiler.FStar_Pervasives.Inl y) ->
         Obj.magic (Obj.repr (cmpa x y))
     | (Fstarcompiler.FStar_Pervasives.Inr x,
        Fstarcompiler.FStar_Pervasives.Inr y) ->
         Obj.magic (Obj.repr (cmpb x y))
     | uu___ ->
         Obj.magic
           (Obj.repr
              (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> false))))
    uu___1 uu___
let pair_eq (cmpa : 'a comparator_for) (cmpb : 'b comparator_for) :
  ('a * 'b) comparator_for=
  fun uu___ uu___1 ->
    match (uu___, uu___1) with
    | ((a1, b1), (a2, b2)) ->
        FStar_Tactics_Effect.tac_bind (Obj.magic (cmpa a1 a2))
          (fun uu___2 ->
             (fun uu___2 ->
                if uu___2
                then Obj.magic (Obj.repr (cmpb b1 b2))
                else
                  Obj.magic
                    (Obj.repr
                       (FStar_Tactics_Effect.lift_div_tac
                          (fun uu___4 -> false)))) uu___2)
let rec list_eq : 'a . 'a comparator_for -> 'a Prims.list comparator_for =
  fun uu___ ->
    (fun cmp l1 l2 ->
       match (l1, l2) with
       | ([], []) -> Obj.magic (Obj.repr (fun uu___ -> true))
       | (x::xs, y::ys) ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind (Obj.magic (cmp x y))
                   (fun uu___ ->
                      (fun uu___ ->
                         if uu___
                         then Obj.magic (Obj.repr (list_eq cmp xs ys))
                         else
                           Obj.magic
                             (Obj.repr
                                (FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___2 -> false)))) uu___)))
       | uu___ ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> false))))
      uu___
let rec univ_eq : FStarC_Reflection_Types.universe comparator_for=
  fun u1 u2 ps ->
    let x = FStarC_Tactics_V2_Builtins.compress_univ u1 ps in
    let x1 = FStarC_Tactics_V2_Builtins.compress_univ u2 ps in
    let x2 = FStarC_Reflection_V2_Builtins.inspect_universe x in
    let x3 = FStarC_Reflection_V2_Builtins.inspect_universe x1 in
    match (x2, x3) with
    | (FStarC_Reflection_V2_Data.Uv_Zero, FStarC_Reflection_V2_Data.Uv_Zero)
        -> true
    | (FStarC_Reflection_V2_Data.Uv_Succ u11,
       FStarC_Reflection_V2_Data.Uv_Succ u21) -> univ_eq u11 u21 ps
    | (FStarC_Reflection_V2_Data.Uv_Max us1, FStarC_Reflection_V2_Data.Uv_Max
       us2) -> list_eq univ_eq us1 us2 ps
    | (FStarC_Reflection_V2_Data.Uv_BVar v1,
       FStarC_Reflection_V2_Data.Uv_BVar v2) -> v1 = v2
    | (FStarC_Reflection_V2_Data.Uv_Name id1,
       FStarC_Reflection_V2_Data.Uv_Name id2) ->
        (FStar_Pervasives_Native.fst
           (FStarC_Reflection_V2_Builtins.inspect_ident id1))
          =
          (FStar_Pervasives_Native.fst
             (FStarC_Reflection_V2_Builtins.inspect_ident id2))
    | (FStarC_Reflection_V2_Data.Uv_Unif u11,
       FStarC_Reflection_V2_Data.Uv_Unif u21) -> false
    | (FStarC_Reflection_V2_Data.Uv_Unk, FStarC_Reflection_V2_Data.Uv_Unk) ->
        false
    | uu___ -> false
let const_eq : FStarC_Reflection_V2_Data.vconst comparator_for=
  fun c1 c2 ->
    Obj.magic
      (fun uu___ ->
         match (c1, c2) with
         | (FStarC_Reflection_V2_Data.C_Unit,
            FStarC_Reflection_V2_Data.C_Unit) -> true
         | (FStarC_Reflection_V2_Data.C_Int i1,
            FStarC_Reflection_V2_Data.C_Int i2) -> i1 = i2
         | (FStarC_Reflection_V2_Data.C_True,
            FStarC_Reflection_V2_Data.C_True) -> true
         | (FStarC_Reflection_V2_Data.C_False,
            FStarC_Reflection_V2_Data.C_False) -> true
         | (FStarC_Reflection_V2_Data.C_String s1,
            FStarC_Reflection_V2_Data.C_String s2) -> s1 = s2
         | (FStarC_Reflection_V2_Data.C_Range r1,
            FStarC_Reflection_V2_Data.C_Range r2) -> true
         | (FStarC_Reflection_V2_Data.C_Reify,
            FStarC_Reflection_V2_Data.C_Reify) -> true
         | (FStarC_Reflection_V2_Data.C_Reflect n1,
            FStarC_Reflection_V2_Data.C_Reflect n2) -> n1 = n2
         | (FStarC_Reflection_V2_Data.C_Real s1,
            FStarC_Reflection_V2_Data.C_Real s2) -> s1 = s2
         | (FStarC_Reflection_V2_Data.C_Char s1,
            FStarC_Reflection_V2_Data.C_Char s2) -> s1 = s2
         | uu___1 -> false)
let rec term_eq : FStarC_Reflection_Types.term comparator_for=
  fun t1 t2 ps ->
    let x = FStarC_Tactics_V2_Builtins.compress t1 ps in
    let x1 = FStarC_Tactics_V2_Builtins.compress t2 ps in
    let x2 = FStarC_Reflection_V2_Builtins.inspect_ln x in
    let x3 = FStarC_Reflection_V2_Builtins.inspect_ln x1 in
    match (x2, x3) with
    | (FStarC_Reflection_V2_Data.Tv_Unsupp, uu___) -> false
    | (uu___, FStarC_Reflection_V2_Data.Tv_Unsupp) -> false
    | (FStarC_Reflection_V2_Data.Tv_Var v1, FStarC_Reflection_V2_Data.Tv_Var
       v2) ->
        (FStarC_Reflection_V2_Builtins.inspect_namedv v1).FStarC_Reflection_V2_Data.uniq
          =
          (FStarC_Reflection_V2_Builtins.inspect_namedv v2).FStarC_Reflection_V2_Data.uniq
    | (FStarC_Reflection_V2_Data.Tv_BVar v1,
       FStarC_Reflection_V2_Data.Tv_BVar v2) ->
        (FStarC_Reflection_V2_Builtins.inspect_bv v1).FStarC_Reflection_V2_Data.index
          =
          (FStarC_Reflection_V2_Builtins.inspect_bv v2).FStarC_Reflection_V2_Data.index
    | (FStarC_Reflection_V2_Data.Tv_FVar f1,
       FStarC_Reflection_V2_Data.Tv_FVar f2) ->
        (FStarC_Reflection_V2_Builtins.inspect_fv f1) =
          (FStarC_Reflection_V2_Builtins.inspect_fv f2)
    | (FStarC_Reflection_V2_Data.Tv_UInst (f1, uu___),
       FStarC_Reflection_V2_Data.Tv_FVar f2) ->
        (FStarC_Reflection_V2_Builtins.inspect_fv f1) =
          (FStarC_Reflection_V2_Builtins.inspect_fv f2)
    | (FStarC_Reflection_V2_Data.Tv_FVar f1,
       FStarC_Reflection_V2_Data.Tv_UInst (f2, uu___)) ->
        (FStarC_Reflection_V2_Builtins.inspect_fv f1) =
          (FStarC_Reflection_V2_Builtins.inspect_fv f2)
    | (FStarC_Reflection_V2_Data.Tv_UInst (f1, uu___),
       FStarC_Reflection_V2_Data.Tv_UInst (f2, uu___1)) ->
        (FStarC_Reflection_V2_Builtins.inspect_fv f1) =
          (FStarC_Reflection_V2_Builtins.inspect_fv f2)
    | (FStarC_Reflection_V2_Data.Tv_App (h1, a1),
       FStarC_Reflection_V2_Data.Tv_App (h2, a2)) ->
        let x4 = term_eq h1 h2 ps in if x4 then arg_eq a1 a2 ps else false
    | (FStarC_Reflection_V2_Data.Tv_Abs (b1, e1),
       FStarC_Reflection_V2_Data.Tv_Abs (b2, e2)) ->
        let x4 = binder_eq b1 b2 ps in if x4 then term_eq e1 e2 ps else false
    | (FStarC_Reflection_V2_Data.Tv_Arrow (b1, c1),
       FStarC_Reflection_V2_Data.Tv_Arrow (b2, c2)) ->
        let x4 = binder_eq b1 b2 ps in if x4 then comp_eq c1 c2 ps else false
    | (FStarC_Reflection_V2_Data.Tv_Type u1,
       FStarC_Reflection_V2_Data.Tv_Type u2) -> true
    | (FStarC_Reflection_V2_Data.Tv_Refine (sb1, r1),
       FStarC_Reflection_V2_Data.Tv_Refine (sb2, r2)) ->
        let x4 = binder_eq sb1 sb2 ps in
        if x4 then term_eq r1 r2 ps else false
    | (FStarC_Reflection_V2_Data.Tv_Const c1,
       FStarC_Reflection_V2_Data.Tv_Const c2) -> const_eq c1 c2 ps
    | (FStarC_Reflection_V2_Data.Tv_Uvar (n1, _u1),
       FStarC_Reflection_V2_Data.Tv_Uvar (n2, _u2)) -> n1 = n2
    | (FStarC_Reflection_V2_Data.Tv_Let (r1, attrs1, sb1, e1, b1),
       FStarC_Reflection_V2_Data.Tv_Let (r2, attrs2, sb2, e2, b2)) ->
        if (Prims.op_Negation r1) = r2
        then false
        else
          (let x4 = let x5 = binder_eq sb1 sb2 ps in Prims.op_Negation x5 in
           if x4
           then false
           else
             (let x5 = let x6 = term_eq e1 e2 ps in Prims.op_Negation x6 in
              if x5 then false else term_eq b1 b2 ps))
    | (FStarC_Reflection_V2_Data.Tv_Match (sc1, o1, brs1),
       FStarC_Reflection_V2_Data.Tv_Match (sc2, o2, brs2)) ->
        let x4 = let x5 = term_eq sc1 sc2 ps in Prims.op_Negation x5 in
        if x4
        then false
        else
          (let x5 =
             let x6 = opt_eq match_returns_ascription_eq o1 o2 ps in
             Prims.op_Negation x6 in
           if x5 then false else list_eq br_eq brs1 brs2 ps)
    | (FStarC_Reflection_V2_Data.Tv_AscribedT (t11, uu___, uu___1, uu___2),
       uu___3) -> term_eq t11 x1 ps
    | (FStarC_Reflection_V2_Data.Tv_AscribedC (t11, uu___, uu___1, uu___2),
       uu___3) -> term_eq t11 x1 ps
    | (uu___, FStarC_Reflection_V2_Data.Tv_AscribedT
       (t21, uu___1, uu___2, uu___3)) -> term_eq x t21 ps
    | (uu___, FStarC_Reflection_V2_Data.Tv_AscribedC
       (t21, uu___1, uu___2, uu___3)) -> term_eq x t21 ps
    | (FStarC_Reflection_V2_Data.Tv_Unknown,
       FStarC_Reflection_V2_Data.Tv_Unknown) -> true
    | uu___ -> false
and arg_eq : FStarC_Reflection_V2_Data.argv comparator_for=
  fun uu___ uu___1 ->
    match (uu___, uu___1) with
    | ((a1, q1), (a2, q2)) ->
        FStar_Tactics_Effect.tac_bind (Obj.magic (term_eq a1 a2))
          (fun uu___2 ->
             (fun uu___2 ->
                if uu___2
                then Obj.magic (Obj.repr (aqual_eq q1 q2))
                else
                  Obj.magic
                    (Obj.repr
                       (FStar_Tactics_Effect.lift_div_tac
                          (fun uu___4 -> false)))) uu___2)
and aqual_eq : FStarC_Reflection_V2_Data.aqualv comparator_for=
  fun a1 a2 ->
    match (a1, a2) with
    | (FStarC_Reflection_V2_Data.Q_Implicit,
       FStarC_Reflection_V2_Data.Q_Implicit) ->
        Obj.magic (Obj.repr (fun uu___ -> true))
    | (FStarC_Reflection_V2_Data.Q_Explicit,
       FStarC_Reflection_V2_Data.Q_Explicit) ->
        Obj.magic (Obj.repr (fun uu___ -> true))
    | (FStarC_Reflection_V2_Data.Q_Equality,
       FStarC_Reflection_V2_Data.Q_Equality) ->
        Obj.magic (Obj.repr (fun uu___ -> true))
    | (FStarC_Reflection_V2_Data.Q_Meta m1, FStarC_Reflection_V2_Data.Q_Meta
       m2) -> Obj.magic (Obj.repr (term_eq m1 m2))
    | uu___ ->
        Obj.magic
          (Obj.repr (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> false)))
and match_returns_ascription_eq :
  FStarC_Syntax_Syntax.match_returns_ascription comparator_for=
  fun asc1 asc2 ps ->
    let x = asc1 in
    match x with
    | (b1, (tc1, tacopt1, eq1)) ->
        let x1 = asc2 in
        (match x1 with
         | (b2, (tc2, tacopt2, eq2)) ->
             let x2 = let x3 = binder_eq b1 b2 ps in Prims.op_Negation x3 in
             if x2
             then false
             else
               (let x3 =
                  let x4 = either_eq term_eq comp_eq tc1 tc2 ps in
                  Prims.op_Negation x4 in
                if x3
                then false
                else
                  (let x4 =
                     let x5 = opt_eq term_eq tacopt1 tacopt2 ps in
                     Prims.op_Negation x5 in
                   if x4 then false else eq1 = eq2)))
and binder_eq : FStarC_Reflection_Types.binder comparator_for=
  fun b1 b2 ps ->
    let x = FStarC_Reflection_V2_Builtins.inspect_binder b1 in
    let x1 = FStarC_Reflection_V2_Builtins.inspect_binder b2 in
    let x2 =
      let x3 =
        term_eq x.FStarC_Reflection_V2_Data.sort2
          x1.FStarC_Reflection_V2_Data.sort2 ps in
      Prims.op_Negation x3 in
    if x2
    then false
    else
      (let x3 =
         let x4 =
           aqual_eq x.FStarC_Reflection_V2_Data.qual
             x1.FStarC_Reflection_V2_Data.qual ps in
         Prims.op_Negation x4 in
       if x3
       then false
       else
         list_eq term_eq x.FStarC_Reflection_V2_Data.attrs
           x1.FStarC_Reflection_V2_Data.attrs ps)
and comp_eq : FStarC_Reflection_Types.comp comparator_for=
  fun c1 c2 ps ->
    let x = FStarC_Reflection_V2_Builtins.inspect_comp c1 in
    let x1 = FStarC_Reflection_V2_Builtins.inspect_comp c2 in
    match (x, x1) with
    | (FStarC_Reflection_V2_Data.C_Total t1,
       FStarC_Reflection_V2_Data.C_Total t2) -> term_eq t1 t2 ps
    | (FStarC_Reflection_V2_Data.C_GTotal t1,
       FStarC_Reflection_V2_Data.C_GTotal t2) -> term_eq t1 t2 ps
    | (FStarC_Reflection_V2_Data.C_Lemma (pre1, post1, pat1),
       FStarC_Reflection_V2_Data.C_Lemma (pre2, post2, pat2)) ->
        let x2 = let x3 = term_eq pre1 pre2 ps in Prims.op_Negation x3 in
        if x2
        then false
        else
          (let x3 = let x4 = term_eq post1 post2 ps in Prims.op_Negation x4 in
           if x3 then false else term_eq pat1 pat2 ps)
    | (FStarC_Reflection_V2_Data.C_Eff (us1, ef1, t1, args1, dec1),
       FStarC_Reflection_V2_Data.C_Eff (us2, ef2, t2, args2, dec2)) ->
        if Prims.op_Negation (ef1 = ef2)
        then false
        else
          (let x2 = let x3 = term_eq t1 t2 ps in Prims.op_Negation x3 in
           if x2 then false else true)
    | uu___ -> false
and br_eq : FStarC_Reflection_V2_Data.branch comparator_for=
  fun br1 br2 ps ->
    let x =
      let x1 =
        pat_eq (FStar_Pervasives_Native.fst br1)
          (FStar_Pervasives_Native.fst br2) ps in
      Prims.op_Negation x1 in
    if x
    then false
    else
      term_eq (FStar_Pervasives_Native.snd br1)
        (FStar_Pervasives_Native.snd br2) ps
and pat_eq : FStarC_Reflection_V2_Data.pattern comparator_for=
  fun p1 p2 ->
    match (p1, p2) with
    | (FStarC_Reflection_V2_Data.Pat_Var (v1, sort1),
       FStarC_Reflection_V2_Data.Pat_Var (v2, sort2)) ->
        Obj.magic
          (Obj.repr (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> true)))
    | (FStarC_Reflection_V2_Data.Pat_Constant x1,
       FStarC_Reflection_V2_Data.Pat_Constant x2) ->
        Obj.magic (Obj.repr (const_eq x1 x2))
    | (FStarC_Reflection_V2_Data.Pat_Dot_Term x1,
       FStarC_Reflection_V2_Data.Pat_Dot_Term x2) ->
        Obj.magic (Obj.repr (opt_eq term_eq x1 x2))
    | (FStarC_Reflection_V2_Data.Pat_Cons (head1, us1, subpats1),
       FStarC_Reflection_V2_Data.Pat_Cons (head2, us2, subpats2)) ->
        Obj.magic
          (Obj.repr
             (if
                Prims.op_Negation
                  ((FStarC_Reflection_V2_Builtins.inspect_fv head1) =
                     (FStarC_Reflection_V2_Builtins.inspect_fv head2))
              then
                Obj.repr
                  (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> false))
              else Obj.repr (list_eq pat_arg_eq subpats1 subpats2)))
    | uu___ ->
        Obj.magic
          (Obj.repr (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> false)))
and pat_arg_eq :
  (FStarC_Reflection_V2_Data.pattern * Prims.bool) comparator_for=
  fun uu___ uu___1 ->
    match (uu___, uu___1) with
    | ((p1, b1), (p2, b2)) ->
        FStar_Tactics_Effect.tac_bind
          (Obj.magic
             (FStar_Tactics_Effect.tac_bind (Obj.magic (pat_eq p1 p2))
                (fun uu___2 uu___3 -> Prims.op_Negation uu___2)))
          (fun uu___2 ->
             if uu___2
             then fun uu___3 -> false
             else FStar_Tactics_Effect.lift_div_tac (fun uu___4 -> b1 = b2))
let lax_term_eq (t1 : FStarC_Reflection_Types.term)
  (t2 : FStarC_Reflection_Types.term) :
  (Prims.bool, unit) FStar_Tactics_Effect.tac_repr=
  fun ps -> let x = term_eq t1 t2 ps in x
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.LaxTermEq.lax_term_eq" (Prims.of_int (3))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_2
               "FStar.Tactics.LaxTermEq.lax_term_eq (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_2 lax_term_eq)
               Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term
               Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term
               Fstarcompiler.FStarC_Syntax_Embeddings.e_bool psc ncb us args)
let lax_univ_eq (u1 : FStarC_Reflection_Types.universe)
  (u2 : FStarC_Reflection_Types.universe) :
  (Prims.bool, unit) FStar_Tactics_Effect.tac_repr= univ_eq u1 u2
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.LaxTermEq.lax_univ_eq" (Prims.of_int (3))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_2
               "FStar.Tactics.LaxTermEq.lax_univ_eq (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_2 lax_univ_eq)
               Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_universe
               Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_universe
               Fstarcompiler.FStarC_Syntax_Embeddings.e_bool psc ncb us args)
