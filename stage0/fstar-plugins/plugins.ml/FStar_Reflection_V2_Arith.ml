open Fstarcompiler
open Prims
type expr =
  | Lit of Prims.int 
  | Atom of Prims.nat * FStarC_Reflection_Types.term 
  | Plus of expr * expr 
  | Mult of expr * expr 
  | Minus of expr * expr 
  | Land of expr * expr 
  | Lxor of expr * expr 
  | Lor of expr * expr 
  | Ladd of expr * expr 
  | Lsub of expr * expr 
  | Shl of expr * expr 
  | Shr of expr * expr 
  | Neg of expr 
  | Udiv of expr * expr 
  | Umod of expr * expr 
  | MulMod of expr * expr 
  | NatToBv of expr 
let uu___is_Lit (projectee : expr) : Prims.bool=
  match projectee with | Lit _0 -> true | uu___ -> false
let __proj__Lit__item___0 (projectee : expr) : Prims.int=
  match projectee with | Lit _0 -> _0
let uu___is_Atom (projectee : expr) : Prims.bool=
  match projectee with | Atom (_0, _1) -> true | uu___ -> false
let __proj__Atom__item___0 (projectee : expr) : Prims.nat=
  match projectee with | Atom (_0, _1) -> _0
let __proj__Atom__item___1 (projectee : expr) : FStarC_Reflection_Types.term=
  match projectee with | Atom (_0, _1) -> _1
let uu___is_Plus (projectee : expr) : Prims.bool=
  match projectee with | Plus (_0, _1) -> true | uu___ -> false
let __proj__Plus__item___0 (projectee : expr) : expr=
  match projectee with | Plus (_0, _1) -> _0
let __proj__Plus__item___1 (projectee : expr) : expr=
  match projectee with | Plus (_0, _1) -> _1
let uu___is_Mult (projectee : expr) : Prims.bool=
  match projectee with | Mult (_0, _1) -> true | uu___ -> false
let __proj__Mult__item___0 (projectee : expr) : expr=
  match projectee with | Mult (_0, _1) -> _0
let __proj__Mult__item___1 (projectee : expr) : expr=
  match projectee with | Mult (_0, _1) -> _1
let uu___is_Minus (projectee : expr) : Prims.bool=
  match projectee with | Minus (_0, _1) -> true | uu___ -> false
let __proj__Minus__item___0 (projectee : expr) : expr=
  match projectee with | Minus (_0, _1) -> _0
let __proj__Minus__item___1 (projectee : expr) : expr=
  match projectee with | Minus (_0, _1) -> _1
let uu___is_Land (projectee : expr) : Prims.bool=
  match projectee with | Land (_0, _1) -> true | uu___ -> false
let __proj__Land__item___0 (projectee : expr) : expr=
  match projectee with | Land (_0, _1) -> _0
let __proj__Land__item___1 (projectee : expr) : expr=
  match projectee with | Land (_0, _1) -> _1
let uu___is_Lxor (projectee : expr) : Prims.bool=
  match projectee with | Lxor (_0, _1) -> true | uu___ -> false
let __proj__Lxor__item___0 (projectee : expr) : expr=
  match projectee with | Lxor (_0, _1) -> _0
let __proj__Lxor__item___1 (projectee : expr) : expr=
  match projectee with | Lxor (_0, _1) -> _1
let uu___is_Lor (projectee : expr) : Prims.bool=
  match projectee with | Lor (_0, _1) -> true | uu___ -> false
let __proj__Lor__item___0 (projectee : expr) : expr=
  match projectee with | Lor (_0, _1) -> _0
let __proj__Lor__item___1 (projectee : expr) : expr=
  match projectee with | Lor (_0, _1) -> _1
let uu___is_Ladd (projectee : expr) : Prims.bool=
  match projectee with | Ladd (_0, _1) -> true | uu___ -> false
let __proj__Ladd__item___0 (projectee : expr) : expr=
  match projectee with | Ladd (_0, _1) -> _0
let __proj__Ladd__item___1 (projectee : expr) : expr=
  match projectee with | Ladd (_0, _1) -> _1
let uu___is_Lsub (projectee : expr) : Prims.bool=
  match projectee with | Lsub (_0, _1) -> true | uu___ -> false
let __proj__Lsub__item___0 (projectee : expr) : expr=
  match projectee with | Lsub (_0, _1) -> _0
let __proj__Lsub__item___1 (projectee : expr) : expr=
  match projectee with | Lsub (_0, _1) -> _1
let uu___is_Shl (projectee : expr) : Prims.bool=
  match projectee with | Shl (_0, _1) -> true | uu___ -> false
let __proj__Shl__item___0 (projectee : expr) : expr=
  match projectee with | Shl (_0, _1) -> _0
let __proj__Shl__item___1 (projectee : expr) : expr=
  match projectee with | Shl (_0, _1) -> _1
let uu___is_Shr (projectee : expr) : Prims.bool=
  match projectee with | Shr (_0, _1) -> true | uu___ -> false
let __proj__Shr__item___0 (projectee : expr) : expr=
  match projectee with | Shr (_0, _1) -> _0
let __proj__Shr__item___1 (projectee : expr) : expr=
  match projectee with | Shr (_0, _1) -> _1
let uu___is_Neg (projectee : expr) : Prims.bool=
  match projectee with | Neg _0 -> true | uu___ -> false
let __proj__Neg__item___0 (projectee : expr) : expr=
  match projectee with | Neg _0 -> _0
let uu___is_Udiv (projectee : expr) : Prims.bool=
  match projectee with | Udiv (_0, _1) -> true | uu___ -> false
let __proj__Udiv__item___0 (projectee : expr) : expr=
  match projectee with | Udiv (_0, _1) -> _0
let __proj__Udiv__item___1 (projectee : expr) : expr=
  match projectee with | Udiv (_0, _1) -> _1
let uu___is_Umod (projectee : expr) : Prims.bool=
  match projectee with | Umod (_0, _1) -> true | uu___ -> false
let __proj__Umod__item___0 (projectee : expr) : expr=
  match projectee with | Umod (_0, _1) -> _0
let __proj__Umod__item___1 (projectee : expr) : expr=
  match projectee with | Umod (_0, _1) -> _1
let uu___is_MulMod (projectee : expr) : Prims.bool=
  match projectee with | MulMod (_0, _1) -> true | uu___ -> false
let __proj__MulMod__item___0 (projectee : expr) : expr=
  match projectee with | MulMod (_0, _1) -> _0
let __proj__MulMod__item___1 (projectee : expr) : expr=
  match projectee with | MulMod (_0, _1) -> _1
let uu___is_NatToBv (projectee : expr) : Prims.bool=
  match projectee with | NatToBv _0 -> true | uu___ -> false
let __proj__NatToBv__item___0 (projectee : expr) : expr=
  match projectee with | NatToBv _0 -> _0
type connective =
  | C_Lt 
  | C_Eq 
  | C_Gt 
  | C_Ne 
let uu___is_C_Lt (projectee : connective) : Prims.bool=
  match projectee with | C_Lt -> true | uu___ -> false
let uu___is_C_Eq (projectee : connective) : Prims.bool=
  match projectee with | C_Eq -> true | uu___ -> false
let uu___is_C_Gt (projectee : connective) : Prims.bool=
  match projectee with | C_Gt -> true | uu___ -> false
let uu___is_C_Ne (projectee : connective) : Prims.bool=
  match projectee with | C_Ne -> true | uu___ -> false
type prop =
  | CompProp of expr * connective * expr 
  | AndProp of prop * prop 
  | OrProp of prop * prop 
  | NotProp of prop 
let uu___is_CompProp (projectee : prop) : Prims.bool=
  match projectee with | CompProp (_0, _1, _2) -> true | uu___ -> false
let __proj__CompProp__item___0 (projectee : prop) : expr=
  match projectee with | CompProp (_0, _1, _2) -> _0
let __proj__CompProp__item___1 (projectee : prop) : connective=
  match projectee with | CompProp (_0, _1, _2) -> _1
let __proj__CompProp__item___2 (projectee : prop) : expr=
  match projectee with | CompProp (_0, _1, _2) -> _2
let uu___is_AndProp (projectee : prop) : Prims.bool=
  match projectee with | AndProp (_0, _1) -> true | uu___ -> false
let __proj__AndProp__item___0 (projectee : prop) : prop=
  match projectee with | AndProp (_0, _1) -> _0
let __proj__AndProp__item___1 (projectee : prop) : prop=
  match projectee with | AndProp (_0, _1) -> _1
let uu___is_OrProp (projectee : prop) : Prims.bool=
  match projectee with | OrProp (_0, _1) -> true | uu___ -> false
let __proj__OrProp__item___0 (projectee : prop) : prop=
  match projectee with | OrProp (_0, _1) -> _0
let __proj__OrProp__item___1 (projectee : prop) : prop=
  match projectee with | OrProp (_0, _1) -> _1
let uu___is_NotProp (projectee : prop) : Prims.bool=
  match projectee with | NotProp _0 -> true | uu___ -> false
let __proj__NotProp__item___0 (projectee : prop) : prop=
  match projectee with | NotProp _0 -> _0
let lt (e1 : expr) (e2 : expr) : prop= CompProp (e1, C_Lt, e2)
let le (e1 : expr) (e2 : expr) : prop=
  CompProp (e1, C_Lt, (Plus ((Lit Prims.int_one), e2)))
let eq (e1 : expr) (e2 : expr) : prop= CompProp (e1, C_Eq, e2)
let ne (e1 : expr) (e2 : expr) : prop= CompProp (e1, C_Ne, e2)
let gt (e1 : expr) (e2 : expr) : prop= CompProp (e1, C_Gt, e2)
let ge (e1 : expr) (e2 : expr) : prop=
  CompProp ((Plus ((Lit Prims.int_one), e1)), C_Gt, e2)
type st = (Prims.nat * FStarC_Reflection_Types.term Prims.list)
type 'a tm =
  st ->
    ((Prims.string, ('a * st)) Fstarcompiler.FStar_Pervasives.either, 
      unit) FStar_Tactics_Effect.tac_repr
let return (uu___ : 'a) : 'a tm=
  (fun x i ->
     Obj.magic (fun uu___ -> Fstarcompiler.FStar_Pervasives.Inr (x, i)))
    uu___
let op_let_Bang (m : 'a tm) (f : 'a -> 'b tm) : 'b tm=
  fun i ps ->
    let x = m i ps in
    match x with
    | Fstarcompiler.FStar_Pervasives.Inr (x1, j) -> f x1 j ps
    | s ->
        Fstarcompiler.FStar_Pervasives.Inl
          (FStar_Pervasives.__proj__Inl__item__v s)
let lift (f : 'a -> ('b, unit) FStar_Tactics_Effect.tac_repr) (x : 'a) :
  'b tm=
  fun st1 ps ->
    let x1 = let x2 = f x ps in (x2, st1) in
    Fstarcompiler.FStar_Pervasives.Inr x1
let liftM (f : 'a -> 'b) (x : 'a tm) : 'b tm=
  op_let_Bang x (fun xx -> return (f xx))
let liftM2 (f : 'a -> 'b -> 'c) (x : 'a tm) (y : 'b tm) : 'c tm=
  op_let_Bang x (fun xx -> op_let_Bang y (fun yy -> return (f xx yy)))
let liftM3 (f : 'a -> 'b -> 'c -> 'd) (x : 'a tm) (y : 'b tm) (z : 'c tm) :
  'd tm=
  op_let_Bang x
    (fun xx ->
       op_let_Bang y
         (fun yy -> op_let_Bang z (fun zz -> return (f xx yy zz))))
let rec find_idx :
  'a .
    ('a -> (Prims.bool, unit) FStar_Tactics_Effect.tac_repr) ->
      'a Prims.list ->
        ((Prims.nat * 'a) FStar_Pervasives_Native.option, unit)
          FStar_Tactics_Effect.tac_repr
  =
  fun uu___1 uu___ ->
    (fun f l ->
       match l with
       | [] ->
           Obj.magic (Obj.repr (fun uu___ -> FStar_Pervasives_Native.None))
       | x::xs ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind (Obj.magic (f x))
                   (fun uu___ ->
                      (fun uu___ ->
                         if uu___
                         then
                           Obj.magic
                             (Obj.repr
                                (fun uu___1 ->
                                   FStar_Pervasives_Native.Some
                                     (Prims.int_zero, x)))
                         else
                           Obj.magic
                             (Obj.repr
                                (FStar_Tactics_Effect.tac_bind
                                   (Obj.magic (find_idx f xs))
                                   (fun uu___2 ->
                                      match uu___2 with
                                      | FStar_Pervasives_Native.None ->
                                          (fun uu___3 ->
                                             FStar_Pervasives_Native.None)
                                      | FStar_Pervasives_Native.Some 
                                          (i, x1) ->
                                          FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___3 ->
                                               FStar_Pervasives_Native.Some
                                                 ((i + Prims.int_one), x1))))))
                        uu___)))) uu___1 uu___
let atom (t : FStarC_Reflection_Types.term) : expr tm=
  fun uu___ ->
    match uu___ with
    | (n, atoms) ->
        FStar_Tactics_Effect.tac_bind
          (Obj.magic
             (find_idx
                (fun uu___1 ->
                   (fun a ->
                      Obj.magic
                        (fun uu___1 ->
                           FStar_Reflection_TermEq_Simple.term_eq t a))
                     uu___1) atoms))
          (fun uu___1 ->
             match uu___1 with
             | FStar_Pervasives_Native.None ->
                 (fun uu___2 ->
                    Fstarcompiler.FStar_Pervasives.Inr
                      ((Atom (n, t)), ((n + Prims.int_one), (t :: atoms))))
             | FStar_Pervasives_Native.Some (i, t1) ->
                 FStar_Tactics_Effect.lift_div_tac
                   (fun uu___2 ->
                      Fstarcompiler.FStar_Pervasives.Inr
                        ((Atom (((n - Prims.int_one) - i), t1)), (n, atoms))))
let fail (uu___ : Prims.string) : 'a tm=
  (fun s i -> Obj.magic (fun uu___ -> Fstarcompiler.FStar_Pervasives.Inl s))
    uu___
let rec as_arith_expr (t : FStarC_Reflection_Types.term) : expr tm=
  let uu___ = FStar_Reflection_V2_Collect.collect_app_ln t in
  match uu___ with
  | (hd, tl) ->
      (match ((FStarC_Reflection_V2_Builtins.inspect_ln hd), tl) with
       | (FStarC_Reflection_V2_Data.Tv_FVar fv,
          (e1, FStarC_Reflection_V2_Data.Q_Implicit)::(e2,
                                                       FStarC_Reflection_V2_Data.Q_Explicit)::
          (e3, FStarC_Reflection_V2_Data.Q_Explicit)::[]) ->
           let qn = FStarC_Reflection_V2_Builtins.inspect_fv fv in
           let e2' = as_arith_expr e2 in
           let e3' = as_arith_expr e3 in
           if qn = FStar_Reflection_Const.land_qn
           then liftM2 (fun uu___1 uu___2 -> Land (uu___1, uu___2)) e2' e3'
           else
             if qn = FStar_Reflection_Const.lxor_qn
             then liftM2 (fun uu___2 uu___3 -> Lxor (uu___2, uu___3)) e2' e3'
             else
               if qn = FStar_Reflection_Const.lor_qn
               then
                 liftM2 (fun uu___3 uu___4 -> Lor (uu___3, uu___4)) e2' e3'
               else
                 if qn = FStar_Reflection_Const.shiftr_qn
                 then
                   liftM2 (fun uu___4 uu___5 -> Shr (uu___4, uu___5)) e2' e3'
                 else
                   if qn = FStar_Reflection_Const.shiftl_qn
                   then
                     liftM2 (fun uu___5 uu___6 -> Shl (uu___5, uu___6)) e2'
                       e3'
                   else
                     if qn = FStar_Reflection_Const.udiv_qn
                     then
                       liftM2 (fun uu___6 uu___7 -> Udiv (uu___6, uu___7))
                         e2' e3'
                     else
                       if qn = FStar_Reflection_Const.umod_qn
                       then
                         liftM2 (fun uu___7 uu___8 -> Umod (uu___7, uu___8))
                           e2' e3'
                       else
                         if qn = FStar_Reflection_Const.mul_mod_qn
                         then
                           liftM2
                             (fun uu___8 uu___9 -> MulMod (uu___8, uu___9))
                             e2' e3'
                         else
                           if qn = FStar_Reflection_Const.ladd_qn
                           then
                             liftM2
                               (fun uu___9 uu___10 -> Ladd (uu___9, uu___10))
                               e2' e3'
                           else
                             if qn = FStar_Reflection_Const.lsub_qn
                             then
                               liftM2
                                 (fun uu___10 uu___11 ->
                                    Lsub (uu___10, uu___11)) e2' e3'
                             else atom t
       | (FStarC_Reflection_V2_Data.Tv_FVar fv,
          (l, FStarC_Reflection_V2_Data.Q_Explicit)::(r,
                                                      FStarC_Reflection_V2_Data.Q_Explicit)::[])
           ->
           let qn = FStarC_Reflection_V2_Builtins.inspect_fv fv in
           let ll = as_arith_expr l in
           let rr = as_arith_expr r in
           if qn = FStar_Reflection_Const.add_qn
           then liftM2 (fun uu___1 uu___2 -> Plus (uu___1, uu___2)) ll rr
           else
             if qn = FStar_Reflection_Const.minus_qn
             then liftM2 (fun uu___2 uu___3 -> Minus (uu___2, uu___3)) ll rr
             else
               if qn = FStar_Reflection_Const.mult_qn
               then liftM2 (fun uu___3 uu___4 -> Mult (uu___3, uu___4)) ll rr
               else
                 if qn = FStar_Reflection_Const.mult'_qn
                 then
                   liftM2 (fun uu___4 uu___5 -> Mult (uu___4, uu___5)) ll rr
                 else atom t
       | (FStarC_Reflection_V2_Data.Tv_FVar fv,
          (l, FStarC_Reflection_V2_Data.Q_Implicit)::(r,
                                                      FStarC_Reflection_V2_Data.Q_Explicit)::[])
           ->
           let qn = FStarC_Reflection_V2_Builtins.inspect_fv fv in
           let ll = as_arith_expr l in
           let rr = as_arith_expr r in
           if qn = FStar_Reflection_Const.nat_bv_qn
           then liftM (fun uu___1 -> NatToBv uu___1) rr
           else atom t
       | (FStarC_Reflection_V2_Data.Tv_FVar fv,
          (a, FStarC_Reflection_V2_Data.Q_Explicit)::[]) ->
           let qn = FStarC_Reflection_V2_Builtins.inspect_fv fv in
           let aa = as_arith_expr a in
           if qn = FStar_Reflection_Const.neg_qn
           then liftM (fun uu___1 -> Neg uu___1) aa
           else atom t
       | (FStarC_Reflection_V2_Data.Tv_Const (FStarC_Reflection_V2_Data.C_Int
          i), uu___1) -> return (Lit i)
       | uu___1 -> atom t)
let is_arith_expr (t : FStarC_Reflection_Types.term) : expr tm=
  op_let_Bang (as_arith_expr t)
    (fun a ->
       match a with
       | Atom (uu___, t1) ->
           let uu___1 = FStar_Reflection_V2_Derived_Lemmas.collect_app_ref t1 in
           (match uu___1 with
            | (hd, tl) ->
                (match ((FStarC_Reflection_V2_Builtins.inspect_ln hd), tl)
                 with
                 | (FStarC_Reflection_V2_Data.Tv_FVar uu___2, []) -> return a
                 | (FStarC_Reflection_V2_Data.Tv_BVar uu___2, []) -> return a
                 | (FStarC_Reflection_V2_Data.Tv_Var uu___2, []) -> return a
                 | uu___2 ->
                     op_let_Bang
                       (lift FStarC_Tactics_V2_Builtins.term_to_string t1)
                       (fun s ->
                          fail
                            (Prims.strcat "not an arithmetic expression: ("
                               (Prims.strcat s ")")))))
       | uu___ -> return a)
let rec is_arith_prop (t : FStarC_Reflection_Types.term) (i : st) :
  ((Prims.string, (prop * st)) Fstarcompiler.FStar_Pervasives.either, 
    unit) FStar_Tactics_Effect.tac_repr=
  op_let_Bang
    (lift (fun t1 -> FStar_Reflection_V2_Formula.term_as_formula t1) t)
    (fun f ->
       match f with
       | FStar_Reflection_V2_Formula.Comp
           (FStar_Reflection_V2_Formula.Eq uu___, l, r) ->
           liftM2 eq (is_arith_expr l) (is_arith_expr r)
       | FStar_Reflection_V2_Formula.Comp
           (FStar_Reflection_V2_Formula.BoolEq uu___, l, r) ->
           liftM2 eq (is_arith_expr l) (is_arith_expr r)
       | FStar_Reflection_V2_Formula.Comp
           (FStar_Reflection_V2_Formula.Lt, l, r) ->
           liftM2 lt (is_arith_expr l) (is_arith_expr r)
       | FStar_Reflection_V2_Formula.Comp
           (FStar_Reflection_V2_Formula.Le, l, r) ->
           liftM2 le (is_arith_expr l) (is_arith_expr r)
       | FStar_Reflection_V2_Formula.And (l, r) ->
           liftM2 (fun uu___ uu___1 -> AndProp (uu___, uu___1))
             (is_arith_prop l) (is_arith_prop r)
       | FStar_Reflection_V2_Formula.Or (l, r) ->
           liftM2 (fun uu___ uu___1 -> OrProp (uu___, uu___1))
             (is_arith_prop l) (is_arith_prop r)
       | uu___ ->
           op_let_Bang (lift FStarC_Tactics_V2_Builtins.term_to_string t)
             (fun s -> fail (Prims.strcat "connector (" (Prims.strcat s ")"))))
    i
let run_tm (m : 'a tm) :
  ((Prims.string, 'a) Fstarcompiler.FStar_Pervasives.either, unit)
    FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = m (Prims.int_zero, []) ps in
    match x with
    | Fstarcompiler.FStar_Pervasives.Inr (x1, uu___) ->
        Fstarcompiler.FStar_Pervasives.Inr x1
    | s ->
        Fstarcompiler.FStar_Pervasives.Inl
          (FStar_Pervasives.__proj__Inl__item__v s)
let rec expr_to_string (e : expr) : Prims.string=
  match e with
  | Atom (i, uu___) -> Prims.strcat "a" (Prims.string_of_int i)
  | Lit i -> Prims.string_of_int i
  | Plus (l, r) ->
      Prims.strcat "("
        (Prims.strcat (expr_to_string l)
           (Prims.strcat " + " (Prims.strcat (expr_to_string r) ")")))
  | Minus (l, r) ->
      Prims.strcat "("
        (Prims.strcat (expr_to_string l)
           (Prims.strcat " - " (Prims.strcat (expr_to_string r) ")")))
  | Mult (l, r) ->
      Prims.strcat "("
        (Prims.strcat (expr_to_string l)
           (Prims.strcat " * " (Prims.strcat (expr_to_string r) ")")))
  | Neg l -> Prims.strcat "(- " (Prims.strcat (expr_to_string l) ")")
  | Land (l, r) ->
      Prims.strcat "("
        (Prims.strcat (expr_to_string l)
           (Prims.strcat " & " (Prims.strcat (expr_to_string r) ")")))
  | Lor (l, r) ->
      Prims.strcat "("
        (Prims.strcat (expr_to_string l)
           (Prims.strcat " | " (Prims.strcat (expr_to_string r) ")")))
  | Lxor (l, r) ->
      Prims.strcat "("
        (Prims.strcat (expr_to_string l)
           (Prims.strcat " ^ " (Prims.strcat (expr_to_string r) ")")))
  | Ladd (l, r) ->
      Prims.strcat "("
        (Prims.strcat (expr_to_string l)
           (Prims.strcat " >> " (Prims.strcat (expr_to_string r) ")")))
  | Lsub (l, r) ->
      Prims.strcat "("
        (Prims.strcat (expr_to_string l)
           (Prims.strcat " >> " (Prims.strcat (expr_to_string r) ")")))
  | Shl (l, r) ->
      Prims.strcat "("
        (Prims.strcat (expr_to_string l)
           (Prims.strcat " << " (Prims.strcat (expr_to_string r) ")")))
  | Shr (l, r) ->
      Prims.strcat "("
        (Prims.strcat (expr_to_string l)
           (Prims.strcat " >> " (Prims.strcat (expr_to_string r) ")")))
  | NatToBv l ->
      Prims.strcat "("
        (Prims.strcat "to_vec " (Prims.strcat (expr_to_string l) ")"))
  | Udiv (l, r) ->
      Prims.strcat "("
        (Prims.strcat (expr_to_string l)
           (Prims.strcat " / " (Prims.strcat (expr_to_string r) ")")))
  | Umod (l, r) ->
      Prims.strcat "("
        (Prims.strcat (expr_to_string l)
           (Prims.strcat " % " (Prims.strcat (expr_to_string r) ")")))
  | MulMod (l, r) ->
      Prims.strcat "("
        (Prims.strcat (expr_to_string l)
           (Prims.strcat " ** " (Prims.strcat (expr_to_string r) ")")))
let rec compare_expr (e1 : expr) (e2 : expr) : FStar_Order.order=
  match (e1, e2) with
  | (Lit i, Lit j) -> FStar_Order.compare_int i j
  | (Atom (uu___, t), Atom (uu___1, s)) ->
      FStar_Reflection_V2_Compare.compare_term t s
  | (Plus (l1, l2), Plus (r1, r2)) ->
      FStar_Order.lex (compare_expr l1 r1) (fun uu___ -> compare_expr l2 r2)
  | (Minus (l1, l2), Minus (r1, r2)) ->
      FStar_Order.lex (compare_expr l1 r1) (fun uu___ -> compare_expr l2 r2)
  | (Mult (l1, l2), Mult (r1, r2)) ->
      FStar_Order.lex (compare_expr l1 r1) (fun uu___ -> compare_expr l2 r2)
  | (Neg e11, Neg e21) -> compare_expr e11 e21
  | (Lit uu___, uu___1) -> FStar_Order.Lt
  | (uu___, Lit uu___1) -> FStar_Order.Gt
  | (Atom (uu___, uu___1), uu___2) -> FStar_Order.Lt
  | (uu___, Atom (uu___1, uu___2)) -> FStar_Order.Gt
  | (Plus (uu___, uu___1), uu___2) -> FStar_Order.Lt
  | (uu___, Plus (uu___1, uu___2)) -> FStar_Order.Gt
  | (Mult (uu___, uu___1), uu___2) -> FStar_Order.Lt
  | (uu___, Mult (uu___1, uu___2)) -> FStar_Order.Gt
  | (Neg uu___, uu___1) -> FStar_Order.Lt
  | (uu___, Neg uu___1) -> FStar_Order.Gt
  | uu___ -> FStar_Order.Gt
