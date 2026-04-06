open Fstarcompiler
open Prims
let term_eq :
  FStarC_Reflection_Types.term -> FStarC_Reflection_Types.term -> Prims.bool=
  FStar_Reflection_TermEq_Simple.term_eq
type atom = Prims.int
type exp =
  | Unit 
  | Mult of exp * exp 
  | Atom of atom 
let uu___is_Unit (projectee : exp) : Prims.bool=
  match projectee with | Unit -> true | uu___ -> false
let uu___is_Mult (projectee : exp) : Prims.bool=
  match projectee with | Mult (_0, _1) -> true | uu___ -> false
let __proj__Mult__item___0 (projectee : exp) : exp=
  match projectee with | Mult (_0, _1) -> _0
let __proj__Mult__item___1 (projectee : exp) : exp=
  match projectee with | Mult (_0, _1) -> _1
let uu___is_Atom (projectee : exp) : Prims.bool=
  match projectee with | Atom _0 -> true | uu___ -> false
let __proj__Atom__item___0 (projectee : exp) : atom=
  match projectee with | Atom _0 -> _0
let rec exp_to_string (e : exp) : Prims.string=
  match e with
  | Unit -> "Unit"
  | Atom x -> Prims.strcat "Atom " (Prims.string_of_int x)
  | Mult (e1, e2) ->
      Prims.strcat "Mult ("
        (Prims.strcat (exp_to_string e1)
           (Prims.strcat ") (" (Prims.strcat (exp_to_string e2) ")")))
type 'a amap = ((atom * 'a) Prims.list * 'a)
let const (xa : 'a) : 'a amap= ([], xa)
let select (x : atom) (am : 'a amap) : 'a=
  match FStar_List_Tot_Base.assoc x (FStar_Pervasives_Native.fst am) with
  | FStar_Pervasives_Native.Some a1 -> a1
  | uu___ -> FStar_Pervasives_Native.snd am
let update (x : atom) (xa : 'a) (am : 'a amap) : 'a amap=
  (((x, xa) :: (FStar_Pervasives_Native.fst am)),
    (FStar_Pervasives_Native.snd am))
let rec mdenote :
  'a .
    'a FStar_Algebra_CommMonoid_Equiv.equiv ->
      ('a, Obj.t) FStar_Algebra_CommMonoid_Equiv.cm -> 'a amap -> exp -> 'a
  =
  fun eq m am e ->
    match e with
    | Unit -> FStar_Algebra_CommMonoid_Equiv.__proj__CM__item__unit eq m
    | Atom x -> select x am
    | Mult (e1, e2) ->
        FStar_Algebra_CommMonoid_Equiv.__proj__CM__item__mult eq m
          (mdenote eq m am e1) (mdenote eq m am e2)
let rec xsdenote :
  'a .
    'a FStar_Algebra_CommMonoid_Equiv.equiv ->
      ('a, Obj.t) FStar_Algebra_CommMonoid_Equiv.cm ->
        'a amap -> atom Prims.list -> 'a
  =
  fun eq m am xs ->
    match xs with
    | [] -> FStar_Algebra_CommMonoid_Equiv.__proj__CM__item__unit eq m
    | x::[] -> select x am
    | x::xs' ->
        FStar_Algebra_CommMonoid_Equiv.__proj__CM__item__mult eq m
          (select x am) (xsdenote eq m am xs')
let rec flatten (e : exp) : atom Prims.list=
  match e with
  | Unit -> []
  | Atom x -> [x]
  | Mult (e1, e2) -> FStar_List_Tot_Base.op_At (flatten e1) (flatten e2)
type permute = atom Prims.list -> atom Prims.list
type 'p permute_correct = unit
type 'p permute_via_swaps = unit

let sort : permute=
  FStar_List_Tot_Base.sortWith (FStar_List_Tot_Base.compare_of_bool (<))

let canon (e : exp) : atom Prims.list= sort (flatten e)
let rec where_aux (uu___2 : Prims.nat)
  (uu___1 : FStar_Tactics_NamedView.term)
  (uu___ : FStar_Tactics_NamedView.term Prims.list) :
  (Prims.nat FStar_Pervasives_Native.option, unit)
    FStar_Tactics_Effect.tac_repr=
  (fun n x xs ->
     match xs with
     | [] -> Obj.magic (Obj.repr (fun uu___ -> FStar_Pervasives_Native.None))
     | x'::xs' ->
         Obj.magic
           (Obj.repr
              (if term_eq x x'
               then
                 Obj.repr
                   (FStar_Tactics_Effect.lift_div_tac
                      (fun uu___ -> FStar_Pervasives_Native.Some n))
               else Obj.repr (where_aux (n + Prims.int_one) x xs')))) uu___2
    uu___1 uu___
let where :
  FStar_Tactics_NamedView.term ->
    FStar_Tactics_NamedView.term Prims.list ->
      (Prims.nat FStar_Pervasives_Native.option, unit)
        FStar_Tactics_Effect.tac_repr=
  where_aux Prims.int_zero
let fatom (t : FStar_Tactics_NamedView.term)
  (ts : FStar_Tactics_NamedView.term Prims.list)
  (am : FStar_Tactics_NamedView.term amap) :
  ((exp * FStar_Tactics_NamedView.term Prims.list *
     FStar_Tactics_NamedView.term amap),
    unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = where t ts ps in
    match x with
    | FStar_Pervasives_Native.Some v -> ((Atom v), ts, am)
    | FStar_Pervasives_Native.None ->
        let x1 = FStar_List_Tot_Base.length ts in
        let x2 =
          FStar_Tactics_V2_Derived.norm_term
            [Fstarcompiler.FStarC_NormSteps.iota;
            Fstarcompiler.FStarC_NormSteps.zeta] t ps in
        ((Atom x1), (FStar_List_Tot_Base.op_At ts [x2]), (update x1 x2 am))
let rec reification_aux (ts : FStar_Tactics_NamedView.term Prims.list)
  (am : FStar_Tactics_NamedView.term amap)
  (mult : FStar_Tactics_NamedView.term) (unit : FStar_Tactics_NamedView.term)
  (t : FStar_Tactics_NamedView.term) :
  ((exp * FStar_Tactics_NamedView.term Prims.list *
     FStar_Tactics_NamedView.term amap),
    unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = FStar_Tactics_V2_SyntaxHelpers.collect_app t ps in
    match x with
    | (hd, tl) ->
        let x1 = let x2 = FStar_Tactics_NamedView.inspect hd ps in (x2, tl) in
        (match x1 with
         | (FStar_Tactics_NamedView.Tv_FVar fv,
            (t1, FStarC_Reflection_V2_Data.Q_Explicit)::(t2,
                                                         FStarC_Reflection_V2_Data.Q_Explicit)::[])
             ->
             if
               term_eq
                 (FStar_Tactics_NamedView.pack
                    (FStar_Tactics_NamedView.Tv_FVar fv)) mult
             then
               let x2 = reification_aux ts am mult unit t1 ps in
               (match x2 with
                | (e1, ts1, am1) ->
                    let x3 = reification_aux ts1 am1 mult unit t2 ps in
                    (match x3 with
                     | (e2, ts2, am2) -> ((Mult (e1, e2)), ts2, am2)))
             else fatom t ts am ps
         | (uu___, uu___1) ->
             if term_eq t unit then (Unit, ts, am) else fatom t ts am ps)
let reification (eq : FStar_Tactics_NamedView.term)
  (m : FStar_Tactics_NamedView.term)
  (ts : FStar_Tactics_NamedView.term Prims.list)
  (am : FStar_Tactics_NamedView.term amap) (t : FStar_Tactics_NamedView.term)
  :
  ((exp * FStar_Tactics_NamedView.term Prims.list *
     FStar_Tactics_NamedView.term amap),
    unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x =
      FStar_Tactics_V2_Derived.norm_term
        [Fstarcompiler.FStarC_NormSteps.iota;
        Fstarcompiler.FStarC_NormSteps.zeta;
        Fstarcompiler.FStarC_NormSteps.delta]
        (FStarC_Reflection_V2_Builtins.pack_ln
           (FStarC_Reflection_V2_Data.Tv_App
              ((FStarC_Reflection_V2_Builtins.pack_ln
                  (FStarC_Reflection_V2_Data.Tv_FVar
                     (FStarC_Reflection_V2_Builtins.pack_fv
                        ["FStar";
                        "Algebra";
                        "CommMonoid";
                        "Equiv";
                        "__proj__CM__item__mult"]))),
                (m, FStarC_Reflection_V2_Data.Q_Explicit)))) ps in
    let x1 =
      FStar_Tactics_V2_Derived.norm_term
        [Fstarcompiler.FStarC_NormSteps.iota;
        Fstarcompiler.FStarC_NormSteps.zeta;
        Fstarcompiler.FStarC_NormSteps.delta]
        (FStarC_Reflection_V2_Builtins.pack_ln
           (FStarC_Reflection_V2_Data.Tv_App
              ((FStarC_Reflection_V2_Builtins.pack_ln
                  (FStarC_Reflection_V2_Data.Tv_FVar
                     (FStarC_Reflection_V2_Builtins.pack_fv
                        ["FStar";
                        "Algebra";
                        "CommMonoid";
                        "Equiv";
                        "__proj__CM__item__unit"]))),
                (m, FStarC_Reflection_V2_Data.Q_Explicit)))) ps in
    let x2 =
      FStar_Tactics_V2_Derived.norm_term
        [Fstarcompiler.FStarC_NormSteps.iota;
        Fstarcompiler.FStarC_NormSteps.zeta] t ps in
    reification_aux ts am x x1 x2 ps
let rec repeat_cong_right_identity (eq : FStar_Tactics_NamedView.term)
  (m : FStar_Tactics_NamedView.term) :
  (unit, unit) FStar_Tactics_Effect.tac_repr=
  FStar_Tactics_V2_Derived.or_else
    (fun uu___ ->
       FStar_Tactics_V2_Derived.apply_lemma
         (FStarC_Reflection_V2_Builtins.pack_ln
            (FStarC_Reflection_V2_Data.Tv_FVar
               (FStarC_Reflection_V2_Builtins.pack_fv
                  ["FStar";
                  "Algebra";
                  "CommMonoid";
                  "Equiv";
                  "right_identity"]))))
    (fun uu___ ps ->
       FStar_Tactics_V2_Derived.apply_lemma
         (FStarC_Reflection_V2_Builtins.pack_ln
            (FStarC_Reflection_V2_Data.Tv_App
               ((FStarC_Reflection_V2_Builtins.pack_ln
                   (FStarC_Reflection_V2_Data.Tv_FVar
                      (FStarC_Reflection_V2_Builtins.pack_fv
                         ["FStar";
                         "Algebra";
                         "CommMonoid";
                         "Equiv";
                         "__proj__CM__item__congruence"]))),
                 (m, FStarC_Reflection_V2_Data.Q_Explicit)))) ps;
       FStar_Tactics_V2_Logic.split () ps;
       FStar_Tactics_V2_Derived.apply_lemma
         (FStarC_Reflection_V2_Builtins.pack_ln
            (FStarC_Reflection_V2_Data.Tv_App
               ((FStarC_Reflection_V2_Builtins.pack_ln
                   (FStarC_Reflection_V2_Data.Tv_FVar
                      (FStarC_Reflection_V2_Builtins.pack_fv
                         ["FStar";
                         "Algebra";
                         "CommMonoid";
                         "Equiv";
                         "__proj__EQ__item__reflexivity"]))),
                 (eq, FStarC_Reflection_V2_Data.Q_Explicit)))) ps;
       repeat_cong_right_identity eq m ps)
let rec convert_map (m : (atom * FStar_Tactics_NamedView.term) Prims.list) :
  FStar_Tactics_NamedView.term=
  match m with
  | [] ->
      FStarC_Reflection_V2_Builtins.pack_ln
        (FStarC_Reflection_V2_Data.Tv_FVar
           (FStarC_Reflection_V2_Builtins.pack_fv ["Prims"; "Nil"]))
  | (a, t)::ps ->
      let a1 =
        FStar_Tactics_NamedView.pack
          (FStar_Tactics_NamedView.Tv_Const
             (FStarC_Reflection_V2_Data.C_Int a)) in
      let uu___ = convert_map ps in
      let uu___1 = t in
      let uu___2 = a1 in
      FStarC_Reflection_V2_Builtins.pack_ln
        (FStarC_Reflection_V2_Data.Tv_App
           ((FStarC_Reflection_V2_Builtins.pack_ln
               (FStarC_Reflection_V2_Data.Tv_App
                  ((FStarC_Reflection_V2_Builtins.pack_ln
                      (FStarC_Reflection_V2_Data.Tv_FVar
                         (FStarC_Reflection_V2_Builtins.pack_fv
                            ["Prims"; "Cons"]))),
                    ((FStarC_Reflection_V2_Builtins.pack_ln
                        (FStarC_Reflection_V2_Data.Tv_App
                           ((FStarC_Reflection_V2_Builtins.pack_ln
                               (FStarC_Reflection_V2_Data.Tv_App
                                  ((FStarC_Reflection_V2_Builtins.pack_ln
                                      (FStarC_Reflection_V2_Data.Tv_FVar
                                         (FStarC_Reflection_V2_Builtins.pack_fv
                                            ["FStar";
                                            "Pervasives";
                                            "Native";
                                            "Mktuple2"]))),
                                    (uu___2,
                                      FStarC_Reflection_V2_Data.Q_Explicit)))),
                             (uu___1, FStarC_Reflection_V2_Data.Q_Explicit)))),
                      FStarC_Reflection_V2_Data.Q_Explicit)))),
             (uu___, FStarC_Reflection_V2_Data.Q_Explicit)))
let convert_am (am : FStar_Tactics_NamedView.term amap) :
  FStar_Tactics_NamedView.term=
  let uu___ = am in
  match uu___ with
  | (map, def) ->
      let uu___1 = def in
      let uu___2 = convert_map map in
      FStarC_Reflection_V2_Builtins.pack_ln
        (FStarC_Reflection_V2_Data.Tv_App
           ((FStarC_Reflection_V2_Builtins.pack_ln
               (FStarC_Reflection_V2_Data.Tv_App
                  ((FStarC_Reflection_V2_Builtins.pack_ln
                      (FStarC_Reflection_V2_Data.Tv_FVar
                         (FStarC_Reflection_V2_Builtins.pack_fv
                            ["FStar"; "Pervasives"; "Native"; "Mktuple2"]))),
                    (uu___2, FStarC_Reflection_V2_Data.Q_Explicit)))),
             (uu___1, FStarC_Reflection_V2_Data.Q_Explicit)))
let rec quote_exp (e : exp) : FStar_Tactics_NamedView.term=
  match e with
  | Unit ->
      FStarC_Reflection_V2_Builtins.pack_ln
        (FStarC_Reflection_V2_Data.Tv_FVar
           (FStarC_Reflection_V2_Builtins.pack_fv
              ["FStar"; "Tactics"; "CanonCommMonoidSimple"; "Equiv"; "Unit"]))
  | Mult (e1, e2) ->
      let uu___ = quote_exp e2 in
      let uu___1 = quote_exp e1 in
      FStarC_Reflection_V2_Builtins.pack_ln
        (FStarC_Reflection_V2_Data.Tv_App
           ((FStarC_Reflection_V2_Builtins.pack_ln
               (FStarC_Reflection_V2_Data.Tv_App
                  ((FStarC_Reflection_V2_Builtins.pack_ln
                      (FStarC_Reflection_V2_Data.Tv_FVar
                         (FStarC_Reflection_V2_Builtins.pack_fv
                            ["FStar";
                            "Tactics";
                            "CanonCommMonoidSimple";
                            "Equiv";
                            "Mult"]))),
                    (uu___1, FStarC_Reflection_V2_Data.Q_Explicit)))),
             (uu___, FStarC_Reflection_V2_Data.Q_Explicit)))
  | Atom n ->
      let nt =
        FStar_Tactics_NamedView.pack
          (FStar_Tactics_NamedView.Tv_Const
             (FStarC_Reflection_V2_Data.C_Int n)) in
      FStarC_Reflection_V2_Builtins.pack_ln
        (FStarC_Reflection_V2_Data.Tv_App
           ((FStarC_Reflection_V2_Builtins.pack_ln
               (FStarC_Reflection_V2_Data.Tv_FVar
                  (FStarC_Reflection_V2_Builtins.pack_fv
                     ["FStar";
                     "Tactics";
                     "CanonCommMonoidSimple";
                     "Equiv";
                     "Atom"]))), (nt, FStarC_Reflection_V2_Data.Q_Explicit)))
let canon_lhs_rhs (eq : FStar_Tactics_NamedView.term)
  (m : FStar_Tactics_NamedView.term) (lhs : FStar_Tactics_NamedView.term)
  (rhs : FStar_Tactics_NamedView.term) :
  (unit, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x =
      FStar_Tactics_V2_Derived.norm_term
        [Fstarcompiler.FStarC_NormSteps.iota;
        Fstarcompiler.FStarC_NormSteps.zeta;
        Fstarcompiler.FStarC_NormSteps.delta]
        (FStarC_Reflection_V2_Builtins.pack_ln
           (FStarC_Reflection_V2_Data.Tv_App
              ((FStarC_Reflection_V2_Builtins.pack_ln
                  (FStarC_Reflection_V2_Data.Tv_FVar
                     (FStarC_Reflection_V2_Builtins.pack_fv
                        ["FStar";
                        "Algebra";
                        "CommMonoid";
                        "Equiv";
                        "__proj__CM__item__unit"]))),
                (m, FStarC_Reflection_V2_Data.Q_Explicit)))) ps in
    let x1 = const x in
    let x2 = reification eq m [] x1 lhs ps in
    match x2 with
    | (r1, ts, am) ->
        let x3 = reification eq m ts am rhs ps in
        (match x3 with
         | (r2, uu___, am1) ->
             let x4 = convert_am am1 in
             let x5 = quote_exp r1 in
             let x6 = quote_exp r2 in
             (FStar_Tactics_V2_Derived.change_sq
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
                                              "Algebra";
                                              "CommMonoid";
                                              "Equiv";
                                              "__proj__EQ__item__eq"]))),
                                      (eq,
                                        FStarC_Reflection_V2_Data.Q_Explicit)))),
                               ((FStarC_Reflection_V2_Builtins.pack_ln
                                   (FStarC_Reflection_V2_Data.Tv_App
                                      ((FStarC_Reflection_V2_Builtins.pack_ln
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
                                                                    "CanonCommMonoidSimple";
                                                                    "Equiv";
                                                                    "mdenote"]))),
                                                             (eq,
                                                               FStarC_Reflection_V2_Data.Q_Explicit)))),
                                                      (m,
                                                        FStarC_Reflection_V2_Data.Q_Explicit)))),
                                               (x4,
                                                 FStarC_Reflection_V2_Data.Q_Explicit)))),
                                        (x5,
                                          FStarC_Reflection_V2_Data.Q_Explicit)))),
                                 FStarC_Reflection_V2_Data.Q_Explicit)))),
                        ((FStarC_Reflection_V2_Builtins.pack_ln
                            (FStarC_Reflection_V2_Data.Tv_App
                               ((FStarC_Reflection_V2_Builtins.pack_ln
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
                                                              "CanonCommMonoidSimple";
                                                              "Equiv";
                                                              "mdenote"]))),
                                                      (eq,
                                                        FStarC_Reflection_V2_Data.Q_Explicit)))),
                                               (m,
                                                 FStarC_Reflection_V2_Data.Q_Explicit)))),
                                        (x4,
                                          FStarC_Reflection_V2_Data.Q_Explicit)))),
                                 (x6, FStarC_Reflection_V2_Data.Q_Explicit)))),
                          FStarC_Reflection_V2_Data.Q_Explicit)))) ps;
              FStar_Tactics_V2_Derived.apply
                (FStarC_Reflection_V2_Builtins.pack_ln
                   (FStarC_Reflection_V2_Data.Tv_FVar
                      (FStarC_Reflection_V2_Builtins.pack_fv
                         ["FStar";
                         "Tactics";
                         "CanonCommMonoidSimple";
                         "Equiv";
                         "monoid_reflect"]))) ps;
              FStarC_Tactics_V2_Builtins.norm
                [Fstarcompiler.FStarC_NormSteps.iota;
                Fstarcompiler.FStarC_NormSteps.zeta;
                Fstarcompiler.FStarC_NormSteps.delta_only
                  ["FStar.Tactics.CanonCommMonoidSimple.Equiv.canon";
                  "FStar.Tactics.CanonCommMonoidSimple.Equiv.xsdenote";
                  "FStar.Tactics.CanonCommMonoidSimple.Equiv.flatten";
                  "FStar.Tactics.CanonCommMonoidSimple.Equiv.sort";
                  "FStar.Tactics.CanonCommMonoidSimple.Equiv.select";
                  "FStar.List.Tot.Base.assoc";
                  "FStar.Pervasives.Native.fst";
                  "FStar.Pervasives.Native.__proj__Mktuple2__item___1";
                  "FStar.List.Tot.Base.op_At";
                  "FStar.List.Tot.Base.append";
                  "FStar.List.Tot.Base.sortWith";
                  "FStar.List.Tot.Base.partition";
                  "FStar.List.Tot.Base.bool_of_compare";
                  "FStar.List.Tot.Base.compare_of_bool"];
                Fstarcompiler.FStarC_NormSteps.primops] ps;
              FStar_Tactics_V2_Derived.or_else
                (fun uu___1 ->
                   FStar_Tactics_V2_Derived.apply_lemma
                     (FStarC_Reflection_V2_Builtins.pack_ln
                        (FStarC_Reflection_V2_Data.Tv_App
                           ((FStarC_Reflection_V2_Builtins.pack_ln
                               (FStarC_Reflection_V2_Data.Tv_FVar
                                  (FStarC_Reflection_V2_Builtins.pack_fv
                                     ["FStar";
                                     "Algebra";
                                     "CommMonoid";
                                     "Equiv";
                                     "__proj__EQ__item__reflexivity"]))),
                             (eq, FStarC_Reflection_V2_Data.Q_Explicit)))))
                (fun uu___1 -> repeat_cong_right_identity eq m) ps))
let canon_monoid (eq : FStar_Tactics_NamedView.term)
  (m : FStar_Tactics_NamedView.term) :
  (unit, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    FStarC_Tactics_V2_Builtins.norm
      [Fstarcompiler.FStarC_NormSteps.iota;
      Fstarcompiler.FStarC_NormSteps.zeta] ps;
    (let x1 = FStar_Tactics_V2_Derived.cur_goal () ps in
     let x2 = FStar_Tactics_V2_SyntaxHelpers.collect_app x1 ps in
     match x2 with
     | (sq, rel_xy) ->
         (match rel_xy with
          | (rel_xy1, uu___)::[] ->
              let x3 = FStar_Tactics_V2_SyntaxHelpers.collect_app rel_xy1 ps in
              (match x3 with
               | (rel, xy) ->
                   if (FStar_List_Tot_Base.length xy) >= (Prims.of_int (2))
                   then
                     (match ((FStar_List_Tot_Base.index xy
                                ((FStar_List_Tot_Base.length xy) -
                                   (Prims.of_int (2)))),
                              (FStar_List_Tot_Base.index xy
                                 ((FStar_List_Tot_Base.length xy) -
                                    Prims.int_one)))
                      with
                      | ((lhs, FStarC_Reflection_V2_Data.Q_Explicit),
                         (rhs, FStarC_Reflection_V2_Data.Q_Explicit)) ->
                          canon_lhs_rhs eq m lhs rhs ps
                      | uu___1 ->
                          FStar_Tactics_V2_Derived.fail
                            "Goal should have been an application of a binary relation to 2 explicit arguments"
                            ps)
                   else
                     FStar_Tactics_V2_Derived.fail
                       "Goal should have been an application of a binary relation to n implicit and 2 explicit arguments"
                       ps)
          | uu___ ->
              FStar_Tactics_V2_Derived.fail
                "Goal should be squash applied to a binary relation" ps))
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.CanonCommMonoidSimple.Equiv.canon_monoid"
    (Prims.of_int (3))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_2
               "FStar.Tactics.CanonCommMonoidSimple.Equiv.canon_monoid (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_2
                  canon_monoid)
               Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term
               Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term
               Fstarcompiler.FStarC_Syntax_Embeddings.e_unit psc ncb us args)
