open Prims
let term_eq :
  FStarC_Reflection_Types.term -> FStarC_Reflection_Types.term -> Prims.bool=
  FStar_Reflection_TermEq_Simple.term_eq
let dump (m : Prims.string) : (unit, Obj.t) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = FStarC_Tactics_V2_Builtins.debugging () ps in
    if x then FStarC_Tactics_V2_Builtins.dump m ps else ()
type atom = Prims.nat
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
let rec mdenote : 'a . 'a FStar_Algebra_CommMonoid.cm -> 'a amap -> exp -> 'a
  =
  fun m am e ->
    match e with
    | Unit -> FStar_Algebra_CommMonoid.__proj__CM__item__unit m
    | Atom x -> select x am
    | Mult (e1, e2) ->
        FStar_Algebra_CommMonoid.__proj__CM__item__mult m (mdenote m am e1)
          (mdenote m am e2)
let rec xsdenote :
  'a . 'a FStar_Algebra_CommMonoid.cm -> 'a amap -> atom Prims.list -> 'a =
  fun m am xs ->
    match xs with
    | [] -> FStar_Algebra_CommMonoid.__proj__CM__item__unit m
    | x::[] -> select x am
    | x::xs' ->
        FStar_Algebra_CommMonoid.__proj__CM__item__mult m (select x am)
          (xsdenote m am xs')
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
let rec where_aux (n : Prims.nat) (x : FStar_Tactics_NamedView.term)
  (xs : FStar_Tactics_NamedView.term Prims.list) :
  (Prims.nat FStar_Pervasives_Native.option, Obj.t)
    FStar_Tactics_Effect.tac_repr=
  match xs with
  | [] -> (fun uu___ -> FStar_Pervasives_Native.None)
  | x'::xs' ->
      if term_eq x x'
      then
        FStar_Tactics_Effect.lift_div_tac ()
          (fun uu___ -> FStar_Pervasives_Native.Some n)
      else where_aux (n + Prims.int_one) x xs'
let where :
  FStar_Tactics_NamedView.term ->
    FStar_Tactics_NamedView.term Prims.list ->
      (Prims.nat FStar_Pervasives_Native.option, Obj.t)
        FStar_Tactics_Effect.tac_repr=
  where_aux Prims.int_zero
let rec reification_aux :
  'a .
    FStar_Tactics_NamedView.term Prims.list ->
      'a amap ->
        FStar_Tactics_NamedView.term ->
          FStar_Tactics_NamedView.term ->
            FStar_Tactics_NamedView.term ->
              ((exp * FStar_Tactics_NamedView.term Prims.list * 'a amap),
                Obj.t) FStar_Tactics_Effect.tac_repr
  =
  fun ts am mult unit t ps ->
    let x = FStar_Reflection_V2_Derived_Lemmas.collect_app_ref t in
    match x with
    | (hd, tl) ->
        let x1 t1 ts1 am1 ps1 =
          let x2 = where t1 ts1 ps1 in
          match x2 with
          | FStar_Pervasives_Native.Some v -> ((Atom v), ts1, am1)
          | FStar_Pervasives_Native.None ->
              let x3 = FStar_List_Tot_Base.length ts1 in
              let x4 = FStarC_Tactics_V2_Builtins.unquote t1 ps1 in
              ((Atom x3), (FStar_List_Tot_Base.op_At ts1 [t1]),
                (update x3 x4 am1)) in
        let x2 =
          let x3 = FStar_Tactics_NamedView.inspect hd ps in
          (x3, (FStar_List_Tot_Base.list_unref () tl)) in
        (match x2 with
         | (FStar_Tactics_NamedView.Tv_FVar fv,
            (t1, FStarC_Reflection_V2_Data.Q_Explicit)::(t2,
                                                         FStarC_Reflection_V2_Data.Q_Explicit)::[])
             ->
             if
               term_eq
                 (FStar_Tactics_NamedView.pack
                    (FStar_Tactics_NamedView.Tv_FVar fv)) mult
             then
               let x3 = reification_aux ts am mult unit t1 ps in
               (match x3 with
                | (e1, ts1, am1) ->
                    let x4 = reification_aux ts1 am1 mult unit t2 ps in
                    (match x4 with
                     | (e2, ts2, am2) -> ((Mult (e1, e2)), ts2, am2)))
             else x1 t ts am ps
         | (uu___, uu___1) ->
             if term_eq t unit then (Unit, ts, am) else x1 t ts am ps)
let reification (m : 'a FStar_Algebra_CommMonoid.cm)
  (ts : FStar_Tactics_NamedView.term Prims.list) (am : 'a amap)
  (t : FStar_Tactics_NamedView.term) :
  ((exp * FStar_Tactics_NamedView.term Prims.list * 'a amap), Obj.t)
    FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x =
      let x1 =
        Obj.magic (failwith "Cannot evaluate open quotation at runtime") in
      FStar_Tactics_V2_Derived.norm_term
        [FStarC_NormSteps.delta;
        FStarC_NormSteps.zeta;
        FStarC_NormSteps.iota] x1 ps in
    let x1 =
      let x2 =
        Obj.magic (failwith "Cannot evaluate open quotation at runtime") in
      FStar_Tactics_V2_Derived.norm_term
        [FStarC_NormSteps.delta;
        FStarC_NormSteps.zeta;
        FStarC_NormSteps.iota] x2 ps in
    let x2 =
      FStar_Tactics_V2_Derived.norm_term
        [FStarC_NormSteps.delta;
        FStarC_NormSteps.zeta;
        FStarC_NormSteps.iota] t ps in
    reification_aux ts am x x1 x2 ps
let canon_monoid (m : 'a FStar_Algebra_CommMonoid.cm) :
  (unit, Obj.t) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    FStarC_Tactics_V2_Builtins.norm [] ps;
    (let x1 =
       let x2 = FStar_Tactics_V2_Derived.cur_goal () ps in
       FStar_Reflection_V2_Formula.term_as_formula x2 ps in
     match x1 with
     | FStar_Reflection_V2_Formula.Comp
         (FStar_Reflection_V2_Formula.Eq (FStar_Pervasives_Native.Some t),
          t1, t2)
         ->
         let x2 =
           let x3 =
             Obj.magic (failwith "Cannot evaluate open quotation at runtime") in
           term_eq t x3 in
         if x2
         then
           let x3 =
             reification m []
               (const (FStar_Algebra_CommMonoid.__proj__CM__item__unit m)) t1
               ps in
           (match x3 with
            | (r1, ts, am) ->
                let x4 = reification m ts am t2 ps in
                (match x4 with
                 | (r2, uu___, am1) ->
                     ((let x6 =
                         let x7 =
                           let x8 =
                             Obj.magic
                               (failwith
                                  "Cannot evaluate open quotation at runtime") in
                           FStarC_Tactics_V2_Builtins.term_to_string x8 ps in
                         Prims.strcat "am =" x7 in
                       dump x6 ps);
                      (let x7 =
                         Obj.magic
                           (failwith
                              "Cannot evaluate open quotation at runtime") in
                       FStar_Tactics_V2_Derived.change_sq x7 ps);
                      FStar_Tactics_V2_Derived.apply
                        (FStarC_Reflection_V2_Builtins.pack_ln
                           (FStarC_Reflection_V2_Data.Tv_FVar
                              (FStarC_Reflection_V2_Builtins.pack_fv
                                 ["FStar";
                                 "Tactics";
                                 "CanonCommMonoidSimple";
                                 "monoid_reflect"]))) ps;
                      FStarC_Tactics_V2_Builtins.norm
                        [FStarC_NormSteps.delta_only
                           ["FStar.Tactics.CanonCommMonoidSimple.canon";
                           "FStar.Tactics.CanonCommMonoidSimple.xsdenote";
                           "FStar.Tactics.CanonCommMonoidSimple.flatten";
                           "FStar.Tactics.CanonCommMonoidSimple.sort";
                           "FStar.Tactics.CanonCommMonoidSimple.select";
                           "FStar.List.Tot.Base.assoc";
                           "FStar.Pervasives.Native.fst";
                           "FStar.Pervasives.Native.__proj__Mktuple2__item___1";
                           "FStar.List.Tot.Base.op_At";
                           "FStar.List.Tot.Base.append";
                           "FStar.List.Tot.Base.sortWith";
                           "FStar.List.Tot.Base.partition";
                           "FStar.List.Tot.Base.bool_of_compare";
                           "FStar.List.Tot.Base.compare_of_bool"];
                        FStarC_NormSteps.primops] ps)))
         else
           FStar_Tactics_V2_Derived.fail
             "Goal should be an equality at the right monoid type" ps
     | uu___ -> FStar_Tactics_V2_Derived.fail "Goal should be an equality" ps)
