open Prims
let term_eq :
  FStarC_Reflection_Types.term -> FStarC_Reflection_Types.term -> Prims.bool=
  FStar_Reflection_TermEq_Simple.term_eq
let dump (m : Prims.string) (ps : FStarC_Tactics_Types.ref_proofstate) :
  unit=
  let x = FStarC_Tactics_V2_Builtins.debugging () ps in
  if x then FStarC_Tactics_V2_Builtins.dump m ps else ()
type var = Prims.nat
type exp =
  | Unit 
  | Var of var 
  | Mult of exp * exp 
let uu___is_Unit (projectee : exp) : Prims.bool=
  match projectee with | Unit -> true | uu___ -> false
let uu___is_Var (projectee : exp) : Prims.bool=
  match projectee with | Var _0 -> true | uu___ -> false
let __proj__Var__item___0 (projectee : exp) : var=
  match projectee with | Var _0 -> _0
let uu___is_Mult (projectee : exp) : Prims.bool=
  match projectee with | Mult (_0, _1) -> true | uu___ -> false
let __proj__Mult__item___0 (projectee : exp) : exp=
  match projectee with | Mult (_0, _1) -> _0
let __proj__Mult__item___1 (projectee : exp) : exp=
  match projectee with | Mult (_0, _1) -> _1
let rec exp_to_string (e : exp) : Prims.string=
  match e with
  | Unit -> "Unit"
  | Var x -> Prims.strcat "Var " (Prims.string_of_int x)
  | Mult (e1, e2) ->
      Prims.strcat "Mult ("
        (Prims.strcat (exp_to_string e1)
           (Prims.strcat ") (" (Prims.strcat (exp_to_string e2) ")")))
type ('a, 'b) vmap = ((var * ('a * 'b)) Prims.list * ('a * 'b))
let const (xa : 'a) (xb : 'b) : ('a, 'b) vmap= ([], (xa, xb))
let select (x : var) (vm : ('a, 'b) vmap) : 'a=
  match FStar_List_Tot_Base.assoc x (FStar_Pervasives_Native.fst vm) with
  | FStar_Pervasives_Native.Some (a1, uu___) -> a1
  | uu___ -> FStar_Pervasives_Native.fst (FStar_Pervasives_Native.snd vm)
let select_extra (x : var) (vm : ('a, 'b) vmap) : 'b=
  match FStar_List_Tot_Base.assoc x (FStar_Pervasives_Native.fst vm) with
  | FStar_Pervasives_Native.Some (uu___, b1) -> b1
  | uu___ -> FStar_Pervasives_Native.snd (FStar_Pervasives_Native.snd vm)
let update (x : var) (xa : 'a) (xb : 'b) (vm : ('a, 'b) vmap) :
  ('a, 'b) vmap=
  (((x, (xa, xb)) :: (FStar_Pervasives_Native.fst vm)),
    (FStar_Pervasives_Native.snd vm))
let rec mdenote :
  'a 'b . 'a FStar_Algebra_CommMonoid.cm -> ('a, 'b) vmap -> exp -> 'a =
  fun m vm e ->
    match e with
    | Unit ->
        (match m with
         | FStar_Algebra_CommMonoid.CM
             (unit, mult, identity, associativity, commutativity) -> unit)
    | Var x -> select x vm
    | Mult (e1, e2) ->
        ((match m with
          | FStar_Algebra_CommMonoid.CM
              (unit, mult, identity, associativity, commutativity) -> mult))
          (mdenote m vm e1) (mdenote m vm e2)
let rec xsdenote :
  'a 'b .
    'a FStar_Algebra_CommMonoid.cm -> ('a, 'b) vmap -> var Prims.list -> 'a
  =
  fun m vm xs ->
    match xs with
    | [] ->
        (match m with
         | FStar_Algebra_CommMonoid.CM
             (unit, mult, identity, associativity, commutativity) -> unit)
    | x::[] -> select x vm
    | x::xs' ->
        ((match m with
          | FStar_Algebra_CommMonoid.CM
              (unit, mult, identity, associativity, commutativity) -> mult))
          (select x vm) (xsdenote m vm xs')
let rec flatten (e : exp) : var Prims.list=
  match e with
  | Unit -> []
  | Var x -> [x]
  | Mult (e1, e2) -> FStar_List_Tot_Base.op_At (flatten e1) (flatten e2)
type 'b permute =
  unit -> (Obj.t, 'b) vmap -> var Prims.list -> var Prims.list
type ('b, 'p) permute_correct = unit
type ('b, 'p) permute_via_swaps = unit

let sort : unit permute=
  fun a vm ->
    FStar_List_Tot_Base.sortWith (FStar_List_Tot_Base.compare_of_bool (<))
let sortWith (f : Prims.nat -> Prims.nat -> Prims.int) : 'b permute=
  fun a vm -> FStar_List_Tot_Base.sortWith f


let canon (vm : ('a, 'b) vmap) (p : 'b permute) (e : exp) : var Prims.list=
  p () (Obj.magic vm) (flatten e)
let rec where_aux (n : Prims.nat) (x : FStar_Tactics_NamedView.term)
  (xs : FStar_Tactics_NamedView.term Prims.list) :
  FStarC_Tactics_Types.ref_proofstate ->
    Prims.nat FStar_Pervasives_Native.option=
  match xs with
  | [] -> (fun uu___ -> FStar_Pervasives_Native.None)
  | x'::xs' ->
      if term_eq x x'
      then (fun uu___ -> FStar_Pervasives_Native.Some n)
      else where_aux (n + Prims.int_one) x xs'
let where :
  FStar_Tactics_NamedView.term ->
    FStar_Tactics_NamedView.term Prims.list ->
      FStarC_Tactics_Types.ref_proofstate ->
        Prims.nat FStar_Pervasives_Native.option=
  where_aux Prims.int_zero
let rec reification_aux :
  'a 'b .
    (FStar_Tactics_NamedView.term ->
       FStarC_Tactics_Types.ref_proofstate -> 'a)
      ->
      FStar_Tactics_NamedView.term Prims.list ->
        ('a, 'b) vmap ->
          (FStar_Tactics_NamedView.term ->
             FStarC_Tactics_Types.ref_proofstate -> 'b)
            ->
            FStar_Tactics_NamedView.term ->
              FStar_Tactics_NamedView.term ->
                FStar_Tactics_NamedView.term ->
                  FStarC_Tactics_Types.ref_proofstate ->
                    (exp * FStar_Tactics_NamedView.term Prims.list * (
                      'a, 'b) vmap)
  =
  fun unquotea ts vm f mult unit t ps ->
    let x = FStar_Reflection_V2_Derived_Lemmas.collect_app_ref t in
    match x with
    | (hd, tl) ->
        let x1 t1 ts1 vm1 ps1 =
          let x2 = where t1 ts1 ps1 in
          match x2 with
          | FStar_Pervasives_Native.Some v -> ((Var v), ts1, vm1)
          | FStar_Pervasives_Native.None ->
              let x3 = FStar_List_Tot_Base.length ts1 in
              let x4 = unquotea t1 ps1 in
              let x5 = let x6 = f t1 ps1 in update x3 x4 x6 vm1 in
              ((Var x3), (FStar_List_Tot_Base.op_At ts1 [t1]), x5) in
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
               let x3 = reification_aux unquotea ts vm f mult unit t1 ps in
               (match x3 with
                | (e1, ts1, vm1) ->
                    let x4 =
                      reification_aux unquotea ts1 vm1 f mult unit t2 ps in
                    (match x4 with
                     | (e2, ts2, vm2) -> ((Mult (e1, e2)), ts2, vm2)))
             else x1 t ts vm ps
         | (uu___, uu___1) ->
             if term_eq t unit then (Unit, ts, vm) else x1 t ts vm ps)
let reification
  (f :
    FStar_Tactics_NamedView.term -> FStarC_Tactics_Types.ref_proofstate -> 'b)
  (def : 'b) (a : unit)
  (unquotea :
    FStar_Tactics_NamedView.term ->
      FStarC_Tactics_Types.ref_proofstate -> Obj.t)
  (quotea :
    Obj.t ->
      FStarC_Tactics_Types.ref_proofstate -> FStar_Tactics_NamedView.term)
  (tmult : FStar_Tactics_NamedView.term)
  (tunit : FStar_Tactics_NamedView.term) (munit : Obj.t)
  (ts : FStar_Tactics_NamedView.term Prims.list)
  (ps : FStarC_Tactics_Types.ref_proofstate) :
  (exp Prims.list * (Obj.t, 'b) vmap)=
  let x =
    FStar_Tactics_V2_Derived.norm_term
      [FStarC_NormSteps.delta; FStarC_NormSteps.zeta; FStarC_NormSteps.iota]
      tmult ps in
  let x1 =
    FStar_Tactics_V2_Derived.norm_term
      [FStarC_NormSteps.delta; FStarC_NormSteps.zeta; FStarC_NormSteps.iota]
      tunit ps in
  let x2 =
    FStar_Tactics_Util.map
      (FStar_Tactics_V2_Derived.norm_term
         [FStarC_NormSteps.delta;
         FStarC_NormSteps.zeta;
         FStarC_NormSteps.iota]) ts ps in
  let x3 =
    FStar_Tactics_Util.fold_left
      (fun uu___ t ->
         match uu___ with
         | (es, vs, vm) ->
             (fun ps1 ->
                let x4 = reification_aux unquotea vs vm f x x1 t ps1 in
                match x4 with | (e, vs1, vm1) -> ((e :: es), vs1, vm1)))
      ([], [], (const munit def)) x2 ps in
  match x3 with | (es, uu___, vm) -> ((FStar_List_Tot_Base.rev es), vm)
let rec term_mem (x : FStar_Tactics_NamedView.term)
  (uu___ : FStar_Tactics_NamedView.term Prims.list) :
  FStarC_Tactics_Types.ref_proofstate -> Prims.bool=
  match uu___ with
  | [] -> (fun uu___1 -> false)
  | hd::tl -> if term_eq hd x then (fun uu___1 -> true) else term_mem x tl
let unfold_topdown (ts : FStar_Tactics_NamedView.term Prims.list)
  (ps : FStarC_Tactics_Types.ref_proofstate) : unit=
  let x s ps1 = let x1 = term_mem s ts ps1 in (x1, Prims.int_zero) in
  let x1 uu___ ps1 =
    FStarC_Tactics_V2_Builtins.norm [FStarC_NormSteps.delta] ps1;
    FStar_Tactics_V2_Derived.trefl () ps1 in
  FStar_Tactics_V2_Derived.topdown_rewrite x x1 ps
let rec quote_list :
  'a .
    FStar_Tactics_NamedView.term ->
      ('a ->
         FStarC_Tactics_Types.ref_proofstate -> FStar_Tactics_NamedView.term)
        ->
        'a Prims.list ->
          FStarC_Tactics_Types.ref_proofstate -> FStar_Tactics_NamedView.term
  =
  fun ta quotea xs ->
    match xs with
    | [] ->
        (fun uu___ ->
           FStar_Reflection_V2_Derived.mk_app
             (FStarC_Reflection_V2_Builtins.pack_ln
                (FStarC_Reflection_V2_Data.Tv_FVar
                   (FStarC_Reflection_V2_Builtins.pack_fv ["Prims"; "Nil"])))
             [(ta, FStarC_Reflection_V2_Data.Q_Implicit)])
    | x::xs' ->
        (fun ps ->
           let x1 =
             let x2 =
               let x3 =
                 let x4 = quotea x ps in
                 (x4, FStarC_Reflection_V2_Data.Q_Explicit) in
               let x4 =
                 let x5 =
                   let x6 = quote_list ta quotea xs' ps in
                   (x6, FStarC_Reflection_V2_Data.Q_Explicit) in
                 [x5] in
               x3 :: x4 in
             (ta, FStarC_Reflection_V2_Data.Q_Implicit) :: x2 in
           FStar_Reflection_V2_Derived.mk_app
             (FStarC_Reflection_V2_Builtins.pack_ln
                (FStarC_Reflection_V2_Data.Tv_FVar
                   (FStarC_Reflection_V2_Builtins.pack_fv ["Prims"; "Cons"])))
             x1)
let quote_vm (ta : FStar_Tactics_NamedView.term)
  (tb : FStar_Tactics_NamedView.term)
  (quotea :
    'a -> FStarC_Tactics_Types.ref_proofstate -> FStar_Tactics_NamedView.term)
  (quoteb :
    'b -> FStarC_Tactics_Types.ref_proofstate -> FStar_Tactics_NamedView.term)
  (vm : ('a, 'b) vmap) (ps : FStarC_Tactics_Types.ref_proofstate) :
  FStar_Tactics_NamedView.term=
  let x p ps1 =
    let x1 =
      let x2 =
        let x3 =
          let x4 =
            let x5 = quotea (FStar_Pervasives_Native.fst p) ps1 in
            (x5, FStarC_Reflection_V2_Data.Q_Explicit) in
          let x5 =
            let x6 =
              let x7 = quoteb (FStar_Pervasives_Native.snd p) ps1 in
              (x7, FStarC_Reflection_V2_Data.Q_Explicit) in
            [x6] in
          x4 :: x5 in
        (tb, FStarC_Reflection_V2_Data.Q_Implicit) :: x3 in
      (ta, FStarC_Reflection_V2_Data.Q_Implicit) :: x2 in
    FStar_Reflection_V2_Derived.mk_app
      (FStarC_Reflection_V2_Builtins.pack_ln
         (FStarC_Reflection_V2_Data.Tv_FVar
            (FStarC_Reflection_V2_Builtins.pack_fv
               ["FStar"; "Pervasives"; "Native"; "Mktuple2"]))) x1 in
  let x1 =
    FStar_Reflection_V2_Derived.mk_e_app
      (FStarC_Reflection_V2_Builtins.pack_ln
         (FStarC_Reflection_V2_Data.Tv_FVar
            (FStarC_Reflection_V2_Builtins.pack_fv
               ["FStar"; "Pervasives"; "Native"; "tuple2"]))) [ta; tb] in
  let x2 p ps1 =
    let x3 =
      let x4 =
        let x5 =
          let x6 =
            let x7 =
              let x8 = x (FStar_Pervasives_Native.snd p) ps1 in
              (x8, FStarC_Reflection_V2_Data.Q_Explicit) in
            [x7] in
          ((FStar_Tactics_NamedView.pack
              (FStar_Tactics_NamedView.Tv_Const
                 (FStarC_Reflection_V2_Data.C_Int
                    (FStar_Pervasives_Native.fst p)))),
            FStarC_Reflection_V2_Data.Q_Explicit) :: x6 in
        (x1, FStarC_Reflection_V2_Data.Q_Implicit) :: x5 in
      ((FStarC_Reflection_V2_Builtins.pack_ln
          (FStarC_Reflection_V2_Data.Tv_FVar
             (FStarC_Reflection_V2_Builtins.pack_fv ["Prims"; "nat"]))),
        FStarC_Reflection_V2_Data.Q_Implicit) :: x4 in
    FStar_Reflection_V2_Derived.mk_app
      (FStarC_Reflection_V2_Builtins.pack_ln
         (FStarC_Reflection_V2_Data.Tv_FVar
            (FStarC_Reflection_V2_Builtins.pack_fv
               ["FStar"; "Pervasives"; "Native"; "Mktuple2"]))) x3 in
  let x3 =
    FStar_Reflection_V2_Derived.mk_e_app
      (FStarC_Reflection_V2_Builtins.pack_ln
         (FStarC_Reflection_V2_Data.Tv_FVar
            (FStarC_Reflection_V2_Builtins.pack_fv
               ["FStar"; "Pervasives"; "Native"; "tuple2"])))
      [FStarC_Reflection_V2_Builtins.pack_ln
         (FStarC_Reflection_V2_Data.Tv_FVar
            (FStarC_Reflection_V2_Builtins.pack_fv ["Prims"; "nat"]));
      x1] in
  let x4 = quote_list x3 x2 (FStar_Pervasives_Native.fst vm) ps in
  let x5 = x (FStar_Pervasives_Native.snd vm) ps in
  FStar_Reflection_V2_Derived.mk_app
    (FStarC_Reflection_V2_Builtins.pack_ln
       (FStarC_Reflection_V2_Data.Tv_FVar
          (FStarC_Reflection_V2_Builtins.pack_fv
             ["FStar"; "Pervasives"; "Native"; "Mktuple2"])))
    [((FStar_Reflection_V2_Derived.mk_e_app
         (FStarC_Reflection_V2_Builtins.pack_ln
            (FStarC_Reflection_V2_Data.Tv_FVar
               (FStarC_Reflection_V2_Builtins.pack_fv ["Prims"; "list"])))
         [x3]), FStarC_Reflection_V2_Data.Q_Implicit);
    (x1, FStarC_Reflection_V2_Data.Q_Implicit);
    (x4, FStarC_Reflection_V2_Data.Q_Explicit);
    (x5, FStarC_Reflection_V2_Data.Q_Explicit)]
let rec quote_exp (e : exp) :
  FStarC_Tactics_Types.ref_proofstate -> FStar_Tactics_NamedView.term=
  match e with
  | Unit ->
      (fun uu___ ->
         FStarC_Reflection_V2_Builtins.pack_ln
           (FStarC_Reflection_V2_Data.Tv_FVar
              (FStarC_Reflection_V2_Builtins.pack_fv
                 ["FStar"; "Tactics"; "CanonCommMonoid"; "Unit"])))
  | Var x ->
      (fun uu___ ->
         FStar_Reflection_V2_Derived.mk_e_app
           (FStarC_Reflection_V2_Builtins.pack_ln
              (FStarC_Reflection_V2_Data.Tv_FVar
                 (FStarC_Reflection_V2_Builtins.pack_fv
                    ["FStar"; "Tactics"; "CanonCommMonoid"; "Var"])))
           [FStar_Tactics_NamedView.pack
              (FStar_Tactics_NamedView.Tv_Const
                 (FStarC_Reflection_V2_Data.C_Int x))])
  | Mult (e1, e2) ->
      (fun ps ->
         let x =
           let x1 = quote_exp e1 ps in
           let x2 = let x3 = quote_exp e2 ps in [x3] in x1 :: x2 in
         FStar_Reflection_V2_Derived.mk_e_app
           (FStarC_Reflection_V2_Builtins.pack_ln
              (FStarC_Reflection_V2_Data.Tv_FVar
                 (FStarC_Reflection_V2_Builtins.pack_fv
                    ["FStar"; "Tactics"; "CanonCommMonoid"; "Mult"]))) x)
let canon_monoid_aux (ta : FStar_Tactics_NamedView.term)
  (unquotea :
    FStar_Tactics_NamedView.term -> FStarC_Tactics_Types.ref_proofstate -> 'a)
  (quotea :
    'a -> FStarC_Tactics_Types.ref_proofstate -> FStar_Tactics_NamedView.term)
  (tm : FStar_Tactics_NamedView.term) (tmult : FStar_Tactics_NamedView.term)
  (tunit : FStar_Tactics_NamedView.term) (munit : 'a)
  (tb : FStar_Tactics_NamedView.term)
  (quoteb :
    'b -> FStarC_Tactics_Types.ref_proofstate -> FStar_Tactics_NamedView.term)
  (f :
    FStar_Tactics_NamedView.term -> FStarC_Tactics_Types.ref_proofstate -> 'b)
  (def : 'b) (tp : FStar_Tactics_NamedView.term)
  (tpc : FStar_Tactics_NamedView.term)
  (ps : FStarC_Tactics_Types.ref_proofstate) : unit=
  FStarC_Tactics_V2_Builtins.norm [] ps;
  (let x1 =
     let x2 = FStar_Tactics_V2_Derived.cur_goal () ps in
     FStar_Reflection_V2_Formula.term_as_formula x2 ps in
   match x1 with
   | FStar_Reflection_V2_Formula.Comp
       (FStar_Reflection_V2_Formula.Eq (FStar_Pervasives_Native.Some t), t1,
        t2)
       ->
       if term_eq t ta
       then
         let x2 =
           Obj.magic
             (reification f def ()
                (fun uu___1 uu___ -> Obj.magic unquotea uu___1 uu___)
                (fun uu___1 uu___ -> Obj.magic quotea uu___1 uu___) tmult
                tunit (Obj.magic munit) [t1; t2] ps) in
         (match x2 with
          | (r1::r2::[], vm) ->
              let x3 = quote_vm ta tb quotea quoteb vm ps in
              let x4 = quote_exp r1 ps in
              let x5 = quote_exp r2 ps in
              let x6 =
                FStar_Reflection_V2_Derived.mk_app
                  (FStarC_Reflection_V2_Builtins.pack_ln
                     (FStarC_Reflection_V2_Data.Tv_FVar
                        (FStarC_Reflection_V2_Builtins.pack_fv
                           ["Prims"; "eq2"])))
                  [(ta, FStarC_Reflection_V2_Data.Q_Implicit);
                  ((FStar_Reflection_V2_Derived.mk_app
                      (FStarC_Reflection_V2_Builtins.pack_ln
                         (FStarC_Reflection_V2_Data.Tv_FVar
                            (FStarC_Reflection_V2_Builtins.pack_fv
                               ["FStar";
                               "Tactics";
                               "CanonCommMonoid";
                               "mdenote"])))
                      [(ta, FStarC_Reflection_V2_Data.Q_Implicit);
                      (tb, FStarC_Reflection_V2_Data.Q_Implicit);
                      (tm, FStarC_Reflection_V2_Data.Q_Explicit);
                      (x3, FStarC_Reflection_V2_Data.Q_Explicit);
                      (x4, FStarC_Reflection_V2_Data.Q_Explicit)]),
                    FStarC_Reflection_V2_Data.Q_Explicit);
                  ((FStar_Reflection_V2_Derived.mk_app
                      (FStarC_Reflection_V2_Builtins.pack_ln
                         (FStarC_Reflection_V2_Data.Tv_FVar
                            (FStarC_Reflection_V2_Builtins.pack_fv
                               ["FStar";
                               "Tactics";
                               "CanonCommMonoid";
                               "mdenote"])))
                      [(ta, FStarC_Reflection_V2_Data.Q_Implicit);
                      (tb, FStarC_Reflection_V2_Data.Q_Implicit);
                      (tm, FStarC_Reflection_V2_Data.Q_Explicit);
                      (x3, FStarC_Reflection_V2_Data.Q_Explicit);
                      (x5, FStarC_Reflection_V2_Data.Q_Explicit)]),
                    FStarC_Reflection_V2_Data.Q_Explicit)] in
              (FStar_Tactics_V2_Derived.change_sq x6 ps;
               FStar_Tactics_V2_Derived.apply_lemma
                 (FStar_Reflection_V2_Derived.mk_app
                    (FStarC_Reflection_V2_Builtins.pack_ln
                       (FStarC_Reflection_V2_Data.Tv_FVar
                          (FStarC_Reflection_V2_Builtins.pack_fv
                             ["FStar";
                             "Tactics";
                             "CanonCommMonoid";
                             "monoid_reflect"])))
                    [(ta, FStarC_Reflection_V2_Data.Q_Implicit);
                    (tb, FStarC_Reflection_V2_Data.Q_Implicit);
                    (tp, FStarC_Reflection_V2_Data.Q_Explicit);
                    (tpc, FStarC_Reflection_V2_Data.Q_Explicit)]) ps;
               unfold_topdown
                 [FStarC_Reflection_V2_Builtins.pack_ln
                    (FStarC_Reflection_V2_Data.Tv_FVar
                       (FStarC_Reflection_V2_Builtins.pack_fv
                          ["FStar"; "Tactics"; "CanonCommMonoid"; "canon"]));
                 FStarC_Reflection_V2_Builtins.pack_ln
                   (FStarC_Reflection_V2_Data.Tv_FVar
                      (FStarC_Reflection_V2_Builtins.pack_fv
                         ["FStar"; "Tactics"; "CanonCommMonoid"; "xsdenote"]));
                 tp] ps;
               FStarC_Tactics_V2_Builtins.norm
                 [FStarC_NormSteps.delta_only
                    ["FStar.Tactics.CanonCommMonoid.canon";
                    "FStar.Tactics.CanonCommMonoid.xsdenote";
                    "FStar.Tactics.CanonCommMonoid.flatten";
                    "FStar.Tactics.CanonCommMonoid.select";
                    "FStar.Tactics.CanonCommMonoid.select_extra";
                    "FStar.Tactics.CanonCommMonoid.quote_list";
                    "FStar.Tactics.CanonCommMonoid.quote_vm";
                    "FStar.Tactics.CanonCommMonoid.quote_exp";
                    "FStar.Tactics.CanonCommMonoid.const_compare";
                    "FStar.Tactics.CanonCommMonoid.special_compare";
                    "FStar.Pervasives.Native.fst";
                    "FStar.Pervasives.Native.snd";
                    "FStar.Pervasives.Native.__proj__Mktuple2__item___1";
                    "FStar.Pervasives.Native.__proj__Mktuple2__item___2";
                    "FStar.List.Tot.Base.assoc";
                    "FStar.List.Tot.Base.op_At";
                    "FStar.List.Tot.Base.append";
                    "SL.AutoTactic.compare_b";
                    "SL.AutoTactic.compare_v";
                    "FStar.Order.int_of_order";
                    "FStar.Reflection.V2.Compare.compare_term";
                    "FStar.List.Tot.Base.sortWith";
                    "FStar.List.Tot.Base.partition";
                    "FStar.List.Tot.Base.bool_of_compare";
                    "FStar.List.Tot.Base.compare_of_bool"];
                 FStarC_NormSteps.zeta;
                 FStarC_NormSteps.iota;
                 FStarC_NormSteps.primops] ps)
          | uu___ -> FStar_Tactics_V2_Derived.fail "Unexpected" ps)
       else
         FStar_Tactics_V2_Derived.fail
           "Goal should be an equality at the right monoid type" ps
   | uu___ -> FStar_Tactics_V2_Derived.fail "Goal should be an equality" ps)
let canon_monoid_with
  (f :
    FStar_Tactics_NamedView.term -> FStarC_Tactics_Types.ref_proofstate -> 'b)
  (def : 'b) (p : 'b permute) (pc : unit) (a : unit)
  (m : Obj.t FStar_Algebra_CommMonoid.cm)
  (ps : FStarC_Tactics_Types.ref_proofstate) : unit=
  let x = Obj.magic (failwith "Cannot evaluate open quotation at runtime") in
  let x1 = Obj.magic (failwith "Cannot evaluate open quotation at runtime") in
  let x2 = Obj.magic (failwith "Cannot evaluate open quotation at runtime") in
  let x3 = Obj.magic (failwith "Cannot evaluate open quotation at runtime") in
  let x4 = Obj.magic (failwith "Cannot evaluate open quotation at runtime") in
  let x5 = Obj.magic (failwith "Cannot evaluate open quotation at runtime") in
  let x6 = Obj.magic (failwith "Cannot evaluate open quotation at runtime") in
  canon_monoid_aux x FStarC_Tactics_V2_Builtins.unquote
    (fun uu___1 uu___ ->
       (fun x7 uu___ ->
          Obj.magic (failwith "Cannot evaluate open quotation at runtime"))
         uu___1 uu___) x1 x2 x3
    (match m with
     | FStar_Algebra_CommMonoid.CM
         (unit, mult, identity, associativity, commutativity) -> unit) x4
    (fun uu___1 uu___ ->
       (fun x7 uu___ ->
          Obj.magic (failwith "Cannot evaluate open quotation at runtime"))
         uu___1 uu___) f def x5 x6 ps
let canon_monoid (cm : 'a FStar_Algebra_CommMonoid.cm) :
  FStarC_Tactics_Types.ref_proofstate -> unit=
  canon_monoid_with (fun uu___ uu___1 -> ()) () (fun a1 -> sort ()) () ()
    (Obj.magic cm)
let is_const (t : FStar_Tactics_NamedView.term)
  (ps : FStarC_Tactics_Types.ref_proofstate) : Prims.bool=
  let x = FStar_Tactics_NamedView.inspect t ps in
  match x with | FStar_Tactics_NamedView.Tv_Const _0 -> true | uu___ -> false
let const_compare (vm : ('a, Prims.bool) vmap) (x : var) (y : var) :
  Prims.int=
  match ((select_extra x vm), (select_extra y vm)) with
  | (false, false) -> FStar_List_Tot_Base.compare_of_bool (<) x y
  | (true, true) -> FStar_List_Tot_Base.compare_of_bool (<) x y
  | (false, true) -> Prims.int_one
  | (true, false) -> Prims.of_int (-1)
let const_last (vm : ('a, Prims.bool) vmap) (xs : var Prims.list) :
  var Prims.list= FStar_List_Tot_Base.sortWith (const_compare vm) xs
let canon_monoid_const (cm : 'a FStar_Algebra_CommMonoid.cm) :
  FStarC_Tactics_Types.ref_proofstate -> unit=
  canon_monoid_with is_const false (fun a1 -> const_last) () ()
    (Obj.magic cm)
let is_special (ts : FStar_Tactics_NamedView.term Prims.list)
  (t : FStar_Tactics_NamedView.term) :
  FStarC_Tactics_Types.ref_proofstate -> Prims.bool= term_mem t ts
let special_compare (vm : ('a, Prims.bool) vmap) (x : var) (y : var) :
  Prims.int=
  match ((select_extra x vm), (select_extra y vm)) with
  | (false, false) -> Prims.int_zero
  | (true, true) -> FStar_List_Tot_Base.compare_of_bool (<) x y
  | (false, true) -> Prims.of_int (-1)
  | (true, false) -> Prims.int_one
let special_first (vm : ('a, Prims.bool) vmap) (xs : var Prims.list) :
  var Prims.list= FStar_List_Tot_Base.sortWith (special_compare vm) xs

let canon_monoid_special (uu___2 : FStar_Tactics_NamedView.term Prims.list)
  (uu___1 : 'uuuuu FStar_Algebra_CommMonoid.cm)
  (uu___ : FStarC_Tactics_Types.ref_proofstate) : unit=
  (fun ts ->
     Obj.magic
       (canon_monoid_with (is_special ts) false (fun a -> special_first) ()
          ())) uu___2 uu___1 uu___
