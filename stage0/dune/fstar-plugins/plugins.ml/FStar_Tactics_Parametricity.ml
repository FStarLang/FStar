open Fstarcompiler
open Prims
exception Unsupported of Prims.string 
let uu___is_Unsupported (projectee : Prims.exn) : Prims.bool=
  match projectee with | Unsupported uu___ -> true | uu___ -> false
let __proj__Unsupported__item__uu___ (projectee : Prims.exn) : Prims.string=
  match projectee with | Unsupported uu___ -> uu___
exception NotFoundFV of FStarC_Reflection_Types.fv 
let uu___is_NotFoundFV (projectee : Prims.exn) : Prims.bool=
  match projectee with | NotFoundFV uu___ -> true | uu___ -> false
let __proj__NotFoundFV__item__uu___ (projectee : Prims.exn) :
  FStarC_Reflection_Types.fv=
  match projectee with | NotFoundFV uu___ -> uu___
type bvmap =
  (FStar_Tactics_NamedView.namedv * (FStar_Tactics_NamedView.binder *
    FStar_Tactics_NamedView.binder * FStar_Tactics_NamedView.binder))
    Prims.list
type fvmap =
  (FStarC_Reflection_Types.fv * FStarC_Reflection_Types.fv) Prims.list
type param_state = {
  bvmap: bvmap ;
  fresh: Prims.int ;
  recs: fvmap }
let __proj__Mkparam_state__item__bvmap (projectee : param_state) : bvmap=
  match projectee with | { bvmap = bvmap1; fresh; recs;_} -> bvmap1
let __proj__Mkparam_state__item__fresh (projectee : param_state) : Prims.int=
  match projectee with | { bvmap = bvmap1; fresh; recs;_} -> fresh
let __proj__Mkparam_state__item__recs (projectee : param_state) : fvmap=
  match projectee with | { bvmap = bvmap1; fresh; recs;_} -> recs
let rec fold_right2 :
  'a 'b 'c .
    ('a -> 'b -> 'c -> ('c, unit) FStar_Tactics_Effect.tac_repr) ->
      'a Prims.list ->
        'b Prims.list -> 'c -> ('c, unit) FStar_Tactics_Effect.tac_repr
  =
  fun uu___3 uu___2 uu___1 uu___ ->
    (fun f l1 l2 c1 ->
       match (l1, l2) with
       | (h1::t1, h2::t2) ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind
                   (Obj.magic (fold_right2 f t1 t2 c1))
                   (fun uu___ ->
                      (fun uu___ -> Obj.magic (f h1 h2 uu___)) uu___)))
       | ([], []) -> Obj.magic (Obj.repr (fun uu___ -> c1))
       | uu___ ->
           Obj.magic (Obj.repr (FStar_Tactics_V2_Derived.fail "fold_right2")))
      uu___3 uu___2 uu___1 uu___
let rec zip3 :
  'a 'b 'c .
    'a Prims.list ->
      'b Prims.list -> 'c Prims.list -> ('a * 'b * 'c) Prims.list
  =
  fun l1 l2 l3 ->
    match (l1, l2, l3) with
    | (h1::t1, h2::t2, h3::t3) -> (h1, h2, h3) :: (zip3 t1 t2 t3)
    | uu___ -> []
let last (uu___ : 'a Prims.list) : ('a, unit) FStar_Tactics_Effect.tac_repr=
  (fun xs ->
     match FStar_List_Tot_Base.rev xs with
     | h::uu___ ->
         Obj.magic
           (Obj.repr (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> h)))
     | [] ->
         Obj.magic
           (Obj.repr (FStar_Tactics_V2_Derived.fail "last: empty list")))
    uu___
let app_binders (uu___1 : FStar_Tactics_NamedView.term)
  (uu___ : FStar_Tactics_NamedView.binder Prims.list) :
  (FStar_Tactics_NamedView.term, unit) FStar_Tactics_Effect.tac_repr=
  (fun t bs ->
     Obj.magic
       (fun uu___ ->
          FStar_Reflection_V2_Derived.mk_e_app t
            (FStar_List_Tot_Base.map
               FStar_Tactics_V2_SyntaxCoercions.binder_to_term bs))) uu___1
    uu___
let push_var_to_state (v : FStar_Tactics_NamedView.namedv)
  (b0 : FStar_Tactics_NamedView.binder) (b1 : FStar_Tactics_NamedView.binder)
  (b2 : FStar_Tactics_NamedView.binder) (s : param_state) : param_state=
  {
    bvmap = ((v, (b0, b1, b2)) :: (s.bvmap));
    fresh = (s.fresh);
    recs = (s.recs)
  }
exception NotARecFV 
let uu___is_NotARecFV (projectee : Prims.exn) : Prims.bool=
  match projectee with | NotARecFV -> true | uu___ -> false
exception NotFoundBV of FStar_Tactics_NamedView.namedv 
let uu___is_NotFoundBV (projectee : Prims.exn) : Prims.bool=
  match projectee with | NotFoundBV uu___ -> true | uu___ -> false
let __proj__NotFoundBV__item__uu___ (projectee : Prims.exn) :
  FStar_Tactics_NamedView.namedv=
  match projectee with | NotFoundBV uu___ -> uu___
let lookup_rec_fv (s : param_state) (f : FStarC_Reflection_Types.fv) :
  (FStarC_Reflection_Types.fv, unit) FStar_Tactics_Effect.tac_repr=
  let rec aux uu___ =
    (fun m ->
       match m with
       | [] ->
           Obj.magic
             (Obj.repr
                (fun ps ->
                   Obj.magic
                     (FStarC_Tactics_V2_Builtins.raise_core NotARecFV ps)))
       | (f1, k)::fs ->
           Obj.magic
             (Obj.repr
                (if
                   (FStar_Reflection_V2_Compare.compare_fv f f1) =
                     FStar_Order.Eq
                 then
                   Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> k))
                 else Obj.repr (aux fs)))) uu___ in
  aux s.recs
let push_fv (f1 : FStarC_Reflection_Types.fv)
  (f2 : FStarC_Reflection_Types.fv) (s : param_state) : param_state=
  { bvmap = (s.bvmap); fresh = (s.fresh); recs = ((f1, f2) :: (s.recs)) }
let lookup (s : param_state) (v : FStar_Tactics_NamedView.namedv) :
  ((FStar_Tactics_NamedView.binder * FStar_Tactics_NamedView.binder *
     FStar_Tactics_NamedView.binder),
    unit) FStar_Tactics_Effect.tac_repr=
  let rec aux uu___ =
    (fun bvm ->
       match bvm with
       | [] ->
           Obj.magic
             (Obj.repr
                (fun ps ->
                   Obj.magic
                     (FStarC_Tactics_V2_Builtins.raise_core (NotFoundBV v) ps)))
       | (v', r)::tl ->
           Obj.magic
             (Obj.repr
                (if
                   (FStar_Tactics_NamedView.inspect_namedv v).FStarC_Reflection_V2_Data.uniq
                     =
                     (FStar_Tactics_NamedView.inspect_namedv v').FStarC_Reflection_V2_Data.uniq
                 then
                   Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> r))
                 else Obj.repr (aux tl)))) uu___ in
  aux s.bvmap
let replace_var (s : param_state) (b : Prims.bool)
  (t : FStar_Tactics_NamedView.term) :
  (FStar_Tactics_NamedView.term, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = FStar_Tactics_NamedView.inspect t ps in
    match x with
    | FStar_Tactics_NamedView.Tv_Var v ->
        FStar_Tactics_V2_Derived.try_with
          (fun uu___ ->
             match () with
             | () ->
                 (fun ps1 ->
                    let x1 = lookup s v ps1 in
                    match x1 with
                    | (x2, y, uu___1) ->
                        FStar_Tactics_NamedView.pack
                          (FStar_Tactics_NamedView.Tv_Var
                             (FStar_Tactics_V2_SyntaxCoercions.binder_to_namedv
                                (if b then y else x2)))))
          (fun uu___ ->
             (fun uu___ ->
                match uu___ with
                | NotFoundBV uu___1 ->
                    Obj.magic
                      (Obj.repr
                         (FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> t)))
                | e ->
                    Obj.magic
                      (Obj.repr
                         (FStar_Tactics_Effect.tac_bind
                            (Obj.magic
                               (FStarC_Tactics_V2_Builtins.raise_core e))
                            (fun uu___1 uu___2 -> Obj.magic ())))) uu___) ps
    | uu___ -> t
let replace_by (s : param_state) (b : Prims.bool)
  (t : FStar_Tactics_NamedView.term) :
  (FStar_Tactics_NamedView.term, unit) FStar_Tactics_Effect.tac_repr=
  fun ps -> let x = FStar_Tactics_Visit.visit_tm (replace_var s b) t ps in x
let tapp (q : FStarC_Reflection_V2_Data.aqualv)
  (t1 : FStar_Tactics_NamedView.term) (t2 : FStarC_Reflection_Types.term) :
  FStar_Tactics_NamedView.term=
  FStar_Tactics_NamedView.pack (FStar_Tactics_NamedView.Tv_App (t1, (t2, q)))
let tabs (uu___1 : FStar_Tactics_NamedView.binder)
  (uu___ : FStar_Tactics_NamedView.term) :
  (FStar_Tactics_NamedView.term, unit) FStar_Tactics_Effect.tac_repr=
  (fun b t ->
     Obj.magic
       (fun uu___ ->
          FStar_Tactics_NamedView.pack
            (FStar_Tactics_NamedView.Tv_Abs (b, t)))) uu___1 uu___
let rec param' (s : param_state) (t : FStar_Tactics_NamedView.term) :
  (FStar_Tactics_NamedView.term, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x =
      let x1 = FStar_Tactics_NamedView.inspect t ps in
      match x1 with
      | FStar_Tactics_NamedView.Tv_Type _u ->
          Obj.magic
            (Obj.repr
               (let x2 = FStar_Tactics_V2_Derived.fresh_binder_named "s" t ps in
                let x3 = FStar_Tactics_V2_Derived.fresh_binder_named "r" t ps in
                let x4 =
                  FStar_Tactics_V2_Derived.fresh_binder_named "xs"
                    (FStar_Tactics_NamedView.pack
                       (FStar_Tactics_NamedView.Tv_Var
                          (FStar_Tactics_V2_SyntaxCoercions.binder_to_namedv
                             x2))) ps in
                let x5 =
                  FStar_Tactics_V2_Derived.fresh_binder_named "xr"
                    (FStar_Tactics_NamedView.pack
                       (FStar_Tactics_NamedView.Tv_Var
                          (FStar_Tactics_V2_SyntaxCoercions.binder_to_namedv
                             x3))) ps in
                FStar_Tactics_NamedView.pack
                  (FStar_Tactics_NamedView.Tv_Abs
                     (x2,
                       (FStar_Tactics_NamedView.pack
                          (FStar_Tactics_NamedView.Tv_Abs
                             (x3,
                               (FStar_Tactics_NamedView.pack
                                  (FStar_Tactics_NamedView.Tv_Arrow
                                     (x4,
                                       (FStarC_Reflection_V2_Data.C_Total
                                          (FStar_Tactics_NamedView.pack
                                             (FStar_Tactics_NamedView.Tv_Arrow
                                                (x5,
                                                  (FStarC_Reflection_V2_Data.C_Total
                                                     (FStar_Tactics_NamedView.pack
                                                        (FStar_Tactics_NamedView.Tv_Type
                                                           (FStar_Tactics_NamedView.pack_universe
                                                              FStar_Tactics_NamedView.Uv_Unk))))))))))))))))))
      | FStar_Tactics_NamedView.Tv_Var bv ->
          Obj.magic
            (Obj.repr
               (let x2 = lookup s bv ps in
                match x2 with
                | (uu___, uu___1, b) ->
                    FStar_Tactics_V2_SyntaxCoercions.binder_to_term b))
      | FStar_Tactics_NamedView.Tv_Arrow (b, c) ->
          Obj.magic
            (Obj.repr
               (match FStar_Tactics_NamedView.inspect_comp c with
                | FStarC_Reflection_V2_Data.C_Total t2 ->
                    Obj.repr
                      (let x2 = push_binder b s ps in
                       match x2 with
                       | (s', (bx0, bx1, bxR)) ->
                           let x3 = b.FStar_Tactics_NamedView.qual in
                           let x4 =
                             let x5 = replace_by s false t ps in
                             FStar_Tactics_V2_Derived.fresh_binder_named "f0"
                               x5 ps in
                           let x5 =
                             let x6 = replace_by s true t ps in
                             FStar_Tactics_V2_Derived.fresh_binder_named "f1"
                               x6 ps in
                           let x6 =
                             FStar_Tactics_V2_SyntaxCoercions.binder_to_term in
                           let x7 =
                             let x8 = tapp x3 (x6 x5) (x6 bx1) in
                             let x9 = tapp x3 (x6 x4) (x6 bx0) in
                             let x10 = param' s' t2 ps in
                             FStarC_Reflection_V2_Builtins.pack_ln
                               (FStarC_Reflection_V2_Data.Tv_App
                                  ((FStarC_Reflection_V2_Builtins.pack_ln
                                      (FStarC_Reflection_V2_Data.Tv_App
                                         (x10,
                                           (x9,
                                             FStarC_Reflection_V2_Data.Q_Explicit)))),
                                    (x8,
                                      FStarC_Reflection_V2_Data.Q_Explicit))) in
                           let x8 =
                             let x9 =
                               FStar_Tactics_V2_SyntaxHelpers.mk_tot_arr
                                 [bx0; bx1; bxR] x7 ps in
                             tabs x5 x9 ps in
                           tabs x4 x8 ps)
                | uu___ ->
                    Obj.repr
                      (FStarC_Tactics_V2_Builtins.raise_core
                         (Unsupported "effects") ps)))
      | FStar_Tactics_NamedView.Tv_App (l, (r, q)) ->
          Obj.magic
            (Obj.repr
               (let x2 = param' s l ps in
                let x3 = replace_by s false r ps in
                let x4 = replace_by s true r ps in
                let x5 = param' s r ps in
                FStar_Reflection_V2_Derived.mk_app x2
                  [(x3, q); (x4, q); (x5, q)]))
      | FStar_Tactics_NamedView.Tv_Abs (b, t1) ->
          Obj.magic
            (Obj.repr
               (let x2 uu___1 uu___ =
                  (fun b1 t2 ->
                     Obj.magic
                       (fun uu___ ->
                          FStar_Tactics_NamedView.pack
                            (FStar_Tactics_NamedView.Tv_Abs (b1, t2))))
                    uu___1 uu___ in
                let x3 = push_binder b s ps in
                match x3 with
                | (s', (bx0, bx1, bxR)) ->
                    let x4 = param' s' t1 ps in
                    let x5 = let x6 = x2 bxR x4 ps in x2 bx1 x6 ps in
                    x2 bx0 x5 ps))
      | FStar_Tactics_NamedView.Tv_Match
          (t1, FStar_Pervasives_Native.None, brs) ->
          Obj.magic
            (Obj.repr
               (let x2 =
                  let x3 = param' s t1 ps in
                  let x4 = FStar_Tactics_Util.map (param_br s) brs ps in
                  FStar_Tactics_NamedView.Tv_Match
                    (x3, FStar_Pervasives_Native.None, x4) in
                FStar_Tactics_NamedView.pack x2))
      | FStar_Tactics_NamedView.Tv_UInst (fv, uu___) ->
          Obj.magic
            (Obj.repr
               (let x2 =
                  let x3 = param_fv s fv ps in
                  FStar_Tactics_NamedView.Tv_FVar x3 in
                FStar_Tactics_NamedView.pack x2))
      | FStar_Tactics_NamedView.Tv_FVar fv ->
          Obj.magic
            (Obj.repr
               (let x2 =
                  let x3 = param_fv s fv ps in
                  FStar_Tactics_NamedView.Tv_FVar x3 in
                FStar_Tactics_NamedView.pack x2))
      | FStar_Tactics_NamedView.Tv_Const c ->
          Obj.magic
            (Obj.repr
               (FStarC_Reflection_V2_Builtins.pack_ln
                  (FStarC_Reflection_V2_Data.Tv_Const
                     FStarC_Reflection_V2_Data.C_Unit)))
      | FStar_Tactics_NamedView.Tv_AscribedT (t1, uu___, uu___1, uu___2) ->
          Obj.magic (Obj.repr (param' s t1 ps))
      | FStar_Tactics_NamedView.Tv_AscribedC (t1, uu___, uu___1, uu___2) ->
          Obj.magic (Obj.repr (param' s t1 ps))
      | uu___ ->
          Obj.magic
            (Obj.repr
               (let x2 =
                  let x3 = FStar_Tactics_Print.term_to_ast_string t ps in
                  Unsupported x3 in
                FStarC_Tactics_V2_Builtins.raise_core x2 ps)) in
    x
and param_fv (s : param_state) (f : FStarC_Reflection_Types.fv) :
  (FStarC_Reflection_Types.fv, unit) FStar_Tactics_Effect.tac_repr=
  FStar_Tactics_V2_Derived.try_with
    (fun uu___ -> match () with | () -> lookup_rec_fv s f)
    (fun uu___ ps ->
       let x =
         FStarC_Reflection_V2_Builtins.explode_qn
           (Prims.strcat
              (FStarC_Reflection_V2_Builtins.implode_qn
                 (FStarC_Reflection_V2_Builtins.inspect_fv f)) "_param") in
       let x1 =
         let x2 = FStarC_Tactics_V2_Builtins.top_env () ps in
         FStarC_Reflection_V2_Builtins.lookup_typ x2 x in
       match x1 with
       | FStar_Pervasives_Native.Some se' ->
           Obj.magic (Obj.repr (FStarC_Reflection_V2_Builtins.pack_fv x))
       | FStar_Pervasives_Native.None ->
           Obj.magic
             (Obj.repr
                (let x2 =
                   let x3 =
                     let x4 =
                       let x5 =
                         let x6 =
                           let x7 =
                             last
                               (FStarC_Reflection_V2_Builtins.inspect_fv f)
                               ps in
                           Prims.strcat x7 "_param" in
                         [x6] in
                       "Parametricity" :: x5 in
                     "Tactics" :: x4 in
                   "FStar" :: x3 in
                 let x3 =
                   let x4 = FStarC_Tactics_V2_Builtins.top_env () ps in
                   FStarC_Reflection_V2_Builtins.lookup_typ x4 x2 in
                 match x3 with
                 | FStar_Pervasives_Native.Some se' ->
                     Obj.repr (FStarC_Reflection_V2_Builtins.pack_fv x2)
                 | FStar_Pervasives_Native.None ->
                     Obj.repr
                       (let x4 =
                          let x5 = FStar_Tactics_V2_Derived.cur_module () ps in
                          let x6 =
                            let x7 =
                              let x8 =
                                last
                                  (FStarC_Reflection_V2_Builtins.inspect_fv f)
                                  ps in
                              Prims.strcat x8 "_param" in
                            [x7] in
                          FStar_List_Tot_Base.op_At x5 x6 in
                        let x5 =
                          let x6 = FStarC_Tactics_V2_Builtins.top_env () ps in
                          FStarC_Reflection_V2_Builtins.lookup_typ x6 x4 in
                        match x5 with
                        | FStar_Pervasives_Native.Some se' ->
                            Obj.repr
                              (FStarC_Reflection_V2_Builtins.pack_fv x4)
                        | FStar_Pervasives_Native.None ->
                            Obj.repr
                              (FStarC_Tactics_V2_Builtins.raise_core
                                 (NotFoundFV f) ps)))))
and param_pat (s : param_state) (p : FStar_Tactics_NamedView.pattern) :
  ((param_state * (FStar_Tactics_NamedView.pattern *
     FStar_Tactics_NamedView.pattern * FStar_Tactics_NamedView.pattern)),
    unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x uu___ =
      (fun p1 ->
         Obj.magic
           (fun uu___ ->
              match p1 with
              | FStar_Tactics_NamedView.Pat_Dot_Term uu___1 -> true
              | uu___1 -> false)) uu___ in
    match p with
    | FStar_Tactics_NamedView.Pat_Cons
        { FStar_Tactics_NamedView.head = fv;
          FStar_Tactics_NamedView.univs = us;
          FStar_Tactics_NamedView.subpats = pats;_}
        ->
        let x1 = param_fv s fv ps in
        let x2 =
          FStar_Tactics_Util.fold_left
            (fun uu___ uu___1 ->
               match (uu___, uu___1) with
               | ((s1, (pats0, pats1, patsr)), (p1, i)) ->
                   FStar_Tactics_Effect.tac_bind (Obj.magic (x p1))
                     (fun uu___2 ->
                        (fun uu___2 ->
                           if uu___2
                           then
                             Obj.magic
                               (Obj.repr
                                  (fun uu___3 -> (s1, (pats0, pats1, patsr))))
                           else
                             Obj.magic
                               (Obj.repr
                                  (FStar_Tactics_Effect.tac_bind
                                     (Obj.magic (param_pat s1 p1))
                                     (fun uu___4 uu___5 ->
                                        match uu___4 with
                                        | (s', (p0, p11, pr)) ->
                                            (s',
                                              (((p0, i) :: pats0), ((p11, i)
                                                :: pats1), ((pr, false) ::
                                                (p11, i) :: (p0, i) ::
                                                patsr))))))) uu___2))
            (s, ([], [], [])) pats ps in
        (match x2 with
         | (s', (pats0, pats1, patsr)) ->
             (s',
               ((FStar_Tactics_NamedView.Pat_Cons
                   {
                     FStar_Tactics_NamedView.head = fv;
                     FStar_Tactics_NamedView.univs = us;
                     FStar_Tactics_NamedView.subpats =
                       (FStar_List_Tot_Base.rev pats0)
                   }),
                 (FStar_Tactics_NamedView.Pat_Cons
                    {
                      FStar_Tactics_NamedView.head = fv;
                      FStar_Tactics_NamedView.univs = us;
                      FStar_Tactics_NamedView.subpats =
                        (FStar_List_Tot_Base.rev pats1)
                    }),
                 (FStar_Tactics_NamedView.Pat_Cons
                    {
                      FStar_Tactics_NamedView.head = x1;
                      FStar_Tactics_NamedView.univs = us;
                      FStar_Tactics_NamedView.subpats =
                        (FStar_List_Tot_Base.rev patsr)
                    }))))
    | FStar_Tactics_NamedView.Pat_Var
        { FStar_Tactics_NamedView.v = v;
          FStar_Tactics_NamedView.sort1 = sort;_}
        ->
        let x1 =
          let x2 = FStarC_Tactics_Unseal.unseal sort ps in
          FStar_Tactics_NamedView.namedv_to_binder v x2 in
        let x2 = push_binder x1 s ps in
        (match x2 with
         | (s', (b0, b1, bR)) ->
             (s',
               ((FStar_Tactics_NamedView.Pat_Var
                   {
                     FStar_Tactics_NamedView.v =
                       (FStar_Tactics_V2_SyntaxCoercions.binder_to_namedv b0);
                     FStar_Tactics_NamedView.sort1 =
                       (FStar_Sealed.seal
                          (FStar_Tactics_V2_Derived.binder_sort b0))
                   }),
                 (FStar_Tactics_NamedView.Pat_Var
                    {
                      FStar_Tactics_NamedView.v =
                        (FStar_Tactics_V2_SyntaxCoercions.binder_to_namedv b1);
                      FStar_Tactics_NamedView.sort1 =
                        (FStar_Sealed.seal
                           (FStar_Tactics_V2_Derived.binder_sort b1))
                    }),
                 (FStar_Tactics_NamedView.Pat_Var
                    {
                      FStar_Tactics_NamedView.v =
                        (FStar_Tactics_V2_SyntaxCoercions.binder_to_namedv bR);
                      FStar_Tactics_NamedView.sort1 =
                        (FStar_Sealed.seal
                           (FStar_Tactics_V2_Derived.binder_sort bR))
                    }))))
    | FStar_Tactics_NamedView.Pat_Dot_Term t ->
        FStar_Tactics_V2_Derived.fail "no dot pats" ps
    | FStar_Tactics_NamedView.Pat_Constant c ->
        let x1 =
          FStar_Tactics_V2_Derived.fresh_binder_named "cR"
            (FStarC_Reflection_V2_Builtins.pack_ln
               FStarC_Reflection_V2_Data.Tv_Unknown) ps in
        (s,
          ((FStar_Tactics_NamedView.Pat_Constant c),
            (FStar_Tactics_NamedView.Pat_Constant c),
            (FStar_Tactics_NamedView.Pat_Var
               {
                 FStar_Tactics_NamedView.v =
                   (FStar_Tactics_V2_SyntaxCoercions.binder_to_namedv x1);
                 FStar_Tactics_NamedView.sort1 =
                   (FStar_Sealed.seal
                      (FStarC_Reflection_V2_Builtins.pack_ln
                         FStarC_Reflection_V2_Data.Tv_Unknown))
               })))
and param_br (s : param_state) (br : FStar_Tactics_NamedView.branch) :
  (FStar_Tactics_NamedView.branch, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = br in
    match x with
    | (pat, t) ->
        let x1 = param_pat s pat ps in
        (match x1 with
         | (s', (uu___, uu___1, pat')) ->
             let x2 = param' s' t ps in (pat', x2))
and push_binder (b : FStar_Tactics_NamedView.binder) (s : param_state) :
  ((param_state * (FStar_Tactics_NamedView.binder *
     FStar_Tactics_NamedView.binder * FStar_Tactics_NamedView.binder)),
    unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = b.FStar_Tactics_NamedView.qual in
    let x1 = b.FStar_Tactics_NamedView.sort in
    let x2 = FStarC_Tactics_Unseal.unseal b.FStar_Tactics_NamedView.ppname ps in
    let x3 uu___1 uu___ =
      (fun s1 t -> Obj.magic (fun uu___ -> Prims.strcat s1 t)) uu___1 uu___ in
    let x4 =
      let x5 = x3 x2 "0" ps in
      let x6 = replace_by s false x1 ps in
      FStar_Tactics_V2_Derived.fresh_binder_named x5 x6 ps in
    let x5 =
      let x6 = x3 x2 "1" ps in
      let x7 = replace_by s true x1 ps in
      FStar_Tactics_V2_Derived.fresh_binder_named x6 x7 ps in
    let x6 =
      let x7 = x3 x2 "R" ps in
      let x8 =
        let x9 = FStar_Tactics_V2_SyntaxCoercions.binder_to_term x5 in
        let x10 = FStar_Tactics_V2_SyntaxCoercions.binder_to_term x4 in
        let x11 = param' s x1 ps in
        FStarC_Reflection_V2_Builtins.pack_ln
          (FStarC_Reflection_V2_Data.Tv_App
             ((FStarC_Reflection_V2_Builtins.pack_ln
                 (FStarC_Reflection_V2_Data.Tv_App
                    (x11, (x10, FStarC_Reflection_V2_Data.Q_Explicit)))),
               (x9, FStarC_Reflection_V2_Data.Q_Explicit))) in
      FStar_Tactics_V2_Derived.fresh_binder_named x7 x8 ps in
    ((push_var_to_state (FStar_Tactics_V2_SyntaxCoercions.binder_to_namedv b)
        {
          FStar_Tactics_NamedView.uniq = (x4.FStar_Tactics_NamedView.uniq);
          FStar_Tactics_NamedView.ppname =
            (x4.FStar_Tactics_NamedView.ppname);
          FStar_Tactics_NamedView.sort = (x4.FStar_Tactics_NamedView.sort);
          FStar_Tactics_NamedView.qual = x;
          FStar_Tactics_NamedView.attrs = (x4.FStar_Tactics_NamedView.attrs)
        }
        {
          FStar_Tactics_NamedView.uniq = (x5.FStar_Tactics_NamedView.uniq);
          FStar_Tactics_NamedView.ppname =
            (x5.FStar_Tactics_NamedView.ppname);
          FStar_Tactics_NamedView.sort = (x5.FStar_Tactics_NamedView.sort);
          FStar_Tactics_NamedView.qual = x;
          FStar_Tactics_NamedView.attrs = (x5.FStar_Tactics_NamedView.attrs)
        }
        {
          FStar_Tactics_NamedView.uniq = (x6.FStar_Tactics_NamedView.uniq);
          FStar_Tactics_NamedView.ppname =
            (x6.FStar_Tactics_NamedView.ppname);
          FStar_Tactics_NamedView.sort = (x6.FStar_Tactics_NamedView.sort);
          FStar_Tactics_NamedView.qual = x;
          FStar_Tactics_NamedView.attrs = (x6.FStar_Tactics_NamedView.attrs)
        } s),
      ({
         FStar_Tactics_NamedView.uniq = (x4.FStar_Tactics_NamedView.uniq);
         FStar_Tactics_NamedView.ppname = (x4.FStar_Tactics_NamedView.ppname);
         FStar_Tactics_NamedView.sort = (x4.FStar_Tactics_NamedView.sort);
         FStar_Tactics_NamedView.qual = x;
         FStar_Tactics_NamedView.attrs = (x4.FStar_Tactics_NamedView.attrs)
       },
        {
          FStar_Tactics_NamedView.uniq = (x5.FStar_Tactics_NamedView.uniq);
          FStar_Tactics_NamedView.ppname =
            (x5.FStar_Tactics_NamedView.ppname);
          FStar_Tactics_NamedView.sort = (x5.FStar_Tactics_NamedView.sort);
          FStar_Tactics_NamedView.qual = x;
          FStar_Tactics_NamedView.attrs = (x5.FStar_Tactics_NamedView.attrs)
        },
        {
          FStar_Tactics_NamedView.uniq = (x6.FStar_Tactics_NamedView.uniq);
          FStar_Tactics_NamedView.ppname =
            (x6.FStar_Tactics_NamedView.ppname);
          FStar_Tactics_NamedView.sort = (x6.FStar_Tactics_NamedView.sort);
          FStar_Tactics_NamedView.qual = x;
          FStar_Tactics_NamedView.attrs = (x6.FStar_Tactics_NamedView.attrs)
        }))
let init_param_state : param_state=
  { bvmap = []; fresh = Prims.int_zero; recs = [] }
let param (t : FStar_Tactics_NamedView.term) :
  (FStar_Tactics_NamedView.term, unit) FStar_Tactics_Effect.tac_repr=
  fun ps -> let x = param' init_param_state t ps in x
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.Parametricity.param" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.Parametricity.param (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_1 param)
               Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term
               Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term psc ncb
               us args)
let fv_to_tm (uu___ : FStarC_Reflection_Types.fv) :
  (FStar_Tactics_NamedView.term, unit) FStar_Tactics_Effect.tac_repr=
  (fun f ->
     Obj.magic
       (fun uu___ ->
          FStar_Tactics_NamedView.pack (FStar_Tactics_NamedView.Tv_FVar f)))
    uu___
let param_ctor (nm_ty : FStarC_Reflection_Types.name) (s : param_state)
  (c : FStarC_Reflection_V2_Data.ctor) :
  (FStarC_Reflection_V2_Data.ctor, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = c in
    match x with
    | (nm, ty) ->
        let x1 =
          let x2 = FStar_Tactics_V2_Derived.cur_module () ps in
          let x3 =
            let x4 = let x5 = last nm ps in Prims.strcat x5 "_param" in [x4] in
          FStar_List_Tot_Base.op_At x2 x3 in
        let x2 = FStar_Tactics_V2_SyntaxHelpers.collect_arr_bs ty ps in
        (match x2 with
         | (bs, c1) ->
             let x3 =
               let x4 =
                 fv_to_tm (FStarC_Reflection_V2_Builtins.pack_fv nm) ps in
               app_binders x4 bs ps in
             let x4 =
               FStar_Tactics_Util.fold_left
                 (fun uu___ b ->
                    match uu___ with
                    | (s1, bvs) ->
                        FStar_Tactics_Effect.tac_bind
                          (Obj.magic (push_binder b s1))
                          (fun uu___1 uu___2 ->
                             match uu___1 with
                             | (s2, (bx0, bx1, bxr)) ->
                                 (s2, (bxr :: bx1 :: bx0 :: bvs)))) (s, [])
                 bs ps in
             (match x4 with
              | (s1, bs1) ->
                  let x5 = FStar_List_Tot_Base.rev bs1 in
                  let x6 =
                    match FStar_Tactics_NamedView.inspect_comp c1 with
                    | FStarC_Reflection_V2_Data.C_Total ty1 -> ty1
                    | uu___ ->
                        FStar_Tactics_V2_Derived.fail
                          "param_ctor got a non-tot comp" ps in
                  let x7 =
                    let x8 = param' s1 x6 ps in
                    let x9 =
                      let x10 = replace_by s1 false x3 ps in
                      let x11 = let x12 = replace_by s1 true x3 ps in [x12] in
                      x10 :: x11 in
                    FStar_Reflection_V2_Derived.mk_e_app x8 x9 in
                  let x8 = FStar_Tactics_V2_SyntaxHelpers.mk_tot_arr x5 x7 ps in
                  (x1, x8)))
let param_inductive (se : FStarC_Reflection_Types.sigelt)
  (fv0 : FStarC_Reflection_Types.fv) (fv1 : FStarC_Reflection_Types.fv) :
  (FStarC_Reflection_Types.decls, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = FStar_Tactics_NamedView.inspect_sigelt se ps in
    match x with
    | FStar_Tactics_NamedView.Sg_Inductive
        { FStar_Tactics_NamedView.nm = nm;
          FStar_Tactics_NamedView.univs1 = univs;
          FStar_Tactics_NamedView.params = params;
          FStar_Tactics_NamedView.typ = typ;
          FStar_Tactics_NamedView.ctors = ctors;_}
        ->
        let x1 = push_fv fv0 fv1 init_param_state in
        let x2 =
          let x3 = fv_to_tm (FStarC_Reflection_V2_Builtins.pack_fv nm) ps in
          app_binders x3 params ps in
        let x3 =
          FStar_Tactics_Util.fold_left
            (fun uu___ b ->
               match uu___ with
               | (s, bvs) ->
                   FStar_Tactics_Effect.tac_bind
                     (Obj.magic (push_binder b s))
                     (fun uu___1 uu___2 ->
                        match uu___1 with
                        | (s1, (bx0, bx1, bxr)) ->
                            (s1, (bxr :: bx1 :: bx0 :: bvs)))) (x1, [])
            params ps in
        (match x3 with
         | (s, param_bs) ->
             let x4 = FStar_List_Tot_Base.rev param_bs in
             let x5 =
               let x6 = param' s typ ps in
               let x7 =
                 let x8 = replace_by s false x2 ps in
                 let x9 = let x10 = replace_by s true x2 ps in [x10] in x8 ::
                   x9 in
               FStar_Reflection_V2_Derived.mk_e_app x6 x7 in
             let x6 = FStar_Tactics_Util.map (param_ctor nm s) ctors ps in
             let x7 =
               FStar_Tactics_NamedView.Sg_Inductive
                 {
                   FStar_Tactics_NamedView.nm =
                     (FStarC_Reflection_V2_Builtins.inspect_fv fv1);
                   FStar_Tactics_NamedView.univs1 = univs;
                   FStar_Tactics_NamedView.params = x4;
                   FStar_Tactics_NamedView.typ = x5;
                   FStar_Tactics_NamedView.ctors = x6
                 } in
             let x8 = FStar_Tactics_NamedView.pack_sigelt x7 ps in [x8])
    | uu___ -> FStar_Tactics_V2_Derived.fail "" ps
let param_letbinding (se : FStarC_Reflection_Types.sigelt)
  (fv0 : FStarC_Reflection_Types.fv) (fv1 : FStarC_Reflection_Types.fv) :
  (FStarC_Reflection_Types.decls, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = FStar_Tactics_NamedView.inspect_sigelt se ps in
    match x with
    | FStar_Tactics_NamedView.Sg_Let
        { FStar_Tactics_NamedView.isrec = r;
          FStar_Tactics_NamedView.lbs = lb::[];_}
        ->
        let x1 = param lb.FStar_Tactics_NamedView.lb_typ ps in
        let x2 =
          let x3 =
            let x4 =
              let x5 = fv_to_tm fv0 ps in
              let x6 = let x7 = fv_to_tm fv0 ps in [x7] in x5 :: x6 in
            FStar_Reflection_V2_Derived.mk_e_app x1 x4 in
          FStar_Tactics_V2_Derived.norm_term [] x3 ps in
        let x3 =
          let x4 =
            let x5 =
              let x6 =
                let x7 = param lb.FStar_Tactics_NamedView.lb_def ps in
                {
                  FStar_Tactics_NamedView.lb_fv = fv1;
                  FStar_Tactics_NamedView.lb_us =
                    (lb.FStar_Tactics_NamedView.lb_us);
                  FStar_Tactics_NamedView.lb_typ = x2;
                  FStar_Tactics_NamedView.lb_def = x7
                } in
              [x6] in
            {
              FStar_Tactics_NamedView.isrec = r;
              FStar_Tactics_NamedView.lbs = x5
            } in
          FStar_Tactics_NamedView.Sg_Let x4 in
        let x4 = FStar_Tactics_NamedView.pack_sigelt x3 ps in [x4]
    | uu___ -> FStar_Tactics_V2_Derived.fail "no mutual recursion" ps
let paramd (nm : Prims.string) :
  (FStarC_Reflection_Types.decls, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x =
      let x1 =
        let x2 = FStar_Tactics_V2_Derived.cur_module () ps in
        let x3 =
          let x4 =
            let x5 = last (FStarC_Reflection_V2_Builtins.explode_qn nm) ps in
            Prims.strcat x5 "_param" in
          [x4] in
        FStar_List_Tot_Base.op_At x2 x3 in
      FStarC_Reflection_V2_Builtins.implode_qn x1 in
    let x1 =
      FStarC_Reflection_V2_Builtins.pack_fv
        (FStarC_Reflection_V2_Builtins.explode_qn nm) in
    let x2 =
      FStarC_Reflection_V2_Builtins.pack_fv
        (FStarC_Reflection_V2_Builtins.explode_qn x) in
    let x3 =
      let x4 = FStarC_Tactics_V2_Builtins.top_env () ps in
      FStarC_Reflection_V2_Builtins.lookup_typ x4
        (FStarC_Reflection_V2_Builtins.explode_qn nm) in
    match x3 with
    | FStar_Pervasives_Native.None ->
        FStar_Tactics_V2_Derived.fail "param_letbinding: not found" ps
    | FStar_Pervasives_Native.Some se ->
        let x4 =
          let x5 = FStar_Tactics_NamedView.inspect_sigelt se ps in
          match x5 with
          | FStar_Tactics_NamedView.Sg_Let uu___ ->
              param_letbinding se x1 x2 ps
          | FStar_Tactics_NamedView.Sg_Inductive uu___ ->
              param_inductive se x1 x2 ps
          | uu___ ->
              FStar_Tactics_V2_Derived.fail "paramd: unsupported sigelt" ps in
        x4
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.Parametricity.paramd" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.Parametricity.paramd (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_1 paramd)
               Fstarcompiler.FStarC_Syntax_Embeddings.e_string
               (Fstarcompiler.FStarC_Syntax_Embeddings.e_list
                  Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_sigelt) psc
               ncb us args)
let paramds (nms : Prims.string Prims.list) :
  (FStarC_Reflection_Types.decls, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = FStar_Tactics_Util.map paramd nms ps in
    FStar_List_Tot_Base.flatten x
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.Parametricity.paramds" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.Parametricity.paramds (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_1 paramds)
               (Fstarcompiler.FStarC_Syntax_Embeddings.e_list
                  Fstarcompiler.FStarC_Syntax_Embeddings.e_string)
               (Fstarcompiler.FStarC_Syntax_Embeddings.e_list
                  Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_sigelt) psc
               ncb us args)
type ('a, 'x, 'y) param_of_eqtype = unit
type ('uuuuu, 'uuuuu1) int_param = unit
type ('uuuuu, 'uuuuu1) bool_param = unit
type ('uuuuu, 'uuuuu1) unit_param = unit
type ('uuuuu, 'uuuuu1) string_param = unit
