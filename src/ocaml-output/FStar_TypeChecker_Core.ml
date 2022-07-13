open Prims
type precondition = FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option
type 'a result = ('a * precondition) FStar_Pervasives_Native.option
type hash_entry =
  {
  he_term: FStar_Syntax_Syntax.term ;
  he_gamma: FStar_Syntax_Syntax.binding Prims.list ;
  he_res: FStar_Syntax_Syntax.typ result }
let (__proj__Mkhash_entry__item__he_term :
  hash_entry -> FStar_Syntax_Syntax.term) =
  fun projectee ->
    match projectee with | { he_term; he_gamma; he_res;_} -> he_term
let (__proj__Mkhash_entry__item__he_gamma :
  hash_entry -> FStar_Syntax_Syntax.binding Prims.list) =
  fun projectee ->
    match projectee with | { he_term; he_gamma; he_res;_} -> he_gamma
let (__proj__Mkhash_entry__item__he_res :
  hash_entry -> FStar_Syntax_Syntax.typ result) =
  fun projectee ->
    match projectee with | { he_term; he_gamma; he_res;_} -> he_res
type tc_table = (FStar_Syntax_Syntax.term, hash_entry) FStar_Hash.hashtable
let (table : tc_table) = FStar_Hash.create FStar_Syntax_Hash.equal_term
let (clear_memo_table : unit -> unit) = fun uu___ -> FStar_Hash.clear table
let (insert :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ result -> unit)
  =
  fun g ->
    fun e ->
      fun res ->
        let entry =
          {
            he_term = e;
            he_gamma = (g.FStar_TypeChecker_Env.gamma);
            he_res = res
          } in
        FStar_Hash.insert (e, FStar_Syntax_Hash.hash_term) entry table
let (lookup :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ result FStar_Pervasives_Native.option)
  =
  fun g ->
    fun e ->
      let uu___ = FStar_Hash.lookup (e, FStar_Syntax_Hash.hash_term) table in
      match uu___ with
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some he ->
          let uu___1 =
            (FStar_Syntax_Hash.equal_term e he.he_term) &&
              (FStar_Compiler_List.forall2
                 (fun b1 ->
                    fun b2 ->
                      match (b1, b2) with
                      | (FStar_Syntax_Syntax.Binding_var x1,
                         FStar_Syntax_Syntax.Binding_var x2) ->
                          x1.FStar_Syntax_Syntax.index =
                            x2.FStar_Syntax_Syntax.index
                      | uu___2 -> true) he.he_gamma
                 g.FStar_TypeChecker_Env.gamma) in
          if uu___1
          then FStar_Pervasives_Native.Some (he.he_res)
          else FStar_Pervasives_Native.None
let return : 'a . 'a -> 'a result =
  fun x -> FStar_Pervasives_Native.Some (x, FStar_Pervasives_Native.None)
let (and_pre :
  precondition ->
    precondition ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
        FStar_Pervasives_Native.option)
  =
  fun p1 ->
    fun p2 ->
      match (p1, p2) with
      | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) ->
          FStar_Pervasives_Native.None
      | (FStar_Pervasives_Native.Some p, FStar_Pervasives_Native.None) ->
          FStar_Pervasives_Native.Some p
      | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some p) ->
          FStar_Pervasives_Native.Some p
      | (FStar_Pervasives_Native.Some p11, FStar_Pervasives_Native.Some p21)
          ->
          let uu___ = FStar_Syntax_Util.mk_conj p11 p21 in
          FStar_Pervasives_Native.Some uu___
let bind : 'a 'b . 'a result -> ('a -> 'b result) -> 'b result =
  fun x ->
    fun y ->
      match x with
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (x1, g1) ->
          let uu___ = y x1 in
          (match uu___ with
           | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some (y1, g2) ->
               let uu___1 = let uu___2 = and_pre g1 g2 in (y1, uu___2) in
               FStar_Pervasives_Native.Some uu___1)
let fail : 'a . unit -> 'a result = fun uu___ -> FStar_Pervasives_Native.None
let handle_with : 'a . 'a result -> (unit -> 'a result) -> 'a result =
  fun x ->
    fun h -> match x with | FStar_Pervasives_Native.None -> h () | res -> res
let (mk_type :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun u ->
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ u))
      FStar_Compiler_Range.dummyRange
let (is_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe result)
  =
  fun g ->
    fun t ->
      let aux t1 =
        let uu___ =
          let uu___1 = FStar_Syntax_Subst.compress t1 in
          uu___1.FStar_Syntax_Syntax.n in
        match uu___ with
        | FStar_Syntax_Syntax.Tm_type u -> return u
        | uu___1 -> fail () in
      let uu___ = aux t in
      handle_with uu___
        (fun uu___1 ->
           let uu___2 =
             let uu___3 = FStar_TypeChecker_Normalize.unfold_whnf g t in
             FStar_Syntax_Util.unrefine uu___3 in
           aux uu___2)
let (is_tot_arrow :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.typ) result)
  =
  fun g ->
    fun t ->
      let aux t1 =
        let uu___ =
          let uu___1 = FStar_Syntax_Subst.compress t1 in
          uu___1.FStar_Syntax_Syntax.n in
        match uu___ with
        | FStar_Syntax_Syntax.Tm_arrow (x::[], c) when
            FStar_Syntax_Util.is_total_comp c ->
            let uu___1 = FStar_Syntax_Subst.open_comp [x] c in
            (match uu___1 with
             | (x1::[], c1) ->
                 return (x1, (FStar_Syntax_Util.comp_result c1)))
        | FStar_Syntax_Syntax.Tm_arrow (x::xs, c) ->
            let t2 =
              FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (xs, c))
                t1.FStar_Syntax_Syntax.pos in
            let uu___1 = FStar_Syntax_Subst.open_term [x] t2 in
            (match uu___1 with | (x1::[], t3) -> return (x1, t3))
        | uu___1 -> fail () in
      let uu___ = aux t in
      handle_with uu___
        (fun uu___1 ->
           let uu___2 = FStar_TypeChecker_Normalize.unfold_whnf g t in
           aux uu___2)
let (check_arg_qual :
  FStar_Syntax_Syntax.aqual -> FStar_Syntax_Syntax.bqual -> unit result) =
  fun a ->
    fun b ->
      match (b, a) with
      | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) ->
          return ()
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit uu___),
         FStar_Pervasives_Native.Some
         { FStar_Syntax_Syntax.aqual_implicit = true;
           FStar_Syntax_Syntax.aqual_attributes = uu___1;_})
          -> return ()
      | (FStar_Pervasives_Native.Some uu___, FStar_Pervasives_Native.None) ->
          return ()
      | (FStar_Pervasives_Native.Some uu___, FStar_Pervasives_Native.Some
         { FStar_Syntax_Syntax.aqual_implicit = false;
           FStar_Syntax_Syntax.aqual_attributes = uu___1;_})
          -> return ()
      | uu___ -> fail ()
let (check_bqual :
  FStar_Syntax_Syntax.bqual -> FStar_Syntax_Syntax.bqual -> unit result) =
  fun b0 ->
    fun b1 ->
      match (b0, b1) with
      | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) ->
          return ()
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit b01),
         FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit b11))
          when b01 = b11 -> return ()
      | uu___ -> fail ()
let (close_guard :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.universes -> precondition -> precondition)
  =
  fun xs ->
    fun us ->
      fun g ->
        match g with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some t ->
            let uu___ =
              FStar_Compiler_List.fold_right2
                (fun u ->
                   fun x ->
                     fun t1 ->
                       FStar_Syntax_Util.mk_forall u
                         x.FStar_Syntax_Syntax.binder_bv t1) us xs t in
            FStar_Pervasives_Native.Some uu___
let (close_guard_with_definition :
  FStar_Syntax_Syntax.binder ->
    FStar_Syntax_Syntax.universe ->
      FStar_Syntax_Syntax.term -> precondition -> precondition)
  =
  fun x ->
    fun u ->
      fun t ->
        fun g ->
          match g with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some t1 ->
              let uu___ =
                let t2 =
                  let uu___1 =
                    let uu___2 =
                      FStar_Syntax_Syntax.bv_to_name
                        x.FStar_Syntax_Syntax.binder_bv in
                    FStar_Syntax_Util.mk_eq2 u
                      (x.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort
                      uu___2 t1 in
                  FStar_Syntax_Util.mk_imp uu___1 t1 in
                FStar_Syntax_Util.mk_forall u x.FStar_Syntax_Syntax.binder_bv
                  t2 in
              FStar_Pervasives_Native.Some uu___
let with_binders :
  'a .
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.universes -> 'a result -> 'a result
  =
  fun xs ->
    fun us ->
      fun f ->
        match f with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (t, g) ->
            let uu___ = let uu___1 = close_guard xs us g in (t, uu___1) in
            FStar_Pervasives_Native.Some uu___
let with_definition :
  'a .
    FStar_Syntax_Syntax.binder ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.term -> 'a result -> 'a result
  =
  fun x ->
    fun u ->
      fun t ->
        fun f ->
          match f with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (t1, g) ->
              let uu___ =
                let uu___1 = close_guard_with_definition x u (Obj.magic t1) g in
                (t1, uu___1) in
              FStar_Pervasives_Native.Some uu___
let (guard : FStar_Syntax_Syntax.typ -> unit result) =
  fun t ->
    FStar_Pervasives_Native.Some ((), (FStar_Pervasives_Native.Some t))
let (abs :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.term) ->
      FStar_Syntax_Syntax.term)
  =
  fun a ->
    fun f ->
      let x = FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None a in
      let xb = FStar_Syntax_Syntax.mk_binder x in
      let uu___ = f xb in
      FStar_Syntax_Util.abs [xb] uu___ FStar_Pervasives_Native.None
let (weaken_subtyping_guard :
  FStar_Syntax_Syntax.term -> precondition -> precondition) =
  fun p ->
    fun g ->
      FStar_Compiler_Util.map_opt g (fun q -> FStar_Syntax_Util.mk_imp p q)
let (strengthen_subtyping_guard :
  FStar_Syntax_Syntax.term -> precondition -> precondition) =
  fun p ->
    fun g ->
      let uu___ =
        let uu___1 =
          FStar_Compiler_Util.map_opt g
            (fun q -> FStar_Syntax_Util.mk_and p q) in
        FStar_Compiler_Util.dflt p uu___1 in
      FStar_Pervasives_Native.Some uu___
let weaken :
  'a .
    FStar_Syntax_Syntax.term ->
      'a result -> ('a * precondition) FStar_Pervasives_Native.option
  =
  fun p ->
    fun g ->
      match g with
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (x, q) ->
          let uu___ = let uu___1 = weaken_subtyping_guard p q in (x, uu___1) in
          FStar_Pervasives_Native.Some uu___
let strengthen :
  'a .
    FStar_Syntax_Syntax.term ->
      'a result -> ('a * precondition) FStar_Pervasives_Native.option
  =
  fun p ->
    fun g ->
      match g with
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (x, q) ->
          let uu___ =
            let uu___1 = strengthen_subtyping_guard p q in (x, uu___1) in
          FStar_Pervasives_Native.Some uu___
let (equatable :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t0 ->
    fun t1 ->
      let uu___ =
        let uu___1 =
          let uu___2 = FStar_Syntax_Subst.compress t0 in
          uu___2.FStar_Syntax_Syntax.n in
        let uu___2 =
          let uu___3 = FStar_Syntax_Subst.compress t1 in
          uu___3.FStar_Syntax_Syntax.n in
        (uu___1, uu___2) in
      match uu___ with
      | (FStar_Syntax_Syntax.Tm_name uu___1, uu___2) -> true
      | (uu___1, FStar_Syntax_Syntax.Tm_name uu___2) -> true
      | uu___1 -> false
let (apply_predicate :
  FStar_Syntax_Syntax.binder ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term)
  =
  fun x ->
    fun p ->
      fun e ->
        FStar_Syntax_Subst.subst
          [FStar_Syntax_Syntax.NT ((x.FStar_Syntax_Syntax.binder_bv), e)] p
let (curry_arrow :
  FStar_Syntax_Syntax.binder ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.comp ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun x ->
    fun xs ->
      fun c ->
        let tail =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (xs, c))
            FStar_Compiler_Range.dummyRange in
        let uu___ =
          let uu___1 =
            let uu___2 = FStar_Syntax_Syntax.mk_Total tail in ([x], uu___2) in
          FStar_Syntax_Syntax.Tm_arrow uu___1 in
        FStar_Syntax_Syntax.mk uu___ FStar_Compiler_Range.dummyRange
let (is_gtot_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c ->
    (FStar_Syntax_Util.is_tot_or_gtot_comp c) &&
      (let uu___ = FStar_Syntax_Util.is_total_comp c in
       Prims.op_Negation uu___)
let rec (check_subtype_whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit result)
  =
  fun g ->
    fun e ->
      fun t0 ->
        fun t1 ->
          let uu___ =
            let uu___1 =
              let uu___2 = FStar_Syntax_Subst.compress t0 in
              uu___2.FStar_Syntax_Syntax.n in
            let uu___2 =
              let uu___3 = FStar_Syntax_Subst.compress t1 in
              uu___3.FStar_Syntax_Syntax.n in
            (uu___1, uu___2) in
          match uu___ with
          | (FStar_Syntax_Syntax.Tm_refine (x0, p0), uu___1) ->
              let uu___2 =
                let uu___3 =
                  let uu___4 = FStar_Syntax_Syntax.mk_binder x0 in [uu___4] in
                FStar_Syntax_Subst.open_term uu___3 p0 in
              (match uu___2 with
               | (x01::[], p01) ->
                   let uu___3 = apply_predicate x01 p01 e in
                   let uu___4 =
                     check_subtype g e
                       (x01.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort
                       t1 in
                   weaken uu___3 uu___4)
          | (uu___1, FStar_Syntax_Syntax.Tm_refine (x1, p1)) ->
              let uu___2 =
                let uu___3 =
                  let uu___4 = FStar_Syntax_Syntax.mk_binder x1 in [uu___4] in
                FStar_Syntax_Subst.open_term uu___3 p1 in
              (match uu___2 with
               | (x11::[], p11) ->
                   let uu___3 = apply_predicate x11 p11 e in
                   let uu___4 =
                     check_subtype g e t0
                       (x11.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort in
                   strengthen uu___3 uu___4)
          | (FStar_Syntax_Syntax.Tm_arrow (x0::[], c0),
             FStar_Syntax_Syntax.Tm_arrow (x1::[], c1)) ->
              let uu___1 = FStar_Syntax_Subst.open_comp [x0] c0 in
              (match uu___1 with
               | (x01::[], c01) ->
                   let uu___2 = FStar_Syntax_Subst.open_comp [x1] c1 in
                   (match uu___2 with
                    | (x11::[], c11) ->
                        let uu___3 =
                          check_bqual x01.FStar_Syntax_Syntax.binder_qual
                            x11.FStar_Syntax_Syntax.binder_qual in
                        bind uu___3
                          (fun uu___4 ->
                             let uu___5 =
                               universe_of g
                                 (x11.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort in
                             bind uu___5
                               (fun u1 ->
                                  let uu___6 =
                                    let uu___7 =
                                      let uu___8 =
                                        FStar_Syntax_Syntax.bv_to_name
                                          x11.FStar_Syntax_Syntax.binder_bv in
                                      check_subtype g uu___8
                                        (x11.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort
                                        (x01.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort in
                                    bind uu___7
                                      (fun uu___8 ->
                                         let uu___9 =
                                           let uu___10 =
                                             let uu___11 =
                                               FStar_Syntax_Util.args_of_binders
                                                 [x11] in
                                             FStar_Pervasives_Native.snd
                                               uu___11 in
                                           FStar_Syntax_Syntax.mk_Tm_app e
                                             uu___10
                                             FStar_Compiler_Range.dummyRange in
                                         check_subcomp g uu___9 c01 c11) in
                                  with_binders [x11] [u1] uu___6))))
          | (FStar_Syntax_Syntax.Tm_arrow (x0::xs0, c0),
             FStar_Syntax_Syntax.Tm_arrow (x1::xs1, c1)) ->
              let uu___1 = curry_arrow x0 xs0 c0 in
              let uu___2 = curry_arrow x1 xs1 c1 in
              check_subtype_whnf g e uu___1 uu___2
          | uu___1 ->
              let uu___2 = equatable t0 t1 in
              if uu___2
              then
                let uu___3 = universe_of g t0 in
                bind uu___3
                  (fun u ->
                     let uu___4 =
                       let uu___5 = mk_type u in
                       FStar_Syntax_Util.mk_eq2 u uu___5 t0 t1 in
                     guard uu___4)
              else fail ()
and (check_subtype :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit result)
  =
  fun g ->
    fun e ->
      fun t0 ->
        fun t1 ->
          let uu___ = FStar_Syntax_Util.eq_tm t0 t1 in
          match uu___ with
          | FStar_Syntax_Util.Equal -> return ()
          | uu___1 ->
              let t01 =
                FStar_TypeChecker_Normalize.normalize_refinement
                  [FStar_TypeChecker_Env.Primops;
                  FStar_TypeChecker_Env.Weak;
                  FStar_TypeChecker_Env.HNF;
                  FStar_TypeChecker_Env.UnfoldUntil
                    FStar_Syntax_Syntax.delta_constant] g t0 in
              let t11 =
                FStar_TypeChecker_Normalize.normalize_refinement
                  [FStar_TypeChecker_Env.Primops;
                  FStar_TypeChecker_Env.Weak;
                  FStar_TypeChecker_Env.HNF;
                  FStar_TypeChecker_Env.UnfoldUntil
                    FStar_Syntax_Syntax.delta_constant] g t1 in
              check_subtype_whnf g e t01 t11
and (check_subcomp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp -> unit result)
  =
  fun g ->
    fun e ->
      fun c0 ->
        fun c1 ->
          let uu___ =
            ((FStar_Syntax_Util.is_total_comp c0) &&
               (FStar_Syntax_Util.is_tot_or_gtot_comp c1))
              || ((is_gtot_comp c0) && (is_gtot_comp c1)) in
          if uu___
          then
            check_subtype g e (FStar_Syntax_Util.comp_result c0)
              (FStar_Syntax_Util.comp_result c1)
          else fail ()
and (check :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ result)
  =
  fun g ->
    fun e ->
      let uu___ = lookup g e in
      match uu___ with
      | FStar_Pervasives_Native.Some r -> r
      | FStar_Pervasives_Native.None ->
          let r = check' g e in (insert g e r; r)
and (check' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ result)
  =
  fun g ->
    fun e ->
      let uu___ =
        let uu___1 = FStar_Syntax_Subst.compress e in
        uu___1.FStar_Syntax_Syntax.n in
      match uu___ with
      | FStar_Syntax_Syntax.Tm_meta (t, uu___1) -> check g t
      | FStar_Syntax_Syntax.Tm_uvar (uv, s) ->
          let uu___1 =
            let uu___2 = FStar_Syntax_Util.ctx_uvar_typ uv in
            FStar_Syntax_Subst.subst' s uu___2 in
          return uu___1
      | FStar_Syntax_Syntax.Tm_name x ->
          let uu___1 = FStar_TypeChecker_Env.lookup_bv g x in
          (match uu___1 with | (t, uu___2) -> return t)
      | FStar_Syntax_Syntax.Tm_fvar f ->
          let uu___1 =
            FStar_TypeChecker_Env.try_lookup_lid g
              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu___1 with
           | FStar_Pervasives_Native.Some (([], t), uu___2) -> return t
           | uu___2 -> fail ())
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
             FStar_Syntax_Syntax.pos = uu___1;
             FStar_Syntax_Syntax.vars = uu___2;
             FStar_Syntax_Syntax.hash_code = uu___3;_},
           us)
          ->
          let uu___4 =
            FStar_TypeChecker_Env.try_lookup_and_inst_lid g us
              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu___4 with
           | FStar_Pervasives_Native.None -> fail ()
           | FStar_Pervasives_Native.Some (t, uu___5) -> return t)
      | FStar_Syntax_Syntax.Tm_constant c ->
          let t =
            FStar_TypeChecker_TcTerm.tc_constant g e.FStar_Syntax_Syntax.pos
              c in
          return t
      | FStar_Syntax_Syntax.Tm_type u ->
          let uu___1 = mk_type (FStar_Syntax_Syntax.U_succ u) in
          return uu___1
      | FStar_Syntax_Syntax.Tm_refine (x, phi) ->
          let uu___1 =
            let uu___2 =
              let uu___3 = FStar_Syntax_Syntax.mk_binder x in [uu___3] in
            FStar_Syntax_Subst.open_term uu___2 phi in
          (match uu___1 with
           | (x1::[], phi1) ->
               let uu___2 =
                 check g
                   (x1.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort in
               bind uu___2
                 (fun t ->
                    let uu___3 = is_type g t in
                    bind uu___3
                      (fun u ->
                         let uu___4 =
                           let g' = FStar_TypeChecker_Env.push_binders g [x1] in
                           let uu___5 = check g' phi1 in
                           bind uu___5
                             (fun t' ->
                                let uu___6 = is_type g' t' in
                                bind uu___6 (fun uu___7 -> return t)) in
                         with_binders [x1] [u] uu___4)))
      | FStar_Syntax_Syntax.Tm_abs (xs, body, uu___1) ->
          let uu___2 = FStar_Syntax_Subst.open_term xs body in
          (match uu___2 with
           | (xs1, body1) ->
               let uu___3 = check_binders g xs1 in
               bind uu___3
                 (fun xs_g ->
                    let uu___4 = xs_g in
                    match uu___4 with
                    | (xs2, us, g1) ->
                        let uu___5 =
                          let uu___6 = check g1 body1 in
                          bind uu___6
                            (fun t ->
                               let uu___7 =
                                 let uu___8 = FStar_Syntax_Syntax.mk_Total t in
                                 FStar_Syntax_Util.arrow xs2 uu___8 in
                               return uu___7) in
                        with_binders xs2 us uu___5))
      | FStar_Syntax_Syntax.Tm_arrow (xs, c) ->
          let uu___1 = FStar_Syntax_Subst.open_comp xs c in
          (match uu___1 with
           | (xs1, c1) ->
               let uu___2 = check_binders g xs1 in
               bind uu___2
                 (fun xs_g ->
                    let uu___3 = xs_g in
                    match uu___3 with
                    | (xs2, us, g1) ->
                        let uu___4 =
                          let uu___5 = check_comp g1 c1 in
                          bind uu___5
                            (fun u ->
                               let uu___6 =
                                 mk_type
                                   (FStar_Syntax_Syntax.U_max (u :: us)) in
                               return uu___6) in
                        with_binders xs2 us uu___4))
      | FStar_Syntax_Syntax.Tm_app (hd, (arg, arg_qual)::[]) ->
          let uu___1 = check g hd in
          bind uu___1
            (fun t ->
               let uu___2 = is_tot_arrow g t in
               bind uu___2
                 (fun x_r ->
                    let uu___3 = x_r in
                    match uu___3 with
                    | (x, t') ->
                        let uu___4 = check g arg in
                        bind uu___4
                          (fun t_arg ->
                             let uu___5 =
                               check_subtype g arg t_arg
                                 (x.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort in
                             bind uu___5
                               (fun uu___6 ->
                                  let uu___7 =
                                    check_arg_qual arg_qual
                                      x.FStar_Syntax_Syntax.binder_qual in
                                  bind uu___7
                                    (fun uu___8 ->
                                       let uu___9 =
                                         FStar_Syntax_Subst.subst
                                           [FStar_Syntax_Syntax.NT
                                              ((x.FStar_Syntax_Syntax.binder_bv),
                                                arg)] t' in
                                       return uu___9)))))
      | FStar_Syntax_Syntax.Tm_app (hd, arg::args) ->
          let head =
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (hd, [arg]))
              e.FStar_Syntax_Syntax.pos in
          let t =
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (head, args))
              e.FStar_Syntax_Syntax.pos in
          check g t
      | FStar_Syntax_Syntax.Tm_ascribed
          (e1, (FStar_Pervasives.Inl t, uu___1, eq), uu___2) ->
          let uu___3 = check g e1 in
          bind uu___3
            (fun te ->
               let uu___4 = check g t in
               bind uu___4
                 (fun t' ->
                    let uu___5 = is_type g t' in
                    bind uu___5
                      (fun uu___6 ->
                         let uu___7 = check_subtype g e1 te t in
                         bind uu___7 (fun uu___8 -> return t))))
      | FStar_Syntax_Syntax.Tm_let ((false, lb::[]), body) ->
          let uu___1 = lb.FStar_Syntax_Syntax.lbname in
          (match uu___1 with
           | FStar_Pervasives.Inl x ->
               let uu___2 =
                 let uu___3 =
                   let uu___4 = FStar_Syntax_Syntax.mk_binder x in [uu___4] in
                 FStar_Syntax_Subst.open_term uu___3 body in
               (match uu___2 with
                | (x1::[], body1) ->
                    let uu___3 =
                      FStar_Ident.lid_equals lb.FStar_Syntax_Syntax.lbeff
                        FStar_Parser_Const.effect_Tot_lid in
                    if uu___3
                    then
                      let uu___4 = check g lb.FStar_Syntax_Syntax.lbdef in
                      bind uu___4
                        (fun tdef ->
                           let uu___5 = check g lb.FStar_Syntax_Syntax.lbtyp in
                           bind uu___5
                             (fun ttyp ->
                                let uu___6 = is_type g ttyp in
                                bind uu___6
                                  (fun u ->
                                     let uu___7 =
                                       check_subtype g
                                         lb.FStar_Syntax_Syntax.lbdef tdef
                                         ttyp in
                                     bind uu___7
                                       (fun uu___8 ->
                                          let uu___9 =
                                            let g1 =
                                              FStar_TypeChecker_Env.push_binders
                                                g [x1] in
                                            check g1 body1 in
                                          with_definition x1 u
                                            lb.FStar_Syntax_Syntax.lbdef
                                            uu___9))))
                    else fail ()))
      | FStar_Syntax_Syntax.Tm_match
          (sc, FStar_Pervasives_Native.None, branches,
           FStar_Pervasives_Native.Some
           { FStar_Syntax_Syntax.residual_effect = uu___1;
             FStar_Syntax_Syntax.residual_typ = FStar_Pervasives_Native.Some
               t;
             FStar_Syntax_Syntax.residual_flags = uu___2;_})
          -> fail ()
      | FStar_Syntax_Syntax.Tm_match uu___1 -> fail ()
      | uu___1 -> fail ()
and (check_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.universe Prims.list
        * FStar_TypeChecker_Env.env) result)
  =
  fun g ->
    fun xs ->
      match xs with
      | [] -> return ([], [], g)
      | x::xs1 ->
          let uu___ =
            check g
              (x.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort in
          bind uu___
            (fun t ->
               let uu___1 = is_type g t in
               bind uu___1
                 (fun u ->
                    let uu___2 =
                      let g' = FStar_TypeChecker_Env.push_binders g [x] in
                      let uu___3 = check_binders g' xs1 in
                      bind uu___3
                        (fun xs_g ->
                           let uu___4 = xs_g in
                           match uu___4 with
                           | (xs2, us, g1) ->
                               return ((x :: xs2), (u :: us), g1)) in
                    with_binders [x] [u] uu___2))
and (check_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.universe result)
  =
  fun g ->
    fun c ->
      let uu___ = FStar_Syntax_Util.is_tot_or_gtot_comp c in
      if uu___
      then
        let uu___1 = check g (FStar_Syntax_Util.comp_result c) in
        bind uu___1 (fun t -> is_type g t)
      else fail ()
and (universe_of :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.universe result)
  =
  fun g ->
    fun t -> let uu___ = check g t in bind uu___ (fun t1 -> is_type g t1)