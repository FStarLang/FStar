open Prims
type env =
  {
  tcenv: FStar_TypeChecker_Env.env ;
  allow_universe_instantiation: Prims.bool }
let (__proj__Mkenv__item__tcenv : env -> FStar_TypeChecker_Env.env) =
  fun projectee ->
    match projectee with | { tcenv; allow_universe_instantiation;_} -> tcenv
let (__proj__Mkenv__item__allow_universe_instantiation : env -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { tcenv; allow_universe_instantiation;_} ->
        allow_universe_instantiation
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun g ->
    fun bs ->
      let uu___ = FStar_TypeChecker_Env.push_binders g.tcenv bs in
      {
        tcenv = uu___;
        allow_universe_instantiation = (g.allow_universe_instantiation)
      }
type precondition = FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option
type 'a success = ('a * precondition)
type context =
  (Prims.string * FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
    Prims.list
let (print_context : context -> Prims.string) =
  fun ctx ->
    let rec aux depth ctx1 =
      match ctx1 with
      | [] -> ""
      | (msg, topt)::tl ->
          let hd =
            let uu___ =
              match topt with
              | FStar_Pervasives_Native.None -> ""
              | FStar_Pervasives_Native.Some t ->
                  FStar_Syntax_Print.term_to_string t in
            FStar_Compiler_Util.format3 "%s %s (%s)\n" depth msg uu___ in
          let tl1 = aux (Prims.op_Hat depth ">") tl in Prims.op_Hat hd tl1 in
    aux "" (FStar_Compiler_List.rev ctx)
type error = (context * Prims.string)
let (print_error : error -> Prims.string) =
  fun err ->
    let uu___ = err in
    match uu___ with
    | (ctx, msg) ->
        let uu___1 = print_context ctx in
        FStar_Compiler_Util.format2 "%s%s" uu___1 msg
type 'a result = context -> ('a success, error) FStar_Pervasives.either
type hash_entry =
  {
  he_term: FStar_Syntax_Syntax.term ;
  he_gamma: FStar_Syntax_Syntax.binding Prims.list ;
  he_res: FStar_Syntax_Syntax.typ success }
let (__proj__Mkhash_entry__item__he_term :
  hash_entry -> FStar_Syntax_Syntax.term) =
  fun projectee ->
    match projectee with | { he_term; he_gamma; he_res;_} -> he_term
let (__proj__Mkhash_entry__item__he_gamma :
  hash_entry -> FStar_Syntax_Syntax.binding Prims.list) =
  fun projectee ->
    match projectee with | { he_term; he_gamma; he_res;_} -> he_gamma
let (__proj__Mkhash_entry__item__he_res :
  hash_entry -> FStar_Syntax_Syntax.typ success) =
  fun projectee ->
    match projectee with | { he_term; he_gamma; he_res;_} -> he_res
type tc_table = (FStar_Syntax_Syntax.term, hash_entry) FStar_Hash.hashtable
let (table : tc_table) = FStar_Hash.create FStar_Syntax_Hash.equal_term
let (clear_memo_table : unit -> unit) = fun uu___ -> FStar_Hash.clear table
let (insert :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ success -> unit)
  =
  fun g ->
    fun e ->
      fun res ->
        let entry =
          {
            he_term = e;
            he_gamma = ((g.tcenv).FStar_TypeChecker_Env.gamma);
            he_res = res
          } in
        FStar_Hash.insert (e, FStar_Syntax_Hash.hash_term) entry table
let return : 'a . 'a -> 'a result =
  fun x ->
    fun uu___ -> FStar_Pervasives.Inl (x, FStar_Pervasives_Native.None)
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
      fun ctx0 ->
        let uu___ = x ctx0 in
        match uu___ with
        | FStar_Pervasives.Inl (x1, g1) ->
            let uu___1 = let uu___2 = y x1 in uu___2 ctx0 in
            (match uu___1 with
             | FStar_Pervasives.Inl (y1, g2) ->
                 let uu___2 = let uu___3 = and_pre g1 g2 in (y1, uu___3) in
                 FStar_Pervasives.Inl uu___2
             | err -> err)
        | FStar_Pervasives.Inr err -> FStar_Pervasives.Inr err
let fail : 'a . Prims.string -> 'a result =
  fun msg -> fun ctx -> FStar_Pervasives.Inr (ctx, msg)
let (dump_context : unit result) =
  fun ctx ->
    (let uu___1 = print_context ctx in
     FStar_Compiler_Util.print_string uu___1);
    (let uu___1 = return () in uu___1 ctx)
let handle_with : 'a . 'a result -> (unit -> 'a result) -> 'a result =
  fun x ->
    fun h ->
      fun ctx ->
        let uu___ = x ctx in
        match uu___ with
        | FStar_Pervasives.Inr uu___1 -> let uu___2 = h () in uu___2 ctx
        | res -> res
let with_context :
  'a .
    Prims.string ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
        (unit -> 'a result) -> 'a result
  =
  fun msg ->
    fun t -> fun x -> fun ctx -> let uu___ = x () in uu___ ((msg, t) :: ctx)
let (mk_type :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun u ->
    FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)
      FStar_Compiler_Range.dummyRange
let (is_type :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe result) =
  fun g ->
    fun t ->
      let aux t1 =
        let uu___ =
          let uu___1 = FStar_Syntax_Subst.compress t1 in
          uu___1.FStar_Syntax_Syntax.n in
        match uu___ with
        | FStar_Syntax_Syntax.Tm_type u -> return u
        | uu___1 ->
            let uu___2 =
              let uu___3 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Compiler_Util.format1 "Expected a type; got %s" uu___3 in
            fail uu___2 in
      with_context "is_type" (FStar_Pervasives_Native.Some t)
        (fun uu___ ->
           let uu___1 = aux t in
           handle_with uu___1
             (fun uu___2 ->
                let uu___3 =
                  let uu___4 =
                    FStar_TypeChecker_Normalize.unfold_whnf g.tcenv t in
                  FStar_Syntax_Util.unrefine uu___4 in
                aux uu___3))
let (is_tot_arrow :
  env ->
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
        | FStar_Syntax_Syntax.Tm_arrow (x::[], c) ->
            let uu___1 = FStar_Syntax_Util.is_total_comp c in
            if uu___1
            then
              let uu___2 = FStar_Syntax_Subst.open_comp [x] c in
              (match uu___2 with
               | (x1::[], c1) ->
                   return (x1, (FStar_Syntax_Util.comp_result c1)))
            else fail "Expected total arrow"
        | FStar_Syntax_Syntax.Tm_arrow (x::xs, c) ->
            let t2 =
              FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (xs, c))
                t1.FStar_Syntax_Syntax.pos in
            let uu___1 = FStar_Syntax_Subst.open_term [x] t2 in
            (match uu___1 with | (x1::[], t3) -> return (x1, t3))
        | uu___1 -> fail "Expected an arrow" in
      with_context "is_tot_arrow" FStar_Pervasives_Native.None
        (fun uu___ ->
           let uu___1 = aux t in
           handle_with uu___1
             (fun uu___2 ->
                let uu___3 =
                  FStar_TypeChecker_Normalize.unfold_whnf g.tcenv t in
                aux uu___3))
let (check_arg_qual :
  FStar_Syntax_Syntax.aqual -> FStar_Syntax_Syntax.bqual -> unit result) =
  fun a ->
    fun b ->
      match b with
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit uu___) ->
          (match a with
           | FStar_Pervasives_Native.Some
               { FStar_Syntax_Syntax.aqual_implicit = true;
                 FStar_Syntax_Syntax.aqual_attributes = uu___1;_}
               -> return ()
           | uu___1 -> fail "missing arg qualifier implicit")
      | uu___ ->
          (match a with
           | FStar_Pervasives_Native.Some
               { FStar_Syntax_Syntax.aqual_implicit = true;
                 FStar_Syntax_Syntax.aqual_attributes = uu___1;_}
               -> fail "extra arg qualifier implicit"
           | uu___1 -> return ())
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
      | uu___ -> fail "Binder qualifier mismatch"
let (check_aqual :
  FStar_Syntax_Syntax.aqual -> FStar_Syntax_Syntax.aqual -> unit result) =
  fun a0 ->
    fun a1 ->
      match (a0, a1) with
      | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) ->
          return ()
      | (FStar_Pervasives_Native.Some
         { FStar_Syntax_Syntax.aqual_implicit = b0;
           FStar_Syntax_Syntax.aqual_attributes = uu___;_},
         FStar_Pervasives_Native.Some
         { FStar_Syntax_Syntax.aqual_implicit = b1;
           FStar_Syntax_Syntax.aqual_attributes = uu___1;_})
          -> if b0 = b1 then return () else fail "Unequal arg qualifiers"
      | uu___ -> fail "Unequal arg qualifiers"
let (mk_forall_l :
  FStar_Syntax_Syntax.universes ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun us ->
    fun xs ->
      fun t ->
        FStar_Compiler_List.fold_right2
          (fun u ->
             fun x ->
               fun t1 ->
                 FStar_Syntax_Util.mk_forall u
                   x.FStar_Syntax_Syntax.binder_bv t1) us xs t
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
            let uu___ = mk_forall_l us xs t in
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
        fun ctx ->
          let uu___ = f ctx in
          match uu___ with
          | FStar_Pervasives.Inl (t, g) ->
              let uu___1 = let uu___2 = close_guard xs us g in (t, uu___2) in
              FStar_Pervasives.Inl uu___1
          | err -> err
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
          fun ctx ->
            let uu___ = f ctx in
            match uu___ with
            | FStar_Pervasives.Inl (a1, g) ->
                let uu___1 =
                  let uu___2 = close_guard_with_definition x u t g in
                  (a1, uu___2) in
                FStar_Pervasives.Inl uu___1
            | err -> err
let (guard : FStar_Syntax_Syntax.typ -> unit result) =
  fun t ->
    fun uu___ -> FStar_Pervasives.Inl ((), (FStar_Pervasives_Native.Some t))
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
      'a result -> context -> ('a success, error) FStar_Pervasives.either
  =
  fun p ->
    fun g ->
      fun ctx ->
        let uu___ = g ctx in
        match uu___ with
        | FStar_Pervasives.Inl (x, q) ->
            let uu___1 =
              let uu___2 = weaken_subtyping_guard p q in (x, uu___2) in
            FStar_Pervasives.Inl uu___1
        | err -> err
let strengthen :
  'a .
    FStar_Syntax_Syntax.term ->
      'a result -> context -> ('a success, error) FStar_Pervasives.either
  =
  fun p ->
    fun g ->
      fun ctx ->
        let uu___ = g ctx in
        match uu___ with
        | FStar_Pervasives.Inl (x, q) ->
            let uu___1 =
              let uu___2 = strengthen_subtyping_guard p q in (x, uu___2) in
            FStar_Pervasives.Inl uu___1
        | err -> err
let no_guard : 'a . 'a result -> 'a result =
  fun g ->
    fun ctx ->
      let uu___ = g ctx in
      match uu___ with
      | FStar_Pervasives.Inl (x, FStar_Pervasives_Native.None) ->
          FStar_Pervasives.Inl (x, FStar_Pervasives_Native.None)
      | FStar_Pervasives.Inl uu___1 ->
          let uu___2 = fail "Unexpected guard" in uu___2 ctx
      | err -> err
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
let rec (context_included :
  FStar_Syntax_Syntax.binding Prims.list ->
    FStar_Syntax_Syntax.binding Prims.list -> Prims.bool)
  =
  fun g0 ->
    fun g1 ->
      match (g0, g1) with
      | ([], uu___) -> true
      | (b0::g0', b1::g1') ->
          (match (b0, b1) with
           | (FStar_Syntax_Syntax.Binding_var x0,
              FStar_Syntax_Syntax.Binding_var x1) ->
               if x0.FStar_Syntax_Syntax.index = x1.FStar_Syntax_Syntax.index
               then context_included g0' g1'
               else context_included g0 g1'
           | (FStar_Syntax_Syntax.Binding_lid uu___,
              FStar_Syntax_Syntax.Binding_lid uu___1) -> true
           | (FStar_Syntax_Syntax.Binding_univ uu___,
              FStar_Syntax_Syntax.Binding_univ uu___1) -> true
           | uu___ -> false)
      | uu___ -> false
let (curry_application :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
      FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
        FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
        Prims.list ->
        FStar_Compiler_Range.range ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun hd ->
    fun arg ->
      fun args ->
        fun p ->
          let head =
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (hd, [arg])) p in
          let t =
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (head, args))
              p in
          t
let (lookup :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ result) =
  fun g ->
    fun e ->
      let uu___ = FStar_Hash.lookup (e, FStar_Syntax_Hash.hash_term) table in
      match uu___ with
      | FStar_Pervasives_Native.None -> fail "not in cache"
      | FStar_Pervasives_Native.Some he ->
          let uu___1 =
            context_included he.he_gamma
              (g.tcenv).FStar_TypeChecker_Env.gamma in
          if uu___1
          then (fun uu___2 -> FStar_Pervasives.Inl (he.he_res))
          else fail "not in cache"
let (check_no_escape :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.term -> unit result) =
  fun bs ->
    fun t ->
      let xs = FStar_Syntax_Free.names t in
      let uu___ =
        FStar_Compiler_Util.for_all
          (fun b ->
             let uu___1 =
               FStar_Compiler_Util.set_mem b.FStar_Syntax_Syntax.binder_bv xs in
             Prims.op_Negation uu___1) bs in
      if uu___ then return () else fail "Name escapes its scope"
let rec iter2 :
  'a 'b .
    'a Prims.list ->
      'a Prims.list -> ('a -> 'a -> 'b -> 'b result) -> 'b -> 'b result
  =
  fun xs ->
    fun ys ->
      fun f ->
        fun b1 ->
          match (xs, ys) with
          | ([], []) -> return b1
          | (x::xs1, y::ys1) ->
              let uu___ = f x y b1 in
              bind uu___ (fun b2 -> iter2 xs1 ys1 f b2)
          | uu___ -> fail "Lists of differing length"
let rec (check_subtype_whnf :
  env ->
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
          | (FStar_Syntax_Syntax.Tm_app (hd0, args0),
             FStar_Syntax_Syntax.Tm_app (hd1, args1)) ->
              let uu___1 = check_equality_whnf g hd0 hd1 in
              bind uu___1
                (fun uu___2 ->
                   iter2 args0 args1
                     (fun uu___3 ->
                        fun uu___4 ->
                          fun uu___5 ->
                            match (uu___3, uu___4) with
                            | ((a0, q0), (a1, q1)) ->
                                let uu___6 = check_aqual q0 q1 in
                                bind uu___6
                                  (fun uu___7 -> check_equality g a0 a1)) ())
          | (FStar_Syntax_Syntax.Tm_type u0, FStar_Syntax_Syntax.Tm_type u1)
              -> check_equality_whnf g t0 t1
          | uu___1 ->
              let uu___2 =
                let uu___3 = FStar_Syntax_Util.eq_tm t0 t1 in
                uu___3 = FStar_Syntax_Util.Equal in
              if uu___2
              then return ()
              else
                (let uu___4 = equatable t0 t1 in
                 if uu___4
                 then
                   let uu___5 = universe_of g t0 in
                   bind uu___5
                     (fun u ->
                        let uu___6 =
                          let uu___7 = mk_type u in
                          FStar_Syntax_Util.mk_eq2 u uu___7 t0 t1 in
                        guard uu___6)
                 else
                   (let uu___6 =
                      let uu___7 = FStar_Syntax_Print.term_to_string t0 in
                      let uu___8 = FStar_Syntax_Print.term_to_string t1 in
                      FStar_Compiler_Util.format2
                        "Subtyping failed: %s </: %s" uu___7 uu___8 in
                    fail uu___6))
and (check_subtype :
  env ->
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
                    FStar_Syntax_Syntax.delta_constant] g.tcenv t0 in
              let t11 =
                FStar_TypeChecker_Normalize.normalize_refinement
                  [FStar_TypeChecker_Env.Primops;
                  FStar_TypeChecker_Env.Weak;
                  FStar_TypeChecker_Env.HNF;
                  FStar_TypeChecker_Env.UnfoldUntil
                    FStar_Syntax_Syntax.delta_constant] g.tcenv t1 in
              check_subtype_whnf g e t01 t11
and (check_equality_whnf :
  env -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit result) =
  fun g ->
    fun t0 ->
      fun t1 ->
        let fail1 uu___ =
          let uu___1 =
            let uu___2 = FStar_Syntax_Print.term_to_string t0 in
            let uu___3 = FStar_Syntax_Print.term_to_string t1 in
            FStar_Compiler_Util.format2 "not equal terms: %s <> %s" uu___2
              uu___3 in
          fail uu___1 in
        let uu___ =
          let uu___1 = FStar_Syntax_Util.eq_tm t0 t1 in
          uu___1 = FStar_Syntax_Util.Equal in
        if uu___
        then return ()
        else
          if g.allow_universe_instantiation
          then
            (match ((t0.FStar_Syntax_Syntax.n), (t1.FStar_Syntax_Syntax.n))
             with
             | (FStar_Syntax_Syntax.Tm_uinst (f0, us0),
                FStar_Syntax_Syntax.Tm_uinst (f1, us1)) ->
                 let uu___2 =
                   let uu___3 = FStar_Syntax_Util.eq_tm f0 f1 in
                   uu___3 = FStar_Syntax_Util.Equal in
                 if uu___2
                 then
                   let uu___3 =
                     FStar_TypeChecker_Rel.teq_nosmt_force g.tcenv t0 t1 in
                   (if uu___3 then return () else fail1 ())
                 else fail1 ()
             | (FStar_Syntax_Syntax.Tm_type u0, FStar_Syntax_Syntax.Tm_type
                u1) ->
                 let uu___2 =
                   FStar_TypeChecker_Rel.teq_nosmt_force g.tcenv t0 t1 in
                 if uu___2 then return () else fail1 ()
             | uu___2 -> fail1 ())
          else fail1 ()
and (check_equality :
  env -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit result) =
  fun g ->
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
                  FStar_Syntax_Syntax.delta_constant] g.tcenv t0 in
            let t11 =
              FStar_TypeChecker_Normalize.normalize_refinement
                [FStar_TypeChecker_Env.Primops;
                FStar_TypeChecker_Env.Weak;
                FStar_TypeChecker_Env.HNF;
                FStar_TypeChecker_Env.UnfoldUntil
                  FStar_Syntax_Syntax.delta_constant] g.tcenv t1 in
            check_equality_whnf g t01 t11
and (check_subcomp :
  env ->
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
          else fail "Subcomp failed"
and (memo_check :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ result) =
  fun g ->
    fun e ->
      let uu___ = lookup g e in
      handle_with uu___
        (fun uu___1 ->
           fun ctx ->
             let r = let uu___2 = check' g e in uu___2 ctx in
             match r with
             | FStar_Pervasives.Inl res -> (insert g e res; r)
             | uu___2 -> r)
and (check :
  Prims.string ->
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ result)
  =
  fun msg ->
    fun g ->
      fun e ->
        with_context msg (FStar_Pervasives_Native.Some e)
          (fun uu___ -> memo_check g e)
and (check' :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ result) =
  fun g ->
    fun e ->
      let e1 = FStar_Syntax_Subst.compress e in
      match e1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta (t, uu___) -> memo_check g t
      | FStar_Syntax_Syntax.Tm_uvar (uv, s) ->
          let uu___ =
            let uu___1 = FStar_Syntax_Util.ctx_uvar_typ uv in
            FStar_Syntax_Subst.subst' s uu___1 in
          return uu___
      | FStar_Syntax_Syntax.Tm_name x ->
          let uu___ = FStar_TypeChecker_Env.lookup_bv g.tcenv x in
          (match uu___ with | (t, uu___1) -> return t)
      | FStar_Syntax_Syntax.Tm_fvar f ->
          let uu___ =
            FStar_TypeChecker_Env.try_lookup_lid g.tcenv
              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu___ with
           | FStar_Pervasives_Native.Some (([], t), uu___1) -> return t
           | uu___1 -> fail "Missing universes instantiation")
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
             FStar_Syntax_Syntax.pos = uu___;
             FStar_Syntax_Syntax.vars = uu___1;
             FStar_Syntax_Syntax.hash_code = uu___2;_},
           us)
          ->
          let uu___3 =
            FStar_TypeChecker_Env.try_lookup_and_inst_lid g.tcenv us
              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu___3 with
           | FStar_Pervasives_Native.None -> fail "Top-level name not found"
           | FStar_Pervasives_Native.Some (t, uu___4) -> return t)
      | FStar_Syntax_Syntax.Tm_constant c ->
          (match c with
           | FStar_Const.Const_range_of -> fail "Unhandled constant"
           | FStar_Const.Const_set_range_of -> fail "Unhandled constant"
           | FStar_Const.Const_reify -> fail "Unhandled constant"
           | FStar_Const.Const_reflect uu___ -> fail "Unhandled constant"
           | uu___ ->
               let t =
                 FStar_TypeChecker_TcTerm.tc_constant g.tcenv
                   e1.FStar_Syntax_Syntax.pos c in
               return t)
      | FStar_Syntax_Syntax.Tm_type u ->
          let uu___ = mk_type (FStar_Syntax_Syntax.U_succ u) in return uu___
      | FStar_Syntax_Syntax.Tm_refine (x, phi) ->
          let uu___ =
            let uu___1 =
              let uu___2 = FStar_Syntax_Syntax.mk_binder x in [uu___2] in
            FStar_Syntax_Subst.open_term uu___1 phi in
          (match uu___ with
           | (x1::[], phi1) ->
               let uu___1 =
                 check "refinement head" g
                   (x1.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort in
               bind uu___1
                 (fun t ->
                    let uu___2 = is_type g t in
                    bind uu___2
                      (fun u ->
                         let uu___3 =
                           let g' = push_binders g [x1] in
                           let uu___4 = check "refinement formula" g' phi1 in
                           bind uu___4
                             (fun t' ->
                                let uu___5 = is_type g' t' in
                                bind uu___5 (fun uu___6 -> return t)) in
                         with_binders [x1] [u] uu___3)))
      | FStar_Syntax_Syntax.Tm_abs (xs, body, uu___) ->
          let uu___1 = FStar_Syntax_Subst.open_term xs body in
          (match uu___1 with
           | (xs1, body1) ->
               let uu___2 =
                 with_context "abs binders" FStar_Pervasives_Native.None
                   (fun uu___3 -> check_binders g xs1) in
               bind uu___2
                 (fun xs_g ->
                    let uu___3 = xs_g in
                    match uu___3 with
                    | (xs2, us, g1) ->
                        let uu___4 =
                          let uu___5 = check "abs body" g1 body1 in
                          bind uu___5
                            (fun t ->
                               let uu___6 =
                                 let uu___7 = FStar_Syntax_Syntax.mk_Total t in
                                 FStar_Syntax_Util.arrow xs2 uu___7 in
                               return uu___6) in
                        with_binders xs2 us uu___4))
      | FStar_Syntax_Syntax.Tm_arrow (xs, c) ->
          let uu___ = FStar_Syntax_Subst.open_comp xs c in
          (match uu___ with
           | (xs1, c1) ->
               let uu___1 =
                 with_context "arrow binders" FStar_Pervasives_Native.None
                   (fun uu___2 -> check_binders g xs1) in
               bind uu___1
                 (fun xs_g ->
                    let uu___2 = xs_g in
                    match uu___2 with
                    | (xs2, us, g1) ->
                        let uu___3 =
                          let uu___4 =
                            with_context "arrow comp"
                              FStar_Pervasives_Native.None
                              (fun uu___5 -> check_comp g1 c1) in
                          bind uu___4
                            (fun u ->
                               let uu___5 =
                                 mk_type
                                   (FStar_Syntax_Syntax.U_max (u :: us)) in
                               return uu___5) in
                        with_binders xs2 us uu___3))
      | FStar_Syntax_Syntax.Tm_app (hd, (arg, arg_qual)::[]) ->
          let uu___ = check "app head" g hd in
          bind uu___
            (fun t ->
               let uu___1 = is_tot_arrow g t in
               bind uu___1
                 (fun x_r ->
                    let uu___2 = x_r in
                    match uu___2 with
                    | (x, t') ->
                        let uu___3 = check "app arg" g arg in
                        bind uu___3
                          (fun t_arg ->
                             let uu___4 =
                               with_context "app subtyping"
                                 FStar_Pervasives_Native.None
                                 (fun uu___5 ->
                                    check_subtype g arg t_arg
                                      (x.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort) in
                             bind uu___4
                               (fun uu___5 ->
                                  let uu___6 =
                                    with_context "app arg qual"
                                      FStar_Pervasives_Native.None
                                      (fun uu___7 ->
                                         check_arg_qual arg_qual
                                           x.FStar_Syntax_Syntax.binder_qual) in
                                  bind uu___6
                                    (fun uu___7 ->
                                       let uu___8 =
                                         FStar_Syntax_Subst.subst
                                           [FStar_Syntax_Syntax.NT
                                              ((x.FStar_Syntax_Syntax.binder_bv),
                                                arg)] t' in
                                       return uu___8)))))
      | FStar_Syntax_Syntax.Tm_app (hd, arg::args) ->
          let head =
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (hd, [arg]))
              e1.FStar_Syntax_Syntax.pos in
          let t =
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (head, args))
              e1.FStar_Syntax_Syntax.pos in
          memo_check g t
      | FStar_Syntax_Syntax.Tm_ascribed
          (e2, (FStar_Pervasives.Inl t, uu___, eq), uu___1) ->
          let uu___2 = check "ascription head" g e2 in
          bind uu___2
            (fun te ->
               let uu___3 = check "ascription type" g t in
               bind uu___3
                 (fun t' ->
                    let uu___4 = is_type g t' in
                    bind uu___4
                      (fun uu___5 ->
                         let uu___6 =
                           with_context "ascription subtyping"
                             FStar_Pervasives_Native.None
                             (fun uu___7 -> check_subtype g e2 te t) in
                         bind uu___6 (fun uu___7 -> return t))))
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu___, (FStar_Pervasives.Inr e2, uu___1, uu___2), uu___3) ->
          fail "Effect ascriptions are not handled yet"
      | FStar_Syntax_Syntax.Tm_let ((false, lb::[]), body) ->
          let uu___ = lb.FStar_Syntax_Syntax.lbname in
          (match uu___ with
           | FStar_Pervasives.Inl x ->
               let uu___1 =
                 let uu___2 =
                   let uu___3 = FStar_Syntax_Syntax.mk_binder x in [uu___3] in
                 FStar_Syntax_Subst.open_term uu___2 body in
               (match uu___1 with
                | (x1::[], body1) ->
                    let uu___2 =
                      FStar_Ident.lid_equals lb.FStar_Syntax_Syntax.lbeff
                        FStar_Parser_Const.effect_Tot_lid in
                    if uu___2
                    then
                      let uu___3 =
                        check "let definition" g lb.FStar_Syntax_Syntax.lbdef in
                      bind uu___3
                        (fun tdef ->
                           let uu___4 =
                             check "let type" g lb.FStar_Syntax_Syntax.lbtyp in
                           bind uu___4
                             (fun ttyp ->
                                let uu___5 = is_type g ttyp in
                                bind uu___5
                                  (fun u ->
                                     let uu___6 =
                                       with_context "let subtyping"
                                         FStar_Pervasives_Native.None
                                         (fun uu___7 ->
                                            check_subtype g
                                              lb.FStar_Syntax_Syntax.lbdef
                                              tdef ttyp) in
                                     bind uu___6
                                       (fun uu___7 ->
                                          let uu___8 =
                                            let g1 = push_binders g [x1] in
                                            let uu___9 =
                                              check "let body" g1 body1 in
                                            bind uu___9
                                              (fun t ->
                                                 let uu___10 =
                                                   check_no_escape [x1] t in
                                                 bind uu___10
                                                   (fun uu___11 -> return t)) in
                                          with_definition x1 u
                                            lb.FStar_Syntax_Syntax.lbdef
                                            uu___8))))
                    else fail "Let binding is effectful"))
      | FStar_Syntax_Syntax.Tm_match
          (sc, FStar_Pervasives_Native.None, branches, rc_opt) ->
          let uu___ = check "scrutinee" g sc in
          bind uu___
            (fun t_sc ->
               let uu___1 =
                 with_context "universe_of"
                   (FStar_Pervasives_Native.Some t_sc)
                   (fun uu___2 -> universe_of g t_sc) in
               bind uu___1
                 (fun u_sc ->
                    let rec check_branches path_condition branch_typ_opt
                      branches1 =
                      match branches1 with
                      | [] ->
                          (match branch_typ_opt with
                           | FStar_Pervasives_Native.None ->
                               fail "could not compute a type for the match"
                           | FStar_Pervasives_Native.Some t ->
                               let uu___2 =
                                 let uu___3 =
                                   FStar_Syntax_Util.mk_imp path_condition
                                     FStar_Syntax_Util.t_false in
                                 guard uu___3 in
                               bind uu___2 (fun uu___3 -> return t))
                      | (p, FStar_Pervasives_Native.None, b)::rest ->
                          let uu___2 =
                            FStar_TypeChecker_PatternUtils.raw_pat_as_exp
                              g.tcenv p in
                          (match uu___2 with
                           | FStar_Pervasives_Native.None ->
                               fail "Ill-formed pattern"
                           | FStar_Pervasives_Native.Some (e2, bvs) ->
                               let binders =
                                 FStar_Compiler_List.map
                                   FStar_Syntax_Syntax.mk_binder bvs in
                               let uu___3 = check_binders g binders in
                               bind uu___3
                                 (fun bs_g ->
                                    let uu___4 = bs_g in
                                    match uu___4 with
                                    | (bs, us, g') ->
                                        let uu___5 =
                                          check "pattern term" g' e2 in
                                        bind uu___5
                                          (fun t ->
                                             let uu___6 =
                                               let uu___7 =
                                                 check_subtype g' e2 t_sc t in
                                               no_guard uu___7 in
                                             bind uu___6
                                               (fun uu___7 ->
                                                  let pat_sc_eq =
                                                    FStar_Syntax_Util.mk_eq2
                                                      u_sc t_sc sc e2 in
                                                  let uu___8 =
                                                    let uu___9 =
                                                      let uu___10 =
                                                        FStar_Syntax_Util.mk_conj
                                                          path_condition
                                                          pat_sc_eq in
                                                      let uu___11 =
                                                        let uu___12 =
                                                          check "branch" g' b in
                                                        bind uu___12
                                                          (fun tbr ->
                                                             match branch_typ_opt
                                                             with
                                                             | FStar_Pervasives_Native.None
                                                                 ->
                                                                 let uu___13
                                                                   =
                                                                   check_no_escape
                                                                    bs tbr in
                                                                 bind uu___13
                                                                   (fun
                                                                    uu___14
                                                                    ->
                                                                    return
                                                                    tbr)
                                                             | FStar_Pervasives_Native.Some
                                                                 expect_tbr
                                                                 ->
                                                                 let uu___13
                                                                   =
                                                                   check_subtype
                                                                    g' b tbr
                                                                    expect_tbr in
                                                                 bind uu___13
                                                                   (fun
                                                                    uu___14
                                                                    ->
                                                                    return
                                                                    expect_tbr)) in
                                                      weaken uu___10 uu___11 in
                                                    with_binders bs us uu___9 in
                                                  bind uu___8
                                                    (fun tbr ->
                                                       let path_condition1 =
                                                         let uu___9 =
                                                           let uu___10 =
                                                             FStar_Syntax_Util.mk_neg
                                                               pat_sc_eq in
                                                           mk_forall_l us bs
                                                             uu___10 in
                                                         FStar_Syntax_Util.mk_conj
                                                           path_condition
                                                           uu___9 in
                                                       match p.FStar_Syntax_Syntax.v
                                                       with
                                                       | FStar_Syntax_Syntax.Pat_var
                                                           uu___9 ->
                                                           (match rest with
                                                            | uu___10::uu___11
                                                                ->
                                                                fail
                                                                  "Redundant branches after wildcard"
                                                            | uu___10 ->
                                                                return tbr)
                                                       | FStar_Syntax_Syntax.Pat_wild
                                                           uu___9 ->
                                                           (match rest with
                                                            | uu___10::uu___11
                                                                ->
                                                                fail
                                                                  "Redundant branches after wildcard"
                                                            | uu___10 ->
                                                                return tbr)
                                                       | uu___9 ->
                                                           check_branches
                                                             path_condition1
                                                             (FStar_Pervasives_Native.Some
                                                                tbr) rest))))) in
                    let uu___2 =
                      match rc_opt with
                      | FStar_Pervasives_Native.Some
                          { FStar_Syntax_Syntax.residual_effect = uu___3;
                            FStar_Syntax_Syntax.residual_typ =
                              FStar_Pervasives_Native.Some t;
                            FStar_Syntax_Syntax.residual_flags = uu___4;_}
                          ->
                          let uu___5 =
                            with_context "residual type"
                              (FStar_Pervasives_Native.Some t)
                              (fun uu___6 -> universe_of g t) in
                          bind uu___5
                            (fun uu___6 ->
                               return (FStar_Pervasives_Native.Some t))
                      | uu___3 -> return FStar_Pervasives_Native.None in
                    bind uu___2
                      (fun branch_typ_opt ->
                         check_branches FStar_Syntax_Util.t_true
                           branch_typ_opt branches)))
      | FStar_Syntax_Syntax.Tm_match uu___ ->
          fail "Match with returns clause is not handled yet"
      | uu___ ->
          let uu___1 =
            let uu___2 = FStar_Syntax_Print.tag_of_term e1 in
            FStar_Compiler_Util.format1 "Unexpected term: %s" uu___2 in
          fail uu___1
and (check_binders :
  env ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.universe Prims.list
        * env) result)
  =
  fun g ->
    fun xs ->
      match xs with
      | [] -> return ([], [], g)
      | x::xs1 ->
          let uu___ =
            check "binder sort" g
              (x.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort in
          bind uu___
            (fun t ->
               let uu___1 = is_type g t in
               bind uu___1
                 (fun u ->
                    let uu___2 =
                      let g' = push_binders g [x] in
                      let uu___3 = check_binders g' xs1 in
                      bind uu___3
                        (fun xs_g ->
                           let uu___4 = xs_g in
                           match uu___4 with
                           | (xs2, us, g1) ->
                               return ((x :: xs2), (u :: us), g1)) in
                    with_binders [x] [u] uu___2))
and (check_comp :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.universe result) =
  fun g ->
    fun c ->
      let uu___ = FStar_Syntax_Util.is_tot_or_gtot_comp c in
      if uu___
      then
        let uu___1 = check "comp result" g (FStar_Syntax_Util.comp_result c) in
        bind uu___1 (fun t -> is_type g t)
      else fail "Computation type is not Tot or GTot"
and (universe_of :
  env -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.universe result) =
  fun g ->
    fun t ->
      let uu___ = check "universe of" g t in
      bind uu___ (fun t1 -> is_type g t1)
let (check_term_top :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ -> unit result)
  =
  fun g ->
    fun e ->
      fun t ->
        let g1 = { tcenv = g; allow_universe_instantiation = false } in
        let uu___ = check "top" g1 e in
        bind uu___
          (fun te ->
             with_context "top-level subtyping" FStar_Pervasives_Native.None
               (fun uu___1 ->
                  check_subtype
                    { tcenv = (g1.tcenv); allow_universe_instantiation = true
                    } e te t))
let (check_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ ->
        (FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option, error)
          FStar_Pervasives.either)
  =
  fun g ->
    fun e ->
      fun t ->
        let uu___ = let uu___1 = check_term_top g e t in uu___1 [] in
        match uu___ with
        | FStar_Pervasives.Inl (uu___1, g1) -> FStar_Pervasives.Inl g1
        | FStar_Pervasives.Inr err -> FStar_Pervasives.Inr err