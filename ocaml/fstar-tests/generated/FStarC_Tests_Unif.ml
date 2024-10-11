open Prims
let (tcenv : unit -> FStarC_TypeChecker_Env.env) =
  fun uu___ -> FStarC_Tests_Pars.init ()
let (guard_to_string :
  FStarC_TypeChecker_Common.guard_formula -> Prims.string) =
  fun g ->
    match g with
    | FStarC_TypeChecker_Common.Trivial -> "trivial"
    | FStarC_TypeChecker_Common.NonTrivial f ->
        let uu___ = tcenv () in
        FStarC_TypeChecker_Normalize.term_to_string uu___ f
let (success : Prims.bool FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Util.mk_ref true
let (fail : Prims.string -> unit) =
  fun msg ->
    FStarC_Compiler_Util.print_string msg;
    FStarC_Compiler_Effect.op_Colon_Equals success false
let (guard_eq :
  Prims.int ->
    FStarC_TypeChecker_Common.guard_formula ->
      FStarC_TypeChecker_Common.guard_formula -> unit)
  =
  fun i ->
    fun g ->
      fun g' ->
        let uu___ =
          match (g, g') with
          | (FStarC_TypeChecker_Common.Trivial,
             FStarC_TypeChecker_Common.Trivial) -> (true, g, g')
          | (FStarC_TypeChecker_Common.NonTrivial f,
             FStarC_TypeChecker_Common.NonTrivial f') ->
              let f1 =
                let uu___1 = tcenv () in
                FStarC_TypeChecker_Normalize.normalize
                  [FStarC_TypeChecker_Env.EraseUniverses] uu___1 f in
              let f'1 =
                let uu___1 = tcenv () in
                FStarC_TypeChecker_Normalize.normalize
                  [FStarC_TypeChecker_Env.EraseUniverses] uu___1 f' in
              let uu___1 = FStarC_Tests_Util.term_eq f1 f'1 in
              (uu___1, (FStarC_TypeChecker_Common.NonTrivial f1),
                (FStarC_TypeChecker_Common.NonTrivial f'1))
          | uu___1 -> (false, g, g') in
        match uu___ with
        | (b, g1, g'1) ->
            (if Prims.op_Negation b
             then
               (let uu___2 =
                  let uu___3 = FStarC_Compiler_Util.string_of_int i in
                  let uu___4 = guard_to_string g'1 in
                  let uu___5 = guard_to_string g1 in
                  FStarC_Compiler_Util.format3
                    "Test %s failed:\n\tExpected guard %s;\n\tGot guard      %s\n"
                    uu___3 uu___4 uu___5 in
                fail uu___2)
             else ();
             (let uu___2 = (FStarC_Compiler_Effect.op_Bang success) && b in
              FStarC_Compiler_Effect.op_Colon_Equals success uu___2))
let (unify :
  Prims.int ->
    FStarC_Syntax_Syntax.bv Prims.list ->
      FStarC_Syntax_Syntax.typ ->
        FStarC_Syntax_Syntax.typ ->
          FStarC_TypeChecker_Common.guard_formula -> (unit -> unit) -> unit)
  =
  fun i ->
    fun bvs ->
      fun x ->
        fun y ->
          fun g' ->
            fun check ->
              (let uu___1 = FStarC_Compiler_Util.string_of_int i in
               FStarC_Compiler_Util.print1 "%s ..." uu___1);
              (let uu___2 = FStarC_Main.process_args () in ());
              (let uu___3 =
                 FStarC_Class_Show.show FStarC_Syntax_Print.showable_term x in
               let uu___4 =
                 FStarC_Class_Show.show FStarC_Syntax_Print.showable_term y in
               FStarC_Compiler_Util.print2 "Unify %s\nand %s\n" uu___3 uu___4);
              (let tcenv1 = tcenv () in
               let tcenv2 = FStarC_TypeChecker_Env.push_bvs tcenv1 bvs in
               let g =
                 let uu___3 =
                   let uu___4 = FStarC_TypeChecker_Rel.teq tcenv2 x y in
                   FStarC_TypeChecker_Rel.solve_deferred_constraints tcenv2
                     uu___4 in
                 FStarC_TypeChecker_Rel.simplify_guard tcenv2 uu___3 in
               guard_eq i g.FStarC_TypeChecker_Common.guard_f g';
               check ();
               FStarC_Options.init ())
let (should_fail :
  FStarC_Syntax_Syntax.typ -> FStarC_Syntax_Syntax.typ -> unit) =
  fun x ->
    fun y ->
      try
        (fun uu___ ->
           match () with
           | () ->
               let g =
                 let uu___1 = tcenv () in
                 let uu___2 =
                   let uu___3 = tcenv () in
                   FStarC_TypeChecker_Rel.teq uu___3 x y in
                 FStarC_TypeChecker_Rel.solve_deferred_constraints uu___1
                   uu___2 in
               (match g.FStarC_TypeChecker_Common.guard_f with
                | FStarC_TypeChecker_Common.Trivial ->
                    let uu___1 =
                      let uu___2 =
                        FStarC_Class_Show.show
                          FStarC_Syntax_Print.showable_term x in
                      let uu___3 =
                        FStarC_Class_Show.show
                          FStarC_Syntax_Print.showable_term y in
                      FStarC_Compiler_Util.format2
                        "%s and %s should not be unifiable\n" uu___2 uu___3 in
                    fail uu___1
                | FStarC_TypeChecker_Common.NonTrivial f ->
                    let uu___1 =
                      FStarC_Class_Show.show
                        FStarC_Syntax_Print.showable_term x in
                    let uu___2 =
                      FStarC_Class_Show.show
                        FStarC_Syntax_Print.showable_term y in
                    let uu___3 =
                      FStarC_Class_Show.show
                        FStarC_Syntax_Print.showable_term f in
                    FStarC_Compiler_Util.print3
                      "%s and %s are unifiable if %s\n" uu___1 uu___2 uu___3))
          ()
      with
      | FStarC_Errors.Error (e, msg, r, _ctx) ->
          let uu___1 = FStarC_Errors_Msg.rendermsg msg in
          FStarC_Compiler_Util.print1 "%s\n" uu___1
let (unify' : Prims.string -> Prims.string -> unit) =
  fun x ->
    fun y ->
      let x1 = FStarC_Tests_Pars.pars x in
      let y1 = FStarC_Tests_Pars.pars y in
      let g =
        let uu___ = tcenv () in
        let uu___1 =
          let uu___2 = tcenv () in FStarC_TypeChecker_Rel.teq uu___2 x1 y1 in
        FStarC_TypeChecker_Rel.solve_deferred_constraints uu___ uu___1 in
      let uu___ = FStarC_Class_Show.show FStarC_Syntax_Print.showable_term x1 in
      let uu___1 =
        FStarC_Class_Show.show FStarC_Syntax_Print.showable_term y1 in
      let uu___2 = guard_to_string g.FStarC_TypeChecker_Common.guard_f in
      FStarC_Compiler_Util.print3 "%s and %s are unifiable with guard %s\n"
        uu___ uu___1 uu___2
let (norm : FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term) =
  fun t ->
    let uu___ = tcenv () in FStarC_TypeChecker_Normalize.normalize [] uu___ t
let (check_core :
  Prims.int ->
    Prims.bool ->
      Prims.bool ->
        FStarC_Syntax_Syntax.typ -> FStarC_Syntax_Syntax.typ -> unit)
  =
  fun i ->
    fun subtyping ->
      fun guard_ok ->
        fun x ->
          fun y ->
            (let uu___1 = FStarC_Main.process_args () in ());
            (let env = tcenv () in
             let res =
               if subtyping
               then
                 FStarC_TypeChecker_Core.check_term_subtyping true true env x
                   y
               else
                 FStarC_TypeChecker_Core.check_term_equality true true env x
                   y in
             (match res with
              | FStar_Pervasives.Inl (FStar_Pervasives_Native.None) ->
                  let uu___2 = FStarC_Compiler_Util.string_of_int i in
                  FStarC_Compiler_Util.print1 "%s core check ok\n" uu___2
              | FStar_Pervasives.Inl (FStar_Pervasives_Native.Some g) ->
                  ((let uu___3 = FStarC_Compiler_Util.string_of_int i in
                    let uu___4 =
                      FStarC_Class_Show.show
                        FStarC_Syntax_Print.showable_term g in
                    FStarC_Compiler_Util.print2
                      "%s core check computed guard %s ok\n" uu___3 uu___4);
                   if Prims.op_Negation guard_ok
                   then FStarC_Compiler_Effect.op_Colon_Equals success false
                   else ())
              | FStar_Pervasives.Inr err ->
                  (FStarC_Compiler_Effect.op_Colon_Equals success false;
                   (let uu___3 = FStarC_Compiler_Util.string_of_int i in
                    let uu___4 = FStarC_TypeChecker_Core.print_error err in
                    FStarC_Compiler_Util.print2 "%s failed\n%s\n" uu___3
                      uu___4)));
             FStarC_Options.init ())
let (check_core_typing :
  Prims.int -> FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.typ -> unit)
  =
  fun i ->
    fun e ->
      fun t ->
        (let uu___1 = FStarC_Main.process_args () in ());
        (let env = tcenv () in
         (let uu___2 = FStarC_TypeChecker_Core.check_term env e t true in
          match uu___2 with
          | FStar_Pervasives.Inl (FStar_Pervasives_Native.None) ->
              let uu___3 = FStarC_Compiler_Util.string_of_int i in
              FStarC_Compiler_Util.print1 "%s core typing ok\n" uu___3
          | FStar_Pervasives.Inl (FStar_Pervasives_Native.Some g) ->
              ((let uu___4 = FStarC_Compiler_Util.string_of_int i in
                FStarC_Compiler_Util.print1
                  "%s core typing produced a guard\n" uu___4);
               FStarC_Compiler_Effect.op_Colon_Equals success false)
          | FStar_Pervasives.Inr err ->
              (FStarC_Compiler_Effect.op_Colon_Equals success false;
               (let uu___4 = FStarC_Compiler_Util.string_of_int i in
                let uu___5 = FStarC_TypeChecker_Core.print_error err in
                FStarC_Compiler_Util.print2 "%s failed\n%s\n" uu___4 uu___5)));
         FStarC_Options.init ())
let (inst :
  Prims.int ->
    FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax ->
      (FStarC_Syntax_Syntax.term * FStarC_Syntax_Syntax.term Prims.list))
  =
  fun n ->
    fun tm ->
      let rec aux out n1 =
        if n1 = Prims.int_zero
        then out
        else
          (let uu___1 =
             let uu___2 = FStarC_Tests_Pars.init () in
             FStarC_TypeChecker_Util.new_implicit_var ""
               FStarC_Compiler_Range_Type.dummyRange uu___2
               FStarC_Syntax_Util.ktype0 false in
           match uu___1 with
           | (t, uu___2, uu___3) ->
               let uu___4 =
                 let uu___5 = FStarC_Tests_Pars.init () in
                 FStarC_TypeChecker_Util.new_implicit_var ""
                   FStarC_Compiler_Range_Type.dummyRange uu___5 t false in
               (match uu___4 with
                | (u, uu___5, uu___6) -> aux (u :: out) (n1 - Prims.int_one))) in
      let us = aux [] n in
      let uu___ = let uu___1 = FStarC_Tests_Util.app tm us in norm uu___1 in
      (uu___, us)
let (run_all : unit -> Prims.bool) =
  fun uu___ ->
    FStarC_Compiler_Util.print_string "Testing the unifier\n";
    FStarC_Options.__set_unit_tests ();
    (let unify_check n bvs x y g f = unify n bvs x y g f in
     let unify1 n bvs x y g = unify n bvs x y g (fun uu___3 -> ()) in
     let int_t = FStarC_Tests_Pars.tc "Prims.int" in
     let x_bv =
       FStarC_Syntax_Syntax.gen_bv "x" FStar_Pervasives_Native.None int_t in
     let y_bv =
       FStarC_Syntax_Syntax.gen_bv "y" FStar_Pervasives_Native.None int_t in
     let x = FStarC_Syntax_Syntax.bv_to_name x_bv in
     let y = FStarC_Syntax_Syntax.bv_to_name y_bv in
     unify1 Prims.int_zero [x_bv] x x FStarC_TypeChecker_Common.Trivial;
     (let uu___5 =
        let uu___6 =
          FStarC_Syntax_Util.mk_eq2 FStarC_Syntax_Syntax.U_zero
            FStarC_Syntax_Util.t_bool x y in
        FStarC_TypeChecker_Common.NonTrivial uu___6 in
      unify1 Prims.int_one [x_bv; y_bv] x y uu___5);
     (let id = FStarC_Tests_Pars.tc "fun (x:bool) -> x" in
      (let uu___6 = FStarC_Tests_Util.app id [x] in
       unify1 (Prims.of_int (2)) [x_bv] x uu___6
         FStarC_TypeChecker_Common.Trivial);
      (let id1 = FStarC_Tests_Pars.tc "fun (x:bool) -> x" in
       unify1 (Prims.of_int (3)) [] id1 id1 FStarC_TypeChecker_Common.Trivial;
       (let id2 = FStarC_Tests_Pars.tc "fun (x:bool) -> x" in
        let id' = FStarC_Tests_Pars.tc "fun (y:bool) -> y" in
        unify1 (Prims.of_int (4)) [] id2 id'
          FStarC_TypeChecker_Common.Trivial;
        (let uu___9 = FStarC_Tests_Pars.tc "fun (x y:bool) -> x" in
         let uu___10 = FStarC_Tests_Pars.tc "fun (a b:bool) -> a" in
         unify1 (Prims.of_int (5)) [] uu___9 uu___10
           FStarC_TypeChecker_Common.Trivial);
        (let uu___10 = FStarC_Tests_Pars.tc "fun (x y z:bool) -> y" in
         let uu___11 = FStarC_Tests_Pars.tc "fun (a b c:bool) -> b" in
         unify1 (Prims.of_int (6)) [] uu___10 uu___11
           FStarC_TypeChecker_Common.Trivial);
        (let uu___11 = FStarC_Tests_Pars.tc "fun (x:int) (y:int) -> y" in
         let uu___12 = FStarC_Tests_Pars.tc "fun (x:int) (y:int) -> x" in
         let uu___13 =
           let uu___14 =
             FStarC_Tests_Pars.tc "(forall (x:int). (forall (y:int). y==x))" in
           FStarC_TypeChecker_Common.NonTrivial uu___14 in
         unify1 (Prims.of_int (7)) [] uu___11 uu___12 uu___13);
        (let uu___12 =
           FStarC_Tests_Pars.tc "fun (x:int) (y:int) (z:int) -> y" in
         let uu___13 =
           FStarC_Tests_Pars.tc "fun (x:int) (y:int) (z:int) -> z" in
         let uu___14 =
           let uu___15 =
             FStarC_Tests_Pars.tc
               "(forall (x:int). (forall (y:int). (forall (z:int). y==z)))" in
           FStarC_TypeChecker_Common.NonTrivial uu___15 in
         unify1 (Prims.of_int (8)) [] uu___12 uu___13 uu___14);
        (let uu___13 = FStarC_Main.process_args () in ());
        (let uu___13 =
           let uu___14 =
             FStarC_Tests_Pars.tc "fun (u:Type0 -> Type0) (x:Type0) -> u x" in
           inst Prims.int_one uu___14 in
         match uu___13 with
         | (tm, us) ->
             let sol = FStarC_Tests_Pars.tc "fun (x:Type0) -> Prims.pair x x" in
             (unify_check (Prims.of_int (9)) [] tm sol
                FStarC_TypeChecker_Common.Trivial
                (fun uu___15 ->
                   let uu___16 =
                     let uu___17 =
                       let uu___18 = FStarC_Compiler_List.hd us in
                       norm uu___18 in
                     let uu___18 = norm sol in
                     FStarC_Tests_Util.term_eq uu___17 uu___18 in
                   FStarC_Tests_Util.always (Prims.of_int (9)) uu___16);
              (let uu___15 =
                 let uu___16 =
                   FStarC_Tests_Pars.tc
                     "fun (u: int -> int -> int) (x:int) -> u x" in
                 inst Prims.int_one uu___16 in
               match uu___15 with
               | (tm1, us1) ->
                   let sol1 = FStarC_Tests_Pars.tc "fun (x y:int) -> x + y" in
                   (unify_check (Prims.of_int (10)) [] tm1 sol1
                      FStarC_TypeChecker_Common.Trivial
                      (fun uu___17 ->
                         let uu___18 =
                           let uu___19 =
                             let uu___20 = FStarC_Compiler_List.hd us1 in
                             norm uu___20 in
                           let uu___20 = norm sol1 in
                           FStarC_Tests_Util.term_eq uu___19 uu___20 in
                         FStarC_Tests_Util.always (Prims.of_int (10)) uu___18);
                    (let tm11 =
                       FStarC_Tests_Pars.tc "x:int -> y:int{eq2 y x} -> bool" in
                     let tm2 = FStarC_Tests_Pars.tc "x:int -> y:int -> bool" in
                     (let uu___18 =
                        let uu___19 =
                          FStarC_Tests_Pars.tc
                            "forall (x:int). (forall (y:int). y==x)" in
                        FStarC_TypeChecker_Common.NonTrivial uu___19 in
                      unify1 (Prims.of_int (11)) [] tm11 tm2 uu___18);
                     (let tm12 =
                        FStarC_Tests_Pars.tc
                          "a:Type0 -> b:(a -> Type0) -> x:a -> y:b x -> Tot Type0" in
                      let tm21 =
                        FStarC_Tests_Pars.tc
                          "a:Type0 -> b:(a -> Type0) -> x:a -> y:b x -> Tot Type0" in
                      unify1 (Prims.of_int (12)) [] tm12 tm21
                        FStarC_TypeChecker_Common.Trivial;
                      (let uu___19 =
                         let int_typ = FStarC_Tests_Pars.tc "int" in
                         let x1 =
                           FStarC_Syntax_Syntax.new_bv
                             FStar_Pervasives_Native.None int_typ in
                         let typ = FStarC_Tests_Pars.tc "unit -> Type0" in
                         let l =
                           FStarC_Tests_Pars.tc
                             "fun (q:(unit -> Type0)) -> q ()" in
                         let q =
                           FStarC_Syntax_Syntax.new_bv
                             FStar_Pervasives_Native.None typ in
                         let tm13 =
                           let uu___20 =
                             let uu___21 =
                               let uu___22 =
                                 FStarC_Syntax_Syntax.bv_to_name q in
                               [uu___22] in
                             FStarC_Tests_Util.app l uu___21 in
                           norm uu___20 in
                         let l1 =
                           FStarC_Tests_Pars.tc "fun (p:unit -> Type0) -> p" in
                         let unit = FStarC_Tests_Pars.tc "()" in
                         let env =
                           let uu___20 = FStarC_Tests_Pars.init () in
                           let uu___21 =
                             let uu___22 = FStarC_Syntax_Syntax.mk_binder x1 in
                             let uu___23 =
                               let uu___24 = FStarC_Syntax_Syntax.mk_binder q in
                               [uu___24] in
                             uu___22 :: uu___23 in
                           FStarC_TypeChecker_Env.push_binders uu___20
                             uu___21 in
                         let uu___20 =
                           FStarC_TypeChecker_Util.new_implicit_var ""
                             FStarC_Compiler_Range_Type.dummyRange env typ
                             false in
                         match uu___20 with
                         | (u_p, uu___21, uu___22) ->
                             let tm22 =
                               let uu___23 =
                                 let uu___24 = FStarC_Tests_Util.app l1 [u_p] in
                                 norm uu___24 in
                               FStarC_Tests_Util.app uu___23 [unit] in
                             (tm13, tm22, [x1; q]) in
                       match uu___19 with
                       | (tm13, tm22, bvs_13) ->
                           (unify1 (Prims.of_int (13)) bvs_13 tm13 tm22
                              FStarC_TypeChecker_Common.Trivial;
                            (let uu___21 =
                               let int_typ = FStarC_Tests_Pars.tc "int" in
                               let x1 =
                                 FStarC_Syntax_Syntax.new_bv
                                   FStar_Pervasives_Native.None int_typ in
                               let typ =
                                 FStarC_Tests_Pars.tc "pure_post unit" in
                               let l =
                                 FStarC_Tests_Pars.tc
                                   "fun (q:pure_post unit) -> q ()" in
                               let q =
                                 FStarC_Syntax_Syntax.new_bv
                                   FStar_Pervasives_Native.None typ in
                               let tm14 =
                                 let uu___22 =
                                   let uu___23 =
                                     let uu___24 =
                                       FStarC_Syntax_Syntax.bv_to_name q in
                                     [uu___24] in
                                   FStarC_Tests_Util.app l uu___23 in
                                 norm uu___22 in
                               let l1 =
                                 FStarC_Tests_Pars.tc
                                   "fun (p:pure_post unit) -> p" in
                               let unit = FStarC_Tests_Pars.tc "()" in
                               let env =
                                 let uu___22 = FStarC_Tests_Pars.init () in
                                 let uu___23 =
                                   let uu___24 =
                                     FStarC_Syntax_Syntax.mk_binder x1 in
                                   let uu___25 =
                                     let uu___26 =
                                       FStarC_Syntax_Syntax.mk_binder q in
                                     [uu___26] in
                                   uu___24 :: uu___25 in
                                 FStarC_TypeChecker_Env.push_binders uu___22
                                   uu___23 in
                               let uu___22 =
                                 FStarC_TypeChecker_Util.new_implicit_var ""
                                   FStarC_Compiler_Range_Type.dummyRange env
                                   typ false in
                               match uu___22 with
                               | (u_p, uu___23, uu___24) ->
                                   let tm23 =
                                     let uu___25 =
                                       let uu___26 =
                                         FStarC_Tests_Util.app l1 [u_p] in
                                       norm uu___26 in
                                     FStarC_Tests_Util.app uu___25 [unit] in
                                   (tm14, tm23, [x1; q]) in
                             match uu___21 with
                             | (tm14, tm23, bvs_14) ->
                                 (unify1 (Prims.of_int (14)) bvs_14 tm14 tm23
                                    FStarC_TypeChecker_Common.Trivial;
                                  (let uu___23 =
                                     FStarC_Tests_Pars.pars_and_tc_fragment
                                       "let ty0 n = x:int { x >= n }\nlet ty1 n = x:ty0 n { x > n }\nassume val tc (t:Type0) : Type0";
                                     (let t0 = FStarC_Tests_Pars.tc "ty1 17" in
                                      let t1 =
                                        FStarC_Tests_Pars.tc
                                          "x:ty0 17 { x > 17 }" in
                                      (t0, t1)) in
                                   match uu___23 with
                                   | (tm15, tm24) ->
                                       (check_core (Prims.of_int (15)) false
                                          false tm15 tm24;
                                        (let uu___25 =
                                           let t0 =
                                             FStarC_Tests_Pars.tc
                                               "x:int { x >= 17 /\\ x > 17 }" in
                                           let t1 =
                                             FStarC_Tests_Pars.tc
                                               "x:ty0 17 { x > 17 }" in
                                           (t0, t1) in
                                         match uu___25 with
                                         | (tm16, tm25) ->
                                             (check_core (Prims.of_int (16))
                                                false false tm16 tm25;
                                              (let uu___27 =
                                                 FStarC_Tests_Pars.pars_and_tc_fragment
                                                   "let defn17_0 (x:nat) : nat -> nat -> Type0 = fun y z -> a:int { a + x == y + z }";
                                                 (let t0 =
                                                    FStarC_Tests_Pars.tc
                                                      "defn17_0 0 1 2" in
                                                  let t1_head =
                                                    FStarC_Tests_Pars.tc
                                                      "(defn17_0 0)" in
                                                  let arg1 =
                                                    FStarC_Tests_Pars.tc "1" in
                                                  let arg2 =
                                                    FStarC_Tests_Pars.tc "2" in
                                                  let t1 =
                                                    FStarC_Syntax_Syntax.mk_Tm_app
                                                      t1_head
                                                      [(arg1,
                                                         FStar_Pervasives_Native.None);
                                                      (arg2,
                                                        FStar_Pervasives_Native.None)]
                                                      t0.FStarC_Syntax_Syntax.pos in
                                                  (t0, t1)) in
                                               match uu___27 with
                                               | (tm17, tm26) ->
                                                   (check_core
                                                      (Prims.of_int (17))
                                                      false false tm17 tm26;
                                                    (let uu___29 =
                                                       let t0 =
                                                         FStarC_Tests_Pars.tc
                                                           "dp:((dtuple2 int (fun (y:int) -> z:int{ z > y })) <: Type0) { let (| x, _ |) = dp in x > 17 }" in
                                                       let t1 =
                                                         FStarC_Tests_Pars.tc
                                                           "(dtuple2 int (fun (y:int) -> z:int{ z > y }))" in
                                                       (t0, t1) in
                                                     match uu___29 with
                                                     | (tm18, tm27) ->
                                                         (check_core
                                                            (Prims.of_int (18))
                                                            true false tm18
                                                            tm27;
                                                          (let uu___31 =
                                                             FStarC_Tests_Pars.pars_and_tc_fragment
                                                               "type vprop' = { t:Type0 ; n:nat }";
                                                             (let t0 =
                                                                FStarC_Tests_Pars.tc
                                                                  "x:(({ t=bool; n=0 }).t <: Type0) { x == false }" in
                                                              let t1 =
                                                                FStarC_Tests_Pars.tc
                                                                  "x:bool{ x == false }" in
                                                              (t0, t1)) in
                                                           match uu___31 with
                                                           | (tm19, tm28) ->
                                                               (check_core
                                                                  (Prims.of_int (19))
                                                                  false false
                                                                  tm19 tm28;
                                                                (let uu___33
                                                                   =
                                                                   let t0 =
                                                                    FStarC_Tests_Pars.tc
                                                                    "int" in
                                                                   let t1 =
                                                                    FStarC_Tests_Pars.tc
                                                                    "j:(i:nat{ i > 17 } <: Type0){j > 42}" in
                                                                   (t0, t1) in
                                                                 match uu___33
                                                                 with
                                                                 | (tm110,
                                                                    tm29) ->
                                                                    (check_core
                                                                    (Prims.of_int (20))
                                                                    true true
                                                                    tm110
                                                                    tm29;
                                                                    (let uu___35
                                                                    =
                                                                    FStarC_Tests_Pars.pars_and_tc_fragment
                                                                    "assume val tstr21 (x:string) : Type0";
                                                                    (
                                                                    let t0 =
                                                                    FStarC_Tests_Pars.tc
                                                                    "(fun (x:bool) (y:int) (z: (fun (x:string) -> tstr21 x) \"hello\") -> x)" in
                                                                    let ty =
                                                                    FStarC_Tests_Pars.tc
                                                                    "bool -> int -> tstr21 \"hello\" -> bool" in
                                                                    (t0, ty)) in
                                                                    match uu___35
                                                                    with
                                                                    | 
                                                                    (tm3, ty)
                                                                    ->
                                                                    (check_core_typing
                                                                    (Prims.of_int (21))
                                                                    tm3 ty;
                                                                    FStarC_Options.__clear_unit_tests
                                                                    ();
                                                                    (let uu___39
                                                                    =
                                                                    FStarC_Compiler_Effect.op_Bang
                                                                    success in
                                                                    if
                                                                    uu___39
                                                                    then
                                                                    FStarC_Compiler_Util.print_string
                                                                    "Unifier ok\n"
                                                                    else ());
                                                                    FStarC_Compiler_Effect.op_Bang
                                                                    success))))))))))))))))))))))))))))