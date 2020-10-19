open Prims
let (tcenv : unit -> FStar_TypeChecker_Env.env) =
  fun uu___ -> FStar_Tests_Pars.init ()
let (guard_to_string :
  FStar_TypeChecker_Common.guard_formula -> Prims.string) =
  fun g ->
    match g with
    | FStar_TypeChecker_Common.Trivial -> "trivial"
    | FStar_TypeChecker_Common.NonTrivial f ->
        let uu___ = tcenv () in
        FStar_TypeChecker_Normalize.term_to_string uu___ f
let (success : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref true
let (fail : Prims.string -> unit) =
  fun msg ->
    FStar_Util.print_string msg; FStar_ST.op_Colon_Equals success false
let (guard_eq :
  Prims.int ->
    FStar_TypeChecker_Common.guard_formula ->
      FStar_TypeChecker_Common.guard_formula -> unit)
  =
  fun i ->
    fun g ->
      fun g' ->
        let uu___ =
          match (g, g') with
          | (FStar_TypeChecker_Common.Trivial,
             FStar_TypeChecker_Common.Trivial) -> (true, g, g')
          | (FStar_TypeChecker_Common.NonTrivial f,
             FStar_TypeChecker_Common.NonTrivial f') ->
              let f1 =
                let uu___1 = tcenv () in
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Env.EraseUniverses] uu___1 f in
              let f'1 =
                let uu___1 = tcenv () in
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Env.EraseUniverses] uu___1 f' in
              let uu___1 = FStar_Tests_Util.term_eq f1 f'1 in
              (uu___1, (FStar_TypeChecker_Common.NonTrivial f1),
                (FStar_TypeChecker_Common.NonTrivial f'1))
          | uu___1 -> (false, g, g') in
        match uu___ with
        | (b, g1, g'1) ->
            (if Prims.op_Negation b
             then
               (let uu___2 =
                  let uu___3 = FStar_Util.string_of_int i in
                  let uu___4 = guard_to_string g'1 in
                  let uu___5 = guard_to_string g1 in
                  FStar_Util.format3
                    "Test %s failed:\n\tExpected guard %s;\n\tGot guard      %s\n"
                    uu___3 uu___4 uu___5 in
                FStar_All.pipe_left fail uu___2)
             else ();
             (let uu___2 = (FStar_ST.op_Bang success) && b in
              FStar_ST.op_Colon_Equals success uu___2))
let (unify :
  Prims.int ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_TypeChecker_Common.guard_formula -> (unit -> unit) -> unit)
  =
  fun i ->
    fun x ->
      fun y ->
        fun g' ->
          fun check ->
            (let uu___1 = FStar_Util.string_of_int i in
             FStar_Util.print1 "%s ..." uu___1);
            (let uu___2 = FStar_Main.process_args () in
             FStar_All.pipe_right uu___2 (fun uu___3 -> ()));
            (let uu___3 = FStar_Syntax_Print.term_to_string x in
             let uu___4 = FStar_Syntax_Print.term_to_string y in
             FStar_Util.print2 "Unify %s\nand %s\n" uu___3 uu___4);
            (let g =
               let uu___3 =
                 let uu___4 =
                   let uu___5 = tcenv () in
                   FStar_TypeChecker_Rel.teq uu___5 x y in
                 let uu___5 =
                   let uu___6 = tcenv () in
                   FStar_TypeChecker_Rel.solve_deferred_constraints uu___6 in
                 FStar_All.pipe_right uu___4 uu___5 in
               let uu___4 =
                 let uu___5 = tcenv () in
                 FStar_TypeChecker_Rel.simplify_guard uu___5 in
               FStar_All.pipe_right uu___3 uu___4 in
             guard_eq i g.FStar_TypeChecker_Common.guard_f g';
             check ();
             FStar_Options.init ())
let (should_fail :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> unit)
  =
  fun x ->
    fun y ->
      try
        (fun uu___ ->
           match () with
           | () ->
               let g =
                 let uu___1 =
                   let uu___2 = tcenv () in
                   FStar_TypeChecker_Rel.teq uu___2 x y in
                 let uu___2 =
                   let uu___3 = tcenv () in
                   FStar_TypeChecker_Rel.solve_deferred_constraints uu___3 in
                 FStar_All.pipe_right uu___1 uu___2 in
               (match g.FStar_TypeChecker_Common.guard_f with
                | FStar_TypeChecker_Common.Trivial ->
                    let uu___1 =
                      let uu___2 = FStar_Syntax_Print.term_to_string x in
                      let uu___3 = FStar_Syntax_Print.term_to_string y in
                      FStar_Util.format2
                        "%s and %s should not be unifiable\n" uu___2 uu___3 in
                    fail uu___1
                | FStar_TypeChecker_Common.NonTrivial f ->
                    let uu___1 = FStar_Syntax_Print.term_to_string x in
                    let uu___2 = FStar_Syntax_Print.term_to_string y in
                    let uu___3 = FStar_Syntax_Print.term_to_string f in
                    FStar_Util.print3 "%s and %s are unifiable if %s\n"
                      uu___1 uu___2 uu___3)) ()
      with
      | FStar_Errors.Error (e, msg, r, _ctx) -> FStar_Util.print1 "%s\n" msg
let (unify' : Prims.string -> Prims.string -> unit) =
  fun x ->
    fun y ->
      let x1 = FStar_Tests_Pars.pars x in
      let y1 = FStar_Tests_Pars.pars y in
      let g =
        let uu___ =
          let uu___1 = tcenv () in FStar_TypeChecker_Rel.teq uu___1 x1 y1 in
        let uu___1 =
          let uu___2 = tcenv () in
          FStar_TypeChecker_Rel.solve_deferred_constraints uu___2 in
        FStar_All.pipe_right uu___ uu___1 in
      let uu___ = FStar_Syntax_Print.term_to_string x1 in
      let uu___1 = FStar_Syntax_Print.term_to_string y1 in
      let uu___2 = guard_to_string g.FStar_TypeChecker_Common.guard_f in
      FStar_Util.print3 "%s and %s are unifiable with guard %s\n" uu___
        uu___1 uu___2
let (norm : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t ->
    let uu___ = tcenv () in FStar_TypeChecker_Normalize.normalize [] uu___ t
let (inst :
  Prims.int ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term Prims.list))
  =
  fun n ->
    fun tm ->
      let rec aux out n1 =
        if n1 = Prims.int_zero
        then out
        else
          (let uu___1 =
             let uu___2 = FStar_Tests_Pars.init () in
             FStar_TypeChecker_Util.new_implicit_var ""
               FStar_Range.dummyRange uu___2 FStar_Syntax_Util.ktype0 in
           match uu___1 with
           | (t, uu___2, uu___3) ->
               let uu___4 =
                 let uu___5 = FStar_Tests_Pars.init () in
                 FStar_TypeChecker_Util.new_implicit_var ""
                   FStar_Range.dummyRange uu___5 t in
               (match uu___4 with
                | (u, uu___5, uu___6) -> aux (u :: out) (n1 - Prims.int_one))) in
      let us = aux [] n in
      let uu___ = let uu___1 = FStar_Tests_Util.app tm us in norm uu___1 in
      (uu___, us)
let (run_all : unit -> Prims.bool) =
  fun uu___ ->
    FStar_Util.print_string "Testing the unifier\n";
    FStar_Options.__set_unit_tests ();
    (let unify_check n x y g f = unify n x y g f in
     let unify1 n x y g = unify n x y g (fun uu___3 -> ()) in
     let int_t = FStar_Tests_Pars.tc "Prims.int" in
     let x =
       let uu___3 =
         FStar_Syntax_Syntax.gen_bv "x" FStar_Pervasives_Native.None int_t in
       FStar_All.pipe_right uu___3 FStar_Syntax_Syntax.bv_to_name in
     let y =
       let uu___3 =
         FStar_Syntax_Syntax.gen_bv "y" FStar_Pervasives_Native.None int_t in
       FStar_All.pipe_right uu___3 FStar_Syntax_Syntax.bv_to_name in
     unify1 Prims.int_zero x x FStar_TypeChecker_Common.Trivial;
     (let uu___5 =
        let uu___6 =
          FStar_Syntax_Util.mk_eq2 FStar_Syntax_Syntax.U_zero
            FStar_Syntax_Util.t_bool x y in
        FStar_TypeChecker_Common.NonTrivial uu___6 in
      unify1 Prims.int_one x y uu___5);
     (let id = FStar_Tests_Pars.tc "fun x -> x" in
      (let uu___6 = FStar_Tests_Util.app id [x] in
       unify1 (Prims.of_int (2)) x uu___6 FStar_TypeChecker_Common.Trivial);
      (let id1 = FStar_Tests_Pars.tc "fun x -> x" in
       unify1 (Prims.of_int (3)) id1 id1 FStar_TypeChecker_Common.Trivial;
       (let id2 = FStar_Tests_Pars.tc "fun x -> x" in
        let id' = FStar_Tests_Pars.tc "fun y -> y" in
        unify1 (Prims.of_int (4)) id2 id' FStar_TypeChecker_Common.Trivial;
        (let uu___9 = FStar_Tests_Pars.tc "fun x y -> x" in
         let uu___10 = FStar_Tests_Pars.tc "fun a b -> a" in
         unify1 (Prims.of_int (5)) uu___9 uu___10
           FStar_TypeChecker_Common.Trivial);
        (let uu___10 = FStar_Tests_Pars.tc "fun x y z -> y" in
         let uu___11 = FStar_Tests_Pars.tc "fun a b c -> b" in
         unify1 (Prims.of_int (6)) uu___10 uu___11
           FStar_TypeChecker_Common.Trivial);
        (let uu___11 = FStar_Tests_Pars.tc "fun (x:int) (y:int) -> y" in
         let uu___12 = FStar_Tests_Pars.tc "fun (x:int) (y:int) -> x" in
         let uu___13 =
           let uu___14 =
             FStar_Tests_Pars.tc "(forall (x:int). (forall (y:int). y==x))" in
           FStar_TypeChecker_Common.NonTrivial uu___14 in
         unify1 (Prims.of_int (7)) uu___11 uu___12 uu___13);
        (let uu___12 = FStar_Tests_Pars.tc "fun (x:int) (y:int) (z:int) -> y" in
         let uu___13 = FStar_Tests_Pars.tc "fun (x:int) (y:int) (z:int) -> z" in
         let uu___14 =
           let uu___15 =
             FStar_Tests_Pars.tc
               "(forall (x:int). (forall (y:int). (forall (z:int). y==z)))" in
           FStar_TypeChecker_Common.NonTrivial uu___15 in
         unify1 (Prims.of_int (8)) uu___12 uu___13 uu___14);
        (let uu___13 = FStar_Main.process_args () in
         FStar_All.pipe_right uu___13 (fun uu___14 -> ()));
        (let uu___13 =
           let uu___14 = FStar_Tests_Pars.tc "fun u x -> u x" in
           inst Prims.int_one uu___14 in
         match uu___13 with
         | (tm, us) ->
             let sol = FStar_Tests_Pars.tc "fun x -> c_and x x" in
             (unify_check (Prims.of_int (9)) tm sol
                FStar_TypeChecker_Common.Trivial
                (fun uu___15 ->
                   let uu___16 =
                     let uu___17 =
                       let uu___18 = FStar_List.hd us in norm uu___18 in
                     let uu___18 = norm sol in
                     FStar_Tests_Util.term_eq uu___17 uu___18 in
                   FStar_Tests_Util.always (Prims.of_int (9)) uu___16);
              (let uu___15 =
                 let uu___16 = FStar_Tests_Pars.tc "fun u x -> u x" in
                 inst Prims.int_one uu___16 in
               match uu___15 with
               | (tm1, us1) ->
                   let sol1 = FStar_Tests_Pars.tc "fun x y -> x + y" in
                   (unify_check (Prims.of_int (10)) tm1 sol1
                      FStar_TypeChecker_Common.Trivial
                      (fun uu___17 ->
                         let uu___18 =
                           let uu___19 =
                             let uu___20 = FStar_List.hd us1 in norm uu___20 in
                           let uu___20 = norm sol1 in
                           FStar_Tests_Util.term_eq uu___19 uu___20 in
                         FStar_Tests_Util.always (Prims.of_int (10)) uu___18);
                    (let tm11 =
                       FStar_Tests_Pars.tc "x:int -> y:int{eq2 y x} -> bool" in
                     let tm2 = FStar_Tests_Pars.tc "x:int -> y:int -> bool" in
                     (let uu___18 =
                        let uu___19 =
                          FStar_Tests_Pars.tc
                            "forall (x:int). (forall (y:int). y==x)" in
                        FStar_TypeChecker_Common.NonTrivial uu___19 in
                      unify1 (Prims.of_int (11)) tm11 tm2 uu___18);
                     (let tm12 =
                        FStar_Tests_Pars.tc
                          "a:Type0 -> b:(a -> Type0) -> x:a -> y:b x -> Tot Type0" in
                      let tm21 =
                        FStar_Tests_Pars.tc
                          "a:Type0 -> b:(a -> Type0) -> x:a -> y:b x -> Tot Type0" in
                      unify1 (Prims.of_int (12)) tm12 tm21
                        FStar_TypeChecker_Common.Trivial;
                      (let uu___19 =
                         let int_typ = FStar_Tests_Pars.tc "int" in
                         let x1 =
                           FStar_Syntax_Syntax.new_bv
                             FStar_Pervasives_Native.None int_typ in
                         let typ = FStar_Tests_Pars.tc "unit -> Type0" in
                         let l =
                           FStar_Tests_Pars.tc
                             "fun (q:(unit -> Type0)) -> q ()" in
                         let q =
                           FStar_Syntax_Syntax.new_bv
                             FStar_Pervasives_Native.None typ in
                         let tm13 =
                           let uu___20 =
                             let uu___21 =
                               let uu___22 = FStar_Syntax_Syntax.bv_to_name q in
                               [uu___22] in
                             FStar_Tests_Util.app l uu___21 in
                           norm uu___20 in
                         let l1 =
                           FStar_Tests_Pars.tc "fun (p:unit -> Type0) -> p" in
                         let unit = FStar_Tests_Pars.tc "()" in
                         let env =
                           let uu___20 = FStar_Tests_Pars.init () in
                           let uu___21 =
                             let uu___22 = FStar_Syntax_Syntax.mk_binder x1 in
                             let uu___23 =
                               let uu___24 = FStar_Syntax_Syntax.mk_binder q in
                               [uu___24] in
                             uu___22 :: uu___23 in
                           FStar_TypeChecker_Env.push_binders uu___20 uu___21 in
                         let uu___20 =
                           FStar_TypeChecker_Util.new_implicit_var ""
                             FStar_Range.dummyRange env typ in
                         match uu___20 with
                         | (u_p, uu___21, uu___22) ->
                             let tm22 =
                               let uu___23 =
                                 let uu___24 = FStar_Tests_Util.app l1 [u_p] in
                                 norm uu___24 in
                               FStar_Tests_Util.app uu___23 [unit] in
                             (tm13, tm22) in
                       match uu___19 with
                       | (tm13, tm22) ->
                           (unify1 (Prims.of_int (13)) tm13 tm22
                              FStar_TypeChecker_Common.Trivial;
                            (let uu___21 =
                               let int_typ = FStar_Tests_Pars.tc "int" in
                               let x1 =
                                 FStar_Syntax_Syntax.new_bv
                                   FStar_Pervasives_Native.None int_typ in
                               let typ = FStar_Tests_Pars.tc "pure_post unit" in
                               let l =
                                 FStar_Tests_Pars.tc
                                   "fun (q:pure_post unit) -> q ()" in
                               let q =
                                 FStar_Syntax_Syntax.new_bv
                                   FStar_Pervasives_Native.None typ in
                               let tm14 =
                                 let uu___22 =
                                   let uu___23 =
                                     let uu___24 =
                                       FStar_Syntax_Syntax.bv_to_name q in
                                     [uu___24] in
                                   FStar_Tests_Util.app l uu___23 in
                                 norm uu___22 in
                               let l1 =
                                 FStar_Tests_Pars.tc
                                   "fun (p:pure_post unit) -> p" in
                               let unit = FStar_Tests_Pars.tc "()" in
                               let env =
                                 let uu___22 = FStar_Tests_Pars.init () in
                                 let uu___23 =
                                   let uu___24 =
                                     FStar_Syntax_Syntax.mk_binder x1 in
                                   let uu___25 =
                                     let uu___26 =
                                       FStar_Syntax_Syntax.mk_binder q in
                                     [uu___26] in
                                   uu___24 :: uu___25 in
                                 FStar_TypeChecker_Env.push_binders uu___22
                                   uu___23 in
                               let uu___22 =
                                 FStar_TypeChecker_Util.new_implicit_var ""
                                   FStar_Range.dummyRange env typ in
                               match uu___22 with
                               | (u_p, uu___23, uu___24) ->
                                   let tm23 =
                                     let uu___25 =
                                       let uu___26 =
                                         FStar_Tests_Util.app l1 [u_p] in
                                       norm uu___26 in
                                     FStar_Tests_Util.app uu___25 [unit] in
                                   (tm14, tm23) in
                             match uu___21 with
                             | (tm14, tm23) ->
                                 (unify1 (Prims.of_int (14)) tm14 tm23
                                    FStar_TypeChecker_Common.Trivial;
                                  FStar_Options.__clear_unit_tests ();
                                  (let uu___25 = FStar_ST.op_Bang success in
                                   if uu___25
                                   then
                                     FStar_Util.print_string "Unifier ok\n"
                                   else ());
                                  FStar_ST.op_Bang success))))))))))))))