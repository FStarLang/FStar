open Prims
let (tcenv : unit -> FStar_TypeChecker_Env.env) =
  fun uu____4  -> FStar_Tests_Pars.init () 
let (guard_to_string :
  FStar_TypeChecker_Common.guard_formula -> Prims.string) =
  fun g  ->
    match g with
    | FStar_TypeChecker_Common.Trivial  -> "trivial"
    | FStar_TypeChecker_Common.NonTrivial f ->
        let uu____15 = tcenv ()  in
        FStar_TypeChecker_Normalize.term_to_string uu____15 f
  
let (success : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref true 
let (fail : Prims.string -> unit) =
  fun msg  ->
    FStar_Util.print_string msg; FStar_ST.op_Colon_Equals success false
  
let (guard_eq :
  Prims.int ->
    FStar_TypeChecker_Common.guard_formula ->
      FStar_TypeChecker_Common.guard_formula -> unit)
  =
  fun i  ->
    fun g  ->
      fun g'  ->
        let uu____71 =
          match (g, g') with
          | (FStar_TypeChecker_Common.Trivial
             ,FStar_TypeChecker_Common.Trivial ) -> (true, g, g')
          | (FStar_TypeChecker_Common.NonTrivial
             f,FStar_TypeChecker_Common.NonTrivial f') ->
              let f1 =
                let uu____91 = tcenv ()  in
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Env.EraseUniverses] uu____91 f
                 in
              let f'1 =
                let uu____93 = tcenv ()  in
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Env.EraseUniverses] uu____93 f'
                 in
              let uu____94 = FStar_Tests_Util.term_eq f1 f'1  in
              (uu____94, (FStar_TypeChecker_Common.NonTrivial f1),
                (FStar_TypeChecker_Common.NonTrivial f'1))
          | uu____97 -> (false, g, g')  in
        match uu____71 with
        | (b,g1,g'1) ->
            (if Prims.op_Negation b
             then
               (let uu____111 =
                  let uu____113 = FStar_Util.string_of_int i  in
                  let uu____115 = guard_to_string g'1  in
                  let uu____117 = guard_to_string g1  in
                  FStar_Util.format3
                    "Test %s failed:\n\tExpected guard %s;\n\tGot guard      %s\n"
                    uu____113 uu____115 uu____117
                   in
                FStar_All.pipe_left fail uu____111)
             else ();
             (let uu____123 = (FStar_ST.op_Bang success) && b  in
              FStar_ST.op_Colon_Equals success uu____123))
  
let (unify :
  Prims.int ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_TypeChecker_Common.guard_formula -> (unit -> unit) -> unit)
  =
  fun i  ->
    fun x1  ->
      fun y1  ->
        fun g'  ->
          fun check1  ->
            (let uu____209 = FStar_Util.string_of_int i  in
             FStar_Util.print1 "%s ..." uu____209);
            (let uu____213 = FStar_Main.process_args ()  in
             FStar_All.pipe_right uu____213 (fun uu____228  -> ()));
            (let uu____230 = FStar_Syntax_Print.term_to_string x1  in
             let uu____232 = FStar_Syntax_Print.term_to_string y1  in
             FStar_Util.print2 "Unify %s\nand %s\n" uu____230 uu____232);
            (let g =
               let uu____236 =
                 let uu____237 =
                   let uu____238 = tcenv ()  in
                   FStar_TypeChecker_Rel.teq uu____238 x1 y1  in
                 let uu____239 =
                   let uu____244 = tcenv ()  in
                   FStar_TypeChecker_Rel.solve_deferred_constraints uu____244
                    in
                 FStar_All.pipe_right uu____237 uu____239  in
               let uu____245 =
                 let uu____250 = tcenv ()  in
                 FStar_TypeChecker_Rel.simplify_guard uu____250  in
               FStar_All.pipe_right uu____236 uu____245  in
             guard_eq i g.FStar_TypeChecker_Common.guard_f g';
             check1 ();
             FStar_Options.init ())
  
let (should_fail :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> unit)
  =
  fun x1  ->
    fun y1  ->
      try
        (fun uu___41_275  ->
           match () with
           | () ->
               let g =
                 let uu____277 =
                   let uu____278 = tcenv ()  in
                   FStar_TypeChecker_Rel.teq uu____278 x1 y1  in
                 let uu____279 =
                   let uu____284 = tcenv ()  in
                   FStar_TypeChecker_Rel.solve_deferred_constraints uu____284
                    in
                 FStar_All.pipe_right uu____277 uu____279  in
               (match g.FStar_TypeChecker_Common.guard_f with
                | FStar_TypeChecker_Common.Trivial  ->
                    let uu____285 =
                      let uu____287 = FStar_Syntax_Print.term_to_string x1
                         in
                      let uu____289 = FStar_Syntax_Print.term_to_string y1
                         in
                      FStar_Util.format2
                        "%s and %s should not be unifiable\n" uu____287
                        uu____289
                       in
                    fail uu____285
                | FStar_TypeChecker_Common.NonTrivial f ->
                    let uu____293 = FStar_Syntax_Print.term_to_string x1  in
                    let uu____295 = FStar_Syntax_Print.term_to_string y1  in
                    let uu____297 = FStar_Syntax_Print.term_to_string f  in
                    FStar_Util.print3 "%s and %s are unifiable if %s\n"
                      uu____293 uu____295 uu____297)) ()
      with | FStar_Errors.Error (e,msg,r) -> FStar_Util.print1 "%s\n" msg
  
let (unify' : Prims.string -> Prims.string -> unit) =
  fun x1  ->
    fun y1  ->
      let x2 = FStar_Tests_Pars.pars x1  in
      let y2 = FStar_Tests_Pars.pars y1  in
      let g =
        let uu____329 =
          let uu____330 = tcenv ()  in
          FStar_TypeChecker_Rel.teq uu____330 x2 y2  in
        let uu____331 =
          let uu____336 = tcenv ()  in
          FStar_TypeChecker_Rel.solve_deferred_constraints uu____336  in
        FStar_All.pipe_right uu____329 uu____331  in
      let uu____337 = FStar_Syntax_Print.term_to_string x2  in
      let uu____339 = FStar_Syntax_Print.term_to_string y2  in
      let uu____341 = guard_to_string g.FStar_TypeChecker_Common.guard_f  in
      FStar_Util.print3 "%s and %s are unifiable with guard %s\n" uu____337
        uu____339 uu____341
  
let (norm : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____350 = tcenv ()  in
    FStar_TypeChecker_Normalize.normalize [] uu____350 t
  
let (inst :
  Prims.int ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term Prims.list))
  =
  fun n1  ->
    fun tm1  ->
      let rec aux out n2 =
        if n2 = Prims.int_zero
        then out
        else
          (let uu____400 =
             let uu____413 = FStar_Tests_Pars.init ()  in
             FStar_TypeChecker_Util.new_implicit_var ""
               FStar_Range.dummyRange uu____413 FStar_Syntax_Util.ktype0
              in
           match uu____400 with
           | (t,uu____418,uu____419) ->
               let uu____432 =
                 let uu____445 = FStar_Tests_Pars.init ()  in
                 FStar_TypeChecker_Util.new_implicit_var ""
                   FStar_Range.dummyRange uu____445 t
                  in
               (match uu____432 with
                | (u,uu____450,uu____451) ->
                    aux (u :: out) (n2 - Prims.int_one)))
         in
      let us = aux [] n1  in
      let uu____468 =
        let uu____469 = FStar_Tests_Util.app tm1 us  in norm uu____469  in
      (uu____468, us)
  
let (run_all : unit -> Prims.bool) =
  fun uu____478  ->
    FStar_Util.print_string "Testing the unifier\n";
    FStar_Options.__set_unit_tests ();
    (let unify_check n1 x1 y1 g f = unify n1 x1 y1 g f  in
     let unify1 n1 x1 y1 g = unify n1 x1 y1 g (fun uu____555  -> ())  in
     let int_t = FStar_Tests_Pars.tc "Prims.int"  in
     let x1 =
       let uu____561 =
         FStar_Syntax_Syntax.gen_bv "x" FStar_Pervasives_Native.None int_t
          in
       FStar_All.pipe_right uu____561 FStar_Syntax_Syntax.bv_to_name  in
     let y1 =
       let uu____568 =
         FStar_Syntax_Syntax.gen_bv "y" FStar_Pervasives_Native.None int_t
          in
       FStar_All.pipe_right uu____568 FStar_Syntax_Syntax.bv_to_name  in
     unify1 Prims.int_zero x1 x1 FStar_TypeChecker_Common.Trivial;
     (let uu____575 =
        let uu____576 =
          FStar_Syntax_Util.mk_eq2 FStar_Syntax_Syntax.U_zero
            FStar_Syntax_Util.t_bool x1 y1
           in
        FStar_TypeChecker_Common.NonTrivial uu____576  in
      unify1 Prims.int_one x1 y1 uu____575);
     (let id1 = FStar_Tests_Pars.tc "fun x -> x"  in
      (let uu____581 = FStar_Tests_Util.app id1 [x1]  in
       unify1 (Prims.of_int (2)) x1 uu____581
         FStar_TypeChecker_Common.Trivial);
      (let id2 = FStar_Tests_Pars.tc "fun x -> x"  in
       unify1 (Prims.of_int (3)) id2 id2 FStar_TypeChecker_Common.Trivial;
       (let id3 = FStar_Tests_Pars.tc "fun x -> x"  in
        let id' = FStar_Tests_Pars.tc "fun y -> y"  in
        unify1 (Prims.of_int (4)) id3 id' FStar_TypeChecker_Common.Trivial;
        (let uu____596 = FStar_Tests_Pars.tc "fun x y -> x"  in
         let uu____600 = FStar_Tests_Pars.tc "fun a b -> a"  in
         unify1 (Prims.of_int (5)) uu____596 uu____600
           FStar_TypeChecker_Common.Trivial);
        (let uu____606 = FStar_Tests_Pars.tc "fun x y z -> y"  in
         let uu____610 = FStar_Tests_Pars.tc "fun a b c -> b"  in
         unify1 (Prims.of_int (6)) uu____606 uu____610
           FStar_TypeChecker_Common.Trivial);
        (let uu____616 = FStar_Tests_Pars.tc "fun (x:int) (y:int) -> y"  in
         let uu____620 = FStar_Tests_Pars.tc "fun (x:int) (y:int) -> x"  in
         let uu____624 =
           let uu____625 =
             FStar_Tests_Pars.tc "(forall (x:int). (forall (y:int). y==x))"
              in
           FStar_TypeChecker_Common.NonTrivial uu____625  in
         unify1 (Prims.of_int (7)) uu____616 uu____620 uu____624);
        (let uu____629 =
           FStar_Tests_Pars.tc "fun (x:int) (y:int) (z:int) -> y"  in
         let uu____633 =
           FStar_Tests_Pars.tc "fun (x:int) (y:int) (z:int) -> z"  in
         let uu____637 =
           let uu____638 =
             FStar_Tests_Pars.tc
               "(forall (x:int). (forall (y:int). (forall (z:int). y==z)))"
              in
           FStar_TypeChecker_Common.NonTrivial uu____638  in
         unify1 (Prims.of_int (8)) uu____629 uu____633 uu____637);
        (let uu____642 = FStar_Main.process_args ()  in
         FStar_All.pipe_right uu____642 (fun uu____657  -> ()));
        (let uu____658 =
           let uu____665 = FStar_Tests_Pars.tc "fun u x -> u x"  in
           inst Prims.int_one uu____665  in
         match uu____658 with
         | (tm1,us) ->
             let sol = FStar_Tests_Pars.tc "fun x -> c_and x x"  in
             (unify_check (Prims.of_int (9)) tm1 sol
                FStar_TypeChecker_Common.Trivial
                (fun uu____683  ->
                   let uu____684 =
                     let uu____686 =
                       let uu____689 = FStar_List.hd us  in norm uu____689
                        in
                     let uu____690 = norm sol  in
                     FStar_Tests_Util.term_eq uu____686 uu____690  in
                   FStar_Tests_Util.always (Prims.of_int (9)) uu____684);
              (let uu____694 =
                 let uu____701 = FStar_Tests_Pars.tc "fun u x -> u x"  in
                 inst Prims.int_one uu____701  in
               match uu____694 with
               | (tm2,us1) ->
                   let sol1 = FStar_Tests_Pars.tc "fun x y -> x + y"  in
                   (unify_check (Prims.of_int (10)) tm2 sol1
                      FStar_TypeChecker_Common.Trivial
                      (fun uu____719  ->
                         let uu____720 =
                           let uu____722 =
                             let uu____725 = FStar_List.hd us1  in
                             norm uu____725  in
                           let uu____726 = norm sol1  in
                           FStar_Tests_Util.term_eq uu____722 uu____726  in
                         FStar_Tests_Util.always (Prims.of_int (10))
                           uu____720);
                    (let tm11 =
                       FStar_Tests_Pars.tc "x:int -> y:int{eq2 y x} -> bool"
                        in
                     let tm21 = FStar_Tests_Pars.tc "x:int -> y:int -> bool"
                        in
                     (let uu____735 =
                        let uu____736 =
                          FStar_Tests_Pars.tc
                            "forall (x:int). (forall (y:int). y==x)"
                           in
                        FStar_TypeChecker_Common.NonTrivial uu____736  in
                      unify1 (Prims.of_int (11)) tm11 tm21 uu____735);
                     (let tm12 =
                        FStar_Tests_Pars.tc
                          "a:Type0 -> b:(a -> Type0) -> x:a -> y:b x -> Tot Type0"
                         in
                      let tm22 =
                        FStar_Tests_Pars.tc
                          "a:Type0 -> b:(a -> Type0) -> x:a -> y:b x -> Tot Type0"
                         in
                      unify1 (Prims.of_int (12)) tm12 tm22
                        FStar_TypeChecker_Common.Trivial;
                      (let uu____745 =
                         let int_typ = FStar_Tests_Pars.tc "int"  in
                         let x2 =
                           FStar_Syntax_Syntax.new_bv
                             FStar_Pervasives_Native.None int_typ
                            in
                         let typ = FStar_Tests_Pars.tc "unit -> Type0"  in
                         let l =
                           FStar_Tests_Pars.tc
                             "fun (q:(unit -> Type0)) -> q ()"
                            in
                         let q =
                           FStar_Syntax_Syntax.new_bv
                             FStar_Pervasives_Native.None typ
                            in
                         let tm13 =
                           let uu____763 =
                             let uu____764 =
                               let uu____767 =
                                 FStar_Syntax_Syntax.bv_to_name q  in
                               [uu____767]  in
                             FStar_Tests_Util.app l uu____764  in
                           norm uu____763  in
                         let l1 =
                           FStar_Tests_Pars.tc "fun (p:unit -> Type0) -> p"
                            in
                         let unit = FStar_Tests_Pars.tc "()"  in
                         let env =
                           let uu____773 = FStar_Tests_Pars.init ()  in
                           let uu____774 =
                             let uu____775 = FStar_Syntax_Syntax.mk_binder x2
                                in
                             let uu____782 =
                               let uu____791 =
                                 FStar_Syntax_Syntax.mk_binder q  in
                               [uu____791]  in
                             uu____775 :: uu____782  in
                           FStar_TypeChecker_Env.push_binders uu____773
                             uu____774
                            in
                         let uu____816 =
                           FStar_TypeChecker_Util.new_implicit_var ""
                             FStar_Range.dummyRange env typ
                            in
                         match uu____816 with
                         | (u_p,uu____839,uu____840) ->
                             let tm23 =
                               let uu____856 =
                                 let uu____859 =
                                   FStar_Tests_Util.app l1 [u_p]  in
                                 norm uu____859  in
                               FStar_Tests_Util.app uu____856 [unit]  in
                             (tm13, tm23)
                          in
                       match uu____745 with
                       | (tm13,tm23) ->
                           (unify1 (Prims.of_int (13)) tm13 tm23
                              FStar_TypeChecker_Common.Trivial;
                            (let uu____877 =
                               let int_typ = FStar_Tests_Pars.tc "int"  in
                               let x2 =
                                 FStar_Syntax_Syntax.new_bv
                                   FStar_Pervasives_Native.None int_typ
                                  in
                               let typ = FStar_Tests_Pars.tc "pure_post unit"
                                  in
                               let l =
                                 FStar_Tests_Pars.tc
                                   "fun (q:pure_post unit) -> q ()"
                                  in
                               let q =
                                 FStar_Syntax_Syntax.new_bv
                                   FStar_Pervasives_Native.None typ
                                  in
                               let tm14 =
                                 let uu____895 =
                                   let uu____896 =
                                     let uu____899 =
                                       FStar_Syntax_Syntax.bv_to_name q  in
                                     [uu____899]  in
                                   FStar_Tests_Util.app l uu____896  in
                                 norm uu____895  in
                               let l1 =
                                 FStar_Tests_Pars.tc
                                   "fun (p:pure_post unit) -> p"
                                  in
                               let unit = FStar_Tests_Pars.tc "()"  in
                               let env =
                                 let uu____905 = FStar_Tests_Pars.init ()  in
                                 let uu____906 =
                                   let uu____907 =
                                     FStar_Syntax_Syntax.mk_binder x2  in
                                   let uu____914 =
                                     let uu____923 =
                                       FStar_Syntax_Syntax.mk_binder q  in
                                     [uu____923]  in
                                   uu____907 :: uu____914  in
                                 FStar_TypeChecker_Env.push_binders uu____905
                                   uu____906
                                  in
                               let uu____948 =
                                 FStar_TypeChecker_Util.new_implicit_var ""
                                   FStar_Range.dummyRange env typ
                                  in
                               match uu____948 with
                               | (u_p,uu____971,uu____972) ->
                                   let tm24 =
                                     let uu____988 =
                                       let uu____991 =
                                         FStar_Tests_Util.app l1 [u_p]  in
                                       norm uu____991  in
                                     FStar_Tests_Util.app uu____988 [unit]
                                      in
                                   (tm14, tm24)
                                in
                             match uu____877 with
                             | (tm14,tm24) ->
                                 (unify1 (Prims.of_int (14)) tm14 tm24
                                    FStar_TypeChecker_Common.Trivial;
                                  FStar_Options.__clear_unit_tests ();
                                  (let uu____1011 = FStar_ST.op_Bang success
                                      in
                                   if uu____1011
                                   then
                                     FStar_Util.print_string "Unifier ok\n"
                                   else ());
                                  FStar_ST.op_Bang success))))))))))))))
  