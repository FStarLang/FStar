open Prims
let (tcenv : unit -> FStar_TypeChecker_Env.env) =
  fun uu____79805  -> FStar_Tests_Pars.init () 
let (guard_to_string :
  FStar_TypeChecker_Common.guard_formula -> Prims.string) =
  fun g  ->
    match g with
    | FStar_TypeChecker_Common.Trivial  -> "trivial"
    | FStar_TypeChecker_Common.NonTrivial f ->
        let uu____79816 = tcenv ()  in
        FStar_TypeChecker_Normalize.term_to_string uu____79816 f
  
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
        let uu____79872 =
          match (g, g') with
          | (FStar_TypeChecker_Common.Trivial
             ,FStar_TypeChecker_Common.Trivial ) -> (true, g, g')
          | (FStar_TypeChecker_Common.NonTrivial
             f,FStar_TypeChecker_Common.NonTrivial f') ->
              let f1 =
                let uu____79892 = tcenv ()  in
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Env.EraseUniverses] uu____79892 f
                 in
              let f'1 =
                let uu____79894 = tcenv ()  in
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Env.EraseUniverses] uu____79894 f'
                 in
              let uu____79895 = FStar_Tests_Util.term_eq f1 f'1  in
              (uu____79895, (FStar_TypeChecker_Common.NonTrivial f1),
                (FStar_TypeChecker_Common.NonTrivial f'1))
          | uu____79898 -> (false, g, g')  in
        match uu____79872 with
        | (b,g1,g'1) ->
            (if Prims.op_Negation b
             then
               (let uu____79912 =
                  let uu____79914 = FStar_Util.string_of_int i  in
                  let uu____79916 = guard_to_string g'1  in
                  let uu____79918 = guard_to_string g1  in
                  FStar_Util.format3
                    "Test %s failed:\n\tExpected guard %s;\n\tGot guard      %s\n"
                    uu____79914 uu____79916 uu____79918
                   in
                FStar_All.pipe_left fail uu____79912)
             else ();
             (let uu____79924 = (FStar_ST.op_Bang success) && b  in
              FStar_ST.op_Colon_Equals success uu____79924))
  
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
            (let uu____80010 = FStar_Util.string_of_int i  in
             FStar_Util.print1 "%s ..." uu____80010);
            (let uu____80014 = FStar_Main.process_args ()  in
             FStar_All.pipe_right uu____80014 (fun a1  -> ()));
            (let uu____80030 = FStar_Syntax_Print.term_to_string x1  in
             let uu____80032 = FStar_Syntax_Print.term_to_string y1  in
             FStar_Util.print2 "Unify %s\nand %s\n" uu____80030 uu____80032);
            (let g =
               let uu____80036 =
                 let uu____80037 =
                   let uu____80038 = tcenv ()  in
                   FStar_TypeChecker_Rel.teq uu____80038 x1 y1  in
                 let uu____80039 =
                   let uu____80044 = tcenv ()  in
                   FStar_TypeChecker_Rel.solve_deferred_constraints
                     uu____80044
                    in
                 FStar_All.pipe_right uu____80037 uu____80039  in
               let uu____80045 =
                 let uu____80050 = tcenv ()  in
                 FStar_TypeChecker_Rel.simplify_guard uu____80050  in
               FStar_All.pipe_right uu____80036 uu____80045  in
             guard_eq i g.FStar_TypeChecker_Env.guard_f g';
             check1 ();
             FStar_Options.init ())
  
let (should_fail :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> unit)
  =
  fun x1  ->
    fun y1  ->
      try
        (fun uu___783_80075  ->
           match () with
           | () ->
               let g =
                 let uu____80077 =
                   let uu____80078 = tcenv ()  in
                   FStar_TypeChecker_Rel.teq uu____80078 x1 y1  in
                 let uu____80079 =
                   let uu____80084 = tcenv ()  in
                   FStar_TypeChecker_Rel.solve_deferred_constraints
                     uu____80084
                    in
                 FStar_All.pipe_right uu____80077 uu____80079  in
               (match g.FStar_TypeChecker_Env.guard_f with
                | FStar_TypeChecker_Common.Trivial  ->
                    let uu____80085 =
                      let uu____80087 = FStar_Syntax_Print.term_to_string x1
                         in
                      let uu____80089 = FStar_Syntax_Print.term_to_string y1
                         in
                      FStar_Util.format2
                        "%s and %s should not be unifiable\n" uu____80087
                        uu____80089
                       in
                    fail uu____80085
                | FStar_TypeChecker_Common.NonTrivial f ->
                    let uu____80093 = FStar_Syntax_Print.term_to_string x1
                       in
                    let uu____80095 = FStar_Syntax_Print.term_to_string y1
                       in
                    let uu____80097 = FStar_Syntax_Print.term_to_string f  in
                    FStar_Util.print3 "%s and %s are unifiable if %s\n"
                      uu____80093 uu____80095 uu____80097)) ()
      with | FStar_Errors.Error (e,msg,r) -> FStar_Util.print1 "%s\n" msg
  
let (unify' : Prims.string -> Prims.string -> unit) =
  fun x1  ->
    fun y1  ->
      let x2 = FStar_Tests_Pars.pars x1  in
      let y2 = FStar_Tests_Pars.pars y1  in
      let g =
        let uu____80129 =
          let uu____80130 = tcenv ()  in
          FStar_TypeChecker_Rel.teq uu____80130 x2 y2  in
        let uu____80131 =
          let uu____80136 = tcenv ()  in
          FStar_TypeChecker_Rel.solve_deferred_constraints uu____80136  in
        FStar_All.pipe_right uu____80129 uu____80131  in
      let uu____80137 = FStar_Syntax_Print.term_to_string x2  in
      let uu____80139 = FStar_Syntax_Print.term_to_string y2  in
      let uu____80141 = guard_to_string g.FStar_TypeChecker_Env.guard_f  in
      FStar_Util.print3 "%s and %s are unifiable with guard %s\n" uu____80137
        uu____80139 uu____80141
  
let (norm : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____80150 = tcenv ()  in
    FStar_TypeChecker_Normalize.normalize [] uu____80150 t
  
let (inst :
  Prims.int ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term Prims.list))
  =
  fun n1  ->
    fun tm1  ->
      let rec aux out n2 =
        if n2 = (Prims.parse_int "0")
        then out
        else
          (let uu____80200 =
             let uu____80213 = FStar_Tests_Pars.init ()  in
             FStar_TypeChecker_Util.new_implicit_var ""
               FStar_Range.dummyRange uu____80213 FStar_Syntax_Util.ktype0
              in
           match uu____80200 with
           | (t,uu____80218,uu____80219) ->
               let uu____80232 =
                 let uu____80245 = FStar_Tests_Pars.init ()  in
                 FStar_TypeChecker_Util.new_implicit_var ""
                   FStar_Range.dummyRange uu____80245 t
                  in
               (match uu____80232 with
                | (u,uu____80250,uu____80251) ->
                    aux (u :: out) (n2 - (Prims.parse_int "1"))))
         in
      let us = aux [] n1  in
      let uu____80268 =
        let uu____80269 = FStar_Tests_Util.app tm1 us  in norm uu____80269
         in
      (uu____80268, us)
  
let (run_all : unit -> Prims.bool) =
  fun uu____80278  ->
    FStar_Util.print_string "Testing the unifier\n";
    FStar_Options.__set_unit_tests ();
    (let unify_check n1 x1 y1 g f = unify n1 x1 y1 g f  in
     let unify1 n1 x1 y1 g = unify n1 x1 y1 g (fun uu____80355  -> ())  in
     let int_t = FStar_Tests_Pars.tc "Prims.int"  in
     let x1 =
       let uu____80361 =
         FStar_Syntax_Syntax.gen_bv "x" FStar_Pervasives_Native.None int_t
          in
       FStar_All.pipe_right uu____80361 FStar_Syntax_Syntax.bv_to_name  in
     let y1 =
       let uu____80368 =
         FStar_Syntax_Syntax.gen_bv "y" FStar_Pervasives_Native.None int_t
          in
       FStar_All.pipe_right uu____80368 FStar_Syntax_Syntax.bv_to_name  in
     unify1 (Prims.parse_int "0") x1 x1 FStar_TypeChecker_Common.Trivial;
     (let uu____80375 =
        let uu____80376 =
          FStar_Syntax_Util.mk_eq2 FStar_Syntax_Syntax.U_zero
            FStar_Syntax_Util.t_bool x1 y1
           in
        FStar_TypeChecker_Common.NonTrivial uu____80376  in
      unify1 (Prims.parse_int "1") x1 y1 uu____80375);
     (let id1 = FStar_Tests_Pars.tc "fun x -> x"  in
      (let uu____80381 = FStar_Tests_Util.app id1 [x1]  in
       unify1 (Prims.parse_int "2") x1 uu____80381
         FStar_TypeChecker_Common.Trivial);
      (let id2 = FStar_Tests_Pars.tc "fun x -> x"  in
       unify1 (Prims.parse_int "3") id2 id2 FStar_TypeChecker_Common.Trivial;
       (let id3 = FStar_Tests_Pars.tc "fun x -> x"  in
        let id' = FStar_Tests_Pars.tc "fun y -> y"  in
        unify1 (Prims.parse_int "4") id3 id' FStar_TypeChecker_Common.Trivial;
        (let uu____80396 = FStar_Tests_Pars.tc "fun x y -> x"  in
         let uu____80400 = FStar_Tests_Pars.tc "fun a b -> a"  in
         unify1 (Prims.parse_int "5") uu____80396 uu____80400
           FStar_TypeChecker_Common.Trivial);
        (let uu____80406 = FStar_Tests_Pars.tc "fun x y z -> y"  in
         let uu____80410 = FStar_Tests_Pars.tc "fun a b c -> b"  in
         unify1 (Prims.parse_int "6") uu____80406 uu____80410
           FStar_TypeChecker_Common.Trivial);
        (let uu____80416 = FStar_Tests_Pars.tc "fun (x:int) (y:int) -> y"  in
         let uu____80420 = FStar_Tests_Pars.tc "fun (x:int) (y:int) -> x"  in
         let uu____80424 =
           let uu____80425 =
             FStar_Tests_Pars.tc "(forall (x:int). (forall (y:int). y==x))"
              in
           FStar_TypeChecker_Common.NonTrivial uu____80425  in
         unify1 (Prims.parse_int "7") uu____80416 uu____80420 uu____80424);
        (let uu____80429 =
           FStar_Tests_Pars.tc "fun (x:int) (y:int) (z:int) -> y"  in
         let uu____80433 =
           FStar_Tests_Pars.tc "fun (x:int) (y:int) (z:int) -> z"  in
         let uu____80437 =
           let uu____80438 =
             FStar_Tests_Pars.tc
               "(forall (x:int). (forall (y:int). (forall (z:int). y==z)))"
              in
           FStar_TypeChecker_Common.NonTrivial uu____80438  in
         unify1 (Prims.parse_int "8") uu____80429 uu____80433 uu____80437);
        (let uu____80442 = FStar_Main.process_args ()  in
         FStar_All.pipe_right uu____80442 (fun a2  -> ()));
        (let uu____80457 =
           let uu____80464 = FStar_Tests_Pars.tc "fun u x -> u x"  in
           inst (Prims.parse_int "1") uu____80464  in
         match uu____80457 with
         | (tm1,us) ->
             let sol = FStar_Tests_Pars.tc "fun x -> c_and x x"  in
             (unify_check (Prims.parse_int "9") tm1 sol
                FStar_TypeChecker_Common.Trivial
                (fun uu____80482  ->
                   let uu____80483 =
                     let uu____80485 =
                       let uu____80488 = FStar_List.hd us  in
                       norm uu____80488  in
                     let uu____80489 = norm sol  in
                     FStar_Tests_Util.term_eq uu____80485 uu____80489  in
                   FStar_Tests_Util.always (Prims.parse_int "9") uu____80483);
              (let uu____80493 =
                 let uu____80500 = FStar_Tests_Pars.tc "fun u x -> u x"  in
                 inst (Prims.parse_int "1") uu____80500  in
               match uu____80493 with
               | (tm2,us1) ->
                   let sol1 = FStar_Tests_Pars.tc "fun x y -> x + y"  in
                   (unify_check (Prims.parse_int "10") tm2 sol1
                      FStar_TypeChecker_Common.Trivial
                      (fun uu____80518  ->
                         let uu____80519 =
                           let uu____80521 =
                             let uu____80524 = FStar_List.hd us1  in
                             norm uu____80524  in
                           let uu____80525 = norm sol1  in
                           FStar_Tests_Util.term_eq uu____80521 uu____80525
                            in
                         FStar_Tests_Util.always (Prims.parse_int "10")
                           uu____80519);
                    (let tm11 =
                       FStar_Tests_Pars.tc "x:int -> y:int{eq2 y x} -> bool"
                        in
                     let tm21 = FStar_Tests_Pars.tc "x:int -> y:int -> bool"
                        in
                     (let uu____80534 =
                        let uu____80535 =
                          FStar_Tests_Pars.tc
                            "forall (x:int). (forall (y:int). y==x)"
                           in
                        FStar_TypeChecker_Common.NonTrivial uu____80535  in
                      unify1 (Prims.parse_int "11") tm11 tm21 uu____80534);
                     (let tm12 =
                        FStar_Tests_Pars.tc
                          "a:Type0 -> b:(a -> Type0) -> x:a -> y:b x -> Tot Type0"
                         in
                      let tm22 =
                        FStar_Tests_Pars.tc
                          "a:Type0 -> b:(a -> Type0) -> x:a -> y:b x -> Tot Type0"
                         in
                      unify1 (Prims.parse_int "12") tm12 tm22
                        FStar_TypeChecker_Common.Trivial;
                      (let uu____80544 =
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
                           let uu____80562 =
                             let uu____80563 =
                               let uu____80566 =
                                 FStar_Syntax_Syntax.bv_to_name q  in
                               [uu____80566]  in
                             FStar_Tests_Util.app l uu____80563  in
                           norm uu____80562  in
                         let l1 =
                           FStar_Tests_Pars.tc "fun (p:unit -> Type0) -> p"
                            in
                         let unit = FStar_Tests_Pars.tc "()"  in
                         let env =
                           let uu____80572 = FStar_Tests_Pars.init ()  in
                           let uu____80573 =
                             let uu____80574 =
                               FStar_Syntax_Syntax.mk_binder x2  in
                             let uu____80581 =
                               let uu____80590 =
                                 FStar_Syntax_Syntax.mk_binder q  in
                               [uu____80590]  in
                             uu____80574 :: uu____80581  in
                           FStar_TypeChecker_Env.push_binders uu____80572
                             uu____80573
                            in
                         let uu____80615 =
                           FStar_TypeChecker_Util.new_implicit_var ""
                             FStar_Range.dummyRange env typ
                            in
                         match uu____80615 with
                         | (u_p,uu____80638,uu____80639) ->
                             let tm23 =
                               let uu____80655 =
                                 let uu____80658 =
                                   FStar_Tests_Util.app l1 [u_p]  in
                                 norm uu____80658  in
                               FStar_Tests_Util.app uu____80655 [unit]  in
                             (tm13, tm23)
                          in
                       match uu____80544 with
                       | (tm13,tm23) ->
                           (unify1 (Prims.parse_int "13") tm13 tm23
                              FStar_TypeChecker_Common.Trivial;
                            (let uu____80676 =
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
                                 let uu____80694 =
                                   let uu____80695 =
                                     let uu____80698 =
                                       FStar_Syntax_Syntax.bv_to_name q  in
                                     [uu____80698]  in
                                   FStar_Tests_Util.app l uu____80695  in
                                 norm uu____80694  in
                               let l1 =
                                 FStar_Tests_Pars.tc
                                   "fun (p:pure_post unit) -> p"
                                  in
                               let unit = FStar_Tests_Pars.tc "()"  in
                               let env =
                                 let uu____80704 = FStar_Tests_Pars.init ()
                                    in
                                 let uu____80705 =
                                   let uu____80706 =
                                     FStar_Syntax_Syntax.mk_binder x2  in
                                   let uu____80713 =
                                     let uu____80722 =
                                       FStar_Syntax_Syntax.mk_binder q  in
                                     [uu____80722]  in
                                   uu____80706 :: uu____80713  in
                                 FStar_TypeChecker_Env.push_binders
                                   uu____80704 uu____80705
                                  in
                               let uu____80747 =
                                 FStar_TypeChecker_Util.new_implicit_var ""
                                   FStar_Range.dummyRange env typ
                                  in
                               match uu____80747 with
                               | (u_p,uu____80770,uu____80771) ->
                                   let tm24 =
                                     let uu____80787 =
                                       let uu____80790 =
                                         FStar_Tests_Util.app l1 [u_p]  in
                                       norm uu____80790  in
                                     FStar_Tests_Util.app uu____80787 [unit]
                                      in
                                   (tm14, tm24)
                                in
                             match uu____80676 with
                             | (tm14,tm24) ->
                                 (unify1 (Prims.parse_int "14") tm14 tm24
                                    FStar_TypeChecker_Common.Trivial;
                                  FStar_Options.__clear_unit_tests ();
                                  (let uu____80810 = FStar_ST.op_Bang success
                                      in
                                   if uu____80810
                                   then
                                     FStar_Util.print_string "Unifier ok\n"
                                   else ());
                                  FStar_ST.op_Bang success))))))))))))))
  