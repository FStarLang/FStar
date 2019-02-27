open Prims
let (tcenv : unit -> FStar_TypeChecker_Env.env) =
  fun uu____84130  -> FStar_Tests_Pars.init () 
let (guard_to_string :
  FStar_TypeChecker_Common.guard_formula -> Prims.string) =
  fun g  ->
    match g with
    | FStar_TypeChecker_Common.Trivial  -> "trivial"
    | FStar_TypeChecker_Common.NonTrivial f ->
        let uu____84141 = tcenv ()  in
        FStar_TypeChecker_Normalize.term_to_string uu____84141 f
  
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
        let uu____84208 =
          match (g, g') with
          | (FStar_TypeChecker_Common.Trivial
             ,FStar_TypeChecker_Common.Trivial ) -> (true, g, g')
          | (FStar_TypeChecker_Common.NonTrivial
             f,FStar_TypeChecker_Common.NonTrivial f') ->
              let f1 =
                let uu____84228 = tcenv ()  in
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Env.EraseUniverses] uu____84228 f
                 in
              let f'1 =
                let uu____84230 = tcenv ()  in
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Env.EraseUniverses] uu____84230 f'
                 in
              let uu____84231 = FStar_Tests_Util.term_eq f1 f'1  in
              (uu____84231, (FStar_TypeChecker_Common.NonTrivial f1),
                (FStar_TypeChecker_Common.NonTrivial f'1))
          | uu____84234 -> (false, g, g')  in
        match uu____84208 with
        | (b,g1,g'1) ->
            (if Prims.op_Negation b
             then
               (let uu____84248 =
                  let uu____84250 = FStar_Util.string_of_int i  in
                  let uu____84252 = guard_to_string g'1  in
                  let uu____84254 = guard_to_string g1  in
                  FStar_Util.format3
                    "Test %s failed:\n\tExpected guard %s;\n\tGot guard      %s\n"
                    uu____84250 uu____84252 uu____84254
                   in
                FStar_All.pipe_left fail uu____84248)
             else ();
             (let uu____84260 = (FStar_ST.op_Bang success) && b  in
              FStar_ST.op_Colon_Equals success uu____84260))
  
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
            (let uu____84346 = FStar_Util.string_of_int i  in
             FStar_Util.print1 "%s ..." uu____84346);
            (let uu____84350 = FStar_Main.process_args ()  in
             FStar_All.pipe_right uu____84350 (fun a1  -> ()));
            (let uu____84366 = FStar_Syntax_Print.term_to_string x1  in
             let uu____84368 = FStar_Syntax_Print.term_to_string y1  in
             FStar_Util.print2 "Unify %s\nand %s\n" uu____84366 uu____84368);
            (let g =
               let uu____84372 =
                 let uu____84373 =
                   let uu____84374 = tcenv ()  in
                   FStar_TypeChecker_Rel.teq uu____84374 x1 y1  in
                 let uu____84375 =
                   let uu____84380 = tcenv ()  in
                   FStar_TypeChecker_Rel.solve_deferred_constraints
                     uu____84380
                    in
                 FStar_All.pipe_right uu____84373 uu____84375  in
               let uu____84381 =
                 let uu____84386 = tcenv ()  in
                 FStar_TypeChecker_Rel.simplify_guard uu____84386  in
               FStar_All.pipe_right uu____84372 uu____84381  in
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
        (fun uu___783_84411  ->
           match () with
           | () ->
               let g =
                 let uu____84413 =
                   let uu____84414 = tcenv ()  in
                   FStar_TypeChecker_Rel.teq uu____84414 x1 y1  in
                 let uu____84415 =
                   let uu____84420 = tcenv ()  in
                   FStar_TypeChecker_Rel.solve_deferred_constraints
                     uu____84420
                    in
                 FStar_All.pipe_right uu____84413 uu____84415  in
               (match g.FStar_TypeChecker_Env.guard_f with
                | FStar_TypeChecker_Common.Trivial  ->
                    let uu____84421 =
                      let uu____84423 = FStar_Syntax_Print.term_to_string x1
                         in
                      let uu____84425 = FStar_Syntax_Print.term_to_string y1
                         in
                      FStar_Util.format2
                        "%s and %s should not be unifiable\n" uu____84423
                        uu____84425
                       in
                    fail uu____84421
                | FStar_TypeChecker_Common.NonTrivial f ->
                    let uu____84429 = FStar_Syntax_Print.term_to_string x1
                       in
                    let uu____84431 = FStar_Syntax_Print.term_to_string y1
                       in
                    let uu____84433 = FStar_Syntax_Print.term_to_string f  in
                    FStar_Util.print3 "%s and %s are unifiable if %s\n"
                      uu____84429 uu____84431 uu____84433)) ()
      with | FStar_Errors.Error (e,msg,r) -> FStar_Util.print1 "%s\n" msg
  
let (unify' : Prims.string -> Prims.string -> unit) =
  fun x1  ->
    fun y1  ->
      let x2 = FStar_Tests_Pars.pars x1  in
      let y2 = FStar_Tests_Pars.pars y1  in
      let g =
        let uu____84465 =
          let uu____84466 = tcenv ()  in
          FStar_TypeChecker_Rel.teq uu____84466 x2 y2  in
        let uu____84467 =
          let uu____84472 = tcenv ()  in
          FStar_TypeChecker_Rel.solve_deferred_constraints uu____84472  in
        FStar_All.pipe_right uu____84465 uu____84467  in
      let uu____84473 = FStar_Syntax_Print.term_to_string x2  in
      let uu____84475 = FStar_Syntax_Print.term_to_string y2  in
      let uu____84477 = guard_to_string g.FStar_TypeChecker_Env.guard_f  in
      FStar_Util.print3 "%s and %s are unifiable with guard %s\n" uu____84473
        uu____84475 uu____84477
  
let (norm : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____84486 = tcenv ()  in
    FStar_TypeChecker_Normalize.normalize [] uu____84486 t
  
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
          (let uu____84536 =
             let uu____84549 = FStar_Tests_Pars.init ()  in
             FStar_TypeChecker_Util.new_implicit_var ""
               FStar_Range.dummyRange uu____84549 FStar_Syntax_Util.ktype0
              in
           match uu____84536 with
           | (t,uu____84554,uu____84555) ->
               let uu____84568 =
                 let uu____84581 = FStar_Tests_Pars.init ()  in
                 FStar_TypeChecker_Util.new_implicit_var ""
                   FStar_Range.dummyRange uu____84581 t
                  in
               (match uu____84568 with
                | (u,uu____84586,uu____84587) ->
                    aux (u :: out) (n2 - (Prims.parse_int "1"))))
         in
      let us = aux [] n1  in
      let uu____84604 =
        let uu____84605 = FStar_Tests_Util.app tm1 us  in norm uu____84605
         in
      (uu____84604, us)
  
let (run_all : unit -> Prims.bool) =
  fun uu____84614  ->
    FStar_Util.print_string "Testing the unifier\n";
    FStar_Options.__set_unit_tests ();
    (let unify_check n1 x1 y1 g f = unify n1 x1 y1 g f  in
     let unify1 n1 x1 y1 g = unify n1 x1 y1 g (fun uu____84691  -> ())  in
     let int_t = FStar_Tests_Pars.tc "Prims.int"  in
     let x1 =
       let uu____84697 =
         FStar_Syntax_Syntax.gen_bv "x" FStar_Pervasives_Native.None int_t
          in
       FStar_All.pipe_right uu____84697 FStar_Syntax_Syntax.bv_to_name  in
     let y1 =
       let uu____84704 =
         FStar_Syntax_Syntax.gen_bv "y" FStar_Pervasives_Native.None int_t
          in
       FStar_All.pipe_right uu____84704 FStar_Syntax_Syntax.bv_to_name  in
     unify1 (Prims.parse_int "0") x1 x1 FStar_TypeChecker_Common.Trivial;
     (let uu____84711 =
        let uu____84712 =
          FStar_Syntax_Util.mk_eq2 FStar_Syntax_Syntax.U_zero
            FStar_Syntax_Util.t_bool x1 y1
           in
        FStar_TypeChecker_Common.NonTrivial uu____84712  in
      unify1 (Prims.parse_int "1") x1 y1 uu____84711);
     (let id1 = FStar_Tests_Pars.tc "fun x -> x"  in
      (let uu____84717 = FStar_Tests_Util.app id1 [x1]  in
       unify1 (Prims.parse_int "2") x1 uu____84717
         FStar_TypeChecker_Common.Trivial);
      (let id2 = FStar_Tests_Pars.tc "fun x -> x"  in
       unify1 (Prims.parse_int "3") id2 id2 FStar_TypeChecker_Common.Trivial;
       (let id3 = FStar_Tests_Pars.tc "fun x -> x"  in
        let id' = FStar_Tests_Pars.tc "fun y -> y"  in
        unify1 (Prims.parse_int "4") id3 id' FStar_TypeChecker_Common.Trivial;
        (let uu____84732 = FStar_Tests_Pars.tc "fun x y -> x"  in
         let uu____84736 = FStar_Tests_Pars.tc "fun a b -> a"  in
         unify1 (Prims.parse_int "5") uu____84732 uu____84736
           FStar_TypeChecker_Common.Trivial);
        (let uu____84742 = FStar_Tests_Pars.tc "fun x y z -> y"  in
         let uu____84746 = FStar_Tests_Pars.tc "fun a b c -> b"  in
         unify1 (Prims.parse_int "6") uu____84742 uu____84746
           FStar_TypeChecker_Common.Trivial);
        (let uu____84752 = FStar_Tests_Pars.tc "fun (x:int) (y:int) -> y"  in
         let uu____84756 = FStar_Tests_Pars.tc "fun (x:int) (y:int) -> x"  in
         let uu____84760 =
           let uu____84761 =
             FStar_Tests_Pars.tc "(forall (x:int). (forall (y:int). y==x))"
              in
           FStar_TypeChecker_Common.NonTrivial uu____84761  in
         unify1 (Prims.parse_int "7") uu____84752 uu____84756 uu____84760);
        (let uu____84765 =
           FStar_Tests_Pars.tc "fun (x:int) (y:int) (z:int) -> y"  in
         let uu____84769 =
           FStar_Tests_Pars.tc "fun (x:int) (y:int) (z:int) -> z"  in
         let uu____84773 =
           let uu____84774 =
             FStar_Tests_Pars.tc
               "(forall (x:int). (forall (y:int). (forall (z:int). y==z)))"
              in
           FStar_TypeChecker_Common.NonTrivial uu____84774  in
         unify1 (Prims.parse_int "8") uu____84765 uu____84769 uu____84773);
        (let uu____84778 = FStar_Main.process_args ()  in
         FStar_All.pipe_right uu____84778 (fun a2  -> ()));
        (let uu____84793 =
           let uu____84800 = FStar_Tests_Pars.tc "fun u x -> u x"  in
           inst (Prims.parse_int "1") uu____84800  in
         match uu____84793 with
         | (tm1,us) ->
             let sol = FStar_Tests_Pars.tc "fun x -> c_and x x"  in
             (unify_check (Prims.parse_int "9") tm1 sol
                FStar_TypeChecker_Common.Trivial
                (fun uu____84818  ->
                   let uu____84819 =
                     let uu____84821 =
                       let uu____84824 = FStar_List.hd us  in
                       norm uu____84824  in
                     let uu____84825 = norm sol  in
                     FStar_Tests_Util.term_eq uu____84821 uu____84825  in
                   FStar_Tests_Util.always (Prims.parse_int "9") uu____84819);
              (let uu____84829 =
                 let uu____84836 = FStar_Tests_Pars.tc "fun u x -> u x"  in
                 inst (Prims.parse_int "1") uu____84836  in
               match uu____84829 with
               | (tm2,us1) ->
                   let sol1 = FStar_Tests_Pars.tc "fun x y -> x + y"  in
                   (unify_check (Prims.parse_int "10") tm2 sol1
                      FStar_TypeChecker_Common.Trivial
                      (fun uu____84854  ->
                         let uu____84855 =
                           let uu____84857 =
                             let uu____84860 = FStar_List.hd us1  in
                             norm uu____84860  in
                           let uu____84861 = norm sol1  in
                           FStar_Tests_Util.term_eq uu____84857 uu____84861
                            in
                         FStar_Tests_Util.always (Prims.parse_int "10")
                           uu____84855);
                    (let tm11 =
                       FStar_Tests_Pars.tc "x:int -> y:int{eq2 y x} -> bool"
                        in
                     let tm21 = FStar_Tests_Pars.tc "x:int -> y:int -> bool"
                        in
                     (let uu____84870 =
                        let uu____84871 =
                          FStar_Tests_Pars.tc
                            "forall (x:int). (forall (y:int). y==x)"
                           in
                        FStar_TypeChecker_Common.NonTrivial uu____84871  in
                      unify1 (Prims.parse_int "11") tm11 tm21 uu____84870);
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
                      (let uu____84880 =
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
                           let uu____84898 =
                             let uu____84899 =
                               let uu____84902 =
                                 FStar_Syntax_Syntax.bv_to_name q  in
                               [uu____84902]  in
                             FStar_Tests_Util.app l uu____84899  in
                           norm uu____84898  in
                         let l1 =
                           FStar_Tests_Pars.tc "fun (p:unit -> Type0) -> p"
                            in
                         let unit = FStar_Tests_Pars.tc "()"  in
                         let env =
                           let uu____84908 = FStar_Tests_Pars.init ()  in
                           let uu____84909 =
                             let uu____84910 =
                               FStar_Syntax_Syntax.mk_binder x2  in
                             let uu____84917 =
                               let uu____84926 =
                                 FStar_Syntax_Syntax.mk_binder q  in
                               [uu____84926]  in
                             uu____84910 :: uu____84917  in
                           FStar_TypeChecker_Env.push_binders uu____84908
                             uu____84909
                            in
                         let uu____84951 =
                           FStar_TypeChecker_Util.new_implicit_var ""
                             FStar_Range.dummyRange env typ
                            in
                         match uu____84951 with
                         | (u_p,uu____84974,uu____84975) ->
                             let tm23 =
                               let uu____84991 =
                                 let uu____84994 =
                                   FStar_Tests_Util.app l1 [u_p]  in
                                 norm uu____84994  in
                               FStar_Tests_Util.app uu____84991 [unit]  in
                             (tm13, tm23)
                          in
                       match uu____84880 with
                       | (tm13,tm23) ->
                           (unify1 (Prims.parse_int "13") tm13 tm23
                              FStar_TypeChecker_Common.Trivial;
                            (let uu____85012 =
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
                                 let uu____85030 =
                                   let uu____85031 =
                                     let uu____85034 =
                                       FStar_Syntax_Syntax.bv_to_name q  in
                                     [uu____85034]  in
                                   FStar_Tests_Util.app l uu____85031  in
                                 norm uu____85030  in
                               let l1 =
                                 FStar_Tests_Pars.tc
                                   "fun (p:pure_post unit) -> p"
                                  in
                               let unit = FStar_Tests_Pars.tc "()"  in
                               let env =
                                 let uu____85040 = FStar_Tests_Pars.init ()
                                    in
                                 let uu____85041 =
                                   let uu____85042 =
                                     FStar_Syntax_Syntax.mk_binder x2  in
                                   let uu____85049 =
                                     let uu____85058 =
                                       FStar_Syntax_Syntax.mk_binder q  in
                                     [uu____85058]  in
                                   uu____85042 :: uu____85049  in
                                 FStar_TypeChecker_Env.push_binders
                                   uu____85040 uu____85041
                                  in
                               let uu____85083 =
                                 FStar_TypeChecker_Util.new_implicit_var ""
                                   FStar_Range.dummyRange env typ
                                  in
                               match uu____85083 with
                               | (u_p,uu____85106,uu____85107) ->
                                   let tm24 =
                                     let uu____85123 =
                                       let uu____85126 =
                                         FStar_Tests_Util.app l1 [u_p]  in
                                       norm uu____85126  in
                                     FStar_Tests_Util.app uu____85123 [unit]
                                      in
                                   (tm14, tm24)
                                in
                             match uu____85012 with
                             | (tm14,tm24) ->
                                 (unify1 (Prims.parse_int "14") tm14 tm24
                                    FStar_TypeChecker_Common.Trivial;
                                  FStar_Options.__clear_unit_tests ();
                                  (let uu____85146 = FStar_ST.op_Bang success
                                      in
                                   if uu____85146
                                   then
                                     FStar_Util.print_string "Unifier ok\n"
                                   else ());
                                  FStar_ST.op_Bang success))))))))))))))
  