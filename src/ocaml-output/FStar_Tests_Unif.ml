open Prims
let (tcenv : unit -> FStar_TypeChecker_Env.env) =
  fun uu____84120  -> FStar_Tests_Pars.init () 
let (guard_to_string :
  FStar_TypeChecker_Common.guard_formula -> Prims.string) =
  fun g  ->
    match g with
    | FStar_TypeChecker_Common.Trivial  -> "trivial"
    | FStar_TypeChecker_Common.NonTrivial f ->
        let uu____84131 = tcenv ()  in
        FStar_TypeChecker_Normalize.term_to_string uu____84131 f
  
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
        let uu____84198 =
          match (g, g') with
          | (FStar_TypeChecker_Common.Trivial
             ,FStar_TypeChecker_Common.Trivial ) -> (true, g, g')
          | (FStar_TypeChecker_Common.NonTrivial
             f,FStar_TypeChecker_Common.NonTrivial f') ->
              let f1 =
                let uu____84218 = tcenv ()  in
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Env.EraseUniverses] uu____84218 f
                 in
              let f'1 =
                let uu____84220 = tcenv ()  in
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Env.EraseUniverses] uu____84220 f'
                 in
              let uu____84221 = FStar_Tests_Util.term_eq f1 f'1  in
              (uu____84221, (FStar_TypeChecker_Common.NonTrivial f1),
                (FStar_TypeChecker_Common.NonTrivial f'1))
          | uu____84224 -> (false, g, g')  in
        match uu____84198 with
        | (b,g1,g'1) ->
            (if Prims.op_Negation b
             then
               (let uu____84238 =
                  let uu____84240 = FStar_Util.string_of_int i  in
                  let uu____84242 = guard_to_string g'1  in
                  let uu____84244 = guard_to_string g1  in
                  FStar_Util.format3
                    "Test %s failed:\n\tExpected guard %s;\n\tGot guard      %s\n"
                    uu____84240 uu____84242 uu____84244
                   in
                FStar_All.pipe_left fail uu____84238)
             else ();
             (let uu____84250 = (FStar_ST.op_Bang success) && b  in
              FStar_ST.op_Colon_Equals success uu____84250))
  
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
            (let uu____84336 = FStar_Util.string_of_int i  in
             FStar_Util.print1 "%s ..." uu____84336);
            (let uu____84340 = FStar_Main.process_args ()  in
             FStar_All.pipe_right uu____84340 (fun a1  -> ()));
            (let uu____84356 = FStar_Syntax_Print.term_to_string x1  in
             let uu____84358 = FStar_Syntax_Print.term_to_string y1  in
             FStar_Util.print2 "Unify %s\nand %s\n" uu____84356 uu____84358);
            (let g =
               let uu____84362 =
                 let uu____84363 =
                   let uu____84364 = tcenv ()  in
                   FStar_TypeChecker_Rel.teq uu____84364 x1 y1  in
                 let uu____84365 =
                   let uu____84370 = tcenv ()  in
                   FStar_TypeChecker_Rel.solve_deferred_constraints
                     uu____84370
                    in
                 FStar_All.pipe_right uu____84363 uu____84365  in
               let uu____84371 =
                 let uu____84376 = tcenv ()  in
                 FStar_TypeChecker_Rel.simplify_guard uu____84376  in
               FStar_All.pipe_right uu____84362 uu____84371  in
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
        (fun uu___783_84401  ->
           match () with
           | () ->
               let g =
                 let uu____84403 =
                   let uu____84404 = tcenv ()  in
                   FStar_TypeChecker_Rel.teq uu____84404 x1 y1  in
                 let uu____84405 =
                   let uu____84410 = tcenv ()  in
                   FStar_TypeChecker_Rel.solve_deferred_constraints
                     uu____84410
                    in
                 FStar_All.pipe_right uu____84403 uu____84405  in
               (match g.FStar_TypeChecker_Env.guard_f with
                | FStar_TypeChecker_Common.Trivial  ->
                    let uu____84411 =
                      let uu____84413 = FStar_Syntax_Print.term_to_string x1
                         in
                      let uu____84415 = FStar_Syntax_Print.term_to_string y1
                         in
                      FStar_Util.format2
                        "%s and %s should not be unifiable\n" uu____84413
                        uu____84415
                       in
                    fail uu____84411
                | FStar_TypeChecker_Common.NonTrivial f ->
                    let uu____84419 = FStar_Syntax_Print.term_to_string x1
                       in
                    let uu____84421 = FStar_Syntax_Print.term_to_string y1
                       in
                    let uu____84423 = FStar_Syntax_Print.term_to_string f  in
                    FStar_Util.print3 "%s and %s are unifiable if %s\n"
                      uu____84419 uu____84421 uu____84423)) ()
      with | FStar_Errors.Error (e,msg,r) -> FStar_Util.print1 "%s\n" msg
  
let (unify' : Prims.string -> Prims.string -> unit) =
  fun x1  ->
    fun y1  ->
      let x2 = FStar_Tests_Pars.pars x1  in
      let y2 = FStar_Tests_Pars.pars y1  in
      let g =
        let uu____84455 =
          let uu____84456 = tcenv ()  in
          FStar_TypeChecker_Rel.teq uu____84456 x2 y2  in
        let uu____84457 =
          let uu____84462 = tcenv ()  in
          FStar_TypeChecker_Rel.solve_deferred_constraints uu____84462  in
        FStar_All.pipe_right uu____84455 uu____84457  in
      let uu____84463 = FStar_Syntax_Print.term_to_string x2  in
      let uu____84465 = FStar_Syntax_Print.term_to_string y2  in
      let uu____84467 = guard_to_string g.FStar_TypeChecker_Env.guard_f  in
      FStar_Util.print3 "%s and %s are unifiable with guard %s\n" uu____84463
        uu____84465 uu____84467
  
let (norm : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____84476 = tcenv ()  in
    FStar_TypeChecker_Normalize.normalize [] uu____84476 t
  
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
          (let uu____84526 =
             let uu____84539 = FStar_Tests_Pars.init ()  in
             FStar_TypeChecker_Util.new_implicit_var ""
               FStar_Range.dummyRange uu____84539 FStar_Syntax_Util.ktype0
              in
           match uu____84526 with
           | (t,uu____84544,uu____84545) ->
               let uu____84558 =
                 let uu____84571 = FStar_Tests_Pars.init ()  in
                 FStar_TypeChecker_Util.new_implicit_var ""
                   FStar_Range.dummyRange uu____84571 t
                  in
               (match uu____84558 with
                | (u,uu____84576,uu____84577) ->
                    aux (u :: out) (n2 - (Prims.parse_int "1"))))
         in
      let us = aux [] n1  in
      let uu____84594 =
        let uu____84595 = FStar_Tests_Util.app tm1 us  in norm uu____84595
         in
      (uu____84594, us)
  
let (run_all : unit -> Prims.bool) =
  fun uu____84604  ->
    FStar_Util.print_string "Testing the unifier\n";
    FStar_Options.__set_unit_tests ();
    (let unify_check n1 x1 y1 g f = unify n1 x1 y1 g f  in
     let unify1 n1 x1 y1 g = unify n1 x1 y1 g (fun uu____84681  -> ())  in
     let int_t = FStar_Tests_Pars.tc "Prims.int"  in
     let x1 =
       let uu____84687 =
         FStar_Syntax_Syntax.gen_bv "x" FStar_Pervasives_Native.None int_t
          in
       FStar_All.pipe_right uu____84687 FStar_Syntax_Syntax.bv_to_name  in
     let y1 =
       let uu____84694 =
         FStar_Syntax_Syntax.gen_bv "y" FStar_Pervasives_Native.None int_t
          in
       FStar_All.pipe_right uu____84694 FStar_Syntax_Syntax.bv_to_name  in
     unify1 (Prims.parse_int "0") x1 x1 FStar_TypeChecker_Common.Trivial;
     (let uu____84701 =
        let uu____84702 =
          FStar_Syntax_Util.mk_eq2 FStar_Syntax_Syntax.U_zero
            FStar_Syntax_Util.t_bool x1 y1
           in
        FStar_TypeChecker_Common.NonTrivial uu____84702  in
      unify1 (Prims.parse_int "1") x1 y1 uu____84701);
     (let id1 = FStar_Tests_Pars.tc "fun x -> x"  in
      (let uu____84707 = FStar_Tests_Util.app id1 [x1]  in
       unify1 (Prims.parse_int "2") x1 uu____84707
         FStar_TypeChecker_Common.Trivial);
      (let id2 = FStar_Tests_Pars.tc "fun x -> x"  in
       unify1 (Prims.parse_int "3") id2 id2 FStar_TypeChecker_Common.Trivial;
       (let id3 = FStar_Tests_Pars.tc "fun x -> x"  in
        let id' = FStar_Tests_Pars.tc "fun y -> y"  in
        unify1 (Prims.parse_int "4") id3 id' FStar_TypeChecker_Common.Trivial;
        (let uu____84722 = FStar_Tests_Pars.tc "fun x y -> x"  in
         let uu____84726 = FStar_Tests_Pars.tc "fun a b -> a"  in
         unify1 (Prims.parse_int "5") uu____84722 uu____84726
           FStar_TypeChecker_Common.Trivial);
        (let uu____84732 = FStar_Tests_Pars.tc "fun x y z -> y"  in
         let uu____84736 = FStar_Tests_Pars.tc "fun a b c -> b"  in
         unify1 (Prims.parse_int "6") uu____84732 uu____84736
           FStar_TypeChecker_Common.Trivial);
        (let uu____84742 = FStar_Tests_Pars.tc "fun (x:int) (y:int) -> y"  in
         let uu____84746 = FStar_Tests_Pars.tc "fun (x:int) (y:int) -> x"  in
         let uu____84750 =
           let uu____84751 =
             FStar_Tests_Pars.tc "(forall (x:int). (forall (y:int). y==x))"
              in
           FStar_TypeChecker_Common.NonTrivial uu____84751  in
         unify1 (Prims.parse_int "7") uu____84742 uu____84746 uu____84750);
        (let uu____84755 =
           FStar_Tests_Pars.tc "fun (x:int) (y:int) (z:int) -> y"  in
         let uu____84759 =
           FStar_Tests_Pars.tc "fun (x:int) (y:int) (z:int) -> z"  in
         let uu____84763 =
           let uu____84764 =
             FStar_Tests_Pars.tc
               "(forall (x:int). (forall (y:int). (forall (z:int). y==z)))"
              in
           FStar_TypeChecker_Common.NonTrivial uu____84764  in
         unify1 (Prims.parse_int "8") uu____84755 uu____84759 uu____84763);
        (let uu____84768 = FStar_Main.process_args ()  in
         FStar_All.pipe_right uu____84768 (fun a2  -> ()));
        (let uu____84783 =
           let uu____84790 = FStar_Tests_Pars.tc "fun u x -> u x"  in
           inst (Prims.parse_int "1") uu____84790  in
         match uu____84783 with
         | (tm1,us) ->
             let sol = FStar_Tests_Pars.tc "fun x -> c_and x x"  in
             (unify_check (Prims.parse_int "9") tm1 sol
                FStar_TypeChecker_Common.Trivial
                (fun uu____84808  ->
                   let uu____84809 =
                     let uu____84811 =
                       let uu____84814 = FStar_List.hd us  in
                       norm uu____84814  in
                     let uu____84815 = norm sol  in
                     FStar_Tests_Util.term_eq uu____84811 uu____84815  in
                   FStar_Tests_Util.always (Prims.parse_int "9") uu____84809);
              (let uu____84819 =
                 let uu____84826 = FStar_Tests_Pars.tc "fun u x -> u x"  in
                 inst (Prims.parse_int "1") uu____84826  in
               match uu____84819 with
               | (tm2,us1) ->
                   let sol1 = FStar_Tests_Pars.tc "fun x y -> x + y"  in
                   (unify_check (Prims.parse_int "10") tm2 sol1
                      FStar_TypeChecker_Common.Trivial
                      (fun uu____84844  ->
                         let uu____84845 =
                           let uu____84847 =
                             let uu____84850 = FStar_List.hd us1  in
                             norm uu____84850  in
                           let uu____84851 = norm sol1  in
                           FStar_Tests_Util.term_eq uu____84847 uu____84851
                            in
                         FStar_Tests_Util.always (Prims.parse_int "10")
                           uu____84845);
                    (let tm11 =
                       FStar_Tests_Pars.tc "x:int -> y:int{eq2 y x} -> bool"
                        in
                     let tm21 = FStar_Tests_Pars.tc "x:int -> y:int -> bool"
                        in
                     (let uu____84860 =
                        let uu____84861 =
                          FStar_Tests_Pars.tc
                            "forall (x:int). (forall (y:int). y==x)"
                           in
                        FStar_TypeChecker_Common.NonTrivial uu____84861  in
                      unify1 (Prims.parse_int "11") tm11 tm21 uu____84860);
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
                      (let uu____84870 =
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
                           let uu____84888 =
                             let uu____84889 =
                               let uu____84892 =
                                 FStar_Syntax_Syntax.bv_to_name q  in
                               [uu____84892]  in
                             FStar_Tests_Util.app l uu____84889  in
                           norm uu____84888  in
                         let l1 =
                           FStar_Tests_Pars.tc "fun (p:unit -> Type0) -> p"
                            in
                         let unit = FStar_Tests_Pars.tc "()"  in
                         let env =
                           let uu____84898 = FStar_Tests_Pars.init ()  in
                           let uu____84899 =
                             let uu____84900 =
                               FStar_Syntax_Syntax.mk_binder x2  in
                             let uu____84907 =
                               let uu____84916 =
                                 FStar_Syntax_Syntax.mk_binder q  in
                               [uu____84916]  in
                             uu____84900 :: uu____84907  in
                           FStar_TypeChecker_Env.push_binders uu____84898
                             uu____84899
                            in
                         let uu____84941 =
                           FStar_TypeChecker_Util.new_implicit_var ""
                             FStar_Range.dummyRange env typ
                            in
                         match uu____84941 with
                         | (u_p,uu____84964,uu____84965) ->
                             let tm23 =
                               let uu____84981 =
                                 let uu____84984 =
                                   FStar_Tests_Util.app l1 [u_p]  in
                                 norm uu____84984  in
                               FStar_Tests_Util.app uu____84981 [unit]  in
                             (tm13, tm23)
                          in
                       match uu____84870 with
                       | (tm13,tm23) ->
                           (unify1 (Prims.parse_int "13") tm13 tm23
                              FStar_TypeChecker_Common.Trivial;
                            (let uu____85002 =
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
                                 let uu____85020 =
                                   let uu____85021 =
                                     let uu____85024 =
                                       FStar_Syntax_Syntax.bv_to_name q  in
                                     [uu____85024]  in
                                   FStar_Tests_Util.app l uu____85021  in
                                 norm uu____85020  in
                               let l1 =
                                 FStar_Tests_Pars.tc
                                   "fun (p:pure_post unit) -> p"
                                  in
                               let unit = FStar_Tests_Pars.tc "()"  in
                               let env =
                                 let uu____85030 = FStar_Tests_Pars.init ()
                                    in
                                 let uu____85031 =
                                   let uu____85032 =
                                     FStar_Syntax_Syntax.mk_binder x2  in
                                   let uu____85039 =
                                     let uu____85048 =
                                       FStar_Syntax_Syntax.mk_binder q  in
                                     [uu____85048]  in
                                   uu____85032 :: uu____85039  in
                                 FStar_TypeChecker_Env.push_binders
                                   uu____85030 uu____85031
                                  in
                               let uu____85073 =
                                 FStar_TypeChecker_Util.new_implicit_var ""
                                   FStar_Range.dummyRange env typ
                                  in
                               match uu____85073 with
                               | (u_p,uu____85096,uu____85097) ->
                                   let tm24 =
                                     let uu____85113 =
                                       let uu____85116 =
                                         FStar_Tests_Util.app l1 [u_p]  in
                                       norm uu____85116  in
                                     FStar_Tests_Util.app uu____85113 [unit]
                                      in
                                   (tm14, tm24)
                                in
                             match uu____85002 with
                             | (tm14,tm24) ->
                                 (unify1 (Prims.parse_int "14") tm14 tm24
                                    FStar_TypeChecker_Common.Trivial;
                                  FStar_Options.__clear_unit_tests ();
                                  (let uu____85136 = FStar_ST.op_Bang success
                                      in
                                   if uu____85136
                                   then
                                     FStar_Util.print_string "Unifier ok\n"
                                   else ());
                                  FStar_ST.op_Bang success))))))))))))))
  