open Prims
let (tcenv : unit -> FStar_TypeChecker_Env.env) =
  fun uu____84227  -> FStar_Tests_Pars.init () 
let (guard_to_string :
  FStar_TypeChecker_Common.guard_formula -> Prims.string) =
  fun g  ->
    match g with
    | FStar_TypeChecker_Common.Trivial  -> "trivial"
    | FStar_TypeChecker_Common.NonTrivial f ->
        let uu____84238 = tcenv ()  in
        FStar_TypeChecker_Normalize.term_to_string uu____84238 f
  
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
        let uu____84305 =
          match (g, g') with
          | (FStar_TypeChecker_Common.Trivial
             ,FStar_TypeChecker_Common.Trivial ) -> (true, g, g')
          | (FStar_TypeChecker_Common.NonTrivial
             f,FStar_TypeChecker_Common.NonTrivial f') ->
              let f1 =
                let uu____84325 = tcenv ()  in
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Env.EraseUniverses] uu____84325 f
                 in
              let f'1 =
                let uu____84327 = tcenv ()  in
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Env.EraseUniverses] uu____84327 f'
                 in
              let uu____84328 = FStar_Tests_Util.term_eq f1 f'1  in
              (uu____84328, (FStar_TypeChecker_Common.NonTrivial f1),
                (FStar_TypeChecker_Common.NonTrivial f'1))
          | uu____84331 -> (false, g, g')  in
        match uu____84305 with
        | (b,g1,g'1) ->
            (if Prims.op_Negation b
             then
               (let uu____84345 =
                  let uu____84347 = FStar_Util.string_of_int i  in
                  let uu____84349 = guard_to_string g'1  in
                  let uu____84351 = guard_to_string g1  in
                  FStar_Util.format3
                    "Test %s failed:\n\tExpected guard %s;\n\tGot guard      %s\n"
                    uu____84347 uu____84349 uu____84351
                   in
                FStar_All.pipe_left fail uu____84345)
             else ();
             (let uu____84357 = (FStar_ST.op_Bang success) && b  in
              FStar_ST.op_Colon_Equals success uu____84357))
  
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
            (let uu____84443 = FStar_Util.string_of_int i  in
             FStar_Util.print1 "%s ..." uu____84443);
            (let uu____84447 = FStar_Main.process_args ()  in
             FStar_All.pipe_right uu____84447 (fun a1  -> ()));
            (let uu____84463 = FStar_Syntax_Print.term_to_string x1  in
             let uu____84465 = FStar_Syntax_Print.term_to_string y1  in
             FStar_Util.print2 "Unify %s\nand %s\n" uu____84463 uu____84465);
            (let g =
               let uu____84469 =
                 let uu____84470 =
                   let uu____84471 = tcenv ()  in
                   FStar_TypeChecker_Rel.teq uu____84471 x1 y1  in
                 let uu____84472 =
                   let uu____84477 = tcenv ()  in
                   FStar_TypeChecker_Rel.solve_deferred_constraints
                     uu____84477
                    in
                 FStar_All.pipe_right uu____84470 uu____84472  in
               let uu____84478 =
                 let uu____84483 = tcenv ()  in
                 FStar_TypeChecker_Rel.simplify_guard uu____84483  in
               FStar_All.pipe_right uu____84469 uu____84478  in
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
        (fun uu___783_84508  ->
           match () with
           | () ->
               let g =
                 let uu____84510 =
                   let uu____84511 = tcenv ()  in
                   FStar_TypeChecker_Rel.teq uu____84511 x1 y1  in
                 let uu____84512 =
                   let uu____84517 = tcenv ()  in
                   FStar_TypeChecker_Rel.solve_deferred_constraints
                     uu____84517
                    in
                 FStar_All.pipe_right uu____84510 uu____84512  in
               (match g.FStar_TypeChecker_Env.guard_f with
                | FStar_TypeChecker_Common.Trivial  ->
                    let uu____84518 =
                      let uu____84520 = FStar_Syntax_Print.term_to_string x1
                         in
                      let uu____84522 = FStar_Syntax_Print.term_to_string y1
                         in
                      FStar_Util.format2
                        "%s and %s should not be unifiable\n" uu____84520
                        uu____84522
                       in
                    fail uu____84518
                | FStar_TypeChecker_Common.NonTrivial f ->
                    let uu____84526 = FStar_Syntax_Print.term_to_string x1
                       in
                    let uu____84528 = FStar_Syntax_Print.term_to_string y1
                       in
                    let uu____84530 = FStar_Syntax_Print.term_to_string f  in
                    FStar_Util.print3 "%s and %s are unifiable if %s\n"
                      uu____84526 uu____84528 uu____84530)) ()
      with | FStar_Errors.Error (e,msg,r) -> FStar_Util.print1 "%s\n" msg
  
let (unify' : Prims.string -> Prims.string -> unit) =
  fun x1  ->
    fun y1  ->
      let x2 = FStar_Tests_Pars.pars x1  in
      let y2 = FStar_Tests_Pars.pars y1  in
      let g =
        let uu____84562 =
          let uu____84563 = tcenv ()  in
          FStar_TypeChecker_Rel.teq uu____84563 x2 y2  in
        let uu____84564 =
          let uu____84569 = tcenv ()  in
          FStar_TypeChecker_Rel.solve_deferred_constraints uu____84569  in
        FStar_All.pipe_right uu____84562 uu____84564  in
      let uu____84570 = FStar_Syntax_Print.term_to_string x2  in
      let uu____84572 = FStar_Syntax_Print.term_to_string y2  in
      let uu____84574 = guard_to_string g.FStar_TypeChecker_Env.guard_f  in
      FStar_Util.print3 "%s and %s are unifiable with guard %s\n" uu____84570
        uu____84572 uu____84574
  
let (norm : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____84583 = tcenv ()  in
    FStar_TypeChecker_Normalize.normalize [] uu____84583 t
  
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
          (let uu____84633 =
             let uu____84646 = FStar_Tests_Pars.init ()  in
             FStar_TypeChecker_Util.new_implicit_var ""
               FStar_Range.dummyRange uu____84646 FStar_Syntax_Util.ktype0
              in
           match uu____84633 with
           | (t,uu____84651,uu____84652) ->
               let uu____84665 =
                 let uu____84678 = FStar_Tests_Pars.init ()  in
                 FStar_TypeChecker_Util.new_implicit_var ""
                   FStar_Range.dummyRange uu____84678 t
                  in
               (match uu____84665 with
                | (u,uu____84683,uu____84684) ->
                    aux (u :: out) (n2 - (Prims.parse_int "1"))))
         in
      let us = aux [] n1  in
      let uu____84701 =
        let uu____84702 = FStar_Tests_Util.app tm1 us  in norm uu____84702
         in
      (uu____84701, us)
  
let (run_all : unit -> Prims.bool) =
  fun uu____84711  ->
    FStar_Util.print_string "Testing the unifier\n";
    FStar_Options.__set_unit_tests ();
    (let unify_check n1 x1 y1 g f = unify n1 x1 y1 g f  in
     let unify1 n1 x1 y1 g = unify n1 x1 y1 g (fun uu____84788  -> ())  in
     let int_t = FStar_Tests_Pars.tc "Prims.int"  in
     let x1 =
       let uu____84794 =
         FStar_Syntax_Syntax.gen_bv "x" FStar_Pervasives_Native.None int_t
          in
       FStar_All.pipe_right uu____84794 FStar_Syntax_Syntax.bv_to_name  in
     let y1 =
       let uu____84801 =
         FStar_Syntax_Syntax.gen_bv "y" FStar_Pervasives_Native.None int_t
          in
       FStar_All.pipe_right uu____84801 FStar_Syntax_Syntax.bv_to_name  in
     unify1 (Prims.parse_int "0") x1 x1 FStar_TypeChecker_Common.Trivial;
     (let uu____84808 =
        let uu____84809 =
          FStar_Syntax_Util.mk_eq2 FStar_Syntax_Syntax.U_zero
            FStar_Syntax_Util.t_bool x1 y1
           in
        FStar_TypeChecker_Common.NonTrivial uu____84809  in
      unify1 (Prims.parse_int "1") x1 y1 uu____84808);
     (let id1 = FStar_Tests_Pars.tc "fun x -> x"  in
      (let uu____84814 = FStar_Tests_Util.app id1 [x1]  in
       unify1 (Prims.parse_int "2") x1 uu____84814
         FStar_TypeChecker_Common.Trivial);
      (let id2 = FStar_Tests_Pars.tc "fun x -> x"  in
       unify1 (Prims.parse_int "3") id2 id2 FStar_TypeChecker_Common.Trivial;
       (let id3 = FStar_Tests_Pars.tc "fun x -> x"  in
        let id' = FStar_Tests_Pars.tc "fun y -> y"  in
        unify1 (Prims.parse_int "4") id3 id' FStar_TypeChecker_Common.Trivial;
        (let uu____84829 = FStar_Tests_Pars.tc "fun x y -> x"  in
         let uu____84833 = FStar_Tests_Pars.tc "fun a b -> a"  in
         unify1 (Prims.parse_int "5") uu____84829 uu____84833
           FStar_TypeChecker_Common.Trivial);
        (let uu____84839 = FStar_Tests_Pars.tc "fun x y z -> y"  in
         let uu____84843 = FStar_Tests_Pars.tc "fun a b c -> b"  in
         unify1 (Prims.parse_int "6") uu____84839 uu____84843
           FStar_TypeChecker_Common.Trivial);
        (let uu____84849 = FStar_Tests_Pars.tc "fun (x:int) (y:int) -> y"  in
         let uu____84853 = FStar_Tests_Pars.tc "fun (x:int) (y:int) -> x"  in
         let uu____84857 =
           let uu____84858 =
             FStar_Tests_Pars.tc "(forall (x:int). (forall (y:int). y==x))"
              in
           FStar_TypeChecker_Common.NonTrivial uu____84858  in
         unify1 (Prims.parse_int "7") uu____84849 uu____84853 uu____84857);
        (let uu____84862 =
           FStar_Tests_Pars.tc "fun (x:int) (y:int) (z:int) -> y"  in
         let uu____84866 =
           FStar_Tests_Pars.tc "fun (x:int) (y:int) (z:int) -> z"  in
         let uu____84870 =
           let uu____84871 =
             FStar_Tests_Pars.tc
               "(forall (x:int). (forall (y:int). (forall (z:int). y==z)))"
              in
           FStar_TypeChecker_Common.NonTrivial uu____84871  in
         unify1 (Prims.parse_int "8") uu____84862 uu____84866 uu____84870);
        (let uu____84875 = FStar_Main.process_args ()  in
         FStar_All.pipe_right uu____84875 (fun a2  -> ()));
        (let uu____84890 =
           let uu____84897 = FStar_Tests_Pars.tc "fun u x -> u x"  in
           inst (Prims.parse_int "1") uu____84897  in
         match uu____84890 with
         | (tm1,us) ->
             let sol = FStar_Tests_Pars.tc "fun x -> c_and x x"  in
             (unify_check (Prims.parse_int "9") tm1 sol
                FStar_TypeChecker_Common.Trivial
                (fun uu____84915  ->
                   let uu____84916 =
                     let uu____84918 =
                       let uu____84921 = FStar_List.hd us  in
                       norm uu____84921  in
                     let uu____84922 = norm sol  in
                     FStar_Tests_Util.term_eq uu____84918 uu____84922  in
                   FStar_Tests_Util.always (Prims.parse_int "9") uu____84916);
              (let uu____84926 =
                 let uu____84933 = FStar_Tests_Pars.tc "fun u x -> u x"  in
                 inst (Prims.parse_int "1") uu____84933  in
               match uu____84926 with
               | (tm2,us1) ->
                   let sol1 = FStar_Tests_Pars.tc "fun x y -> x + y"  in
                   (unify_check (Prims.parse_int "10") tm2 sol1
                      FStar_TypeChecker_Common.Trivial
                      (fun uu____84951  ->
                         let uu____84952 =
                           let uu____84954 =
                             let uu____84957 = FStar_List.hd us1  in
                             norm uu____84957  in
                           let uu____84958 = norm sol1  in
                           FStar_Tests_Util.term_eq uu____84954 uu____84958
                            in
                         FStar_Tests_Util.always (Prims.parse_int "10")
                           uu____84952);
                    (let tm11 =
                       FStar_Tests_Pars.tc "x:int -> y:int{eq2 y x} -> bool"
                        in
                     let tm21 = FStar_Tests_Pars.tc "x:int -> y:int -> bool"
                        in
                     (let uu____84967 =
                        let uu____84968 =
                          FStar_Tests_Pars.tc
                            "forall (x:int). (forall (y:int). y==x)"
                           in
                        FStar_TypeChecker_Common.NonTrivial uu____84968  in
                      unify1 (Prims.parse_int "11") tm11 tm21 uu____84967);
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
                      (let uu____84977 =
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
                           let uu____84995 =
                             let uu____84996 =
                               let uu____84999 =
                                 FStar_Syntax_Syntax.bv_to_name q  in
                               [uu____84999]  in
                             FStar_Tests_Util.app l uu____84996  in
                           norm uu____84995  in
                         let l1 =
                           FStar_Tests_Pars.tc "fun (p:unit -> Type0) -> p"
                            in
                         let unit = FStar_Tests_Pars.tc "()"  in
                         let env =
                           let uu____85005 = FStar_Tests_Pars.init ()  in
                           let uu____85006 =
                             let uu____85007 =
                               FStar_Syntax_Syntax.mk_binder x2  in
                             let uu____85014 =
                               let uu____85023 =
                                 FStar_Syntax_Syntax.mk_binder q  in
                               [uu____85023]  in
                             uu____85007 :: uu____85014  in
                           FStar_TypeChecker_Env.push_binders uu____85005
                             uu____85006
                            in
                         let uu____85048 =
                           FStar_TypeChecker_Util.new_implicit_var ""
                             FStar_Range.dummyRange env typ
                            in
                         match uu____85048 with
                         | (u_p,uu____85071,uu____85072) ->
                             let tm23 =
                               let uu____85088 =
                                 let uu____85091 =
                                   FStar_Tests_Util.app l1 [u_p]  in
                                 norm uu____85091  in
                               FStar_Tests_Util.app uu____85088 [unit]  in
                             (tm13, tm23)
                          in
                       match uu____84977 with
                       | (tm13,tm23) ->
                           (unify1 (Prims.parse_int "13") tm13 tm23
                              FStar_TypeChecker_Common.Trivial;
                            (let uu____85109 =
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
                                 let uu____85127 =
                                   let uu____85128 =
                                     let uu____85131 =
                                       FStar_Syntax_Syntax.bv_to_name q  in
                                     [uu____85131]  in
                                   FStar_Tests_Util.app l uu____85128  in
                                 norm uu____85127  in
                               let l1 =
                                 FStar_Tests_Pars.tc
                                   "fun (p:pure_post unit) -> p"
                                  in
                               let unit = FStar_Tests_Pars.tc "()"  in
                               let env =
                                 let uu____85137 = FStar_Tests_Pars.init ()
                                    in
                                 let uu____85138 =
                                   let uu____85139 =
                                     FStar_Syntax_Syntax.mk_binder x2  in
                                   let uu____85146 =
                                     let uu____85155 =
                                       FStar_Syntax_Syntax.mk_binder q  in
                                     [uu____85155]  in
                                   uu____85139 :: uu____85146  in
                                 FStar_TypeChecker_Env.push_binders
                                   uu____85137 uu____85138
                                  in
                               let uu____85180 =
                                 FStar_TypeChecker_Util.new_implicit_var ""
                                   FStar_Range.dummyRange env typ
                                  in
                               match uu____85180 with
                               | (u_p,uu____85203,uu____85204) ->
                                   let tm24 =
                                     let uu____85220 =
                                       let uu____85223 =
                                         FStar_Tests_Util.app l1 [u_p]  in
                                       norm uu____85223  in
                                     FStar_Tests_Util.app uu____85220 [unit]
                                      in
                                   (tm14, tm24)
                                in
                             match uu____85109 with
                             | (tm14,tm24) ->
                                 (unify1 (Prims.parse_int "14") tm14 tm24
                                    FStar_TypeChecker_Common.Trivial;
                                  FStar_Options.__clear_unit_tests ();
                                  (let uu____85243 = FStar_ST.op_Bang success
                                      in
                                   if uu____85243
                                   then
                                     FStar_Util.print_string "Unifier ok\n"
                                   else ());
                                  FStar_ST.op_Bang success))))))))))))))
  