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
             FStar_All.pipe_right uu____213 (fun a1  -> ()));
            (let uu____229 = FStar_Syntax_Print.term_to_string x1  in
             let uu____231 = FStar_Syntax_Print.term_to_string y1  in
             FStar_Util.print2 "Unify %s\nand %s\n" uu____229 uu____231);
            (let g =
               let uu____235 =
                 let uu____236 =
                   let uu____237 = tcenv ()  in
                   FStar_TypeChecker_Rel.teq uu____237 x1 y1  in
                 let uu____238 =
                   let uu____243 = tcenv ()  in
                   FStar_TypeChecker_Rel.solve_deferred_constraints uu____243
                    in
                 FStar_All.pipe_right uu____236 uu____238  in
               let uu____244 =
                 let uu____249 = tcenv ()  in
                 FStar_TypeChecker_Rel.simplify_guard uu____249  in
               FStar_All.pipe_right uu____235 uu____244  in
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
        (fun uu___41_274  ->
           match () with
           | () ->
               let g =
                 let uu____276 =
                   let uu____277 = tcenv ()  in
                   FStar_TypeChecker_Rel.teq uu____277 x1 y1  in
                 let uu____278 =
                   let uu____283 = tcenv ()  in
                   FStar_TypeChecker_Rel.solve_deferred_constraints uu____283
                    in
                 FStar_All.pipe_right uu____276 uu____278  in
               (match g.FStar_TypeChecker_Env.guard_f with
                | FStar_TypeChecker_Common.Trivial  ->
                    let uu____284 =
                      let uu____286 = FStar_Syntax_Print.term_to_string x1
                         in
                      let uu____288 = FStar_Syntax_Print.term_to_string y1
                         in
                      FStar_Util.format2
                        "%s and %s should not be unifiable\n" uu____286
                        uu____288
                       in
                    fail uu____284
                | FStar_TypeChecker_Common.NonTrivial f ->
                    let uu____292 = FStar_Syntax_Print.term_to_string x1  in
                    let uu____294 = FStar_Syntax_Print.term_to_string y1  in
                    let uu____296 = FStar_Syntax_Print.term_to_string f  in
                    FStar_Util.print3 "%s and %s are unifiable if %s\n"
                      uu____292 uu____294 uu____296)) ()
      with | FStar_Errors.Error (e,msg,r) -> FStar_Util.print1 "%s\n" msg
  
let (unify' : Prims.string -> Prims.string -> unit) =
  fun x1  ->
    fun y1  ->
      let x2 = FStar_Tests_Pars.pars x1  in
      let y2 = FStar_Tests_Pars.pars y1  in
      let g =
        let uu____328 =
          let uu____329 = tcenv ()  in
          FStar_TypeChecker_Rel.teq uu____329 x2 y2  in
        let uu____330 =
          let uu____335 = tcenv ()  in
          FStar_TypeChecker_Rel.solve_deferred_constraints uu____335  in
        FStar_All.pipe_right uu____328 uu____330  in
      let uu____336 = FStar_Syntax_Print.term_to_string x2  in
      let uu____338 = FStar_Syntax_Print.term_to_string y2  in
      let uu____340 = guard_to_string g.FStar_TypeChecker_Env.guard_f  in
      FStar_Util.print3 "%s and %s are unifiable with guard %s\n" uu____336
        uu____338 uu____340
  
let (norm : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____349 = tcenv ()  in
    FStar_TypeChecker_Normalize.normalize [] uu____349 t
  
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
          (let uu____399 =
             let uu____412 = FStar_Tests_Pars.init ()  in
             FStar_TypeChecker_Util.new_implicit_var ""
               FStar_Range.dummyRange uu____412 FStar_Syntax_Util.ktype0
              in
           match uu____399 with
           | (t,uu____417,uu____418) ->
               let uu____431 =
                 let uu____444 = FStar_Tests_Pars.init ()  in
                 FStar_TypeChecker_Util.new_implicit_var ""
                   FStar_Range.dummyRange uu____444 t
                  in
               (match uu____431 with
                | (u,uu____449,uu____450) ->
                    aux (u :: out) (n2 - (Prims.parse_int "1"))))
         in
      let us = aux [] n1  in
      let uu____467 =
        let uu____468 = FStar_Tests_Util.app tm1 us  in norm uu____468  in
      (uu____467, us)
  
let (run_all : unit -> Prims.bool) =
  fun uu____477  ->
    FStar_Util.print_string "Testing the unifier\n";
    FStar_Options.__set_unit_tests ();
    (let unify_check n1 x1 y1 g f = unify n1 x1 y1 g f  in
     let unify1 n1 x1 y1 g = unify n1 x1 y1 g (fun uu____554  -> ())  in
     let int_t = FStar_Tests_Pars.tc "Prims.int"  in
     let x1 =
       let uu____560 =
         FStar_Syntax_Syntax.gen_bv "x" FStar_Pervasives_Native.None int_t
          in
       FStar_All.pipe_right uu____560 FStar_Syntax_Syntax.bv_to_name  in
     let y1 =
       let uu____567 =
         FStar_Syntax_Syntax.gen_bv "y" FStar_Pervasives_Native.None int_t
          in
       FStar_All.pipe_right uu____567 FStar_Syntax_Syntax.bv_to_name  in
     unify1 (Prims.parse_int "0") x1 x1 FStar_TypeChecker_Common.Trivial;
     (let uu____574 =
        let uu____575 =
          FStar_Syntax_Util.mk_eq2 FStar_Syntax_Syntax.U_zero
            FStar_Syntax_Util.t_bool x1 y1
           in
        FStar_TypeChecker_Common.NonTrivial uu____575  in
      unify1 (Prims.parse_int "1") x1 y1 uu____574);
     (let id1 = FStar_Tests_Pars.tc "fun x -> x"  in
      (let uu____580 = FStar_Tests_Util.app id1 [x1]  in
       unify1 (Prims.parse_int "2") x1 uu____580
         FStar_TypeChecker_Common.Trivial);
      (let id2 = FStar_Tests_Pars.tc "fun x -> x"  in
       unify1 (Prims.parse_int "3") id2 id2 FStar_TypeChecker_Common.Trivial;
       (let id3 = FStar_Tests_Pars.tc "fun x -> x"  in
        let id' = FStar_Tests_Pars.tc "fun y -> y"  in
        unify1 (Prims.parse_int "4") id3 id' FStar_TypeChecker_Common.Trivial;
        (let uu____595 = FStar_Tests_Pars.tc "fun x y -> x"  in
         let uu____599 = FStar_Tests_Pars.tc "fun a b -> a"  in
         unify1 (Prims.parse_int "5") uu____595 uu____599
           FStar_TypeChecker_Common.Trivial);
        (let uu____605 = FStar_Tests_Pars.tc "fun x y z -> y"  in
         let uu____609 = FStar_Tests_Pars.tc "fun a b c -> b"  in
         unify1 (Prims.parse_int "6") uu____605 uu____609
           FStar_TypeChecker_Common.Trivial);
        (let uu____615 = FStar_Tests_Pars.tc "fun (x:int) (y:int) -> y"  in
         let uu____619 = FStar_Tests_Pars.tc "fun (x:int) (y:int) -> x"  in
         let uu____623 =
           let uu____624 =
             FStar_Tests_Pars.tc "(forall (x:int). (forall (y:int). y==x))"
              in
           FStar_TypeChecker_Common.NonTrivial uu____624  in
         unify1 (Prims.parse_int "7") uu____615 uu____619 uu____623);
        (let uu____628 =
           FStar_Tests_Pars.tc "fun (x:int) (y:int) (z:int) -> y"  in
         let uu____632 =
           FStar_Tests_Pars.tc "fun (x:int) (y:int) (z:int) -> z"  in
         let uu____636 =
           let uu____637 =
             FStar_Tests_Pars.tc
               "(forall (x:int). (forall (y:int). (forall (z:int). y==z)))"
              in
           FStar_TypeChecker_Common.NonTrivial uu____637  in
         unify1 (Prims.parse_int "8") uu____628 uu____632 uu____636);
        (let uu____641 = FStar_Main.process_args ()  in
         FStar_All.pipe_right uu____641 (fun a2  -> ()));
        (let uu____656 =
           let uu____663 = FStar_Tests_Pars.tc "fun u x -> u x"  in
           inst (Prims.parse_int "1") uu____663  in
         match uu____656 with
         | (tm1,us) ->
             let sol = FStar_Tests_Pars.tc "fun x -> c_and x x"  in
             (unify_check (Prims.parse_int "9") tm1 sol
                FStar_TypeChecker_Common.Trivial
                (fun uu____681  ->
                   let uu____682 =
                     let uu____684 =
                       let uu____687 = FStar_List.hd us  in norm uu____687
                        in
                     let uu____688 = norm sol  in
                     FStar_Tests_Util.term_eq uu____684 uu____688  in
                   FStar_Tests_Util.always (Prims.parse_int "9") uu____682);
              (let uu____692 =
                 let uu____699 = FStar_Tests_Pars.tc "fun u x -> u x"  in
                 inst (Prims.parse_int "1") uu____699  in
               match uu____692 with
               | (tm2,us1) ->
                   let sol1 = FStar_Tests_Pars.tc "fun x y -> x + y"  in
                   (unify_check (Prims.parse_int "10") tm2 sol1
                      FStar_TypeChecker_Common.Trivial
                      (fun uu____717  ->
                         let uu____718 =
                           let uu____720 =
                             let uu____723 = FStar_List.hd us1  in
                             norm uu____723  in
                           let uu____724 = norm sol1  in
                           FStar_Tests_Util.term_eq uu____720 uu____724  in
                         FStar_Tests_Util.always (Prims.parse_int "10")
                           uu____718);
                    (let tm11 =
                       FStar_Tests_Pars.tc "x:int -> y:int{eq2 y x} -> bool"
                        in
                     let tm21 = FStar_Tests_Pars.tc "x:int -> y:int -> bool"
                        in
                     (let uu____733 =
                        let uu____734 =
                          FStar_Tests_Pars.tc
                            "forall (x:int). (forall (y:int). y==x)"
                           in
                        FStar_TypeChecker_Common.NonTrivial uu____734  in
                      unify1 (Prims.parse_int "11") tm11 tm21 uu____733);
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
                      (let uu____743 =
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
                           let uu____761 =
                             let uu____762 =
                               let uu____765 =
                                 FStar_Syntax_Syntax.bv_to_name q  in
                               [uu____765]  in
                             FStar_Tests_Util.app l uu____762  in
                           norm uu____761  in
                         let l1 =
                           FStar_Tests_Pars.tc "fun (p:unit -> Type0) -> p"
                            in
                         let unit = FStar_Tests_Pars.tc "()"  in
                         let env =
                           let uu____771 = FStar_Tests_Pars.init ()  in
                           let uu____772 =
                             let uu____773 = FStar_Syntax_Syntax.mk_binder x2
                                in
                             let uu____780 =
                               let uu____789 =
                                 FStar_Syntax_Syntax.mk_binder q  in
                               [uu____789]  in
                             uu____773 :: uu____780  in
                           FStar_TypeChecker_Env.push_binders uu____771
                             uu____772
                            in
                         let uu____814 =
                           FStar_TypeChecker_Util.new_implicit_var ""
                             FStar_Range.dummyRange env typ
                            in
                         match uu____814 with
                         | (u_p,uu____837,uu____838) ->
                             let tm23 =
                               let uu____854 =
                                 let uu____857 =
                                   FStar_Tests_Util.app l1 [u_p]  in
                                 norm uu____857  in
                               FStar_Tests_Util.app uu____854 [unit]  in
                             (tm13, tm23)
                          in
                       match uu____743 with
                       | (tm13,tm23) ->
                           (unify1 (Prims.parse_int "13") tm13 tm23
                              FStar_TypeChecker_Common.Trivial;
                            (let uu____875 =
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
                                 let uu____893 =
                                   let uu____894 =
                                     let uu____897 =
                                       FStar_Syntax_Syntax.bv_to_name q  in
                                     [uu____897]  in
                                   FStar_Tests_Util.app l uu____894  in
                                 norm uu____893  in
                               let l1 =
                                 FStar_Tests_Pars.tc
                                   "fun (p:pure_post unit) -> p"
                                  in
                               let unit = FStar_Tests_Pars.tc "()"  in
                               let env =
                                 let uu____903 = FStar_Tests_Pars.init ()  in
                                 let uu____904 =
                                   let uu____905 =
                                     FStar_Syntax_Syntax.mk_binder x2  in
                                   let uu____912 =
                                     let uu____921 =
                                       FStar_Syntax_Syntax.mk_binder q  in
                                     [uu____921]  in
                                   uu____905 :: uu____912  in
                                 FStar_TypeChecker_Env.push_binders uu____903
                                   uu____904
                                  in
                               let uu____946 =
                                 FStar_TypeChecker_Util.new_implicit_var ""
                                   FStar_Range.dummyRange env typ
                                  in
                               match uu____946 with
                               | (u_p,uu____969,uu____970) ->
                                   let tm24 =
                                     let uu____986 =
                                       let uu____989 =
                                         FStar_Tests_Util.app l1 [u_p]  in
                                       norm uu____989  in
                                     FStar_Tests_Util.app uu____986 [unit]
                                      in
                                   (tm14, tm24)
                                in
                             match uu____875 with
                             | (tm14,tm24) ->
                                 (unify1 (Prims.parse_int "14") tm14 tm24
                                    FStar_TypeChecker_Common.Trivial;
                                  FStar_Options.__clear_unit_tests ();
                                  (let uu____1009 = FStar_ST.op_Bang success
                                      in
                                   if uu____1009
                                   then
                                     FStar_Util.print_string "Unifier ok\n"
                                   else ());
                                  FStar_ST.op_Bang success))))))))))))))
  