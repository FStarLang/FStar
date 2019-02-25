open Prims
let (tcenv : unit -> FStar_TypeChecker_Env.env) =
  fun uu____84102  -> FStar_Tests_Pars.init () 
let (guard_to_string :
  FStar_TypeChecker_Common.guard_formula -> Prims.string) =
  fun g  ->
    match g with
    | FStar_TypeChecker_Common.Trivial  -> "trivial"
    | FStar_TypeChecker_Common.NonTrivial f ->
        let uu____84113 = tcenv ()  in
        FStar_TypeChecker_Normalize.term_to_string uu____84113 f
  
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
        let uu____84180 =
          match (g, g') with
          | (FStar_TypeChecker_Common.Trivial
             ,FStar_TypeChecker_Common.Trivial ) -> (true, g, g')
          | (FStar_TypeChecker_Common.NonTrivial
             f,FStar_TypeChecker_Common.NonTrivial f') ->
              let f1 =
                let uu____84200 = tcenv ()  in
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Env.EraseUniverses] uu____84200 f
                 in
              let f'1 =
                let uu____84202 = tcenv ()  in
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Env.EraseUniverses] uu____84202 f'
                 in
              let uu____84203 = FStar_Tests_Util.term_eq f1 f'1  in
              (uu____84203, (FStar_TypeChecker_Common.NonTrivial f1),
                (FStar_TypeChecker_Common.NonTrivial f'1))
          | uu____84206 -> (false, g, g')  in
        match uu____84180 with
        | (b,g1,g'1) ->
            (if Prims.op_Negation b
             then
               (let uu____84220 =
                  let uu____84222 = FStar_Util.string_of_int i  in
                  let uu____84224 = guard_to_string g'1  in
                  let uu____84226 = guard_to_string g1  in
                  FStar_Util.format3
                    "Test %s failed:\n\tExpected guard %s;\n\tGot guard      %s\n"
                    uu____84222 uu____84224 uu____84226
                   in
                FStar_All.pipe_left fail uu____84220)
             else ();
             (let uu____84232 = (FStar_ST.op_Bang success) && b  in
              FStar_ST.op_Colon_Equals success uu____84232))
  
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
            (let uu____84318 = FStar_Util.string_of_int i  in
             FStar_Util.print1 "%s ..." uu____84318);
            (let uu____84322 = FStar_Main.process_args ()  in
             FStar_All.pipe_right uu____84322 (fun a1  -> ()));
            (let uu____84338 = FStar_Syntax_Print.term_to_string x1  in
             let uu____84340 = FStar_Syntax_Print.term_to_string y1  in
             FStar_Util.print2 "Unify %s\nand %s\n" uu____84338 uu____84340);
            (let g =
               let uu____84344 =
                 let uu____84345 =
                   let uu____84346 = tcenv ()  in
                   FStar_TypeChecker_Rel.teq uu____84346 x1 y1  in
                 let uu____84347 =
                   let uu____84352 = tcenv ()  in
                   FStar_TypeChecker_Rel.solve_deferred_constraints
                     uu____84352
                    in
                 FStar_All.pipe_right uu____84345 uu____84347  in
               let uu____84353 =
                 let uu____84358 = tcenv ()  in
                 FStar_TypeChecker_Rel.simplify_guard uu____84358  in
               FStar_All.pipe_right uu____84344 uu____84353  in
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
        (fun uu___783_84383  ->
           match () with
           | () ->
               let g =
                 let uu____84385 =
                   let uu____84386 = tcenv ()  in
                   FStar_TypeChecker_Rel.teq uu____84386 x1 y1  in
                 let uu____84387 =
                   let uu____84392 = tcenv ()  in
                   FStar_TypeChecker_Rel.solve_deferred_constraints
                     uu____84392
                    in
                 FStar_All.pipe_right uu____84385 uu____84387  in
               (match g.FStar_TypeChecker_Env.guard_f with
                | FStar_TypeChecker_Common.Trivial  ->
                    let uu____84393 =
                      let uu____84395 = FStar_Syntax_Print.term_to_string x1
                         in
                      let uu____84397 = FStar_Syntax_Print.term_to_string y1
                         in
                      FStar_Util.format2
                        "%s and %s should not be unifiable\n" uu____84395
                        uu____84397
                       in
                    fail uu____84393
                | FStar_TypeChecker_Common.NonTrivial f ->
                    let uu____84401 = FStar_Syntax_Print.term_to_string x1
                       in
                    let uu____84403 = FStar_Syntax_Print.term_to_string y1
                       in
                    let uu____84405 = FStar_Syntax_Print.term_to_string f  in
                    FStar_Util.print3 "%s and %s are unifiable if %s\n"
                      uu____84401 uu____84403 uu____84405)) ()
      with | FStar_Errors.Error (e,msg,r) -> FStar_Util.print1 "%s\n" msg
  
let (unify' : Prims.string -> Prims.string -> unit) =
  fun x1  ->
    fun y1  ->
      let x2 = FStar_Tests_Pars.pars x1  in
      let y2 = FStar_Tests_Pars.pars y1  in
      let g =
        let uu____84437 =
          let uu____84438 = tcenv ()  in
          FStar_TypeChecker_Rel.teq uu____84438 x2 y2  in
        let uu____84439 =
          let uu____84444 = tcenv ()  in
          FStar_TypeChecker_Rel.solve_deferred_constraints uu____84444  in
        FStar_All.pipe_right uu____84437 uu____84439  in
      let uu____84445 = FStar_Syntax_Print.term_to_string x2  in
      let uu____84447 = FStar_Syntax_Print.term_to_string y2  in
      let uu____84449 = guard_to_string g.FStar_TypeChecker_Env.guard_f  in
      FStar_Util.print3 "%s and %s are unifiable with guard %s\n" uu____84445
        uu____84447 uu____84449
  
let (norm : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____84458 = tcenv ()  in
    FStar_TypeChecker_Normalize.normalize [] uu____84458 t
  
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
          (let uu____84508 =
             let uu____84521 = FStar_Tests_Pars.init ()  in
             FStar_TypeChecker_Util.new_implicit_var ""
               FStar_Range.dummyRange uu____84521 FStar_Syntax_Util.ktype0
              in
           match uu____84508 with
           | (t,uu____84526,uu____84527) ->
               let uu____84540 =
                 let uu____84553 = FStar_Tests_Pars.init ()  in
                 FStar_TypeChecker_Util.new_implicit_var ""
                   FStar_Range.dummyRange uu____84553 t
                  in
               (match uu____84540 with
                | (u,uu____84558,uu____84559) ->
                    aux (u :: out) (n2 - (Prims.parse_int "1"))))
         in
      let us = aux [] n1  in
      let uu____84576 =
        let uu____84577 = FStar_Tests_Util.app tm1 us  in norm uu____84577
         in
      (uu____84576, us)
  
let (run_all : unit -> Prims.bool) =
  fun uu____84586  ->
    FStar_Util.print_string "Testing the unifier\n";
    FStar_Options.__set_unit_tests ();
    (let unify_check n1 x1 y1 g f = unify n1 x1 y1 g f  in
     let unify1 n1 x1 y1 g = unify n1 x1 y1 g (fun uu____84663  -> ())  in
     let int_t = FStar_Tests_Pars.tc "Prims.int"  in
     let x1 =
       let uu____84669 =
         FStar_Syntax_Syntax.gen_bv "x" FStar_Pervasives_Native.None int_t
          in
       FStar_All.pipe_right uu____84669 FStar_Syntax_Syntax.bv_to_name  in
     let y1 =
       let uu____84676 =
         FStar_Syntax_Syntax.gen_bv "y" FStar_Pervasives_Native.None int_t
          in
       FStar_All.pipe_right uu____84676 FStar_Syntax_Syntax.bv_to_name  in
     unify1 (Prims.parse_int "0") x1 x1 FStar_TypeChecker_Common.Trivial;
     (let uu____84683 =
        let uu____84684 =
          FStar_Syntax_Util.mk_eq2 FStar_Syntax_Syntax.U_zero
            FStar_Syntax_Util.t_bool x1 y1
           in
        FStar_TypeChecker_Common.NonTrivial uu____84684  in
      unify1 (Prims.parse_int "1") x1 y1 uu____84683);
     (let id1 = FStar_Tests_Pars.tc "fun x -> x"  in
      (let uu____84689 = FStar_Tests_Util.app id1 [x1]  in
       unify1 (Prims.parse_int "2") x1 uu____84689
         FStar_TypeChecker_Common.Trivial);
      (let id2 = FStar_Tests_Pars.tc "fun x -> x"  in
       unify1 (Prims.parse_int "3") id2 id2 FStar_TypeChecker_Common.Trivial;
       (let id3 = FStar_Tests_Pars.tc "fun x -> x"  in
        let id' = FStar_Tests_Pars.tc "fun y -> y"  in
        unify1 (Prims.parse_int "4") id3 id' FStar_TypeChecker_Common.Trivial;
        (let uu____84704 = FStar_Tests_Pars.tc "fun x y -> x"  in
         let uu____84708 = FStar_Tests_Pars.tc "fun a b -> a"  in
         unify1 (Prims.parse_int "5") uu____84704 uu____84708
           FStar_TypeChecker_Common.Trivial);
        (let uu____84714 = FStar_Tests_Pars.tc "fun x y z -> y"  in
         let uu____84718 = FStar_Tests_Pars.tc "fun a b c -> b"  in
         unify1 (Prims.parse_int "6") uu____84714 uu____84718
           FStar_TypeChecker_Common.Trivial);
        (let uu____84724 = FStar_Tests_Pars.tc "fun (x:int) (y:int) -> y"  in
         let uu____84728 = FStar_Tests_Pars.tc "fun (x:int) (y:int) -> x"  in
         let uu____84732 =
           let uu____84733 =
             FStar_Tests_Pars.tc "(forall (x:int). (forall (y:int). y==x))"
              in
           FStar_TypeChecker_Common.NonTrivial uu____84733  in
         unify1 (Prims.parse_int "7") uu____84724 uu____84728 uu____84732);
        (let uu____84737 =
           FStar_Tests_Pars.tc "fun (x:int) (y:int) (z:int) -> y"  in
         let uu____84741 =
           FStar_Tests_Pars.tc "fun (x:int) (y:int) (z:int) -> z"  in
         let uu____84745 =
           let uu____84746 =
             FStar_Tests_Pars.tc
               "(forall (x:int). (forall (y:int). (forall (z:int). y==z)))"
              in
           FStar_TypeChecker_Common.NonTrivial uu____84746  in
         unify1 (Prims.parse_int "8") uu____84737 uu____84741 uu____84745);
        (let uu____84750 = FStar_Main.process_args ()  in
         FStar_All.pipe_right uu____84750 (fun a2  -> ()));
        (let uu____84765 =
           let uu____84772 = FStar_Tests_Pars.tc "fun u x -> u x"  in
           inst (Prims.parse_int "1") uu____84772  in
         match uu____84765 with
         | (tm1,us) ->
             let sol = FStar_Tests_Pars.tc "fun x -> c_and x x"  in
             (unify_check (Prims.parse_int "9") tm1 sol
                FStar_TypeChecker_Common.Trivial
                (fun uu____84790  ->
                   let uu____84791 =
                     let uu____84793 =
                       let uu____84796 = FStar_List.hd us  in
                       norm uu____84796  in
                     let uu____84797 = norm sol  in
                     FStar_Tests_Util.term_eq uu____84793 uu____84797  in
                   FStar_Tests_Util.always (Prims.parse_int "9") uu____84791);
              (let uu____84801 =
                 let uu____84808 = FStar_Tests_Pars.tc "fun u x -> u x"  in
                 inst (Prims.parse_int "1") uu____84808  in
               match uu____84801 with
               | (tm2,us1) ->
                   let sol1 = FStar_Tests_Pars.tc "fun x y -> x + y"  in
                   (unify_check (Prims.parse_int "10") tm2 sol1
                      FStar_TypeChecker_Common.Trivial
                      (fun uu____84826  ->
                         let uu____84827 =
                           let uu____84829 =
                             let uu____84832 = FStar_List.hd us1  in
                             norm uu____84832  in
                           let uu____84833 = norm sol1  in
                           FStar_Tests_Util.term_eq uu____84829 uu____84833
                            in
                         FStar_Tests_Util.always (Prims.parse_int "10")
                           uu____84827);
                    (let tm11 =
                       FStar_Tests_Pars.tc "x:int -> y:int{eq2 y x} -> bool"
                        in
                     let tm21 = FStar_Tests_Pars.tc "x:int -> y:int -> bool"
                        in
                     (let uu____84842 =
                        let uu____84843 =
                          FStar_Tests_Pars.tc
                            "forall (x:int). (forall (y:int). y==x)"
                           in
                        FStar_TypeChecker_Common.NonTrivial uu____84843  in
                      unify1 (Prims.parse_int "11") tm11 tm21 uu____84842);
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
                      (let uu____84852 =
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
                           let uu____84870 =
                             let uu____84871 =
                               let uu____84874 =
                                 FStar_Syntax_Syntax.bv_to_name q  in
                               [uu____84874]  in
                             FStar_Tests_Util.app l uu____84871  in
                           norm uu____84870  in
                         let l1 =
                           FStar_Tests_Pars.tc "fun (p:unit -> Type0) -> p"
                            in
                         let unit = FStar_Tests_Pars.tc "()"  in
                         let env =
                           let uu____84880 = FStar_Tests_Pars.init ()  in
                           let uu____84881 =
                             let uu____84882 =
                               FStar_Syntax_Syntax.mk_binder x2  in
                             let uu____84889 =
                               let uu____84898 =
                                 FStar_Syntax_Syntax.mk_binder q  in
                               [uu____84898]  in
                             uu____84882 :: uu____84889  in
                           FStar_TypeChecker_Env.push_binders uu____84880
                             uu____84881
                            in
                         let uu____84923 =
                           FStar_TypeChecker_Util.new_implicit_var ""
                             FStar_Range.dummyRange env typ
                            in
                         match uu____84923 with
                         | (u_p,uu____84946,uu____84947) ->
                             let tm23 =
                               let uu____84963 =
                                 let uu____84966 =
                                   FStar_Tests_Util.app l1 [u_p]  in
                                 norm uu____84966  in
                               FStar_Tests_Util.app uu____84963 [unit]  in
                             (tm13, tm23)
                          in
                       match uu____84852 with
                       | (tm13,tm23) ->
                           (unify1 (Prims.parse_int "13") tm13 tm23
                              FStar_TypeChecker_Common.Trivial;
                            (let uu____84984 =
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
                                 let uu____85002 =
                                   let uu____85003 =
                                     let uu____85006 =
                                       FStar_Syntax_Syntax.bv_to_name q  in
                                     [uu____85006]  in
                                   FStar_Tests_Util.app l uu____85003  in
                                 norm uu____85002  in
                               let l1 =
                                 FStar_Tests_Pars.tc
                                   "fun (p:pure_post unit) -> p"
                                  in
                               let unit = FStar_Tests_Pars.tc "()"  in
                               let env =
                                 let uu____85012 = FStar_Tests_Pars.init ()
                                    in
                                 let uu____85013 =
                                   let uu____85014 =
                                     FStar_Syntax_Syntax.mk_binder x2  in
                                   let uu____85021 =
                                     let uu____85030 =
                                       FStar_Syntax_Syntax.mk_binder q  in
                                     [uu____85030]  in
                                   uu____85014 :: uu____85021  in
                                 FStar_TypeChecker_Env.push_binders
                                   uu____85012 uu____85013
                                  in
                               let uu____85055 =
                                 FStar_TypeChecker_Util.new_implicit_var ""
                                   FStar_Range.dummyRange env typ
                                  in
                               match uu____85055 with
                               | (u_p,uu____85078,uu____85079) ->
                                   let tm24 =
                                     let uu____85095 =
                                       let uu____85098 =
                                         FStar_Tests_Util.app l1 [u_p]  in
                                       norm uu____85098  in
                                     FStar_Tests_Util.app uu____85095 [unit]
                                      in
                                   (tm14, tm24)
                                in
                             match uu____84984 with
                             | (tm14,tm24) ->
                                 (unify1 (Prims.parse_int "14") tm14 tm24
                                    FStar_TypeChecker_Common.Trivial;
                                  FStar_Options.__clear_unit_tests ();
                                  (let uu____85118 = FStar_ST.op_Bang success
                                      in
                                   if uu____85118
                                   then
                                     FStar_Util.print_string "Unifier ok\n"
                                   else ());
                                  FStar_ST.op_Bang success))))))))))))))
  