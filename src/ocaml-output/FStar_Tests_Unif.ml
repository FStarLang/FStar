open Prims
let (tcenv : unit -> FStar_TypeChecker_Env.env) =
  fun uu____84189  -> FStar_Tests_Pars.init () 
let (guard_to_string :
  FStar_TypeChecker_Common.guard_formula -> Prims.string) =
  fun g  ->
    match g with
    | FStar_TypeChecker_Common.Trivial  -> "trivial"
    | FStar_TypeChecker_Common.NonTrivial f ->
        let uu____84200 = tcenv ()  in
        FStar_TypeChecker_Normalize.term_to_string uu____84200 f
  
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
        let uu____84267 =
          match (g, g') with
          | (FStar_TypeChecker_Common.Trivial
             ,FStar_TypeChecker_Common.Trivial ) -> (true, g, g')
          | (FStar_TypeChecker_Common.NonTrivial
             f,FStar_TypeChecker_Common.NonTrivial f') ->
              let f1 =
                let uu____84287 = tcenv ()  in
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Env.EraseUniverses] uu____84287 f
                 in
              let f'1 =
                let uu____84289 = tcenv ()  in
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Env.EraseUniverses] uu____84289 f'
                 in
              let uu____84290 = FStar_Tests_Util.term_eq f1 f'1  in
              (uu____84290, (FStar_TypeChecker_Common.NonTrivial f1),
                (FStar_TypeChecker_Common.NonTrivial f'1))
          | uu____84293 -> (false, g, g')  in
        match uu____84267 with
        | (b,g1,g'1) ->
            (if Prims.op_Negation b
             then
               (let uu____84307 =
                  let uu____84309 = FStar_Util.string_of_int i  in
                  let uu____84311 = guard_to_string g'1  in
                  let uu____84313 = guard_to_string g1  in
                  FStar_Util.format3
                    "Test %s failed:\n\tExpected guard %s;\n\tGot guard      %s\n"
                    uu____84309 uu____84311 uu____84313
                   in
                FStar_All.pipe_left fail uu____84307)
             else ();
             (let uu____84319 = (FStar_ST.op_Bang success) && b  in
              FStar_ST.op_Colon_Equals success uu____84319))
  
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
            (let uu____84405 = FStar_Util.string_of_int i  in
             FStar_Util.print1 "%s ..." uu____84405);
            (let uu____84409 = FStar_Main.process_args ()  in
             FStar_All.pipe_right uu____84409 (fun a1  -> ()));
            (let uu____84425 = FStar_Syntax_Print.term_to_string x1  in
             let uu____84427 = FStar_Syntax_Print.term_to_string y1  in
             FStar_Util.print2 "Unify %s\nand %s\n" uu____84425 uu____84427);
            (let g =
               let uu____84431 =
                 let uu____84432 =
                   let uu____84433 = tcenv ()  in
                   FStar_TypeChecker_Rel.teq uu____84433 x1 y1  in
                 let uu____84434 =
                   let uu____84439 = tcenv ()  in
                   FStar_TypeChecker_Rel.solve_deferred_constraints
                     uu____84439
                    in
                 FStar_All.pipe_right uu____84432 uu____84434  in
               let uu____84440 =
                 let uu____84445 = tcenv ()  in
                 FStar_TypeChecker_Rel.simplify_guard uu____84445  in
               FStar_All.pipe_right uu____84431 uu____84440  in
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
        (fun uu___783_84470  ->
           match () with
           | () ->
               let g =
                 let uu____84472 =
                   let uu____84473 = tcenv ()  in
                   FStar_TypeChecker_Rel.teq uu____84473 x1 y1  in
                 let uu____84474 =
                   let uu____84479 = tcenv ()  in
                   FStar_TypeChecker_Rel.solve_deferred_constraints
                     uu____84479
                    in
                 FStar_All.pipe_right uu____84472 uu____84474  in
               (match g.FStar_TypeChecker_Env.guard_f with
                | FStar_TypeChecker_Common.Trivial  ->
                    let uu____84480 =
                      let uu____84482 = FStar_Syntax_Print.term_to_string x1
                         in
                      let uu____84484 = FStar_Syntax_Print.term_to_string y1
                         in
                      FStar_Util.format2
                        "%s and %s should not be unifiable\n" uu____84482
                        uu____84484
                       in
                    fail uu____84480
                | FStar_TypeChecker_Common.NonTrivial f ->
                    let uu____84488 = FStar_Syntax_Print.term_to_string x1
                       in
                    let uu____84490 = FStar_Syntax_Print.term_to_string y1
                       in
                    let uu____84492 = FStar_Syntax_Print.term_to_string f  in
                    FStar_Util.print3 "%s and %s are unifiable if %s\n"
                      uu____84488 uu____84490 uu____84492)) ()
      with | FStar_Errors.Error (e,msg,r) -> FStar_Util.print1 "%s\n" msg
  
let (unify' : Prims.string -> Prims.string -> unit) =
  fun x1  ->
    fun y1  ->
      let x2 = FStar_Tests_Pars.pars x1  in
      let y2 = FStar_Tests_Pars.pars y1  in
      let g =
        let uu____84524 =
          let uu____84525 = tcenv ()  in
          FStar_TypeChecker_Rel.teq uu____84525 x2 y2  in
        let uu____84526 =
          let uu____84531 = tcenv ()  in
          FStar_TypeChecker_Rel.solve_deferred_constraints uu____84531  in
        FStar_All.pipe_right uu____84524 uu____84526  in
      let uu____84532 = FStar_Syntax_Print.term_to_string x2  in
      let uu____84534 = FStar_Syntax_Print.term_to_string y2  in
      let uu____84536 = guard_to_string g.FStar_TypeChecker_Env.guard_f  in
      FStar_Util.print3 "%s and %s are unifiable with guard %s\n" uu____84532
        uu____84534 uu____84536
  
let (norm : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____84545 = tcenv ()  in
    FStar_TypeChecker_Normalize.normalize [] uu____84545 t
  
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
          (let uu____84595 =
             let uu____84608 = FStar_Tests_Pars.init ()  in
             FStar_TypeChecker_Util.new_implicit_var ""
               FStar_Range.dummyRange uu____84608 FStar_Syntax_Util.ktype0
              in
           match uu____84595 with
           | (t,uu____84613,uu____84614) ->
               let uu____84627 =
                 let uu____84640 = FStar_Tests_Pars.init ()  in
                 FStar_TypeChecker_Util.new_implicit_var ""
                   FStar_Range.dummyRange uu____84640 t
                  in
               (match uu____84627 with
                | (u,uu____84645,uu____84646) ->
                    aux (u :: out) (n2 - (Prims.parse_int "1"))))
         in
      let us = aux [] n1  in
      let uu____84663 =
        let uu____84664 = FStar_Tests_Util.app tm1 us  in norm uu____84664
         in
      (uu____84663, us)
  
let (run_all : unit -> Prims.bool) =
  fun uu____84673  ->
    FStar_Util.print_string "Testing the unifier\n";
    FStar_Options.__set_unit_tests ();
    (let unify_check n1 x1 y1 g f = unify n1 x1 y1 g f  in
     let unify1 n1 x1 y1 g = unify n1 x1 y1 g (fun uu____84750  -> ())  in
     let int_t = FStar_Tests_Pars.tc "Prims.int"  in
     let x1 =
       let uu____84756 =
         FStar_Syntax_Syntax.gen_bv "x" FStar_Pervasives_Native.None int_t
          in
       FStar_All.pipe_right uu____84756 FStar_Syntax_Syntax.bv_to_name  in
     let y1 =
       let uu____84763 =
         FStar_Syntax_Syntax.gen_bv "y" FStar_Pervasives_Native.None int_t
          in
       FStar_All.pipe_right uu____84763 FStar_Syntax_Syntax.bv_to_name  in
     unify1 (Prims.parse_int "0") x1 x1 FStar_TypeChecker_Common.Trivial;
     (let uu____84770 =
        let uu____84771 =
          FStar_Syntax_Util.mk_eq2 FStar_Syntax_Syntax.U_zero
            FStar_Syntax_Util.t_bool x1 y1
           in
        FStar_TypeChecker_Common.NonTrivial uu____84771  in
      unify1 (Prims.parse_int "1") x1 y1 uu____84770);
     (let id1 = FStar_Tests_Pars.tc "fun x -> x"  in
      (let uu____84776 = FStar_Tests_Util.app id1 [x1]  in
       unify1 (Prims.parse_int "2") x1 uu____84776
         FStar_TypeChecker_Common.Trivial);
      (let id2 = FStar_Tests_Pars.tc "fun x -> x"  in
       unify1 (Prims.parse_int "3") id2 id2 FStar_TypeChecker_Common.Trivial;
       (let id3 = FStar_Tests_Pars.tc "fun x -> x"  in
        let id' = FStar_Tests_Pars.tc "fun y -> y"  in
        unify1 (Prims.parse_int "4") id3 id' FStar_TypeChecker_Common.Trivial;
        (let uu____84791 = FStar_Tests_Pars.tc "fun x y -> x"  in
         let uu____84795 = FStar_Tests_Pars.tc "fun a b -> a"  in
         unify1 (Prims.parse_int "5") uu____84791 uu____84795
           FStar_TypeChecker_Common.Trivial);
        (let uu____84801 = FStar_Tests_Pars.tc "fun x y z -> y"  in
         let uu____84805 = FStar_Tests_Pars.tc "fun a b c -> b"  in
         unify1 (Prims.parse_int "6") uu____84801 uu____84805
           FStar_TypeChecker_Common.Trivial);
        (let uu____84811 = FStar_Tests_Pars.tc "fun (x:int) (y:int) -> y"  in
         let uu____84815 = FStar_Tests_Pars.tc "fun (x:int) (y:int) -> x"  in
         let uu____84819 =
           let uu____84820 =
             FStar_Tests_Pars.tc "(forall (x:int). (forall (y:int). y==x))"
              in
           FStar_TypeChecker_Common.NonTrivial uu____84820  in
         unify1 (Prims.parse_int "7") uu____84811 uu____84815 uu____84819);
        (let uu____84824 =
           FStar_Tests_Pars.tc "fun (x:int) (y:int) (z:int) -> y"  in
         let uu____84828 =
           FStar_Tests_Pars.tc "fun (x:int) (y:int) (z:int) -> z"  in
         let uu____84832 =
           let uu____84833 =
             FStar_Tests_Pars.tc
               "(forall (x:int). (forall (y:int). (forall (z:int). y==z)))"
              in
           FStar_TypeChecker_Common.NonTrivial uu____84833  in
         unify1 (Prims.parse_int "8") uu____84824 uu____84828 uu____84832);
        (let uu____84837 = FStar_Main.process_args ()  in
         FStar_All.pipe_right uu____84837 (fun a2  -> ()));
        (let uu____84852 =
           let uu____84859 = FStar_Tests_Pars.tc "fun u x -> u x"  in
           inst (Prims.parse_int "1") uu____84859  in
         match uu____84852 with
         | (tm1,us) ->
             let sol = FStar_Tests_Pars.tc "fun x -> c_and x x"  in
             (unify_check (Prims.parse_int "9") tm1 sol
                FStar_TypeChecker_Common.Trivial
                (fun uu____84877  ->
                   let uu____84878 =
                     let uu____84880 =
                       let uu____84883 = FStar_List.hd us  in
                       norm uu____84883  in
                     let uu____84884 = norm sol  in
                     FStar_Tests_Util.term_eq uu____84880 uu____84884  in
                   FStar_Tests_Util.always (Prims.parse_int "9") uu____84878);
              (let uu____84888 =
                 let uu____84895 = FStar_Tests_Pars.tc "fun u x -> u x"  in
                 inst (Prims.parse_int "1") uu____84895  in
               match uu____84888 with
               | (tm2,us1) ->
                   let sol1 = FStar_Tests_Pars.tc "fun x y -> x + y"  in
                   (unify_check (Prims.parse_int "10") tm2 sol1
                      FStar_TypeChecker_Common.Trivial
                      (fun uu____84913  ->
                         let uu____84914 =
                           let uu____84916 =
                             let uu____84919 = FStar_List.hd us1  in
                             norm uu____84919  in
                           let uu____84920 = norm sol1  in
                           FStar_Tests_Util.term_eq uu____84916 uu____84920
                            in
                         FStar_Tests_Util.always (Prims.parse_int "10")
                           uu____84914);
                    (let tm11 =
                       FStar_Tests_Pars.tc "x:int -> y:int{eq2 y x} -> bool"
                        in
                     let tm21 = FStar_Tests_Pars.tc "x:int -> y:int -> bool"
                        in
                     (let uu____84929 =
                        let uu____84930 =
                          FStar_Tests_Pars.tc
                            "forall (x:int). (forall (y:int). y==x)"
                           in
                        FStar_TypeChecker_Common.NonTrivial uu____84930  in
                      unify1 (Prims.parse_int "11") tm11 tm21 uu____84929);
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
                      (let uu____84939 =
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
                           let uu____84957 =
                             let uu____84958 =
                               let uu____84961 =
                                 FStar_Syntax_Syntax.bv_to_name q  in
                               [uu____84961]  in
                             FStar_Tests_Util.app l uu____84958  in
                           norm uu____84957  in
                         let l1 =
                           FStar_Tests_Pars.tc "fun (p:unit -> Type0) -> p"
                            in
                         let unit = FStar_Tests_Pars.tc "()"  in
                         let env =
                           let uu____84967 = FStar_Tests_Pars.init ()  in
                           let uu____84968 =
                             let uu____84969 =
                               FStar_Syntax_Syntax.mk_binder x2  in
                             let uu____84976 =
                               let uu____84985 =
                                 FStar_Syntax_Syntax.mk_binder q  in
                               [uu____84985]  in
                             uu____84969 :: uu____84976  in
                           FStar_TypeChecker_Env.push_binders uu____84967
                             uu____84968
                            in
                         let uu____85010 =
                           FStar_TypeChecker_Util.new_implicit_var ""
                             FStar_Range.dummyRange env typ
                            in
                         match uu____85010 with
                         | (u_p,uu____85033,uu____85034) ->
                             let tm23 =
                               let uu____85050 =
                                 let uu____85053 =
                                   FStar_Tests_Util.app l1 [u_p]  in
                                 norm uu____85053  in
                               FStar_Tests_Util.app uu____85050 [unit]  in
                             (tm13, tm23)
                          in
                       match uu____84939 with
                       | (tm13,tm23) ->
                           (unify1 (Prims.parse_int "13") tm13 tm23
                              FStar_TypeChecker_Common.Trivial;
                            (let uu____85071 =
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
                                 let uu____85089 =
                                   let uu____85090 =
                                     let uu____85093 =
                                       FStar_Syntax_Syntax.bv_to_name q  in
                                     [uu____85093]  in
                                   FStar_Tests_Util.app l uu____85090  in
                                 norm uu____85089  in
                               let l1 =
                                 FStar_Tests_Pars.tc
                                   "fun (p:pure_post unit) -> p"
                                  in
                               let unit = FStar_Tests_Pars.tc "()"  in
                               let env =
                                 let uu____85099 = FStar_Tests_Pars.init ()
                                    in
                                 let uu____85100 =
                                   let uu____85101 =
                                     FStar_Syntax_Syntax.mk_binder x2  in
                                   let uu____85108 =
                                     let uu____85117 =
                                       FStar_Syntax_Syntax.mk_binder q  in
                                     [uu____85117]  in
                                   uu____85101 :: uu____85108  in
                                 FStar_TypeChecker_Env.push_binders
                                   uu____85099 uu____85100
                                  in
                               let uu____85142 =
                                 FStar_TypeChecker_Util.new_implicit_var ""
                                   FStar_Range.dummyRange env typ
                                  in
                               match uu____85142 with
                               | (u_p,uu____85165,uu____85166) ->
                                   let tm24 =
                                     let uu____85182 =
                                       let uu____85185 =
                                         FStar_Tests_Util.app l1 [u_p]  in
                                       norm uu____85185  in
                                     FStar_Tests_Util.app uu____85182 [unit]
                                      in
                                   (tm14, tm24)
                                in
                             match uu____85071 with
                             | (tm14,tm24) ->
                                 (unify1 (Prims.parse_int "14") tm14 tm24
                                    FStar_TypeChecker_Common.Trivial;
                                  FStar_Options.__clear_unit_tests ();
                                  (let uu____85205 = FStar_ST.op_Bang success
                                      in
                                   if uu____85205
                                   then
                                     FStar_Util.print_string "Unifier ok\n"
                                   else ());
                                  FStar_ST.op_Bang success))))))))))))))
  