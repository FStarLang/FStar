open Prims
let (tcenv : unit -> FStar_TypeChecker_Env.env) =
  fun uu____84199  -> FStar_Tests_Pars.init () 
let (guard_to_string :
  FStar_TypeChecker_Common.guard_formula -> Prims.string) =
  fun g  ->
    match g with
    | FStar_TypeChecker_Common.Trivial  -> "trivial"
    | FStar_TypeChecker_Common.NonTrivial f ->
        let uu____84210 = tcenv ()  in
        FStar_TypeChecker_Normalize.term_to_string uu____84210 f
  
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
        let uu____84277 =
          match (g, g') with
          | (FStar_TypeChecker_Common.Trivial
             ,FStar_TypeChecker_Common.Trivial ) -> (true, g, g')
          | (FStar_TypeChecker_Common.NonTrivial
             f,FStar_TypeChecker_Common.NonTrivial f') ->
              let f1 =
                let uu____84297 = tcenv ()  in
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Env.EraseUniverses] uu____84297 f
                 in
              let f'1 =
                let uu____84299 = tcenv ()  in
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Env.EraseUniverses] uu____84299 f'
                 in
              let uu____84300 = FStar_Tests_Util.term_eq f1 f'1  in
              (uu____84300, (FStar_TypeChecker_Common.NonTrivial f1),
                (FStar_TypeChecker_Common.NonTrivial f'1))
          | uu____84303 -> (false, g, g')  in
        match uu____84277 with
        | (b,g1,g'1) ->
            (if Prims.op_Negation b
             then
               (let uu____84317 =
                  let uu____84319 = FStar_Util.string_of_int i  in
                  let uu____84321 = guard_to_string g'1  in
                  let uu____84323 = guard_to_string g1  in
                  FStar_Util.format3
                    "Test %s failed:\n\tExpected guard %s;\n\tGot guard      %s\n"
                    uu____84319 uu____84321 uu____84323
                   in
                FStar_All.pipe_left fail uu____84317)
             else ();
             (let uu____84329 = (FStar_ST.op_Bang success) && b  in
              FStar_ST.op_Colon_Equals success uu____84329))
  
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
            (let uu____84415 = FStar_Util.string_of_int i  in
             FStar_Util.print1 "%s ..." uu____84415);
            (let uu____84419 = FStar_Main.process_args ()  in
             FStar_All.pipe_right uu____84419 (fun a1  -> ()));
            (let uu____84435 = FStar_Syntax_Print.term_to_string x1  in
             let uu____84437 = FStar_Syntax_Print.term_to_string y1  in
             FStar_Util.print2 "Unify %s\nand %s\n" uu____84435 uu____84437);
            (let g =
               let uu____84441 =
                 let uu____84442 =
                   let uu____84443 = tcenv ()  in
                   FStar_TypeChecker_Rel.teq uu____84443 x1 y1  in
                 let uu____84444 =
                   let uu____84449 = tcenv ()  in
                   FStar_TypeChecker_Rel.solve_deferred_constraints
                     uu____84449
                    in
                 FStar_All.pipe_right uu____84442 uu____84444  in
               let uu____84450 =
                 let uu____84455 = tcenv ()  in
                 FStar_TypeChecker_Rel.simplify_guard uu____84455  in
               FStar_All.pipe_right uu____84441 uu____84450  in
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
        (fun uu___783_84480  ->
           match () with
           | () ->
               let g =
                 let uu____84482 =
                   let uu____84483 = tcenv ()  in
                   FStar_TypeChecker_Rel.teq uu____84483 x1 y1  in
                 let uu____84484 =
                   let uu____84489 = tcenv ()  in
                   FStar_TypeChecker_Rel.solve_deferred_constraints
                     uu____84489
                    in
                 FStar_All.pipe_right uu____84482 uu____84484  in
               (match g.FStar_TypeChecker_Env.guard_f with
                | FStar_TypeChecker_Common.Trivial  ->
                    let uu____84490 =
                      let uu____84492 = FStar_Syntax_Print.term_to_string x1
                         in
                      let uu____84494 = FStar_Syntax_Print.term_to_string y1
                         in
                      FStar_Util.format2
                        "%s and %s should not be unifiable\n" uu____84492
                        uu____84494
                       in
                    fail uu____84490
                | FStar_TypeChecker_Common.NonTrivial f ->
                    let uu____84498 = FStar_Syntax_Print.term_to_string x1
                       in
                    let uu____84500 = FStar_Syntax_Print.term_to_string y1
                       in
                    let uu____84502 = FStar_Syntax_Print.term_to_string f  in
                    FStar_Util.print3 "%s and %s are unifiable if %s\n"
                      uu____84498 uu____84500 uu____84502)) ()
      with | FStar_Errors.Error (e,msg,r) -> FStar_Util.print1 "%s\n" msg
  
let (unify' : Prims.string -> Prims.string -> unit) =
  fun x1  ->
    fun y1  ->
      let x2 = FStar_Tests_Pars.pars x1  in
      let y2 = FStar_Tests_Pars.pars y1  in
      let g =
        let uu____84534 =
          let uu____84535 = tcenv ()  in
          FStar_TypeChecker_Rel.teq uu____84535 x2 y2  in
        let uu____84536 =
          let uu____84541 = tcenv ()  in
          FStar_TypeChecker_Rel.solve_deferred_constraints uu____84541  in
        FStar_All.pipe_right uu____84534 uu____84536  in
      let uu____84542 = FStar_Syntax_Print.term_to_string x2  in
      let uu____84544 = FStar_Syntax_Print.term_to_string y2  in
      let uu____84546 = guard_to_string g.FStar_TypeChecker_Env.guard_f  in
      FStar_Util.print3 "%s and %s are unifiable with guard %s\n" uu____84542
        uu____84544 uu____84546
  
let (norm : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____84555 = tcenv ()  in
    FStar_TypeChecker_Normalize.normalize [] uu____84555 t
  
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
          (let uu____84605 =
             let uu____84618 = FStar_Tests_Pars.init ()  in
             FStar_TypeChecker_Util.new_implicit_var ""
               FStar_Range.dummyRange uu____84618 FStar_Syntax_Util.ktype0
              in
           match uu____84605 with
           | (t,uu____84623,uu____84624) ->
               let uu____84637 =
                 let uu____84650 = FStar_Tests_Pars.init ()  in
                 FStar_TypeChecker_Util.new_implicit_var ""
                   FStar_Range.dummyRange uu____84650 t
                  in
               (match uu____84637 with
                | (u,uu____84655,uu____84656) ->
                    aux (u :: out) (n2 - (Prims.parse_int "1"))))
         in
      let us = aux [] n1  in
      let uu____84673 =
        let uu____84674 = FStar_Tests_Util.app tm1 us  in norm uu____84674
         in
      (uu____84673, us)
  
let (run_all : unit -> Prims.bool) =
  fun uu____84683  ->
    FStar_Util.print_string "Testing the unifier\n";
    FStar_Options.__set_unit_tests ();
    (let unify_check n1 x1 y1 g f = unify n1 x1 y1 g f  in
     let unify1 n1 x1 y1 g = unify n1 x1 y1 g (fun uu____84760  -> ())  in
     let int_t = FStar_Tests_Pars.tc "Prims.int"  in
     let x1 =
       let uu____84766 =
         FStar_Syntax_Syntax.gen_bv "x" FStar_Pervasives_Native.None int_t
          in
       FStar_All.pipe_right uu____84766 FStar_Syntax_Syntax.bv_to_name  in
     let y1 =
       let uu____84773 =
         FStar_Syntax_Syntax.gen_bv "y" FStar_Pervasives_Native.None int_t
          in
       FStar_All.pipe_right uu____84773 FStar_Syntax_Syntax.bv_to_name  in
     unify1 (Prims.parse_int "0") x1 x1 FStar_TypeChecker_Common.Trivial;
     (let uu____84780 =
        let uu____84781 =
          FStar_Syntax_Util.mk_eq2 FStar_Syntax_Syntax.U_zero
            FStar_Syntax_Util.t_bool x1 y1
           in
        FStar_TypeChecker_Common.NonTrivial uu____84781  in
      unify1 (Prims.parse_int "1") x1 y1 uu____84780);
     (let id1 = FStar_Tests_Pars.tc "fun x -> x"  in
      (let uu____84786 = FStar_Tests_Util.app id1 [x1]  in
       unify1 (Prims.parse_int "2") x1 uu____84786
         FStar_TypeChecker_Common.Trivial);
      (let id2 = FStar_Tests_Pars.tc "fun x -> x"  in
       unify1 (Prims.parse_int "3") id2 id2 FStar_TypeChecker_Common.Trivial;
       (let id3 = FStar_Tests_Pars.tc "fun x -> x"  in
        let id' = FStar_Tests_Pars.tc "fun y -> y"  in
        unify1 (Prims.parse_int "4") id3 id' FStar_TypeChecker_Common.Trivial;
        (let uu____84801 = FStar_Tests_Pars.tc "fun x y -> x"  in
         let uu____84805 = FStar_Tests_Pars.tc "fun a b -> a"  in
         unify1 (Prims.parse_int "5") uu____84801 uu____84805
           FStar_TypeChecker_Common.Trivial);
        (let uu____84811 = FStar_Tests_Pars.tc "fun x y z -> y"  in
         let uu____84815 = FStar_Tests_Pars.tc "fun a b c -> b"  in
         unify1 (Prims.parse_int "6") uu____84811 uu____84815
           FStar_TypeChecker_Common.Trivial);
        (let uu____84821 = FStar_Tests_Pars.tc "fun (x:int) (y:int) -> y"  in
         let uu____84825 = FStar_Tests_Pars.tc "fun (x:int) (y:int) -> x"  in
         let uu____84829 =
           let uu____84830 =
             FStar_Tests_Pars.tc "(forall (x:int). (forall (y:int). y==x))"
              in
           FStar_TypeChecker_Common.NonTrivial uu____84830  in
         unify1 (Prims.parse_int "7") uu____84821 uu____84825 uu____84829);
        (let uu____84834 =
           FStar_Tests_Pars.tc "fun (x:int) (y:int) (z:int) -> y"  in
         let uu____84838 =
           FStar_Tests_Pars.tc "fun (x:int) (y:int) (z:int) -> z"  in
         let uu____84842 =
           let uu____84843 =
             FStar_Tests_Pars.tc
               "(forall (x:int). (forall (y:int). (forall (z:int). y==z)))"
              in
           FStar_TypeChecker_Common.NonTrivial uu____84843  in
         unify1 (Prims.parse_int "8") uu____84834 uu____84838 uu____84842);
        (let uu____84847 = FStar_Main.process_args ()  in
         FStar_All.pipe_right uu____84847 (fun a2  -> ()));
        (let uu____84862 =
           let uu____84869 = FStar_Tests_Pars.tc "fun u x -> u x"  in
           inst (Prims.parse_int "1") uu____84869  in
         match uu____84862 with
         | (tm1,us) ->
             let sol = FStar_Tests_Pars.tc "fun x -> c_and x x"  in
             (unify_check (Prims.parse_int "9") tm1 sol
                FStar_TypeChecker_Common.Trivial
                (fun uu____84887  ->
                   let uu____84888 =
                     let uu____84890 =
                       let uu____84893 = FStar_List.hd us  in
                       norm uu____84893  in
                     let uu____84894 = norm sol  in
                     FStar_Tests_Util.term_eq uu____84890 uu____84894  in
                   FStar_Tests_Util.always (Prims.parse_int "9") uu____84888);
              (let uu____84898 =
                 let uu____84905 = FStar_Tests_Pars.tc "fun u x -> u x"  in
                 inst (Prims.parse_int "1") uu____84905  in
               match uu____84898 with
               | (tm2,us1) ->
                   let sol1 = FStar_Tests_Pars.tc "fun x y -> x + y"  in
                   (unify_check (Prims.parse_int "10") tm2 sol1
                      FStar_TypeChecker_Common.Trivial
                      (fun uu____84923  ->
                         let uu____84924 =
                           let uu____84926 =
                             let uu____84929 = FStar_List.hd us1  in
                             norm uu____84929  in
                           let uu____84930 = norm sol1  in
                           FStar_Tests_Util.term_eq uu____84926 uu____84930
                            in
                         FStar_Tests_Util.always (Prims.parse_int "10")
                           uu____84924);
                    (let tm11 =
                       FStar_Tests_Pars.tc "x:int -> y:int{eq2 y x} -> bool"
                        in
                     let tm21 = FStar_Tests_Pars.tc "x:int -> y:int -> bool"
                        in
                     (let uu____84939 =
                        let uu____84940 =
                          FStar_Tests_Pars.tc
                            "forall (x:int). (forall (y:int). y==x)"
                           in
                        FStar_TypeChecker_Common.NonTrivial uu____84940  in
                      unify1 (Prims.parse_int "11") tm11 tm21 uu____84939);
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
                      (let uu____84949 =
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
                           let uu____84967 =
                             let uu____84968 =
                               let uu____84971 =
                                 FStar_Syntax_Syntax.bv_to_name q  in
                               [uu____84971]  in
                             FStar_Tests_Util.app l uu____84968  in
                           norm uu____84967  in
                         let l1 =
                           FStar_Tests_Pars.tc "fun (p:unit -> Type0) -> p"
                            in
                         let unit = FStar_Tests_Pars.tc "()"  in
                         let env =
                           let uu____84977 = FStar_Tests_Pars.init ()  in
                           let uu____84978 =
                             let uu____84979 =
                               FStar_Syntax_Syntax.mk_binder x2  in
                             let uu____84986 =
                               let uu____84995 =
                                 FStar_Syntax_Syntax.mk_binder q  in
                               [uu____84995]  in
                             uu____84979 :: uu____84986  in
                           FStar_TypeChecker_Env.push_binders uu____84977
                             uu____84978
                            in
                         let uu____85020 =
                           FStar_TypeChecker_Util.new_implicit_var ""
                             FStar_Range.dummyRange env typ
                            in
                         match uu____85020 with
                         | (u_p,uu____85043,uu____85044) ->
                             let tm23 =
                               let uu____85060 =
                                 let uu____85063 =
                                   FStar_Tests_Util.app l1 [u_p]  in
                                 norm uu____85063  in
                               FStar_Tests_Util.app uu____85060 [unit]  in
                             (tm13, tm23)
                          in
                       match uu____84949 with
                       | (tm13,tm23) ->
                           (unify1 (Prims.parse_int "13") tm13 tm23
                              FStar_TypeChecker_Common.Trivial;
                            (let uu____85081 =
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
                                 let uu____85099 =
                                   let uu____85100 =
                                     let uu____85103 =
                                       FStar_Syntax_Syntax.bv_to_name q  in
                                     [uu____85103]  in
                                   FStar_Tests_Util.app l uu____85100  in
                                 norm uu____85099  in
                               let l1 =
                                 FStar_Tests_Pars.tc
                                   "fun (p:pure_post unit) -> p"
                                  in
                               let unit = FStar_Tests_Pars.tc "()"  in
                               let env =
                                 let uu____85109 = FStar_Tests_Pars.init ()
                                    in
                                 let uu____85110 =
                                   let uu____85111 =
                                     FStar_Syntax_Syntax.mk_binder x2  in
                                   let uu____85118 =
                                     let uu____85127 =
                                       FStar_Syntax_Syntax.mk_binder q  in
                                     [uu____85127]  in
                                   uu____85111 :: uu____85118  in
                                 FStar_TypeChecker_Env.push_binders
                                   uu____85109 uu____85110
                                  in
                               let uu____85152 =
                                 FStar_TypeChecker_Util.new_implicit_var ""
                                   FStar_Range.dummyRange env typ
                                  in
                               match uu____85152 with
                               | (u_p,uu____85175,uu____85176) ->
                                   let tm24 =
                                     let uu____85192 =
                                       let uu____85195 =
                                         FStar_Tests_Util.app l1 [u_p]  in
                                       norm uu____85195  in
                                     FStar_Tests_Util.app uu____85192 [unit]
                                      in
                                   (tm14, tm24)
                                in
                             match uu____85081 with
                             | (tm14,tm24) ->
                                 (unify1 (Prims.parse_int "14") tm14 tm24
                                    FStar_TypeChecker_Common.Trivial;
                                  FStar_Options.__clear_unit_tests ();
                                  (let uu____85215 = FStar_ST.op_Bang success
                                      in
                                   if uu____85215
                                   then
                                     FStar_Util.print_string "Unifier ok\n"
                                   else ());
                                  FStar_ST.op_Bang success))))))))))))))
  