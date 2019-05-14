open Prims
let (tcenv : unit -> FStar_TypeChecker_Env.env) =
  fun uu____58  -> FStar_Tests_Pars.init () 
let (guard_to_string :
  FStar_TypeChecker_Common.guard_formula -> Prims.string) =
  fun g  ->
    match g with
    | FStar_TypeChecker_Common.Trivial  -> "trivial"
    | FStar_TypeChecker_Common.NonTrivial f ->
        let uu____73 = tcenv ()  in
        FStar_TypeChecker_Normalize.term_to_string uu____73 f
  
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
        let uu____237 =
          match (g, g') with
          | (FStar_TypeChecker_Common.Trivial
             ,FStar_TypeChecker_Common.Trivial ) -> (true, g, g')
          | (FStar_TypeChecker_Common.NonTrivial
             f,FStar_TypeChecker_Common.NonTrivial f') ->
              let f1 =
                let uu____273 = tcenv ()  in
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Env.EraseUniverses] uu____273 f
                 in
              let f'1 =
                let uu____391 = tcenv ()  in
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Env.EraseUniverses] uu____391 f'
                 in
              let uu____500 = FStar_Tests_Util.term_eq f1 f'1  in
              (uu____500, (FStar_TypeChecker_Common.NonTrivial f1),
                (FStar_TypeChecker_Common.NonTrivial f'1))
          | uu____503 -> (false, g, g')  in
        match uu____237 with
        | (b,g1,g'1) ->
            (if Prims.op_Negation b
             then
               (let uu____517 =
                  let uu____519 = FStar_Util.string_of_int i  in
                  let uu____521 = guard_to_string g'1  in
                  let uu____523 = guard_to_string g1  in
                  FStar_Util.format3
                    "Test %s failed:\n\tExpected guard %s;\n\tGot guard      %s\n"
                    uu____519 uu____521 uu____523
                   in
                FStar_All.pipe_left fail uu____517)
             else ();
             (let uu____529 = (FStar_ST.op_Bang success) && b  in
              FStar_ST.op_Colon_Equals success uu____529))
  
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
            (let uu____631 = FStar_Util.string_of_int i  in
             FStar_Util.print1 "%s ..." uu____631);
            (let uu____635 = FStar_Main.process_args ()  in
             FStar_All.pipe_right uu____635 (fun a1  -> ()));
            (let uu____651 = FStar_Syntax_Print.term_to_string x1  in
             let uu____653 = FStar_Syntax_Print.term_to_string y1  in
             FStar_Util.print2 "Unify %s\nand %s\n" uu____651 uu____653);
            (let g =
               let uu____665 =
                 let uu____674 =
                   let uu____683 = tcenv ()  in
                   FStar_TypeChecker_Rel.teq uu____683 x1 y1  in
                 let uu____792 =
                   let uu____805 = tcenv ()  in
                   FStar_TypeChecker_Rel.solve_deferred_constraints uu____805
                    in
                 FStar_All.pipe_right uu____674 uu____792  in
               let uu____922 =
                 let uu____935 = tcenv ()  in
                 FStar_TypeChecker_Rel.simplify_guard uu____935  in
               FStar_All.pipe_right uu____665 uu____922  in
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
        (fun uu___41_1092  ->
           match () with
           | () ->
               let g =
                 let uu____1102 =
                   let uu____1111 = tcenv ()  in
                   FStar_TypeChecker_Rel.teq uu____1111 x1 y1  in
                 let uu____1220 =
                   let uu____1233 = tcenv ()  in
                   FStar_TypeChecker_Rel.solve_deferred_constraints
                     uu____1233
                    in
                 FStar_All.pipe_right uu____1102 uu____1220  in
               (match g.FStar_TypeChecker_Env.guard_f with
                | FStar_TypeChecker_Common.Trivial  ->
                    let uu____1350 =
                      let uu____1352 = FStar_Syntax_Print.term_to_string x1
                         in
                      let uu____1354 = FStar_Syntax_Print.term_to_string y1
                         in
                      FStar_Util.format2
                        "%s and %s should not be unifiable\n" uu____1352
                        uu____1354
                       in
                    fail uu____1350
                | FStar_TypeChecker_Common.NonTrivial f ->
                    let uu____1362 = FStar_Syntax_Print.term_to_string x1  in
                    let uu____1364 = FStar_Syntax_Print.term_to_string y1  in
                    let uu____1366 = FStar_Syntax_Print.term_to_string f  in
                    FStar_Util.print3 "%s and %s are unifiable if %s\n"
                      uu____1362 uu____1364 uu____1366)) ()
      with | FStar_Errors.Error (e,msg,r) -> FStar_Util.print1 "%s\n" msg
  
let (unify' : Prims.string -> Prims.string -> unit) =
  fun x1  ->
    fun y1  ->
      let x2 = FStar_Tests_Pars.pars x1  in
      let y2 = FStar_Tests_Pars.pars y1  in
      let g =
        let uu____1422 =
          let uu____1431 = tcenv ()  in
          FStar_TypeChecker_Rel.teq uu____1431 x2 y2  in
        let uu____1540 =
          let uu____1553 = tcenv ()  in
          FStar_TypeChecker_Rel.solve_deferred_constraints uu____1553  in
        FStar_All.pipe_right uu____1422 uu____1540  in
      let uu____1670 = FStar_Syntax_Print.term_to_string x2  in
      let uu____1672 = FStar_Syntax_Print.term_to_string y2  in
      let uu____1674 = guard_to_string g.FStar_TypeChecker_Env.guard_f  in
      FStar_Util.print3 "%s and %s are unifiable with guard %s\n" uu____1670
        uu____1672 uu____1674
  
let (norm : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____1695 = tcenv ()  in
    FStar_TypeChecker_Normalize.normalize [] uu____1695 t
  
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
          (let uu____1885 =
             let uu____1914 = FStar_Tests_Pars.init ()  in
             FStar_TypeChecker_Util.new_implicit_var ""
               FStar_Range.dummyRange uu____1914 FStar_Syntax_Util.ktype0
              in
           match uu____1885 with
           | (t,uu____2031,uu____2032) ->
               let uu____2077 =
                 let uu____2106 = FStar_Tests_Pars.init ()  in
                 FStar_TypeChecker_Util.new_implicit_var ""
                   FStar_Range.dummyRange uu____2106 t
                  in
               (match uu____2077 with
                | (u,uu____2223,uu____2224) ->
                    aux (u :: out) (n2 - (Prims.parse_int "1"))))
         in
      let us = aux [] n1  in
      let uu____2285 =
        let uu____2294 = FStar_Tests_Util.app tm1 us  in norm uu____2294  in
      (uu____2285, us)
  
let (run_all : unit -> Prims.bool) =
  fun uu____2319  ->
    FStar_Util.print_string "Testing the unifier\n";
    FStar_Options.__set_unit_tests ();
    (let unify_check n1 x1 y1 g f = unify n1 x1 y1 g f  in
     let unify1 n1 x1 y1 g = unify n1 x1 y1 g (fun uu____2428  -> ())  in
     let int_t = FStar_Tests_Pars.tc "Prims.int"  in
     let x1 =
       let uu____2450 =
         FStar_Syntax_Syntax.gen_bv "x" FStar_Pervasives_Native.None int_t
          in
       FStar_All.pipe_right uu____2450 FStar_Syntax_Syntax.bv_to_name  in
     let y1 =
       let uu____2484 =
         FStar_Syntax_Syntax.gen_bv "y" FStar_Pervasives_Native.None int_t
          in
       FStar_All.pipe_right uu____2484 FStar_Syntax_Syntax.bv_to_name  in
     unify1 (Prims.parse_int "0") x1 x1 FStar_TypeChecker_Common.Trivial;
     (let uu____2510 =
        let uu____2511 =
          FStar_Syntax_Util.mk_eq2 FStar_Syntax_Syntax.U_zero
            FStar_Syntax_Util.t_bool x1 y1
           in
        FStar_TypeChecker_Common.NonTrivial uu____2511  in
      unify1 (Prims.parse_int "1") x1 y1 uu____2510);
     (let id1 = FStar_Tests_Pars.tc "fun x -> x"  in
      (let uu____2532 = FStar_Tests_Util.app id1 [x1]  in
       unify1 (Prims.parse_int "2") x1 uu____2532
         FStar_TypeChecker_Common.Trivial);
      (let id2 = FStar_Tests_Pars.tc "fun x -> x"  in
       unify1 (Prims.parse_int "3") id2 id2 FStar_TypeChecker_Common.Trivial;
       (let id3 = FStar_Tests_Pars.tc "fun x -> x"  in
        let id' = FStar_Tests_Pars.tc "fun y -> y"  in
        unify1 (Prims.parse_int "4") id3 id' FStar_TypeChecker_Common.Trivial;
        (let uu____2587 = FStar_Tests_Pars.tc "fun x y -> x"  in
         let uu____2599 = FStar_Tests_Pars.tc "fun a b -> a"  in
         unify1 (Prims.parse_int "5") uu____2587 uu____2599
           FStar_TypeChecker_Common.Trivial);
        (let uu____2613 = FStar_Tests_Pars.tc "fun x y z -> y"  in
         let uu____2625 = FStar_Tests_Pars.tc "fun a b c -> b"  in
         unify1 (Prims.parse_int "6") uu____2613 uu____2625
           FStar_TypeChecker_Common.Trivial);
        (let uu____2639 = FStar_Tests_Pars.tc "fun (x:int) (y:int) -> y"  in
         let uu____2651 = FStar_Tests_Pars.tc "fun (x:int) (y:int) -> x"  in
         let uu____2663 =
           let uu____2664 =
             FStar_Tests_Pars.tc "(forall (x:int). (forall (y:int). y==x))"
              in
           FStar_TypeChecker_Common.NonTrivial uu____2664  in
         unify1 (Prims.parse_int "7") uu____2639 uu____2651 uu____2663);
        (let uu____2676 =
           FStar_Tests_Pars.tc "fun (x:int) (y:int) (z:int) -> y"  in
         let uu____2688 =
           FStar_Tests_Pars.tc "fun (x:int) (y:int) (z:int) -> z"  in
         let uu____2700 =
           let uu____2701 =
             FStar_Tests_Pars.tc
               "(forall (x:int). (forall (y:int). (forall (z:int). y==z)))"
              in
           FStar_TypeChecker_Common.NonTrivial uu____2701  in
         unify1 (Prims.parse_int "8") uu____2676 uu____2688 uu____2700);
        (let uu____2713 = FStar_Main.process_args ()  in
         FStar_All.pipe_right uu____2713 (fun a2  -> ()));
        (let uu____2728 =
           let uu____2743 = FStar_Tests_Pars.tc "fun u x -> u x"  in
           inst (Prims.parse_int "1") uu____2743  in
         match uu____2728 with
         | (tm1,us) ->
             let sol = FStar_Tests_Pars.tc "fun x -> c_and x x"  in
             (unify_check (Prims.parse_int "9") tm1 sol
                FStar_TypeChecker_Common.Trivial
                (fun uu____2793  ->
                   let uu____2794 =
                     let uu____2796 =
                       let uu____2807 = FStar_List.hd us  in norm uu____2807
                        in
                     let uu____2820 = norm sol  in
                     FStar_Tests_Util.term_eq uu____2796 uu____2820  in
                   FStar_Tests_Util.always (Prims.parse_int "9") uu____2794);
              (let uu____2832 =
                 let uu____2847 = FStar_Tests_Pars.tc "fun u x -> u x"  in
                 inst (Prims.parse_int "1") uu____2847  in
               match uu____2832 with
               | (tm2,us1) ->
                   let sol1 = FStar_Tests_Pars.tc "fun x y -> x + y"  in
                   (unify_check (Prims.parse_int "10") tm2 sol1
                      FStar_TypeChecker_Common.Trivial
                      (fun uu____2897  ->
                         let uu____2898 =
                           let uu____2900 =
                             let uu____2911 = FStar_List.hd us1  in
                             norm uu____2911  in
                           let uu____2924 = norm sol1  in
                           FStar_Tests_Util.term_eq uu____2900 uu____2924  in
                         FStar_Tests_Util.always (Prims.parse_int "10")
                           uu____2898);
                    (let tm11 =
                       FStar_Tests_Pars.tc "x:int -> y:int{eq2 y x} -> bool"
                        in
                     let tm21 = FStar_Tests_Pars.tc "x:int -> y:int -> bool"
                        in
                     (let uu____2957 =
                        let uu____2958 =
                          FStar_Tests_Pars.tc
                            "forall (x:int). (forall (y:int). y==x)"
                           in
                        FStar_TypeChecker_Common.NonTrivial uu____2958  in
                      unify1 (Prims.parse_int "11") tm11 tm21 uu____2957);
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
                      (let uu____2991 =
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
                           let uu____3069 =
                             let uu____3078 =
                               let uu____3085 =
                                 FStar_Syntax_Syntax.bv_to_name q  in
                               [uu____3085]  in
                             FStar_Tests_Util.app l uu____3078  in
                           norm uu____3069  in
                         let l1 =
                           FStar_Tests_Pars.tc "fun (p:unit -> Type0) -> p"
                            in
                         let unit = FStar_Tests_Pars.tc "()"  in
                         let env =
                           let uu____3231 = FStar_Tests_Pars.init ()  in
                           let uu____3340 =
                             let uu____3341 =
                               FStar_Syntax_Syntax.mk_binder x2  in
                             let uu____3353 =
                               let uu____3367 =
                                 FStar_Syntax_Syntax.mk_binder q  in
                               [uu____3367]  in
                             uu____3341 :: uu____3353  in
                           FStar_TypeChecker_Env.push_binders uu____3231
                             uu____3340
                            in
                         let uu____3412 =
                           FStar_TypeChecker_Util.new_implicit_var ""
                             FStar_Range.dummyRange env typ
                            in
                         match uu____3412 with
                         | (u_p,uu____3459,uu____3460) ->
                             let tm23 =
                               let uu____3516 =
                                 let uu____3527 =
                                   FStar_Tests_Util.app l1 [u_p]  in
                                 norm uu____3527  in
                               FStar_Tests_Util.app uu____3516 [unit]  in
                             (tm13, tm23)
                          in
                       match uu____2991 with
                       | (tm13,tm23) ->
                           (unify1 (Prims.parse_int "13") tm13 tm23
                              FStar_TypeChecker_Common.Trivial;
                            (let uu____3593 =
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
                                 let uu____3671 =
                                   let uu____3680 =
                                     let uu____3687 =
                                       FStar_Syntax_Syntax.bv_to_name q  in
                                     [uu____3687]  in
                                   FStar_Tests_Util.app l uu____3680  in
                                 norm uu____3671  in
                               let l1 =
                                 FStar_Tests_Pars.tc
                                   "fun (p:pure_post unit) -> p"
                                  in
                               let unit = FStar_Tests_Pars.tc "()"  in
                               let env =
                                 let uu____3833 = FStar_Tests_Pars.init ()
                                    in
                                 let uu____3942 =
                                   let uu____3943 =
                                     FStar_Syntax_Syntax.mk_binder x2  in
                                   let uu____3955 =
                                     let uu____3969 =
                                       FStar_Syntax_Syntax.mk_binder q  in
                                     [uu____3969]  in
                                   uu____3943 :: uu____3955  in
                                 FStar_TypeChecker_Env.push_binders
                                   uu____3833 uu____3942
                                  in
                               let uu____4014 =
                                 FStar_TypeChecker_Util.new_implicit_var ""
                                   FStar_Range.dummyRange env typ
                                  in
                               match uu____4014 with
                               | (u_p,uu____4061,uu____4062) ->
                                   let tm24 =
                                     let uu____4118 =
                                       let uu____4129 =
                                         FStar_Tests_Util.app l1 [u_p]  in
                                       norm uu____4129  in
                                     FStar_Tests_Util.app uu____4118 [unit]
                                      in
                                   (tm14, tm24)
                                in
                             match uu____3593 with
                             | (tm14,tm24) ->
                                 (unify1 (Prims.parse_int "14") tm14 tm24
                                    FStar_TypeChecker_Common.Trivial;
                                  FStar_Options.__clear_unit_tests ();
                                  (let uu____4197 = FStar_ST.op_Bang success
                                      in
                                   if uu____4197
                                   then
                                     FStar_Util.print_string "Unifier ok\n"
                                   else ());
                                  FStar_ST.op_Bang success))))))))))))))
  