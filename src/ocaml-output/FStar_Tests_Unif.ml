open Prims
let (tcenv : unit -> FStar_TypeChecker_Env.env) =
  fun uu____78847  -> FStar_Tests_Pars.init () 
let (guard_to_string :
  FStar_TypeChecker_Common.guard_formula -> Prims.string) =
  fun g  ->
    match g with
    | FStar_TypeChecker_Common.Trivial  -> "trivial"
    | FStar_TypeChecker_Common.NonTrivial f ->
        let uu____78858 = tcenv ()  in
        FStar_TypeChecker_Normalize.term_to_string uu____78858 f
  
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
        let uu____78914 =
          match (g, g') with
          | (FStar_TypeChecker_Common.Trivial
             ,FStar_TypeChecker_Common.Trivial ) -> (true, g, g')
          | (FStar_TypeChecker_Common.NonTrivial
             f,FStar_TypeChecker_Common.NonTrivial f') ->
              let f1 =
                let uu____78934 = tcenv ()  in
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Env.EraseUniverses] uu____78934 f
                 in
              let f'1 =
                let uu____78936 = tcenv ()  in
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Env.EraseUniverses] uu____78936 f'
                 in
              let uu____78937 = FStar_Tests_Util.term_eq f1 f'1  in
              (uu____78937, (FStar_TypeChecker_Common.NonTrivial f1),
                (FStar_TypeChecker_Common.NonTrivial f'1))
          | uu____78940 -> (false, g, g')  in
        match uu____78914 with
        | (b,g1,g'1) ->
            (if Prims.op_Negation b
             then
               (let uu____78954 =
                  let uu____78956 = FStar_Util.string_of_int i  in
                  let uu____78958 = guard_to_string g'1  in
                  let uu____78960 = guard_to_string g1  in
                  FStar_Util.format3
                    "Test %s failed:\n\tExpected guard %s;\n\tGot guard      %s\n"
                    uu____78956 uu____78958 uu____78960
                   in
                FStar_All.pipe_left fail uu____78954)
             else ();
             (let uu____78966 = (FStar_ST.op_Bang success) && b  in
              FStar_ST.op_Colon_Equals success uu____78966))
  
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
            (let uu____79052 = FStar_Util.string_of_int i  in
             FStar_Util.print1 "%s ..." uu____79052);
            (let uu____79056 = FStar_Main.process_args ()  in
             FStar_All.pipe_right uu____79056 (fun a1  -> ()));
            (let uu____79072 = FStar_Syntax_Print.term_to_string x1  in
             let uu____79074 = FStar_Syntax_Print.term_to_string y1  in
             FStar_Util.print2 "Unify %s\nand %s\n" uu____79072 uu____79074);
            (let g =
               let uu____79078 =
                 let uu____79079 =
                   let uu____79080 = tcenv ()  in
                   FStar_TypeChecker_Rel.teq uu____79080 x1 y1  in
                 let uu____79081 =
                   let uu____79086 = tcenv ()  in
                   FStar_TypeChecker_Rel.solve_deferred_constraints
                     uu____79086
                    in
                 FStar_All.pipe_right uu____79079 uu____79081  in
               let uu____79087 =
                 let uu____79092 = tcenv ()  in
                 FStar_TypeChecker_Rel.simplify_guard uu____79092  in
               FStar_All.pipe_right uu____79078 uu____79087  in
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
        (fun uu___783_79117  ->
           match () with
           | () ->
               let g =
                 let uu____79119 =
                   let uu____79120 = tcenv ()  in
                   FStar_TypeChecker_Rel.teq uu____79120 x1 y1  in
                 let uu____79121 =
                   let uu____79126 = tcenv ()  in
                   FStar_TypeChecker_Rel.solve_deferred_constraints
                     uu____79126
                    in
                 FStar_All.pipe_right uu____79119 uu____79121  in
               (match g.FStar_TypeChecker_Env.guard_f with
                | FStar_TypeChecker_Common.Trivial  ->
                    let uu____79127 =
                      let uu____79129 = FStar_Syntax_Print.term_to_string x1
                         in
                      let uu____79131 = FStar_Syntax_Print.term_to_string y1
                         in
                      FStar_Util.format2
                        "%s and %s should not be unifiable\n" uu____79129
                        uu____79131
                       in
                    fail uu____79127
                | FStar_TypeChecker_Common.NonTrivial f ->
                    let uu____79135 = FStar_Syntax_Print.term_to_string x1
                       in
                    let uu____79137 = FStar_Syntax_Print.term_to_string y1
                       in
                    let uu____79139 = FStar_Syntax_Print.term_to_string f  in
                    FStar_Util.print3 "%s and %s are unifiable if %s\n"
                      uu____79135 uu____79137 uu____79139)) ()
      with | FStar_Errors.Error (e,msg,r) -> FStar_Util.print1 "%s\n" msg
  
let (unify' : Prims.string -> Prims.string -> unit) =
  fun x1  ->
    fun y1  ->
      let x2 = FStar_Tests_Pars.pars x1  in
      let y2 = FStar_Tests_Pars.pars y1  in
      let g =
        let uu____79171 =
          let uu____79172 = tcenv ()  in
          FStar_TypeChecker_Rel.teq uu____79172 x2 y2  in
        let uu____79173 =
          let uu____79178 = tcenv ()  in
          FStar_TypeChecker_Rel.solve_deferred_constraints uu____79178  in
        FStar_All.pipe_right uu____79171 uu____79173  in
      let uu____79179 = FStar_Syntax_Print.term_to_string x2  in
      let uu____79181 = FStar_Syntax_Print.term_to_string y2  in
      let uu____79183 = guard_to_string g.FStar_TypeChecker_Env.guard_f  in
      FStar_Util.print3 "%s and %s are unifiable with guard %s\n" uu____79179
        uu____79181 uu____79183
  
let (norm : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____79192 = tcenv ()  in
    FStar_TypeChecker_Normalize.normalize [] uu____79192 t
  
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
          (let uu____79242 =
             let uu____79255 = FStar_Tests_Pars.init ()  in
             FStar_TypeChecker_Util.new_implicit_var ""
               FStar_Range.dummyRange uu____79255 FStar_Syntax_Util.ktype0
              in
           match uu____79242 with
           | (t,uu____79260,uu____79261) ->
               let uu____79274 =
                 let uu____79287 = FStar_Tests_Pars.init ()  in
                 FStar_TypeChecker_Util.new_implicit_var ""
                   FStar_Range.dummyRange uu____79287 t
                  in
               (match uu____79274 with
                | (u,uu____79292,uu____79293) ->
                    aux (u :: out) (n2 - (Prims.parse_int "1"))))
         in
      let us = aux [] n1  in
      let uu____79310 =
        let uu____79311 = FStar_Tests_Util.app tm1 us  in norm uu____79311
         in
      (uu____79310, us)
  
let (run_all : unit -> Prims.bool) =
  fun uu____79320  ->
    FStar_Util.print_string "Testing the unifier\n";
    FStar_Options.__set_unit_tests ();
    (let unify_check n1 x1 y1 g f = unify n1 x1 y1 g f  in
     let unify1 n1 x1 y1 g = unify n1 x1 y1 g (fun uu____79397  -> ())  in
     let int_t = FStar_Tests_Pars.tc "Prims.int"  in
     let x1 =
       let uu____79403 =
         FStar_Syntax_Syntax.gen_bv "x" FStar_Pervasives_Native.None int_t
          in
       FStar_All.pipe_right uu____79403 FStar_Syntax_Syntax.bv_to_name  in
     let y1 =
       let uu____79410 =
         FStar_Syntax_Syntax.gen_bv "y" FStar_Pervasives_Native.None int_t
          in
       FStar_All.pipe_right uu____79410 FStar_Syntax_Syntax.bv_to_name  in
     unify1 (Prims.parse_int "0") x1 x1 FStar_TypeChecker_Common.Trivial;
     (let uu____79417 =
        let uu____79418 =
          FStar_Syntax_Util.mk_eq2 FStar_Syntax_Syntax.U_zero
            FStar_Syntax_Util.t_bool x1 y1
           in
        FStar_TypeChecker_Common.NonTrivial uu____79418  in
      unify1 (Prims.parse_int "1") x1 y1 uu____79417);
     (let id1 = FStar_Tests_Pars.tc "fun x -> x"  in
      (let uu____79423 = FStar_Tests_Util.app id1 [x1]  in
       unify1 (Prims.parse_int "2") x1 uu____79423
         FStar_TypeChecker_Common.Trivial);
      (let id2 = FStar_Tests_Pars.tc "fun x -> x"  in
       unify1 (Prims.parse_int "3") id2 id2 FStar_TypeChecker_Common.Trivial;
       (let id3 = FStar_Tests_Pars.tc "fun x -> x"  in
        let id' = FStar_Tests_Pars.tc "fun y -> y"  in
        unify1 (Prims.parse_int "4") id3 id' FStar_TypeChecker_Common.Trivial;
        (let uu____79438 = FStar_Tests_Pars.tc "fun x y -> x"  in
         let uu____79442 = FStar_Tests_Pars.tc "fun a b -> a"  in
         unify1 (Prims.parse_int "5") uu____79438 uu____79442
           FStar_TypeChecker_Common.Trivial);
        (let uu____79448 = FStar_Tests_Pars.tc "fun x y z -> y"  in
         let uu____79452 = FStar_Tests_Pars.tc "fun a b c -> b"  in
         unify1 (Prims.parse_int "6") uu____79448 uu____79452
           FStar_TypeChecker_Common.Trivial);
        (let uu____79458 = FStar_Tests_Pars.tc "fun (x:int) (y:int) -> y"  in
         let uu____79462 = FStar_Tests_Pars.tc "fun (x:int) (y:int) -> x"  in
         let uu____79466 =
           let uu____79467 =
             FStar_Tests_Pars.tc "(forall (x:int). (forall (y:int). y==x))"
              in
           FStar_TypeChecker_Common.NonTrivial uu____79467  in
         unify1 (Prims.parse_int "7") uu____79458 uu____79462 uu____79466);
        (let uu____79471 =
           FStar_Tests_Pars.tc "fun (x:int) (y:int) (z:int) -> y"  in
         let uu____79475 =
           FStar_Tests_Pars.tc "fun (x:int) (y:int) (z:int) -> z"  in
         let uu____79479 =
           let uu____79480 =
             FStar_Tests_Pars.tc
               "(forall (x:int). (forall (y:int). (forall (z:int). y==z)))"
              in
           FStar_TypeChecker_Common.NonTrivial uu____79480  in
         unify1 (Prims.parse_int "8") uu____79471 uu____79475 uu____79479);
        (let uu____79484 = FStar_Main.process_args ()  in
         FStar_All.pipe_right uu____79484 (fun a2  -> ()));
        (let uu____79499 =
           let uu____79506 = FStar_Tests_Pars.tc "fun u x -> u x"  in
           inst (Prims.parse_int "1") uu____79506  in
         match uu____79499 with
         | (tm1,us) ->
             let sol = FStar_Tests_Pars.tc "fun x -> c_and x x"  in
             (unify_check (Prims.parse_int "9") tm1 sol
                FStar_TypeChecker_Common.Trivial
                (fun uu____79524  ->
                   let uu____79525 =
                     let uu____79527 =
                       let uu____79530 = FStar_List.hd us  in
                       norm uu____79530  in
                     let uu____79531 = norm sol  in
                     FStar_Tests_Util.term_eq uu____79527 uu____79531  in
                   FStar_Tests_Util.always (Prims.parse_int "9") uu____79525);
              (let uu____79535 =
                 let uu____79542 = FStar_Tests_Pars.tc "fun u x -> u x"  in
                 inst (Prims.parse_int "1") uu____79542  in
               match uu____79535 with
               | (tm2,us1) ->
                   let sol1 = FStar_Tests_Pars.tc "fun x y -> x + y"  in
                   (unify_check (Prims.parse_int "10") tm2 sol1
                      FStar_TypeChecker_Common.Trivial
                      (fun uu____79560  ->
                         let uu____79561 =
                           let uu____79563 =
                             let uu____79566 = FStar_List.hd us1  in
                             norm uu____79566  in
                           let uu____79567 = norm sol1  in
                           FStar_Tests_Util.term_eq uu____79563 uu____79567
                            in
                         FStar_Tests_Util.always (Prims.parse_int "10")
                           uu____79561);
                    (let tm11 =
                       FStar_Tests_Pars.tc "x:int -> y:int{eq2 y x} -> bool"
                        in
                     let tm21 = FStar_Tests_Pars.tc "x:int -> y:int -> bool"
                        in
                     (let uu____79576 =
                        let uu____79577 =
                          FStar_Tests_Pars.tc
                            "forall (x:int). (forall (y:int). y==x)"
                           in
                        FStar_TypeChecker_Common.NonTrivial uu____79577  in
                      unify1 (Prims.parse_int "11") tm11 tm21 uu____79576);
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
                      (let uu____79586 =
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
                           let uu____79604 =
                             let uu____79605 =
                               let uu____79608 =
                                 FStar_Syntax_Syntax.bv_to_name q  in
                               [uu____79608]  in
                             FStar_Tests_Util.app l uu____79605  in
                           norm uu____79604  in
                         let l1 =
                           FStar_Tests_Pars.tc "fun (p:unit -> Type0) -> p"
                            in
                         let unit = FStar_Tests_Pars.tc "()"  in
                         let env =
                           let uu____79614 = FStar_Tests_Pars.init ()  in
                           let uu____79615 =
                             let uu____79616 =
                               FStar_Syntax_Syntax.mk_binder x2  in
                             let uu____79623 =
                               let uu____79632 =
                                 FStar_Syntax_Syntax.mk_binder q  in
                               [uu____79632]  in
                             uu____79616 :: uu____79623  in
                           FStar_TypeChecker_Env.push_binders uu____79614
                             uu____79615
                            in
                         let uu____79657 =
                           FStar_TypeChecker_Util.new_implicit_var ""
                             FStar_Range.dummyRange env typ
                            in
                         match uu____79657 with
                         | (u_p,uu____79680,uu____79681) ->
                             let tm23 =
                               let uu____79697 =
                                 let uu____79700 =
                                   FStar_Tests_Util.app l1 [u_p]  in
                                 norm uu____79700  in
                               FStar_Tests_Util.app uu____79697 [unit]  in
                             (tm13, tm23)
                          in
                       match uu____79586 with
                       | (tm13,tm23) ->
                           (unify1 (Prims.parse_int "13") tm13 tm23
                              FStar_TypeChecker_Common.Trivial;
                            (let uu____79718 =
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
                                 let uu____79736 =
                                   let uu____79737 =
                                     let uu____79740 =
                                       FStar_Syntax_Syntax.bv_to_name q  in
                                     [uu____79740]  in
                                   FStar_Tests_Util.app l uu____79737  in
                                 norm uu____79736  in
                               let l1 =
                                 FStar_Tests_Pars.tc
                                   "fun (p:pure_post unit) -> p"
                                  in
                               let unit = FStar_Tests_Pars.tc "()"  in
                               let env =
                                 let uu____79746 = FStar_Tests_Pars.init ()
                                    in
                                 let uu____79747 =
                                   let uu____79748 =
                                     FStar_Syntax_Syntax.mk_binder x2  in
                                   let uu____79755 =
                                     let uu____79764 =
                                       FStar_Syntax_Syntax.mk_binder q  in
                                     [uu____79764]  in
                                   uu____79748 :: uu____79755  in
                                 FStar_TypeChecker_Env.push_binders
                                   uu____79746 uu____79747
                                  in
                               let uu____79789 =
                                 FStar_TypeChecker_Util.new_implicit_var ""
                                   FStar_Range.dummyRange env typ
                                  in
                               match uu____79789 with
                               | (u_p,uu____79812,uu____79813) ->
                                   let tm24 =
                                     let uu____79829 =
                                       let uu____79832 =
                                         FStar_Tests_Util.app l1 [u_p]  in
                                       norm uu____79832  in
                                     FStar_Tests_Util.app uu____79829 [unit]
                                      in
                                   (tm14, tm24)
                                in
                             match uu____79718 with
                             | (tm14,tm24) ->
                                 (unify1 (Prims.parse_int "14") tm14 tm24
                                    FStar_TypeChecker_Common.Trivial;
                                  FStar_Options.__clear_unit_tests ();
                                  (let uu____79852 = FStar_ST.op_Bang success
                                      in
                                   if uu____79852
                                   then
                                     FStar_Util.print_string "Unifier ok\n"
                                   else ());
                                  FStar_ST.op_Bang success))))))))))))))
  