open Prims
let (tcenv : unit -> FStar_TypeChecker_Env.env) =
  fun uu____5  -> FStar_Tests_Pars.init () 
let (guard_to_string :
  FStar_TypeChecker_Common.guard_formula -> Prims.string) =
  fun g  ->
    match g with
    | FStar_TypeChecker_Common.Trivial  -> "trivial"
    | FStar_TypeChecker_Common.NonTrivial f ->
        let uu____12 = tcenv ()  in
        FStar_TypeChecker_Normalize.term_to_string uu____12 f
  
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
        let uu____66 =
          match (g, g') with
          | (FStar_TypeChecker_Common.Trivial
             ,FStar_TypeChecker_Common.Trivial ) -> (true, g, g')
          | (FStar_TypeChecker_Common.NonTrivial
             f,FStar_TypeChecker_Common.NonTrivial f') ->
              let f1 =
                let uu____82 = tcenv ()  in
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Env.EraseUniverses] uu____82 f
                 in
              let f'1 =
                let uu____84 = tcenv ()  in
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Env.EraseUniverses] uu____84 f'
                 in
              let uu____85 = FStar_Tests_Util.term_eq f1 f'1  in
              (uu____85, (FStar_TypeChecker_Common.NonTrivial f1),
                (FStar_TypeChecker_Common.NonTrivial f'1))
          | uu____86 -> (false, g, g')  in
        match uu____66 with
        | (b,g1,g'1) ->
            (if Prims.op_Negation b
             then
               (let uu____95 =
                  let uu____96 = FStar_Util.string_of_int i  in
                  let uu____97 = guard_to_string g'1  in
                  let uu____98 = guard_to_string g1  in
                  FStar_Util.format3
                    "Test %s failed:\n\tExpected guard %s;\n\tGot guard      %s\n"
                    uu____96 uu____97 uu____98
                   in
                FStar_All.pipe_left fail uu____95)
             else ();
             (let uu____100 = (FStar_ST.op_Bang success) && b  in
              FStar_ST.op_Colon_Equals success uu____100))
  
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
            (let uu____178 = FStar_Util.string_of_int i  in
             FStar_Util.print1 "%s ..." uu____178);
            (let uu____180 = FStar_Main.process_args ()  in
             FStar_All.pipe_right uu____180 (fun a1  -> ()));
            (let uu____194 = FStar_Syntax_Print.term_to_string x1  in
             let uu____195 = FStar_Syntax_Print.term_to_string y1  in
             FStar_Util.print2 "Unify %s\nand %s\n" uu____194 uu____195);
            (let g =
               let uu____197 =
                 let uu____198 =
                   let uu____199 = tcenv ()  in
                   FStar_TypeChecker_Rel.teq uu____199 x1 y1  in
                 let uu____200 =
                   let uu____205 = tcenv ()  in
                   FStar_TypeChecker_Rel.solve_deferred_constraints uu____205
                    in
                 FStar_All.pipe_right uu____198 uu____200  in
               let uu____206 =
                 let uu____211 = tcenv ()  in
                 FStar_TypeChecker_Rel.simplify_guard uu____211  in
               FStar_All.pipe_right uu____197 uu____206  in
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
        (fun uu___478_235  ->
           match () with
           | () ->
               let g =
                 let uu____237 =
                   let uu____238 = tcenv ()  in
                   FStar_TypeChecker_Rel.teq uu____238 x1 y1  in
                 let uu____239 =
                   let uu____244 = tcenv ()  in
                   FStar_TypeChecker_Rel.solve_deferred_constraints uu____244
                    in
                 FStar_All.pipe_right uu____237 uu____239  in
               (match g.FStar_TypeChecker_Env.guard_f with
                | FStar_TypeChecker_Common.Trivial  ->
                    let uu____245 =
                      let uu____246 = FStar_Syntax_Print.term_to_string x1
                         in
                      let uu____247 = FStar_Syntax_Print.term_to_string y1
                         in
                      FStar_Util.format2
                        "%s and %s should not be unifiable\n" uu____246
                        uu____247
                       in
                    fail uu____245
                | FStar_TypeChecker_Common.NonTrivial f ->
                    let uu____249 = FStar_Syntax_Print.term_to_string x1  in
                    let uu____250 = FStar_Syntax_Print.term_to_string y1  in
                    let uu____251 = FStar_Syntax_Print.term_to_string f  in
                    FStar_Util.print3 "%s and %s are unifiable if %s\n"
                      uu____249 uu____250 uu____251)) ()
      with | FStar_Errors.Error (e,msg,r) -> FStar_Util.print1 "%s\n" msg
  
let (unify' : Prims.string -> Prims.string -> unit) =
  fun x1  ->
    fun y1  ->
      let x2 = FStar_Tests_Pars.pars x1  in
      let y2 = FStar_Tests_Pars.pars y1  in
      let g =
        let uu____273 =
          let uu____274 = tcenv ()  in
          FStar_TypeChecker_Rel.teq uu____274 x2 y2  in
        let uu____275 =
          let uu____280 = tcenv ()  in
          FStar_TypeChecker_Rel.solve_deferred_constraints uu____280  in
        FStar_All.pipe_right uu____273 uu____275  in
      let uu____281 = FStar_Syntax_Print.term_to_string x2  in
      let uu____282 = FStar_Syntax_Print.term_to_string y2  in
      let uu____283 = guard_to_string g.FStar_TypeChecker_Env.guard_f  in
      FStar_Util.print3 "%s and %s are unifiable with guard %s\n" uu____281
        uu____282 uu____283
  
let (norm : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____289 = tcenv ()  in
    FStar_TypeChecker_Normalize.normalize [] uu____289 t
  
let (inst :
  Prims.int ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun n1  ->
    fun tm1  ->
      let rec aux out n2 =
        if n2 = (Prims.parse_int "0")
        then out
        else
          (let uu____330 =
             let uu____343 = FStar_Tests_Pars.init ()  in
             FStar_TypeChecker_Util.new_implicit_var ""
               FStar_Range.dummyRange uu____343 FStar_Syntax_Util.ktype0
              in
           match uu____330 with
           | (t,uu____347,uu____348) ->
               let uu____361 =
                 let uu____374 = FStar_Tests_Pars.init ()  in
                 FStar_TypeChecker_Util.new_implicit_var ""
                   FStar_Range.dummyRange uu____374 t
                  in
               (match uu____361 with
                | (u,uu____378,uu____379) ->
                    aux (u :: out) (n2 - (Prims.parse_int "1"))))
         in
      let us = aux [] n1  in
      let uu____395 =
        let uu____396 = FStar_Tests_Util.app tm1 us  in norm uu____396  in
      (uu____395, us)
  
let (run_all : unit -> Prims.bool) =
  fun uu____403  ->
    FStar_Util.print_string "Testing the unifier\n";
    FStar_Options.__set_unit_tests ();
    (let unify_check n1 x1 y1 g f = unify n1 x1 y1 g f  in
     let unify1 n1 x1 y1 g = unify n1 x1 y1 g (fun uu____475  -> ())  in
     let int_t = FStar_Tests_Pars.tc "Prims.int"  in
     let x1 =
       let uu____480 =
         FStar_Syntax_Syntax.gen_bv "x" FStar_Pervasives_Native.None int_t
          in
       FStar_All.pipe_right uu____480 FStar_Syntax_Syntax.bv_to_name  in
     let y1 =
       let uu____486 =
         FStar_Syntax_Syntax.gen_bv "y" FStar_Pervasives_Native.None int_t
          in
       FStar_All.pipe_right uu____486 FStar_Syntax_Syntax.bv_to_name  in
     unify1 (Prims.parse_int "0") x1 x1 FStar_TypeChecker_Common.Trivial;
     (let uu____491 =
        let uu____492 =
          FStar_Syntax_Util.mk_eq2 FStar_Syntax_Syntax.U_zero
            FStar_Syntax_Util.t_bool x1 y1
           in
        FStar_TypeChecker_Common.NonTrivial uu____492  in
      unify1 (Prims.parse_int "1") x1 y1 uu____491);
     (let id1 = FStar_Tests_Pars.tc "fun x -> x"  in
      (let uu____495 = FStar_Tests_Util.app id1 [x1]  in
       unify1 (Prims.parse_int "2") x1 uu____495
         FStar_TypeChecker_Common.Trivial);
      (let id2 = FStar_Tests_Pars.tc "fun x -> x"  in
       unify1 (Prims.parse_int "3") id2 id2 FStar_TypeChecker_Common.Trivial;
       (let id3 = FStar_Tests_Pars.tc "fun x -> x"  in
        let id' = FStar_Tests_Pars.tc "fun y -> y"  in
        unify1 (Prims.parse_int "4") id3 id' FStar_TypeChecker_Common.Trivial;
        (let uu____504 = FStar_Tests_Pars.tc "fun x y -> x"  in
         let uu____507 = FStar_Tests_Pars.tc "fun a b -> a"  in
         unify1 (Prims.parse_int "5") uu____504 uu____507
           FStar_TypeChecker_Common.Trivial);
        (let uu____511 = FStar_Tests_Pars.tc "fun x y z -> y"  in
         let uu____514 = FStar_Tests_Pars.tc "fun a b c -> b"  in
         unify1 (Prims.parse_int "6") uu____511 uu____514
           FStar_TypeChecker_Common.Trivial);
        (let uu____518 = FStar_Tests_Pars.tc "fun (x:int) (y:int) -> y"  in
         let uu____521 = FStar_Tests_Pars.tc "fun (x:int) (y:int) -> x"  in
         let uu____524 =
           let uu____525 =
             FStar_Tests_Pars.tc "(forall (x:int). (forall (y:int). y==x))"
              in
           FStar_TypeChecker_Common.NonTrivial uu____525  in
         unify1 (Prims.parse_int "7") uu____518 uu____521 uu____524);
        (let uu____527 =
           FStar_Tests_Pars.tc "fun (x:int) (y:int) (z:int) -> y"  in
         let uu____530 =
           FStar_Tests_Pars.tc "fun (x:int) (y:int) (z:int) -> z"  in
         let uu____533 =
           let uu____534 =
             FStar_Tests_Pars.tc
               "(forall (x:int). (forall (y:int). (forall (z:int). y==z)))"
              in
           FStar_TypeChecker_Common.NonTrivial uu____534  in
         unify1 (Prims.parse_int "8") uu____527 uu____530 uu____533);
        (let uu____536 = FStar_Main.process_args ()  in
         FStar_All.pipe_right uu____536 (fun a2  -> ()));
        (let uu____549 =
           let uu____556 = FStar_Tests_Pars.tc "fun u x -> u x"  in
           inst (Prims.parse_int "1") uu____556  in
         match uu____549 with
         | (tm1,us) ->
             let sol = FStar_Tests_Pars.tc "fun x -> c_and x x"  in
             (unify_check (Prims.parse_int "9") tm1 sol
                FStar_TypeChecker_Common.Trivial
                (fun uu____569  ->
                   let uu____570 =
                     let uu____571 =
                       let uu____574 = FStar_List.hd us  in norm uu____574
                        in
                     let uu____575 = norm sol  in
                     FStar_Tests_Util.term_eq uu____571 uu____575  in
                   FStar_Tests_Util.always (Prims.parse_int "9") uu____570);
              (let uu____578 =
                 let uu____585 = FStar_Tests_Pars.tc "fun u x -> u x"  in
                 inst (Prims.parse_int "1") uu____585  in
               match uu____578 with
               | (tm2,us1) ->
                   let sol1 = FStar_Tests_Pars.tc "fun x y -> x + y"  in
                   (unify_check (Prims.parse_int "10") tm2 sol1
                      FStar_TypeChecker_Common.Trivial
                      (fun uu____598  ->
                         let uu____599 =
                           let uu____600 =
                             let uu____603 = FStar_List.hd us1  in
                             norm uu____603  in
                           let uu____604 = norm sol1  in
                           FStar_Tests_Util.term_eq uu____600 uu____604  in
                         FStar_Tests_Util.always (Prims.parse_int "10")
                           uu____599);
                    (let tm11 =
                       FStar_Tests_Pars.tc "x:int -> y:int{eq2 y x} -> bool"
                        in
                     let tm21 = FStar_Tests_Pars.tc "x:int -> y:int -> bool"
                        in
                     (let uu____610 =
                        let uu____611 =
                          FStar_Tests_Pars.tc
                            "forall (x:int). (forall (y:int). y==x)"
                           in
                        FStar_TypeChecker_Common.NonTrivial uu____611  in
                      unify1 (Prims.parse_int "11") tm11 tm21 uu____610);
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
                      (let uu____615 =
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
                           let uu____630 =
                             let uu____631 =
                               let uu____634 =
                                 FStar_Syntax_Syntax.bv_to_name q  in
                               [uu____634]  in
                             FStar_Tests_Util.app l uu____631  in
                           norm uu____630  in
                         let l1 =
                           FStar_Tests_Pars.tc "fun (p:unit -> Type0) -> p"
                            in
                         let unit = FStar_Tests_Pars.tc "()"  in
                         let env =
                           let uu____638 = FStar_Tests_Pars.init ()  in
                           let uu____639 =
                             let uu____640 = FStar_Syntax_Syntax.mk_binder x2
                                in
                             let uu____647 =
                               let uu____656 =
                                 FStar_Syntax_Syntax.mk_binder q  in
                               [uu____656]  in
                             uu____640 :: uu____647  in
                           FStar_TypeChecker_Env.push_binders uu____638
                             uu____639
                            in
                         let uu____681 =
                           FStar_TypeChecker_Util.new_implicit_var ""
                             FStar_Range.dummyRange env typ
                            in
                         match uu____681 with
                         | (u_p,uu____703,uu____704) ->
                             let tm23 =
                               let uu____720 =
                                 let uu____723 =
                                   FStar_Tests_Util.app l1 [u_p]  in
                                 norm uu____723  in
                               FStar_Tests_Util.app uu____720 [unit]  in
                             (tm13, tm23)
                          in
                       match uu____615 with
                       | (tm13,tm23) ->
                           (unify1 (Prims.parse_int "13") tm13 tm23
                              FStar_TypeChecker_Common.Trivial;
                            (let uu____739 =
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
                                 let uu____754 =
                                   let uu____755 =
                                     let uu____758 =
                                       FStar_Syntax_Syntax.bv_to_name q  in
                                     [uu____758]  in
                                   FStar_Tests_Util.app l uu____755  in
                                 norm uu____754  in
                               let l1 =
                                 FStar_Tests_Pars.tc
                                   "fun (p:pure_post unit) -> p"
                                  in
                               let unit = FStar_Tests_Pars.tc "()"  in
                               let env =
                                 let uu____762 = FStar_Tests_Pars.init ()  in
                                 let uu____763 =
                                   let uu____764 =
                                     FStar_Syntax_Syntax.mk_binder x2  in
                                   let uu____771 =
                                     let uu____780 =
                                       FStar_Syntax_Syntax.mk_binder q  in
                                     [uu____780]  in
                                   uu____764 :: uu____771  in
                                 FStar_TypeChecker_Env.push_binders uu____762
                                   uu____763
                                  in
                               let uu____805 =
                                 FStar_TypeChecker_Util.new_implicit_var ""
                                   FStar_Range.dummyRange env typ
                                  in
                               match uu____805 with
                               | (u_p,uu____827,uu____828) ->
                                   let tm24 =
                                     let uu____844 =
                                       let uu____847 =
                                         FStar_Tests_Util.app l1 [u_p]  in
                                       norm uu____847  in
                                     FStar_Tests_Util.app uu____844 [unit]
                                      in
                                   (tm14, tm24)
                                in
                             match uu____739 with
                             | (tm14,tm24) ->
                                 (unify1 (Prims.parse_int "14") tm14 tm24
                                    FStar_TypeChecker_Common.Trivial;
                                  FStar_Options.__clear_unit_tests ();
                                  (let uu____865 = FStar_ST.op_Bang success
                                      in
                                   if uu____865
                                   then
                                     FStar_Util.print_string "Unifier ok\n"
                                   else ());
                                  FStar_ST.op_Bang success))))))))))))))
  