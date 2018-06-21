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
        let uu____70 =
          match (g, g') with
          | (FStar_TypeChecker_Common.Trivial
             ,FStar_TypeChecker_Common.Trivial ) -> (true, g, g')
          | (FStar_TypeChecker_Common.NonTrivial
             f,FStar_TypeChecker_Common.NonTrivial f') ->
              let f1 =
                let uu____86 = tcenv ()  in
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Normalize.EraseUniverses] uu____86 f
                 in
              let f'1 =
                let uu____88 = tcenv ()  in
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Normalize.EraseUniverses] uu____88 f'
                 in
              let uu____89 = FStar_Tests_Util.term_eq f1 f'1  in
              (uu____89, (FStar_TypeChecker_Common.NonTrivial f1),
                (FStar_TypeChecker_Common.NonTrivial f'1))
          | uu____90 -> (false, g, g')  in
        match uu____70 with
        | (b,g1,g'1) ->
            (if Prims.op_Negation b
             then
               (let uu____99 =
                  let uu____100 = FStar_Util.string_of_int i  in
                  let uu____101 = guard_to_string g'1  in
                  let uu____102 = guard_to_string g1  in
                  FStar_Util.format3
                    "Test %s failed:\n\tExpected guard %s;\n\tGot guard      %s\n"
                    uu____100 uu____101 uu____102
                   in
                FStar_All.pipe_left fail uu____99)
             else ();
             (let uu____104 = (FStar_ST.op_Bang success) && b  in
              FStar_ST.op_Colon_Equals success uu____104))
  
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
            (let uu____190 = FStar_Util.string_of_int i  in
             FStar_Util.print1 "%s ..." uu____190);
            (let uu____192 = FStar_Main.process_args ()  in
             FStar_All.pipe_right uu____192 (fun a242  -> ()));
            (let uu____206 = FStar_Syntax_Print.term_to_string x1  in
             let uu____207 = FStar_Syntax_Print.term_to_string y1  in
             FStar_Util.print2 "Unify %s\nand %s\n" uu____206 uu____207);
            (let g =
               let uu____209 =
                 let uu____210 =
                   let uu____211 = tcenv ()  in
                   FStar_TypeChecker_Rel.teq uu____211 x1 y1  in
                 let uu____212 =
                   let uu____217 = tcenv ()  in
                   FStar_TypeChecker_Rel.solve_deferred_constraints uu____217
                    in
                 FStar_All.pipe_right uu____210 uu____212  in
               let uu____218 =
                 let uu____223 = tcenv ()  in
                 FStar_TypeChecker_Rel.simplify_guard uu____223  in
               FStar_All.pipe_right uu____209 uu____218  in
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
        let g =
          let uu____249 =
            let uu____250 = tcenv ()  in
            FStar_TypeChecker_Rel.teq uu____250 x1 y1  in
          let uu____251 =
            let uu____256 = tcenv ()  in
            FStar_TypeChecker_Rel.solve_deferred_constraints uu____256  in
          FStar_All.pipe_right uu____249 uu____251  in
        match g.FStar_TypeChecker_Env.guard_f with
        | FStar_TypeChecker_Common.Trivial  ->
            let uu____257 =
              let uu____258 = FStar_Syntax_Print.term_to_string x1  in
              let uu____259 = FStar_Syntax_Print.term_to_string y1  in
              FStar_Util.format2 "%s and %s should not be unifiable\n"
                uu____258 uu____259
               in
            fail uu____257
        | FStar_TypeChecker_Common.NonTrivial f ->
            let uu____261 = FStar_Syntax_Print.term_to_string x1  in
            let uu____262 = FStar_Syntax_Print.term_to_string y1  in
            let uu____263 = FStar_Syntax_Print.term_to_string f  in
            FStar_Util.print3 "%s and %s are unifiable if %s\n" uu____261
              uu____262 uu____263
      with | FStar_Errors.Error (e,msg,r) -> FStar_Util.print1 "%s\n" msg
  
let (unify' : Prims.string -> Prims.string -> unit) =
  fun x1  ->
    fun y1  ->
      let x2 = FStar_Tests_Pars.pars x1  in
      let y2 = FStar_Tests_Pars.pars y1  in
      let g =
        let uu____285 =
          let uu____286 = tcenv ()  in
          FStar_TypeChecker_Rel.teq uu____286 x2 y2  in
        let uu____287 =
          let uu____292 = tcenv ()  in
          FStar_TypeChecker_Rel.solve_deferred_constraints uu____292  in
        FStar_All.pipe_right uu____285 uu____287  in
      let uu____293 = FStar_Syntax_Print.term_to_string x2  in
      let uu____294 = FStar_Syntax_Print.term_to_string y2  in
      let uu____295 = guard_to_string g.FStar_TypeChecker_Env.guard_f  in
      FStar_Util.print3 "%s and %s are unifiable with guard %s\n" uu____293
        uu____294 uu____295
  
let (norm : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____301 = tcenv ()  in
    FStar_TypeChecker_Normalize.normalize [] uu____301 t
  
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
          (let uu____342 =
             let uu____355 = FStar_Tests_Pars.init ()  in
             FStar_TypeChecker_Util.new_implicit_var ""
               FStar_Range.dummyRange uu____355 FStar_Syntax_Util.ktype0
              in
           match uu____342 with
           | (t,uu____359,uu____360) ->
               let uu____373 =
                 let uu____386 = FStar_Tests_Pars.init ()  in
                 FStar_TypeChecker_Util.new_implicit_var ""
                   FStar_Range.dummyRange uu____386 t
                  in
               (match uu____373 with
                | (u,uu____390,uu____391) ->
                    aux (u :: out) (n2 - (Prims.parse_int "1"))))
         in
      let us = aux [] n1  in
      let uu____407 =
        let uu____408 = FStar_Tests_Util.app tm1 us  in norm uu____408  in
      (uu____407, us)
  
let (run_all : unit -> Prims.bool) =
  fun uu____415  ->
    FStar_Util.print_string "Testing the unifier\n";
    FStar_Options.__set_unit_tests ();
    (let unify_check n1 x1 y1 g f = unify n1 x1 y1 g f  in
     let unify1 n1 x1 y1 g = unify n1 x1 y1 g (fun uu____487  -> ())  in
     let int_t = FStar_Tests_Pars.tc "Prims.int"  in
     let x1 =
       let uu____492 =
         FStar_Syntax_Syntax.gen_bv "x" FStar_Pervasives_Native.None int_t
          in
       FStar_All.pipe_right uu____492 FStar_Syntax_Syntax.bv_to_name  in
     let y1 =
       let uu____498 =
         FStar_Syntax_Syntax.gen_bv "y" FStar_Pervasives_Native.None int_t
          in
       FStar_All.pipe_right uu____498 FStar_Syntax_Syntax.bv_to_name  in
     unify1 (Prims.parse_int "0") x1 x1 FStar_TypeChecker_Common.Trivial;
     (let uu____503 =
        let uu____504 =
          FStar_Syntax_Util.mk_eq2 FStar_Syntax_Syntax.U_zero
            FStar_Syntax_Util.t_bool x1 y1
           in
        FStar_TypeChecker_Common.NonTrivial uu____504  in
      unify1 (Prims.parse_int "1") x1 y1 uu____503);
     (let id1 = FStar_Tests_Pars.tc "fun x -> x"  in
      (let uu____507 = FStar_Tests_Util.app id1 [x1]  in
       unify1 (Prims.parse_int "2") x1 uu____507
         FStar_TypeChecker_Common.Trivial);
      (let id2 = FStar_Tests_Pars.tc "fun x -> x"  in
       unify1 (Prims.parse_int "3") id2 id2 FStar_TypeChecker_Common.Trivial;
       (let id3 = FStar_Tests_Pars.tc "fun x -> x"  in
        let id' = FStar_Tests_Pars.tc "fun y -> y"  in
        unify1 (Prims.parse_int "4") id3 id' FStar_TypeChecker_Common.Trivial;
        (let uu____516 = FStar_Tests_Pars.tc "fun x y -> x"  in
         let uu____519 = FStar_Tests_Pars.tc "fun a b -> a"  in
         unify1 (Prims.parse_int "5") uu____516 uu____519
           FStar_TypeChecker_Common.Trivial);
        (let uu____523 = FStar_Tests_Pars.tc "fun x y z -> y"  in
         let uu____526 = FStar_Tests_Pars.tc "fun a b c -> b"  in
         unify1 (Prims.parse_int "6") uu____523 uu____526
           FStar_TypeChecker_Common.Trivial);
        (let uu____530 = FStar_Tests_Pars.tc "fun (x:int) (y:int) -> y"  in
         let uu____533 = FStar_Tests_Pars.tc "fun (x:int) (y:int) -> x"  in
         let uu____536 =
           let uu____537 =
             FStar_Tests_Pars.tc "(forall (x:int). (forall (y:int). y==x))"
              in
           FStar_TypeChecker_Common.NonTrivial uu____537  in
         unify1 (Prims.parse_int "7") uu____530 uu____533 uu____536);
        (let uu____539 =
           FStar_Tests_Pars.tc "fun (x:int) (y:int) (z:int) -> y"  in
         let uu____542 =
           FStar_Tests_Pars.tc "fun (x:int) (y:int) (z:int) -> z"  in
         let uu____545 =
           let uu____546 =
             FStar_Tests_Pars.tc
               "(forall (x:int). (forall (y:int). (forall (z:int). y==z)))"
              in
           FStar_TypeChecker_Common.NonTrivial uu____546  in
         unify1 (Prims.parse_int "8") uu____539 uu____542 uu____545);
        (let uu____548 = FStar_Main.process_args ()  in
         FStar_All.pipe_right uu____548 (fun a243  -> ()));
        (let uu____561 =
           let uu____568 = FStar_Tests_Pars.tc "fun u x -> u x"  in
           inst (Prims.parse_int "1") uu____568  in
         match uu____561 with
         | (tm1,us) ->
             let sol = FStar_Tests_Pars.tc "fun x -> c_and x x"  in
             (unify_check (Prims.parse_int "9") tm1 sol
                FStar_TypeChecker_Common.Trivial
                (fun uu____581  ->
                   let uu____582 =
                     let uu____583 =
                       let uu____586 = FStar_List.hd us  in norm uu____586
                        in
                     let uu____587 = norm sol  in
                     FStar_Tests_Util.term_eq uu____583 uu____587  in
                   FStar_Tests_Util.always (Prims.parse_int "9") uu____582);
              (let uu____590 =
                 let uu____597 = FStar_Tests_Pars.tc "fun u x -> u x"  in
                 inst (Prims.parse_int "1") uu____597  in
               match uu____590 with
               | (tm2,us1) ->
                   let sol1 = FStar_Tests_Pars.tc "fun x y -> x + y"  in
                   (unify_check (Prims.parse_int "10") tm2 sol1
                      FStar_TypeChecker_Common.Trivial
                      (fun uu____610  ->
                         let uu____611 =
                           let uu____612 =
                             let uu____615 = FStar_List.hd us1  in
                             norm uu____615  in
                           let uu____616 = norm sol1  in
                           FStar_Tests_Util.term_eq uu____612 uu____616  in
                         FStar_Tests_Util.always (Prims.parse_int "10")
                           uu____611);
                    (let tm11 =
                       FStar_Tests_Pars.tc "x:int -> y:int{eq2 y x} -> bool"
                        in
                     let tm21 = FStar_Tests_Pars.tc "x:int -> y:int -> bool"
                        in
                     (let uu____622 =
                        let uu____623 =
                          FStar_Tests_Pars.tc
                            "forall (x:int). (forall (y:int). y==x)"
                           in
                        FStar_TypeChecker_Common.NonTrivial uu____623  in
                      unify1 (Prims.parse_int "11") tm11 tm21 uu____622);
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
                      (let uu____627 =
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
                           let uu____642 =
                             let uu____643 =
                               let uu____646 =
                                 FStar_Syntax_Syntax.bv_to_name q  in
                               [uu____646]  in
                             FStar_Tests_Util.app l uu____643  in
                           norm uu____642  in
                         let l1 =
                           FStar_Tests_Pars.tc "fun (p:unit -> Type0) -> p"
                            in
                         let unit = FStar_Tests_Pars.tc "()"  in
                         let env =
                           let uu____650 = FStar_Tests_Pars.init ()  in
                           let uu____651 =
                             let uu____652 = FStar_Syntax_Syntax.mk_binder x2
                                in
                             let uu____657 =
                               let uu____664 =
                                 FStar_Syntax_Syntax.mk_binder q  in
                               [uu____664]  in
                             uu____652 :: uu____657  in
                           FStar_TypeChecker_Env.push_binders uu____650
                             uu____651
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
                       match uu____627 with
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
                                   let uu____769 =
                                     let uu____776 =
                                       FStar_Syntax_Syntax.mk_binder q  in
                                     [uu____776]  in
                                   uu____764 :: uu____769  in
                                 FStar_TypeChecker_Env.push_binders uu____762
                                   uu____763
                                  in
                               let uu____793 =
                                 FStar_TypeChecker_Util.new_implicit_var ""
                                   FStar_Range.dummyRange env typ
                                  in
                               match uu____793 with
                               | (u_p,uu____815,uu____816) ->
                                   let tm24 =
                                     let uu____832 =
                                       let uu____835 =
                                         FStar_Tests_Util.app l1 [u_p]  in
                                       norm uu____835  in
                                     FStar_Tests_Util.app uu____832 [unit]
                                      in
                                   (tm14, tm24)
                                in
                             match uu____739 with
                             | (tm14,tm24) ->
                                 (unify1 (Prims.parse_int "14") tm14 tm24
                                    FStar_TypeChecker_Common.Trivial;
                                  FStar_Options.__clear_unit_tests ();
                                  (let uu____853 = FStar_ST.op_Bang success
                                      in
                                   if uu____853
                                   then
                                     FStar_Util.print_string "Unifier ok\n"
                                   else ());
                                  FStar_ST.op_Bang success))))))))))))))
  