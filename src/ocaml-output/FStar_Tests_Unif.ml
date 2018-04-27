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
             FStar_All.pipe_right uu____192 (fun a245  -> ()));
            (let uu____206 = FStar_Syntax_Print.term_to_string x1  in
             let uu____207 = FStar_Syntax_Print.term_to_string y1  in
             FStar_Util.print2 "Unify %s\nand %s\n" uu____206 uu____207);
            (let g =
               let uu____209 =
                 let uu____210 = tcenv ()  in
                 FStar_TypeChecker_Rel.teq uu____210 x1 y1  in
               let uu____211 =
                 let uu____216 = tcenv ()  in
                 FStar_TypeChecker_Rel.solve_deferred_constraints uu____216
                  in
               FStar_All.pipe_right uu____209 uu____211  in
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
          let uu____242 =
            let uu____243 = tcenv ()  in
            FStar_TypeChecker_Rel.teq uu____243 x1 y1  in
          let uu____244 =
            let uu____249 = tcenv ()  in
            FStar_TypeChecker_Rel.solve_deferred_constraints uu____249  in
          FStar_All.pipe_right uu____242 uu____244  in
        match g.FStar_TypeChecker_Env.guard_f with
        | FStar_TypeChecker_Common.Trivial  ->
            let uu____250 =
              let uu____251 = FStar_Syntax_Print.term_to_string x1  in
              let uu____252 = FStar_Syntax_Print.term_to_string y1  in
              FStar_Util.format2 "%s and %s should not be unifiable\n"
                uu____251 uu____252
               in
            fail uu____250
        | FStar_TypeChecker_Common.NonTrivial f ->
            let uu____254 = FStar_Syntax_Print.term_to_string x1  in
            let uu____255 = FStar_Syntax_Print.term_to_string y1  in
            let uu____256 = FStar_Syntax_Print.term_to_string f  in
            FStar_Util.print3 "%s and %s are unifiable if %s\n" uu____254
              uu____255 uu____256
      with | FStar_Errors.Error (e,msg,r) -> FStar_Util.print1 "%s\n" msg
  
let (unify' : Prims.string -> Prims.string -> unit) =
  fun x1  ->
    fun y1  ->
      let x2 = FStar_Tests_Pars.pars x1  in
      let y2 = FStar_Tests_Pars.pars y1  in
      let g =
        let uu____278 =
          let uu____279 = tcenv ()  in
          FStar_TypeChecker_Rel.teq uu____279 x2 y2  in
        let uu____280 =
          let uu____285 = tcenv ()  in
          FStar_TypeChecker_Rel.solve_deferred_constraints uu____285  in
        FStar_All.pipe_right uu____278 uu____280  in
      let uu____286 = FStar_Syntax_Print.term_to_string x2  in
      let uu____287 = FStar_Syntax_Print.term_to_string y2  in
      let uu____288 = guard_to_string g.FStar_TypeChecker_Env.guard_f  in
      FStar_Util.print3 "%s and %s are unifiable with guard %s\n" uu____286
        uu____287 uu____288
  
let (norm : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____294 = tcenv ()  in
    FStar_TypeChecker_Normalize.normalize [] uu____294 t
  
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
          (let uu____335 =
             let uu____348 = FStar_Tests_Pars.init ()  in
             FStar_TypeChecker_Util.new_implicit_var ""
               FStar_Range.dummyRange uu____348 FStar_Syntax_Util.ktype0
              in
           match uu____335 with
           | (t,uu____352,uu____353) ->
               let uu____366 =
                 let uu____379 = FStar_Tests_Pars.init ()  in
                 FStar_TypeChecker_Util.new_implicit_var ""
                   FStar_Range.dummyRange uu____379 t
                  in
               (match uu____366 with
                | (u,uu____383,uu____384) ->
                    aux (u :: out) (n2 - (Prims.parse_int "1"))))
         in
      let us = aux [] n1  in
      let uu____400 =
        let uu____401 = FStar_Tests_Util.app tm1 us  in norm uu____401  in
      (uu____400, us)
  
let (run_all : unit -> Prims.bool) =
  fun uu____408  ->
    FStar_Util.print_string "Testing the unifier\n";
    FStar_Options.__set_unit_tests ();
    (let unify_check n1 x1 y1 g f = unify n1 x1 y1 g f  in
     let unify1 n1 x1 y1 g = unify n1 x1 y1 g (fun uu____480  -> ())  in
     let int_t = FStar_Tests_Pars.tc "Prims.int"  in
     let x1 =
       let uu____485 =
         FStar_Syntax_Syntax.gen_bv "x" FStar_Pervasives_Native.None int_t
          in
       FStar_All.pipe_right uu____485 FStar_Syntax_Syntax.bv_to_name  in
     let y1 =
       let uu____491 =
         FStar_Syntax_Syntax.gen_bv "y" FStar_Pervasives_Native.None int_t
          in
       FStar_All.pipe_right uu____491 FStar_Syntax_Syntax.bv_to_name  in
     unify1 (Prims.parse_int "0") x1 x1 FStar_TypeChecker_Common.Trivial;
     (let uu____496 =
        let uu____497 =
          FStar_Syntax_Util.mk_eq2 FStar_Syntax_Syntax.U_zero
            FStar_Syntax_Util.t_bool x1 y1
           in
        FStar_TypeChecker_Common.NonTrivial uu____497  in
      unify1 (Prims.parse_int "1") x1 y1 uu____496);
     (let id1 = FStar_Tests_Pars.tc "fun x -> x"  in
      (let uu____500 = FStar_Tests_Util.app id1 [x1]  in
       unify1 (Prims.parse_int "2") x1 uu____500
         FStar_TypeChecker_Common.Trivial);
      (let id2 = FStar_Tests_Pars.tc "fun x -> x"  in
       unify1 (Prims.parse_int "3") id2 id2 FStar_TypeChecker_Common.Trivial;
       (let id3 = FStar_Tests_Pars.tc "fun x -> x"  in
        let id' = FStar_Tests_Pars.tc "fun y -> y"  in
        unify1 (Prims.parse_int "4") id3 id' FStar_TypeChecker_Common.Trivial;
        (let uu____509 = FStar_Tests_Pars.tc "fun x y -> x"  in
         let uu____512 = FStar_Tests_Pars.tc "fun a b -> a"  in
         unify1 (Prims.parse_int "5") uu____509 uu____512
           FStar_TypeChecker_Common.Trivial);
        (let uu____516 = FStar_Tests_Pars.tc "fun x y z -> y"  in
         let uu____519 = FStar_Tests_Pars.tc "fun a b c -> b"  in
         unify1 (Prims.parse_int "6") uu____516 uu____519
           FStar_TypeChecker_Common.Trivial);
        (let uu____523 = FStar_Tests_Pars.tc "fun (x:int) (y:int) -> y"  in
         let uu____526 = FStar_Tests_Pars.tc "fun (x:int) (y:int) -> x"  in
         let uu____529 =
           let uu____530 =
             FStar_Tests_Pars.tc "(forall (x:int). (forall (y:int). y==x))"
              in
           FStar_TypeChecker_Common.NonTrivial uu____530  in
         unify1 (Prims.parse_int "7") uu____523 uu____526 uu____529);
        (let uu____532 =
           FStar_Tests_Pars.tc "fun (x:int) (y:int) (z:int) -> y"  in
         let uu____535 =
           FStar_Tests_Pars.tc "fun (x:int) (y:int) (z:int) -> z"  in
         let uu____538 =
           let uu____539 =
             FStar_Tests_Pars.tc
               "(forall (x:int). (forall (y:int). (forall (z:int). y==z)))"
              in
           FStar_TypeChecker_Common.NonTrivial uu____539  in
         unify1 (Prims.parse_int "8") uu____532 uu____535 uu____538);
        (let uu____541 = FStar_Main.process_args ()  in
         FStar_All.pipe_right uu____541 (fun a246  -> ()));
        (let uu____554 =
           let uu____561 = FStar_Tests_Pars.tc "fun u x -> u x"  in
           inst (Prims.parse_int "1") uu____561  in
         match uu____554 with
         | (tm1,us) ->
             let sol = FStar_Tests_Pars.tc "fun x -> c_and x x"  in
             (unify_check (Prims.parse_int "9") tm1 sol
                FStar_TypeChecker_Common.Trivial
                (fun uu____574  ->
                   let uu____575 =
                     let uu____576 =
                       let uu____579 = FStar_List.hd us  in norm uu____579
                        in
                     let uu____580 = norm sol  in
                     FStar_Tests_Util.term_eq uu____576 uu____580  in
                   FStar_Tests_Util.always (Prims.parse_int "9") uu____575);
              (let uu____583 =
                 let uu____590 = FStar_Tests_Pars.tc "fun u x -> u x"  in
                 inst (Prims.parse_int "1") uu____590  in
               match uu____583 with
               | (tm2,us1) ->
                   let sol1 = FStar_Tests_Pars.tc "fun x y -> x + y"  in
                   (unify_check (Prims.parse_int "10") tm2 sol1
                      FStar_TypeChecker_Common.Trivial
                      (fun uu____603  ->
                         let uu____604 =
                           let uu____605 =
                             let uu____608 = FStar_List.hd us1  in
                             norm uu____608  in
                           let uu____609 = norm sol1  in
                           FStar_Tests_Util.term_eq uu____605 uu____609  in
                         FStar_Tests_Util.always (Prims.parse_int "10")
                           uu____604);
                    (let tm11 =
                       FStar_Tests_Pars.tc "x:int -> y:int{eq2 y x} -> bool"
                        in
                     let tm21 = FStar_Tests_Pars.tc "x:int -> y:int -> bool"
                        in
                     (let uu____615 =
                        let uu____616 =
                          FStar_Tests_Pars.tc
                            "forall (x:int). (forall (y:int). y==x)"
                           in
                        FStar_TypeChecker_Common.NonTrivial uu____616  in
                      unify1 (Prims.parse_int "11") tm11 tm21 uu____615);
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
                      (let uu____620 =
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
                           let uu____633 =
                             let uu____634 =
                               let uu____637 =
                                 FStar_Syntax_Syntax.bv_to_name q  in
                               [uu____637]  in
                             FStar_Tests_Util.app l uu____634  in
                           norm uu____633  in
                         let l1 =
                           FStar_Tests_Pars.tc "fun (p:unit -> Type0) -> p"
                            in
                         let unit = FStar_Tests_Pars.tc "()"  in
                         let env =
                           let uu____641 = FStar_Tests_Pars.init ()  in
                           let uu____642 =
                             let uu____643 = FStar_Syntax_Syntax.mk_binder x2
                                in
                             let uu____648 =
                               let uu____655 =
                                 FStar_Syntax_Syntax.mk_binder q  in
                               [uu____655]  in
                             uu____643 :: uu____648  in
                           FStar_TypeChecker_Env.push_binders uu____641
                             uu____642
                            in
                         let uu____672 =
                           FStar_TypeChecker_Util.new_implicit_var ""
                             FStar_Range.dummyRange env typ
                            in
                         match uu____672 with
                         | (u_p,uu____692,uu____693) ->
                             let tm23 =
                               let uu____709 =
                                 let uu____712 =
                                   FStar_Tests_Util.app l1 [u_p]  in
                                 norm uu____712  in
                               FStar_Tests_Util.app uu____709 [unit]  in
                             (tm13, tm23)
                          in
                       match uu____620 with
                       | (tm13,tm23) ->
                           ((let uu____722 =
                               let uu____723 =
                                 FStar_Tests_Pars.tc "Prims.l_True"  in
                               FStar_TypeChecker_Common.NonTrivial uu____723
                                in
                             unify1 (Prims.parse_int "13") tm13 tm23
                               uu____722);
                            (let uu____724 =
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
                                 let uu____737 =
                                   let uu____738 =
                                     let uu____741 =
                                       FStar_Syntax_Syntax.bv_to_name q  in
                                     [uu____741]  in
                                   FStar_Tests_Util.app l uu____738  in
                                 norm uu____737  in
                               let l1 =
                                 FStar_Tests_Pars.tc
                                   "fun (p:pure_post unit) -> p"
                                  in
                               let unit = FStar_Tests_Pars.tc "()"  in
                               let env =
                                 let uu____745 = FStar_Tests_Pars.init ()  in
                                 let uu____746 =
                                   let uu____747 =
                                     FStar_Syntax_Syntax.mk_binder x2  in
                                   let uu____752 =
                                     let uu____759 =
                                       FStar_Syntax_Syntax.mk_binder q  in
                                     [uu____759]  in
                                   uu____747 :: uu____752  in
                                 FStar_TypeChecker_Env.push_binders uu____745
                                   uu____746
                                  in
                               let uu____776 =
                                 FStar_TypeChecker_Util.new_implicit_var ""
                                   FStar_Range.dummyRange env typ
                                  in
                               match uu____776 with
                               | (u_p,uu____796,uu____797) ->
                                   let tm24 =
                                     let uu____813 =
                                       let uu____816 =
                                         FStar_Tests_Util.app l1 [u_p]  in
                                       norm uu____816  in
                                     FStar_Tests_Util.app uu____813 [unit]
                                      in
                                   (tm14, tm24)
                                in
                             match uu____724 with
                             | (tm14,tm24) ->
                                 ((let uu____826 =
                                     let uu____827 =
                                       FStar_Tests_Pars.tc "Prims.l_True"  in
                                     FStar_TypeChecker_Common.NonTrivial
                                       uu____827
                                      in
                                   unify1 (Prims.parse_int "14") tm14 tm24
                                     uu____826);
                                  FStar_Options.__clear_unit_tests ();
                                  (let uu____830 = FStar_ST.op_Bang success
                                      in
                                   if uu____830
                                   then
                                     FStar_Util.print_string "Unifier ok\n"
                                   else ());
                                  FStar_ST.op_Bang success))))))))))))))
  