open Prims
let (tcenv : unit -> FStar_TypeChecker_Env.env) =
  fun uu____5  -> FStar_Tests_Pars.init () 
let (guard_to_string :
  FStar_TypeChecker_Common.guard_formula -> Prims.string) =
  fun g  ->
    match g with
    | FStar_TypeChecker_Common.Trivial  -> "trivial"
    | FStar_TypeChecker_Common.NonTrivial f ->
        let uu____16 = tcenv ()  in
        FStar_TypeChecker_Normalize.term_to_string uu____16 f
  
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
        let uu____83 =
          match (g, g') with
          | (FStar_TypeChecker_Common.Trivial
             ,FStar_TypeChecker_Common.Trivial ) -> (true, g, g')
          | (FStar_TypeChecker_Common.NonTrivial
             f,FStar_TypeChecker_Common.NonTrivial f') ->
              let f1 =
                let uu____103 = tcenv ()  in
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Env.EraseUniverses] uu____103 f
                 in
              let f'1 =
                let uu____105 = tcenv ()  in
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Env.EraseUniverses] uu____105 f'
                 in
              let uu____106 = FStar_Tests_Util.term_eq f1 f'1  in
              (uu____106, (FStar_TypeChecker_Common.NonTrivial f1),
                (FStar_TypeChecker_Common.NonTrivial f'1))
          | uu____109 -> (false, g, g')  in
        match uu____83 with
        | (b,g1,g'1) ->
            (if Prims.op_Negation b
             then
               (let uu____123 =
                  let uu____125 = FStar_Util.string_of_int i  in
                  let uu____127 = guard_to_string g'1  in
                  let uu____129 = guard_to_string g1  in
                  FStar_Util.format3
                    "Test %s failed:\n\tExpected guard %s;\n\tGot guard      %s\n"
                    uu____125 uu____127 uu____129
                   in
                FStar_All.pipe_left fail uu____123)
             else ();
             (let uu____135 = (FStar_ST.op_Bang success) && b  in
              FStar_ST.op_Colon_Equals success uu____135))
  
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
            (let uu____221 = FStar_Util.string_of_int i  in
             FStar_Util.print1 "%s ..." uu____221);
            (let uu____225 = FStar_Main.process_args ()  in
             FStar_All.pipe_right uu____225 (fun a1  -> ()));
            (let uu____241 = FStar_Syntax_Print.term_to_string x1  in
             let uu____243 = FStar_Syntax_Print.term_to_string y1  in
             FStar_Util.print2 "Unify %s\nand %s\n" uu____241 uu____243);
            (let g =
               let uu____247 =
                 let uu____248 =
                   let uu____249 = tcenv ()  in
                   FStar_TypeChecker_Rel.teq uu____249 x1 y1  in
                 let uu____250 =
                   let uu____255 = tcenv ()  in
                   FStar_TypeChecker_Rel.solve_deferred_constraints uu____255
                    in
                 FStar_All.pipe_right uu____248 uu____250  in
               let uu____256 =
                 let uu____261 = tcenv ()  in
                 FStar_TypeChecker_Rel.simplify_guard uu____261  in
               FStar_All.pipe_right uu____247 uu____256  in
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
        (fun uu___481_286  ->
           match () with
           | () ->
               let g =
                 let uu____288 =
                   let uu____289 = tcenv ()  in
                   FStar_TypeChecker_Rel.teq uu____289 x1 y1  in
                 let uu____290 =
                   let uu____295 = tcenv ()  in
                   FStar_TypeChecker_Rel.solve_deferred_constraints uu____295
                    in
                 FStar_All.pipe_right uu____288 uu____290  in
               (match g.FStar_TypeChecker_Env.guard_f with
                | FStar_TypeChecker_Common.Trivial  ->
                    let uu____296 =
                      let uu____298 = FStar_Syntax_Print.term_to_string x1
                         in
                      let uu____300 = FStar_Syntax_Print.term_to_string y1
                         in
                      FStar_Util.format2
                        "%s and %s should not be unifiable\n" uu____298
                        uu____300
                       in
                    fail uu____296
                | FStar_TypeChecker_Common.NonTrivial f ->
                    let uu____304 = FStar_Syntax_Print.term_to_string x1  in
                    let uu____306 = FStar_Syntax_Print.term_to_string y1  in
                    let uu____308 = FStar_Syntax_Print.term_to_string f  in
                    FStar_Util.print3 "%s and %s are unifiable if %s\n"
                      uu____304 uu____306 uu____308)) ()
      with | FStar_Errors.Error (e,msg,r) -> FStar_Util.print1 "%s\n" msg
  
let (unify' : Prims.string -> Prims.string -> unit) =
  fun x1  ->
    fun y1  ->
      let x2 = FStar_Tests_Pars.pars x1  in
      let y2 = FStar_Tests_Pars.pars y1  in
      let g =
        let uu____340 =
          let uu____341 = tcenv ()  in
          FStar_TypeChecker_Rel.teq uu____341 x2 y2  in
        let uu____342 =
          let uu____347 = tcenv ()  in
          FStar_TypeChecker_Rel.solve_deferred_constraints uu____347  in
        FStar_All.pipe_right uu____340 uu____342  in
      let uu____348 = FStar_Syntax_Print.term_to_string x2  in
      let uu____350 = FStar_Syntax_Print.term_to_string y2  in
      let uu____352 = guard_to_string g.FStar_TypeChecker_Env.guard_f  in
      FStar_Util.print3 "%s and %s are unifiable with guard %s\n" uu____348
        uu____350 uu____352
  
let (norm : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____361 = tcenv ()  in
    FStar_TypeChecker_Normalize.normalize [] uu____361 t
  
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
          (let uu____411 =
             let uu____424 = FStar_Tests_Pars.init ()  in
             FStar_TypeChecker_Util.new_implicit_var ""
               FStar_Range.dummyRange uu____424 FStar_Syntax_Util.ktype0
              in
           match uu____411 with
           | (t,uu____429,uu____430) ->
               let uu____443 =
                 let uu____456 = FStar_Tests_Pars.init ()  in
                 FStar_TypeChecker_Util.new_implicit_var ""
                   FStar_Range.dummyRange uu____456 t
                  in
               (match uu____443 with
                | (u,uu____461,uu____462) ->
                    aux (u :: out) (n2 - (Prims.parse_int "1"))))
         in
      let us = aux [] n1  in
      let uu____479 =
        let uu____480 = FStar_Tests_Util.app tm1 us  in norm uu____480  in
      (uu____479, us)
  
let (run_all : unit -> Prims.bool) =
  fun uu____489  ->
    FStar_Util.print_string "Testing the unifier\n";
    FStar_Options.__set_unit_tests ();
    (let unify_check n1 x1 y1 g f = unify n1 x1 y1 g f  in
     let unify1 n1 x1 y1 g = unify n1 x1 y1 g (fun uu____566  -> ())  in
     let int_t = FStar_Tests_Pars.tc "Prims.int"  in
     let x1 =
       let uu____572 =
         FStar_Syntax_Syntax.gen_bv "x" FStar_Pervasives_Native.None int_t
          in
       FStar_All.pipe_right uu____572 FStar_Syntax_Syntax.bv_to_name  in
     let y1 =
       let uu____579 =
         FStar_Syntax_Syntax.gen_bv "y" FStar_Pervasives_Native.None int_t
          in
       FStar_All.pipe_right uu____579 FStar_Syntax_Syntax.bv_to_name  in
     unify1 (Prims.parse_int "0") x1 x1 FStar_TypeChecker_Common.Trivial;
     (let uu____586 =
        let uu____587 =
          FStar_Syntax_Util.mk_eq2 FStar_Syntax_Syntax.U_zero
            FStar_Syntax_Util.t_bool x1 y1
           in
        FStar_TypeChecker_Common.NonTrivial uu____587  in
      unify1 (Prims.parse_int "1") x1 y1 uu____586);
     (let id1 = FStar_Tests_Pars.tc "fun x -> x"  in
      (let uu____592 = FStar_Tests_Util.app id1 [x1]  in
       unify1 (Prims.parse_int "2") x1 uu____592
         FStar_TypeChecker_Common.Trivial);
      (let id2 = FStar_Tests_Pars.tc "fun x -> x"  in
       unify1 (Prims.parse_int "3") id2 id2 FStar_TypeChecker_Common.Trivial;
       (let id3 = FStar_Tests_Pars.tc "fun x -> x"  in
        let id' = FStar_Tests_Pars.tc "fun y -> y"  in
        unify1 (Prims.parse_int "4") id3 id' FStar_TypeChecker_Common.Trivial;
        (let uu____607 = FStar_Tests_Pars.tc "fun x y -> x"  in
         let uu____611 = FStar_Tests_Pars.tc "fun a b -> a"  in
         unify1 (Prims.parse_int "5") uu____607 uu____611
           FStar_TypeChecker_Common.Trivial);
        (let uu____617 = FStar_Tests_Pars.tc "fun x y z -> y"  in
         let uu____621 = FStar_Tests_Pars.tc "fun a b c -> b"  in
         unify1 (Prims.parse_int "6") uu____617 uu____621
           FStar_TypeChecker_Common.Trivial);
        (let uu____627 = FStar_Tests_Pars.tc "fun (x:int) (y:int) -> y"  in
         let uu____631 = FStar_Tests_Pars.tc "fun (x:int) (y:int) -> x"  in
         let uu____635 =
           let uu____636 =
             FStar_Tests_Pars.tc "(forall (x:int). (forall (y:int). y==x))"
              in
           FStar_TypeChecker_Common.NonTrivial uu____636  in
         unify1 (Prims.parse_int "7") uu____627 uu____631 uu____635);
        (let uu____640 =
           FStar_Tests_Pars.tc "fun (x:int) (y:int) (z:int) -> y"  in
         let uu____644 =
           FStar_Tests_Pars.tc "fun (x:int) (y:int) (z:int) -> z"  in
         let uu____648 =
           let uu____649 =
             FStar_Tests_Pars.tc
               "(forall (x:int). (forall (y:int). (forall (z:int). y==z)))"
              in
           FStar_TypeChecker_Common.NonTrivial uu____649  in
         unify1 (Prims.parse_int "8") uu____640 uu____644 uu____648);
        (let uu____653 = FStar_Main.process_args ()  in
         FStar_All.pipe_right uu____653 (fun a2  -> ()));
        (let uu____668 =
           let uu____675 = FStar_Tests_Pars.tc "fun u x -> u x"  in
           inst (Prims.parse_int "1") uu____675  in
         match uu____668 with
         | (tm1,us) ->
             let sol = FStar_Tests_Pars.tc "fun x -> c_and x x"  in
             (unify_check (Prims.parse_int "9") tm1 sol
                FStar_TypeChecker_Common.Trivial
                (fun uu____693  ->
                   let uu____694 =
                     let uu____696 =
                       let uu____699 = FStar_List.hd us  in norm uu____699
                        in
                     let uu____700 = norm sol  in
                     FStar_Tests_Util.term_eq uu____696 uu____700  in
                   FStar_Tests_Util.always (Prims.parse_int "9") uu____694);
              (let uu____704 =
                 let uu____711 = FStar_Tests_Pars.tc "fun u x -> u x"  in
                 inst (Prims.parse_int "1") uu____711  in
               match uu____704 with
               | (tm2,us1) ->
                   let sol1 = FStar_Tests_Pars.tc "fun x y -> x + y"  in
                   (unify_check (Prims.parse_int "10") tm2 sol1
                      FStar_TypeChecker_Common.Trivial
                      (fun uu____729  ->
                         let uu____730 =
                           let uu____732 =
                             let uu____735 = FStar_List.hd us1  in
                             norm uu____735  in
                           let uu____736 = norm sol1  in
                           FStar_Tests_Util.term_eq uu____732 uu____736  in
                         FStar_Tests_Util.always (Prims.parse_int "10")
                           uu____730);
                    (let tm11 =
                       FStar_Tests_Pars.tc "x:int -> y:int{eq2 y x} -> bool"
                        in
                     let tm21 = FStar_Tests_Pars.tc "x:int -> y:int -> bool"
                        in
                     (let uu____745 =
                        let uu____746 =
                          FStar_Tests_Pars.tc
                            "forall (x:int). (forall (y:int). y==x)"
                           in
                        FStar_TypeChecker_Common.NonTrivial uu____746  in
                      unify1 (Prims.parse_int "11") tm11 tm21 uu____745);
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
                      (let uu____755 =
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
                           let uu____773 =
                             let uu____774 =
                               let uu____777 =
                                 FStar_Syntax_Syntax.bv_to_name q  in
                               [uu____777]  in
                             FStar_Tests_Util.app l uu____774  in
                           norm uu____773  in
                         let l1 =
                           FStar_Tests_Pars.tc "fun (p:unit -> Type0) -> p"
                            in
                         let unit = FStar_Tests_Pars.tc "()"  in
                         let env =
                           let uu____783 = FStar_Tests_Pars.init ()  in
                           let uu____784 =
                             let uu____785 = FStar_Syntax_Syntax.mk_binder x2
                                in
                             let uu____792 =
                               let uu____801 =
                                 FStar_Syntax_Syntax.mk_binder q  in
                               [uu____801]  in
                             uu____785 :: uu____792  in
                           FStar_TypeChecker_Env.push_binders uu____783
                             uu____784
                            in
                         let uu____826 =
                           FStar_TypeChecker_Util.new_implicit_var ""
                             FStar_Range.dummyRange env typ
                            in
                         match uu____826 with
                         | (u_p,uu____849,uu____850) ->
                             let tm23 =
                               let uu____866 =
                                 let uu____869 =
                                   FStar_Tests_Util.app l1 [u_p]  in
                                 norm uu____869  in
                               FStar_Tests_Util.app uu____866 [unit]  in
                             (tm13, tm23)
                          in
                       match uu____755 with
                       | (tm13,tm23) ->
                           (unify1 (Prims.parse_int "13") tm13 tm23
                              FStar_TypeChecker_Common.Trivial;
                            (let uu____887 =
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
                                 let uu____905 =
                                   let uu____906 =
                                     let uu____909 =
                                       FStar_Syntax_Syntax.bv_to_name q  in
                                     [uu____909]  in
                                   FStar_Tests_Util.app l uu____906  in
                                 norm uu____905  in
                               let l1 =
                                 FStar_Tests_Pars.tc
                                   "fun (p:pure_post unit) -> p"
                                  in
                               let unit = FStar_Tests_Pars.tc "()"  in
                               let env =
                                 let uu____915 = FStar_Tests_Pars.init ()  in
                                 let uu____916 =
                                   let uu____917 =
                                     FStar_Syntax_Syntax.mk_binder x2  in
                                   let uu____924 =
                                     let uu____933 =
                                       FStar_Syntax_Syntax.mk_binder q  in
                                     [uu____933]  in
                                   uu____917 :: uu____924  in
                                 FStar_TypeChecker_Env.push_binders uu____915
                                   uu____916
                                  in
                               let uu____958 =
                                 FStar_TypeChecker_Util.new_implicit_var ""
                                   FStar_Range.dummyRange env typ
                                  in
                               match uu____958 with
                               | (u_p,uu____981,uu____982) ->
                                   let tm24 =
                                     let uu____998 =
                                       let uu____1001 =
                                         FStar_Tests_Util.app l1 [u_p]  in
                                       norm uu____1001  in
                                     FStar_Tests_Util.app uu____998 [unit]
                                      in
                                   (tm14, tm24)
                                in
                             match uu____887 with
                             | (tm14,tm24) ->
                                 (unify1 (Prims.parse_int "14") tm14 tm24
                                    FStar_TypeChecker_Common.Trivial;
                                  FStar_Options.__clear_unit_tests ();
                                  (let uu____1021 = FStar_ST.op_Bang success
                                      in
                                   if uu____1021
                                   then
                                     FStar_Util.print_string "Unifier ok\n"
                                   else ());
                                  FStar_ST.op_Bang success))))))))))))))
  