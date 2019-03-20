open Prims
let (tcenv : unit -> FStar_TypeChecker_Env.env) =
  fun uu____78909  -> FStar_Tests_Pars.init () 
let (guard_to_string :
  FStar_TypeChecker_Common.guard_formula -> Prims.string) =
  fun g  ->
    match g with
    | FStar_TypeChecker_Common.Trivial  -> "trivial"
    | FStar_TypeChecker_Common.NonTrivial f ->
        let uu____78920 = tcenv ()  in
        FStar_TypeChecker_Normalize.term_to_string uu____78920 f
  
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
        let uu____78976 =
          match (g, g') with
          | (FStar_TypeChecker_Common.Trivial
             ,FStar_TypeChecker_Common.Trivial ) -> (true, g, g')
          | (FStar_TypeChecker_Common.NonTrivial
             f,FStar_TypeChecker_Common.NonTrivial f') ->
              let f1 =
                let uu____78996 = tcenv ()  in
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Env.EraseUniverses] uu____78996 f
                 in
              let f'1 =
                let uu____78998 = tcenv ()  in
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Env.EraseUniverses] uu____78998 f'
                 in
              let uu____78999 = FStar_Tests_Util.term_eq f1 f'1  in
              (uu____78999, (FStar_TypeChecker_Common.NonTrivial f1),
                (FStar_TypeChecker_Common.NonTrivial f'1))
          | uu____79002 -> (false, g, g')  in
        match uu____78976 with
        | (b,g1,g'1) ->
            (if Prims.op_Negation b
             then
               (let uu____79016 =
                  let uu____79018 = FStar_Util.string_of_int i  in
                  let uu____79020 = guard_to_string g'1  in
                  let uu____79022 = guard_to_string g1  in
                  FStar_Util.format3
                    "Test %s failed:\n\tExpected guard %s;\n\tGot guard      %s\n"
                    uu____79018 uu____79020 uu____79022
                   in
                FStar_All.pipe_left fail uu____79016)
             else ();
             (let uu____79028 = (FStar_ST.op_Bang success) && b  in
              FStar_ST.op_Colon_Equals success uu____79028))
  
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
            (let uu____79114 = FStar_Util.string_of_int i  in
             FStar_Util.print1 "%s ..." uu____79114);
            (let uu____79118 = FStar_Main.process_args ()  in
             FStar_All.pipe_right uu____79118 (fun a1  -> ()));
            (let uu____79134 = FStar_Syntax_Print.term_to_string x1  in
             let uu____79136 = FStar_Syntax_Print.term_to_string y1  in
             FStar_Util.print2 "Unify %s\nand %s\n" uu____79134 uu____79136);
            (let g =
               let uu____79140 =
                 let uu____79141 =
                   let uu____79142 = tcenv ()  in
                   FStar_TypeChecker_Rel.teq uu____79142 x1 y1  in
                 let uu____79143 =
                   let uu____79148 = tcenv ()  in
                   FStar_TypeChecker_Rel.solve_deferred_constraints
                     uu____79148
                    in
                 FStar_All.pipe_right uu____79141 uu____79143  in
               let uu____79149 =
                 let uu____79154 = tcenv ()  in
                 FStar_TypeChecker_Rel.simplify_guard uu____79154  in
               FStar_All.pipe_right uu____79140 uu____79149  in
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
        (fun uu___783_79179  ->
           match () with
           | () ->
               let g =
                 let uu____79181 =
                   let uu____79182 = tcenv ()  in
                   FStar_TypeChecker_Rel.teq uu____79182 x1 y1  in
                 let uu____79183 =
                   let uu____79188 = tcenv ()  in
                   FStar_TypeChecker_Rel.solve_deferred_constraints
                     uu____79188
                    in
                 FStar_All.pipe_right uu____79181 uu____79183  in
               (match g.FStar_TypeChecker_Env.guard_f with
                | FStar_TypeChecker_Common.Trivial  ->
                    let uu____79189 =
                      let uu____79191 = FStar_Syntax_Print.term_to_string x1
                         in
                      let uu____79193 = FStar_Syntax_Print.term_to_string y1
                         in
                      FStar_Util.format2
                        "%s and %s should not be unifiable\n" uu____79191
                        uu____79193
                       in
                    fail uu____79189
                | FStar_TypeChecker_Common.NonTrivial f ->
                    let uu____79197 = FStar_Syntax_Print.term_to_string x1
                       in
                    let uu____79199 = FStar_Syntax_Print.term_to_string y1
                       in
                    let uu____79201 = FStar_Syntax_Print.term_to_string f  in
                    FStar_Util.print3 "%s and %s are unifiable if %s\n"
                      uu____79197 uu____79199 uu____79201)) ()
      with | FStar_Errors.Error (e,msg,r) -> FStar_Util.print1 "%s\n" msg
  
let (unify' : Prims.string -> Prims.string -> unit) =
  fun x1  ->
    fun y1  ->
      let x2 = FStar_Tests_Pars.pars x1  in
      let y2 = FStar_Tests_Pars.pars y1  in
      let g =
        let uu____79233 =
          let uu____79234 = tcenv ()  in
          FStar_TypeChecker_Rel.teq uu____79234 x2 y2  in
        let uu____79235 =
          let uu____79240 = tcenv ()  in
          FStar_TypeChecker_Rel.solve_deferred_constraints uu____79240  in
        FStar_All.pipe_right uu____79233 uu____79235  in
      let uu____79241 = FStar_Syntax_Print.term_to_string x2  in
      let uu____79243 = FStar_Syntax_Print.term_to_string y2  in
      let uu____79245 = guard_to_string g.FStar_TypeChecker_Env.guard_f  in
      FStar_Util.print3 "%s and %s are unifiable with guard %s\n" uu____79241
        uu____79243 uu____79245
  
let (norm : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____79254 = tcenv ()  in
    FStar_TypeChecker_Normalize.normalize [] uu____79254 t
  
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
          (let uu____79304 =
             let uu____79317 = FStar_Tests_Pars.init ()  in
             FStar_TypeChecker_Util.new_implicit_var ""
               FStar_Range.dummyRange uu____79317 FStar_Syntax_Util.ktype0
              in
           match uu____79304 with
           | (t,uu____79322,uu____79323) ->
               let uu____79336 =
                 let uu____79349 = FStar_Tests_Pars.init ()  in
                 FStar_TypeChecker_Util.new_implicit_var ""
                   FStar_Range.dummyRange uu____79349 t
                  in
               (match uu____79336 with
                | (u,uu____79354,uu____79355) ->
                    aux (u :: out) (n2 - (Prims.parse_int "1"))))
         in
      let us = aux [] n1  in
      let uu____79372 =
        let uu____79373 = FStar_Tests_Util.app tm1 us  in norm uu____79373
         in
      (uu____79372, us)
  
let (run_all : unit -> Prims.bool) =
  fun uu____79382  ->
    FStar_Util.print_string "Testing the unifier\n";
    FStar_Options.__set_unit_tests ();
    (let unify_check n1 x1 y1 g f = unify n1 x1 y1 g f  in
     let unify1 n1 x1 y1 g = unify n1 x1 y1 g (fun uu____79459  -> ())  in
     let int_t = FStar_Tests_Pars.tc "Prims.int"  in
     let x1 =
       let uu____79465 =
         FStar_Syntax_Syntax.gen_bv "x" FStar_Pervasives_Native.None int_t
          in
       FStar_All.pipe_right uu____79465 FStar_Syntax_Syntax.bv_to_name  in
     let y1 =
       let uu____79472 =
         FStar_Syntax_Syntax.gen_bv "y" FStar_Pervasives_Native.None int_t
          in
       FStar_All.pipe_right uu____79472 FStar_Syntax_Syntax.bv_to_name  in
     unify1 (Prims.parse_int "0") x1 x1 FStar_TypeChecker_Common.Trivial;
     (let uu____79479 =
        let uu____79480 =
          FStar_Syntax_Util.mk_eq2 FStar_Syntax_Syntax.U_zero
            FStar_Syntax_Util.t_bool x1 y1
           in
        FStar_TypeChecker_Common.NonTrivial uu____79480  in
      unify1 (Prims.parse_int "1") x1 y1 uu____79479);
     (let id1 = FStar_Tests_Pars.tc "fun x -> x"  in
      (let uu____79485 = FStar_Tests_Util.app id1 [x1]  in
       unify1 (Prims.parse_int "2") x1 uu____79485
         FStar_TypeChecker_Common.Trivial);
      (let id2 = FStar_Tests_Pars.tc "fun x -> x"  in
       unify1 (Prims.parse_int "3") id2 id2 FStar_TypeChecker_Common.Trivial;
       (let id3 = FStar_Tests_Pars.tc "fun x -> x"  in
        let id' = FStar_Tests_Pars.tc "fun y -> y"  in
        unify1 (Prims.parse_int "4") id3 id' FStar_TypeChecker_Common.Trivial;
        (let uu____79500 = FStar_Tests_Pars.tc "fun x y -> x"  in
         let uu____79504 = FStar_Tests_Pars.tc "fun a b -> a"  in
         unify1 (Prims.parse_int "5") uu____79500 uu____79504
           FStar_TypeChecker_Common.Trivial);
        (let uu____79510 = FStar_Tests_Pars.tc "fun x y z -> y"  in
         let uu____79514 = FStar_Tests_Pars.tc "fun a b c -> b"  in
         unify1 (Prims.parse_int "6") uu____79510 uu____79514
           FStar_TypeChecker_Common.Trivial);
        (let uu____79520 = FStar_Tests_Pars.tc "fun (x:int) (y:int) -> y"  in
         let uu____79524 = FStar_Tests_Pars.tc "fun (x:int) (y:int) -> x"  in
         let uu____79528 =
           let uu____79529 =
             FStar_Tests_Pars.tc "(forall (x:int). (forall (y:int). y==x))"
              in
           FStar_TypeChecker_Common.NonTrivial uu____79529  in
         unify1 (Prims.parse_int "7") uu____79520 uu____79524 uu____79528);
        (let uu____79533 =
           FStar_Tests_Pars.tc "fun (x:int) (y:int) (z:int) -> y"  in
         let uu____79537 =
           FStar_Tests_Pars.tc "fun (x:int) (y:int) (z:int) -> z"  in
         let uu____79541 =
           let uu____79542 =
             FStar_Tests_Pars.tc
               "(forall (x:int). (forall (y:int). (forall (z:int). y==z)))"
              in
           FStar_TypeChecker_Common.NonTrivial uu____79542  in
         unify1 (Prims.parse_int "8") uu____79533 uu____79537 uu____79541);
        (let uu____79546 = FStar_Main.process_args ()  in
         FStar_All.pipe_right uu____79546 (fun a2  -> ()));
        (let uu____79561 =
           let uu____79568 = FStar_Tests_Pars.tc "fun u x -> u x"  in
           inst (Prims.parse_int "1") uu____79568  in
         match uu____79561 with
         | (tm1,us) ->
             let sol = FStar_Tests_Pars.tc "fun x -> c_and x x"  in
             (unify_check (Prims.parse_int "9") tm1 sol
                FStar_TypeChecker_Common.Trivial
                (fun uu____79586  ->
                   let uu____79587 =
                     let uu____79589 =
                       let uu____79592 = FStar_List.hd us  in
                       norm uu____79592  in
                     let uu____79593 = norm sol  in
                     FStar_Tests_Util.term_eq uu____79589 uu____79593  in
                   FStar_Tests_Util.always (Prims.parse_int "9") uu____79587);
              (let uu____79597 =
                 let uu____79604 = FStar_Tests_Pars.tc "fun u x -> u x"  in
                 inst (Prims.parse_int "1") uu____79604  in
               match uu____79597 with
               | (tm2,us1) ->
                   let sol1 = FStar_Tests_Pars.tc "fun x y -> x + y"  in
                   (unify_check (Prims.parse_int "10") tm2 sol1
                      FStar_TypeChecker_Common.Trivial
                      (fun uu____79622  ->
                         let uu____79623 =
                           let uu____79625 =
                             let uu____79628 = FStar_List.hd us1  in
                             norm uu____79628  in
                           let uu____79629 = norm sol1  in
                           FStar_Tests_Util.term_eq uu____79625 uu____79629
                            in
                         FStar_Tests_Util.always (Prims.parse_int "10")
                           uu____79623);
                    (let tm11 =
                       FStar_Tests_Pars.tc "x:int -> y:int{eq2 y x} -> bool"
                        in
                     let tm21 = FStar_Tests_Pars.tc "x:int -> y:int -> bool"
                        in
                     (let uu____79638 =
                        let uu____79639 =
                          FStar_Tests_Pars.tc
                            "forall (x:int). (forall (y:int). y==x)"
                           in
                        FStar_TypeChecker_Common.NonTrivial uu____79639  in
                      unify1 (Prims.parse_int "11") tm11 tm21 uu____79638);
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
                      (let uu____79648 =
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
                           let uu____79666 =
                             let uu____79667 =
                               let uu____79670 =
                                 FStar_Syntax_Syntax.bv_to_name q  in
                               [uu____79670]  in
                             FStar_Tests_Util.app l uu____79667  in
                           norm uu____79666  in
                         let l1 =
                           FStar_Tests_Pars.tc "fun (p:unit -> Type0) -> p"
                            in
                         let unit = FStar_Tests_Pars.tc "()"  in
                         let env =
                           let uu____79676 = FStar_Tests_Pars.init ()  in
                           let uu____79677 =
                             let uu____79678 =
                               FStar_Syntax_Syntax.mk_binder x2  in
                             let uu____79685 =
                               let uu____79694 =
                                 FStar_Syntax_Syntax.mk_binder q  in
                               [uu____79694]  in
                             uu____79678 :: uu____79685  in
                           FStar_TypeChecker_Env.push_binders uu____79676
                             uu____79677
                            in
                         let uu____79719 =
                           FStar_TypeChecker_Util.new_implicit_var ""
                             FStar_Range.dummyRange env typ
                            in
                         match uu____79719 with
                         | (u_p,uu____79742,uu____79743) ->
                             let tm23 =
                               let uu____79759 =
                                 let uu____79762 =
                                   FStar_Tests_Util.app l1 [u_p]  in
                                 norm uu____79762  in
                               FStar_Tests_Util.app uu____79759 [unit]  in
                             (tm13, tm23)
                          in
                       match uu____79648 with
                       | (tm13,tm23) ->
                           (unify1 (Prims.parse_int "13") tm13 tm23
                              FStar_TypeChecker_Common.Trivial;
                            (let uu____79780 =
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
                                 let uu____79798 =
                                   let uu____79799 =
                                     let uu____79802 =
                                       FStar_Syntax_Syntax.bv_to_name q  in
                                     [uu____79802]  in
                                   FStar_Tests_Util.app l uu____79799  in
                                 norm uu____79798  in
                               let l1 =
                                 FStar_Tests_Pars.tc
                                   "fun (p:pure_post unit) -> p"
                                  in
                               let unit = FStar_Tests_Pars.tc "()"  in
                               let env =
                                 let uu____79808 = FStar_Tests_Pars.init ()
                                    in
                                 let uu____79809 =
                                   let uu____79810 =
                                     FStar_Syntax_Syntax.mk_binder x2  in
                                   let uu____79817 =
                                     let uu____79826 =
                                       FStar_Syntax_Syntax.mk_binder q  in
                                     [uu____79826]  in
                                   uu____79810 :: uu____79817  in
                                 FStar_TypeChecker_Env.push_binders
                                   uu____79808 uu____79809
                                  in
                               let uu____79851 =
                                 FStar_TypeChecker_Util.new_implicit_var ""
                                   FStar_Range.dummyRange env typ
                                  in
                               match uu____79851 with
                               | (u_p,uu____79874,uu____79875) ->
                                   let tm24 =
                                     let uu____79891 =
                                       let uu____79894 =
                                         FStar_Tests_Util.app l1 [u_p]  in
                                       norm uu____79894  in
                                     FStar_Tests_Util.app uu____79891 [unit]
                                      in
                                   (tm14, tm24)
                                in
                             match uu____79780 with
                             | (tm14,tm24) ->
                                 (unify1 (Prims.parse_int "14") tm14 tm24
                                    FStar_TypeChecker_Common.Trivial;
                                  FStar_Options.__clear_unit_tests ();
                                  (let uu____79914 = FStar_ST.op_Bang success
                                      in
                                   if uu____79914
                                   then
                                     FStar_Util.print_string "Unifier ok\n"
                                   else ());
                                  FStar_ST.op_Bang success))))))))))))))
  