open Prims
let (tcenv : unit -> FStar_TypeChecker_Env.env) =
  fun uu____78800  -> FStar_Tests_Pars.init () 
let (guard_to_string :
  FStar_TypeChecker_Common.guard_formula -> Prims.string) =
  fun g  ->
    match g with
    | FStar_TypeChecker_Common.Trivial  -> "trivial"
    | FStar_TypeChecker_Common.NonTrivial f ->
        let uu____78811 = tcenv ()  in
        FStar_TypeChecker_Normalize.term_to_string uu____78811 f
  
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
        let uu____78867 =
          match (g, g') with
          | (FStar_TypeChecker_Common.Trivial
             ,FStar_TypeChecker_Common.Trivial ) -> (true, g, g')
          | (FStar_TypeChecker_Common.NonTrivial
             f,FStar_TypeChecker_Common.NonTrivial f') ->
              let f1 =
                let uu____78887 = tcenv ()  in
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Env.EraseUniverses] uu____78887 f
                 in
              let f'1 =
                let uu____78889 = tcenv ()  in
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Env.EraseUniverses] uu____78889 f'
                 in
              let uu____78890 = FStar_Tests_Util.term_eq f1 f'1  in
              (uu____78890, (FStar_TypeChecker_Common.NonTrivial f1),
                (FStar_TypeChecker_Common.NonTrivial f'1))
          | uu____78893 -> (false, g, g')  in
        match uu____78867 with
        | (b,g1,g'1) ->
            (if Prims.op_Negation b
             then
               (let uu____78907 =
                  let uu____78909 = FStar_Util.string_of_int i  in
                  let uu____78911 = guard_to_string g'1  in
                  let uu____78913 = guard_to_string g1  in
                  FStar_Util.format3
                    "Test %s failed:\n\tExpected guard %s;\n\tGot guard      %s\n"
                    uu____78909 uu____78911 uu____78913
                   in
                FStar_All.pipe_left fail uu____78907)
             else ();
             (let uu____78919 = (FStar_ST.op_Bang success) && b  in
              FStar_ST.op_Colon_Equals success uu____78919))
  
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
            (let uu____79005 = FStar_Util.string_of_int i  in
             FStar_Util.print1 "%s ..." uu____79005);
            (let uu____79009 = FStar_Main.process_args ()  in
             FStar_All.pipe_right uu____79009 (fun a1  -> ()));
            (let uu____79025 = FStar_Syntax_Print.term_to_string x1  in
             let uu____79027 = FStar_Syntax_Print.term_to_string y1  in
             FStar_Util.print2 "Unify %s\nand %s\n" uu____79025 uu____79027);
            (let g =
               let uu____79031 =
                 let uu____79032 =
                   let uu____79033 = tcenv ()  in
                   FStar_TypeChecker_Rel.teq uu____79033 x1 y1  in
                 let uu____79034 =
                   let uu____79039 = tcenv ()  in
                   FStar_TypeChecker_Rel.solve_deferred_constraints
                     uu____79039
                    in
                 FStar_All.pipe_right uu____79032 uu____79034  in
               let uu____79040 =
                 let uu____79045 = tcenv ()  in
                 FStar_TypeChecker_Rel.simplify_guard uu____79045  in
               FStar_All.pipe_right uu____79031 uu____79040  in
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
        (fun uu___783_79070  ->
           match () with
           | () ->
               let g =
                 let uu____79072 =
                   let uu____79073 = tcenv ()  in
                   FStar_TypeChecker_Rel.teq uu____79073 x1 y1  in
                 let uu____79074 =
                   let uu____79079 = tcenv ()  in
                   FStar_TypeChecker_Rel.solve_deferred_constraints
                     uu____79079
                    in
                 FStar_All.pipe_right uu____79072 uu____79074  in
               (match g.FStar_TypeChecker_Env.guard_f with
                | FStar_TypeChecker_Common.Trivial  ->
                    let uu____79080 =
                      let uu____79082 = FStar_Syntax_Print.term_to_string x1
                         in
                      let uu____79084 = FStar_Syntax_Print.term_to_string y1
                         in
                      FStar_Util.format2
                        "%s and %s should not be unifiable\n" uu____79082
                        uu____79084
                       in
                    fail uu____79080
                | FStar_TypeChecker_Common.NonTrivial f ->
                    let uu____79088 = FStar_Syntax_Print.term_to_string x1
                       in
                    let uu____79090 = FStar_Syntax_Print.term_to_string y1
                       in
                    let uu____79092 = FStar_Syntax_Print.term_to_string f  in
                    FStar_Util.print3 "%s and %s are unifiable if %s\n"
                      uu____79088 uu____79090 uu____79092)) ()
      with | FStar_Errors.Error (e,msg,r) -> FStar_Util.print1 "%s\n" msg
  
let (unify' : Prims.string -> Prims.string -> unit) =
  fun x1  ->
    fun y1  ->
      let x2 = FStar_Tests_Pars.pars x1  in
      let y2 = FStar_Tests_Pars.pars y1  in
      let g =
        let uu____79124 =
          let uu____79125 = tcenv ()  in
          FStar_TypeChecker_Rel.teq uu____79125 x2 y2  in
        let uu____79126 =
          let uu____79131 = tcenv ()  in
          FStar_TypeChecker_Rel.solve_deferred_constraints uu____79131  in
        FStar_All.pipe_right uu____79124 uu____79126  in
      let uu____79132 = FStar_Syntax_Print.term_to_string x2  in
      let uu____79134 = FStar_Syntax_Print.term_to_string y2  in
      let uu____79136 = guard_to_string g.FStar_TypeChecker_Env.guard_f  in
      FStar_Util.print3 "%s and %s are unifiable with guard %s\n" uu____79132
        uu____79134 uu____79136
  
let (norm : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____79145 = tcenv ()  in
    FStar_TypeChecker_Normalize.normalize [] uu____79145 t
  
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
          (let uu____79195 =
             let uu____79208 = FStar_Tests_Pars.init ()  in
             FStar_TypeChecker_Util.new_implicit_var ""
               FStar_Range.dummyRange uu____79208 FStar_Syntax_Util.ktype0
              in
           match uu____79195 with
           | (t,uu____79213,uu____79214) ->
               let uu____79227 =
                 let uu____79240 = FStar_Tests_Pars.init ()  in
                 FStar_TypeChecker_Util.new_implicit_var ""
                   FStar_Range.dummyRange uu____79240 t
                  in
               (match uu____79227 with
                | (u,uu____79245,uu____79246) ->
                    aux (u :: out) (n2 - (Prims.parse_int "1"))))
         in
      let us = aux [] n1  in
      let uu____79263 =
        let uu____79264 = FStar_Tests_Util.app tm1 us  in norm uu____79264
         in
      (uu____79263, us)
  
let (run_all : unit -> Prims.bool) =
  fun uu____79273  ->
    FStar_Util.print_string "Testing the unifier\n";
    FStar_Options.__set_unit_tests ();
    (let unify_check n1 x1 y1 g f = unify n1 x1 y1 g f  in
     let unify1 n1 x1 y1 g = unify n1 x1 y1 g (fun uu____79350  -> ())  in
     let int_t = FStar_Tests_Pars.tc "Prims.int"  in
     let x1 =
       let uu____79356 =
         FStar_Syntax_Syntax.gen_bv "x" FStar_Pervasives_Native.None int_t
          in
       FStar_All.pipe_right uu____79356 FStar_Syntax_Syntax.bv_to_name  in
     let y1 =
       let uu____79363 =
         FStar_Syntax_Syntax.gen_bv "y" FStar_Pervasives_Native.None int_t
          in
       FStar_All.pipe_right uu____79363 FStar_Syntax_Syntax.bv_to_name  in
     unify1 (Prims.parse_int "0") x1 x1 FStar_TypeChecker_Common.Trivial;
     (let uu____79370 =
        let uu____79371 =
          FStar_Syntax_Util.mk_eq2 FStar_Syntax_Syntax.U_zero
            FStar_Syntax_Util.t_bool x1 y1
           in
        FStar_TypeChecker_Common.NonTrivial uu____79371  in
      unify1 (Prims.parse_int "1") x1 y1 uu____79370);
     (let id1 = FStar_Tests_Pars.tc "fun x -> x"  in
      (let uu____79376 = FStar_Tests_Util.app id1 [x1]  in
       unify1 (Prims.parse_int "2") x1 uu____79376
         FStar_TypeChecker_Common.Trivial);
      (let id2 = FStar_Tests_Pars.tc "fun x -> x"  in
       unify1 (Prims.parse_int "3") id2 id2 FStar_TypeChecker_Common.Trivial;
       (let id3 = FStar_Tests_Pars.tc "fun x -> x"  in
        let id' = FStar_Tests_Pars.tc "fun y -> y"  in
        unify1 (Prims.parse_int "4") id3 id' FStar_TypeChecker_Common.Trivial;
        (let uu____79391 = FStar_Tests_Pars.tc "fun x y -> x"  in
         let uu____79395 = FStar_Tests_Pars.tc "fun a b -> a"  in
         unify1 (Prims.parse_int "5") uu____79391 uu____79395
           FStar_TypeChecker_Common.Trivial);
        (let uu____79401 = FStar_Tests_Pars.tc "fun x y z -> y"  in
         let uu____79405 = FStar_Tests_Pars.tc "fun a b c -> b"  in
         unify1 (Prims.parse_int "6") uu____79401 uu____79405
           FStar_TypeChecker_Common.Trivial);
        (let uu____79411 = FStar_Tests_Pars.tc "fun (x:int) (y:int) -> y"  in
         let uu____79415 = FStar_Tests_Pars.tc "fun (x:int) (y:int) -> x"  in
         let uu____79419 =
           let uu____79420 =
             FStar_Tests_Pars.tc "(forall (x:int). (forall (y:int). y==x))"
              in
           FStar_TypeChecker_Common.NonTrivial uu____79420  in
         unify1 (Prims.parse_int "7") uu____79411 uu____79415 uu____79419);
        (let uu____79424 =
           FStar_Tests_Pars.tc "fun (x:int) (y:int) (z:int) -> y"  in
         let uu____79428 =
           FStar_Tests_Pars.tc "fun (x:int) (y:int) (z:int) -> z"  in
         let uu____79432 =
           let uu____79433 =
             FStar_Tests_Pars.tc
               "(forall (x:int). (forall (y:int). (forall (z:int). y==z)))"
              in
           FStar_TypeChecker_Common.NonTrivial uu____79433  in
         unify1 (Prims.parse_int "8") uu____79424 uu____79428 uu____79432);
        (let uu____79437 = FStar_Main.process_args ()  in
         FStar_All.pipe_right uu____79437 (fun a2  -> ()));
        (let uu____79452 =
           let uu____79459 = FStar_Tests_Pars.tc "fun u x -> u x"  in
           inst (Prims.parse_int "1") uu____79459  in
         match uu____79452 with
         | (tm1,us) ->
             let sol = FStar_Tests_Pars.tc "fun x -> c_and x x"  in
             (unify_check (Prims.parse_int "9") tm1 sol
                FStar_TypeChecker_Common.Trivial
                (fun uu____79477  ->
                   let uu____79478 =
                     let uu____79480 =
                       let uu____79483 = FStar_List.hd us  in
                       norm uu____79483  in
                     let uu____79484 = norm sol  in
                     FStar_Tests_Util.term_eq uu____79480 uu____79484  in
                   FStar_Tests_Util.always (Prims.parse_int "9") uu____79478);
              (let uu____79488 =
                 let uu____79495 = FStar_Tests_Pars.tc "fun u x -> u x"  in
                 inst (Prims.parse_int "1") uu____79495  in
               match uu____79488 with
               | (tm2,us1) ->
                   let sol1 = FStar_Tests_Pars.tc "fun x y -> x + y"  in
                   (unify_check (Prims.parse_int "10") tm2 sol1
                      FStar_TypeChecker_Common.Trivial
                      (fun uu____79513  ->
                         let uu____79514 =
                           let uu____79516 =
                             let uu____79519 = FStar_List.hd us1  in
                             norm uu____79519  in
                           let uu____79520 = norm sol1  in
                           FStar_Tests_Util.term_eq uu____79516 uu____79520
                            in
                         FStar_Tests_Util.always (Prims.parse_int "10")
                           uu____79514);
                    (let tm11 =
                       FStar_Tests_Pars.tc "x:int -> y:int{eq2 y x} -> bool"
                        in
                     let tm21 = FStar_Tests_Pars.tc "x:int -> y:int -> bool"
                        in
                     (let uu____79529 =
                        let uu____79530 =
                          FStar_Tests_Pars.tc
                            "forall (x:int). (forall (y:int). y==x)"
                           in
                        FStar_TypeChecker_Common.NonTrivial uu____79530  in
                      unify1 (Prims.parse_int "11") tm11 tm21 uu____79529);
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
                      (let uu____79539 =
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
                           let uu____79557 =
                             let uu____79558 =
                               let uu____79561 =
                                 FStar_Syntax_Syntax.bv_to_name q  in
                               [uu____79561]  in
                             FStar_Tests_Util.app l uu____79558  in
                           norm uu____79557  in
                         let l1 =
                           FStar_Tests_Pars.tc "fun (p:unit -> Type0) -> p"
                            in
                         let unit = FStar_Tests_Pars.tc "()"  in
                         let env =
                           let uu____79567 = FStar_Tests_Pars.init ()  in
                           let uu____79568 =
                             let uu____79569 =
                               FStar_Syntax_Syntax.mk_binder x2  in
                             let uu____79576 =
                               let uu____79585 =
                                 FStar_Syntax_Syntax.mk_binder q  in
                               [uu____79585]  in
                             uu____79569 :: uu____79576  in
                           FStar_TypeChecker_Env.push_binders uu____79567
                             uu____79568
                            in
                         let uu____79610 =
                           FStar_TypeChecker_Util.new_implicit_var ""
                             FStar_Range.dummyRange env typ
                            in
                         match uu____79610 with
                         | (u_p,uu____79633,uu____79634) ->
                             let tm23 =
                               let uu____79650 =
                                 let uu____79653 =
                                   FStar_Tests_Util.app l1 [u_p]  in
                                 norm uu____79653  in
                               FStar_Tests_Util.app uu____79650 [unit]  in
                             (tm13, tm23)
                          in
                       match uu____79539 with
                       | (tm13,tm23) ->
                           (unify1 (Prims.parse_int "13") tm13 tm23
                              FStar_TypeChecker_Common.Trivial;
                            (let uu____79671 =
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
                                 let uu____79689 =
                                   let uu____79690 =
                                     let uu____79693 =
                                       FStar_Syntax_Syntax.bv_to_name q  in
                                     [uu____79693]  in
                                   FStar_Tests_Util.app l uu____79690  in
                                 norm uu____79689  in
                               let l1 =
                                 FStar_Tests_Pars.tc
                                   "fun (p:pure_post unit) -> p"
                                  in
                               let unit = FStar_Tests_Pars.tc "()"  in
                               let env =
                                 let uu____79699 = FStar_Tests_Pars.init ()
                                    in
                                 let uu____79700 =
                                   let uu____79701 =
                                     FStar_Syntax_Syntax.mk_binder x2  in
                                   let uu____79708 =
                                     let uu____79717 =
                                       FStar_Syntax_Syntax.mk_binder q  in
                                     [uu____79717]  in
                                   uu____79701 :: uu____79708  in
                                 FStar_TypeChecker_Env.push_binders
                                   uu____79699 uu____79700
                                  in
                               let uu____79742 =
                                 FStar_TypeChecker_Util.new_implicit_var ""
                                   FStar_Range.dummyRange env typ
                                  in
                               match uu____79742 with
                               | (u_p,uu____79765,uu____79766) ->
                                   let tm24 =
                                     let uu____79782 =
                                       let uu____79785 =
                                         FStar_Tests_Util.app l1 [u_p]  in
                                       norm uu____79785  in
                                     FStar_Tests_Util.app uu____79782 [unit]
                                      in
                                   (tm14, tm24)
                                in
                             match uu____79671 with
                             | (tm14,tm24) ->
                                 (unify1 (Prims.parse_int "14") tm14 tm24
                                    FStar_TypeChecker_Common.Trivial;
                                  FStar_Options.__clear_unit_tests ();
                                  (let uu____79805 = FStar_ST.op_Bang success
                                      in
                                   if uu____79805
                                   then
                                     FStar_Util.print_string "Unifier ok\n"
                                   else ());
                                  FStar_ST.op_Bang success))))))))))))))
  