open Prims
let (tcenv : unit -> FStar_TypeChecker_Env.env) =
  fun uu____78876  -> FStar_Tests_Pars.init () 
let (guard_to_string :
  FStar_TypeChecker_Common.guard_formula -> Prims.string) =
  fun g  ->
    match g with
    | FStar_TypeChecker_Common.Trivial  -> "trivial"
    | FStar_TypeChecker_Common.NonTrivial f ->
        let uu____78887 = tcenv ()  in
        FStar_TypeChecker_Normalize.term_to_string uu____78887 f
  
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
        let uu____78943 =
          match (g, g') with
          | (FStar_TypeChecker_Common.Trivial
             ,FStar_TypeChecker_Common.Trivial ) -> (true, g, g')
          | (FStar_TypeChecker_Common.NonTrivial
             f,FStar_TypeChecker_Common.NonTrivial f') ->
              let f1 =
                let uu____78963 = tcenv ()  in
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Env.EraseUniverses] uu____78963 f
                 in
              let f'1 =
                let uu____78965 = tcenv ()  in
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Env.EraseUniverses] uu____78965 f'
                 in
              let uu____78966 = FStar_Tests_Util.term_eq f1 f'1  in
              (uu____78966, (FStar_TypeChecker_Common.NonTrivial f1),
                (FStar_TypeChecker_Common.NonTrivial f'1))
          | uu____78969 -> (false, g, g')  in
        match uu____78943 with
        | (b,g1,g'1) ->
            (if Prims.op_Negation b
             then
               (let uu____78983 =
                  let uu____78985 = FStar_Util.string_of_int i  in
                  let uu____78987 = guard_to_string g'1  in
                  let uu____78989 = guard_to_string g1  in
                  FStar_Util.format3
                    "Test %s failed:\n\tExpected guard %s;\n\tGot guard      %s\n"
                    uu____78985 uu____78987 uu____78989
                   in
                FStar_All.pipe_left fail uu____78983)
             else ();
             (let uu____78995 = (FStar_ST.op_Bang success) && b  in
              FStar_ST.op_Colon_Equals success uu____78995))
  
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
            (let uu____79081 = FStar_Util.string_of_int i  in
             FStar_Util.print1 "%s ..." uu____79081);
            (let uu____79085 = FStar_Main.process_args ()  in
             FStar_All.pipe_right uu____79085 (fun a1  -> ()));
            (let uu____79101 = FStar_Syntax_Print.term_to_string x1  in
             let uu____79103 = FStar_Syntax_Print.term_to_string y1  in
             FStar_Util.print2 "Unify %s\nand %s\n" uu____79101 uu____79103);
            (let g =
               let uu____79107 =
                 let uu____79108 =
                   let uu____79109 = tcenv ()  in
                   FStar_TypeChecker_Rel.teq uu____79109 x1 y1  in
                 let uu____79110 =
                   let uu____79115 = tcenv ()  in
                   FStar_TypeChecker_Rel.solve_deferred_constraints
                     uu____79115
                    in
                 FStar_All.pipe_right uu____79108 uu____79110  in
               let uu____79116 =
                 let uu____79121 = tcenv ()  in
                 FStar_TypeChecker_Rel.simplify_guard uu____79121  in
               FStar_All.pipe_right uu____79107 uu____79116  in
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
        (fun uu___783_79146  ->
           match () with
           | () ->
               let g =
                 let uu____79148 =
                   let uu____79149 = tcenv ()  in
                   FStar_TypeChecker_Rel.teq uu____79149 x1 y1  in
                 let uu____79150 =
                   let uu____79155 = tcenv ()  in
                   FStar_TypeChecker_Rel.solve_deferred_constraints
                     uu____79155
                    in
                 FStar_All.pipe_right uu____79148 uu____79150  in
               (match g.FStar_TypeChecker_Env.guard_f with
                | FStar_TypeChecker_Common.Trivial  ->
                    let uu____79156 =
                      let uu____79158 = FStar_Syntax_Print.term_to_string x1
                         in
                      let uu____79160 = FStar_Syntax_Print.term_to_string y1
                         in
                      FStar_Util.format2
                        "%s and %s should not be unifiable\n" uu____79158
                        uu____79160
                       in
                    fail uu____79156
                | FStar_TypeChecker_Common.NonTrivial f ->
                    let uu____79164 = FStar_Syntax_Print.term_to_string x1
                       in
                    let uu____79166 = FStar_Syntax_Print.term_to_string y1
                       in
                    let uu____79168 = FStar_Syntax_Print.term_to_string f  in
                    FStar_Util.print3 "%s and %s are unifiable if %s\n"
                      uu____79164 uu____79166 uu____79168)) ()
      with | FStar_Errors.Error (e,msg,r) -> FStar_Util.print1 "%s\n" msg
  
let (unify' : Prims.string -> Prims.string -> unit) =
  fun x1  ->
    fun y1  ->
      let x2 = FStar_Tests_Pars.pars x1  in
      let y2 = FStar_Tests_Pars.pars y1  in
      let g =
        let uu____79200 =
          let uu____79201 = tcenv ()  in
          FStar_TypeChecker_Rel.teq uu____79201 x2 y2  in
        let uu____79202 =
          let uu____79207 = tcenv ()  in
          FStar_TypeChecker_Rel.solve_deferred_constraints uu____79207  in
        FStar_All.pipe_right uu____79200 uu____79202  in
      let uu____79208 = FStar_Syntax_Print.term_to_string x2  in
      let uu____79210 = FStar_Syntax_Print.term_to_string y2  in
      let uu____79212 = guard_to_string g.FStar_TypeChecker_Env.guard_f  in
      FStar_Util.print3 "%s and %s are unifiable with guard %s\n" uu____79208
        uu____79210 uu____79212
  
let (norm : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____79221 = tcenv ()  in
    FStar_TypeChecker_Normalize.normalize [] uu____79221 t
  
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
          (let uu____79271 =
             let uu____79284 = FStar_Tests_Pars.init ()  in
             FStar_TypeChecker_Util.new_implicit_var ""
               FStar_Range.dummyRange uu____79284 FStar_Syntax_Util.ktype0
              in
           match uu____79271 with
           | (t,uu____79289,uu____79290) ->
               let uu____79303 =
                 let uu____79316 = FStar_Tests_Pars.init ()  in
                 FStar_TypeChecker_Util.new_implicit_var ""
                   FStar_Range.dummyRange uu____79316 t
                  in
               (match uu____79303 with
                | (u,uu____79321,uu____79322) ->
                    aux (u :: out) (n2 - (Prims.parse_int "1"))))
         in
      let us = aux [] n1  in
      let uu____79339 =
        let uu____79340 = FStar_Tests_Util.app tm1 us  in norm uu____79340
         in
      (uu____79339, us)
  
let (run_all : unit -> Prims.bool) =
  fun uu____79349  ->
    FStar_Util.print_string "Testing the unifier\n";
    FStar_Options.__set_unit_tests ();
    (let unify_check n1 x1 y1 g f = unify n1 x1 y1 g f  in
     let unify1 n1 x1 y1 g = unify n1 x1 y1 g (fun uu____79426  -> ())  in
     let int_t = FStar_Tests_Pars.tc "Prims.int"  in
     let x1 =
       let uu____79432 =
         FStar_Syntax_Syntax.gen_bv "x" FStar_Pervasives_Native.None int_t
          in
       FStar_All.pipe_right uu____79432 FStar_Syntax_Syntax.bv_to_name  in
     let y1 =
       let uu____79439 =
         FStar_Syntax_Syntax.gen_bv "y" FStar_Pervasives_Native.None int_t
          in
       FStar_All.pipe_right uu____79439 FStar_Syntax_Syntax.bv_to_name  in
     unify1 (Prims.parse_int "0") x1 x1 FStar_TypeChecker_Common.Trivial;
     (let uu____79446 =
        let uu____79447 =
          FStar_Syntax_Util.mk_eq2 FStar_Syntax_Syntax.U_zero
            FStar_Syntax_Util.t_bool x1 y1
           in
        FStar_TypeChecker_Common.NonTrivial uu____79447  in
      unify1 (Prims.parse_int "1") x1 y1 uu____79446);
     (let id1 = FStar_Tests_Pars.tc "fun x -> x"  in
      (let uu____79452 = FStar_Tests_Util.app id1 [x1]  in
       unify1 (Prims.parse_int "2") x1 uu____79452
         FStar_TypeChecker_Common.Trivial);
      (let id2 = FStar_Tests_Pars.tc "fun x -> x"  in
       unify1 (Prims.parse_int "3") id2 id2 FStar_TypeChecker_Common.Trivial;
       (let id3 = FStar_Tests_Pars.tc "fun x -> x"  in
        let id' = FStar_Tests_Pars.tc "fun y -> y"  in
        unify1 (Prims.parse_int "4") id3 id' FStar_TypeChecker_Common.Trivial;
        (let uu____79467 = FStar_Tests_Pars.tc "fun x y -> x"  in
         let uu____79471 = FStar_Tests_Pars.tc "fun a b -> a"  in
         unify1 (Prims.parse_int "5") uu____79467 uu____79471
           FStar_TypeChecker_Common.Trivial);
        (let uu____79477 = FStar_Tests_Pars.tc "fun x y z -> y"  in
         let uu____79481 = FStar_Tests_Pars.tc "fun a b c -> b"  in
         unify1 (Prims.parse_int "6") uu____79477 uu____79481
           FStar_TypeChecker_Common.Trivial);
        (let uu____79487 = FStar_Tests_Pars.tc "fun (x:int) (y:int) -> y"  in
         let uu____79491 = FStar_Tests_Pars.tc "fun (x:int) (y:int) -> x"  in
         let uu____79495 =
           let uu____79496 =
             FStar_Tests_Pars.tc "(forall (x:int). (forall (y:int). y==x))"
              in
           FStar_TypeChecker_Common.NonTrivial uu____79496  in
         unify1 (Prims.parse_int "7") uu____79487 uu____79491 uu____79495);
        (let uu____79500 =
           FStar_Tests_Pars.tc "fun (x:int) (y:int) (z:int) -> y"  in
         let uu____79504 =
           FStar_Tests_Pars.tc "fun (x:int) (y:int) (z:int) -> z"  in
         let uu____79508 =
           let uu____79509 =
             FStar_Tests_Pars.tc
               "(forall (x:int). (forall (y:int). (forall (z:int). y==z)))"
              in
           FStar_TypeChecker_Common.NonTrivial uu____79509  in
         unify1 (Prims.parse_int "8") uu____79500 uu____79504 uu____79508);
        (let uu____79513 = FStar_Main.process_args ()  in
         FStar_All.pipe_right uu____79513 (fun a2  -> ()));
        (let uu____79528 =
           let uu____79535 = FStar_Tests_Pars.tc "fun u x -> u x"  in
           inst (Prims.parse_int "1") uu____79535  in
         match uu____79528 with
         | (tm1,us) ->
             let sol = FStar_Tests_Pars.tc "fun x -> c_and x x"  in
             (unify_check (Prims.parse_int "9") tm1 sol
                FStar_TypeChecker_Common.Trivial
                (fun uu____79553  ->
                   let uu____79554 =
                     let uu____79556 =
                       let uu____79559 = FStar_List.hd us  in
                       norm uu____79559  in
                     let uu____79560 = norm sol  in
                     FStar_Tests_Util.term_eq uu____79556 uu____79560  in
                   FStar_Tests_Util.always (Prims.parse_int "9") uu____79554);
              (let uu____79564 =
                 let uu____79571 = FStar_Tests_Pars.tc "fun u x -> u x"  in
                 inst (Prims.parse_int "1") uu____79571  in
               match uu____79564 with
               | (tm2,us1) ->
                   let sol1 = FStar_Tests_Pars.tc "fun x y -> x + y"  in
                   (unify_check (Prims.parse_int "10") tm2 sol1
                      FStar_TypeChecker_Common.Trivial
                      (fun uu____79589  ->
                         let uu____79590 =
                           let uu____79592 =
                             let uu____79595 = FStar_List.hd us1  in
                             norm uu____79595  in
                           let uu____79596 = norm sol1  in
                           FStar_Tests_Util.term_eq uu____79592 uu____79596
                            in
                         FStar_Tests_Util.always (Prims.parse_int "10")
                           uu____79590);
                    (let tm11 =
                       FStar_Tests_Pars.tc "x:int -> y:int{eq2 y x} -> bool"
                        in
                     let tm21 = FStar_Tests_Pars.tc "x:int -> y:int -> bool"
                        in
                     (let uu____79605 =
                        let uu____79606 =
                          FStar_Tests_Pars.tc
                            "forall (x:int). (forall (y:int). y==x)"
                           in
                        FStar_TypeChecker_Common.NonTrivial uu____79606  in
                      unify1 (Prims.parse_int "11") tm11 tm21 uu____79605);
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
                      (let uu____79615 =
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
                           let uu____79633 =
                             let uu____79634 =
                               let uu____79637 =
                                 FStar_Syntax_Syntax.bv_to_name q  in
                               [uu____79637]  in
                             FStar_Tests_Util.app l uu____79634  in
                           norm uu____79633  in
                         let l1 =
                           FStar_Tests_Pars.tc "fun (p:unit -> Type0) -> p"
                            in
                         let unit = FStar_Tests_Pars.tc "()"  in
                         let env =
                           let uu____79643 = FStar_Tests_Pars.init ()  in
                           let uu____79644 =
                             let uu____79645 =
                               FStar_Syntax_Syntax.mk_binder x2  in
                             let uu____79652 =
                               let uu____79661 =
                                 FStar_Syntax_Syntax.mk_binder q  in
                               [uu____79661]  in
                             uu____79645 :: uu____79652  in
                           FStar_TypeChecker_Env.push_binders uu____79643
                             uu____79644
                            in
                         let uu____79686 =
                           FStar_TypeChecker_Util.new_implicit_var ""
                             FStar_Range.dummyRange env typ
                            in
                         match uu____79686 with
                         | (u_p,uu____79709,uu____79710) ->
                             let tm23 =
                               let uu____79726 =
                                 let uu____79729 =
                                   FStar_Tests_Util.app l1 [u_p]  in
                                 norm uu____79729  in
                               FStar_Tests_Util.app uu____79726 [unit]  in
                             (tm13, tm23)
                          in
                       match uu____79615 with
                       | (tm13,tm23) ->
                           (unify1 (Prims.parse_int "13") tm13 tm23
                              FStar_TypeChecker_Common.Trivial;
                            (let uu____79747 =
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
                                 let uu____79765 =
                                   let uu____79766 =
                                     let uu____79769 =
                                       FStar_Syntax_Syntax.bv_to_name q  in
                                     [uu____79769]  in
                                   FStar_Tests_Util.app l uu____79766  in
                                 norm uu____79765  in
                               let l1 =
                                 FStar_Tests_Pars.tc
                                   "fun (p:pure_post unit) -> p"
                                  in
                               let unit = FStar_Tests_Pars.tc "()"  in
                               let env =
                                 let uu____79775 = FStar_Tests_Pars.init ()
                                    in
                                 let uu____79776 =
                                   let uu____79777 =
                                     FStar_Syntax_Syntax.mk_binder x2  in
                                   let uu____79784 =
                                     let uu____79793 =
                                       FStar_Syntax_Syntax.mk_binder q  in
                                     [uu____79793]  in
                                   uu____79777 :: uu____79784  in
                                 FStar_TypeChecker_Env.push_binders
                                   uu____79775 uu____79776
                                  in
                               let uu____79818 =
                                 FStar_TypeChecker_Util.new_implicit_var ""
                                   FStar_Range.dummyRange env typ
                                  in
                               match uu____79818 with
                               | (u_p,uu____79841,uu____79842) ->
                                   let tm24 =
                                     let uu____79858 =
                                       let uu____79861 =
                                         FStar_Tests_Util.app l1 [u_p]  in
                                       norm uu____79861  in
                                     FStar_Tests_Util.app uu____79858 [unit]
                                      in
                                   (tm14, tm24)
                                in
                             match uu____79747 with
                             | (tm14,tm24) ->
                                 (unify1 (Prims.parse_int "14") tm14 tm24
                                    FStar_TypeChecker_Common.Trivial;
                                  FStar_Options.__clear_unit_tests ();
                                  (let uu____79881 = FStar_ST.op_Bang success
                                      in
                                   if uu____79881
                                   then
                                     FStar_Util.print_string "Unifier ok\n"
                                   else ());
                                  FStar_ST.op_Bang success))))))))))))))
  