open Prims
let (tcenv : unit -> FStar_TypeChecker_Env.env) =
  fun uu____84222  -> FStar_Tests_Pars.init () 
let (guard_to_string :
  FStar_TypeChecker_Common.guard_formula -> Prims.string) =
  fun g  ->
    match g with
    | FStar_TypeChecker_Common.Trivial  -> "trivial"
    | FStar_TypeChecker_Common.NonTrivial f ->
        let uu____84233 = tcenv ()  in
        FStar_TypeChecker_Normalize.term_to_string uu____84233 f
  
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
        let uu____84300 =
          match (g, g') with
          | (FStar_TypeChecker_Common.Trivial
             ,FStar_TypeChecker_Common.Trivial ) -> (true, g, g')
          | (FStar_TypeChecker_Common.NonTrivial
             f,FStar_TypeChecker_Common.NonTrivial f') ->
              let f1 =
                let uu____84320 = tcenv ()  in
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Env.EraseUniverses] uu____84320 f
                 in
              let f'1 =
                let uu____84322 = tcenv ()  in
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Env.EraseUniverses] uu____84322 f'
                 in
              let uu____84323 = FStar_Tests_Util.term_eq f1 f'1  in
              (uu____84323, (FStar_TypeChecker_Common.NonTrivial f1),
                (FStar_TypeChecker_Common.NonTrivial f'1))
          | uu____84326 -> (false, g, g')  in
        match uu____84300 with
        | (b,g1,g'1) ->
            (if Prims.op_Negation b
             then
               (let uu____84340 =
                  let uu____84342 = FStar_Util.string_of_int i  in
                  let uu____84344 = guard_to_string g'1  in
                  let uu____84346 = guard_to_string g1  in
                  FStar_Util.format3
                    "Test %s failed:\n\tExpected guard %s;\n\tGot guard      %s\n"
                    uu____84342 uu____84344 uu____84346
                   in
                FStar_All.pipe_left fail uu____84340)
             else ();
             (let uu____84352 = (FStar_ST.op_Bang success) && b  in
              FStar_ST.op_Colon_Equals success uu____84352))
  
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
            (let uu____84438 = FStar_Util.string_of_int i  in
             FStar_Util.print1 "%s ..." uu____84438);
            (let uu____84442 = FStar_Main.process_args ()  in
             FStar_All.pipe_right uu____84442 (fun a1  -> ()));
            (let uu____84458 = FStar_Syntax_Print.term_to_string x1  in
             let uu____84460 = FStar_Syntax_Print.term_to_string y1  in
             FStar_Util.print2 "Unify %s\nand %s\n" uu____84458 uu____84460);
            (let g =
               let uu____84464 =
                 let uu____84465 =
                   let uu____84466 = tcenv ()  in
                   FStar_TypeChecker_Rel.teq uu____84466 x1 y1  in
                 let uu____84467 =
                   let uu____84472 = tcenv ()  in
                   FStar_TypeChecker_Rel.solve_deferred_constraints
                     uu____84472
                    in
                 FStar_All.pipe_right uu____84465 uu____84467  in
               let uu____84473 =
                 let uu____84478 = tcenv ()  in
                 FStar_TypeChecker_Rel.simplify_guard uu____84478  in
               FStar_All.pipe_right uu____84464 uu____84473  in
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
        (fun uu___783_84503  ->
           match () with
           | () ->
               let g =
                 let uu____84505 =
                   let uu____84506 = tcenv ()  in
                   FStar_TypeChecker_Rel.teq uu____84506 x1 y1  in
                 let uu____84507 =
                   let uu____84512 = tcenv ()  in
                   FStar_TypeChecker_Rel.solve_deferred_constraints
                     uu____84512
                    in
                 FStar_All.pipe_right uu____84505 uu____84507  in
               (match g.FStar_TypeChecker_Env.guard_f with
                | FStar_TypeChecker_Common.Trivial  ->
                    let uu____84513 =
                      let uu____84515 = FStar_Syntax_Print.term_to_string x1
                         in
                      let uu____84517 = FStar_Syntax_Print.term_to_string y1
                         in
                      FStar_Util.format2
                        "%s and %s should not be unifiable\n" uu____84515
                        uu____84517
                       in
                    fail uu____84513
                | FStar_TypeChecker_Common.NonTrivial f ->
                    let uu____84521 = FStar_Syntax_Print.term_to_string x1
                       in
                    let uu____84523 = FStar_Syntax_Print.term_to_string y1
                       in
                    let uu____84525 = FStar_Syntax_Print.term_to_string f  in
                    FStar_Util.print3 "%s and %s are unifiable if %s\n"
                      uu____84521 uu____84523 uu____84525)) ()
      with | FStar_Errors.Error (e,msg,r) -> FStar_Util.print1 "%s\n" msg
  
let (unify' : Prims.string -> Prims.string -> unit) =
  fun x1  ->
    fun y1  ->
      let x2 = FStar_Tests_Pars.pars x1  in
      let y2 = FStar_Tests_Pars.pars y1  in
      let g =
        let uu____84557 =
          let uu____84558 = tcenv ()  in
          FStar_TypeChecker_Rel.teq uu____84558 x2 y2  in
        let uu____84559 =
          let uu____84564 = tcenv ()  in
          FStar_TypeChecker_Rel.solve_deferred_constraints uu____84564  in
        FStar_All.pipe_right uu____84557 uu____84559  in
      let uu____84565 = FStar_Syntax_Print.term_to_string x2  in
      let uu____84567 = FStar_Syntax_Print.term_to_string y2  in
      let uu____84569 = guard_to_string g.FStar_TypeChecker_Env.guard_f  in
      FStar_Util.print3 "%s and %s are unifiable with guard %s\n" uu____84565
        uu____84567 uu____84569
  
let (norm : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____84578 = tcenv ()  in
    FStar_TypeChecker_Normalize.normalize [] uu____84578 t
  
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
          (let uu____84628 =
             let uu____84641 = FStar_Tests_Pars.init ()  in
             FStar_TypeChecker_Util.new_implicit_var ""
               FStar_Range.dummyRange uu____84641 FStar_Syntax_Util.ktype0
              in
           match uu____84628 with
           | (t,uu____84646,uu____84647) ->
               let uu____84660 =
                 let uu____84673 = FStar_Tests_Pars.init ()  in
                 FStar_TypeChecker_Util.new_implicit_var ""
                   FStar_Range.dummyRange uu____84673 t
                  in
               (match uu____84660 with
                | (u,uu____84678,uu____84679) ->
                    aux (u :: out) (n2 - (Prims.parse_int "1"))))
         in
      let us = aux [] n1  in
      let uu____84696 =
        let uu____84697 = FStar_Tests_Util.app tm1 us  in norm uu____84697
         in
      (uu____84696, us)
  
let (run_all : unit -> Prims.bool) =
  fun uu____84706  ->
    FStar_Util.print_string "Testing the unifier\n";
    FStar_Options.__set_unit_tests ();
    (let unify_check n1 x1 y1 g f = unify n1 x1 y1 g f  in
     let unify1 n1 x1 y1 g = unify n1 x1 y1 g (fun uu____84783  -> ())  in
     let int_t = FStar_Tests_Pars.tc "Prims.int"  in
     let x1 =
       let uu____84789 =
         FStar_Syntax_Syntax.gen_bv "x" FStar_Pervasives_Native.None int_t
          in
       FStar_All.pipe_right uu____84789 FStar_Syntax_Syntax.bv_to_name  in
     let y1 =
       let uu____84796 =
         FStar_Syntax_Syntax.gen_bv "y" FStar_Pervasives_Native.None int_t
          in
       FStar_All.pipe_right uu____84796 FStar_Syntax_Syntax.bv_to_name  in
     unify1 (Prims.parse_int "0") x1 x1 FStar_TypeChecker_Common.Trivial;
     (let uu____84803 =
        let uu____84804 =
          FStar_Syntax_Util.mk_eq2 FStar_Syntax_Syntax.U_zero
            FStar_Syntax_Util.t_bool x1 y1
           in
        FStar_TypeChecker_Common.NonTrivial uu____84804  in
      unify1 (Prims.parse_int "1") x1 y1 uu____84803);
     (let id1 = FStar_Tests_Pars.tc "fun x -> x"  in
      (let uu____84809 = FStar_Tests_Util.app id1 [x1]  in
       unify1 (Prims.parse_int "2") x1 uu____84809
         FStar_TypeChecker_Common.Trivial);
      (let id2 = FStar_Tests_Pars.tc "fun x -> x"  in
       unify1 (Prims.parse_int "3") id2 id2 FStar_TypeChecker_Common.Trivial;
       (let id3 = FStar_Tests_Pars.tc "fun x -> x"  in
        let id' = FStar_Tests_Pars.tc "fun y -> y"  in
        unify1 (Prims.parse_int "4") id3 id' FStar_TypeChecker_Common.Trivial;
        (let uu____84824 = FStar_Tests_Pars.tc "fun x y -> x"  in
         let uu____84828 = FStar_Tests_Pars.tc "fun a b -> a"  in
         unify1 (Prims.parse_int "5") uu____84824 uu____84828
           FStar_TypeChecker_Common.Trivial);
        (let uu____84834 = FStar_Tests_Pars.tc "fun x y z -> y"  in
         let uu____84838 = FStar_Tests_Pars.tc "fun a b c -> b"  in
         unify1 (Prims.parse_int "6") uu____84834 uu____84838
           FStar_TypeChecker_Common.Trivial);
        (let uu____84844 = FStar_Tests_Pars.tc "fun (x:int) (y:int) -> y"  in
         let uu____84848 = FStar_Tests_Pars.tc "fun (x:int) (y:int) -> x"  in
         let uu____84852 =
           let uu____84853 =
             FStar_Tests_Pars.tc "(forall (x:int). (forall (y:int). y==x))"
              in
           FStar_TypeChecker_Common.NonTrivial uu____84853  in
         unify1 (Prims.parse_int "7") uu____84844 uu____84848 uu____84852);
        (let uu____84857 =
           FStar_Tests_Pars.tc "fun (x:int) (y:int) (z:int) -> y"  in
         let uu____84861 =
           FStar_Tests_Pars.tc "fun (x:int) (y:int) (z:int) -> z"  in
         let uu____84865 =
           let uu____84866 =
             FStar_Tests_Pars.tc
               "(forall (x:int). (forall (y:int). (forall (z:int). y==z)))"
              in
           FStar_TypeChecker_Common.NonTrivial uu____84866  in
         unify1 (Prims.parse_int "8") uu____84857 uu____84861 uu____84865);
        (let uu____84870 = FStar_Main.process_args ()  in
         FStar_All.pipe_right uu____84870 (fun a2  -> ()));
        (let uu____84885 =
           let uu____84892 = FStar_Tests_Pars.tc "fun u x -> u x"  in
           inst (Prims.parse_int "1") uu____84892  in
         match uu____84885 with
         | (tm1,us) ->
             let sol = FStar_Tests_Pars.tc "fun x -> c_and x x"  in
             (unify_check (Prims.parse_int "9") tm1 sol
                FStar_TypeChecker_Common.Trivial
                (fun uu____84910  ->
                   let uu____84911 =
                     let uu____84913 =
                       let uu____84916 = FStar_List.hd us  in
                       norm uu____84916  in
                     let uu____84917 = norm sol  in
                     FStar_Tests_Util.term_eq uu____84913 uu____84917  in
                   FStar_Tests_Util.always (Prims.parse_int "9") uu____84911);
              (let uu____84921 =
                 let uu____84928 = FStar_Tests_Pars.tc "fun u x -> u x"  in
                 inst (Prims.parse_int "1") uu____84928  in
               match uu____84921 with
               | (tm2,us1) ->
                   let sol1 = FStar_Tests_Pars.tc "fun x y -> x + y"  in
                   (unify_check (Prims.parse_int "10") tm2 sol1
                      FStar_TypeChecker_Common.Trivial
                      (fun uu____84946  ->
                         let uu____84947 =
                           let uu____84949 =
                             let uu____84952 = FStar_List.hd us1  in
                             norm uu____84952  in
                           let uu____84953 = norm sol1  in
                           FStar_Tests_Util.term_eq uu____84949 uu____84953
                            in
                         FStar_Tests_Util.always (Prims.parse_int "10")
                           uu____84947);
                    (let tm11 =
                       FStar_Tests_Pars.tc "x:int -> y:int{eq2 y x} -> bool"
                        in
                     let tm21 = FStar_Tests_Pars.tc "x:int -> y:int -> bool"
                        in
                     (let uu____84962 =
                        let uu____84963 =
                          FStar_Tests_Pars.tc
                            "forall (x:int). (forall (y:int). y==x)"
                           in
                        FStar_TypeChecker_Common.NonTrivial uu____84963  in
                      unify1 (Prims.parse_int "11") tm11 tm21 uu____84962);
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
                      (let uu____84972 =
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
                           let uu____84990 =
                             let uu____84991 =
                               let uu____84994 =
                                 FStar_Syntax_Syntax.bv_to_name q  in
                               [uu____84994]  in
                             FStar_Tests_Util.app l uu____84991  in
                           norm uu____84990  in
                         let l1 =
                           FStar_Tests_Pars.tc "fun (p:unit -> Type0) -> p"
                            in
                         let unit = FStar_Tests_Pars.tc "()"  in
                         let env =
                           let uu____85000 = FStar_Tests_Pars.init ()  in
                           let uu____85001 =
                             let uu____85002 =
                               FStar_Syntax_Syntax.mk_binder x2  in
                             let uu____85009 =
                               let uu____85018 =
                                 FStar_Syntax_Syntax.mk_binder q  in
                               [uu____85018]  in
                             uu____85002 :: uu____85009  in
                           FStar_TypeChecker_Env.push_binders uu____85000
                             uu____85001
                            in
                         let uu____85043 =
                           FStar_TypeChecker_Util.new_implicit_var ""
                             FStar_Range.dummyRange env typ
                            in
                         match uu____85043 with
                         | (u_p,uu____85066,uu____85067) ->
                             let tm23 =
                               let uu____85083 =
                                 let uu____85086 =
                                   FStar_Tests_Util.app l1 [u_p]  in
                                 norm uu____85086  in
                               FStar_Tests_Util.app uu____85083 [unit]  in
                             (tm13, tm23)
                          in
                       match uu____84972 with
                       | (tm13,tm23) ->
                           (unify1 (Prims.parse_int "13") tm13 tm23
                              FStar_TypeChecker_Common.Trivial;
                            (let uu____85104 =
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
                                 let uu____85122 =
                                   let uu____85123 =
                                     let uu____85126 =
                                       FStar_Syntax_Syntax.bv_to_name q  in
                                     [uu____85126]  in
                                   FStar_Tests_Util.app l uu____85123  in
                                 norm uu____85122  in
                               let l1 =
                                 FStar_Tests_Pars.tc
                                   "fun (p:pure_post unit) -> p"
                                  in
                               let unit = FStar_Tests_Pars.tc "()"  in
                               let env =
                                 let uu____85132 = FStar_Tests_Pars.init ()
                                    in
                                 let uu____85133 =
                                   let uu____85134 =
                                     FStar_Syntax_Syntax.mk_binder x2  in
                                   let uu____85141 =
                                     let uu____85150 =
                                       FStar_Syntax_Syntax.mk_binder q  in
                                     [uu____85150]  in
                                   uu____85134 :: uu____85141  in
                                 FStar_TypeChecker_Env.push_binders
                                   uu____85132 uu____85133
                                  in
                               let uu____85175 =
                                 FStar_TypeChecker_Util.new_implicit_var ""
                                   FStar_Range.dummyRange env typ
                                  in
                               match uu____85175 with
                               | (u_p,uu____85198,uu____85199) ->
                                   let tm24 =
                                     let uu____85215 =
                                       let uu____85218 =
                                         FStar_Tests_Util.app l1 [u_p]  in
                                       norm uu____85218  in
                                     FStar_Tests_Util.app uu____85215 [unit]
                                      in
                                   (tm14, tm24)
                                in
                             match uu____85104 with
                             | (tm14,tm24) ->
                                 (unify1 (Prims.parse_int "14") tm14 tm24
                                    FStar_TypeChecker_Common.Trivial;
                                  FStar_Options.__clear_unit_tests ();
                                  (let uu____85238 = FStar_ST.op_Bang success
                                      in
                                   if uu____85238
                                   then
                                     FStar_Util.print_string "Unifier ok\n"
                                   else ());
                                  FStar_ST.op_Bang success))))))))))))))
  