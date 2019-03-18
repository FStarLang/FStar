open Prims
let (tcenv : unit -> FStar_TypeChecker_Env.env) =
  fun uu____79001  -> FStar_Tests_Pars.init () 
let (guard_to_string :
  FStar_TypeChecker_Common.guard_formula -> Prims.string) =
  fun g  ->
    match g with
    | FStar_TypeChecker_Common.Trivial  -> "trivial"
    | FStar_TypeChecker_Common.NonTrivial f ->
        let uu____79012 = tcenv ()  in
        FStar_TypeChecker_Normalize.term_to_string uu____79012 f
  
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
        let uu____79068 =
          match (g, g') with
          | (FStar_TypeChecker_Common.Trivial
             ,FStar_TypeChecker_Common.Trivial ) -> (true, g, g')
          | (FStar_TypeChecker_Common.NonTrivial
             f,FStar_TypeChecker_Common.NonTrivial f') ->
              let f1 =
                let uu____79088 = tcenv ()  in
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Env.EraseUniverses] uu____79088 f
                 in
              let f'1 =
                let uu____79090 = tcenv ()  in
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Env.EraseUniverses] uu____79090 f'
                 in
              let uu____79091 = FStar_Tests_Util.term_eq f1 f'1  in
              (uu____79091, (FStar_TypeChecker_Common.NonTrivial f1),
                (FStar_TypeChecker_Common.NonTrivial f'1))
          | uu____79094 -> (false, g, g')  in
        match uu____79068 with
        | (b,g1,g'1) ->
            (if Prims.op_Negation b
             then
               (let uu____79108 =
                  let uu____79110 = FStar_Util.string_of_int i  in
                  let uu____79112 = guard_to_string g'1  in
                  let uu____79114 = guard_to_string g1  in
                  FStar_Util.format3
                    "Test %s failed:\n\tExpected guard %s;\n\tGot guard      %s\n"
                    uu____79110 uu____79112 uu____79114
                   in
                FStar_All.pipe_left fail uu____79108)
             else ();
             (let uu____79120 = (FStar_ST.op_Bang success) && b  in
              FStar_ST.op_Colon_Equals success uu____79120))
  
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
            (let uu____79206 = FStar_Util.string_of_int i  in
             FStar_Util.print1 "%s ..." uu____79206);
            (let uu____79210 = FStar_Main.process_args ()  in
             FStar_All.pipe_right uu____79210 (fun a1  -> ()));
            (let uu____79226 = FStar_Syntax_Print.term_to_string x1  in
             let uu____79228 = FStar_Syntax_Print.term_to_string y1  in
             FStar_Util.print2 "Unify %s\nand %s\n" uu____79226 uu____79228);
            (let g =
               let uu____79232 =
                 let uu____79233 =
                   let uu____79234 = tcenv ()  in
                   FStar_TypeChecker_Rel.teq uu____79234 x1 y1  in
                 let uu____79235 =
                   let uu____79240 = tcenv ()  in
                   FStar_TypeChecker_Rel.solve_deferred_constraints
                     uu____79240
                    in
                 FStar_All.pipe_right uu____79233 uu____79235  in
               let uu____79241 =
                 let uu____79246 = tcenv ()  in
                 FStar_TypeChecker_Rel.simplify_guard uu____79246  in
               FStar_All.pipe_right uu____79232 uu____79241  in
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
        (fun uu___783_79271  ->
           match () with
           | () ->
               let g =
                 let uu____79273 =
                   let uu____79274 = tcenv ()  in
                   FStar_TypeChecker_Rel.teq uu____79274 x1 y1  in
                 let uu____79275 =
                   let uu____79280 = tcenv ()  in
                   FStar_TypeChecker_Rel.solve_deferred_constraints
                     uu____79280
                    in
                 FStar_All.pipe_right uu____79273 uu____79275  in
               (match g.FStar_TypeChecker_Env.guard_f with
                | FStar_TypeChecker_Common.Trivial  ->
                    let uu____79281 =
                      let uu____79283 = FStar_Syntax_Print.term_to_string x1
                         in
                      let uu____79285 = FStar_Syntax_Print.term_to_string y1
                         in
                      FStar_Util.format2
                        "%s and %s should not be unifiable\n" uu____79283
                        uu____79285
                       in
                    fail uu____79281
                | FStar_TypeChecker_Common.NonTrivial f ->
                    let uu____79289 = FStar_Syntax_Print.term_to_string x1
                       in
                    let uu____79291 = FStar_Syntax_Print.term_to_string y1
                       in
                    let uu____79293 = FStar_Syntax_Print.term_to_string f  in
                    FStar_Util.print3 "%s and %s are unifiable if %s\n"
                      uu____79289 uu____79291 uu____79293)) ()
      with | FStar_Errors.Error (e,msg,r) -> FStar_Util.print1 "%s\n" msg
  
let (unify' : Prims.string -> Prims.string -> unit) =
  fun x1  ->
    fun y1  ->
      let x2 = FStar_Tests_Pars.pars x1  in
      let y2 = FStar_Tests_Pars.pars y1  in
      let g =
        let uu____79325 =
          let uu____79326 = tcenv ()  in
          FStar_TypeChecker_Rel.teq uu____79326 x2 y2  in
        let uu____79327 =
          let uu____79332 = tcenv ()  in
          FStar_TypeChecker_Rel.solve_deferred_constraints uu____79332  in
        FStar_All.pipe_right uu____79325 uu____79327  in
      let uu____79333 = FStar_Syntax_Print.term_to_string x2  in
      let uu____79335 = FStar_Syntax_Print.term_to_string y2  in
      let uu____79337 = guard_to_string g.FStar_TypeChecker_Env.guard_f  in
      FStar_Util.print3 "%s and %s are unifiable with guard %s\n" uu____79333
        uu____79335 uu____79337
  
let (norm : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____79346 = tcenv ()  in
    FStar_TypeChecker_Normalize.normalize [] uu____79346 t
  
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
          (let uu____79396 =
             let uu____79409 = FStar_Tests_Pars.init ()  in
             FStar_TypeChecker_Util.new_implicit_var ""
               FStar_Range.dummyRange uu____79409 FStar_Syntax_Util.ktype0
              in
           match uu____79396 with
           | (t,uu____79414,uu____79415) ->
               let uu____79428 =
                 let uu____79441 = FStar_Tests_Pars.init ()  in
                 FStar_TypeChecker_Util.new_implicit_var ""
                   FStar_Range.dummyRange uu____79441 t
                  in
               (match uu____79428 with
                | (u,uu____79446,uu____79447) ->
                    aux (u :: out) (n2 - (Prims.parse_int "1"))))
         in
      let us = aux [] n1  in
      let uu____79464 =
        let uu____79465 = FStar_Tests_Util.app tm1 us  in norm uu____79465
         in
      (uu____79464, us)
  
let (run_all : unit -> Prims.bool) =
  fun uu____79474  ->
    FStar_Util.print_string "Testing the unifier\n";
    FStar_Options.__set_unit_tests ();
    (let unify_check n1 x1 y1 g f = unify n1 x1 y1 g f  in
     let unify1 n1 x1 y1 g = unify n1 x1 y1 g (fun uu____79551  -> ())  in
     let int_t = FStar_Tests_Pars.tc "Prims.int"  in
     let x1 =
       let uu____79557 =
         FStar_Syntax_Syntax.gen_bv "x" FStar_Pervasives_Native.None int_t
          in
       FStar_All.pipe_right uu____79557 FStar_Syntax_Syntax.bv_to_name  in
     let y1 =
       let uu____79564 =
         FStar_Syntax_Syntax.gen_bv "y" FStar_Pervasives_Native.None int_t
          in
       FStar_All.pipe_right uu____79564 FStar_Syntax_Syntax.bv_to_name  in
     unify1 (Prims.parse_int "0") x1 x1 FStar_TypeChecker_Common.Trivial;
     (let uu____79571 =
        let uu____79572 =
          FStar_Syntax_Util.mk_eq2 FStar_Syntax_Syntax.U_zero
            FStar_Syntax_Util.t_bool x1 y1
           in
        FStar_TypeChecker_Common.NonTrivial uu____79572  in
      unify1 (Prims.parse_int "1") x1 y1 uu____79571);
     (let id1 = FStar_Tests_Pars.tc "fun x -> x"  in
      (let uu____79577 = FStar_Tests_Util.app id1 [x1]  in
       unify1 (Prims.parse_int "2") x1 uu____79577
         FStar_TypeChecker_Common.Trivial);
      (let id2 = FStar_Tests_Pars.tc "fun x -> x"  in
       unify1 (Prims.parse_int "3") id2 id2 FStar_TypeChecker_Common.Trivial;
       (let id3 = FStar_Tests_Pars.tc "fun x -> x"  in
        let id' = FStar_Tests_Pars.tc "fun y -> y"  in
        unify1 (Prims.parse_int "4") id3 id' FStar_TypeChecker_Common.Trivial;
        (let uu____79592 = FStar_Tests_Pars.tc "fun x y -> x"  in
         let uu____79596 = FStar_Tests_Pars.tc "fun a b -> a"  in
         unify1 (Prims.parse_int "5") uu____79592 uu____79596
           FStar_TypeChecker_Common.Trivial);
        (let uu____79602 = FStar_Tests_Pars.tc "fun x y z -> y"  in
         let uu____79606 = FStar_Tests_Pars.tc "fun a b c -> b"  in
         unify1 (Prims.parse_int "6") uu____79602 uu____79606
           FStar_TypeChecker_Common.Trivial);
        (let uu____79612 = FStar_Tests_Pars.tc "fun (x:int) (y:int) -> y"  in
         let uu____79616 = FStar_Tests_Pars.tc "fun (x:int) (y:int) -> x"  in
         let uu____79620 =
           let uu____79621 =
             FStar_Tests_Pars.tc "(forall (x:int). (forall (y:int). y==x))"
              in
           FStar_TypeChecker_Common.NonTrivial uu____79621  in
         unify1 (Prims.parse_int "7") uu____79612 uu____79616 uu____79620);
        (let uu____79625 =
           FStar_Tests_Pars.tc "fun (x:int) (y:int) (z:int) -> y"  in
         let uu____79629 =
           FStar_Tests_Pars.tc "fun (x:int) (y:int) (z:int) -> z"  in
         let uu____79633 =
           let uu____79634 =
             FStar_Tests_Pars.tc
               "(forall (x:int). (forall (y:int). (forall (z:int). y==z)))"
              in
           FStar_TypeChecker_Common.NonTrivial uu____79634  in
         unify1 (Prims.parse_int "8") uu____79625 uu____79629 uu____79633);
        (let uu____79638 = FStar_Main.process_args ()  in
         FStar_All.pipe_right uu____79638 (fun a2  -> ()));
        (let uu____79653 =
           let uu____79660 = FStar_Tests_Pars.tc "fun u x -> u x"  in
           inst (Prims.parse_int "1") uu____79660  in
         match uu____79653 with
         | (tm1,us) ->
             let sol = FStar_Tests_Pars.tc "fun x -> c_and x x"  in
             (unify_check (Prims.parse_int "9") tm1 sol
                FStar_TypeChecker_Common.Trivial
                (fun uu____79678  ->
                   let uu____79679 =
                     let uu____79681 =
                       let uu____79684 = FStar_List.hd us  in
                       norm uu____79684  in
                     let uu____79685 = norm sol  in
                     FStar_Tests_Util.term_eq uu____79681 uu____79685  in
                   FStar_Tests_Util.always (Prims.parse_int "9") uu____79679);
              (let uu____79689 =
                 let uu____79696 = FStar_Tests_Pars.tc "fun u x -> u x"  in
                 inst (Prims.parse_int "1") uu____79696  in
               match uu____79689 with
               | (tm2,us1) ->
                   let sol1 = FStar_Tests_Pars.tc "fun x y -> x + y"  in
                   (unify_check (Prims.parse_int "10") tm2 sol1
                      FStar_TypeChecker_Common.Trivial
                      (fun uu____79714  ->
                         let uu____79715 =
                           let uu____79717 =
                             let uu____79720 = FStar_List.hd us1  in
                             norm uu____79720  in
                           let uu____79721 = norm sol1  in
                           FStar_Tests_Util.term_eq uu____79717 uu____79721
                            in
                         FStar_Tests_Util.always (Prims.parse_int "10")
                           uu____79715);
                    (let tm11 =
                       FStar_Tests_Pars.tc "x:int -> y:int{eq2 y x} -> bool"
                        in
                     let tm21 = FStar_Tests_Pars.tc "x:int -> y:int -> bool"
                        in
                     (let uu____79730 =
                        let uu____79731 =
                          FStar_Tests_Pars.tc
                            "forall (x:int). (forall (y:int). y==x)"
                           in
                        FStar_TypeChecker_Common.NonTrivial uu____79731  in
                      unify1 (Prims.parse_int "11") tm11 tm21 uu____79730);
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
                      (let uu____79740 =
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
                           let uu____79758 =
                             let uu____79759 =
                               let uu____79762 =
                                 FStar_Syntax_Syntax.bv_to_name q  in
                               [uu____79762]  in
                             FStar_Tests_Util.app l uu____79759  in
                           norm uu____79758  in
                         let l1 =
                           FStar_Tests_Pars.tc "fun (p:unit -> Type0) -> p"
                            in
                         let unit = FStar_Tests_Pars.tc "()"  in
                         let env =
                           let uu____79768 = FStar_Tests_Pars.init ()  in
                           let uu____79769 =
                             let uu____79770 =
                               FStar_Syntax_Syntax.mk_binder x2  in
                             let uu____79777 =
                               let uu____79786 =
                                 FStar_Syntax_Syntax.mk_binder q  in
                               [uu____79786]  in
                             uu____79770 :: uu____79777  in
                           FStar_TypeChecker_Env.push_binders uu____79768
                             uu____79769
                            in
                         let uu____79811 =
                           FStar_TypeChecker_Util.new_implicit_var ""
                             FStar_Range.dummyRange env typ
                            in
                         match uu____79811 with
                         | (u_p,uu____79834,uu____79835) ->
                             let tm23 =
                               let uu____79851 =
                                 let uu____79854 =
                                   FStar_Tests_Util.app l1 [u_p]  in
                                 norm uu____79854  in
                               FStar_Tests_Util.app uu____79851 [unit]  in
                             (tm13, tm23)
                          in
                       match uu____79740 with
                       | (tm13,tm23) ->
                           (unify1 (Prims.parse_int "13") tm13 tm23
                              FStar_TypeChecker_Common.Trivial;
                            (let uu____79872 =
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
                                 let uu____79890 =
                                   let uu____79891 =
                                     let uu____79894 =
                                       FStar_Syntax_Syntax.bv_to_name q  in
                                     [uu____79894]  in
                                   FStar_Tests_Util.app l uu____79891  in
                                 norm uu____79890  in
                               let l1 =
                                 FStar_Tests_Pars.tc
                                   "fun (p:pure_post unit) -> p"
                                  in
                               let unit = FStar_Tests_Pars.tc "()"  in
                               let env =
                                 let uu____79900 = FStar_Tests_Pars.init ()
                                    in
                                 let uu____79901 =
                                   let uu____79902 =
                                     FStar_Syntax_Syntax.mk_binder x2  in
                                   let uu____79909 =
                                     let uu____79918 =
                                       FStar_Syntax_Syntax.mk_binder q  in
                                     [uu____79918]  in
                                   uu____79902 :: uu____79909  in
                                 FStar_TypeChecker_Env.push_binders
                                   uu____79900 uu____79901
                                  in
                               let uu____79943 =
                                 FStar_TypeChecker_Util.new_implicit_var ""
                                   FStar_Range.dummyRange env typ
                                  in
                               match uu____79943 with
                               | (u_p,uu____79966,uu____79967) ->
                                   let tm24 =
                                     let uu____79983 =
                                       let uu____79986 =
                                         FStar_Tests_Util.app l1 [u_p]  in
                                       norm uu____79986  in
                                     FStar_Tests_Util.app uu____79983 [unit]
                                      in
                                   (tm14, tm24)
                                in
                             match uu____79872 with
                             | (tm14,tm24) ->
                                 (unify1 (Prims.parse_int "14") tm14 tm24
                                    FStar_TypeChecker_Common.Trivial;
                                  FStar_Options.__clear_unit_tests ();
                                  (let uu____80006 = FStar_ST.op_Bang success
                                      in
                                   if uu____80006
                                   then
                                     FStar_Util.print_string "Unifier ok\n"
                                   else ());
                                  FStar_ST.op_Bang success))))))))))))))
  