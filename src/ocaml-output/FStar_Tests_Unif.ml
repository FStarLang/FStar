open Prims
let (tcenv : unit -> FStar_TypeChecker_Env.env) =
  fun uu____78889  -> FStar_Tests_Pars.init () 
let (guard_to_string :
  FStar_TypeChecker_Common.guard_formula -> Prims.string) =
  fun g  ->
    match g with
    | FStar_TypeChecker_Common.Trivial  -> "trivial"
    | FStar_TypeChecker_Common.NonTrivial f ->
        let uu____78900 = tcenv ()  in
        FStar_TypeChecker_Normalize.term_to_string uu____78900 f
  
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
        let uu____78956 =
          match (g, g') with
          | (FStar_TypeChecker_Common.Trivial
             ,FStar_TypeChecker_Common.Trivial ) -> (true, g, g')
          | (FStar_TypeChecker_Common.NonTrivial
             f,FStar_TypeChecker_Common.NonTrivial f') ->
              let f1 =
                let uu____78976 = tcenv ()  in
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Env.EraseUniverses] uu____78976 f
                 in
              let f'1 =
                let uu____78978 = tcenv ()  in
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Env.EraseUniverses] uu____78978 f'
                 in
              let uu____78979 = FStar_Tests_Util.term_eq f1 f'1  in
              (uu____78979, (FStar_TypeChecker_Common.NonTrivial f1),
                (FStar_TypeChecker_Common.NonTrivial f'1))
          | uu____78982 -> (false, g, g')  in
        match uu____78956 with
        | (b,g1,g'1) ->
            (if Prims.op_Negation b
             then
               (let uu____78996 =
                  let uu____78998 = FStar_Util.string_of_int i  in
                  let uu____79000 = guard_to_string g'1  in
                  let uu____79002 = guard_to_string g1  in
                  FStar_Util.format3
                    "Test %s failed:\n\tExpected guard %s;\n\tGot guard      %s\n"
                    uu____78998 uu____79000 uu____79002
                   in
                FStar_All.pipe_left fail uu____78996)
             else ();
             (let uu____79008 = (FStar_ST.op_Bang success) && b  in
              FStar_ST.op_Colon_Equals success uu____79008))
  
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
            (let uu____79094 = FStar_Util.string_of_int i  in
             FStar_Util.print1 "%s ..." uu____79094);
            (let uu____79098 = FStar_Main.process_args ()  in
             FStar_All.pipe_right uu____79098 (fun a1  -> ()));
            (let uu____79114 = FStar_Syntax_Print.term_to_string x1  in
             let uu____79116 = FStar_Syntax_Print.term_to_string y1  in
             FStar_Util.print2 "Unify %s\nand %s\n" uu____79114 uu____79116);
            (let g =
               let uu____79120 =
                 let uu____79121 =
                   let uu____79122 = tcenv ()  in
                   FStar_TypeChecker_Rel.teq uu____79122 x1 y1  in
                 let uu____79123 =
                   let uu____79128 = tcenv ()  in
                   FStar_TypeChecker_Rel.solve_deferred_constraints
                     uu____79128
                    in
                 FStar_All.pipe_right uu____79121 uu____79123  in
               let uu____79129 =
                 let uu____79134 = tcenv ()  in
                 FStar_TypeChecker_Rel.simplify_guard uu____79134  in
               FStar_All.pipe_right uu____79120 uu____79129  in
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
        (fun uu___783_79159  ->
           match () with
           | () ->
               let g =
                 let uu____79161 =
                   let uu____79162 = tcenv ()  in
                   FStar_TypeChecker_Rel.teq uu____79162 x1 y1  in
                 let uu____79163 =
                   let uu____79168 = tcenv ()  in
                   FStar_TypeChecker_Rel.solve_deferred_constraints
                     uu____79168
                    in
                 FStar_All.pipe_right uu____79161 uu____79163  in
               (match g.FStar_TypeChecker_Env.guard_f with
                | FStar_TypeChecker_Common.Trivial  ->
                    let uu____79169 =
                      let uu____79171 = FStar_Syntax_Print.term_to_string x1
                         in
                      let uu____79173 = FStar_Syntax_Print.term_to_string y1
                         in
                      FStar_Util.format2
                        "%s and %s should not be unifiable\n" uu____79171
                        uu____79173
                       in
                    fail uu____79169
                | FStar_TypeChecker_Common.NonTrivial f ->
                    let uu____79177 = FStar_Syntax_Print.term_to_string x1
                       in
                    let uu____79179 = FStar_Syntax_Print.term_to_string y1
                       in
                    let uu____79181 = FStar_Syntax_Print.term_to_string f  in
                    FStar_Util.print3 "%s and %s are unifiable if %s\n"
                      uu____79177 uu____79179 uu____79181)) ()
      with | FStar_Errors.Error (e,msg,r) -> FStar_Util.print1 "%s\n" msg
  
let (unify' : Prims.string -> Prims.string -> unit) =
  fun x1  ->
    fun y1  ->
      let x2 = FStar_Tests_Pars.pars x1  in
      let y2 = FStar_Tests_Pars.pars y1  in
      let g =
        let uu____79213 =
          let uu____79214 = tcenv ()  in
          FStar_TypeChecker_Rel.teq uu____79214 x2 y2  in
        let uu____79215 =
          let uu____79220 = tcenv ()  in
          FStar_TypeChecker_Rel.solve_deferred_constraints uu____79220  in
        FStar_All.pipe_right uu____79213 uu____79215  in
      let uu____79221 = FStar_Syntax_Print.term_to_string x2  in
      let uu____79223 = FStar_Syntax_Print.term_to_string y2  in
      let uu____79225 = guard_to_string g.FStar_TypeChecker_Env.guard_f  in
      FStar_Util.print3 "%s and %s are unifiable with guard %s\n" uu____79221
        uu____79223 uu____79225
  
let (norm : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____79234 = tcenv ()  in
    FStar_TypeChecker_Normalize.normalize [] uu____79234 t
  
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
          (let uu____79284 =
             let uu____79297 = FStar_Tests_Pars.init ()  in
             FStar_TypeChecker_Util.new_implicit_var ""
               FStar_Range.dummyRange uu____79297 FStar_Syntax_Util.ktype0
              in
           match uu____79284 with
           | (t,uu____79302,uu____79303) ->
               let uu____79316 =
                 let uu____79329 = FStar_Tests_Pars.init ()  in
                 FStar_TypeChecker_Util.new_implicit_var ""
                   FStar_Range.dummyRange uu____79329 t
                  in
               (match uu____79316 with
                | (u,uu____79334,uu____79335) ->
                    aux (u :: out) (n2 - (Prims.parse_int "1"))))
         in
      let us = aux [] n1  in
      let uu____79352 =
        let uu____79353 = FStar_Tests_Util.app tm1 us  in norm uu____79353
         in
      (uu____79352, us)
  
let (run_all : unit -> Prims.bool) =
  fun uu____79362  ->
    FStar_Util.print_string "Testing the unifier\n";
    FStar_Options.__set_unit_tests ();
    (let unify_check n1 x1 y1 g f = unify n1 x1 y1 g f  in
     let unify1 n1 x1 y1 g = unify n1 x1 y1 g (fun uu____79439  -> ())  in
     let int_t = FStar_Tests_Pars.tc "Prims.int"  in
     let x1 =
       let uu____79445 =
         FStar_Syntax_Syntax.gen_bv "x" FStar_Pervasives_Native.None int_t
          in
       FStar_All.pipe_right uu____79445 FStar_Syntax_Syntax.bv_to_name  in
     let y1 =
       let uu____79452 =
         FStar_Syntax_Syntax.gen_bv "y" FStar_Pervasives_Native.None int_t
          in
       FStar_All.pipe_right uu____79452 FStar_Syntax_Syntax.bv_to_name  in
     unify1 (Prims.parse_int "0") x1 x1 FStar_TypeChecker_Common.Trivial;
     (let uu____79459 =
        let uu____79460 =
          FStar_Syntax_Util.mk_eq2 FStar_Syntax_Syntax.U_zero
            FStar_Syntax_Util.t_bool x1 y1
           in
        FStar_TypeChecker_Common.NonTrivial uu____79460  in
      unify1 (Prims.parse_int "1") x1 y1 uu____79459);
     (let id1 = FStar_Tests_Pars.tc "fun x -> x"  in
      (let uu____79465 = FStar_Tests_Util.app id1 [x1]  in
       unify1 (Prims.parse_int "2") x1 uu____79465
         FStar_TypeChecker_Common.Trivial);
      (let id2 = FStar_Tests_Pars.tc "fun x -> x"  in
       unify1 (Prims.parse_int "3") id2 id2 FStar_TypeChecker_Common.Trivial;
       (let id3 = FStar_Tests_Pars.tc "fun x -> x"  in
        let id' = FStar_Tests_Pars.tc "fun y -> y"  in
        unify1 (Prims.parse_int "4") id3 id' FStar_TypeChecker_Common.Trivial;
        (let uu____79480 = FStar_Tests_Pars.tc "fun x y -> x"  in
         let uu____79484 = FStar_Tests_Pars.tc "fun a b -> a"  in
         unify1 (Prims.parse_int "5") uu____79480 uu____79484
           FStar_TypeChecker_Common.Trivial);
        (let uu____79490 = FStar_Tests_Pars.tc "fun x y z -> y"  in
         let uu____79494 = FStar_Tests_Pars.tc "fun a b c -> b"  in
         unify1 (Prims.parse_int "6") uu____79490 uu____79494
           FStar_TypeChecker_Common.Trivial);
        (let uu____79500 = FStar_Tests_Pars.tc "fun (x:int) (y:int) -> y"  in
         let uu____79504 = FStar_Tests_Pars.tc "fun (x:int) (y:int) -> x"  in
         let uu____79508 =
           let uu____79509 =
             FStar_Tests_Pars.tc "(forall (x:int). (forall (y:int). y==x))"
              in
           FStar_TypeChecker_Common.NonTrivial uu____79509  in
         unify1 (Prims.parse_int "7") uu____79500 uu____79504 uu____79508);
        (let uu____79513 =
           FStar_Tests_Pars.tc "fun (x:int) (y:int) (z:int) -> y"  in
         let uu____79517 =
           FStar_Tests_Pars.tc "fun (x:int) (y:int) (z:int) -> z"  in
         let uu____79521 =
           let uu____79522 =
             FStar_Tests_Pars.tc
               "(forall (x:int). (forall (y:int). (forall (z:int). y==z)))"
              in
           FStar_TypeChecker_Common.NonTrivial uu____79522  in
         unify1 (Prims.parse_int "8") uu____79513 uu____79517 uu____79521);
        (let uu____79526 = FStar_Main.process_args ()  in
         FStar_All.pipe_right uu____79526 (fun a2  -> ()));
        (let uu____79541 =
           let uu____79548 = FStar_Tests_Pars.tc "fun u x -> u x"  in
           inst (Prims.parse_int "1") uu____79548  in
         match uu____79541 with
         | (tm1,us) ->
             let sol = FStar_Tests_Pars.tc "fun x -> c_and x x"  in
             (unify_check (Prims.parse_int "9") tm1 sol
                FStar_TypeChecker_Common.Trivial
                (fun uu____79566  ->
                   let uu____79567 =
                     let uu____79569 =
                       let uu____79572 = FStar_List.hd us  in
                       norm uu____79572  in
                     let uu____79573 = norm sol  in
                     FStar_Tests_Util.term_eq uu____79569 uu____79573  in
                   FStar_Tests_Util.always (Prims.parse_int "9") uu____79567);
              (let uu____79577 =
                 let uu____79584 = FStar_Tests_Pars.tc "fun u x -> u x"  in
                 inst (Prims.parse_int "1") uu____79584  in
               match uu____79577 with
               | (tm2,us1) ->
                   let sol1 = FStar_Tests_Pars.tc "fun x y -> x + y"  in
                   (unify_check (Prims.parse_int "10") tm2 sol1
                      FStar_TypeChecker_Common.Trivial
                      (fun uu____79602  ->
                         let uu____79603 =
                           let uu____79605 =
                             let uu____79608 = FStar_List.hd us1  in
                             norm uu____79608  in
                           let uu____79609 = norm sol1  in
                           FStar_Tests_Util.term_eq uu____79605 uu____79609
                            in
                         FStar_Tests_Util.always (Prims.parse_int "10")
                           uu____79603);
                    (let tm11 =
                       FStar_Tests_Pars.tc "x:int -> y:int{eq2 y x} -> bool"
                        in
                     let tm21 = FStar_Tests_Pars.tc "x:int -> y:int -> bool"
                        in
                     (let uu____79618 =
                        let uu____79619 =
                          FStar_Tests_Pars.tc
                            "forall (x:int). (forall (y:int). y==x)"
                           in
                        FStar_TypeChecker_Common.NonTrivial uu____79619  in
                      unify1 (Prims.parse_int "11") tm11 tm21 uu____79618);
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
                      (let uu____79628 =
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
                           let uu____79646 =
                             let uu____79647 =
                               let uu____79650 =
                                 FStar_Syntax_Syntax.bv_to_name q  in
                               [uu____79650]  in
                             FStar_Tests_Util.app l uu____79647  in
                           norm uu____79646  in
                         let l1 =
                           FStar_Tests_Pars.tc "fun (p:unit -> Type0) -> p"
                            in
                         let unit = FStar_Tests_Pars.tc "()"  in
                         let env =
                           let uu____79656 = FStar_Tests_Pars.init ()  in
                           let uu____79657 =
                             let uu____79658 =
                               FStar_Syntax_Syntax.mk_binder x2  in
                             let uu____79665 =
                               let uu____79674 =
                                 FStar_Syntax_Syntax.mk_binder q  in
                               [uu____79674]  in
                             uu____79658 :: uu____79665  in
                           FStar_TypeChecker_Env.push_binders uu____79656
                             uu____79657
                            in
                         let uu____79699 =
                           FStar_TypeChecker_Util.new_implicit_var ""
                             FStar_Range.dummyRange env typ
                            in
                         match uu____79699 with
                         | (u_p,uu____79722,uu____79723) ->
                             let tm23 =
                               let uu____79739 =
                                 let uu____79742 =
                                   FStar_Tests_Util.app l1 [u_p]  in
                                 norm uu____79742  in
                               FStar_Tests_Util.app uu____79739 [unit]  in
                             (tm13, tm23)
                          in
                       match uu____79628 with
                       | (tm13,tm23) ->
                           (unify1 (Prims.parse_int "13") tm13 tm23
                              FStar_TypeChecker_Common.Trivial;
                            (let uu____79760 =
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
                                 let uu____79778 =
                                   let uu____79779 =
                                     let uu____79782 =
                                       FStar_Syntax_Syntax.bv_to_name q  in
                                     [uu____79782]  in
                                   FStar_Tests_Util.app l uu____79779  in
                                 norm uu____79778  in
                               let l1 =
                                 FStar_Tests_Pars.tc
                                   "fun (p:pure_post unit) -> p"
                                  in
                               let unit = FStar_Tests_Pars.tc "()"  in
                               let env =
                                 let uu____79788 = FStar_Tests_Pars.init ()
                                    in
                                 let uu____79789 =
                                   let uu____79790 =
                                     FStar_Syntax_Syntax.mk_binder x2  in
                                   let uu____79797 =
                                     let uu____79806 =
                                       FStar_Syntax_Syntax.mk_binder q  in
                                     [uu____79806]  in
                                   uu____79790 :: uu____79797  in
                                 FStar_TypeChecker_Env.push_binders
                                   uu____79788 uu____79789
                                  in
                               let uu____79831 =
                                 FStar_TypeChecker_Util.new_implicit_var ""
                                   FStar_Range.dummyRange env typ
                                  in
                               match uu____79831 with
                               | (u_p,uu____79854,uu____79855) ->
                                   let tm24 =
                                     let uu____79871 =
                                       let uu____79874 =
                                         FStar_Tests_Util.app l1 [u_p]  in
                                       norm uu____79874  in
                                     FStar_Tests_Util.app uu____79871 [unit]
                                      in
                                   (tm14, tm24)
                                in
                             match uu____79760 with
                             | (tm14,tm24) ->
                                 (unify1 (Prims.parse_int "14") tm14 tm24
                                    FStar_TypeChecker_Common.Trivial;
                                  FStar_Options.__clear_unit_tests ();
                                  (let uu____79894 = FStar_ST.op_Bang success
                                      in
                                   if uu____79894
                                   then
                                     FStar_Util.print_string "Unifier ok\n"
                                   else ());
                                  FStar_ST.op_Bang success))))))))))))))
  