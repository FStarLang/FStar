open Prims
let (tcenv : unit -> FStar_TypeChecker_Env.env) =
  fun uu____78833  -> FStar_Tests_Pars.init () 
let (guard_to_string :
  FStar_TypeChecker_Common.guard_formula -> Prims.string) =
  fun g  ->
    match g with
    | FStar_TypeChecker_Common.Trivial  -> "trivial"
    | FStar_TypeChecker_Common.NonTrivial f ->
        let uu____78844 = tcenv ()  in
        FStar_TypeChecker_Normalize.term_to_string uu____78844 f
  
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
        let uu____78900 =
          match (g, g') with
          | (FStar_TypeChecker_Common.Trivial
             ,FStar_TypeChecker_Common.Trivial ) -> (true, g, g')
          | (FStar_TypeChecker_Common.NonTrivial
             f,FStar_TypeChecker_Common.NonTrivial f') ->
              let f1 =
                let uu____78920 = tcenv ()  in
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Env.EraseUniverses] uu____78920 f
                 in
              let f'1 =
                let uu____78922 = tcenv ()  in
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Env.EraseUniverses] uu____78922 f'
                 in
              let uu____78923 = FStar_Tests_Util.term_eq f1 f'1  in
              (uu____78923, (FStar_TypeChecker_Common.NonTrivial f1),
                (FStar_TypeChecker_Common.NonTrivial f'1))
          | uu____78926 -> (false, g, g')  in
        match uu____78900 with
        | (b,g1,g'1) ->
            (if Prims.op_Negation b
             then
               (let uu____78940 =
                  let uu____78942 = FStar_Util.string_of_int i  in
                  let uu____78944 = guard_to_string g'1  in
                  let uu____78946 = guard_to_string g1  in
                  FStar_Util.format3
                    "Test %s failed:\n\tExpected guard %s;\n\tGot guard      %s\n"
                    uu____78942 uu____78944 uu____78946
                   in
                FStar_All.pipe_left fail uu____78940)
             else ();
             (let uu____78952 = (FStar_ST.op_Bang success) && b  in
              FStar_ST.op_Colon_Equals success uu____78952))
  
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
            (let uu____79038 = FStar_Util.string_of_int i  in
             FStar_Util.print1 "%s ..." uu____79038);
            (let uu____79042 = FStar_Main.process_args ()  in
             FStar_All.pipe_right uu____79042 (fun a1  -> ()));
            (let uu____79058 = FStar_Syntax_Print.term_to_string x1  in
             let uu____79060 = FStar_Syntax_Print.term_to_string y1  in
             FStar_Util.print2 "Unify %s\nand %s\n" uu____79058 uu____79060);
            (let g =
               let uu____79064 =
                 let uu____79065 =
                   let uu____79066 = tcenv ()  in
                   FStar_TypeChecker_Rel.teq uu____79066 x1 y1  in
                 let uu____79067 =
                   let uu____79072 = tcenv ()  in
                   FStar_TypeChecker_Rel.solve_deferred_constraints
                     uu____79072
                    in
                 FStar_All.pipe_right uu____79065 uu____79067  in
               let uu____79073 =
                 let uu____79078 = tcenv ()  in
                 FStar_TypeChecker_Rel.simplify_guard uu____79078  in
               FStar_All.pipe_right uu____79064 uu____79073  in
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
        (fun uu___783_79103  ->
           match () with
           | () ->
               let g =
                 let uu____79105 =
                   let uu____79106 = tcenv ()  in
                   FStar_TypeChecker_Rel.teq uu____79106 x1 y1  in
                 let uu____79107 =
                   let uu____79112 = tcenv ()  in
                   FStar_TypeChecker_Rel.solve_deferred_constraints
                     uu____79112
                    in
                 FStar_All.pipe_right uu____79105 uu____79107  in
               (match g.FStar_TypeChecker_Env.guard_f with
                | FStar_TypeChecker_Common.Trivial  ->
                    let uu____79113 =
                      let uu____79115 = FStar_Syntax_Print.term_to_string x1
                         in
                      let uu____79117 = FStar_Syntax_Print.term_to_string y1
                         in
                      FStar_Util.format2
                        "%s and %s should not be unifiable\n" uu____79115
                        uu____79117
                       in
                    fail uu____79113
                | FStar_TypeChecker_Common.NonTrivial f ->
                    let uu____79121 = FStar_Syntax_Print.term_to_string x1
                       in
                    let uu____79123 = FStar_Syntax_Print.term_to_string y1
                       in
                    let uu____79125 = FStar_Syntax_Print.term_to_string f  in
                    FStar_Util.print3 "%s and %s are unifiable if %s\n"
                      uu____79121 uu____79123 uu____79125)) ()
      with | FStar_Errors.Error (e,msg,r) -> FStar_Util.print1 "%s\n" msg
  
let (unify' : Prims.string -> Prims.string -> unit) =
  fun x1  ->
    fun y1  ->
      let x2 = FStar_Tests_Pars.pars x1  in
      let y2 = FStar_Tests_Pars.pars y1  in
      let g =
        let uu____79157 =
          let uu____79158 = tcenv ()  in
          FStar_TypeChecker_Rel.teq uu____79158 x2 y2  in
        let uu____79159 =
          let uu____79164 = tcenv ()  in
          FStar_TypeChecker_Rel.solve_deferred_constraints uu____79164  in
        FStar_All.pipe_right uu____79157 uu____79159  in
      let uu____79165 = FStar_Syntax_Print.term_to_string x2  in
      let uu____79167 = FStar_Syntax_Print.term_to_string y2  in
      let uu____79169 = guard_to_string g.FStar_TypeChecker_Env.guard_f  in
      FStar_Util.print3 "%s and %s are unifiable with guard %s\n" uu____79165
        uu____79167 uu____79169
  
let (norm : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____79178 = tcenv ()  in
    FStar_TypeChecker_Normalize.normalize [] uu____79178 t
  
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
          (let uu____79228 =
             let uu____79241 = FStar_Tests_Pars.init ()  in
             FStar_TypeChecker_Util.new_implicit_var ""
               FStar_Range.dummyRange uu____79241 FStar_Syntax_Util.ktype0
              in
           match uu____79228 with
           | (t,uu____79246,uu____79247) ->
               let uu____79260 =
                 let uu____79273 = FStar_Tests_Pars.init ()  in
                 FStar_TypeChecker_Util.new_implicit_var ""
                   FStar_Range.dummyRange uu____79273 t
                  in
               (match uu____79260 with
                | (u,uu____79278,uu____79279) ->
                    aux (u :: out) (n2 - (Prims.parse_int "1"))))
         in
      let us = aux [] n1  in
      let uu____79296 =
        let uu____79297 = FStar_Tests_Util.app tm1 us  in norm uu____79297
         in
      (uu____79296, us)
  
let (run_all : unit -> Prims.bool) =
  fun uu____79306  ->
    FStar_Util.print_string "Testing the unifier\n";
    FStar_Options.__set_unit_tests ();
    (let unify_check n1 x1 y1 g f = unify n1 x1 y1 g f  in
     let unify1 n1 x1 y1 g = unify n1 x1 y1 g (fun uu____79383  -> ())  in
     let int_t = FStar_Tests_Pars.tc "Prims.int"  in
     let x1 =
       let uu____79389 =
         FStar_Syntax_Syntax.gen_bv "x" FStar_Pervasives_Native.None int_t
          in
       FStar_All.pipe_right uu____79389 FStar_Syntax_Syntax.bv_to_name  in
     let y1 =
       let uu____79396 =
         FStar_Syntax_Syntax.gen_bv "y" FStar_Pervasives_Native.None int_t
          in
       FStar_All.pipe_right uu____79396 FStar_Syntax_Syntax.bv_to_name  in
     unify1 (Prims.parse_int "0") x1 x1 FStar_TypeChecker_Common.Trivial;
     (let uu____79403 =
        let uu____79404 =
          FStar_Syntax_Util.mk_eq2 FStar_Syntax_Syntax.U_zero
            FStar_Syntax_Util.t_bool x1 y1
           in
        FStar_TypeChecker_Common.NonTrivial uu____79404  in
      unify1 (Prims.parse_int "1") x1 y1 uu____79403);
     (let id1 = FStar_Tests_Pars.tc "fun x -> x"  in
      (let uu____79409 = FStar_Tests_Util.app id1 [x1]  in
       unify1 (Prims.parse_int "2") x1 uu____79409
         FStar_TypeChecker_Common.Trivial);
      (let id2 = FStar_Tests_Pars.tc "fun x -> x"  in
       unify1 (Prims.parse_int "3") id2 id2 FStar_TypeChecker_Common.Trivial;
       (let id3 = FStar_Tests_Pars.tc "fun x -> x"  in
        let id' = FStar_Tests_Pars.tc "fun y -> y"  in
        unify1 (Prims.parse_int "4") id3 id' FStar_TypeChecker_Common.Trivial;
        (let uu____79424 = FStar_Tests_Pars.tc "fun x y -> x"  in
         let uu____79428 = FStar_Tests_Pars.tc "fun a b -> a"  in
         unify1 (Prims.parse_int "5") uu____79424 uu____79428
           FStar_TypeChecker_Common.Trivial);
        (let uu____79434 = FStar_Tests_Pars.tc "fun x y z -> y"  in
         let uu____79438 = FStar_Tests_Pars.tc "fun a b c -> b"  in
         unify1 (Prims.parse_int "6") uu____79434 uu____79438
           FStar_TypeChecker_Common.Trivial);
        (let uu____79444 = FStar_Tests_Pars.tc "fun (x:int) (y:int) -> y"  in
         let uu____79448 = FStar_Tests_Pars.tc "fun (x:int) (y:int) -> x"  in
         let uu____79452 =
           let uu____79453 =
             FStar_Tests_Pars.tc "(forall (x:int). (forall (y:int). y==x))"
              in
           FStar_TypeChecker_Common.NonTrivial uu____79453  in
         unify1 (Prims.parse_int "7") uu____79444 uu____79448 uu____79452);
        (let uu____79457 =
           FStar_Tests_Pars.tc "fun (x:int) (y:int) (z:int) -> y"  in
         let uu____79461 =
           FStar_Tests_Pars.tc "fun (x:int) (y:int) (z:int) -> z"  in
         let uu____79465 =
           let uu____79466 =
             FStar_Tests_Pars.tc
               "(forall (x:int). (forall (y:int). (forall (z:int). y==z)))"
              in
           FStar_TypeChecker_Common.NonTrivial uu____79466  in
         unify1 (Prims.parse_int "8") uu____79457 uu____79461 uu____79465);
        (let uu____79470 = FStar_Main.process_args ()  in
         FStar_All.pipe_right uu____79470 (fun a2  -> ()));
        (let uu____79485 =
           let uu____79492 = FStar_Tests_Pars.tc "fun u x -> u x"  in
           inst (Prims.parse_int "1") uu____79492  in
         match uu____79485 with
         | (tm1,us) ->
             let sol = FStar_Tests_Pars.tc "fun x -> c_and x x"  in
             (unify_check (Prims.parse_int "9") tm1 sol
                FStar_TypeChecker_Common.Trivial
                (fun uu____79510  ->
                   let uu____79511 =
                     let uu____79513 =
                       let uu____79516 = FStar_List.hd us  in
                       norm uu____79516  in
                     let uu____79517 = norm sol  in
                     FStar_Tests_Util.term_eq uu____79513 uu____79517  in
                   FStar_Tests_Util.always (Prims.parse_int "9") uu____79511);
              (let uu____79521 =
                 let uu____79528 = FStar_Tests_Pars.tc "fun u x -> u x"  in
                 inst (Prims.parse_int "1") uu____79528  in
               match uu____79521 with
               | (tm2,us1) ->
                   let sol1 = FStar_Tests_Pars.tc "fun x y -> x + y"  in
                   (unify_check (Prims.parse_int "10") tm2 sol1
                      FStar_TypeChecker_Common.Trivial
                      (fun uu____79546  ->
                         let uu____79547 =
                           let uu____79549 =
                             let uu____79552 = FStar_List.hd us1  in
                             norm uu____79552  in
                           let uu____79553 = norm sol1  in
                           FStar_Tests_Util.term_eq uu____79549 uu____79553
                            in
                         FStar_Tests_Util.always (Prims.parse_int "10")
                           uu____79547);
                    (let tm11 =
                       FStar_Tests_Pars.tc "x:int -> y:int{eq2 y x} -> bool"
                        in
                     let tm21 = FStar_Tests_Pars.tc "x:int -> y:int -> bool"
                        in
                     (let uu____79562 =
                        let uu____79563 =
                          FStar_Tests_Pars.tc
                            "forall (x:int). (forall (y:int). y==x)"
                           in
                        FStar_TypeChecker_Common.NonTrivial uu____79563  in
                      unify1 (Prims.parse_int "11") tm11 tm21 uu____79562);
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
                      (let uu____79572 =
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
                           let uu____79590 =
                             let uu____79591 =
                               let uu____79594 =
                                 FStar_Syntax_Syntax.bv_to_name q  in
                               [uu____79594]  in
                             FStar_Tests_Util.app l uu____79591  in
                           norm uu____79590  in
                         let l1 =
                           FStar_Tests_Pars.tc "fun (p:unit -> Type0) -> p"
                            in
                         let unit = FStar_Tests_Pars.tc "()"  in
                         let env =
                           let uu____79600 = FStar_Tests_Pars.init ()  in
                           let uu____79601 =
                             let uu____79602 =
                               FStar_Syntax_Syntax.mk_binder x2  in
                             let uu____79609 =
                               let uu____79618 =
                                 FStar_Syntax_Syntax.mk_binder q  in
                               [uu____79618]  in
                             uu____79602 :: uu____79609  in
                           FStar_TypeChecker_Env.push_binders uu____79600
                             uu____79601
                            in
                         let uu____79643 =
                           FStar_TypeChecker_Util.new_implicit_var ""
                             FStar_Range.dummyRange env typ
                            in
                         match uu____79643 with
                         | (u_p,uu____79666,uu____79667) ->
                             let tm23 =
                               let uu____79683 =
                                 let uu____79686 =
                                   FStar_Tests_Util.app l1 [u_p]  in
                                 norm uu____79686  in
                               FStar_Tests_Util.app uu____79683 [unit]  in
                             (tm13, tm23)
                          in
                       match uu____79572 with
                       | (tm13,tm23) ->
                           (unify1 (Prims.parse_int "13") tm13 tm23
                              FStar_TypeChecker_Common.Trivial;
                            (let uu____79704 =
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
                                 let uu____79722 =
                                   let uu____79723 =
                                     let uu____79726 =
                                       FStar_Syntax_Syntax.bv_to_name q  in
                                     [uu____79726]  in
                                   FStar_Tests_Util.app l uu____79723  in
                                 norm uu____79722  in
                               let l1 =
                                 FStar_Tests_Pars.tc
                                   "fun (p:pure_post unit) -> p"
                                  in
                               let unit = FStar_Tests_Pars.tc "()"  in
                               let env =
                                 let uu____79732 = FStar_Tests_Pars.init ()
                                    in
                                 let uu____79733 =
                                   let uu____79734 =
                                     FStar_Syntax_Syntax.mk_binder x2  in
                                   let uu____79741 =
                                     let uu____79750 =
                                       FStar_Syntax_Syntax.mk_binder q  in
                                     [uu____79750]  in
                                   uu____79734 :: uu____79741  in
                                 FStar_TypeChecker_Env.push_binders
                                   uu____79732 uu____79733
                                  in
                               let uu____79775 =
                                 FStar_TypeChecker_Util.new_implicit_var ""
                                   FStar_Range.dummyRange env typ
                                  in
                               match uu____79775 with
                               | (u_p,uu____79798,uu____79799) ->
                                   let tm24 =
                                     let uu____79815 =
                                       let uu____79818 =
                                         FStar_Tests_Util.app l1 [u_p]  in
                                       norm uu____79818  in
                                     FStar_Tests_Util.app uu____79815 [unit]
                                      in
                                   (tm14, tm24)
                                in
                             match uu____79704 with
                             | (tm14,tm24) ->
                                 (unify1 (Prims.parse_int "14") tm14 tm24
                                    FStar_TypeChecker_Common.Trivial;
                                  FStar_Options.__clear_unit_tests ();
                                  (let uu____79838 = FStar_ST.op_Bang success
                                      in
                                   if uu____79838
                                   then
                                     FStar_Util.print_string "Unifier ok\n"
                                   else ());
                                  FStar_ST.op_Bang success))))))))))))))
  