open Prims
let (tcenv : Prims.unit -> FStar_TypeChecker_Env.env) =
  fun uu____3  -> FStar_Tests_Pars.init () 
let (guard_to_string :
  FStar_TypeChecker_Common.guard_formula -> Prims.string) =
  fun g  ->
    match g with
    | FStar_TypeChecker_Common.Trivial  -> "trivial"
    | FStar_TypeChecker_Common.NonTrivial f ->
        let uu____8 = tcenv ()  in
        FStar_TypeChecker_Normalize.term_to_string uu____8 f
  
let (guard_eq :
  Prims.int ->
    FStar_TypeChecker_Common.guard_formula ->
      FStar_TypeChecker_Common.guard_formula -> Prims.unit)
  =
  fun i  ->
    fun g  ->
      fun g'  ->
        let uu____18 =
          match (g, g') with
          | (FStar_TypeChecker_Common.Trivial
             ,FStar_TypeChecker_Common.Trivial ) -> (true, g, g')
          | (FStar_TypeChecker_Common.NonTrivial
             f,FStar_TypeChecker_Common.NonTrivial f') ->
              let f1 =
                let uu____34 = tcenv ()  in
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Normalize.EraseUniverses] uu____34 f
                 in
              let f'1 =
                let uu____36 = tcenv ()  in
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Normalize.EraseUniverses] uu____36 f'
                 in
              let uu____37 = FStar_Tests_Util.term_eq f1 f'1  in
              (uu____37, (FStar_TypeChecker_Common.NonTrivial f1),
                (FStar_TypeChecker_Common.NonTrivial f'1))
          | uu____38 -> (false, g, g')  in
        match uu____18 with
        | (b,g1,g'1) ->
            if Prims.op_Negation b
            then
              let msg =
                let uu____47 = FStar_Util.string_of_int i  in
                let uu____48 = guard_to_string g'1  in
                let uu____49 = guard_to_string g1  in
                FStar_Util.format3
                  "Test %s failed:\n\tExpected guard %s;\n\tGot guard      %s\n"
                  uu____47 uu____48 uu____49
                 in
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_UnexpectedGuard, msg)
                FStar_Range.dummyRange
            else ()
  
let (unify :
  Prims.int ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term ->
        FStar_TypeChecker_Common.guard_formula ->
          (Prims.unit -> Prims.unit) -> Prims.unit)
  =
  fun i  ->
    fun x1  ->
      fun y1  ->
        fun g'  ->
          fun check  ->
            (let uu____72 = FStar_Util.string_of_int i  in
             FStar_Util.print1 "%s ..." uu____72);
            (let uu____74 = FStar_Main.process_args ()  in
             FStar_All.pipe_right uu____74 FStar_Pervasives.ignore);
            (let uu____94 = FStar_Syntax_Print.term_to_string x1  in
             let uu____95 = FStar_Syntax_Print.term_to_string y1  in
             FStar_Util.print2 "Unify %s\nand %s\n" uu____94 uu____95);
            (let g =
               let uu____97 =
                 let uu____98 = tcenv ()  in
                 FStar_TypeChecker_Rel.teq uu____98 x1 y1  in
               let uu____99 =
                 let uu____102 = tcenv ()  in
                 FStar_TypeChecker_Rel.solve_deferred_constraints uu____102
                  in
               FStar_All.pipe_right uu____97 uu____99  in
             guard_eq i g.FStar_TypeChecker_Env.guard_f g';
             check ();
             FStar_Options.init ())
  
let (should_fail :
  FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.unit) =
  fun x1  ->
    fun y1  ->
      try
        let g =
          let uu____116 =
            let uu____117 = tcenv ()  in
            FStar_TypeChecker_Rel.teq uu____117 x1 y1  in
          let uu____118 =
            let uu____121 = tcenv ()  in
            FStar_TypeChecker_Rel.solve_deferred_constraints uu____121  in
          FStar_All.pipe_right uu____116 uu____118  in
        match g.FStar_TypeChecker_Env.guard_f with
        | FStar_TypeChecker_Common.Trivial  ->
            let uu____122 =
              let uu____123 = FStar_Syntax_Print.term_to_string x1  in
              let uu____124 = FStar_Syntax_Print.term_to_string y1  in
              FStar_Util.format2 "%s and %s should not be unifiable\n"
                uu____123 uu____124
               in
            failwith uu____122
        | FStar_TypeChecker_Common.NonTrivial f ->
            let uu____126 = FStar_Syntax_Print.term_to_string x1  in
            let uu____127 = FStar_Syntax_Print.term_to_string y1  in
            let uu____128 = FStar_Syntax_Print.term_to_string f  in
            FStar_Util.print3 "%s and %s are unifiable if %s\n" uu____126
              uu____127 uu____128
      with | FStar_Errors.Error (e,msg,r) -> FStar_Util.print1 "%s\n" msg
  
let (unify' : Prims.string -> Prims.string -> Prims.unit) =
  fun x1  ->
    fun y1  ->
      let x2 = FStar_Tests_Pars.pars x1  in
      let y2 = FStar_Tests_Pars.pars y1  in
      let g =
        let uu____146 =
          let uu____147 = tcenv ()  in
          FStar_TypeChecker_Rel.teq uu____147 x2 y2  in
        let uu____148 =
          let uu____151 = tcenv ()  in
          FStar_TypeChecker_Rel.solve_deferred_constraints uu____151  in
        FStar_All.pipe_right uu____146 uu____148  in
      let uu____152 = FStar_Syntax_Print.term_to_string x2  in
      let uu____153 = FStar_Syntax_Print.term_to_string y2  in
      let uu____154 = guard_to_string g.FStar_TypeChecker_Env.guard_f  in
      FStar_Util.print3 "%s and %s are unifiable with guard %s\n" uu____152
        uu____153 uu____154
  
let (norm : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____158 = tcenv ()  in
    FStar_TypeChecker_Normalize.normalize [] uu____158 t
  
let (inst :
  Prims.int ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.typ Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun n1  ->
    fun tm1  ->
      let rec aux out n2 =
        if n2 = (Prims.parse_int "0")
        then out
        else
          (let uu____191 =
             FStar_TypeChecker_Rel.new_uvar FStar_Range.dummyRange []
               FStar_Syntax_Util.ktype0
              in
           match uu____191 with
           | (t,uu____203) ->
               let uu____204 =
                 FStar_TypeChecker_Rel.new_uvar FStar_Range.dummyRange [] t
                  in
               (match uu____204 with
                | (u,uu____216) ->
                    aux (u :: out) (n2 - (Prims.parse_int "1"))))
         in
      let us = aux [] n1  in
      let uu____220 =
        let uu____221 = FStar_Tests_Util.app tm1 us  in norm uu____221  in
      (uu____220, us)
  
let (run_all : Prims.unit -> Prims.unit) =
  fun uu____226  ->
    FStar_Util.print_string "Testing the unifier\n";
    FStar_Options.__set_unit_tests ();
    (let unify_check n1 x1 y1 g f = unify n1 x1 y1 g f  in
     let unify1 n1 x1 y1 g = unify n1 x1 y1 g (fun uu____264  -> ())  in
     let int_t = FStar_Tests_Pars.tc "Prims.int"  in
     let x1 =
       let uu____267 =
         FStar_Syntax_Syntax.gen_bv "x" FStar_Pervasives_Native.None int_t
          in
       FStar_All.pipe_right uu____267 FStar_Syntax_Syntax.bv_to_name  in
     let y1 =
       let uu____269 =
         FStar_Syntax_Syntax.gen_bv "y" FStar_Pervasives_Native.None int_t
          in
       FStar_All.pipe_right uu____269 FStar_Syntax_Syntax.bv_to_name  in
     unify1 (Prims.parse_int "0") x1 x1 FStar_TypeChecker_Common.Trivial;
     (let uu____272 =
        let uu____273 =
          FStar_Syntax_Util.mk_eq2 FStar_Syntax_Syntax.U_zero
            FStar_Syntax_Util.t_bool x1 y1
           in
        FStar_TypeChecker_Common.NonTrivial uu____273  in
      unify1 (Prims.parse_int "1") x1 y1 uu____272);
     (let id1 = FStar_Tests_Pars.tc "fun x -> x"  in
      (let uu____276 = FStar_Tests_Util.app id1 [x1]  in
       unify1 (Prims.parse_int "2") x1 uu____276
         FStar_TypeChecker_Common.Trivial);
      (let id2 = FStar_Tests_Pars.tc "fun x -> x"  in
       unify1 (Prims.parse_int "3") id2 id2 FStar_TypeChecker_Common.Trivial;
       (let id3 = FStar_Tests_Pars.tc "fun x -> x"  in
        let id' = FStar_Tests_Pars.tc "fun y -> y"  in
        unify1 (Prims.parse_int "4") id3 id' FStar_TypeChecker_Common.Trivial;
        (let uu____283 = FStar_Tests_Pars.tc "fun x y -> x"  in
         let uu____284 = FStar_Tests_Pars.tc "fun a b -> a"  in
         unify1 (Prims.parse_int "5") uu____283 uu____284
           FStar_TypeChecker_Common.Trivial);
        (let uu____286 = FStar_Tests_Pars.tc "fun x y z -> y"  in
         let uu____287 = FStar_Tests_Pars.tc "fun a b c -> b"  in
         unify1 (Prims.parse_int "6") uu____286 uu____287
           FStar_TypeChecker_Common.Trivial);
        (let uu____289 = FStar_Tests_Pars.tc "fun (x:int) (y:int) -> y"  in
         let uu____290 = FStar_Tests_Pars.tc "fun (x:int) (y:int) -> x"  in
         let uu____291 =
           let uu____292 =
             FStar_Tests_Pars.tc "(forall (x:int). (forall (y:int). y==x))"
              in
           FStar_TypeChecker_Common.NonTrivial uu____292  in
         unify1 (Prims.parse_int "7") uu____289 uu____290 uu____291);
        (let uu____294 =
           FStar_Tests_Pars.tc "fun (x:int) (y:int) (z:int) -> y"  in
         let uu____295 =
           FStar_Tests_Pars.tc "fun (x:int) (y:int) (z:int) -> z"  in
         let uu____296 =
           let uu____297 =
             FStar_Tests_Pars.tc
               "(forall (x:int). (forall (y:int). (forall (z:int). y==z)))"
              in
           FStar_TypeChecker_Common.NonTrivial uu____297  in
         unify1 (Prims.parse_int "8") uu____294 uu____295 uu____296);
        (let uu____299 = FStar_Main.process_args ()  in
         FStar_All.pipe_right uu____299 FStar_Pervasives.ignore);
        (let uu____318 =
           let uu____325 = FStar_Tests_Pars.tc "fun u x -> u x"  in
           inst (Prims.parse_int "1") uu____325  in
         match uu____318 with
         | (tm1,us) ->
             let sol = FStar_Tests_Pars.tc "fun x -> c_and x x"  in
             (unify_check (Prims.parse_int "9") tm1 sol
                FStar_TypeChecker_Common.Trivial
                (fun uu____338  ->
                   let uu____339 =
                     let uu____340 =
                       let uu____341 = FStar_List.hd us  in norm uu____341
                        in
                     let uu____342 = norm sol  in
                     FStar_Tests_Util.term_eq uu____340 uu____342  in
                   FStar_Tests_Util.always (Prims.parse_int "9") uu____339);
              (let uu____343 =
                 let uu____350 = FStar_Tests_Pars.tc "fun u x -> u x"  in
                 inst (Prims.parse_int "1") uu____350  in
               match uu____343 with
               | (tm2,us1) ->
                   let sol1 = FStar_Tests_Pars.tc "fun x y -> x + y"  in
                   (unify_check (Prims.parse_int "10") tm2 sol1
                      FStar_TypeChecker_Common.Trivial
                      (fun uu____363  ->
                         let uu____364 =
                           let uu____365 =
                             let uu____366 = FStar_List.hd us1  in
                             norm uu____366  in
                           let uu____367 = norm sol1  in
                           FStar_Tests_Util.term_eq uu____365 uu____367  in
                         FStar_Tests_Util.always (Prims.parse_int "10")
                           uu____364);
                    (let tm11 =
                       FStar_Tests_Pars.tc "x:int -> y:int{eq2 y x} -> bool"
                        in
                     let tm21 = FStar_Tests_Pars.tc "x:int -> y:int -> bool"
                        in
                     (let uu____371 =
                        let uu____372 =
                          FStar_Tests_Pars.tc
                            "forall (x:int). (forall (y:int). y==x)"
                           in
                        FStar_TypeChecker_Common.NonTrivial uu____372  in
                      unify1 (Prims.parse_int "11") tm11 tm21 uu____371);
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
                      (let uu____376 =
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
                           let uu____389 =
                             let uu____390 =
                               let uu____393 =
                                 FStar_Syntax_Syntax.bv_to_name q  in
                               [uu____393]  in
                             FStar_Tests_Util.app l uu____390  in
                           norm uu____389  in
                         let l1 =
                           FStar_Tests_Pars.tc "fun (p:unit -> Type0) -> p"
                            in
                         let unit = FStar_Tests_Pars.tc "()"  in
                         let uu____396 =
                           let uu____401 =
                             let uu____402 = FStar_Syntax_Syntax.mk_binder x2
                                in
                             let uu____403 =
                               let uu____406 =
                                 FStar_Syntax_Syntax.mk_binder q  in
                               [uu____406]  in
                             uu____402 :: uu____403  in
                           FStar_TypeChecker_Rel.new_uvar
                             FStar_Range.dummyRange uu____401 typ
                            in
                         match uu____396 with
                         | (u_p,uu____414) ->
                             let tm23 =
                               let uu____418 =
                                 let uu____421 =
                                   FStar_Tests_Util.app l1 [u_p]  in
                                 norm uu____421  in
                               FStar_Tests_Util.app uu____418 [unit]  in
                             (tm13, tm23)
                          in
                       match uu____376 with
                       | (tm13,tm23) ->
                           ((let uu____431 =
                               let uu____432 =
                                 FStar_Tests_Pars.tc "Prims.l_True"  in
                               FStar_TypeChecker_Common.NonTrivial uu____432
                                in
                             unify1 (Prims.parse_int "13") tm13 tm23
                               uu____431);
                            (let uu____433 =
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
                                 let uu____446 =
                                   let uu____447 =
                                     let uu____450 =
                                       FStar_Syntax_Syntax.bv_to_name q  in
                                     [uu____450]  in
                                   FStar_Tests_Util.app l uu____447  in
                                 norm uu____446  in
                               let l1 =
                                 FStar_Tests_Pars.tc
                                   "fun (p:pure_post unit) -> p"
                                  in
                               let unit = FStar_Tests_Pars.tc "()"  in
                               let uu____453 =
                                 let uu____458 =
                                   let uu____459 =
                                     FStar_Syntax_Syntax.mk_binder x2  in
                                   let uu____460 =
                                     let uu____463 =
                                       FStar_Syntax_Syntax.mk_binder q  in
                                     [uu____463]  in
                                   uu____459 :: uu____460  in
                                 FStar_TypeChecker_Rel.new_uvar
                                   FStar_Range.dummyRange uu____458 typ
                                  in
                               match uu____453 with
                               | (u_p,uu____471) ->
                                   let tm24 =
                                     let uu____475 =
                                       let uu____478 =
                                         FStar_Tests_Util.app l1 [u_p]  in
                                       norm uu____478  in
                                     FStar_Tests_Util.app uu____475 [unit]
                                      in
                                   (tm14, tm24)
                                in
                             match uu____433 with
                             | (tm14,tm24) ->
                                 ((let uu____488 =
                                     let uu____489 =
                                       FStar_Tests_Pars.tc "Prims.l_True"  in
                                     FStar_TypeChecker_Common.NonTrivial
                                       uu____489
                                      in
                                   unify1 (Prims.parse_int "14") tm14 tm24
                                     uu____488);
                                  FStar_Options.__clear_unit_tests ();
                                  FStar_Util.print_string "Unifier ok\n"))))))))))))))
  