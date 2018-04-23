open Prims
let tcenv : unit -> FStar_TypeChecker_Env.env =
  fun uu____5  -> FStar_Tests_Pars.init () 
let guard_to_string : FStar_TypeChecker_Common.guard_formula -> Prims.string
  =
  fun g  ->
    match g with
    | FStar_TypeChecker_Common.Trivial  -> "trivial"
    | FStar_TypeChecker_Common.NonTrivial f ->
        let uu____12 = tcenv ()  in
        FStar_TypeChecker_Normalize.term_to_string uu____12 f
  
let guard_eq :
  Prims.int ->
    FStar_TypeChecker_Common.guard_formula ->
      FStar_TypeChecker_Common.guard_formula -> unit
  =
  fun i  ->
    fun g  ->
      fun g'  ->
        let uu____28 =
          match (g, g') with
          | (FStar_TypeChecker_Common.Trivial
             ,FStar_TypeChecker_Common.Trivial ) -> (true, g, g')
          | (FStar_TypeChecker_Common.NonTrivial
             f,FStar_TypeChecker_Common.NonTrivial f') ->
              let f1 =
                let uu____44 = tcenv ()  in
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Normalize.EraseUniverses] uu____44 f
                 in
              let f'1 =
                let uu____46 = tcenv ()  in
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Normalize.EraseUniverses] uu____46 f'
                 in
              let uu____47 = FStar_Tests_Util.term_eq f1 f'1  in
              (uu____47, (FStar_TypeChecker_Common.NonTrivial f1),
                (FStar_TypeChecker_Common.NonTrivial f'1))
          | uu____48 -> (false, g, g')  in
        match uu____28 with
        | (b,g1,g'1) ->
            if Prims.op_Negation b
            then
              let msg =
                let uu____57 = FStar_Util.string_of_int i  in
                let uu____58 = guard_to_string g'1  in
                let uu____59 = guard_to_string g1  in
                FStar_Util.format3
                  "Test %s failed:\n\tExpected guard %s;\n\tGot guard      %s\n"
                  uu____57 uu____58 uu____59
                 in
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_UnexpectedGuard, msg)
                FStar_Range.dummyRange
            else ()
  
let unify :
  Prims.int ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term ->
        FStar_TypeChecker_Common.guard_formula -> (unit -> unit) -> unit
  =
  fun i  ->
    fun x1  ->
      fun y1  ->
        fun g'  ->
          fun check1  ->
            (let uu____92 = FStar_Util.string_of_int i  in
             FStar_Util.print1 "%s ..." uu____92);
            (let uu____94 = FStar_Main.process_args ()  in
             FStar_All.pipe_right uu____94 (fun a246  -> ()));
            (let uu____108 = FStar_Syntax_Print.term_to_string x1  in
             let uu____109 = FStar_Syntax_Print.term_to_string y1  in
             FStar_Util.print2 "Unify %s\nand %s\n" uu____108 uu____109);
            (let g =
               let uu____111 =
                 let uu____112 = tcenv ()  in
                 FStar_TypeChecker_Rel.teq uu____112 x1 y1  in
               let uu____113 =
                 let uu____118 = tcenv ()  in
                 FStar_TypeChecker_Rel.solve_deferred_constraints uu____118
                  in
               FStar_All.pipe_right uu____111 uu____113  in
             guard_eq i g.FStar_TypeChecker_Env.guard_f g';
             check1 ();
             FStar_Options.init ())
  
let should_fail : FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit
  =
  fun x1  ->
    fun y1  ->
      try
        let g =
          let uu____136 =
            let uu____137 = tcenv ()  in
            FStar_TypeChecker_Rel.teq uu____137 x1 y1  in
          let uu____138 =
            let uu____143 = tcenv ()  in
            FStar_TypeChecker_Rel.solve_deferred_constraints uu____143  in
          FStar_All.pipe_right uu____136 uu____138  in
        match g.FStar_TypeChecker_Env.guard_f with
        | FStar_TypeChecker_Common.Trivial  ->
            let uu____144 =
              let uu____145 = FStar_Syntax_Print.term_to_string x1  in
              let uu____146 = FStar_Syntax_Print.term_to_string y1  in
              FStar_Util.format2 "%s and %s should not be unifiable\n"
                uu____145 uu____146
               in
            failwith uu____144
        | FStar_TypeChecker_Common.NonTrivial f ->
            let uu____148 = FStar_Syntax_Print.term_to_string x1  in
            let uu____149 = FStar_Syntax_Print.term_to_string y1  in
            let uu____150 = FStar_Syntax_Print.term_to_string f  in
            FStar_Util.print3 "%s and %s are unifiable if %s\n" uu____148
              uu____149 uu____150
      with | FStar_Errors.Error (e,msg,r) -> FStar_Util.print1 "%s\n" msg
  
let unify' : Prims.string -> Prims.string -> unit =
  fun x1  ->
    fun y1  ->
      let x2 = FStar_Tests_Pars.pars x1  in
      let y2 = FStar_Tests_Pars.pars y1  in
      let g =
        let uu____172 =
          let uu____173 = tcenv ()  in
          FStar_TypeChecker_Rel.teq uu____173 x2 y2  in
        let uu____174 =
          let uu____179 = tcenv ()  in
          FStar_TypeChecker_Rel.solve_deferred_constraints uu____179  in
        FStar_All.pipe_right uu____172 uu____174  in
      let uu____180 = FStar_Syntax_Print.term_to_string x2  in
      let uu____181 = FStar_Syntax_Print.term_to_string y2  in
      let uu____182 = guard_to_string g.FStar_TypeChecker_Env.guard_f  in
      FStar_Util.print3 "%s and %s are unifiable with guard %s\n" uu____180
        uu____181 uu____182
  
let norm : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let uu____188 = tcenv ()  in
    FStar_TypeChecker_Normalize.normalize [] uu____188 t
  
let inst :
  Prims.int ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.typ Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun n1  ->
    fun tm1  ->
      let rec aux out n2 =
        if n2 = (Prims.lift_native_int (0))
        then out
        else
          (let uu____229 =
             FStar_TypeChecker_Rel.new_uvar FStar_Range.dummyRange []
               FStar_Syntax_Util.ktype0
              in
           match uu____229 with
           | (t,uu____241) ->
               let uu____242 =
                 FStar_TypeChecker_Rel.new_uvar FStar_Range.dummyRange [] t
                  in
               (match uu____242 with
                | (u,uu____254) ->
                    aux (u :: out) (n2 - (Prims.lift_native_int (1)))))
         in
      let us = aux [] n1  in
      let uu____258 =
        let uu____259 = FStar_Tests_Util.app tm1 us  in norm uu____259  in
      (uu____258, us)
  
let run_all : unit -> unit =
  fun uu____266  ->
    FStar_Util.print_string "Testing the unifier\n";
    FStar_Options.__set_unit_tests ();
    (let unify_check n1 x1 y1 g f = unify n1 x1 y1 g f  in
     let unify1 n1 x1 y1 g = unify n1 x1 y1 g (fun uu____322  -> ())  in
     let int_t = FStar_Tests_Pars.tc "Prims.int"  in
     let x1 =
       let uu____325 =
         FStar_Syntax_Syntax.gen_bv "x" FStar_Pervasives_Native.None int_t
          in
       FStar_All.pipe_right uu____325 FStar_Syntax_Syntax.bv_to_name  in
     let y1 =
       let uu____327 =
         FStar_Syntax_Syntax.gen_bv "y" FStar_Pervasives_Native.None int_t
          in
       FStar_All.pipe_right uu____327 FStar_Syntax_Syntax.bv_to_name  in
     unify1 (Prims.lift_native_int (0)) x1 x1
       FStar_TypeChecker_Common.Trivial;
     (let uu____330 =
        let uu____331 =
          FStar_Syntax_Util.mk_eq2 FStar_Syntax_Syntax.U_zero
            FStar_Syntax_Util.t_bool x1 y1
           in
        FStar_TypeChecker_Common.NonTrivial uu____331  in
      unify1 (Prims.lift_native_int (1)) x1 y1 uu____330);
     (let id1 = FStar_Tests_Pars.tc "fun x -> x"  in
      (let uu____334 = FStar_Tests_Util.app id1 [x1]  in
       unify1 (Prims.lift_native_int (2)) x1 uu____334
         FStar_TypeChecker_Common.Trivial);
      (let id2 = FStar_Tests_Pars.tc "fun x -> x"  in
       unify1 (Prims.lift_native_int (3)) id2 id2
         FStar_TypeChecker_Common.Trivial;
       (let id3 = FStar_Tests_Pars.tc "fun x -> x"  in
        let id' = FStar_Tests_Pars.tc "fun y -> y"  in
        unify1 (Prims.lift_native_int (4)) id3 id'
          FStar_TypeChecker_Common.Trivial;
        (let uu____341 = FStar_Tests_Pars.tc "fun x y -> x"  in
         let uu____342 = FStar_Tests_Pars.tc "fun a b -> a"  in
         unify1 (Prims.lift_native_int (5)) uu____341 uu____342
           FStar_TypeChecker_Common.Trivial);
        (let uu____344 = FStar_Tests_Pars.tc "fun x y z -> y"  in
         let uu____345 = FStar_Tests_Pars.tc "fun a b c -> b"  in
         unify1 (Prims.lift_native_int (6)) uu____344 uu____345
           FStar_TypeChecker_Common.Trivial);
        (let uu____347 = FStar_Tests_Pars.tc "fun (x:int) (y:int) -> y"  in
         let uu____348 = FStar_Tests_Pars.tc "fun (x:int) (y:int) -> x"  in
         let uu____349 =
           let uu____350 =
             FStar_Tests_Pars.tc "(forall (x:int). (forall (y:int). y==x))"
              in
           FStar_TypeChecker_Common.NonTrivial uu____350  in
         unify1 (Prims.lift_native_int (7)) uu____347 uu____348 uu____349);
        (let uu____352 =
           FStar_Tests_Pars.tc "fun (x:int) (y:int) (z:int) -> y"  in
         let uu____353 =
           FStar_Tests_Pars.tc "fun (x:int) (y:int) (z:int) -> z"  in
         let uu____354 =
           let uu____355 =
             FStar_Tests_Pars.tc
               "(forall (x:int). (forall (y:int). (forall (z:int). y==z)))"
              in
           FStar_TypeChecker_Common.NonTrivial uu____355  in
         unify1 (Prims.lift_native_int (8)) uu____352 uu____353 uu____354);
        (let uu____357 = FStar_Main.process_args ()  in
         FStar_All.pipe_right uu____357 (fun a247  -> ()));
        (let uu____370 =
           let uu____377 = FStar_Tests_Pars.tc "fun u x -> u x"  in
           inst (Prims.lift_native_int (1)) uu____377  in
         match uu____370 with
         | (tm1,us) ->
             let sol = FStar_Tests_Pars.tc "fun x -> c_and x x"  in
             (unify_check (Prims.lift_native_int (9)) tm1 sol
                FStar_TypeChecker_Common.Trivial
                (fun uu____390  ->
                   let uu____391 =
                     let uu____392 =
                       let uu____393 = FStar_List.hd us  in norm uu____393
                        in
                     let uu____394 = norm sol  in
                     FStar_Tests_Util.term_eq uu____392 uu____394  in
                   FStar_Tests_Util.always (Prims.lift_native_int (9))
                     uu____391);
              (let uu____395 =
                 let uu____402 = FStar_Tests_Pars.tc "fun u x -> u x"  in
                 inst (Prims.lift_native_int (1)) uu____402  in
               match uu____395 with
               | (tm2,us1) ->
                   let sol1 = FStar_Tests_Pars.tc "fun x y -> x + y"  in
                   (unify_check (Prims.lift_native_int (10)) tm2 sol1
                      FStar_TypeChecker_Common.Trivial
                      (fun uu____415  ->
                         let uu____416 =
                           let uu____417 =
                             let uu____418 = FStar_List.hd us1  in
                             norm uu____418  in
                           let uu____419 = norm sol1  in
                           FStar_Tests_Util.term_eq uu____417 uu____419  in
                         FStar_Tests_Util.always (Prims.lift_native_int (10))
                           uu____416);
                    (let tm11 =
                       FStar_Tests_Pars.tc "x:int -> y:int{eq2 y x} -> bool"
                        in
                     let tm21 = FStar_Tests_Pars.tc "x:int -> y:int -> bool"
                        in
                     (let uu____423 =
                        let uu____424 =
                          FStar_Tests_Pars.tc
                            "forall (x:int). (forall (y:int). y==x)"
                           in
                        FStar_TypeChecker_Common.NonTrivial uu____424  in
                      unify1 (Prims.lift_native_int (11)) tm11 tm21 uu____423);
                     (let tm12 =
                        FStar_Tests_Pars.tc
                          "a:Type0 -> b:(a -> Type0) -> x:a -> y:b x -> Tot Type0"
                         in
                      let tm22 =
                        FStar_Tests_Pars.tc
                          "a:Type0 -> b:(a -> Type0) -> x:a -> y:b x -> Tot Type0"
                         in
                      unify1 (Prims.lift_native_int (12)) tm12 tm22
                        FStar_TypeChecker_Common.Trivial;
                      (let uu____428 =
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
                           let uu____441 =
                             let uu____442 =
                               let uu____445 =
                                 FStar_Syntax_Syntax.bv_to_name q  in
                               [uu____445]  in
                             FStar_Tests_Util.app l uu____442  in
                           norm uu____441  in
                         let l1 =
                           FStar_Tests_Pars.tc "fun (p:unit -> Type0) -> p"
                            in
                         let unit = FStar_Tests_Pars.tc "()"  in
                         let uu____448 =
                           let uu____453 =
                             let uu____454 = FStar_Syntax_Syntax.mk_binder x2
                                in
                             let uu____455 =
                               let uu____458 =
                                 FStar_Syntax_Syntax.mk_binder q  in
                               [uu____458]  in
                             uu____454 :: uu____455  in
                           FStar_TypeChecker_Rel.new_uvar
                             FStar_Range.dummyRange uu____453 typ
                            in
                         match uu____448 with
                         | (u_p,uu____466) ->
                             let tm23 =
                               let uu____470 =
                                 let uu____473 =
                                   FStar_Tests_Util.app l1 [u_p]  in
                                 norm uu____473  in
                               FStar_Tests_Util.app uu____470 [unit]  in
                             (tm13, tm23)
                          in
                       match uu____428 with
                       | (tm13,tm23) ->
                           ((let uu____483 =
                               let uu____484 =
                                 FStar_Tests_Pars.tc "Prims.l_True"  in
                               FStar_TypeChecker_Common.NonTrivial uu____484
                                in
                             unify1 (Prims.lift_native_int (13)) tm13 tm23
                               uu____483);
                            (let uu____485 =
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
                                 let uu____498 =
                                   let uu____499 =
                                     let uu____502 =
                                       FStar_Syntax_Syntax.bv_to_name q  in
                                     [uu____502]  in
                                   FStar_Tests_Util.app l uu____499  in
                                 norm uu____498  in
                               let l1 =
                                 FStar_Tests_Pars.tc
                                   "fun (p:pure_post unit) -> p"
                                  in
                               let unit = FStar_Tests_Pars.tc "()"  in
                               let uu____505 =
                                 let uu____510 =
                                   let uu____511 =
                                     FStar_Syntax_Syntax.mk_binder x2  in
                                   let uu____512 =
                                     let uu____515 =
                                       FStar_Syntax_Syntax.mk_binder q  in
                                     [uu____515]  in
                                   uu____511 :: uu____512  in
                                 FStar_TypeChecker_Rel.new_uvar
                                   FStar_Range.dummyRange uu____510 typ
                                  in
                               match uu____505 with
                               | (u_p,uu____523) ->
                                   let tm24 =
                                     let uu____527 =
                                       let uu____530 =
                                         FStar_Tests_Util.app l1 [u_p]  in
                                       norm uu____530  in
                                     FStar_Tests_Util.app uu____527 [unit]
                                      in
                                   (tm14, tm24)
                                in
                             match uu____485 with
                             | (tm14,tm24) ->
                                 ((let uu____540 =
                                     let uu____541 =
                                       FStar_Tests_Pars.tc "Prims.l_True"  in
                                     FStar_TypeChecker_Common.NonTrivial
                                       uu____541
                                      in
                                   unify1 (Prims.lift_native_int (14)) tm14
                                     tm24 uu____540);
                                  FStar_Options.__clear_unit_tests ();
                                  FStar_Util.print_string "Unifier ok\n"))))))))))))))
  