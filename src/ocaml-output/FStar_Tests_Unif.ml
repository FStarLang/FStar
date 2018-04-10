open Prims
let (tcenv : unit -> FStar_TypeChecker_Env.env) =
  fun uu____5  -> FStar_Tests_Pars.init () 
let (guard_to_string :
  FStar_TypeChecker_Common.guard_formula -> Prims.string) =
  fun g  ->
    match g with
    | FStar_TypeChecker_Common.Trivial  -> "trivial"
    | FStar_TypeChecker_Common.NonTrivial f ->
        let uu____12 = tcenv ()  in
        FStar_TypeChecker_Normalize.term_to_string uu____12 f
  
let (guard_eq :
  Prims.int ->
    FStar_TypeChecker_Common.guard_formula ->
      FStar_TypeChecker_Common.guard_formula -> unit)
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
  
let (unify :
  Prims.int ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term ->
        FStar_TypeChecker_Common.guard_formula -> (unit -> unit) -> unit)
  =
  fun i  ->
    fun x1  ->
      fun y1  ->
        fun g'  ->
          fun check1  ->
            let uu____91 =
              let uu____92 = FStar_Util.string_of_int i  in
              FStar_Util.print1 "%s ..." uu____92  in
            let uu____93 =
              let uu____94 = FStar_Main.process_args ()  in
              FStar_All.pipe_right uu____94
                (fun a253  -> (Obj.magic ()) a253)
               in
            let uu____107 =
              let uu____108 = FStar_Syntax_Print.term_to_string x1  in
              let uu____109 = FStar_Syntax_Print.term_to_string y1  in
              FStar_Util.print2 "Unify %s\nand %s\n" uu____108 uu____109  in
            let g =
              let uu____111 =
                let uu____112 = tcenv ()  in
                FStar_TypeChecker_Rel.teq uu____112 x1 y1  in
              let uu____113 =
                let uu____117 = tcenv ()  in
                FStar_TypeChecker_Rel.solve_deferred_constraints uu____117
                 in
              FStar_All.pipe_right uu____111 uu____113  in
            let uu____118 = guard_eq i g.FStar_TypeChecker_Env.guard_f g'  in
            let uu____119 = check1 ()  in FStar_Options.init ()
  
let (should_fail :
  FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit) =
  fun x1  ->
    fun y1  ->
      try
        let g =
          let uu____135 =
            let uu____136 = tcenv ()  in
            FStar_TypeChecker_Rel.teq uu____136 x1 y1  in
          let uu____137 =
            let uu____141 = tcenv ()  in
            FStar_TypeChecker_Rel.solve_deferred_constraints uu____141  in
          FStar_All.pipe_right uu____135 uu____137  in
        match g.FStar_TypeChecker_Env.guard_f with
        | FStar_TypeChecker_Common.Trivial  ->
            let uu____142 =
              let uu____143 = FStar_Syntax_Print.term_to_string x1  in
              let uu____144 = FStar_Syntax_Print.term_to_string y1  in
              FStar_Util.format2 "%s and %s should not be unifiable\n"
                uu____143 uu____144
               in
            failwith uu____142
        | FStar_TypeChecker_Common.NonTrivial f ->
            let uu____146 = FStar_Syntax_Print.term_to_string x1  in
            let uu____147 = FStar_Syntax_Print.term_to_string y1  in
            let uu____148 = FStar_Syntax_Print.term_to_string f  in
            FStar_Util.print3 "%s and %s are unifiable if %s\n" uu____146
              uu____147 uu____148
      with | FStar_Errors.Error (e,msg,r) -> FStar_Util.print1 "%s\n" msg
  
let (unify' : Prims.string -> Prims.string -> unit) =
  fun x1  ->
    fun y1  ->
      let x2 = FStar_Tests_Pars.pars x1  in
      let y2 = FStar_Tests_Pars.pars y1  in
      let g =
        let uu____170 =
          let uu____171 = tcenv ()  in
          FStar_TypeChecker_Rel.teq uu____171 x2 y2  in
        let uu____172 =
          let uu____176 = tcenv ()  in
          FStar_TypeChecker_Rel.solve_deferred_constraints uu____176  in
        FStar_All.pipe_right uu____170 uu____172  in
      let uu____177 = FStar_Syntax_Print.term_to_string x2  in
      let uu____178 = FStar_Syntax_Print.term_to_string y2  in
      let uu____179 = guard_to_string g.FStar_TypeChecker_Env.guard_f  in
      FStar_Util.print3 "%s and %s are unifiable with guard %s\n" uu____177
        uu____178 uu____179
  
let (norm : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____185 = tcenv ()  in
    FStar_TypeChecker_Normalize.normalize [] uu____185 t
  
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
          (let uu____224 =
             FStar_TypeChecker_Rel.new_uvar FStar_Range.dummyRange []
               FStar_Syntax_Util.ktype0
              in
           match uu____224 with
           | (t,uu____236) ->
               let uu____237 =
                 FStar_TypeChecker_Rel.new_uvar FStar_Range.dummyRange [] t
                  in
               (match uu____237 with
                | (u,uu____249) ->
                    aux (u :: out) (n2 - (Prims.parse_int "1"))))
         in
      let us = aux [] n1  in
      let uu____253 =
        let uu____254 = FStar_Tests_Util.app tm1 us  in norm uu____254  in
      (uu____253, us)
  
let (run_all : unit -> unit) =
  fun uu____261  ->
    let uu____262 = FStar_Util.print_string "Testing the unifier\n"  in
    let uu____263 = FStar_Options.__set_unit_tests ()  in
    let unify_check n1 x1 y1 g f = unify n1 x1 y1 g f  in
    let unify1 n1 x1 y1 g = unify n1 x1 y1 g (fun uu____308  -> ())  in
    let int_t = FStar_Tests_Pars.tc "Prims.int"  in
    let x1 =
      let uu____311 =
        FStar_Syntax_Syntax.gen_bv "x" FStar_Pervasives_Native.None int_t  in
      FStar_All.pipe_right uu____311 FStar_Syntax_Syntax.bv_to_name  in
    let y1 =
      let uu____313 =
        FStar_Syntax_Syntax.gen_bv "y" FStar_Pervasives_Native.None int_t  in
      FStar_All.pipe_right uu____313 FStar_Syntax_Syntax.bv_to_name  in
    let uu____314 =
      unify1 (Prims.parse_int "0") x1 x1 FStar_TypeChecker_Common.Trivial  in
    let uu____315 =
      let uu____316 =
        let uu____317 =
          FStar_Syntax_Util.mk_eq2 FStar_Syntax_Syntax.U_zero
            FStar_Syntax_Util.t_bool x1 y1
           in
        FStar_TypeChecker_Common.NonTrivial uu____317  in
      unify1 (Prims.parse_int "1") x1 y1 uu____316  in
    let id1 = FStar_Tests_Pars.tc "fun x -> x"  in
    let uu____319 =
      let uu____320 = FStar_Tests_Util.app id1 [x1]  in
      unify1 (Prims.parse_int "2") x1 uu____320
        FStar_TypeChecker_Common.Trivial
       in
    let id2 = FStar_Tests_Pars.tc "fun x -> x"  in
    let uu____322 =
      unify1 (Prims.parse_int "3") id2 id2 FStar_TypeChecker_Common.Trivial
       in
    let id3 = FStar_Tests_Pars.tc "fun x -> x"  in
    let id' = FStar_Tests_Pars.tc "fun y -> y"  in
    let uu____325 =
      unify1 (Prims.parse_int "4") id3 id' FStar_TypeChecker_Common.Trivial
       in
    let uu____326 =
      let uu____327 = FStar_Tests_Pars.tc "fun x y -> x"  in
      let uu____328 = FStar_Tests_Pars.tc "fun a b -> a"  in
      unify1 (Prims.parse_int "5") uu____327 uu____328
        FStar_TypeChecker_Common.Trivial
       in
    let uu____329 =
      let uu____330 = FStar_Tests_Pars.tc "fun x y z -> y"  in
      let uu____331 = FStar_Tests_Pars.tc "fun a b c -> b"  in
      unify1 (Prims.parse_int "6") uu____330 uu____331
        FStar_TypeChecker_Common.Trivial
       in
    let uu____332 =
      let uu____333 = FStar_Tests_Pars.tc "fun (x:int) (y:int) -> y"  in
      let uu____334 = FStar_Tests_Pars.tc "fun (x:int) (y:int) -> x"  in
      let uu____335 =
        let uu____336 =
          FStar_Tests_Pars.tc "(forall (x:int). (forall (y:int). y==x))"  in
        FStar_TypeChecker_Common.NonTrivial uu____336  in
      unify1 (Prims.parse_int "7") uu____333 uu____334 uu____335  in
    let uu____337 =
      let uu____338 = FStar_Tests_Pars.tc "fun (x:int) (y:int) (z:int) -> y"
         in
      let uu____339 = FStar_Tests_Pars.tc "fun (x:int) (y:int) (z:int) -> z"
         in
      let uu____340 =
        let uu____341 =
          FStar_Tests_Pars.tc
            "(forall (x:int). (forall (y:int). (forall (z:int). y==z)))"
           in
        FStar_TypeChecker_Common.NonTrivial uu____341  in
      unify1 (Prims.parse_int "8") uu____338 uu____339 uu____340  in
    let uu____342 =
      let uu____343 = FStar_Main.process_args ()  in
      FStar_All.pipe_right uu____343 (fun a254  -> (Obj.magic ()) a254)  in
    let uu____356 =
      let uu____363 = FStar_Tests_Pars.tc "fun u x -> u x"  in
      inst (Prims.parse_int "1") uu____363  in
    match uu____356 with
    | (tm1,us) ->
        let sol = FStar_Tests_Pars.tc "fun x -> c_and x x"  in
        let uu____373 =
          unify_check (Prims.parse_int "9") tm1 sol
            FStar_TypeChecker_Common.Trivial
            (fun uu____376  ->
               let uu____377 =
                 let uu____378 =
                   let uu____379 = FStar_List.hd us  in norm uu____379  in
                 let uu____380 = norm sol  in
                 FStar_Tests_Util.term_eq uu____378 uu____380  in
               FStar_Tests_Util.always (Prims.parse_int "9") uu____377)
           in
        let uu____381 =
          let uu____388 = FStar_Tests_Pars.tc "fun u x -> u x"  in
          inst (Prims.parse_int "1") uu____388  in
        (match uu____381 with
         | (tm2,us1) ->
             let sol1 = FStar_Tests_Pars.tc "fun x y -> x + y"  in
             let uu____398 =
               unify_check (Prims.parse_int "10") tm2 sol1
                 FStar_TypeChecker_Common.Trivial
                 (fun uu____401  ->
                    let uu____402 =
                      let uu____403 =
                        let uu____404 = FStar_List.hd us1  in norm uu____404
                         in
                      let uu____405 = norm sol1  in
                      FStar_Tests_Util.term_eq uu____403 uu____405  in
                    FStar_Tests_Util.always (Prims.parse_int "10") uu____402)
                in
             let tm11 = FStar_Tests_Pars.tc "x:int -> y:int{eq2 y x} -> bool"
                in
             let tm21 = FStar_Tests_Pars.tc "x:int -> y:int -> bool"  in
             let uu____408 =
               let uu____409 =
                 let uu____410 =
                   FStar_Tests_Pars.tc
                     "forall (x:int). (forall (y:int). y==x)"
                    in
                 FStar_TypeChecker_Common.NonTrivial uu____410  in
               unify1 (Prims.parse_int "11") tm11 tm21 uu____409  in
             let tm12 =
               FStar_Tests_Pars.tc
                 "a:Type0 -> b:(a -> Type0) -> x:a -> y:b x -> Tot Type0"
                in
             let tm22 =
               FStar_Tests_Pars.tc
                 "a:Type0 -> b:(a -> Type0) -> x:a -> y:b x -> Tot Type0"
                in
             let uu____413 =
               unify1 (Prims.parse_int "12") tm12 tm22
                 FStar_TypeChecker_Common.Trivial
                in
             let uu____414 =
               let int_typ = FStar_Tests_Pars.tc "int"  in
               let x2 =
                 FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                   int_typ
                  in
               let typ = FStar_Tests_Pars.tc "unit -> Type0"  in
               let l = FStar_Tests_Pars.tc "fun (q:(unit -> Type0)) -> q ()"
                  in
               let q =
                 FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None typ
                  in
               let tm13 =
                 let uu____427 =
                   let uu____428 =
                     let uu____431 = FStar_Syntax_Syntax.bv_to_name q  in
                     [uu____431]  in
                   FStar_Tests_Util.app l uu____428  in
                 norm uu____427  in
               let l1 = FStar_Tests_Pars.tc "fun (p:unit -> Type0) -> p"  in
               let unit = FStar_Tests_Pars.tc "()"  in
               let uu____434 =
                 let uu____439 =
                   let uu____440 = FStar_Syntax_Syntax.mk_binder x2  in
                   let uu____441 =
                     let uu____444 = FStar_Syntax_Syntax.mk_binder q  in
                     [uu____444]  in
                   uu____440 :: uu____441  in
                 FStar_TypeChecker_Rel.new_uvar FStar_Range.dummyRange
                   uu____439 typ
                  in
               match uu____434 with
               | (u_p,uu____452) ->
                   let tm23 =
                     let uu____456 =
                       let uu____459 = FStar_Tests_Util.app l1 [u_p]  in
                       norm uu____459  in
                     FStar_Tests_Util.app uu____456 [unit]  in
                   (tm13, tm23)
                in
             (match uu____414 with
              | (tm13,tm23) ->
                  let uu____468 =
                    let uu____469 =
                      let uu____470 = FStar_Tests_Pars.tc "Prims.l_True"  in
                      FStar_TypeChecker_Common.NonTrivial uu____470  in
                    unify1 (Prims.parse_int "13") tm13 tm23 uu____469  in
                  let uu____471 =
                    let int_typ = FStar_Tests_Pars.tc "int"  in
                    let x2 =
                      FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                        int_typ
                       in
                    let typ = FStar_Tests_Pars.tc "pure_post unit"  in
                    let l =
                      FStar_Tests_Pars.tc "fun (q:pure_post unit) -> q ()"
                       in
                    let q =
                      FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                        typ
                       in
                    let tm14 =
                      let uu____484 =
                        let uu____485 =
                          let uu____488 = FStar_Syntax_Syntax.bv_to_name q
                             in
                          [uu____488]  in
                        FStar_Tests_Util.app l uu____485  in
                      norm uu____484  in
                    let l1 =
                      FStar_Tests_Pars.tc "fun (p:pure_post unit) -> p"  in
                    let unit = FStar_Tests_Pars.tc "()"  in
                    let uu____491 =
                      let uu____496 =
                        let uu____497 = FStar_Syntax_Syntax.mk_binder x2  in
                        let uu____498 =
                          let uu____501 = FStar_Syntax_Syntax.mk_binder q  in
                          [uu____501]  in
                        uu____497 :: uu____498  in
                      FStar_TypeChecker_Rel.new_uvar FStar_Range.dummyRange
                        uu____496 typ
                       in
                    match uu____491 with
                    | (u_p,uu____509) ->
                        let tm24 =
                          let uu____513 =
                            let uu____516 = FStar_Tests_Util.app l1 [u_p]  in
                            norm uu____516  in
                          FStar_Tests_Util.app uu____513 [unit]  in
                        (tm14, tm24)
                     in
                  (match uu____471 with
                   | (tm14,tm24) ->
                       let uu____525 =
                         let uu____526 =
                           let uu____527 = FStar_Tests_Pars.tc "Prims.l_True"
                              in
                           FStar_TypeChecker_Common.NonTrivial uu____527  in
                         unify1 (Prims.parse_int "14") tm14 tm24 uu____526
                          in
                       let uu____528 = FStar_Options.__clear_unit_tests ()
                          in
                       FStar_Util.print_string "Unifier ok\n")))
  