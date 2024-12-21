open Prims
type 'a id =
  | I of 'a 
let uu___is_I : 'a . 'a id -> Prims.bool = fun projectee -> true
let __proj__I__item__run : 'a . 'a id -> 'a =
  fun projectee -> match projectee with | I run -> run
let (uu___0 : unit id FStarC_Class_Monad.monad) =
  {
    FStarC_Class_Monad.return =
      (fun uu___1 ->
         fun uu___ -> (fun a -> fun a1 -> Obj.magic (I a1)) uu___1 uu___);
    FStarC_Class_Monad.op_let_Bang =
      (fun uu___3 ->
         fun uu___2 ->
           fun uu___1 ->
             fun uu___ ->
               (fun a ->
                  fun b ->
                    fun uu___ ->
                      let uu___ = Obj.magic uu___ in
                      fun f ->
                        let f = Obj.magic f in
                        match uu___ with | I a1 -> Obj.magic (f a1)) uu___3
                 uu___2 uu___1 uu___)
  }
let op_Less_Less :
  'uuuuu 'uuuuu1 'uuuuu2 .
    ('uuuuu -> 'uuuuu1) -> ('uuuuu2 -> 'uuuuu) -> 'uuuuu2 -> 'uuuuu1
  = fun f -> fun g -> fun x -> let uu___ = g x in f uu___
let (visit_term :
  Prims.bool ->
    (FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term) ->
      FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term)
  =
  fun pq ->
    fun vt ->
      fun t ->
        let uu___ =
          Obj.magic
            (FStarC_Syntax_VisitM.visitM_term uu___0 pq
               (fun uu___1 ->
                  (Obj.magic (op_Less_Less (fun uu___1 -> I uu___1) vt))
                    uu___1) t) in
        __proj__I__item__run uu___
let (visit_term_univs :
  Prims.bool ->
    (FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term) ->
      (FStarC_Syntax_Syntax.universe -> FStarC_Syntax_Syntax.universe) ->
        FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term)
  =
  fun pq ->
    fun vt ->
      fun vu ->
        fun t ->
          let uu___ =
            Obj.magic
              (FStarC_Syntax_VisitM.visitM_term_univs uu___0 pq
                 (fun uu___1 ->
                    (Obj.magic (op_Less_Less (fun uu___1 -> I uu___1) vt))
                      uu___1)
                 (fun uu___1 ->
                    (Obj.magic (op_Less_Less (fun uu___1 -> I uu___1) vu))
                      uu___1) t) in
          __proj__I__item__run uu___
let (visit_sigelt :
  Prims.bool ->
    (FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term) ->
      (FStarC_Syntax_Syntax.universe -> FStarC_Syntax_Syntax.universe) ->
        FStarC_Syntax_Syntax.sigelt -> FStarC_Syntax_Syntax.sigelt)
  =
  fun pq ->
    fun vt ->
      fun vu ->
        fun se ->
          let uu___ =
            Obj.magic
              (FStarC_Syntax_VisitM.visitM_sigelt uu___0 pq
                 (fun uu___1 ->
                    (Obj.magic (op_Less_Less (fun uu___1 -> I uu___1) vt))
                      uu___1)
                 (fun uu___1 ->
                    (Obj.magic (op_Less_Less (fun uu___1 -> I uu___1) vu))
                      uu___1) se) in
          __proj__I__item__run uu___