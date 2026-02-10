open Prims
type 'a id =
  | I of 'a 
let uu___is_I (projectee : 'a id) : Prims.bool= true
let __proj__I__item__run (projectee : 'a id) : 'a=
  match projectee with | I run -> run
let uu___0 : unit id FStarC_Class_Monad.monad=
  {
    FStarC_Class_Monad.return =
      (fun uu___1 uu___ -> (fun a a1 -> Obj.magic (I a1)) uu___1 uu___);
    FStarC_Class_Monad.bind =
      (fun uu___3 uu___2 uu___1 uu___ ->
         (fun a b uu___ ->
            let uu___ = Obj.magic uu___ in
            fun f ->
              let f = Obj.magic f in
              match uu___ with | I a1 -> Obj.magic (f a1)) uu___3 uu___2
           uu___1 uu___)
  }
let op_Less_Less (f : 'uuuuu -> 'uuuuu1) (g : 'uuuuu2 -> 'uuuuu)
  (x : 'uuuuu2) : 'uuuuu1= let uu___ = g x in f uu___
let visit_term (pq : Prims.bool)
  (vt : FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term)
  (t : FStarC_Syntax_Syntax.term) : FStarC_Syntax_Syntax.term=
  let uu___ =
    Obj.magic
      (FStarC_Syntax_VisitM.visitM_term uu___0 pq
         (fun uu___1 ->
            (Obj.magic (op_Less_Less (fun uu___1 -> I uu___1) vt)) uu___1) t) in
  __proj__I__item__run uu___
let visit_term_univs (pq : Prims.bool)
  (vt : FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term)
  (vu : FStarC_Syntax_Syntax.universe -> FStarC_Syntax_Syntax.universe)
  (t : FStarC_Syntax_Syntax.term) : FStarC_Syntax_Syntax.term=
  let uu___ =
    Obj.magic
      (FStarC_Syntax_VisitM.visitM_term_univs uu___0 pq
         (fun uu___1 ->
            (Obj.magic (op_Less_Less (fun uu___1 -> I uu___1) vt)) uu___1)
         (fun uu___1 ->
            (Obj.magic (op_Less_Less (fun uu___1 -> I uu___1) vu)) uu___1) t) in
  __proj__I__item__run uu___
let visit_sigelt (pq : Prims.bool)
  (vt : FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term)
  (vu : FStarC_Syntax_Syntax.universe -> FStarC_Syntax_Syntax.universe)
  (se : FStarC_Syntax_Syntax.sigelt) : FStarC_Syntax_Syntax.sigelt=
  let uu___ =
    Obj.magic
      (FStarC_Syntax_VisitM.visitM_sigelt uu___0 pq
         (fun uu___1 ->
            (Obj.magic (op_Less_Less (fun uu___1 -> I uu___1) vt)) uu___1)
         (fun uu___1 ->
            (Obj.magic (op_Less_Less (fun uu___1 -> I uu___1) vu)) uu___1) se) in
  __proj__I__item__run uu___
