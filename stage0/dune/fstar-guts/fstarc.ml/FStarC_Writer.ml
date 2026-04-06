open Prims
type ('m, 'uuuuu, 'a) writer =
  | Wr of ('m * 'a) 
let uu___is_Wr (uu___ : 'm FStarC_Class_Monoid.monoid) (a : unit)
  (projectee : ('m, Obj.t, Obj.t) writer) : Prims.bool= true
let __proj__Wr__item___0 (uu___ : 'm FStarC_Class_Monoid.monoid) (a : unit)
  (projectee : ('m, Obj.t, Obj.t) writer) : ('m * Obj.t)=
  match projectee with | Wr _0 -> _0
let writer_return (uu___ : 'm FStarC_Class_Monoid.monoid) (a : unit)
  (x : Obj.t) : ('m, Obj.t, Obj.t) writer=
  Wr ((FStarC_Class_Monoid.mzero uu___), x)
let run_writer (uu___ : 'm FStarC_Class_Monoid.monoid) (a : unit)
  (x : ('m, Obj.t, Obj.t) writer) : ('m * Obj.t)=
  let uu___1 = x in match uu___1 with | Wr (m1, x1) -> (m1, x1)
let writer_bind (uu___ : 'm FStarC_Class_Monoid.monoid) (a : unit) (b : unit)
  (x : ('m, Obj.t, Obj.t) writer) (f : Obj.t -> ('m, Obj.t, Obj.t) writer) :
  ('m, Obj.t, Obj.t) writer=
  let uu___1 = x in
  match uu___1 with
  | Wr (a1, x1) ->
      let uu___2 = f x1 in
      (match uu___2 with
       | Wr (b1, y) ->
           let uu___3 =
             let uu___4 = FStarC_Class_Monoid.mplus uu___ a1 b1 in
             (uu___4, y) in
           Wr uu___3)
let monad_writer (d : 'm FStarC_Class_Monoid.monoid) :
  ('m, Obj.t, unit) writer FStarC_Class_Monad.monad=
  {
    FStarC_Class_Monad.return =
      (fun uu___1 uu___ -> (Obj.magic (writer_return d)) uu___1 uu___);
    FStarC_Class_Monad.bind =
      (fun uu___3 uu___2 uu___1 uu___ ->
         (Obj.magic (writer_bind d)) uu___3 uu___2 uu___1 uu___)
  }
let emit (uu___ : 'm FStarC_Class_Monoid.monoid) (x : 'm) :
  ('m, Obj.t, unit) writer= Wr (x, ())
