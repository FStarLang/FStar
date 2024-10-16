open Prims
type ('m, 'uuuuu, 'a) writer =
  | Wr of ('m * 'a) 
let uu___is_Wr :
  'm .
    'm FStarC_Class_Monoid.monoid ->
      unit -> ('m, unit, Obj.t) writer -> Prims.bool
  = fun uu___ -> fun a -> fun projectee -> true
let __proj__Wr__item___0 :
  'm .
    'm FStarC_Class_Monoid.monoid ->
      unit -> ('m, unit, Obj.t) writer -> ('m * Obj.t)
  = fun uu___ -> fun a -> fun projectee -> match projectee with | Wr _0 -> _0
let writer_return :
  'm .
    'm FStarC_Class_Monoid.monoid ->
      unit -> Obj.t -> ('m, unit, Obj.t) writer
  = fun uu___ -> fun a -> fun x -> Wr ((FStarC_Class_Monoid.mzero uu___), x)
let run_writer :
  'm .
    'm FStarC_Class_Monoid.monoid ->
      unit -> ('m, unit, Obj.t) writer -> ('m * Obj.t)
  =
  fun uu___ ->
    fun a ->
      fun x -> let uu___1 = x in match uu___1 with | Wr (m1, x1) -> (m1, x1)
let writer_bind :
  'm .
    'm FStarC_Class_Monoid.monoid ->
      unit ->
        unit ->
          ('m, unit, Obj.t) writer ->
            (Obj.t -> ('m, unit, Obj.t) writer) -> ('m, unit, Obj.t) writer
  =
  fun uu___ ->
    fun a ->
      fun b ->
        fun x ->
          fun f ->
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
let monad_writer :
  'm .
    'm FStarC_Class_Monoid.monoid ->
      ('m, unit, unit) writer FStarC_Class_Monad.monad
  =
  fun d ->
    {
      FStarC_Class_Monad.return =
        (fun uu___1 ->
           fun uu___ -> (Obj.magic (writer_return d)) uu___1 uu___);
      FStarC_Class_Monad.op_let_Bang =
        (fun uu___3 ->
           fun uu___2 ->
             fun uu___1 ->
               fun uu___ ->
                 (Obj.magic (writer_bind d)) uu___3 uu___2 uu___1 uu___)
    }
let emit :
  'm . 'm FStarC_Class_Monoid.monoid -> 'm -> ('m, unit, unit) writer =
  fun uu___ -> fun x -> Wr (x, ())