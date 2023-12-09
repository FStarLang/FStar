open Prims
type 'm monad =
  {
  return: unit -> Obj.t -> 'm ;
  op_let_Bang: unit -> unit -> 'm -> (Obj.t -> 'm) -> 'm }
let __proj__Mkmonad__item__return : 'm . 'm monad -> unit -> Obj.t -> 'm =
  fun projectee -> match projectee with | { return; op_let_Bang;_} -> return
let __proj__Mkmonad__item__op_let_Bang :
  'm . 'm monad -> unit -> unit -> 'm -> (Obj.t -> 'm) -> 'm =
  fun projectee ->
    match projectee with | { return; op_let_Bang;_} -> op_let_Bang
let return : 'm . 'm monad -> unit -> Obj.t -> 'm =
  fun projectee ->
    match projectee with | { return = return1; op_let_Bang;_} -> return1
let op_let_Bang : 'm . 'm monad -> unit -> unit -> 'm -> (Obj.t -> 'm) -> 'm
  =
  fun projectee ->
    match projectee with
    | { return = return1; op_let_Bang = op_let_Bang1;_} -> op_let_Bang1
let rec mapM :
  'm . 'm monad -> unit -> unit -> (Obj.t -> 'm) -> Obj.t Prims.list -> 'm =
  fun uu___ ->
    fun a ->
      fun b ->
        fun f ->
          fun l ->
            match l with
            | [] -> return uu___ () (Obj.magic [])
            | x::xs ->
                let uu___1 = f x in
                op_let_Bang uu___ () () uu___1
                  (fun y ->
                     let uu___2 = mapM uu___ () () f xs in
                     op_let_Bang uu___ () () uu___2
                       (fun uu___3 ->
                          (fun ys ->
                             let ys = Obj.magic ys in
                             Obj.magic
                               (return uu___ () (Obj.magic (y :: ys))))
                            uu___3))
let rec foldM_left :
  'm .
    'm monad ->
      unit ->
        unit -> (Obj.t -> Obj.t -> 'm) -> Obj.t -> Obj.t Prims.list -> 'm
  =
  fun uu___ ->
    fun a ->
      fun b ->
        fun f ->
          fun e ->
            fun xs ->
              match xs with
              | [] -> return uu___ () e
              | x::xs1 ->
                  let uu___1 = f e x in
                  op_let_Bang uu___ () () uu___1
                    (fun e' -> foldM_left uu___ () () f e' xs1)
let rec foldM_right :
  'm .
    'm monad ->
      unit ->
        unit -> (Obj.t -> Obj.t -> 'm) -> Obj.t Prims.list -> Obj.t -> 'm
  =
  fun uu___ ->
    fun a ->
      fun b ->
        fun f ->
          fun xs ->
            fun e ->
              match xs with
              | [] -> return uu___ () e
              | x::xs1 ->
                  let uu___1 = foldM_right uu___ () () f xs1 e in
                  op_let_Bang uu___ () () uu___1 (fun e' -> f x e')