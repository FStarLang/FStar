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
let (monad_option : unit FStar_Pervasives_Native.option monad) =
  {
    return =
      (fun uu___1 ->
         fun uu___ ->
           (fun a -> fun x -> Obj.magic (FStar_Pervasives_Native.Some x))
             uu___1 uu___);
    op_let_Bang =
      (fun uu___3 ->
         fun uu___2 ->
           fun uu___1 ->
             fun uu___ ->
               (fun uu___1 ->
                  fun uu___ -> Obj.magic FStar_Compiler_Util.bind_opt) uu___3
                 uu___2 uu___1 uu___)
  }
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
let op_Less_Dollar_Greater :
  'm . 'm monad -> unit -> unit -> (Obj.t -> Obj.t) -> 'm -> 'm =
  fun uu___ ->
    fun a ->
      fun b ->
        fun f ->
          fun x ->
            op_let_Bang uu___ () () x
              (fun v -> let uu___1 = f v in return uu___ () uu___1)
let op_Less_Star_Greater : 'm . 'm monad -> unit -> unit -> 'm -> 'm -> 'm =
  fun uu___ ->
    fun a ->
      fun b ->
        fun ff ->
          fun x ->
            op_let_Bang uu___ () () ff
              (fun uu___1 ->
                 (fun f ->
                    let f = Obj.magic f in
                    Obj.magic
                      (op_let_Bang uu___ () () x
                         (fun v -> let uu___1 = f v in return uu___ () uu___1)))
                   uu___1)