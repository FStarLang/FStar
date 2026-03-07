open Prims
type 'm monad =
  {
  return: unit -> Obj.t -> 'm ;
  bind: unit -> unit -> 'm -> (Obj.t -> 'm) -> 'm }
let __proj__Mkmonad__item__return (projectee : 'm monad) :
  unit -> Obj.t -> 'm= match projectee with | { return; bind;_} -> return
let __proj__Mkmonad__item__bind (projectee : 'm monad) :
  unit -> unit -> 'm -> (Obj.t -> 'm) -> 'm=
  match projectee with | { return; bind;_} -> bind
let return (projectee : 'm monad) : unit -> Obj.t -> 'm=
  match projectee with | { return = return1; bind;_} -> return1
let bind (projectee : 'm monad) : unit -> unit -> 'm -> (Obj.t -> 'm) -> 'm=
  match projectee with | { return = return1; bind = bind1;_} -> bind1
let op_let_Bang : 'm monad -> unit -> unit -> 'm -> (Obj.t -> 'm) -> 'm= bind
let op_Greater_Greater_Equals :
  'm monad -> unit -> unit -> 'm -> (Obj.t -> 'm) -> 'm= bind
let op_Greater_Equals_Greater (uu___ : 'm monad) (a : unit) (b : unit)
  (c : unit) (f : Obj.t -> 'm) (g : Obj.t -> 'm) (x : Obj.t) : 'm=
  let uu___1 = f x in op_Greater_Greater_Equals uu___ () () uu___1 g
let monad_option : unit FStar_Pervasives_Native.option monad=
  {
    return =
      (fun uu___1 uu___ ->
         (fun a x -> Obj.magic (FStar_Pervasives_Native.Some x)) uu___1 uu___);
    bind =
      (fun uu___3 uu___2 uu___1 uu___ ->
         (fun a b o ->
            let o = Obj.magic o in
            fun f ->
              let f = Obj.magic f in
              match o with
              | FStar_Pervasives_Native.None ->
                  Obj.magic FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some v -> Obj.magic (f v)) uu___3
           uu___2 uu___1 uu___)
  }
let monad_list : unit Prims.list monad=
  {
    return = (fun uu___1 uu___ -> (fun a x -> Obj.magic [x]) uu___1 uu___);
    bind =
      (fun uu___3 uu___2 uu___1 uu___ ->
         (fun a b l ->
            let l = Obj.magic l in
            fun f ->
              let f = Obj.magic f in Obj.magic (FStarC_List.concatMap f l))
           uu___3 uu___2 uu___1 uu___)
  }
let rec mapM :
  'm . 'm monad -> unit -> unit -> (Obj.t -> 'm) -> Obj.t Prims.list -> 'm =
  fun uu___ a b f l ->
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
                     Obj.magic (return uu___ () (Obj.magic (y :: ys))))
                    uu___3))
let mapMi (uu___ : 'm monad) (a : unit) (b : unit)
  (f : Prims.int -> Obj.t -> 'm) (l : Obj.t Prims.list) : 'm=
  let rec mapMi_go i l1 =
    match l1 with
    | [] -> return uu___ () (Obj.magic [])
    | x::xs ->
        let uu___1 = f i x in
        op_let_Bang uu___ () () uu___1
          (fun y ->
             let uu___2 = mapMi_go (i + Prims.int_one) xs in
             op_let_Bang uu___ () () uu___2
               (fun uu___3 ->
                  (fun ys ->
                     let ys = Obj.magic ys in
                     Obj.magic (return uu___ () (Obj.magic (y :: ys))))
                    uu___3)) in
  mapMi_go Prims.int_zero l
let map_optM (uu___ : 'm monad) (a : unit) (b : unit) (f : Obj.t -> 'm)
  (l : Obj.t FStar_Pervasives_Native.option) : 'm=
  match l with
  | FStar_Pervasives_Native.None ->
      return uu___ () (Obj.magic FStar_Pervasives_Native.None)
  | FStar_Pervasives_Native.Some x ->
      let uu___1 = f x in
      op_let_Bang uu___ () () uu___1
        (fun x1 ->
           return uu___ () (Obj.magic (FStar_Pervasives_Native.Some x1)))
let rec iterM :
  'm . 'm monad -> unit -> (Obj.t -> 'm) -> Obj.t Prims.list -> 'm =
  fun uu___ a f l ->
    match l with
    | [] -> return uu___ () (Obj.repr ())
    | x::xs ->
        let uu___1 = f x in
        op_let_Bang uu___ () () uu___1
          (fun uu___2 ->
             (fun uu___2 ->
                let uu___2 = Obj.magic uu___2 in
                Obj.magic (iterM uu___ () f xs)) uu___2)
let rec foldM_left :
  'm .
    'm monad ->
      unit ->
        unit -> (Obj.t -> Obj.t -> 'm) -> Obj.t -> Obj.t Prims.list -> 'm
  =
  fun uu___ a b f e xs ->
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
  fun uu___ a b f xs e ->
    match xs with
    | [] -> return uu___ () e
    | x::xs1 ->
        let uu___1 = foldM_right uu___ () () f xs1 e in
        op_let_Bang uu___ () () uu___1 (fun e' -> f x e')
let op_Less_Dollar_Greater (uu___ : 'm monad) (a : unit) (b : unit)
  (f : Obj.t -> Obj.t) (x : 'm) : 'm=
  op_let_Bang uu___ () () x (fun v -> let r = f v in return uu___ () r)
let op_Less_Star_Greater (uu___ : 'm monad) (a : unit) (b : unit) (ff : 'm)
  (x : 'm) : 'm=
  op_let_Bang uu___ () () ff
    (fun uu___1 ->
       (fun f ->
          let f = Obj.magic f in
          Obj.magic
            (op_let_Bang uu___ () () x (fun v -> return uu___ () (f v))))
         uu___1)
let fmap (uu___ : 'm monad) (a : unit) (b : unit) (f : Obj.t -> Obj.t)
  (m1 : 'm) : 'm=
  op_let_Bang uu___ () () m1 (fun v -> let r = f v in return uu___ () r)
