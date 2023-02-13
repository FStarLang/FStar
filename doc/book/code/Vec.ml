 open Prims
type 'a even =
  | ENil 
  | ECons of 'a * 'a odd 
and 'a odd =
  | OCons of 'a * 'a even 
let uu___is_ENil : 'a . 'a even -> Prims.bool =
  fun projectee -> match projectee with | ENil -> true | uu___ -> false
let uu___is_ECons : 'a . 'a even -> Prims.bool =
  fun projectee ->
    match projectee with | ECons (_0, _1) -> true | uu___ -> false
let __proj__ECons__item___0 : 'a . 'a even -> 'a =
  fun projectee -> match projectee with | ECons (_0, _1) -> _0
let __proj__ECons__item___1 : 'a . 'a even -> 'a odd =
  fun projectee -> match projectee with | ECons (_0, _1) -> _1
let uu___is_OCons : 'a . 'a odd -> Prims.bool = fun projectee -> true
let __proj__OCons__item___0 : 'a . 'a odd -> 'a =
  fun projectee -> match projectee with | OCons (_0, _1) -> _0
let __proj__OCons__item___1 : 'a . 'a odd -> 'a even =
  fun projectee -> match projectee with | OCons (_0, _1) -> _1
let rec elength : 'a . 'a even -> Prims.nat =
  fun e ->
    match e with
    | ENil -> Prims.int_zero
    | ECons (uu___, tl) -> Prims.int_one + (olength tl)
and olength : 'a . 'a odd -> Prims.nat =
  fun o ->
    let uu___ = o in
    match uu___ with | OCons (uu___1, tl) -> Prims.int_one + (elength tl)
type ('a, 'dummyV0) even_or_odd_list =
  | EONil 
  | EOCons of 'a * Prims.bool * ('a, unit) even_or_odd_list 
let uu___is_EONil :
  'a . Prims.bool -> ('a, unit) even_or_odd_list -> Prims.bool =
  fun uu___ ->
    fun projectee -> match projectee with | EONil -> true | uu___1 -> false
let uu___is_EOCons :
  'a . Prims.bool -> ('a, unit) even_or_odd_list -> Prims.bool =
  fun uu___ ->
    fun projectee ->
      match projectee with | EOCons (_0, b, _2) -> true | uu___1 -> false
let __proj__EOCons__item___0 :
  'a . Prims.bool -> ('a, unit) even_or_odd_list -> 'a =
  fun uu___ ->
    fun projectee -> match projectee with | EOCons (_0, b, _2) -> _0
let __proj__EOCons__item__b :
  'a . Prims.bool -> ('a, unit) even_or_odd_list -> Prims.bool =
  fun uu___ ->
    fun projectee -> match projectee with | EOCons (_0, b, _2) -> b
let __proj__EOCons__item___2 :
  'a .
    Prims.bool -> ('a, unit) even_or_odd_list -> ('a, unit) even_or_odd_list
  =
  fun uu___ ->
    fun projectee -> match projectee with | EOCons (_0, b, _2) -> _2
let rec eo_length :
  'a . Prims.bool -> ('a, unit) even_or_odd_list -> Prims.nat =
  fun b ->
    fun l ->
      match l with
      | EONil -> Prims.int_zero
      | EOCons (uu___, uu___1, tl) -> Prims.int_one + (eo_length uu___1 tl)
(* SNIPPET_START: vec *)
type ('a, 'dummy) vec =
  | Nil 
  | Cons of Prims.nat * 'a * ('a, unit) vec
(* SNIPPET_END: vec *)
let uu___is_Nil : 'a . Prims.nat -> ('a, unit) vec -> Prims.bool =
  fun uu___ ->
    fun projectee -> match projectee with | Nil -> true | uu___1 -> false
let uu___is_Cons : 'a . Prims.nat -> ('a, unit) vec -> Prims.bool =
  fun uu___ ->
    fun projectee ->
      match projectee with | Cons (n, hd, tl) -> true | uu___1 -> false
let __proj__Cons__item__n : 'a . Prims.nat -> ('a, unit) vec -> Prims.nat =
  fun uu___ -> fun projectee -> match projectee with | Cons (n, hd, tl) -> n
let __proj__Cons__item__hd : 'a . Prims.nat -> ('a, unit) vec -> 'a =
  fun uu___ -> fun projectee -> match projectee with | Cons (n, hd, tl) -> hd
let __proj__Cons__item__tl :
  'a . Prims.nat -> ('a, unit) vec -> ('a, unit) vec =
  fun uu___ -> fun projectee -> match projectee with | Cons (n, hd, tl) -> tl
type ('a, 'n) vec' = ('a, unit) vec
let rec get : 'a . Prims.int -> Prims.nat -> ('a, unit) vec -> 'a =
  fun n ->
    fun i ->
      fun v ->
        match v with
        | Nil -> FStar_Pervasives.false_elim ()
        | Cons (uu___, hd, tl) ->
            if i = Prims.int_zero
            then hd
            else get uu___ (i - Prims.int_one) tl
let rec split_at :
  'a .
    Prims.int ->
      Prims.nat -> ('a, unit) vec -> (('a, unit) vec * ('a, unit) vec)
  =
  fun n ->
    fun i ->
      fun v ->
        if i = Prims.int_zero
        then (Nil, v)
        else
          (let uu___1 = v in
           match uu___1 with
           | Cons (uu___2, hd, tl) ->
               let uu___3 = split_at uu___2 (i - Prims.int_one) tl in
               (match uu___3 with
                | (l, r) -> ((Cons ((i - Prims.int_one), hd, l)), r)))
(* SNIPPET_START: append *)
let rec append :
  'a .
    Prims.nat ->
      Prims.nat -> ('a, unit) vec -> ('a, unit) vec -> ('a, unit) vec
  =
  fun n ->
    fun m ->
      fun v1 ->
        fun v2 ->
          match v1 with
          | Nil -> v2
          | Cons (n', hd, tl) ->
              Cons ((n' + m), hd, (append n' m tl v2))
(* SNIPPET_END: append *)
let rec reverse : 'a . Prims.nat -> ('a, unit) vec -> ('a, unit) vec =
  fun n ->
    fun v ->
      match v with
      | Nil -> Nil
      | Cons (uu___, hd, tl) ->
          append uu___ Prims.int_one (reverse uu___ tl)
            (Cons (Prims.int_zero, hd, Nil))
let split_at_tail :
  'a .
    Prims.int ->
      Prims.nat -> ('a, unit) vec -> (('a, unit) vec * ('a, unit) vec)
  =
  fun n ->
    fun i ->
      fun v ->
        let rec aux j v1 out =
          if j = Prims.int_zero
          then ((reverse (i - j) out), v1)
          else
            (let uu___1 = v1 in
             match uu___1 with
             | Cons (uu___2, hd, tl) ->
                 aux (j - Prims.int_one) tl (Cons ((i - j), hd, out))) in
        aux i v Nil
let rec foldr :
  'a .
    Prims.nat ->
      unit -> ('a -> Obj.t -> Obj.t) -> ('a, unit) vec -> Obj.t -> Obj.t
  =
  fun n ->
    fun acc ->
      fun f ->
        fun v ->
          fun init ->
            match v with
            | Nil -> init
            | Cons (uu___, hd, tl) -> f hd (foldr uu___ () f tl init)
let rec (pow2 : Prims.nat -> Prims.nat) =
  fun n ->
    if n = Prims.int_zero
    then Prims.int_one
    else (Prims.of_int (2)) * (pow2 (n - Prims.int_one))
let rec fold_right : 'a 'b . ('b -> 'a -> 'a) -> 'b Prims.list -> 'a -> 'a =
  fun f ->
    fun l ->
      fun x -> match l with | [] -> x | hd::tl -> f hd (fold_right f tl x)


let (implies_intro :
  unit -> (FStar_Reflection_Types.binder, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (Prims.mk_range "Vec.fst" (Prims.of_int (160)) (Prims.of_int (2))
         (Prims.of_int (160)) (Prims.of_int (14)))
      (Prims.mk_range "Vec.fst" (Prims.of_int (161)) (Prims.of_int (2))
         (Prims.of_int (161)) (Prims.of_int (9)))
      (Obj.magic
         (FStar_Tactics_Derived.apply
            (FStar_Reflection_Builtins.pack_ln
               (FStar_Reflection_Data.Tv_FVar
                  (FStar_Reflection_Builtins.pack_fv ["Vec"; "lem"])))))
      (fun uu___1 ->
         (fun uu___1 -> Obj.magic (FStar_Tactics_Builtins.intro ())) uu___1)

let (split : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_Derived.apply
      (FStar_Reflection_Builtins.pack_ln
         (FStar_Reflection_Data.Tv_FVar
            (FStar_Reflection_Builtins.pack_fv ["Vec"; "split_lem'"])))
