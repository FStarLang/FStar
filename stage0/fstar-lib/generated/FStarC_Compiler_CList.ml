open Prims
type 'a clist =
  | CNil 
  | CCons of 'a * 'a clist 
  | CCat of 'a clist * 'a clist 
let uu___is_CNil : 'a . 'a clist -> Prims.bool =
  fun projectee -> match projectee with | CNil -> true | uu___ -> false
let uu___is_CCons : 'a . 'a clist -> Prims.bool =
  fun projectee ->
    match projectee with | CCons (_0, _1) -> true | uu___ -> false
let __proj__CCons__item___0 : 'a . 'a clist -> 'a =
  fun projectee -> match projectee with | CCons (_0, _1) -> _0
let __proj__CCons__item___1 : 'a . 'a clist -> 'a clist =
  fun projectee -> match projectee with | CCons (_0, _1) -> _1
let uu___is_CCat : 'a . 'a clist -> Prims.bool =
  fun projectee ->
    match projectee with | CCat (_0, _1) -> true | uu___ -> false
let __proj__CCat__item___0 : 'a . 'a clist -> 'a clist =
  fun projectee -> match projectee with | CCat (_0, _1) -> _0
let __proj__CCat__item___1 : 'a . 'a clist -> 'a clist =
  fun projectee -> match projectee with | CCat (_0, _1) -> _1
type 'a t = 'a clist
let ccat : 'a . 'a clist -> 'a clist -> 'a clist =
  fun xs ->
    fun ys ->
      match (xs, ys) with
      | (CNil, uu___) -> ys
      | (uu___, CNil) -> xs
      | uu___ -> CCat (xs, ys)
let rec view : 'a . 'a clist -> ('a, 'a clist) FStarC_Class_Listlike.view_t =
  fun l ->
    match l with
    | CNil -> FStarC_Class_Listlike.VNil
    | CCons (x, xs) -> FStarC_Class_Listlike.VCons (x, xs)
    | CCat (CCat (xs, ys), zs) -> view (CCat (xs, (CCat (ys, zs))))
    | CCat (xs, ys) ->
        (match view xs with
         | FStarC_Class_Listlike.VNil -> view ys
         | FStarC_Class_Listlike.VCons (x, xs') ->
             FStarC_Class_Listlike.VCons (x, (CCat (xs', ys))))
let listlike_clist : 'a . unit -> ('a, 'a t) FStarC_Class_Listlike.listlike =
  fun uu___ ->
    {
      FStarC_Class_Listlike.empty = CNil;
      FStarC_Class_Listlike.cons =
        (fun uu___1 -> fun uu___2 -> CCons (uu___1, uu___2));
      FStarC_Class_Listlike.view = view
    }
let monoid_clist : 'a . unit -> 'a t FStarC_Class_Monoid.monoid =
  fun uu___ ->
    { FStarC_Class_Monoid.mzero = CNil; FStarC_Class_Monoid.mplus = ccat }
let showable_clist :
  'a . 'a FStarC_Class_Show.showable -> 'a t FStarC_Class_Show.showable =
  fun uu___ ->
    {
      FStarC_Class_Show.show =
        (fun l ->
           let uu___1 = FStarC_Class_Listlike.to_list (listlike_clist ()) l in
           FStarC_Class_Show.show (FStarC_Class_Show.show_list uu___) uu___1)
    }
let eq_clist : 'a . 'a FStarC_Class_Deq.deq -> 'a t FStarC_Class_Deq.deq =
  fun d ->
    {
      FStarC_Class_Deq.op_Equals_Question =
        (fun l1 ->
           fun l2 ->
             let uu___ = FStarC_Class_Listlike.to_list (listlike_clist ()) l1 in
             let uu___1 =
               FStarC_Class_Listlike.to_list (listlike_clist ()) l2 in
             FStarC_Class_Deq.op_Equals_Question
               (FStarC_Class_Deq.deq_list d) uu___ uu___1)
    }
let ord_clist : 'a . 'a FStarC_Class_Ord.ord -> 'a t FStarC_Class_Ord.ord =
  fun d ->
    {
      FStarC_Class_Ord.super = (eq_clist (FStarC_Class_Ord.ord_eq d));
      FStarC_Class_Ord.cmp =
        (fun l1 ->
           fun l2 ->
             let uu___ = FStarC_Class_Listlike.to_list (listlike_clist ()) l1 in
             let uu___1 =
               FStarC_Class_Listlike.to_list (listlike_clist ()) l2 in
             FStarC_Class_Ord.cmp (FStarC_Class_Ord.ord_list d) uu___ uu___1)
    }
let rec map : 'a 'b . ('a -> 'b) -> 'a clist -> 'b clist =
  fun f ->
    fun l ->
      match l with
      | CNil -> CNil
      | CCons (x, xs) ->
          let uu___ = f x in let uu___1 = map f xs in CCons (uu___, uu___1)
      | CCat (xs, ys) ->
          let uu___ = map f xs in let uu___1 = map f ys in ccat uu___ uu___1
let rec existsb : 'a . ('a -> Prims.bool) -> 'a clist -> Prims.bool =
  fun p ->
    fun l ->
      match l with
      | CNil -> false
      | CCons (x, xs) -> (p x) || (existsb p xs)
      | CCat (xs, ys) -> (existsb p xs) || (existsb p ys)
let rec for_all : 'a . ('a -> Prims.bool) -> 'a clist -> Prims.bool =
  fun p ->
    fun l ->
      match l with
      | CNil -> true
      | CCons (x, xs) -> (p x) && (for_all p xs)
      | CCat (xs, ys) -> (for_all p xs) && (for_all p ys)
let rec partition :
  'a . ('a -> Prims.bool) -> 'a clist -> ('a clist * 'a clist) =
  fun p ->
    fun l ->
      match l with
      | CNil -> (CNil, CNil)
      | CCons (x, xs) ->
          let uu___ = partition p xs in
          (match uu___ with
           | (ys, zs) ->
               let uu___1 = p x in
               if uu___1
               then ((CCons (x, ys)), zs)
               else (ys, (CCons (x, zs))))
      | CCat (xs, ys) ->
          let uu___ = partition p xs in
          (match uu___ with
           | (ys1, zs) ->
               let uu___1 = partition p ys1 in
               (match uu___1 with
                | (us, vs) ->
                    let uu___2 = ccat ys1 us in
                    let uu___3 = ccat zs vs in (uu___2, uu___3)))
let rec collect : 'a 'b . ('a -> 'b clist) -> 'a clist -> 'b clist =
  fun f ->
    fun l ->
      match l with
      | CNil -> CNil
      | CCons (x, xs) ->
          let uu___ = f x in let uu___1 = collect f xs in ccat uu___ uu___1
      | CCat (xs, ys) ->
          let uu___ = collect f xs in
          let uu___1 = collect f ys in ccat uu___ uu___1