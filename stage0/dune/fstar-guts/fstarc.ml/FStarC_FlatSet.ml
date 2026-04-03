open Prims
type 't flat_set = 't Prims.list
type 'a t = 'a flat_set
let rec add :
  'a . 'a FStarC_Class_Ord.ord -> 'a -> 'a flat_set -> 'a flat_set =
  fun uu___ x s ->
    match s with
    | [] -> [x]
    | y::yy ->
        let r =
          FStarC_Class_Deq.op_Equals_Question (FStarC_Class_Ord.ord_eq uu___)
            x y in
        if r then s else (let uu___2 = add uu___ x yy in y :: uu___2)
let empty (uu___ : unit) : 'a flat_set= []
let from_list (uu___ : 'a FStarC_Class_Ord.ord) (xs : 'a Prims.list) :
  'a flat_set= FStarC_Class_Ord.dedup uu___ xs
let mem (uu___ : 'a FStarC_Class_Ord.ord) (x : 'a) (s : 'a flat_set) :
  Prims.bool=
  FStarC_List.existsb
    (fun y ->
       FStarC_Class_Deq.op_Equals_Question (FStarC_Class_Ord.ord_eq uu___) x
         y) s
let singleton (uu___ : 'a FStarC_Class_Ord.ord) (x : 'a) : 'a flat_set= [x]
let is_empty (s : 'a flat_set) : Prims.bool= Prims.uu___is_Nil s
let addn (uu___ : 'a FStarC_Class_Ord.ord) (xs : 'a Prims.list)
  (ys : 'a flat_set) : 'a flat_set= FStarC_List.fold_right (add uu___) xs ys
let rec remove :
  'a . 'a FStarC_Class_Ord.ord -> 'a -> 'a flat_set -> 'a flat_set =
  fun uu___ x s ->
    match s with
    | [] -> []
    | y::yy ->
        let r =
          FStarC_Class_Deq.op_Equals_Question (FStarC_Class_Ord.ord_eq uu___)
            x y in
        if r then yy else (let uu___2 = remove uu___ x yy in y :: uu___2)
let elems (s : 'a flat_set) : 'a Prims.list= s
let for_all (p : 'a -> Prims.bool) (s : 'a flat_set) : Prims.bool=
  FStarC_List.for_all p (elems s)
let for_any (p : 'a -> Prims.bool) (s : 'a flat_set) : Prims.bool=
  FStarC_List.existsb p (elems s)
let subset (uu___ : 'a FStarC_Class_Ord.ord) (s1 : 'a flat_set)
  (s2 : 'a flat_set) : Prims.bool= for_all (fun y -> mem uu___ y s2) s1
let equal (uu___ : 'a FStarC_Class_Ord.ord) (s1 : 'a flat_set)
  (s2 : 'a flat_set) : Prims.bool=
  let r =
    let uu___1 = FStarC_Class_Ord.sort uu___ s1 in
    let uu___2 = FStarC_Class_Ord.sort uu___ s2 in
    FStarC_Class_Deq.op_Equals_Question
      (FStarC_Class_Ord.ord_eq (FStarC_Class_Ord.ord_list uu___)) uu___1
      uu___2 in
  r
let union (uu___ : 'a FStarC_Class_Ord.ord) (s1 : 'a flat_set)
  (s2 : 'a flat_set) : 'a flat_set=
  FStarC_List.fold_left (fun s x -> add uu___ x s) s1 s2
let inter (uu___ : 'a FStarC_Class_Ord.ord) (s1 : 'a flat_set)
  (s2 : 'a flat_set) : 'a flat_set=
  FStarC_List.filter (fun y -> mem uu___ y s2) s1
let diff (uu___ : 'a FStarC_Class_Ord.ord) (s1 : 'a flat_set)
  (s2 : 'a flat_set) : 'a flat_set=
  FStarC_List.filter (fun y -> let r = mem uu___ y s2 in Prims.op_Negation r)
    s1
let collect (uu___ : 'b FStarC_Class_Ord.ord) (f : 'a -> 'b flat_set)
  (l : 'a Prims.list) : 'b flat_set=
  FStarC_List.fold_right
    (fun x acc -> let uu___1 = f x in union uu___ uu___1 acc) l (empty ())
let showable_set (uu___ : 'a FStarC_Class_Ord.ord)
  (uu___1 : 'a FStarC_Class_Show.showable) :
  'a flat_set FStarC_Class_Show.showable=
  {
    FStarC_Class_Show.show =
      (fun s ->
         FStarC_Class_Show.show (FStarC_Class_Show.show_list uu___1)
           (elems s))
  }
let setlike_flat_set (uu___ : 'a FStarC_Class_Ord.ord) :
  ('a, 'a flat_set) FStarC_Class_Setlike.setlike=
  {
    FStarC_Class_Setlike.empty = empty;
    FStarC_Class_Setlike.singleton = (singleton uu___);
    FStarC_Class_Setlike.is_empty = is_empty;
    FStarC_Class_Setlike.add = (add uu___);
    FStarC_Class_Setlike.remove = (remove uu___);
    FStarC_Class_Setlike.mem = (mem uu___);
    FStarC_Class_Setlike.equal = (equal uu___);
    FStarC_Class_Setlike.subset = (subset uu___);
    FStarC_Class_Setlike.union = (union uu___);
    FStarC_Class_Setlike.inter = (inter uu___);
    FStarC_Class_Setlike.diff = (diff uu___);
    FStarC_Class_Setlike.for_all = for_all;
    FStarC_Class_Setlike.for_any = for_any;
    FStarC_Class_Setlike.elems = elems;
    FStarC_Class_Setlike.filter = FStarC_List.filter;
    FStarC_Class_Setlike.collect = (collect uu___);
    FStarC_Class_Setlike.from_list = (from_list uu___);
    FStarC_Class_Setlike.addn = (addn uu___)
  }
