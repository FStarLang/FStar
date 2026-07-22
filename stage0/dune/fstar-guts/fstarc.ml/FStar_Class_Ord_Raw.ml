open Prims
type 'a ord =
  {
  super: 'a FStar_Class_Eq_Raw.deq ;
  cmp: 'a -> 'a -> FStar_Order.order }
let __proj__Mkord__item__super (projectee : 'a ord) :
  'a FStar_Class_Eq_Raw.deq= match projectee with | { super; cmp;_} -> super
let __proj__Mkord__item__cmp (projectee : 'a ord) :
  'a -> 'a -> FStar_Order.order=
  match projectee with | { super; cmp;_} -> cmp
let super (projectee : 'a ord) : 'a FStar_Class_Eq_Raw.deq=
  __proj__Mkord__item__super projectee
let cmp (projectee : 'a ord) : 'a -> 'a -> FStar_Order.order=
  __proj__Mkord__item__cmp projectee
let ord_eq (d : 'a ord) : 'a FStar_Class_Eq_Raw.deq= d.super
let op_Less_Question (uu___ : 'a ord) (x : 'a) (y : 'a) : Prims.bool=
  FStar_Order.uu___is_Lt (cmp uu___ x y)
let op_Greater_Question (uu___ : 'a ord) (x : 'a) (y : 'a) : Prims.bool=
  FStar_Order.uu___is_Gt (cmp uu___ x y)
let op_Less_Equals_Question (uu___ : 'a ord) (x : 'a) (y : 'a) : Prims.bool=
  Prims.op_Negation (op_Greater_Question uu___ x y)
let op_Greater_Equals_Question (uu___ : 'a ord) (x : 'a) (y : 'a) :
  Prims.bool= Prims.op_Negation (op_Less_Question uu___ x y)
let min (uu___ : 'a ord) (x : 'a) (y : 'a) : 'a=
  if op_Less_Equals_Question uu___ x y then x else y
let max (uu___ : 'a ord) (x : 'a) (y : 'a) : 'a=
  if op_Greater_Equals_Question uu___ x y then x else y
let rec sort : 'a . 'a ord -> 'a Prims.list -> 'a Prims.list =
  fun uu___ xs ->
    let rec insert x xs1 =
      match xs1 with
      | [] -> [x]
      | y::ys ->
          if op_Less_Equals_Question uu___ x y
          then x :: y :: ys
          else y :: (insert x ys) in
    match xs with | [] -> [] | x::xs1 -> insert x (sort uu___ xs1)
let sort_by (f : 'a -> 'a -> FStar_Order.order) (xs : 'a Prims.list) :
  'a Prims.list=
  let d =
    {
      super =
        { FStar_Class_Eq_Raw.eq = (fun a1 b -> (f a1 b) = FStar_Order.Eq) };
      cmp = f
    } in
  sort d xs
let dedup (uu___ : 'a ord) (xs : 'a Prims.list) : 'a Prims.list=
  let out =
    FStar_List_Tot_Base.fold_left
      (fun out1 x ->
         if
           FStar_List_Tot_Base.existsb
             (fun y -> FStar_Class_Eq_Raw.op_Equals (ord_eq uu___) x y) out1
         then out1
         else x :: out1) [] xs in
  FStar_List_Tot_Base.rev out
let rec insert_nodup : 'a . 'a ord -> 'a -> 'a Prims.list -> 'a Prims.list =
  fun uu___ x xs ->
    match xs with
    | [] -> [x]
    | y::ys ->
        (match cmp uu___ x y with
         | FStar_Order.Eq -> xs
         | FStar_Order.Lt -> x :: xs
         | FStar_Order.Gt -> y :: (insert_nodup uu___ x ys))
let rec sort_dedup : 'a . 'a ord -> 'a Prims.list -> 'a Prims.list =
  fun uu___ xs ->
    match xs with
    | [] -> []
    | x::xs1 -> insert_nodup uu___ x (sort_dedup uu___ xs1)
let ord_list_diff (uu___ : 'a ord) (xs : 'a Prims.list) (ys : 'a Prims.list)
  : ('a Prims.list * 'a Prims.list)=
  let xs1 = sort_dedup uu___ xs in
  let ys1 = sort_dedup uu___ ys in
  let rec go xd yd xs2 ys2 =
    match (xs2, ys2) with
    | (x::xs3, y::ys3) ->
        (match cmp uu___ x y with
         | FStar_Order.Lt -> go (x :: xd) yd xs3 (y :: ys3)
         | FStar_Order.Eq -> go xd yd xs3 ys3
         | FStar_Order.Gt -> go xd (y :: yd) (x :: xs3) ys3)
    | (xs3, ys3) ->
        ((FStar_List_Tot_Base.rev_acc xd xs3),
          (FStar_List_Tot_Base.rev_acc yd ys3)) in
  go [] [] xs1 ys1
let ord_int : Prims.int ord=
  { super = FStar_Class_Eq_Raw.int_has_eq; cmp = FStar_Order.compare_int }
let ord_unit : unit ord=
  {
    super = FStar_Class_Eq_Raw.unit_has_eq;
    cmp = (fun uu___ uu___1 -> FStar_Order.Eq)
  }
let ord_string : Prims.string ord=
  {
    super = FStar_Class_Eq_Raw.string_has_eq;
    cmp = (fun x y -> FStar_Order.order_from_int (FStar_String.compare x y))
  }
let ord_option (d : 'a ord) : 'a FStar_Pervasives_Native.option ord=
  {
    super = (FStar_Class_Eq_Raw.eq_option (ord_eq d));
    cmp =
      (fun x y ->
         match (x, y) with
         | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) ->
             FStar_Order.Eq
         | (FStar_Pervasives_Native.Some uu___, FStar_Pervasives_Native.None)
             -> FStar_Order.Gt
         | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some uu___)
             -> FStar_Order.Lt
         | (FStar_Pervasives_Native.Some x1, FStar_Pervasives_Native.Some y1)
             -> cmp d x1 y1)
  }
let ord_list (d : 'a ord) : 'a Prims.list ord=
  {
    super = (FStar_Class_Eq_Raw.eq_list (ord_eq d));
    cmp = (fun l1 l2 -> FStar_Order.compare_list l1 l2 (cmp d))
  }
let ord_either (d1 : 'a ord) (d2 : 'b ord) :
  ('a, 'b) FStar_Pervasives.either ord=
  {
    super = (FStar_Class_Eq_Raw.eq_either (ord_eq d1) (ord_eq d2));
    cmp =
      (fun x y ->
         match (x, y) with
         | (FStar_Pervasives.Inl uu___, FStar_Pervasives.Inr uu___1) ->
             FStar_Order.Lt
         | (FStar_Pervasives.Inr uu___, FStar_Pervasives.Inl uu___1) ->
             FStar_Order.Gt
         | (FStar_Pervasives.Inl x1, FStar_Pervasives.Inl y1) -> cmp d1 x1 y1
         | (FStar_Pervasives.Inr x1, FStar_Pervasives.Inr y1) -> cmp d2 x1 y1)
  }
let ord_tuple2 (d1 : 'a ord) (d2 : 'b ord) : ('a * 'b) ord=
  {
    super = (FStar_Class_Eq_Raw.eq_pair (ord_eq d1) (ord_eq d2));
    cmp =
      (fun uu___ uu___1 ->
         match (uu___, uu___1) with
         | ((x1, x2), (y1, y2)) ->
             FStar_Order.lex (cmp d1 x1 y1) (fun uu___2 -> cmp d2 x2 y2))
  }
