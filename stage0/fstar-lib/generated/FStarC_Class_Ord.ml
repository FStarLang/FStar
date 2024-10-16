open Prims
type 'a ord =
  {
  super: 'a FStarC_Class_Deq.deq ;
  cmp: 'a -> 'a -> FStarC_Compiler_Order.order }
let __proj__Mkord__item__super : 'a . 'a ord -> 'a FStarC_Class_Deq.deq =
  fun projectee -> match projectee with | { super; cmp;_} -> super
let __proj__Mkord__item__cmp :
  'a . 'a ord -> 'a -> 'a -> FStarC_Compiler_Order.order =
  fun projectee -> match projectee with | { super; cmp;_} -> cmp
let super : 'a . 'a ord -> 'a FStarC_Class_Deq.deq =
  fun projectee -> match projectee with | { super = super1; cmp;_} -> super1
let cmp : 'a . 'a ord -> 'a -> 'a -> FStarC_Compiler_Order.order =
  fun projectee ->
    match projectee with | { super = super1; cmp = cmp1;_} -> cmp1
let op_Less_Question : 'a . 'a ord -> 'a -> 'a -> Prims.bool =
  fun uu___ ->
    fun x ->
      fun y ->
        let uu___1 = cmp uu___ x y in uu___1 = FStarC_Compiler_Order.Lt
let op_Less_Equals_Question : 'a . 'a ord -> 'a -> 'a -> Prims.bool =
  fun uu___ ->
    fun x ->
      fun y ->
        let uu___1 = cmp uu___ x y in uu___1 <> FStarC_Compiler_Order.Gt
let op_Greater_Question : 'a . 'a ord -> 'a -> 'a -> Prims.bool =
  fun uu___ ->
    fun x ->
      fun y ->
        let uu___1 = cmp uu___ x y in uu___1 = FStarC_Compiler_Order.Gt
let op_Greater_Equals_Question : 'a . 'a ord -> 'a -> 'a -> Prims.bool =
  fun uu___ ->
    fun x ->
      fun y ->
        let uu___1 = cmp uu___ x y in uu___1 <> FStarC_Compiler_Order.Lt
let min : 'a . 'a ord -> 'a -> 'a -> 'a =
  fun uu___ ->
    fun x ->
      fun y ->
        let uu___1 = op_Less_Equals_Question uu___ x y in
        if uu___1 then x else y
let max : 'a . 'a ord -> 'a -> 'a -> 'a =
  fun uu___ ->
    fun x ->
      fun y ->
        let uu___1 = op_Greater_Equals_Question uu___ x y in
        if uu___1 then x else y
let ord_eq : 'a . 'a ord -> 'a FStarC_Class_Deq.deq = fun d -> d.super
let rec sort : 'a . 'a ord -> 'a Prims.list -> 'a Prims.list =
  fun uu___ ->
    fun xs ->
      let rec insert x xs1 =
        match xs1 with
        | [] -> [x]
        | y::ys ->
            let uu___1 = op_Less_Equals_Question uu___ x y in
            if uu___1
            then x :: y :: ys
            else (let uu___3 = insert x ys in y :: uu___3) in
      match xs with
      | [] -> []
      | x::xs1 -> let uu___1 = sort uu___ xs1 in insert x uu___1
let dedup : 'a . 'a ord -> 'a Prims.list -> 'a Prims.list =
  fun uu___ ->
    fun xs ->
      let out =
        FStarC_Compiler_List.fold_left
          (fun out1 ->
             fun x ->
               let uu___1 =
                 FStarC_Compiler_List.existsb
                   (fun y ->
                      FStarC_Class_Deq.op_Equals_Question (ord_eq uu___) x y)
                   out1 in
               if uu___1 then out1 else x :: out1) [] xs in
      FStarC_Compiler_List.rev out
let rec sort_dedup : 'a . 'a ord -> 'a Prims.list -> 'a Prims.list =
  fun uu___ ->
    fun xs ->
      let rec insert x xs1 =
        match xs1 with
        | [] -> [x]
        | y::ys ->
            let uu___1 = cmp uu___ x y in
            (match uu___1 with
             | FStarC_Compiler_Order.Eq -> ys
             | FStarC_Compiler_Order.Lt -> x :: y :: ys
             | FStarC_Compiler_Order.Gt ->
                 let uu___2 = insert x ys in y :: uu___2) in
      match xs with
      | [] -> []
      | x::xs1 -> let uu___1 = sort_dedup uu___ xs1 in insert x uu___1
let ord_list_diff :
  'a .
    'a ord ->
      'a Prims.list -> 'a Prims.list -> ('a Prims.list * 'a Prims.list)
  =
  fun uu___ ->
    fun xs ->
      fun ys ->
        let xs1 = sort_dedup uu___ xs in
        let ys1 = sort_dedup uu___ ys in
        let rec go uu___1 xs2 ys2 =
          match uu___1 with
          | (xd, yd) ->
              (match (xs2, ys2) with
               | (x::xs3, y::ys3) ->
                   let uu___2 = cmp uu___ x y in
                   (match uu___2 with
                    | FStarC_Compiler_Order.Lt ->
                        go ((x :: xd), yd) xs3 (y :: ys3)
                    | FStarC_Compiler_Order.Eq -> go (xd, yd) xs3 ys3
                    | FStarC_Compiler_Order.Gt ->
                        go (xd, (y :: yd)) (x :: xs3) ys3)
               | (xs3, ys3) ->
                   ((FStarC_Compiler_List.rev_append xd xs3),
                     (FStarC_Compiler_List.rev_append yd ys3))) in
        go ([], []) xs1 ys1
let (ord_int : Prims.int ord) =
  { super = FStarC_Class_Deq.deq_int; cmp = FStarC_Compiler_Order.compare_int
  }
let (ord_bool : Prims.bool ord) =
  {
    super = FStarC_Class_Deq.deq_bool;
    cmp = FStarC_Compiler_Order.compare_bool
  }
let (ord_unit : unit ord) =
  {
    super = FStarC_Class_Deq.deq_unit;
    cmp = (fun uu___ -> fun uu___1 -> FStarC_Compiler_Order.Eq)
  }
let (ord_string : Prims.string ord) =
  {
    super = FStarC_Class_Deq.deq_string;
    cmp =
      (fun x ->
         fun y ->
           FStarC_Compiler_Order.order_from_int
             (FStarC_Compiler_String.compare x y))
  }
let ord_option : 'a . 'a ord -> 'a FStar_Pervasives_Native.option ord =
  fun d ->
    {
      super = (FStarC_Class_Deq.deq_option (ord_eq d));
      cmp =
        (fun x ->
           fun y ->
             match (x, y) with
             | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
                 -> FStarC_Compiler_Order.Eq
             | (FStar_Pervasives_Native.Some uu___,
                FStar_Pervasives_Native.None) -> FStarC_Compiler_Order.Gt
             | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some
                uu___) -> FStarC_Compiler_Order.Lt
             | (FStar_Pervasives_Native.Some x1, FStar_Pervasives_Native.Some
                y1) -> cmp d x1 y1)
    }
let ord_list : 'a . 'a ord -> 'a Prims.list ord =
  fun d ->
    {
      super = (FStarC_Class_Deq.deq_list (ord_eq d));
      cmp =
        (fun l1 -> fun l2 -> FStarC_Compiler_Order.compare_list l1 l2 (cmp d))
    }
let ord_either :
  'a 'b . 'a ord -> 'b ord -> ('a, 'b) FStar_Pervasives.either ord =
  fun d1 ->
    fun d2 ->
      {
        super = (FStarC_Class_Deq.deq_either (ord_eq d1) (ord_eq d2));
        cmp =
          (fun x ->
             fun y ->
               match (x, y) with
               | (FStar_Pervasives.Inl uu___, FStar_Pervasives.Inr uu___1) ->
                   FStarC_Compiler_Order.Lt
               | (FStar_Pervasives.Inr uu___, FStar_Pervasives.Inl uu___1) ->
                   FStarC_Compiler_Order.Gt
               | (FStar_Pervasives.Inl x1, FStar_Pervasives.Inl y1) ->
                   cmp d1 x1 y1
               | (FStar_Pervasives.Inr x1, FStar_Pervasives.Inr y1) ->
                   cmp d2 x1 y1)
      }
let ord_tuple2 : 'a 'b . 'a ord -> 'b ord -> ('a * 'b) ord =
  fun d1 ->
    fun d2 ->
      {
        super = (FStarC_Class_Deq.deq_tuple2 (ord_eq d1) (ord_eq d2));
        cmp =
          (fun uu___ ->
             fun uu___1 ->
               match (uu___, uu___1) with
               | ((x1, x2), (y1, y2)) ->
                   let uu___2 = cmp d1 x1 y1 in
                   FStarC_Compiler_Order.lex uu___2
                     (fun uu___3 -> cmp d2 x2 y2))
      }
let ord_tuple3 : 'a 'b 'c . 'a ord -> 'b ord -> 'c ord -> ('a * 'b * 'c) ord
  =
  fun d1 ->
    fun d2 ->
      fun d3 ->
        {
          super =
            (FStarC_Class_Deq.deq_tuple3 (ord_eq d1) (ord_eq d2) (ord_eq d3));
          cmp =
            (fun uu___ ->
               fun uu___1 ->
                 match (uu___, uu___1) with
                 | ((x1, x2, x3), (y1, y2, y3)) ->
                     let uu___2 = cmp d1 x1 y1 in
                     FStarC_Compiler_Order.lex uu___2
                       (fun uu___3 ->
                          let uu___4 = cmp d2 x2 y2 in
                          FStarC_Compiler_Order.lex uu___4
                            (fun uu___5 -> cmp d3 x3 y3)))
        }
let ord_tuple4 :
  'a 'b 'c 'd .
    'a ord -> 'b ord -> 'c ord -> 'd ord -> ('a * 'b * 'c * 'd) ord
  =
  fun d1 ->
    fun d2 ->
      fun d3 ->
        fun d4 ->
          {
            super =
              (FStarC_Class_Deq.deq_tuple4 (ord_eq d1) (ord_eq d2)
                 (ord_eq d3) (ord_eq d4));
            cmp =
              (fun uu___ ->
                 fun uu___1 ->
                   match (uu___, uu___1) with
                   | ((x1, x2, x3, x4), (y1, y2, y3, y4)) ->
                       let uu___2 = cmp d1 x1 y1 in
                       FStarC_Compiler_Order.lex uu___2
                         (fun uu___3 ->
                            let uu___4 = cmp d2 x2 y2 in
                            FStarC_Compiler_Order.lex uu___4
                              (fun uu___5 ->
                                 let uu___6 = cmp d3 x3 y3 in
                                 FStarC_Compiler_Order.lex uu___6
                                   (fun uu___7 -> cmp d4 x4 y4))))
          }
let ord_tuple5 :
  'a 'b 'c 'd 'e .
    'a ord ->
      'b ord -> 'c ord -> 'd ord -> 'e ord -> ('a * 'b * 'c * 'd * 'e) ord
  =
  fun d1 ->
    fun d2 ->
      fun d3 ->
        fun d4 ->
          fun d5 ->
            {
              super =
                (FStarC_Class_Deq.deq_tuple5 (ord_eq d1) (ord_eq d2)
                   (ord_eq d3) (ord_eq d4) (ord_eq d5));
              cmp =
                (fun uu___ ->
                   fun uu___1 ->
                     match (uu___, uu___1) with
                     | ((x1, x2, x3, x4, x5), (y1, y2, y3, y4, y5)) ->
                         let uu___2 = cmp d1 x1 y1 in
                         FStarC_Compiler_Order.lex uu___2
                           (fun uu___3 ->
                              let uu___4 = cmp d2 x2 y2 in
                              FStarC_Compiler_Order.lex uu___4
                                (fun uu___5 ->
                                   let uu___6 = cmp d3 x3 y3 in
                                   FStarC_Compiler_Order.lex uu___6
                                     (fun uu___7 ->
                                        let uu___8 = cmp d4 x4 y4 in
                                        FStarC_Compiler_Order.lex uu___8
                                          (fun uu___9 -> cmp d5 x5 y5)))))
            }
let ord_tuple6 :
  'a 'b 'c 'd 'e 'f .
    'a ord ->
      'b ord ->
        'c ord ->
          'd ord -> 'e ord -> 'f ord -> ('a * 'b * 'c * 'd * 'e * 'f) ord
  =
  fun d1 ->
    fun d2 ->
      fun d3 ->
        fun d4 ->
          fun d5 ->
            fun d6 ->
              {
                super =
                  (FStarC_Class_Deq.deq_tuple6 (ord_eq d1) (ord_eq d2)
                     (ord_eq d3) (ord_eq d4) (ord_eq d5) (ord_eq d6));
                cmp =
                  (fun uu___ ->
                     fun uu___1 ->
                       match (uu___, uu___1) with
                       | ((x1, x2, x3, x4, x5, x6), (y1, y2, y3, y4, y5, y6))
                           ->
                           let uu___2 = cmp d1 x1 y1 in
                           FStarC_Compiler_Order.lex uu___2
                             (fun uu___3 ->
                                let uu___4 = cmp d2 x2 y2 in
                                FStarC_Compiler_Order.lex uu___4
                                  (fun uu___5 ->
                                     let uu___6 = cmp d3 x3 y3 in
                                     FStarC_Compiler_Order.lex uu___6
                                       (fun uu___7 ->
                                          let uu___8 = cmp d4 x4 y4 in
                                          FStarC_Compiler_Order.lex uu___8
                                            (fun uu___9 ->
                                               let uu___10 = cmp d5 x5 y5 in
                                               FStarC_Compiler_Order.lex
                                                 uu___10
                                                 (fun uu___11 -> cmp d6 x6 y6))))))
              }