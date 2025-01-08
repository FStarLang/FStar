open Prims
type order =
  | Lt 
  | Eq 
  | Gt 
let rec __knot_e_order _ =
  FStarC_Syntax_Embeddings_Base.mk_extracted_embedding "FStar.Order.order"
    (fun tm_0 ->
       match tm_0 with
       | ("FStar.Order.Lt", []) -> FStar_Pervasives_Native.Some Lt
       | ("FStar.Order.Eq", []) -> FStar_Pervasives_Native.Some Eq
       | ("FStar.Order.Gt", []) -> FStar_Pervasives_Native.Some Gt
       | _ -> FStar_Pervasives_Native.None)
    (fun tm_4 ->
       match tm_4 with
       | Lt ->
           FStarC_Syntax_Util.mk_app
             (FStarC_Syntax_Syntax.tdataconstr
                (FStarC_Ident.lid_of_str "FStar.Order.Lt")) []
       | Eq ->
           FStarC_Syntax_Util.mk_app
             (FStarC_Syntax_Syntax.tdataconstr
                (FStarC_Ident.lid_of_str "FStar.Order.Eq")) []
       | Gt ->
           FStarC_Syntax_Util.mk_app
             (FStarC_Syntax_Syntax.tdataconstr
                (FStarC_Ident.lid_of_str "FStar.Order.Gt")) [])
let e_order = __knot_e_order ()
let (uu___is_Lt : order -> Prims.bool) =
  fun projectee -> match projectee with | Lt -> true | uu___ -> false
let (uu___is_Eq : order -> Prims.bool) =
  fun projectee -> match projectee with | Eq -> true | uu___ -> false
let (uu___is_Gt : order -> Prims.bool) =
  fun projectee -> match projectee with | Gt -> true | uu___ -> false
let (ge : order -> Prims.bool) = fun o -> o <> Lt
let (le : order -> Prims.bool) = fun o -> o <> Gt
let (ne : order -> Prims.bool) = fun o -> o <> Eq
let (gt : order -> Prims.bool) = fun o -> o = Gt
let (lt : order -> Prims.bool) = fun o -> o = Lt
let (eq : order -> Prims.bool) = fun o -> o = Eq
let (lex : order -> (unit -> order) -> order) =
  fun o1 -> fun o2 -> match o1 with | Lt -> Lt | Eq -> o2 () | Gt -> Gt
let (order_from_int : Prims.int -> order) =
  fun i ->
    if i < Prims.int_zero then Lt else if i = Prims.int_zero then Eq else Gt
let (int_of_order : order -> Prims.int) =
  fun uu___ ->
    match uu___ with
    | Lt -> (Prims.of_int (-1))
    | Eq -> Prims.int_zero
    | Gt -> Prims.int_one
let (compare_int : Prims.int -> Prims.int -> order) =
  fun i -> fun j -> order_from_int (i - j)
let rec compare_list :
  'a . 'a Prims.list -> 'a Prims.list -> ('a -> 'a -> order) -> order =
  fun l1 ->
    fun l2 ->
      fun f ->
        match (l1, l2) with
        | ([], []) -> Eq
        | ([], uu___) -> Lt
        | (uu___, []) -> Gt
        | (x::xs, y::ys) -> lex (f x y) (fun uu___ -> compare_list xs ys f)
let compare_option :
  'a .
    ('a -> 'a -> order) ->
      'a FStar_Pervasives_Native.option ->
        'a FStar_Pervasives_Native.option -> order
  =
  fun f ->
    fun x ->
      fun y ->
        match (x, y) with
        | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) -> Eq
        | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some uu___)
            -> Lt
        | (FStar_Pervasives_Native.Some uu___, FStar_Pervasives_Native.None)
            -> Gt
        | (FStar_Pervasives_Native.Some x1, FStar_Pervasives_Native.Some y1)
            -> f x1 y1