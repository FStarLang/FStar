open Fstarcompiler
open Prims
type order =
  | Lt 
  | Eq 
  | Gt 
let rec __knot_e_order _ =
  Fstarcompiler.FStarC_Syntax_Embeddings_Base.mk_extracted_embedding
    "FStar.Order.order"
    (fun tm_0 ->
       match tm_0 with
       | ("FStar.Order.Lt", []) -> FStar_Pervasives_Native.Some Lt
       | ("FStar.Order.Eq", []) -> FStar_Pervasives_Native.Some Eq
       | ("FStar.Order.Gt", []) -> FStar_Pervasives_Native.Some Gt
       | _ -> FStar_Pervasives_Native.None)
    (fun tm_4 ->
       match tm_4 with
       | Lt ->
           Fstarcompiler.FStarC_Syntax_Util.mk_app
             (Fstarcompiler.FStarC_Syntax_Syntax.tdataconstr
                (Fstarcompiler.FStarC_Ident.lid_of_str "FStar.Order.Lt")) []
       | Eq ->
           Fstarcompiler.FStarC_Syntax_Util.mk_app
             (Fstarcompiler.FStarC_Syntax_Syntax.tdataconstr
                (Fstarcompiler.FStarC_Ident.lid_of_str "FStar.Order.Eq")) []
       | Gt ->
           Fstarcompiler.FStarC_Syntax_Util.mk_app
             (Fstarcompiler.FStarC_Syntax_Syntax.tdataconstr
                (Fstarcompiler.FStarC_Ident.lid_of_str "FStar.Order.Gt")) [])
let e_order = __knot_e_order ()
let uu___is_Lt (projectee : order) : Prims.bool=
  match projectee with | Lt -> true | uu___ -> false
let uu___is_Eq (projectee : order) : Prims.bool=
  match projectee with | Eq -> true | uu___ -> false
let uu___is_Gt (projectee : order) : Prims.bool=
  match projectee with | Gt -> true | uu___ -> false
let ge (o : order) : Prims.bool= o <> Lt
let le (o : order) : Prims.bool= o <> Gt
let ne (o : order) : Prims.bool= o <> Eq
let gt (o : order) : Prims.bool= o = Gt
let lt (o : order) : Prims.bool= o = Lt
let eq (o : order) : Prims.bool= o = Eq
let lex (o1 : order) (o2 : unit -> order) : order=
  match o1 with | Lt -> Lt | Eq -> o2 () | Gt -> Gt
let order_from_int (i : Prims.int) : order=
  if i < Prims.int_zero then Lt else if i = Prims.int_zero then Eq else Gt
let int_of_order (uu___ : order) : Prims.int=
  match uu___ with
  | Lt -> (Prims.of_int (-1))
  | Eq -> Prims.int_zero
  | Gt -> Prims.int_one
let compare_int (i : Prims.int) (j : Prims.int) : order=
  order_from_int (i - j)
let rec compare_list :
  'a . 'a Prims.list -> 'a Prims.list -> ('a -> 'a -> order) -> order =
  fun l1 l2 f ->
    match (l1, l2) with
    | ([], []) -> Eq
    | ([], uu___) -> Lt
    | (uu___, []) -> Gt
    | (x::xs, y::ys) -> lex (f x y) (fun uu___ -> compare_list xs ys f)
let compare_option (f : 'a -> 'a -> order)
  (x : 'a FStar_Pervasives_Native.option)
  (y : 'a FStar_Pervasives_Native.option) : order=
  match (x, y) with
  | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) -> Eq
  | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some uu___) -> Lt
  | (FStar_Pervasives_Native.Some uu___, FStar_Pervasives_Native.None) -> Gt
  | (FStar_Pervasives_Native.Some x1, FStar_Pervasives_Native.Some y1) ->
      f x1 y1
