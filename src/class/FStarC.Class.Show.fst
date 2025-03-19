module FStarC.Class.Show

open FStarC.Effect

instance showable_unit : showable unit =
{
  show = (fun _ -> "()")
}

instance showable_bool : showable bool =
{
  show = Prims.string_of_bool
}

instance showable_nat : showable nat =
{
  show = Prims.string_of_int
}

instance showable_int : showable int =
{
  show = Prims.string_of_int
}

instance showable_string : showable string =
{
  show = fun x -> "\"" ^ x ^ "\""
}

instance show_list (a:Type) (_ : showable a) : Tot (showable (list a)) = {
  show =
    (fun l ->
      let rec show_list_aux = (fun l ->
        match l with
        | [] -> ""
        | [x] -> show x
        | x::xs -> show x ^ ", " ^ show_list_aux xs
      ) in
      "[" ^ show_list_aux l ^ "]"
    );
}

instance show_option (a:Type) (_ : showable a) : Tot (showable (option a)) = {
  show = (function None -> "None"
                 | Some x -> "Some " ^ show x);
}

instance show_either
   (_ : showable 'a)
   (_ : showable 'b)
= {
  show = (function Inl x -> "Inl " ^ show x
                 | Inr y -> "Inr " ^ show y);
}

instance show_tuple2
   (_ : showable 'a)
   (_ : showable 'b)
= {
  show = (fun (x1, x2) -> "("
                ^ show x1 ^ ", "
                ^ show x2 ^ ")");
}

instance show_tuple3
   (_ : showable 'a)
   (_ : showable 'b)
   (_ : showable 'c)
= {
  show = (fun (x1, x2, x3) -> "("
                ^ show x1 ^ ", "
                ^ show x2 ^ ", "
                ^ show x3 ^ ")");
}

instance show_tuple4
   (_ : showable 'a)
   (_ : showable 'b)
   (_ : showable 'c)
   (_ : showable 'd)
= {
  show = (fun (x1, x2, x3, x4) -> "("
                ^ show x1 ^ ", "
                ^ show x2 ^ ", "
                ^ show x3 ^ ", "
                ^ show x4 ^ ")");
}

instance show_tuple5
   (_ : showable 'a)
   (_ : showable 'b)
   (_ : showable 'c)
   (_ : showable 'd)
   (_ : showable 'e)
= {
  show = (fun (x1, x2, x3, x4, x5) -> "("
                ^ show x1 ^ ", "
                ^ show x2 ^ ", "
                ^ show x3 ^ ", "
                ^ show x4 ^ ", "
                ^ show x5 ^ ")");
}

instance show_tuple6
   (_ : showable 'a)
   (_ : showable 'b)
   (_ : showable 'c)
   (_ : showable 'd)
   (_ : showable 'e)
   (_ : showable 'f)
= {
  show = (fun (x1, x2, x3, x4, x5, x6) -> "("
                ^ show x1 ^ ", "
                ^ show x2 ^ ", "
                ^ show x3 ^ ", "
                ^ show x4 ^ ", "
                ^ show x5 ^ ", "
                ^ show x6 ^ ")");
}
