module FStar.Class.PP

open FStar.Compiler.Effect
open FStar.Pprint

instance pp_unit = {
   pp = (fun _ -> doc_of_string "()");
}

instance pp_int = {
   pp = (fun x -> doc_of_string (string_of_int x));
}

instance pp_bool = {
   pp = doc_of_bool;
}

instance pp_list (a:Type) (_ : pretty a) : Tot (pretty (list a)) = {
  pp = (fun l -> brackets (separate_map colon pp l));
}

instance pp_option (a:Type) (_ : pretty a) : Tot (pretty (option a)) = {
  pp = (fun o -> match o with
                 | Some v -> doc_of_string "Some" ^/^ pp v
                 | None -> doc_of_string "None");
}

instance pp_either (_ : pretty 'a) (_ : pretty 'b) = {
  pp = (fun e -> match e with
                 | Inl x -> doc_of_string "Inl" ^/^ pp x
                 | Inr x -> doc_of_string "Inr" ^/^ pp x);
}

instance pp_tuple2
   (_ : pretty 'a)
   (_ : pretty 'b)
= {
  pp = (fun (x1, x2) ->
            parens (separate comma [pp x1; pp x2]));
}

instance pp_tuple3
   (_ : pretty 'a)
   (_ : pretty 'b)
   (_ : pretty 'c)
= {
  pp = (fun (x1, x2, x3) ->
            parens (separate comma [pp x1; pp x2; pp x3]));
}

instance pp_tuple4
   (_ : pretty 'a)
   (_ : pretty 'b)
   (_ : pretty 'c)
   (_ : pretty 'd)
= {
  pp = (fun (x1, x2, x3, x4) ->
            parens (separate comma [pp x1; pp x2; pp x3; pp x4]));
}

instance pp_tuple5
   (_ : pretty 'a)
   (_ : pretty 'b)
   (_ : pretty 'c)
   (_ : pretty 'd)
   (_ : pretty 'e)
= {
  pp = (fun (x1, x2, x3, x4, x5) ->
            parens (separate comma [pp x1; pp x2; pp x3; pp x4; pp x5]));
}

instance pp_tuple6
   (_ : pretty 'a)
   (_ : pretty 'b)
   (_ : pretty 'c)
   (_ : pretty 'd)
   (_ : pretty 'e)
   (_ : pretty 'f)
= {
  pp = (fun (x1, x2, x3, x4, x5, x6) ->
            parens (separate comma [pp x1; pp x2; pp x3; pp x4; pp x5; pp x6]));
}

let from_showable (a:Type) {| _ : Class.Show.showable a |} : Tot (pretty a) = {
   pp = (fun x -> arbitrary_string (Class.Show.show x));
}
