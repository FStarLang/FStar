module FStarC.Class.PP

open FStarC
open FStarC.Effect
open FStarC.Pprint
open FStarC.Class.Show

let gparens a = group (nest 2 (parens a))
let gbrackets a = group (nest 2 (brackets a))

instance pp_unit = {
   pp = (fun _ -> doc_of_string "()");
}

instance pp_int = {
   pp = (fun x -> doc_of_string (show x));
}

instance pp_bool = {
   pp = doc_of_bool;
}

instance pp_list (a:Type) (_ : pretty a) : Tot (pretty (list a)) = {
  pp = (fun l -> gbrackets (flow_map (semi ^^ break_ 1) pp l));
}

instance pp_option (a:Type) (_ : pretty a) : Tot (pretty (option a)) = {
  pp = (fun o -> match o with
                 | Some v -> group (nest 2 (doc_of_string "Some" ^/^ pp v))
                 | None -> doc_of_string "None");
}

instance pp_either (_ : pretty 'a) (_ : pretty 'b) = {
  pp = (fun e -> group (nest 2 (match e with
                 | Inl x -> doc_of_string "Inl" ^/^ pp x
                 | Inr x -> doc_of_string "Inr" ^/^ pp x)));
}

let comma_space = comma ^^ break_ 1

instance pp_tuple2
   (_ : pretty 'a)
   (_ : pretty 'b)
= {
  pp = (fun (x1, x2) ->
            gparens (separate comma_space [pp x1; pp x2]));
}

instance pp_tuple3
   (_ : pretty 'a)
   (_ : pretty 'b)
   (_ : pretty 'c)
= {
  pp = (fun (x1, x2, x3) ->
            gparens (separate comma_space [pp x1; pp x2; pp x3]));
}

instance pp_tuple4
   (_ : pretty 'a)
   (_ : pretty 'b)
   (_ : pretty 'c)
   (_ : pretty 'd)
= {
  pp = (fun (x1, x2, x3, x4) ->
            gparens (separate comma_space [pp x1; pp x2; pp x3; pp x4]));
}

instance pp_tuple5
   (_ : pretty 'a)
   (_ : pretty 'b)
   (_ : pretty 'c)
   (_ : pretty 'd)
   (_ : pretty 'e)
= {
  pp = (fun (x1, x2, x3, x4, x5) ->
            gparens (separate comma_space [pp x1; pp x2; pp x3; pp x4; pp x5]));
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
            gparens (separate comma_space [pp x1; pp x2; pp x3; pp x4; pp x5; pp x6]));
}

let pretty_from_showable (#a:Type) {| _ : Class.Show.showable a |} : Tot (pretty a) = {
   pp = (fun x -> arbitrary_string (Class.Show.show x));
}

let showable_from_pretty (#a:Type) {| _ : pretty a |} : Tot (Class.Show.showable a) = {
   show = (fun x -> render (pp x));
}
