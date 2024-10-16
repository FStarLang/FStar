module FStar.Class.Embeddable

open FStar.Reflection.V2

instance embeddable_string : embeddable string = {
  embed = (fun s -> pack_ln (Tv_Const (C_String s)));
  typ = (`string);
}

instance embeddable_bool : embeddable bool = {
  embed = (fun b -> pack_ln (Tv_Const (if b then C_True else C_False)));
  typ = (`bool);
}

instance embeddable_int : embeddable int = {
  embed = (fun i -> pack_ln (Tv_Const (C_Int i)));
  typ = (`int);
}

let rec e_list #a {| ea : embeddable a |} (xs : list a) : term =
  match xs with
  | [] -> `(Nil #(`# ea.typ))
  | x::xs -> `(Cons #(`#(ea.typ)) (`#(embed x)) (`#(e_list xs)))

instance embeddable_list (a:Type) (ea : embeddable a) : embeddable (list a) = {
  embed = e_list;
  typ = (`list (`#ea.typ));
}
