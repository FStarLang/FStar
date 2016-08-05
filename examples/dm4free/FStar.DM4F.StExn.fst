module FStar.DM4F.StExn

let stexn a =
  int -> M (option a * int)

let return (a: Type) (x: a): stexn a =
  fun s ->
    Some x, s

let bind (a: Type) (b: Type) (f: stexn a) (g: a -> stexn b): stexn b =
  fun s0 ->
    let ex, s1 = f s0 in
    match ex with
    | None -> None, s1
    | Some r -> g r s1

reifiable reflectable new_effect_for_free {
  STEXN: a:Type -> Effect with
    repr = stexn;
    return = return;
    bind = bind
}
