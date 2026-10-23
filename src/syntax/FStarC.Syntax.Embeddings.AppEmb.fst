module FStarC.Syntax.Embeddings.AppEmb

open FStarC.Effect
open FStarC.Syntax.Syntax
open FStarC.Syntax.Embeddings.Base

let one (e : embedding 'a) : appemb 'a =
  fun args ->
    match args with
    | (t,_)::xs ->
      match try_unembed t id_norm_cb with
      | None -> None
      | Some v -> Some (v, xs)

[@@FStar.Attributes.custard_inline]
let (<*>) u1 u2 =
  fun args ->
    let? f, args' = u1 args in
    let? v, args'' = u2 args' in
    let r = f v in
    Some (r, args'')

[@@FStar.Attributes.custard_inline]
let (<**>) u1 u2 = u1 <*> one u2

[@@FStar.Attributes.custard_inline]
let pure (x : 'a) : appemb 'a =
  fun args -> Some (x, args)

[@@FStar.Attributes.custard_inline]
let (<$>) u1 u2 = pure u1 <*> u2

[@@FStar.Attributes.custard_inline]
let (<$$>) u1 u2 = pure u1 <*> one u2

[@@FStar.Attributes.custard_inline]
let run args u : ML (option _) =
  match u args with
  | Some (r, []) -> Some r
  | _ -> None

let wrap (f : _ -> ML (option _)) : appemb _ =
  fun args ->
    match args with
    | (t,_)::xs ->
      match f t with
      | None -> None
      | Some v -> Some (v, xs)
