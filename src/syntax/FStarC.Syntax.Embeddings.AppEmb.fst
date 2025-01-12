module FStarC.Syntax.Embeddings.AppEmb

open FStarC.Syntax.Syntax
open FStarC.Syntax.Embeddings.Base

let one (e : embedding 'a) : appemb 'a =
  fun args ->
    match args with
    | (t,_)::xs ->
      match try_unembed t id_norm_cb with
      | None -> None
      | Some v -> Some (v, xs)

let (let?) o f = match o with | None -> None | Some v -> f v

let (<*>) u1 u2 =
  fun args ->
    let? f, args' = u1 args in
    let? v, args'' = u2 args' in
    Some (f v, args'')

let (<**>) u1 u2 = u1 <*> one u2

let pure (x : 'a) : appemb 'a =
  fun args -> Some (x, args)

let (<$>) u1 u2 = pure u1 <*> u2

let (<$$>) u1 u2 = pure u1 <*> one u2

let run args u =
  match u args with
  | Some (r, []) -> Some r
  | _ -> None

let wrap f =
  fun args ->
    match args with
    | (t,_)::xs ->
      match f t with
      | None -> None
      | Some v -> Some (v, xs)
