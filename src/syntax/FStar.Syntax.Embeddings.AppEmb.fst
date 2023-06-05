module FStar.Syntax.Embeddings.AppEmb

open FStar.Syntax.Syntax
open FStar.Syntax.Embeddings.Base

type appemb 'a =
  args -> option ('a & args)

let one (e : embedding 'a) : appemb 'a =
  fun args ->
    match args with
    | (t,_)::xs ->
      match try_unembed e t id_norm_cb with
      | None -> None
      | Some v -> Some (v, xs)

let (let?) o f = match o with | None -> None | Some v -> f v

val (<*>) : appemb ('a -> 'b) -> appemb 'a -> appemb 'b
let (<*>) u1 u2 =
  fun args ->
    let? f, args' = u1 args in
    let? v, args'' = u2 args' in
    Some (f v, args'')

val (<**>) : appemb ('a -> 'b) -> embedding 'a -> appemb 'b
let (<**>) u1 u2 = u1 <*> one u2

let pure (x : 'a) : appemb 'a =
  fun args -> Some (x, args)

val (<$>) : ('a -> 'b) -> appemb 'a -> appemb 'b
let (<$>) u1 u2 = pure u1 <*> u2

val (<$$>) : ('a -> 'b) -> embedding 'a -> appemb 'b
let (<$$>) u1 u2 = pure u1 <*> one u2

val run : args -> appemb 'a -> option 'a
let run args u =
  match u args with
  | Some (r, []) -> Some r
  | _ -> None

val wrap : (term -> option 'a) -> appemb 'a
let wrap f =
  fun args ->
    match args with
    | (t,_)::xs ->
      match f t with
      | None -> None
      | Some v -> Some (v, xs)
