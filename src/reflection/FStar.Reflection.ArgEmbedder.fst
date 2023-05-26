module FStar.Reflection.ArgEmbedder

open FStar.Syntax.Syntax
open FStar.Syntax.Embeddings

(* Copied from reflection embeddings. *)
let mk_emb f g t =
    mk_emb (fun x r _topt _norm -> f r x)
           (fun x w _norm -> g w x)
           (term_as_fv t)
let embed e r x = embed e x r None id_norm_cb
let unembed' w e x = unembed e x w id_norm_cb

type arg_unembedder 'a = args -> option ('a & args)

let one (e : embedding 'a) : arg_unembedder 'a =
  fun args ->
    match args with
    | (t,_)::xs ->
      match unembed' false e t with
      | None -> None
      | Some v -> Some (v, xs)

let (let?) o f = match o with | None -> None | Some v -> f v

val (<*>) : arg_unembedder ('a -> 'b) -> arg_unembedder 'a -> arg_unembedder 'b
let (<*>) u1 u2 =
  fun args ->
    let? f, args' = u1 args in
    let? v, args'' = u2 args' in
    Some (f v, args'')

val (<**>) : arg_unembedder ('a -> 'b) -> embedding 'a -> arg_unembedder 'b
let (<**>) u1 u2 = u1 <*> one u2

let pure (x : 'a) : arg_unembedder 'a =
  fun args -> Some (x, args)

val (<$>) : ('a -> 'b) -> arg_unembedder 'a -> arg_unembedder 'b
let (<$>) u1 u2 = pure u1 <*> u2

val (<$$>) : ('a -> 'b) -> embedding 'a -> arg_unembedder 'b
let (<$$>) u1 u2 = pure u1 <*> one u2

val run : args -> arg_unembedder 'a -> option 'a
let run args u =
  match u args with
  | Some (r, []) -> Some r
  | _ -> None
