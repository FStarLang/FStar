module FStarC.Syntax.Embeddings.AppEmb

open FStarC.Syntax.Syntax
open FStarC.Syntax.Embeddings.Base

type appemb 'a =
  args -> option ('a & args)

let (let?) o f = match o with | None -> None | Some v -> f v

val (<*>) : appemb ('a -> 'b) -> appemb 'a -> appemb 'b
val (<**>) : appemb ('a -> 'b) -> embedding 'a -> appemb 'b

val pure (x : 'a) : appemb 'a

val (<$>) : ('a -> 'b) -> appemb 'a -> appemb 'b

val (<$$>) : ('a -> 'b) -> embedding 'a -> appemb 'b

val run : args -> appemb 'a -> option 'a

val wrap : (term -> option 'a) -> appemb 'a
