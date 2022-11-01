module Steel.TypeDictionary

open Steel.Effect.Common
open Steel.Effect
open Steel.Effect.Atomic

val inv : Ghost.erased Steel.Memory.iname

[@@erasable; must_erase_for_extraction]
val token : Type0

[@@noextract_to "krml"]
val type_of_token
  (n: token)
: Tot Type0

val type_of_token_inj
  (#opened: _) (n1 n2: token)
: SteelGhost unit opened
  emp
  (fun _ -> emp)
  (fun _ ->
    type_of_token n1 == type_of_token n2 /\
    Ghost.reveal (mem_inv opened inv) == false
  )
  (fun _ _ _ -> n1 == n2)

val get_token
  (#opened: _)
  (t: Type0)
: SteelGhost token opened
  emp
  (fun _ -> emp)
  (fun _ -> Ghost.reveal (mem_inv opened inv) == false)
  (fun _ n _ -> type_of_token n == t)
