module Bug2605

open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect
open Steel.ST.Util
open Steel.ST.Coercions

assume val phi : int -> Type0

assume
val f3 (i:int{phi i})
  : STT unit emp (fun _ -> emp)

let g3 (#a:Type) (i:int)
  : Steel unit emp (λ _ → emp)
      (requires λ _ → phi i)
      (ensures λ _ _ _ → ⊤)
  = f3 i
