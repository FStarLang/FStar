module Bug749

open FStar.List.Tot

assume type symbol

val code_length : ss:(list (symbol * pos)) -> cs:(list nat) -> Pure nat
  (requires (List.Tot.length cs == List.Tot.length ss))
  (ensures (fun _ -> True))
let code_length ss cs =
  fold_left2 (fun (a:nat) (sw:symbol*pos) c ->
              let (s,w) = sw in a + w `op_Multiply` c) 0 ss cs
