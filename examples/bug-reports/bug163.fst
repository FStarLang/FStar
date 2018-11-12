module Bug163

open FStar.ST

val swap_add_sub : #int:Type -> r1:(ref int) -> r2:(ref int) -> ST unit
      (requires (fun h -> True))
      (ensures (fun h' _ h -> True))
let swap_add_sub #int r1 r2 =
  write r1 (read r1 + read r2);
  write r2 (read r1 - read r2);
  write r1 (read r1 - read r2)
