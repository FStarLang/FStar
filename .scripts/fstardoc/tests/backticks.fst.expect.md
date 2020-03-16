#### op_Multiply

Integer multiplication, no special symbol. See FStar.Mul

```fstar
[@smt_theory_symbol]
assume
val op_Multiply           : int -> int -> Tot int
```

#### rec

`pow2 x` is `2^x`:

```fstar
let rec pow2 (x:nat) : Tot pos =
  match x with
  | 0  -> 1
  | _  -> 2 `op_Multiply` (pow2 (x-1))
```
