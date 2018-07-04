module Bug1319e

assume val err (a:Type0) : Type0
assume val return (#a:Type) (x:a) : err a
assume val bind (#a:Type) (#b:Type) (f:err a) (g: a -> Tot (err b)) : Tot (err b)

assume val conv (x:int) : y:nat{y === x} //without the refinement on the result type here everything is fine

[@(expect_failure [54])]
let test (x: err (int * unit)) : Tot (err (nat * unit))
= bind (x) (fun bu ->
  return (conv (fst bu), snd bu))
