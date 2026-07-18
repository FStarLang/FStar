module Bug2074

let bad : (a : Type u#aa) -> (l : list int) -> unit = fun _ _ -> ()

type repr2 (a:Type u#aa) (labs : list int) : Type u#aa = a

type repr3 (a:Type u#aa) (s0 s1 : Type) : Type u#aa =
  s0 -> Tot (option a & s1)
