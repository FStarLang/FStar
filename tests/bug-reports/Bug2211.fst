module Bug2211
assume val comba (ret:Type u#a) : Type u#(max a 1)
assume val f: #ret:Type u#a -> list u#(max a 1) (comba u#a ret) -> list u#a ret
assume val x: list u#1 (comba u#0 int)
let t = f x
