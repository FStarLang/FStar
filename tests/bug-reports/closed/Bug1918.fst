module Bug1918

class mon = {
  t : Type0;
  comp : t -> t -> t;
}

let comp1 (_:mon) (x:t) (y:t) : t = comp x y

[@@expect_failure [228]]
let comp2 (x:t) (y:t) : t = comp x y
