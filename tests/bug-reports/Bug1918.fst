module Bug1918

class mon = {
  t : Type;
  comp : t -> t -> t;
}

[@@expect_failure [66]]
let (++) (a:_) (b:_) = comp a b
