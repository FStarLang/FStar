module Bug3115

class eq a = {
  (=?) : a -> a -> bool;
}

[@@expect_failure [228]]
let test x (y z : int) = y =? z
