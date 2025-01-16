module Bug3644

let t = nat -> nat
let s = nat -> GTot nat

let f : t = (fun n -> n)
let g : s = f

// `g` must not have the type `nat -> GTot nat`
[@@expect_failure [19]]
let _ = assert (has_type g t)
