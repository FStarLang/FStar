module Bug2167

[@@expect_failure [12]]
type t (a:int) (u:unit) =
  | N : t a
  
[@@expect_failure [173]]
type t (a:int) =
  | N : t a ()

[@@expect_failure [12]]
type t (a:int) : unit -> Type =
  | N : t a


[@@expect_failure [189]]
type t2 (u:unit) =
  | N : t2

[@@expect_failure [71]]
type t =
  | N : t ()

[@@expect_failure [189]]
type t : unit -> Type =
  | N : t
