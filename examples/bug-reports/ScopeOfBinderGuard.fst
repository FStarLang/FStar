module ScopeOfBinderGuard
let t (z:bool) =
  match z with
  | true -> bool
  | false -> unit
let bool_t = t true

[@expect_failure [19]]
let test1 = fun (b:bool_t) (x:unit{eq2 #unit x b}) -> true
[@expect_failure [19]]
let test2 = fun (b:bool) (x:t false{eq2 #bool x b}) -> true
