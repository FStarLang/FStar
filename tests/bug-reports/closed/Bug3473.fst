module Bug3473
let rec uhoh t : Dv t = uhoh t

let foo (x: option nat) : Dv string =
  uhoh unit; "foo"