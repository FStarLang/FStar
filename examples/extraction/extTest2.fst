module Test2

open Test1

val mult : a:nnat -> b:nnat -> Tot nnat
let rec mult a b =
match a with
| O -> O
| S a' -> add b (mult a' b)
