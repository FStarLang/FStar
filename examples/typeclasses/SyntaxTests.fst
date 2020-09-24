module SyntaxTests

open Add

let foo  (#a:Type) {|additive a|} (x y : a) : Tot a = plus x y

let foo2 (#a:Type) {|additive a|} (x y : a) : Tot a = plus x y

let foo3 (#a:Type) {|additive a|} (x y : a) : Tot a = plus x y

let foo4 (#a:Type) {|additive a|} (x y : a) : Tot a = plus x y
let foo5 (#a:Type) {|additive a|} (x y : a) : Tot a = plus x y
