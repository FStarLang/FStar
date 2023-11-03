module RecordFields

type r = {a:int; b:int; c:int}

let t1 : r = {a=1; b=2; c=3}

[@@expect_failure [118]]
let t2 : r = {a=1; b=2; c=3; d=4}

[@@expect_failure [118]]
let t3 : r = {a=1; b=2}

[@@expect_failure [118]]
let t4 : r = {a=1; b=2; d=4}
