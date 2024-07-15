module UnresolvedFields

type t = {
    a:int;
    b:int;
}

[@@expect_failure]
let test0 = {
    c=2;
    a=1;
    b=3;
}

[@@expect_failure]
let test1 : t = {
    c=2;
    a=1;
    b=3;
}

[@@expect_failure]
let test2 : t = {
    a=1;
    b=3;
    c=2;
}