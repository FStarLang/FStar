
module Test

type rdt =
 | Nothing
 | Something of rdt
 | SomethingElse of rdt * rdt

type rt = {
        test : int->int;
        other : int
}

let x = SomethingElse(Nothing, Something(Nothing))
let l = [1; 2]
let p = ("t", 0)
let r = {
 test = (fun x->x+1);
 other = 1;
}
let s = r.test (snd p)

val fib : int -> int
let rec fib n = match n with
 | 0 -> 1 | 1 -> 1
 | _ -> (fib (n-1)) + (fib (n-2))

