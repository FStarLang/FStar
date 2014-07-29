
module JSUnit.Records

type rt = {
 test : int->int->int;
 other : int * int;
 next: option<rt> ;
}

let r = {
 test = (fun x y->x+y);
 other = (41,1);
 next = None;
}

let s = r.test (fst r.other) (snd r.other)

let t = function
 | {next = Some(x)} -> x.test 1 2
 | {other = (_, 1)} -> 1
 | _ -> 2

type tr = {
 entry1: int;
 entry2: list<int>;
 entry3: option<tr>;
}

let tt =
 let x = {entry1=0; entry2 = [1;2]; entry3 = None}
 in match x with
 | {entry3=Some(t)} -> t.entry2
 | {entry2=1::r} -> r
 | _ -> []

let nil =
        JS.utest "PropRead" s 42 ;
        JS.utest "RecPatternMatch" (t r) 1;
        JS.utest "RecSubtyping" tt ([2])

