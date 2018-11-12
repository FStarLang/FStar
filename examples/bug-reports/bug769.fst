module Bug769

type nstype = {fn:string; ln:string;}
(* works *)
let a = {fn="hello";ln="world"}
let b = {a with fn="go";lname="universe"}
(* fails *)
let a = {fn="hello";ln="world"}
let b = {a with fname="go";ln="universe"}

