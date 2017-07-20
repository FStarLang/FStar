module Bug769b

type nstype = {fn:string;}
(* all of the following works *)
let a = {fn="hello";ln="world"}
let b = {fn="go";lname="universe"}

