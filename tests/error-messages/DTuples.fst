module DTuples

(* Basic test *)
let _ = a:int & b:int{a > b} & c:int{c == a+b}

(* Desugared version, resugars to the same *)
let _ = dtuple3 int
                (fun a -> b:int{a > b})
                (fun a b -> c:int{c == a+b})

(* This one is resugared properly too, taking z to be the
name of the component, and of type (b:int{a > b}). *)
let _ = dtuple3 int
                (fun a -> b:int{a > b})
                (fun a z -> c:int{c == a+z})

(* Bunch of regression tests. *)               
let _ = (a:int & b:int{a>b} & unit)

let _ = (a:int & b:int & int)
let _ = (a:int & b:int & c:int & int)
let _ = (a:int & b:int & c:int & d:int & int)


let _ = (int & int)
let _ = (int & int & int)
let _ = (int & int & int & int)
let _ = (int & int & int & int & int)

let _ = (int & (int & int))
let _ = (int & (int & (int & int)))
let _ = (int & (int & (int & (int & int))))

(* All of these were terribly broken in master *)
let _ = tuple4 int bool
let _ = (tuple4 int bool) string unit

let _ = dtuple4 int (fun _ -> bool)

let t1 = (1,2,3)
let t2 = ((1,2),3)
let t3 = (1,(2,3))

let d1 = (|1,2,3|)
let d2 = (|(1,2),3|)
let d3 = (|1,(2,3)|)

let dd2 = (|(|1,2|),3|)
let dd3 = (|1,(|2,3|)|)
