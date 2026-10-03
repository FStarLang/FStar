module Beta

let test (y:int) = (fun (x:int{False}) -> assert (x > 0)) y