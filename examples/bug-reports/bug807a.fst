module Bug807a

let test1 = 
  let find (#a:Type) (x:nat) (l:list (int * a)) : option (int * a) = admit() in
  find 0 []

let test2 = 
  let find (#a:Type) (l:list a) : option a = admit() in
  find []

assume val id: #a:Type0 -> a -> Tot a
assume val app_id: (#a:Type0 -> a -> Tot a) -> Tot unit
let test3 = app_id id

let test4 = app_id (fun (#a:Type0) -> id #a)
