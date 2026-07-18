module Bug2614

assume val t: int -> Type0
assume val p: x:int -> y:t x -> prop

// Previously led to
//(Error 230) Variable "a#59" not found
let test_exists_intro (x:int) (y:t x) (_:squash (p x y)) =
  introduce exists (a:int) (b:t a). p a b
  with x y
  and ()

//Ugly workaround
let test_exists_intro_workaround (x:int) (y:t x) (_:squash (p x y)) =
  introduce exists (a:int). (exists (b:t a). p a b)
  with x and (
    introduce exists (b:t x). p x b
    with y and ()
  )

let test_exists_elim (_:squash(exists (x:int) (y:t x). p x y)) =
  eliminate exists (x:int) (y:t x). p x y
  returns True
  with _. ()

let test_forall_intro (f:(x:int -> y:t x -> squash (p x y))) =
  introduce forall (x:int) (y: t x). p x y
  with f x y

// Previously led to
//(Error 230) Variable "x#1492" not found
let test_forall_elim (a:int) (b:t a) (_:squash(forall (x:int) (y:t x). p x y)) =
  eliminate forall (x:int) (y:t x). p x y
  with a b

// //Ugly workaround
let test_forall_elim_workaround (a:int) (b:t a) (_:squash(forall (x:int) (y:t x). p x y)) =
  eliminate forall (x:int). (forall (y:t x). p x y)
  with a;
  eliminate forall (y:t a). p a y
  with b
