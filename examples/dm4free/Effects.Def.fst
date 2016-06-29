(* This module defines 4 monads arranged in a partial order

       stexn
        ^ ^
       /   \       
      st   exn 
       \   /
        v v 
       exnst

   Proving the monad laws for each point and the morphism laws for
   each edge.
*)
module Effects.Def
open FStar.FunctionalExtensionality //proving the laws requires feq

(********************************************************************************)
(* Effect (st a) : A state monad over an abstract state type s                  *)
(********************************************************************************)
assume type s : Type //an abstract type of the state

let st (a:Type) = s -> Tot (a * s)

let return_st  (#a:Type) (x:a)
  : st a = fun s -> (x, s)
  
let bind_st (#a:Type) (#b:Type) (f:st a) (g: a -> Tot (st b))
  : st b 
  = fun s0 -> let x, s1 = f s0 in 
           g x s1

//Two actions: get and put
let get (u:unit) : st s = fun s -> s, s
let put (s:s) : st unit = fun _ -> (),s

////////////////////////////////////////////////////////////////////////////////
// The monad laws for (st a)
////////////////////////////////////////////////////////////////////////////////
let right_unit (a:Type) (f:st a) 
  : Lemma (bind_st f return_st = f)
  = assert (feq (bind_st f return_st) f)
  
let left_unit (a:Type) (b:Type) (x:a) (f:a -> Tot (st b)) 
  : Lemma (bind_st (return_st x) f = f x)
  = assert (feq (bind_st (return_st x) f) (f x))

let assoc (a:Type) (b:Type) (c:Type) (f:st a) (g:(a -> Tot (st b))) (h:(b -> Tot (st c)))
  : Lemma  (bind_st f (fun x -> bind_st (g x) h) = bind_st (bind_st f g) h) 
  = assert (feq (bind_st f (fun x -> bind_st (g x) h)) (bind_st (bind_st f g) h))

(********************************************************************************)
(* Effect (ex a) : A state monad over an abstract state type s                  *)
(********************************************************************************)
let ex (a:Type) = unit -> Tot (option a)

let return_ex (#a:Type) (x:a) 
  : ex a 
  = fun _ -> Some x
  
let bind_ex (#a:Type) (#b:Type) (f:ex a) (g: a -> Tot (ex b)) 
  : ex b 
  = fun _ -> match f () with 
          | None -> None
   	  | Some x -> g x ()

//one action: raise
let raise_ (#a:Type) 
  : ex a
  = fun () -> None

//and a handler
let handle (#a:Type) (f:ex a) (g:unit -> Tot a) 
  : Tot a 
  = match f () with 
    | None -> g()
    | Some x -> x

////////////////////////////////////////////////////////////////////////////////
// The monad laws for (ex a)
////////////////////////////////////////////////////////////////////////////////
let right_unit_ex (a:Type) (f:ex a) : Lemma (bind_ex f return_ex = f)
  = assert (feq (bind_ex f return_ex) f)
  
let left_unit_ex (a:Type) (b:Type) (x:a) (f:a -> Tot (ex b)) : Lemma (bind_ex (return_ex x) f = f x)
  = assert (feq (bind_ex (return_ex x) f) (f x))

let assoc_ex (a:Type) (b:Type) (c:Type) (f:ex a) (g:(a -> Tot (ex b))) (h:(b -> Tot (ex c)))
  : Lemma  (bind_ex f (fun x -> bind_ex (g x) h) = bind_ex (bind_ex f g) h) 
  = assert (feq (bind_ex f (fun x -> bind_ex (g x) h)) (bind_ex (bind_ex f g) h))

(********************************************************************************)
(* Effect (stexn a) : A combined monad, exceptions over state                   *)
(********************************************************************************)
let stexn (a:Type) = s -> Tot (option a * s)

let return_stexn (#a:Type) (x:a) 
  : stexn a 
  = fun s -> Some x, s
  
let bind_stexn (#a:Type) (#b:Type) (f:stexn a) (g: a -> Tot (stexn b)) 
  : stexn b 
  = fun s0 -> match f s0 with 
           | None, s1 -> None, s1
  	   | Some x, s1 -> g x s1

//no actions of its own

////////////////////////////////////////////////////////////////////////////////
// The monad laws for (stexn a)
////////////////////////////////////////////////////////////////////////////////
let right_unit_stexn (a:Type) (f:stexn a) 
  : Lemma (bind_stexn f return_stexn = f)
  = assert (feq (bind_stexn f return_stexn) f)
  
let left_unit_stexn (a:Type) (b:Type) (x:a) (f:a -> Tot (stexn b)) 
  : Lemma (bind_stexn (return_stexn x) f = f x)
  = assert (feq (bind_stexn (return_stexn x) f) (f x))

let assoc_stexn (a:Type) (b:Type) (c:Type) (f:stexn a) (g:(a -> Tot (stexn b))) (h:(b -> Tot (stexn c)))
  : Lemma  (bind_stexn f (fun x -> bind_stexn (g x) h) = bind_stexn (bind_stexn f g) h) 
  = assert (feq (bind_stexn f (fun x -> bind_stexn (g x) h)) (bind_stexn (bind_stexn f g) h))

(********************************************************************************)
(* Effect (exnst a) : A combined monad, state over exceptions                   *)
(********************************************************************************)
let exnst (a:Type) = s -> Tot (option (a * s))

let return_exnst (#a:Type) (x:a) 
  : exnst a 
  = fun s -> Some (x, s)
  
let bind_exnst (#a:Type) (#b:Type) (f:exnst a) (g: a -> Tot (exnst b)) 
  : exnst b 
  = fun s0 -> match f s0 with 
           | None -> None
           | Some (x, s1) -> g x s1
	   
//no actions of its own

////////////////////////////////////////////////////////////////////////////////
// The monad laws for (exnst a)
////////////////////////////////////////////////////////////////////////////////
let right_unit_exnst (a:Type) (f:exnst a) 
  : Lemma (bind_exnst f return_exnst = f)
  = assert (feq (bind_exnst f return_exnst) f)
  
let left_unit_exnst (a:Type) (b:Type) (x:a) (f:a -> Tot (exnst b)) 
  : Lemma (bind_exnst (return_exnst x) f = f x)
  = assert (feq (bind_exnst (return_exnst x) f) (f x))

let assoc_exnst (a:Type) (b:Type) (c:Type) (f:exnst a) (g:(a -> Tot (exnst b))) (h:(b -> Tot (exnst c)))
  : Lemma  (bind_exnst f (fun x -> bind_exnst (g x) h) = bind_exnst (bind_exnst f g) h) 
  = assert (feq (bind_exnst f (fun x -> bind_exnst (g x) h)) (bind_exnst (bind_exnst f g) h))

(********************************************************************************)
(* Morphism: st -> stexn                                                        *)
(********************************************************************************)
let lift_st_stexn (#a:Type) (f:st a) 
  : stexn a 
  = fun s0 -> let x, s1 = f s0 in Some x, s1

//morphism laws
let lift_unit_st_stexn (a:Type) (x:a) 
  : Lemma (lift_st_stexn (return_st x) = return_stexn x)
  = assert (feq (lift_st_stexn (return_st x)) (return_stexn x))

let lift_bind_st_stexn (a:Type) (b:Type) (f:st a) (g:(a -> Tot (st b)))
  : Lemma (lift_st_stexn (bind_st f g) = bind_stexn (lift_st_stexn f) (fun x -> lift_st_stexn (g x)))
  = assert (feq (lift_st_stexn (bind_st f g)) (bind_stexn (lift_st_stexn f) (fun x -> lift_st_stexn (g x))))

(********************************************************************************)
(* Morphism: exn -> stexn                                                       *)
(********************************************************************************)
let lift_ex_stexn (#a:Type) (f:ex a) 
  : stexn a 
  = fun s0 -> f (), s0

//morphism laws
let lift_unit_ex_stexn (a:Type) (x:a) 
  : Lemma (lift_ex_stexn (return_ex x) = return_stexn x)
  = assert (feq (lift_ex_stexn (return_ex x)) (return_stexn x))

let lift_bind_ex_stexn (a:Type) (b:Type) (f:ex a) (g:(a -> Tot (ex b)))
  : Lemma (lift_ex_stexn (bind_ex f g) = bind_stexn (lift_ex_stexn f) (fun x -> lift_ex_stexn (g x)))
  = assert (feq (lift_ex_stexn (bind_ex f g)) (bind_stexn (lift_ex_stexn f) (fun x -> lift_ex_stexn (g x))))

(********************************************************************************)
(* Morphism: st -> exnst                                                        *)
(********************************************************************************)
let lift_st_exnst (#a:Type) (f:st a) 
  : exnst a 
  = fun s0 -> Some (f s0)

//morphism laws
let lift_unit_st_exnst (a:Type) (x:a) 
  : Lemma (lift_st_exnst (return_st x) = return_exnst x)
  = assert (feq (lift_st_exnst (return_st x)) (return_exnst x))

let lift_bind_st_exnst (a:Type) (b:Type) (f:st a) (g:(a -> Tot (st b)))
  : Lemma (lift_st_exnst (bind_st f g) = bind_exnst (lift_st_exnst f) (fun x -> lift_st_exnst (g x)))
  = assert (feq (lift_st_exnst (bind_st f g)) (bind_exnst (lift_st_exnst f) (fun x -> lift_st_exnst (g x))))

(********************************************************************************)
(* Morphism: ex -> exnst                                                        *)
(********************************************************************************)
let lift_ex_exnst (#a:Type) (f:ex a) 
  : exnst a 
  = fun s0 -> match f () with 
           | None -> None
	   | Some x -> Some (x, s0)

//morphism laws  
let lift_unit_ex_exnst (a:Type) (x:a) 
  : Lemma (lift_ex_exnst (return_ex x) = return_exnst x)
  = assert (feq (lift_ex_exnst (return_ex x)) (return_exnst x))

let lift_bind_ex_exnst (a:Type) (b:Type) (f:ex a) (g:(a -> Tot (ex b)))
  : Lemma (lift_ex_exnst (bind_ex f g) = bind_exnst (lift_ex_exnst f) (fun x -> lift_ex_exnst (g x)))
  = assert (feq (lift_ex_exnst (bind_ex f g)) (bind_exnst (lift_ex_exnst f) (fun x -> lift_ex_exnst (g x))))
