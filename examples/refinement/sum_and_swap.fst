module Sum_and_swap


open LowComp
open HighComp

module B = LowStar.Buffer
module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module U32 = FStar.UInt32

val swap_and_sum : unit -> comp int 
let swap_and_sum () =  
  hbind mint int (hread 0) (fun x0 -> 
  hbind mint int (hread 1) (fun x1 -> 
  hbind unit int (hwrite 0 x1) (fun () -> 
  hbind unit int (hwrite 1 x0) (fun () ->
  hbind mint int (hread 0) (fun x0' -> 
  hreturn int (U32.v x0 + U32.v x1))))))
 


let sum_wp : hwp int  = fun s0 post -> let (r1, r2) = s0 in post (U32.v r1 + U32.v r2, (r2, r1))

val hswap_and_sum : unit -> HIGH int sum_wp 
let hswap_and_sum () = 
  let x0 = HIGH?.get 0 in 
  let x1 = HIGH?.get 1 in 
  let _  = HIGH?.put 0 x1 in
  let _  = HIGH?.put 1 x0 in
  U32.v x0 + U32.v x1

//val swap_and_sum' : unit -> comp_wp int sum_wp 
let swap_and_sum' () =  
  hbind' (hread' 0) (fun x0 -> 
  hbind' (hread' 1) (fun x1 -> 
  hbind' (hwrite' 0 x1) (fun () -> 
  hbind' (hwrite' 1 x0) (fun () ->
  hbind' (hread' 0) (fun x0' -> 
  hreturn' (U32.v x0 + U32.v x1))))))


val lswap_and_sum : unit -> lcomp_wp int sum_wp (swap_and_sum' ())
let lswap_and_sum () =  
  lbind (lread 0) (fun x0 -> 
  lbind (lread 1) (fun x1 -> 
  lbind (lwrite 0 x1) (fun () -> 
  lbind (lwrite 1 x0) (fun () ->
  lbind (lread 0) (fun x0' -> 
  lreturn (U32.v x0 + U32.v x1))))))
  
