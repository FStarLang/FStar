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
  hreturn int (U32.v x0 + U32.v x1)))))
 

// WP for sum and swap
unfold
let sum_wp : hwp int  = fun s0 post -> let (r1, r2) = s0 in post (U32.v r1 + U32.v r2, (r2, r1))

// Pre and Post 
unfold 
let sum_pre = fun s0 -> True

unfold 
let sum_post = fun s0 res -> let (x, s1) = res in
                          let (r1, r2) = s0 in 
                          let (r1', r2') = s1 in 
                          x = U32.v r1 + U32.v r2 /\
                          r1 = r2' /\ r2 = r1'


val hswap_and_sum : unit -> HIGH int sum_wp 
let hswap_and_sum () = 
  let x0 = HIGH?.get 0 in 
  let x1 = HIGH?.get 1 in 
  let _  = HIGH?.put 0 x1 in
  let _  = HIGH?.put 1 x0 in
  U32.v x0 + U32.v x1

val swap_and_sum' : unit -> comp_wp' int sum_wp 
let swap_and_sum' () =  
  hbind' (hread' 0) (fun x0 -> 
  hbind' (hread' 1) (fun x1 -> 
  hbind' (hwrite' 0 x1) (fun () ->
  hbind' (hwrite' 1 x0) (fun () ->
  hreturn' (U32.v x0 + U32.v x1)))))


val lswap_and_sum : unit -> lcomp_wp' int sum_wp (reif sum_wp hswap_and_sum)
let lswap_and_sum () =  
  lbind (lread 0) (fun x0 -> 
  lbind (lread 1) (fun x1 -> 
  lbind (lwrite 0 x1) (fun () -> 
  lbind (lwrite 1 x0) (fun () ->
  lreturn (U32.v x0 + U32.v x1)))))
  
// lemmas to comute reif and bind 
// interm proof obligations remain provable in low comp
// extend beyond seq composition with if and rec
