module Sum_and_swap


open FStar.Classical
open FStar.Tactics
open FStar.Reflection
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
let sum_wp : hwp_mon int = 
    fun s0 post -> let (r1, r2) = s0 in post (U32.v r1 + U32.v r2, (r2, r1))


// Hardwritten for now but can be easily computed with a tactic (if there isn't support for this already)
unfold 
let sum_wp_full : hwp_mon int = 
  bind_wp (read_wp 0) (fun x0 ->
  bind_wp (read_wp 1) (fun x1 ->
  bind_wp (write_wp 0 x1) (fun () ->
  bind_wp (write_wp 1 x0) (fun () ->
  return_wp (U32.v x0 + U32.v x1)))))


//unfold let normal (#a:Type) (x:a) : a = norm [primops; delta; zeta] x

let wp_impl s0 post : Lemma (sum_wp_full s0 post ==> sum_wp s0 post) = ()

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
  let x0 = get_action 0 in 
  let x1 = get_action 1 in 
  let _  = put_action 0 x1 in
  let _  = put_action 1 x0 in
  U32.v x0 + U32.v x1


unfold
let wp1 (x0 : mint) : hwp_mon int =
  bind_wp (read_wp 1) (fun x1 ->
  bind_wp (write_wp 0 x1) (fun () ->
  bind_wp (write_wp 1 x0) (fun () ->
  return_wp (U32.v x0 + U32.v x1))))

unfold
let wp2 (x0 x1 : mint) : hwp_mon int = 
  bind_wp (write_wp 0 x1) (fun () ->
  bind_wp (write_wp 1 x0) (fun () ->
  return_wp (U32.v x0 + U32.v x1)))

unfold
let wp4 (x0 x1 : mint) (u : unit) : hwp_mon int = 
  return_wp (U32.v x0 + U32.v x1)

unfold
let wp3 (x0 x1 : mint) (u : unit) : hwp_mon int = 
  bind_wp (write_wp 1 x0) (wp4 x0 x1)

let force_eq #a #wp ($f:comp_wp a wp) : comp_wp a wp = f

//NS: Annoyingly, we seem to need to write this in this
//    partially eta-expanded form for inference to succeed
//    That's probably easily fixable
val swap_and_sum' :
  comp_wp int
          (bind_wp (fun s0 -> read_wp 0 s0) (fun x0 s1 ->
           bind_wp (fun s0 -> read_wp 1 s0) (fun x1 s2 -> 
           bind_wp (fun s0 -> write_wp 0 x1 s0) (fun _ s3 ->
           bind_wp (fun s0 -> write_wp 1 x0 s0) (fun _ s4 ->
           return_wp (U32.v x0 + U32.v x1) s4) s3) s2) s1))


//NS: More tricky is that it seems that to check the implementation
//    we need to turn off two phase tc
//    Otherwise, additional proof obligations about monotonicity
//    refinements pollute the computed VC and things go off the rails
#set-options "--use_two_phase_tc false"
let swap_and_sum' =
            (bind_elab (hread' 0) (fun x0 ->
             bind_elab (hread' 1) (fun x1 ->
             bind_elab (hwrite' 0 x1) (fun _ ->
             bind_elab (hwrite' 1 x0) (fun _ ->
             return_elab (U32.v x0 + U32.v x1))))))
  
val lswap_and_sum : unit -> lcomp_wp int sum_wp_full (reif sum_wp_full hswap_and_sum)
[@expect_failure] //still doesn't work
let lswap_and_sum () =  
  lbind (lread 0) (fun x0 -> 
  lbind (lread 1) (fun x1 -> 
  lbind (lwrite 0 x1) (fun () ->
  lbind (lwrite 1 x0) (fun () ->
  lreturn (U32.v x0 + U32.v x1)))))
  
