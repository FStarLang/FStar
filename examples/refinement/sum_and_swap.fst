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
let sum_wp : (wp:hwp int{monotonic wp}) = 
  let wp = 
    fun s0 post -> let (r1, r2) = s0 in post (U32.v r1 + U32.v r2, (r2, r1))
  in
  let p : squash (monotonic wp) = 
    let p (p1 : int * state -> Type) (p2 : int * state -> Type) (s : state) 
          (h: squash (forall y. p1 y ==> p2 y)) : GTot (squash (wp s p1 ==> wp s p2)) = 
      ()
    in
    let p' p1 p2 s : Lemma ((forall y. p1 y ==> p2 y) ==> (wp s p1 ==> wp s p2)) = 
      arrow_to_impl (p p1 p2 s)
    in
    forall_intro_3 p'
  in 
  assert (monotonic wp);
  wp


// Hardwritten for now but can be easily computed with a tactic (if there isn't support for this already)
unfold 
let sum_wp_full : (wp:hwp int{monotonic wp}) = 
  bind_wp (read_wp 0) (fun x0 ->
  bind_wp (read_wp 1) (fun x1 ->
  bind_wp (write_wp 0 x1) (fun () ->
  bind_wp (write_wp 1 x0) (fun () ->
  return_wp (U32.v x0 + U32.v x1)))))


//unfold let normal (#a:Type) (x:a) : a = norm [primops; delta; zeta] x

let wp_impl s0 post : Lemma (sum_wp_full s0 post ==> sum_wp s0 post) = admit ()

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


unfold
let wp1 (x0 : mint) : (wp:hwp int{monotonic wp}) = 
  bind_wp (read_wp 1) (fun x1 ->
  bind_wp (write_wp 0 x1) (fun () ->
  bind_wp (write_wp 1 x0) (fun () ->
  return_wp (U32.v x0 + U32.v x1))))

unfold
let wp2 (x0 x1 : mint) : (wp:hwp int{monotonic wp}) = 
  bind_wp (write_wp 0 x1) (fun () ->
  bind_wp (write_wp 1 x0) (fun () ->
  return_wp (U32.v x0 + U32.v x1)))

unfold
let wp4 (x0 x1 : mint) (u : unit) : (wp:hwp int{monotonic wp}) = 
  return_wp (U32.v x0 + U32.v x1)

unfold
let wp3 (x0 x1 : mint) (u : unit) : (wp:hwp int{monotonic wp}) = 
  bind_wp (write_wp 1 x0) (wp4 x0 x1)

val swap_and_sum' : x0:mint -> x1:mint -> comp_wp'  int (bind_wp (write_wp 1 x0) (fun () -> return_wp (U32.v x0 + U32.v x1)))
let swap_and_sum' x0 x1 =  
  bind_elab #mint #int #(read_wp 0) (hread' 0) #wp1 (fun x0 -> 
  bind_elab #mint #int #(read_wp 1) (hread' 1) #(wp2 x0) (fun x1 -> 
  bind_elab #unit #int #(write_wp 0 x1) (hwrite' 0 x1) #(wp3 x0 x1) (fun () ->
  bind_elab #unit #int #(write_wp 1 x0) (hwrite' 1 x0) #(fun () -> return_wp (U32.v x0 + U32.v x1)) (fun () ->
  return_elab #int (U32.v x0 + U32.v x1)))))

val lswap_and_sum : unit -> lcomp_wp2 int sum_wp_full (reif sum_wp_full hswap_and_sum)
let lswap_and_sum () =  
  lbind (lread 0) (fun x0 -> 
  lbind (lread 1) (fun x1 -> 
  lbind (lwrite 0 x1) (fun () ->
  lbind (lwrite 1 x0) (fun () ->
  lreturn (U32.v x0 + U32.v x1)))))
  
