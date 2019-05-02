module GenRecParam

noeq
type data = {
     dom : Type ;
     cod : dom -> Type0 ;
     pre : dom -> Type0 ;
     post : (d:dom) -> cod d -> Type0
  }

#set-options "--print_universes --__temp_no_proj  GenRecParam"

noeq
type gr (h : data) (d0 : h.dom) (a:Type) : Type =
  | Ret : a -> gr h d0 a
  | Call : (d:h.dom{d << d0}) -> (h.cod d -> gr h d0 a) -> gr h d0 a

// let ret (a:Type) d0 (x:a) : gr d0 a = Ret x

open FStar.WellFounded

let rec lift (h:data) b (post : b -> Type0) d0 (c : gr h d0 b) : Type0 =
  match c with
  | Ret x -> post x
  | Call d' k -> h.pre d' /\ // d' << d /\
    (forall c. h.post d' c ==> (axiom1 k c ; lift h b post d0 (k c)))

open FStar.Tactics

let call h (d0 d:h.dom) : Pure (gr h d0 (h.cod d)) (requires (h.pre d /\ d << d0)) (ensures (lift h _ (h.post d) d0)) // by (compute (); explode (); dump "")
  =
  let r = Call d (fun c -> Ret c) in
  // assert (lift h_post d r) by (compute (); explode (); dump "");
  r

// let rec eval
//   (d0 : h.dom)
//   b pre post
//   (c : unit -> unit)
//   () : Pure b (requires pre) (ensures post) (decreases %[d0 ; (assume pre; c ())])
//    by (fail ""; dump "")
//   = magic ()

(* Without `hh`, the decreases clause is ill-formed. We anyway get rid of it
 * ahead in `eval`. *)
let rec eval_boot (h:data)
  (body : (d:h.dom) -> Pure (gr h d (h.cod d)) (requires (h.pre d)) (ensures (lift h _ (h.post d) d)))
  (d0 : h.dom)
  b pre post (c : unit -> Pure (gr h d0 b) (requires pre) (ensures (lift h _ post d0)))
  (hh : squash pre)
  () : Pure b (requires True) (ensures post) (decreases %[d0; c ()])
  =
    match c () with
      | Ret x -> x
      | Call d k ->
        let r = eval_boot h body d (h.cod d) (h.pre d) (h.post d) (fun () ->  body d) hh in
        let r0 = r () in axiom1 k r0 ;
        eval_boot h body d0 b (pre /\ h.pre d) post (fun () ->  k r0) hh ()

let eval (h:data)
  (body : (d:h.dom) -> Pure (gr h d (h.cod d)) (requires (h.pre d)) (ensures (lift h _ (h.post d) d)))
  (d0 : h.dom)
  b pre post (c : unit -> Pure (gr h d0 b) (requires pre) (ensures (lift h _ post d0)))
  () : Pure b (requires pre) (ensures post)
  = eval_boot h body d0 b pre post c () ()

let fix (h:data) (body : (d:h.dom) -> Pure (gr h d (h.cod d)) (requires (h.pre d)) (ensures (lift h _ (h.post d) d))) (d:h.dom) : Pure (h.cod d) (requires (h.pre d)) (ensures (h.post d)) =
  eval h body d (h.cod d) (h.pre d) (h.post d) (fun () -> body d) ()

let fib0_data = { dom = nat ; cod = (fun _ -> nat) ; pre = (fun _ -> True) ; post = fun  _ r -> r >= 0}

let ret #h #d0 #a (x:a) : gr h d0 a = Ret x
let rec bind #h #d0 #a #b (m:gr h d0 a) (f: a -> gr h d0 b) : gr h d0 b =
  match m with
  | Ret x -> f x
  | Call d k -> Call d (fun x -> axiom1 k x; bind (k x) f)


let fib0 (n:nat) : Pure (gr fib0_data n nat)
  (requires (fib0_data.pre n))
  (ensures (lift fib0_data _ (fib0_data.post n) n)) =
  if n <= 1 then
    ret 1
  else
    bind (call fib0_data n (n-1))
    (fun r1 -> bind (call fib0_data n (n-2))
      (fun r2 -> ret #_ #_ #nat (r1 + r2)))

let fib (n:nat) = fix fib0_data fib0 n

let fib0_data' = { dom = nat ; cod = (fun _ -> nat) ; pre = (fun _ -> True) ; post = fun  n r -> r >= 1 /\ r >= n}


let fib0' (n:nat) : Pure (gr fib0_data' n nat)
  (requires (fib0_data'.pre n))
  (ensures (lift fib0_data' _ (fib0_data'.post n) n)) =
  if n <= 1 then
    ret 1
  else
    bind (call fib0_data' n (n-1))
    (fun r1 -> bind (call fib0_data' n (n-2))
      (fun r2 -> ret #_ #_ #nat (r1 + r2)))

let fib' (n:nat) : Pure _ True (fun r -> r >= n) = fix fib0_data' fib0' n
