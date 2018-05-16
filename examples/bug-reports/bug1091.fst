module Bug1091
//disabling of two phase tc here is intentional, as the bug happens only then
#set-options "--max_fuel 1 --max_ifuel 1 --initial_fuel 1 --initial_ifuel 1 --use_two_phase_tc false"

////////////////////////////////////////////////////////////////////////////////
// June 21, 2017
////////////////////////////////////////////////////////////////////////////////
module UInt = FStar.UInt
module U64 = FStar.UInt64

type jun21_2017_t = { low: U64.t; high: U64.t }

assume val jun21_2017_v: jun21_2017_t -> n:nat{n < pow2 128}

[@ (fail [66;19])]
let jun21_2017_logand_fail (a b: jun21_2017_t) : Pure jun21_2017_t
  (requires True)
  (ensures (fun r -> jun21_2017_v r = UInt.logand (jun21_2017_v a) (jun21_2017_v b))) = a

assume val jun21_2017_vv: jun21_2017_t -> UInt.uint_t 128
[@ (fail [19])]
let jun21_2017_logand (a b: jun21_2017_t) : Pure jun21_2017_t
  (requires True)
  (ensures (fun r -> jun21_2017_vv r = UInt.logand (jun21_2017_vv a) (jun21_2017_vv b))) = a

////////////////////////////////////////////////////////////////////////////////
// June 29, 2017
let jun29_2017 =
    let x =
      let rec __f u : unit = __f u in
      __f
    in x

////////////////////////////////////////////////////////////////////////////////
// July 25, 2017
////////////////////////////////////////////////////////////////////////////////
let jul25_2017_secTry (s:string): Tot Type0 =
     match s with
     | _ -> string

type jul25_2017_uList (s:string) = (jul25_2017_secTry s)
let jul25_2017_refUL (#s:string) (tl:jul25_2017_uList s) = FStar.Ref.alloc tl

////////////////////////////////////////////////////////////////////////////////
// Oct 4, 2017
////////////////////////////////////////////////////////////////////////////////
assume val oct4_2017_m : Type -> Type
assume val oct4_2017_return_m : #a:Type -> a -> oct4_2017_m a
assume val oct4_2017_bind_m : #a:Type -> #b:Type -> oct4_2017_m a -> (a -> oct4_2017_m b) -> oct4_2017_m b
assume val oct4_2017_push_m : #a:Type -> #b:(a -> Type) -> (x:a -> oct4_2017_m (b x)) -> oct4_2017_m (x:a -> b x)

(* The original report says that omitting either of the implicit arguments
   below results in a crash.
   But, that's not longer the case.
   Omitting them both fails to infer the expected type but no crash *)
val oct4_2017_push_sum : #a:Type -> #b:(a -> Type) ->
                  dtuple2 a (fun (x:a) -> oct4_2017_m (b x)) -> oct4_2017_m (dtuple2 a b)
let oct4_2017_push_sum (#a:Type) (#b:(a -> Type)) (p : (dtuple2 a (fun (x:a) -> oct4_2017_m (b x)))) =
    match p with
    | Mkdtuple2 x y ->
        oct4_2017_bind_m #(b x) // #(dtuple2 a b)
    y (fun (y' : b x) ->
        oct4_2017_return_m #(dtuple2 a b) (Mkdtuple2 x y'))

////////////////////////////////////////////////////////////////////////////////
//Oct 18, 2017
////////////////////////////////////////////////////////////////////////////////
let oct18_2017_xderef t pre m a = FStar.HyperStack.sel #t #pre m a

////////////////////////////////////////////////////////////////////////////////
//April 19, 2017
////////////////////////////////////////////////////////////////////////////////
open FStar.Tactics
val apr19_2017_mem: #a:eqtype -> a -> list a -> Tot bool
let rec apr19_2017_mem #a x xs =
        match xs with
        | [] -> false
        | hd :: tl -> if x = hd then true else apr19_2017_mem x tl

[@ (FStar.Pervasives.fail [19;19;19])]
let apr19_2017_mem_sanity_fail #a x xs =
        assert_by_tactic (apr19_2017_mem x xs <==> apr19_2017_mem x xs) idtac

let apr19_2017_mem_sanity (#a:eqtype) (x:a) xs =
        assert_by_tactic (apr19_2017_mem x xs <==> apr19_2017_mem x xs) idtac

////////////////////////////////////////////////////////////////////////////////
//April 21, 2017
////////////////////////////////////////////////////////////////////////////////
[@ (FStar.Pervasives.fail [19])]
let rec apr21_2017_ackermann_fail m n =
  if m=0 then n + 1
  else if n = 0 then apr21_2017_ackermann_fail (m - 1) 1
  else apr21_2017_ackermann_fail (m - 1) (apr21_2017_ackermann_fail m (n - 1))

let rec apr21_2017_ackermann (m n : nat) =
  if m=0 then n + 1
  else if n = 0 then apr21_2017_ackermann (m - 1) 1
  else apr21_2017_ackermann (m - 1) (apr21_2017_ackermann m (n - 1))
