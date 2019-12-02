(*
   Copyright 2008-2018 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module MSeqExn

open FStar.HyperStack.ST
open FStar.Monotonic.Seq

module HS = FStar.HyperStack

type result (a:Type) =
  | Success : a -> result a
  | Error   : string -> result a


/// WP is standard post -> pre ... but on the type (result a)
///
/// With an additional monotonicity refinement -- this should hopefully go away when we start treating monotonicity better


type st_ewp (a:Type) = wp:st_wp (result a){
   forall p q. (forall r x. p r x ==> q r x) ==> (forall x. wp p x ==> wp q x)
}


/// The global trace reference


assume val entry_t : Type0

assume val trace_inv0 : Seq.seq entry_t -> Type0

assume val trace_ref : i_seq HS.root entry_t trace_inv0


/// Now the underlying representation of the new effect
///
/// Under the hoods, it's a STATE function that only modifies trace_ref


type st_erepr (a:Type) (wp:st_ewp a) =
  unit ->
  STATE (result a) (fun p h0 ->
    wp
      (fun r h1 ->
       (equal_stack_domains h0 h1 /\
        HS.modifies_one HS.root h0 h1 /\
        HS.modifies_ref HS.root (Set.singleton (HS.as_addr trace_ref)) h0 h1) ==> p r h1) h0)


/// Effect combinators


/// return

let st_ereturn (a:Type) (x:a)
: st_erepr a (fun p s -> p (Success x) s)
= fun _ -> Success x


/// bind

let st_ebind (a:Type) (b:Type)
  (wp_f:st_ewp a) (wp_g:a -> st_ewp b)
  (f:st_erepr a wp_f) (g:(x:a -> st_erepr b (wp_g x)))
: st_erepr b
  (fun p s0 -> wp_f (fun r s1 ->
    match r with
    | Success x -> (wp_g x) p s1
    | Error s -> p (Error s) s1) s0)
= let lemma_modifies_one_is_transitive ()  //Sad!
  : Lemma
    (forall h0 h1 h2. (HS.modifies_one HS.root h0 h1 /\ HS.modifies_one HS.root h1 h2) ==>
                  HS.modifies_one HS.root h0 h2)
  = () in

  lemma_modifies_one_is_transitive ();
  fun _ ->
  let r = f () in
  match r with
  | Success x -> (g x) ()
  | Error s -> Error s


/// sub computation

let st_esubcomp (a:Type)
  (wp_f:st_ewp a) (wp_g:st_ewp a)
  (f:st_erepr a wp_f)
: Pure (st_erepr a wp_g)
  (requires forall p n. wp_g p n ==> wp_f p n)
  (ensures fun _ -> True)
= f


/// if_then_else

let st_eif_then_else (a:Type)
  (wp_then:st_ewp a) (wp_else:st_ewp a)
  (f:st_erepr a wp_then) (g:st_erepr a wp_else)
  (p:Type0)
: Type
= st_erepr a (fun post n ->
    (p ==> wp_then post n) /\
    ((~ p) ==> wp_else post n))
  

/// And finally the effect definition

reifiable reflectable
layered_effect {
  STEXN : a:Type -> st_ewp a -> Effect
  with
  repr = st_erepr;
  return = st_ereturn;
  bind = st_ebind;
  subcomp = st_esubcomp;
  if_then_else = st_eif_then_else
}


/// DIV can be lifted to our effect


let lift_div_stexn (a:Type) (wp:pure_wp a{forall p q. (forall x. p x ==> q x) ==> (wp p ==> wp q)}) (f:unit -> DIV a wp)
: st_erepr a (fun p h -> wp (fun x -> p (Success x) h))
= fun _ -> Success (f ())

sub_effect DIV ~> STEXN = lift_div_stexn


/// Hoare-style abbreviation
///
/// The pre- and postcondition can only be over the pure traces,
///   so that in the specs one doesn't have to think about mem, modifies etc.
///
/// Also we by-default bake-in the trace_inv too, so that this also doesn't need to carried along


type trace = s:Seq.seq entry_t{trace_inv0 s}


effect StExn (a:Type) (pre:trace -> Type0) (post:trace -> result a -> trace -> Type0) =
  STEXN a (fun p h0 -> pre (i_sel h0 trace_ref) /\ (forall x h1. post (i_sel h0 trace_ref) x (i_sel h1 trace_ref) ==> p x h1))



/// To work with this new effect
///   while the DIV (and PURE) computations be lifted by the typechecker automatically,
///   STATE computations need to be `reflected` explicitly


let write_at_end (x:entry_t)
: StExn unit
  (requires fun s -> trace_inv0 (Seq.snoc s x))
  (ensures fun s0 r s1 -> r == Success () /\ s1 == Seq.snoc s0 x)
= STEXN?.reflect (fun _ ->
    i_write_at_end trace_ref x;
    Success ())


/// Similarly we can define a read function

let read (i:nat)
: StExn entry_t
  (requires fun s -> i < Seq.length s)
  (ensures fun s0 r s1 -> i < Seq.length s0 /\ r == Success (Seq.index s0 i) /\ s1 == s0)
= STEXN?.reflect (fun _ ->
    let s = i_read trace_ref in
    Success (Seq.index s i))


/// Some functions which we will use for testing

assume val some_pure_function (x:entry_t) : int


/// A get () function

let get ()
: StExn trace
  (requires fun _ -> True)
  (ensures fun s0 r s1 -> r == Success s0 /\ s1 == s0)
= STEXN?.reflect (fun _ -> Success (i_read trace_ref))


/// A function that reads the i-th index in the trace or throws error if i is not in bounds

let read_or_throw (i:nat)
: StExn entry_t
  (requires fun _ -> True)
  (ensures fun s0 r s1 ->
    s0 == s1 /\
    (i < Seq.length s0 ==> r == Success (Seq.index s0 i)) /\
    (i >= Seq.length s0 ==> r == Error ""))
= STEXN?.reflect (fun _ ->
    let s = i_read trace_ref in
    if i < Seq.length s then Success (Seq.index s i) else Error "")



/// Now we will write code in this new effect using the "actions" that we defined above


/// We don't need state libraries or monotonic sequence anymore!


#set-options "--using_facts_from '* -FStar.HyperStack -FStar.Monotonic'"

let test (i j:nat)
: StExn unit
  (requires fun s -> i < Seq.length s)
  (ensures fun s0 r s1 ->
    match j < Seq.length s0 with
    | true -> r == Success () /\ Seq.length s1 == Seq.length s0 + 1
    | false -> r == Error "" /\ s0 == s1)
= let x = read i in
  let y = read_or_throw j in  //no need to explicitly pattern match on the exception, it's propagated up automatically
  let b = some_pure_function y in
  let s = get () in
  if b > 0 then begin
    assume (trace_inv0 (Seq.snoc s y));
    write_at_end y
  end
  else begin
    assume (trace_inv0 (Seq.snoc s x));
    write_at_end x
  end



/// But the clients need not buy into our effect, we can tell the clients a stateful spec of test, for example:


/// Restart the solver to get state facts etc. in the context again


#restart-solver
#reset-options

let test_st (i j:nat)
: ST (result unit)
  (requires fun h -> i < Seq.length (i_sel h trace_ref))
  (ensures fun h0 r h1 -> 
    HS.modifies_one HS.root h0 h1 /\
    HS.modifies_ref HS.root (Set.singleton (HS.as_addr trace_ref)) h0 h1)  //can add functional specs too
= reify (test i j) ()


type epre = Type0
type epost (a:Type) = result a -> Type0
type ewp (a:Type) = wp:(epost a -> epre){
  forall p q. (forall x. p x ==> q x) ==> (wp p ==> wp q)
}


type erepr (a:Type) (wp:ewp a) = unit -> PURE (result a) wp


let ereturn (a:Type) (x:a)
: erepr a (fun p -> p (Success x))
= fun _ -> Success x

let ebind (a:Type) (b:Type)
  (wp_f:ewp a) (wp_g:a -> ewp b)
  (f:erepr a wp_f) (g:(x:a -> erepr b (wp_g x)))
: erepr b
  (fun p -> wp_f (fun r ->
    match r with
    | Success x -> (wp_g x) p
    | Error s -> p (Error s)))
= fun _ ->
  let r = f () in
  match r with
  | Success x -> (g x) ()
  | Error s -> Error s

let esubcomp (a:Type)
  (wp_f:ewp a) (wp_g:ewp a)
  (f:erepr a wp_f)
: Pure (erepr a wp_g)
  (requires forall p. wp_g p ==> wp_f p)
  (ensures fun _ -> True)
= f

let eif_then_else (a:Type)
  (wp_then:ewp a) (wp_else:ewp a)
  (f:erepr a wp_then) (g:erepr a wp_else)
  (p:Type0)
: Type
= erepr a (fun post ->
    (p ==> wp_then post) /\
    ((~ p) ==> wp_else post))
  

reifiable reflectable
layered_effect {
  EXN : a:Type -> ewp a -> Effect
  with
  repr = erepr;
  return = ereturn;
  bind = ebind;
  subcomp = esubcomp;
  if_then_else = eif_then_else
}


let lift_pure_exn (a:Type) (wp:pure_wp a{forall p q. (forall x. p x ==> q x) ==> (wp p ==> wp q)}) (f:unit -> PURE a wp)
: erepr a (fun p -> wp (fun x -> p (Success x)))
= fun _ -> Success (f ())

sub_effect PURE ~> EXN = lift_pure_exn


let lift_exn_stexn (a:Type) (wp:ewp a) (f:erepr a wp)
: st_erepr a (fun p h -> wp (fun r -> p r h))
= f


sub_effect EXN ~> STEXN = lift_exn_stexn


assume val test_lift_exn_stexn0 (b:bool)
: EXN int (fun p -> (b ==> p (Error "")) /\ ((~ b) ==> p (Success 0)))

let test_lift_exn_stexn1 ()
: STEXN int (fun p h -> p (Success 0) h)
= test_lift_exn_stexn0 false
