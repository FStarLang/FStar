(*
   Copyright 2020 Microsoft Research

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

module Steel.Channel.Protocol

type tag = | Send | Recv

// AF: Make it non erasable for now to implement duplex.PCM
//[@@erasable]
noeq
type prot : Type -> Type =
| Return  : #a:Type -> v:a -> prot a
| Msg     : tag -> a:Type -> #b:Type -> k:(a -> prot b) -> prot b
| DoWhile : prot bool -> #a:Type -> k:prot a -> prot a

let rec ok #a (p:prot a) =
  match p with
  | Return _ -> True
  | Msg _ a k -> (forall x. ok (k x))
  | DoWhile p k -> Msg? p /\ ok p /\ ok k

let protocol a = p:prot a { ok p }


let flip_tag = function
  | Send -> Recv
  | Recv -> Send

let rec dual #a (p:protocol a) : q:protocol a{Msg? p ==> Msg? q} =
  match p with
  | Return _ -> p
  | Msg tag b #a k ->
    let k : b -> protocol a =
      fun (x:b) -> dual #a (k x)
    in
    Msg (flip_tag tag) b #a k
  | DoWhile p #a k -> DoWhile (dual p) #a (dual k)


let rec bind #a #b (p:protocol a) (q:(a -> protocol b))
  : protocol b
  = match p with
    | Return v -> q v
    | Msg tag c #a' k ->
      let k : c -> protocol b =
        fun x -> bind (k x) q
      in
      Msg tag c k
    | DoWhile w k -> DoWhile w (bind k q)

let return (#a:Type) (x:a) : protocol a = Return x
let done = return ()
let send (t:Type) : protocol t = Msg Send t (fun x -> return x)
let recv (t:Type) : protocol t = Msg Recv t (fun x -> return x)

(* Some simple protocols *)

(* Send an int [x], recv a [y > x] *)
let xy : prot unit =
  x <-- send int;
  y <-- recv (y:int{y > x});
  return ()

let rec hnf (p:protocol 'a)
  : (q:protocol 'a{(Return? q \/ Msg? q) /\ (~(DoWhile? p) ==> (p == q))})
  = match p with
    | DoWhile p k -> b <-- hnf p ; if b then DoWhile p k else k
    | _ -> p

let finished (p:protocol 'a) : GTot bool = Return? (hnf p)
let more_msgs (p:protocol 'a) : GTot bool = Msg? (hnf p)
let next_msg_t (p:protocol 'a) : Type = match hnf p with | Msg _ a _ -> a | Return #a _ -> a
let step (p:protocol 'a{more_msgs p}) (x:next_msg_t p) : protocol 'a = Msg?.k (hnf p) x


noeq
type trace : from:protocol unit -> to:protocol unit -> Type =
  | Waiting  : p:protocol unit -> trace p p
  | Message  : from:protocol unit{more_msgs from} ->
               x:next_msg_t from ->
               to:protocol unit ->
               trace (step from x) to->
               trace from to

let rec extend (#from #to:protocol unit)
               (t:trace from to{more_msgs to})
               (m:next_msg_t to)
  : Tot (trace from (step to m)) (decreases t)
  = match t with
    | Waiting _ ->
      Message _ _ _ (Waiting (step to m))
    | Message _from x _to tail ->
      Message _ _ _ (extend tail m)

let rec last_step_of (#from #to:protocol unit)
                     (t:trace from to { ~ (Waiting? t) })

   : Tot (q:protocol unit &
          x:next_msg_t q &
          squash (more_msgs q /\to == step q x))
         (decreases t)
   = match t with
     | Message _ x _ (Waiting _) -> (| from , x, () |)
     | Message _ _ _ tail -> last_step_of tail

noeq
type partial_trace_of (p:protocol unit) = {
  to:protocol unit;
  tr:trace p to
}

module P = FStar.Preorder
module R = FStar.ReflexiveTransitiveClosure

let next (#p:protocol unit) : P.relation (partial_trace_of p) =
  fun (t0 t1: partial_trace_of p) ->
    more_msgs t0.to /\
    (exists (msg:next_msg_t t0.to).
      t1.to == step t0.to msg /\
      t1.tr == extend t0.tr msg)

let extended_to (#p:protocol unit) : P.preorder (partial_trace_of p) =
  R.closure (next #p)

let extend_partial_trace (#p:protocol unit)
                         (x:partial_trace_of p)
                         (msg:next_msg_t x.to{more_msgs x.to})
  : Tot (y:partial_trace_of p{x `extended_to` y})
  = { to=_; tr=extend x.tr msg}


let more (p:protocol unit) = more_msgs p
let tag_of (p:protocol unit{more p}) : GTot tag = Msg?._0 (hnf p)
let msg_t (p:protocol unit) = next_msg_t p
let extension_of #p (tr:partial_trace_of p) = ts:partial_trace_of p{tr `extended_to` ts}
let until #p (tr:partial_trace_of p) = tr.to
