module Steel.Channel.Protocol

[@erasable]
noeq
type prot : Type -> Type =
| Return  : #a:Type -> v:a -> prot a
| Msg     : a:Type -> #b:Type -> k:(a -> prot b) -> prot b
| DoWhile : prot bool -> #a:Type -> k:prot a -> prot a

module WF = FStar.WellFounded

let rec ok #a (p:prot a) =
  match p with
  | Return _ -> True
  | Msg a k -> (forall x. (WF.axiom1 k x; ok (k x)))
  | DoWhile p k -> Msg? p /\ ok p /\ ok k

let protocol a = p:prot a { ok p }

let rec bind #a #b (p:protocol a) (q:(a -> protocol b))
  : protocol b
  = match p with
    | Return v -> q v
    | Msg c #a' k ->
      let k : c -> protocol b =
        fun x -> WF.axiom1 k x;
              bind (k x) q
      in
      Msg c k
    | DoWhile w k -> DoWhile w (bind k q)

let return (#a:Type) (x:a) : protocol a = Return x
let msg (t:Type) : protocol t = Msg t (fun x -> return x)

let xy : prot unit =
  x <-- msg int;
  y <-- msg (y:int{y = x + 1});
  return ()

let rec hnf (p:protocol 'a)
  : (q:protocol 'a{(Return? q \/ Msg? q) /\ (~(DoWhile? p) ==> (p == q))})
  = match p with
    | DoWhile p k -> b <-- hnf p ; if b then DoWhile p k else k
    | _ -> p

let finished (p:protocol 'a) : GTot bool = Return? (hnf p)
let more_msgs (p:protocol 'a) : GTot bool = Msg? (hnf p)
let next_msg_t (p:protocol 'a) : Type = match hnf p with | Msg a _ -> a | Return #a _ -> a
let step (p:protocol 'a{more_msgs p}) (x:next_msg_t p) : protocol 'a = Msg?.k (hnf p) x
