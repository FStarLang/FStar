module Asm1

module Map=FStar.Map
let map = Map.t
let op_String_Access = Map.sel
let op_String_Assignment = Map.upd
let contains = Map.contains

///////////////// Trusted definitions /////////////////

type reg = int
noeq type state = { regs:map reg int; mem:map int int }

type ins =
  | ILoad : lDst:reg -> lSrc:reg -> lOffset:int -> ins
  | IStore : sDst:reg -> sOffset:int -> sSrc:reg -> ins

let eval_ins (i:ins) (s:state) : Tot (option state) =
  match i with
  | ILoad dst src offset ->
      if contains s.regs dst && contains s.regs src then
        let a = s.regs.[src] + offset in
        if contains s.mem a then Some ({s with regs = (s.regs.[dst] <- s.mem.[a])})
        else None
      else None
  | IStore dst offset src ->
      if contains s.regs dst && contains s.regs src then
        let a = s.regs.[dst] + offset in
        if contains s.mem a then Some ({s with mem = (s.mem.[a] <- s.regs.[src])})
        else None
      else None

let rec eval_block (block:list ins) (s0:state) : Tot (option state) =
  match block with
  | [] -> Some s0
  | hd::tl ->
    (
      match eval_ins hd s0 with
      | None -> None
      | Some s1 -> eval_block tl s1
    )

///////////////// Vale-like untrusted lemmas /////////////////

let valid_state (s:state) : Tot bool =
  contains s.regs 0 && contains s.regs 1 && contains s.regs 2 && contains s.regs 3

let valid_reg (r:reg) : Tot bool = 0 <= r && r < 4

let lemma_load (b0:list ins) (s0:state
    {   (valid_state s0)
     /\ (match b0 with (ILoad dst src offset)::tl ->
            valid_reg dst
         /\ valid_reg src
         /\ contains s0.mem (s0.regs.[src] + offset) | _ -> False)}) :
  Tot (b1_s1:(list ins * state) {
    let (b1, s1) = b1_s1 in
    let Cons i _ = b0 in
    let ILoad dst src offset = i in
        b0 == i::b1
     /\ valid_state s1
     /\ Some s1 == eval_ins i s0
     /\ eval_block b0 s0 == eval_block b1 s1
     /\ s1 == {s0 with regs = (s0.regs.[dst] <- s0.mem.[s0.regs.[src] + offset])}}) =
  let Cons i b1 = b0 in
  let Some s1 = eval_ins i s0 in
  (b1, s1)

let lemma_store (b0:list ins) (s0:state
    {   (valid_state s0)
    /\  (match b0 with (IStore dst offset src)::tl ->
           valid_reg dst
        /\ valid_reg src
        /\ contains s0.mem (s0.regs.[dst] + offset) | _ -> False)}) :
  Tot (b1_s1:(list ins * state) {
    let (b1, s1) = b1_s1 in
    let Cons i _ = b0 in
    let IStore dst offset src = i in
        b0 == i::b1
     /\ valid_state s1
     /\ Some s1 == eval_ins i s0
     /\ eval_block b0 s0 == eval_block b1 s1
     /\ s1 == {s0 with mem = (s0.mem.[s0.regs.[dst] + offset] <- s0.regs.[src])}}) =
  let Cons i b1 = b0 in
  let Some s1 = eval_ins i s0 in
  (b1, s1)

let lemma_empty (s0:state) : Lemma
    (requires True)
    (ensures (eval_block [] s0 == Some s0)) =
  ()

let copy =
  [
    ILoad 0 3 0;
    ILoad 1 3 1;
    ILoad 2 3 2;
    IStore 3 20 0;
    IStore 3 21 1;
    IStore 3 22 2;
  ]

let lemma_copy (s0:state
    {   valid_state s0
     /\ (let a = s0.regs.[3] in
         let m = s0.mem in
            contains m (a + 0)
         /\ contains m (a + 1)
         /\ contains m (a + 2)
         /\ contains m (a + 20)
         /\ contains m (a + 21)
         /\ contains m (a + 22))}) :
  Tot (sN:state {
        valid_state sN
     /\ Some sN == eval_block copy s0
     /\ (let a = s0.regs.[3] in
         let m0 = s0.mem in
         let mN = sN.mem in
            mN.[a + 20] == m0.[a + 0]
         /\ mN.[a + 21] == m0.[a + 1]
         /\ mN.[a + 22] == m0.[a + 2])}) =
  let b0 = copy in
  let (b1, s1) = lemma_load b0 s0 in
  let (b2, s2) = lemma_load b1 s1 in
  let (b3, s3) = lemma_load b2 s2 in
  let (b4, s4) = lemma_store b3 s3 in
  let (b5, s5) = lemma_store b4 s4 in
  let (b6, s6) = lemma_store b5 s5 in
  lemma_empty s6;
  s6
