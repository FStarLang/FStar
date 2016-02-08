module TEST
open FStar.HyperHeap
type gid = int

type rw = 
  | Reader
  | Writer

type state (i:gid) (rw:rw) = 
  | State :
      #region:rid{region<>root}
    -> #peer_region:rid{peer_region <> root 
                     /\ HyperHeap.disjoint region peer_region}
    -> log:  rref (if rw=Reader then peer_region else region) int
    -> state i rw


let f (#i:gid) (#r:rw) (s:state i r) = !(State.log s)

let g (#i:gid) (#r:rw) (s:state i r) = 
  let (State l) = s in 
  !l
