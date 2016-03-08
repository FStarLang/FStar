module Test
assume new type id
assume new type rid
assume new type rref : rid -> Type0

type rw = 
  | Reader 
  | Writer

type state (i:id) (rw:rw) =
  | State: #region:rid 
         -> #peer_region:rid
         -> log: rref (if rw=Reader then peer_region else region) 
         -> state i rw

type writer i = s:state i Writer

assume val contains_ref: #r:rid -> rref r -> Tot bool

module Test2
open Test
let f i (w:writer i) h = contains_ref w.log
