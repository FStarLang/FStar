
open Prims

type rid =
FStar_HyperHeap.rid


type 'Aa reln =
'Aa  ->  'Aa  ->  Obj.t


type ('Aa, 'Ab) monotonic =
Prims.unit


type ('Ar, 'Aa, 'Ab) m_rref =
'Aa FStar_HyperStack.ref


let as_ref : rid  ->  Prims.unit  ->  Prims.unit  ->  (Prims.unit, Obj.t, Obj.t) m_rref  ->  Obj.t FStar_HyperStack.ref = (fun r a b x -> (Obj.magic (())))


let as_rref : rid  ->  Prims.unit  ->  Prims.unit  ->  (Prims.unit, Obj.t, Obj.t) m_rref  ->  (Prims.unit, Obj.t) FStar_HyperHeap.rref = (fun r a b x -> (Obj.magic (())))


let m_contains : rid  ->  Prims.unit  ->  Prims.unit  ->  (Prims.unit, Obj.t, Obj.t) m_rref  ->  FStar_HyperStack.mem  ->  Prims.bool = (fun r a b mr m -> (Obj.magic (())))


type ('Ar, 'Aa, 'Ab, 'Amr, 'Am0, 'Am1) m_fresh =
Prims.unit


let m_sel : rid  ->  Prims.unit  ->  Prims.unit  ->  FStar_HyperStack.mem  ->  (Prims.unit, Obj.t, Obj.t) m_rref  ->  Obj.t = (fun r a b m mr -> (Obj.magic (())))


let m_upd : rid  ->  Prims.unit  ->  Prims.unit  ->  FStar_HyperStack.mem  ->  (Prims.unit, Obj.t, Obj.t) m_rref  ->  Obj.t  ->  FStar_HyperStack.mem = (fun r a b m mr v -> (Obj.magic (())))


let m_alloc = (fun r init -> (FStar_HST.ralloc r init))


let m_read  (* : rid  ->  Prims.unit  ->  Prims.unit  ->  (Prims.unit, Obj.t, Obj.t) m_rref  ->  Obj.t *) = (fun r a b mr -> (FStar_HST.op_Bang mr))


let m_write = fun r a b mr v -> FStar_HST.op_Colon_Equals mr v


type ('Ai, 'Aa, 'Ab, 'Ar, 'Ap) stable_on_mem =
Prims.unit


type 'Ap witnessed =
Prims.l_True


let witness : rid  ->  Prims.unit  ->  Prims.unit  ->  (Prims.unit, Obj.t, Obj.t) m_rref  ->  Prims.unit  ->  Prims.unit = (fun r a b mr p -> ())


let weaken_witness = (fun uu____771 -> ())


let testify = (fun uu____774 -> ())


let testify_forall = (fun s -> ())


let m_recall = fun r a b mr -> FStar_HST.recall mr


type ('Ar, 'Am) rid_exists =
Prims.unit Prims.b2t


type ex_rid =
rid


let ex_rid_of_rid : rid  ->  ex_rid = (Obj.magic ((fun r -> ())))




