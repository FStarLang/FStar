module Example.SimpleDBModel
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.GhostPCMReference
open FStar.Preorder
module GR = Pulse.Lib.GhostPCMReference
module MR = Pulse.Lib.MonotonicGhostRef
let as_prop (p:prop) = p <==> True
// A tiny db
type db = {
  inventory:nat;
  pending_orders:nat;
}

//Actions that can be performed on the db
type action =
| Restock of nat
| Order of nat
| Fulfill of nat

//A single step transition relation for the db, i.e. the semantics of the actions
let step (a:action) (d:db) : db = 
  match a with
  | Restock n -> 
    { d with inventory = d.inventory + n }
  | Order n -> 
    if d.inventory >= n 
    then { inventory=d.inventory - n; pending_orders=d.pending_orders + n}
    else d
  | Fulfill n -> 
    if d.pending_orders >= n
    then { d with pending_orders=d.pending_orders - n}
    else d

module R = FStar.ReflexiveTransitiveClosure
let db_single_step : R.binrel db = fun d0 d1 -> exists a. step a d0 == d1 
//Many steps of the db evolution
let db_evolves : preorder db = R.closure db_single_step

//Now you can already do proofs on the db_evolves relation
//showing that it we never order more than the inventory etc.
//or fulfill more than the pending orders etc.

//the type of a db query & guard, & update
let query (a:Type) = db -> a
let guard = db -> bool
//an update is a legal transition of the db, possibly many actions
let update = d0:db -> d1:db {db_evolves d0 d1}
//a transaction is a guard and an update
let tx = (guard & update)

//We'll represent the DB as a single mutable reference to the entire DB
//and a ghost history of the DB as it evolves
//and a lock to protect them both and tie them together
module L = Pulse.Lib.SpinLock
noeq
type db_state = {
  db_ref : ref db; //the actual mutable database
  db_ghost: MR.mref db_evolves; //the ghost history of the database
  db_lock : L.lock
}


//Knowledge that the database d is exactly db
// (with some fraction f, so that this can be shared, though that's not used now)
let db_exactly ([@@@mkey] d:db_state) (db:db)
= MR.pts_to d.db_ghost #1.0R db ** //the ghost state points to some history h
  d.db_ref |-> db

//Knowledge the the database was once db
let db_snapshot ([@@@mkey] d:db_state) (db:db)
= MR.snapshot d.db_ghost db
  
//asserting that the lock of the database is alive (and so usable)
[@@pulse_unfold]
let db_lock (#f:perm) (d:db_state) =  L.lock_alive d.db_lock #f (exists* db. db_exactly d db)

//At any point, you can take a snapshot of exact knowledge of the db
ghost
fn take_snapshot (d:db_state) (#dbval:db)
preserves db_exactly d dbval
ensures db_snapshot d dbval
{
  unfold db_exactly;
  MR.take_snapshot d.db_ghost dbval;
  fold (db_snapshot d dbval);
  fold db_exactly;
}

//Knowing that the databse is now db
//and that it was once db0
//we can conclude that db0 evolved to db
ghost
fn recall_snapshot (d:db_state) (#d0 #d1:db)
preserves db_exactly d d1
preserves db_snapshot d d0
ensures pure (as_prop (db_evolves d0 d1))
{
  unfold db_exactly;
  unfold db_snapshot;
  MR.recall_snapshot d.db_ghost;
  fold (db_snapshot d d0);
  fold db_exactly;
}


//Now to run a query:
fn run_query (#a:Type0) (d:db_state) (#f:perm) (#d0:erased db) (q:query a)
preserves db_lock #f d //given that the lock is alive
requires db_snapshot d d0 //and the db was once d0
returns result:a // it returns the query result
ensures 
  exists* d1. 
    db_snapshot d d1 ** ///along with the proof that d0 evolved to d1
    pure (
      db_evolves d0 d1 /\
      result == q d1 //and the result is the query on d1
    )
{
  //In the model: we acquire the lock; run the query; release the lock
  L.acquire d.db_lock;
  recall_snapshot d;
  drop_ (db_snapshot d d0);
  take_snapshot d; //advance the snapshot
  unfold db_exactly;
  let d1 = !d.db_ref;
  let result = q d1;
  fold db_exactly;
  L.release d.db_lock;
  result
}

//Running a transaction
fn run_tx (d:db_state) (tx:tx) (#f:perm) (#d0:erased db)
preserves db_lock #f d //given that the lock is alive
requires db_snapshot d d0  //and the db was once d0
returns b:bool //return whether the transaction succeeded
ensures 
  exists* d2.
    db_snapshot d d2 ** //the db snapshot is d2
    pure (
      exists d1. 
        db_evolves d0 d1 /\  //d0 ~> d1
        db_evolves d1 d2 /\  //d1 ~> d2
        (b == fst tx d1) /\ //and the guard of the transaction is satisfied at d1 iff the transaction succeeds
        (if b then d2 == snd tx d1 else d2 == d1) 
        //and if the transaction succeeds,
        //the db is updated to the update of the transaction,
        //otherwise it stays at d1
    )
{ 
  L.acquire d.db_lock;
  recall_snapshot d;
  drop_ (db_snapshot d d0);
  unfold db_exactly;
  let d1 = !d.db_ref;
  let guard_ok = fst tx d1;
  if guard_ok
  {
    d.db_ref := snd tx d1;
    //advance the ghost state to reflect the update
    MR.update d.db_ghost (snd tx d1);
    fold db_exactly;
    take_snapshot d;
    L.release d.db_lock;
    true
  }
  else
  {
    fold db_exactly;
    take_snapshot d;
    L.release d.db_lock;
    false
  }
}