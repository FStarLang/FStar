module Domains

open Pulse.Main
open Pulse.Steel.Wrapper
open Steel.Effect.Common

module R = Steel.ST.Reference
module HR = Steel.ST.HigherReference

assume val domain : a:Type0 -> (a -> vprop) -> Type0
// should contain (at least):
// 1. the reference where we will put the result
// 2. a lock that gives back the postcondition

assume val joinable :
  #a:Type0 -> #post:(a -> vprop) ->
  domain a post -> vprop

open Steel.Memory
open Steel.ST.Effect
open Steel.ST.Util

module Lock = Steel.ST.SpinLock

let unit_emp_stt_pure_pure a p
  = unit -> stt a emp (fun x -> pure (p x))

let maybe_sat #a (p: a -> prop) (x: option a)
  = match x with
  | None -> True
  | Some x -> p x

// TODO: Once it is possible, we should have an SL pre and post
let task_elem = (
  a: Type0 // return type of the computation
  & p: (a -> prop) // postcondition about the return value
  & (unit_emp_stt_pure_pure a p) // the computation
  & r: R.ref (option a) // the reference where we put the result of the computation
  & Lock.lock (exists_ (fun v -> R.pts_to r full_perm v `star` pure (maybe_sat p v)))
)

let task_queue: Type u#1 = list task_elem

unfold
let inv_task_queue
  (q: HR.ref task_queue) // the task queue
  (c: R.ref nat) // a counter of how many tasks are currently being performed
  : vprop
= (exists_ (fun vq -> exists_ (fun vc ->
    HR.pts_to q full_perm vq `star`
    R.pts_to c full_perm vc)))

let create_task_elem #a p f r l: task_elem
  = (| a, p, f, r, l |)

assume
val higher_alloc (#a:Type) (x:a)
  : stt (HR.ref a) emp (fun r -> HR.pts_to r full_perm x)
//= admit()
//= (fun _ -> let x = HR.alloc x in return x)

assume
val higher_read (#a:Type)
         (#p:perm)
         (#v:Ghost.erased a)
         (r:HR.ref a)
  : stt a
      (HR.pts_to r p v)
      (fun x -> HR.pts_to r p v `star` pure (x == Ghost.reveal v))
      //(requires true)
//      (ensures fun x -> x == Ghost.reveal v)

assume val higher_write (#a:Type)
          (#v:Ghost.erased a)
          (r:HR.ref a)
          (x:a)
  : stt unit
      (HR.pts_to r full_perm v)
      (fun _ -> HR.pts_to r full_perm x)


let enqueue (t: task_elem) (q: task_queue): task_queue
  = t::q

```pulse
fn acquire_queue_lock
  (#q: HR.ref task_queue) (#c: R.ref nat)
  (l: Lock.lock (inv_task_queue q c))
  requires emp
  ensures (exists vq vc. HR.pts_to q full_perm vq ** R.pts_to c full_perm vc)
{
  acquire l;
  rewrite (inv_task_queue q c) as (exists vq vc. HR.pts_to q full_perm vq ** R.pts_to c full_perm vc);
  ()
}
```

```pulse
fn release_queue_lock
  (#q: HR.ref task_queue) (#c: R.ref nat)
  (l: Lock.lock (inv_task_queue q c))
  requires (exists vq vc. HR.pts_to q full_perm vq ** R.pts_to c full_perm vc)
  ensures emp
{
  rewrite (exists vq vc. HR.pts_to q full_perm vq ** R.pts_to c full_perm vc) as (inv_task_queue q c);
  release l;
  ()
}
```

let ref_ownership r: vprop
  = exists_ (fun v -> R.pts_to r full_perm v)


let handler #a (post: a -> prop)
  = (res: R.ref (option a) & Lock.lock (exists_ (fun v -> R.pts_to res full_perm v `star` pure (maybe_sat post v))))

let mk_handler #a (p: a -> prop) (r: R.ref (option a)) (l: Lock.lock (exists_ (fun v -> R.pts_to r full_perm v `star` pure (maybe_sat p v))))
 : handler p //(res: R.ref (option a) & Lock.lock (exists_ (fun v -> R.pts_to res full_perm v `star` pure (maybe_sat p v))))
= (| r, l |)

```pulse
fn spawn_emp
  (#a:Type0)
  //(#post : (a -> vprop))
  (post: (a -> prop))
  (#q: HR.ref task_queue) (#c: R.ref nat)
  (l: Lock.lock (inv_task_queue q c))
  (f : unit_emp_stt_pure_pure a post)
 requires emp // requires prop?
 returns r: handler post //(res: R.ref (option a) & Lock.lock (exists_ (fun v -> R.pts_to res full_perm v `star` pure (maybe_sat post v))))
  //Lock.lock
 ensures emp
{
  let res = alloc #(option a) None;
  let l_res = new_lock (exists_ (fun v -> R.pts_to res full_perm v `star` pure (maybe_sat post v)));
  let task = create_task_elem #a post f res l_res;

  //acquire l;
  //rewrite (inv_task_queue q c) as (exists vq vc. HR.pts_to q full_perm vq ** R.pts_to c full_perm vc);
  acquire_queue_lock l;

  with vq. assert (HR.pts_to q full_perm vq);
  let vq = higher_read #_ #full_perm #vq q;
  higher_write #_ #vq q (enqueue task vq);

  release_queue_lock l;

  let r = mk_handler post res l_res;
  r
}
```

assume val free_ref (#a:Type) (r: R.ref a)
 //(x:a)
  : stt unit
  (exists_ (fun v -> R.pts_to r full_perm v))
  (fun _ -> emp)
  


```pulse
fn join
  (#a:Type0)
  (#post: (a -> prop))
  (#q: HR.ref task_queue) (#c: R.ref nat)
  (l: Lock.lock (inv_task_queue q c))
  (h: handler post)
 requires emp
 returns res: a
 ensures pure (post res)
{
  let r = alloc #(option a) None;
  while (let res = !r; None? res)
    invariant b. (exists res. R.pts_to r full_perm res ** pure (b == None? res)
    ** pure (maybe_sat post res))
  {
    acquire h._2;
    let new_res = !h._1;
    r := new_res;
    release h._2;
    ()
  };
  let res = !r;
  free_ref r;
  Some?.v res
}
```

 

assume val spawn_model :
 (#a:Type0) -> (#pre : vprop) -> (#post : (a -> vprop)) ->
 ($f : (unit -> stt a pre post)) ->
 stt (domain a post) pre (fun dom -> joinable dom)

assume val join_model :
  (#a:Type0) -> (#post : (a -> vprop)) ->
  d:domain a post ->
  stt a (joinable d) post
  
assume val in_parallel_section : vprop

// invariant on task_queue?
// monotonocity? can be enforced with a witness token
// pure post?
assume val begin_par_block :
  #a:_ -> #pre:_ -> #post:_ ->
  n:nat ->
  (unit -> stt a (in_parallel_section `star` pre) post) ->
  // ^ can maybe take a "blockid" identfying the thread pool?
  // not now at least, since we won't have unscoped sections yet
  stt a pre post

let empty_task_queue: task_queue = []

let inv_queue r: vprop
 = (exists_ (fun q -> HR.pts_to r full_perm q))

#push-options "--z3rlimit 40"

let len (q: task_queue): nat
= List.Tot.length q

let rec nth (q: task_queue) (i: nat{i < len q}): task_elem
= match q with
| t::q' -> if i = 0 then t else nth q' (i - 1)

assume val assume_prop (p: prop): stt unit emp (fun _ -> pure p)

let get_task (task: task_elem): (a:Type & (unit -> stt a emp (fun _ -> emp)))
= let (| a, task, _ |) = task in (| a, task |)

assume val replace_elem (q: task_queue) (i: nat) (t: task_elem): task_queue

```pulse
fn begin_par_block_pulse (#a: Type0)
  (#pre :vprop) (#post: (a -> vprop))
  (main_block: (unit -> stt a pre post))
  requires emp
  ensures emp
{
  let r = higher_alloc empty_task_queue; //([]) in //: R.ref task_queue = magic() in
  let index_task = alloc 0; // points to the next available task
  let lock = new_lock (exists_ (fun q -> exists_ (fun i_task ->
    HR.pts_to r full_perm q `star`
    R.pts_to index_task full_perm i_task `star`
    pure (i_task >= 0 /\ available_from q i_task)
    )));
  parallel
    requires (emp) and (emp)
    ensures (emp) and (emp)
  {
    let x = main_block ();
    () // main thread
  }
  {
    parallel
      requires (emp) and (emp)
      ensures (emp) and (emp)
    {
      while (true)
        invariant tr. emp ** pure (tr == true)
      {
        acquire lock;
        let i_task = !index_task;
        with q. assert (HR.pts_to r full_perm q);
        let vq = higher_read #_ #full_perm #q r;
        //let perform_task = i_task < len vq;
        if (i_task < len vq)
        {
          // get the task
          let task = nth vq i_task;
          // increase index
          index_task := i_task + 1;

          assume_prop (available_from vq (i_task + 1));
          release lock;

          let to_perform = get_task task;
          let res = (to_perform._2) (); // Actually performing the task

          // Finally, we put the result of the task in the queue
          let new_task = Mkdtuple3 task._1 task._2 (Done res);
          acquire lock;

          // Step 2: perform task
          //let (| a, actual_task, _ |) = task;


          release lock;
          ()
        }
        else {
          release lock;
          ()
        }
      };
      () // worker
    }
    {
      () // worker
    };
    ()
  };
  admit()
}
```

  (*
  Code:
  let q: task_queue = [] in
  let l = new_lock in
  parallel (
    parallel (
      ...
    )
  )
  (
    parallel (
      ...
    )
  )
  *)

 (*
 let handler: domain a post = spawn (fun () -> ...)
 consumes precondition
 returns token
the precondition goes into the lock for this particular location...
1) We acquire the *main* lock
2) We add one task to the shared list
--> we need to add
- the actual task (unit -> stt ...)
- the lock (Lock.lock p, where p is a vprop)
- some value that says whether the task is
  1. available
  2. ongoing
  3. finished (with result...)
We allocate a new lock
 *)


  // begin_par_block 16 (fun () ->
  //   let th1 = spawn(..) in
  //   let th2 = spawn(..) in  
  //   join th1 + join th2
  // )

let rec fib0 (n:nat) : nat =
  if n < 2 then n
  else fib0 (n-1) + fib0 (n-2)

// ```pulse
// fn pth (n:pos) (_:unit)
//   requires emp
//   returns r:(r:nat{r == fib0 (n-1)})
//   ensures emp

//   // With this version:
//   //    returns r:nat
//   //    ensures pure (r == fib0 (n-1))
//   // We get:
//   //    cannot prove vprop pure (eq2 (fib0 (op_Subtraction n 1)) (fib0 (op_Subtraction n 1))) in the context: emp
//   //    (the prover was started with goal pure (eq2 (fib0 (op_Subtraction n 1)) (fib0 (op_Subtraction n 1))) and initial context emp)
// {
//   let r = fib0 (n-1);
//   r
// }
// ```

```pulse
fn sfib (n:nat)
  requires emp
  returns r:(r:nat{r == fib0 n})
  ensures emp
{
  admit()
}
```

```pulse
fn pfib (n:nat)
  (cb : (n:nat -> stt (r:nat{r == fib0 n}) emp (fun _ -> emp))) // callback as we don't have recursion
  requires emp
  returns r:(r:nat{r == fib0 n})
  ensures emp
{
  if (n < 20) {
    let r = sfib n;
    r
  } else {
    let r_th = spawn (fun () -> cb (n-1));
    let l = sfib (n-2);
    let r = join r_th;
    let res = l+r;
    res
  }
}
```
