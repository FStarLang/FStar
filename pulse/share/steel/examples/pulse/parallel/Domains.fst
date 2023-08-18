module Domains

open Steel.Memory
open Steel.ST.Effect
open Steel.ST.Util

module Lock = Pulse.Lib.SpinLock
open Pulse.Lib.Pervasives
open Pulse.Lib.Core
module HR = Pulse.Lib.HigherReference


(*
assume val domain : a:Type0 -> (a -> vprop) -> Type0
// should contain (at least):
// 1. the reference where we will put the result
// 2. a lock that gives back the postcondition

assume val joinable :
  #a:Type0 -> #post:(a -> vprop) ->
  domain a post -> vprop
*)

(*
noeq
type par_env = | ParEnv : list task -> par_env
and task = | Task : (ref par_env -> stt nat emp (fun _ -> emp)) -> task
*)

//let unit_emp_stt_pure_pure a p
//  = unit -> stt a emp (fun x -> pure (p x))
  // depends negatively on par_env

let maybe_sat #a (p: a -> prop) (x: option a)
  = match x with
  | None -> True
  | Some x -> p x

// TODO: Once it is possible, we should have an SL pre and post
let task_elem = (
  a: Type0 // return type of the computation
  & p: (a -> prop) // postcondition about the return value
  & (unit_emp_stt_pure_pure a p) // the computation
  & r: ref (option a) // the reference where we put the result of the computation
  & Lock.lock (exists_ (fun v -> pts_to r v ** pure (maybe_sat p v)))
)
// depends negatively on par_env

let task_queue: Type u#1 = list task_elem
// depends negatively on par_env

let inv_task_queue
  (q: HR.ref task_queue) // the task queue
  (c: ref int) // a counter of how many tasks are currently being performed
  : vprop
= (exists_ (fun vq -> exists_ (fun vc ->
    HR.pts_to q vq **
    pts_to c vc)))
// depends postivitely on task_queue
// depends negatively on par_env

let par_env = (q: HR.ref task_queue & c: ref int & Lock.lock (inv_task_queue q c))
// if lock depends positively on the vprop
// then it depends negatively

let get_queue (p: par_env): HR.ref task_queue
  = p._1

let get_counter (p: par_env): ref int
  = p._2

let get_lock (p: par_env): Lock.lock (inv_task_queue (get_queue p) (get_counter p))
  = p._3

let create_task_elem #a p f r l: task_elem
  = (| a, p, f, r, l |)

assume
val higher_alloc (#a:Type) (x:a)
  : stt (HR.ref a) emp (fun r -> HR.pts_to r x)
//= admit()
//= (fun _ -> let x = HR.alloc x in return x)

assume
val higher_free (#a:Type) (r: HR.ref a)
  : stt unit (exists_ (fun v -> HR.pts_to r v)) (fun _ -> emp)

assume
val higher_read (#a:Type)
         (#p:perm)
         (#v:Ghost.erased a)
         (r:HR.ref a)
  : stt a
      (HR.pts_to r #p v)
      (fun x -> HR.pts_to r #p v ** pure (x == Ghost.reveal v))
      //(requires true)
//      (ensures fun x -> x == Ghost.reveal v)

assume val higher_write (#a:Type)
          (#v:Ghost.erased a)
          (r:HR.ref a)
          (x:a)
  : stt unit
      (HR.pts_to r v)
      (fun _ -> HR.pts_to r x)


let enqueue (t: task_elem) (q: task_queue): task_queue
  = t::q

```pulse
fn acquire_queue_lock
  (p: par_env)
  //(#q: HR.ref task_queue) (#c: ref int)
  //(l: Lock.lock (inv_task_queue q c))
  requires emp
  ensures (exists vq vc. HR.pts_to (get_queue p) vq ** pts_to (get_counter p) vc)
{
  Lock.acquire (get_lock p);
  unfold (inv_task_queue (get_queue p) (get_counter p));
  ()
}
```

```pulse
fn release_queue_lock
  //(#q: HR.ref task_queue) (#c: ref int)
  //(l: Lock.lock (inv_task_queue q c))
  (p: par_env)
  requires (exists vq vc. HR.pts_to (get_queue p) vq ** pts_to (get_counter p) vc)
  ensures emp
{
  fold (inv_task_queue (get_queue p) (get_counter p));
  Lock.release (get_lock p);
  ()
}
```

let ref_ownership r: vprop
  = exists_ (fun v -> pts_to r v)


let pure_handler #a (post: a -> prop)
  = (res: ref (option a) & Lock.lock (exists_ (fun v -> pts_to res v ** pure (maybe_sat post v))))

let mk_pure_handler #a (p: a -> prop) (r: ref (option a)) (l: Lock.lock (exists_ (fun v -> pts_to r v ** pure (maybe_sat p v))))
 : pure_handler p //(res: ref (option a) & Lock.lock (exists_ (fun v -> pts_to res v ** pure (maybe_sat p v))))
= (| r, l |)

```pulse
fn spawn_emp'
  (#a:Type0)
  //(#post : (a -> vprop))
  //(#q: HR.ref task_queue) (#c: ref int)
  (p: par_env) // par_env'
  (post: (a -> prop))
  //(l: Lock.lock (inv_task_queue q c))
  (f : (par_env -> unit_emp_stt_pure_pure a post))
 requires emp // requires prop?
 returns r: pure_handler post //(res: ref (option a) & Lock.lock (exists_ (fun v -> pts_to res v ** pure (maybe_sat post v))))
  //Lock.lock
 ensures emp
{
  let res = Pulse.Lib.Reference.alloc #(option a) None;
  let l_res = Lock.new_lock (exists_ (fun v -> pts_to res v ** pure (maybe_sat post v)));
  let task = create_task_elem #a post (f p) res l_res;

  acquire_queue_lock p;

  with vq. assert (HR.pts_to (get_queue p) vq);
  let vq = higher_read #_ #full_perm #vq (get_queue p);
  higher_write #_ #vq (get_queue p) (enqueue task vq);

  release_queue_lock p;

  let r = mk_pure_handler post res l_res;
  r
}
```

let spawn_emp = spawn_emp'

assume val share (#a:Type0) (r:ref a) (#v:a) (#p:perm)
  : stt unit
      (pts_to r #p v)
      (fun _ ->
       pts_to r #(half_perm p) v **
       pts_to r #(half_perm p) v)

assume val gather (#a:Type0) (r:ref a) (#x0 #x1:a) (#p0 #p1:perm)
  : stt unit
      (pts_to r #p0 x0 ** pts_to r #p1 x1)
      (fun _ -> pts_to r #(sum_perm p0 p1) x0 ** pure (x0 == x1))

let half = half_perm


assume val free_ref (#a:Type) (r: ref a)
 //(x:a)
  : stt unit
  (exists_ (fun v -> pts_to r v))
  (fun _ -> emp)
  


```pulse
fn join_emp'
  (#a:Type0)
  (#post: (a -> prop))
  //(#q: HR.ref task_queue) (#c: ref int)
  //(l: Lock.lock (inv_task_queue q c))
  //(p: par_env)
  (h: pure_handler post)
 requires emp
 returns res: a
 ensures pure (post res)
{
  let r = Pulse.Lib.Reference.alloc #(option a) None;
  while (let res = !r; None? res)
    invariant b. (exists res. pts_to r res ** pure (b == None? res)
    ** pure (maybe_sat post res))
  {
    Lock.acquire h._2;
    let new_res = !h._1;
    r := new_res;
    Lock.release h._2;
    // TODO: if None? res then check whether the task we're waiting on is in the queue
    ()
  };
  let res = !r;
  free_ref r;
  Some?.v res
}
```

let join_emp = join_emp'


let len (q: task_queue): nat
= List.Tot.length q

let pop (q: task_queue{len q > 0}): task_elem & task_queue
= let t::q' = q in (t, q')

assume val assert_prop (p: prop): stt unit (pure p) (fun _ -> emp)

      (*
  a: Type0 // return type of the computation
  & p: (a -> prop) // postcondition about the return value
  & (unit_emp_stt_pure_pure a p) // the computation
  & r: ref (option a) // the reference where we put the result of the computation
  & Lock.lock (exists_ (fun v -> pts_to r v ** pure (maybe_sat p v)))
      *)

let perform_task (t: task_elem): stt (t._1) emp (fun x -> pure (t._2 x))
= t._3 ()

(*
let perform_task (t: task_elem):
  (res:task._1)
= task._3 ()
*)
let get_ref_res (t: task_elem): ref (option t._1) = t._4

```pulse
fn write_res (t: task_elem) (res: t._1)
  requires pure (t._2 res)
  ensures emp
{
  Lock.acquire t._5;
  (t._4) := Some res;
  Lock.release t._5;
  ()
}
```

```pulse
fn decrease_counter (p: par_env)// (#q: HR.ref task_queue) (#c: ref int) (l: Lock.lock (inv_task_queue q c))
  requires emp
  ensures emp
{
  acquire_queue_lock p;
  let vc = !(get_counter p);
  (get_counter p) := vc - 1;
  release_queue_lock p;
  ()
}
```

```pulse
fn worker' //(#q: HR.ref task_queue) (#c: ref int) (l: Lock.lock (inv_task_queue q c))
  (p: par_env)
  requires emp
  ensures emp
{

  let r_working = alloc #bool true;
  
  while (let working = !r_working; working)
    invariant b. (exists w. pts_to r_working w ** pure (b == w))
  {
    acquire_queue_lock p;

    with vq. assert (HR.pts_to (get_queue p) vq);
    let vq = higher_read #_ #full_perm #vq (get_queue p);
    let vc = !(get_counter p);

    // We check whether there's a task in the queue
    if (len vq > 0) {
      // 1. pop the task and increase counter
      let pair = pop vq;
      (get_counter p) := vc + 1;
      higher_write #_ #vq (get_queue p) (pair._2);
      release_queue_lock p;
      let task = pair._1;

      // 2. perform the task
      let res = perform_task task; // (task._3) (); // Actually performing the task

      // 3. put the result in the reference
      write_res task res;

      // 4. decrease counter
      decrease_counter p;
      ()
    }
    else {
      release_queue_lock p;
      r_working := (vc > 0); // we continue working if and only if some task is still running...
      ()
    }
  };
  free_ref r_working;
  ()
}
```
let worker = worker'

let empty_task_queue: task_queue = []

let mk_par_env q c l: par_env = (| q, c, l |)

```pulse
fn init_par_env' (_: unit)
  requires emp
  returns p: par_env
  ensures emp
{
  // creating parallel env
  let work_queue = higher_alloc empty_task_queue;
  let counter = alloc 0;
  fold (inv_task_queue work_queue counter);
  assert (inv_task_queue work_queue counter);
  let lock = Lock.new_lock (inv_task_queue work_queue counter);
  let p = mk_par_env work_queue counter lock;
  p
}
```

let init_par_env = init_par_env'

let typed_id a (x:a): a = x

```pulse
fn par_block_pulse_emp' (#a: Type0)
  (#post: (a -> (prop)))
  (main_block: (par_env -> (unit_emp_stt_pure_pure a post)))
  requires emp
  returns res: a
  ensures pure (post res)
{
  let p = init_par_env ();
  // adding the main task to the queue
  let main_pure_handler = spawn_emp p post main_block;

  parallel
    requires (emp) and (emp)
    ensures (emp) and (emp)
  {
    worker p
  }
  {
    worker p
  };

  // joining main task
  let res = join_emp' #a #post main_pure_handler; // needs more typing info, from interface
  res
}
```

let par_block_pulse_emp = par_block_pulse_emp'




// Using the previous interface to have resourceful tasks

let resourceful_res #a post = (x:a & Lock.lock (post x))

let unit_stt a pre post = (unit -> stt a pre post)

let exec_unit_stt #a #pre #post
  (f : unit_stt a pre post)
: stt a pre (fun y -> post y)
= sub_stt _ _ (vprop_equiv_refl _) (intro_vprop_post_equiv _ _ (fun _ -> vprop_equiv_refl _)) (f ())

let mk_resourceful_res #a #post (x: a) (l: Lock.lock (post x)):
  resourceful_res post
= (| x, l |)

#set-options "--debug Domains --debug_level st_app --print_implicits --print_universes --print_full_names"

```pulse
fn lockify_vprops
  (#a:Type0)
  (#pre: vprop)
  (#post : (a -> vprop))
  //(#q: HR.ref task_queue) (#c: ref int)
  //(l: Lock.lock (inv_task_queue q c))
  //(f : (unit -> (stt a pre post)))
  (f: (par_env -> unit_stt a pre post))
  (lpre: Lock.lock pre)
  (p: par_env)
  (_: unit)
  requires emp
  returns res: (resourceful_res post)
    //x:a & Lock.lock (post x))
  ensures pure (true)
{
  Lock.acquire lpre;
  // we own the pre
  let y = f p;
  let x = exec_unit_stt y;
  // we own post x
  let l = Lock.new_lock (post x);
  let res = mk_resourceful_res x l;
  res
}
```

let maybe_sat_vprop #a (p: a -> vprop) (x: option a)
  = match x with
  | None -> emp
  | Some x -> p x

let handler (#a: Type0) (post: a -> vprop)
  = pure_handler #(resourceful_res post) (fun (_: resourceful_res post) -> true)

(*
// let's get rid? of the lock
// and use invariants instead

let pure_handler #a (post: a -> prop)
  = (res: ref (option a) & Lock.lock (exists_ (fun v -> pts_to res v ** pure (maybe_sat post v))))

let resourceful_res #a post = (x:a & Lock.lock (post x))

let handler (#a: Type0) (post: a -> vprop)
  = pure_handler #(resourceful_res post) (fun (_: resourceful_res post) -> true)

handler, now:
- reference to option (result and lock with the postcondition)
- lock with full permission over this full reference

what we want:
- ref bool: done?
- ref bool: resources claimed?
- lock (invariant, really) with
- 1/2 done * 1/2 claimed * (done ==> 1/2 ref_res)
* (done && !claimed ==> post x)

The other 1/2 of done is in the end in finished...
The other 1/2 of claimed is in promise or joined (with false)
The other half of ref_res is ???
*)


```pulse
fn spawn'
  (#a:Type0)
  (#pre: vprop)
  (#post : (a -> vprop))
  //(#q: HR.ref task_queue) (#c: ref int)
  //(l: Lock.lock (inv_task_queue q c))
  (p: par_env)
  (f : (par_env -> unit -> stt a pre post))
 requires pre
 returns r: handler post
 // let's think about what we return
 ensures emp
{
  // we create a lock for the precondition
  let lpre = Lock.new_lock pre;
  let h = spawn_emp #(resourceful_res post) p (fun _ -> true) (lockify_vprops f lpre); //(fun _ -> lockify_vprops f lpre);
  h
}
```

let spawn #a #pre #post = spawn' #a #pre #post

```pulse
fn join'
  (#a:Type0)
  (#post: (a -> vprop))
  //(#q: HR.ref task_queue) (#c: ref int)
  //(l: Lock.lock (inv_task_queue q c))
  (h: handler post)
 requires emp
 returns res: a
 ensures post res
{
  let x = join_emp h;
  // x has type resourceful_res pot = (x:a & Lock.lock (post x))
  Lock.acquire x._2;
  x._1
}
```

let join #a #post = join' #a #post

```pulse
fn par_block_pulse' (#a: Type0) (#pre: vprop)
  (#post: (a -> vprop))
  (main_block: (par_env -> unit -> (stt a pre post)))
  requires pre
  returns res: a
  ensures post res
{
  let p = init_par_env ();
  // adding the main task to the queue
  let main_handler = spawn p main_block;

  parallel
    requires (emp) and (emp)
    ensures (emp) and (emp)
  {
    worker p
  }
  {
    worker p
  };

  // joining main task
  let res = join main_handler; // needs more typing info, from interface
  res
}
```

let par_block_pulse #a #pre #post = par_block_pulse' #a #pre #post

```pulse 
fn double (#n: nat) (r:ref nat)
  requires pts_to r n
  returns res:nat
  ensures pts_to r n ** pure (res = n + n)
{
  let vr = !r;
  let x = vr + vr;
  x
}
```

let promote_seq #a #pre #post
  (f: stt a pre post)
: par_env -> unit -> stt a pre post
= (fun _ -> fun _ -> f)

```pulse
fn add_double (#na #nb: nat) (a b: ref nat)
  (p: par_env)
  (_: unit)
  requires pts_to a na ** pts_to b nb
  returns res:nat
  ensures pts_to b nb ** pure (res = na + na + nb + nb)
{
  let aa_t = spawn p (promote_seq (double #na a));
  let bb_t = spawn p (promote_seq (double #nb b));
  let aa = join aa_t;
  let bb = join bb_t;
  let x = aa + bb;
  free_ref a;
  x
}
```

```pulse
fn par_add_double
  (a b: nat)
  requires emp
  returns r:nat
  //returns r:nat
  ensures pure (r = a + a + b + b)
{
  let a' = alloc a;
  let b' = alloc b;
  let x = par_block_pulse' (add_double #a #b a' b');
  free_ref b';
  x
}
```

let combine_posts #a #b
  (post1: a -> vprop) (post2: b -> vprop)
: (a & b) -> vprop
= (fun r -> post1 r._1 ** post2 r._2)

(*
TODO:
- Define promise list (vprop)
- Function that takes a list of elems of some type,
and returns a

e.g.,
[int, unit, nat]
f: 
*)
