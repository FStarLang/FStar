(* This is a quick-and-dirty wrapper over Domainslib.Task
   that makes teardown_pool wait until all tasks have finished,
   instead of being unspecified in that case. *)

module T = Domainslib.Task
module CV = Condition
open Either

let dbg s = print_string (s ^ "\n"); flush stdout

type 'a task = 'a T.task

type !'a promise = 'a T.promise

type pool = {
    p   : T.pool;
    m : Mutex.t;
    ctr : int ref;
    cv : CV.t;
}

let setup_pool num_domains =
    let p = T.setup_pool ~num_domains () in
    let ctr = ref 0 in
    let m = Mutex.create () in
    let cv = CV.create () in
    { p; m; ctr; cv }

let rec wait_for_empty p =
    if !(p.ctr) <> 0 then (
        CV.wait p.cv p.m;
        wait_for_empty p
    )

let wrap_task p (t : 'a task) : 'a task = fun () ->
    let r =
        match t () with
        | exception ex -> Left ex
        | v -> Right v
    in
    Mutex.lock p.m;
    p.ctr := !(p.ctr) - 1;
    if !(p.ctr) = 0 then
        CV.broadcast p.cv;
    Mutex.unlock p.m;
    match r with
    | Left ex -> raise ex (* this will mess with stack traces, but at least won't deadlock *)
    | Right v -> v

let inc_ctr p =
    Mutex.lock p.m;
    p.ctr := !(p.ctr) + 1;
    (* dbg ("counter now = " ^string_of_int !(p.ctr)); *)
    Mutex.unlock p.m

let async p t =
    inc_ctr p;
    T.async p.p (wrap_task p t)

let await p h =
    T.await p.p h

let await_pool p () () () =
    (* dbg "await_pool.1"; *)
    Mutex.lock p.m;
    (* dbg "await_pool.2"; *)
    wait_for_empty p;
    (* dbg "await_pool.3"; *)
    Mutex.unlock p.m;
    ()

let teardown_pool p =
    Mutex.lock p.m;
    wait_for_empty p;
    T.teardown_pool p.p

let spawn_ p () () () f =
    let _ = async p f in
    ()
