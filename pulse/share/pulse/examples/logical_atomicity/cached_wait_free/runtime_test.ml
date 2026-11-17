(**
   Handwritten extraction regressions, not a proof over all schedules.
   Every domain uses the verified shared wrappers. Native construction
   respects erased preconditions: immutable nodes, a distinct desired-node
   ticket for each changing CAS, and no reuse of a published identity.
*)

module C = CachedWF
let a = C.pulse_Lib_LogicalAtomicity_Example_CachedWaitFree_Clients_a
let b = C.pulse_Lib_LogicalAtomicity_Example_CachedWaitFree_Clients_b
let c = C.pulse_Lib_LogicalAtomicity_Example_CachedWaitFree_Clients_c
let create cells = C.pulse_Lib_LogicalAtomicity_Example_CachedWaitFree_State_create cells Prims.int_zero
let read cells q = C.pulse_Lib_LogicalAtomicity_Example_CachedWaitFree_Clients_read_shared cells q ()
let cas cells q expected node =
  C.pulse_Lib_LogicalAtomicity_Example_CachedWaitFree_Clients_cas_shared cells q expected (Prims.of_int node)
let cas_local cells q expected node =
  C.pulse_Lib_LogicalAtomicity_Example_CachedWaitFree_Clients_cas_shared_local cells q expected (Prims.of_int node)
let check message ok = if not ok then failwith message

let wait message predicate =
  let deadline = Unix.gettimeofday () +. 15. in
  while not (predicate ()) do
    if Unix.gettimeofday () > deadline then failwith ("timeout: " ^ message);
    Domain.cpu_relax ()
  done

type gate = {
  kind : string;
  at : int;
  target : Domain.id option Atomic.t;
  count : int Atomic.t;
  arrived : bool Atomic.t;
  resume : bool Atomic.t;
}

let gate kind at = {
  kind; at; target = Atomic.make None; count = Atomic.make 0;
  arrived = Atomic.make false; resume = Atomic.make false;
}

let on_event g kind =
  if kind = g.kind && Atomic.get g.target = Some (Domain.self ()) then (
    let n = Atomic.fetch_and_add g.count 1 + 1 in
    if n = g.at then (
      Atomic.set g.arrived true;
      wait "resume paused operation" (fun () -> Atomic.get g.resume)))

let start g f = Domain.spawn (fun () ->
  Atomic.set g.target (Some (Domain.self ()));
  f ())
let arrived g = wait "reach primitive boundary" (fun () -> Atomic.get g.arrived)
let resume g = Atomic.set g.resume true
let with_gates gates f =
  CachedWF_atomics.set_hook (fun kind -> List.iter (fun g -> on_event g kind) gates);
  Fun.protect f ~finally:(fun () ->
    List.iter resume gates;
    CachedWF_atomics.set_hook (fun _ -> ()))

let torn_cache () =
  let cells = [a; b] in
  let q = create cells and r = gate "read" 2 in
  with_gates [r] (fun () ->
    let reader = start r (fun () -> read cells q) in
    arrived r;
    check "publish B during copy" (cas cells q a 1);
    resume r;
    check "reject mixed A.first/B.second" (Domain.join reader = b))

let delayed_writer () =
  let cells = [a; b; c] in
  let q = create cells and w = gate "exchange" 1 in
  with_gates [w] (fun () ->
    let writer = start w (fun () -> cas cells q a 1) in
    arrived w;
    check "marked backup is readable before cache copy" (read cells q = b);
    check "newer writer publishes C" (cas cells q b 2);
    resume w;
    check "old publication succeeded" (Domain.join writer);
    check "old writer cannot overwrite newer cache" (read cells q = c))

let captured_backup () =
  let cells = [a; b; c] in
  let q = create cells and w = gate "exchange" 1 and r = gate "read" 4 in
  with_gates [w; r] (fun () ->
    let writer = start w (fun () -> cas cells q a 1) in
    arrived w;
    let reader = start r (fun () -> read cells q) in
    arrived r;
    check "replace captured backup" (cas cells q b 2);
    resume r;
    check "fallback follows captured B, not fresh C" (Domain.join reader = b);
    resume w;
    check "delayed writer returns" (Domain.join writer);
    check "current value remains C" (read cells q = c))

let unmark_race () =
  let cells = [a; b; c] in
  let q = create cells and w = gate "write" 3 in
  with_gates [w] (fun () ->
    let writer = start w (fun () -> cas cells q a 1) in
    arrived w;
    check "publish after older cache unlock" (cas cells q b 2);
    resume w;
    check "older writer returns after failed unmark" (Domain.join writer);
    check "failed unmark does not validate the wrong node" (read cells q = c))

let second_publication_attempt () =
  let cells = [a; b; c] in
  let q = create cells and w = gate "write" 3 and next = gate "read" 4 in
  with_gates [w; next] (fun () ->
    let writer = start w (fun () -> cas cells q a 1) in
    arrived w;
    let follower = start next (fun () -> cas cells q b 2) in
    arrived next;
    resume w;
    check "validate B between observation and CAS" (Domain.join writer);
    resume next;
    check "unmarked-pointer retry succeeds" (Domain.join follower);
    check "second pointer CAS avoided restarting the read" (Atomic.get next.count = 4);
    check "second attempt published C" (read cells q = c))

let aba_helped_failure () =
  let cells = [a; b; a; c] in
  let q = create cells and w = gate "read" 5 in
  with_gates [w] (fun () ->
    let writer = start w (fun () -> cas_local cells q a 3) in
    arrived w;
    check "ABA: A to B" (cas cells q a 1);
    check "ABA: B to fresh A" (cas cells q b 2);
    resume w;
    check "CAS was helped to failure at B, before A returned" (not (Domain.join writer));
    check "helped failure does not restart the read" (Atomic.get w.count = 5);
    check "failed CAS leaves the returned A untouched" (read cells q = a))

let aba_between_attempts () =
  let cells = [a; b; a; c] in
  let q = create cells and r = gate "read" 5 and x = gate "exchange" 1 in
  with_gates [r; x] (fun () ->
    let writer = start r (fun () ->
      Atomic.set x.target (Some (Domain.self ()));
      cas_local cells q a 3) in
    arrived r;
    check "invalidate before first publication attempt" (cas cells q a 1);
    resume r;
    arrived x;
    check "restore A between the two failed attempts" (cas cells q b 2);
    resume x;
    check "second failure returns the saved continuation" (not (Domain.join writer));
    check "exactly two publication attempts" (Atomic.get x.count = 2);
    check "no fresh read between attempts" (Atomic.get r.count = 5);
    check "A remains current" (read cells q = a))

let help_all_pending () =
  let cells = [a; b; a; c; c; c] in
  let q = create cells and gates = List.init 3 (fun _ -> gate "read" 5) in
  with_gates gates (fun () ->
    let writers = List.mapi (fun index g ->
      start g (fun () -> cas_local cells q a (index + 3))) gates in
    List.iter arrived gates;
    check "one publication helps all pending callers" (cas cells q a 1);
    check "completed requests survive a second publication" (cas cells q b 2);
    List.iter resume gates;
    List.iter (fun writer -> check "each pending caller returns failure" (not (Domain.join writer))) writers;
    List.iter (fun g -> check "no helped caller retries its read" (Atomic.get g.count = 5)) gates;
    check "all failures preserve the current value" (read cells q = a))

let race () =
  let cells = [a; b; c] in
  let q = create cells in
  let ready = Atomic.make 0 and go = Atomic.make false in
  let worker node = Domain.spawn (fun () ->
    ignore (Atomic.fetch_and_add ready 1);
    wait "start race" (fun () -> Atomic.get go);
    cas cells q a node) in
  let x = worker 1 and y = worker 2 in
  wait "race workers ready" (fun () -> Atomic.get ready = 2);
  Atomic.set go true;
  let xb = Domain.join x and yb = Domain.join y in
  check "exactly one competing CAS succeeds" (xb <> yb);
  check "read returns the winner's complete pair" (read cells q = if xb then b else c)

let () =
  check "verified owned-state client"
    (C.pulse_Lib_LogicalAtomicity_Example_CachedWaitFree_Clients_sequential () = a);
  torn_cache ();
  delayed_writer ();
  captured_backup ();
  unmark_race ();
  second_publication_attempt ();
  aba_helped_failure ();
  aba_between_attempts ();
  help_all_pending ();
  for _ = 1 to 64 do race () done;
  print_endline "Cached big-atomic extraction tests passed"
