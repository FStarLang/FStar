(**
   Executable regressions for the extracted Michael--Scott FIFO.

   The F* sources prove resource/abstract-state contracts; these tests check
   extraction, native realization, and representative schedules. This OCaml
   harness itself is not verified: erased preconditions (fresh tickets,
   disjoint producer IDs, shared invariant setup) are respected by its test
   construction rather than enforced by OCaml types.

   Sequential checks cover exclusive-payload FIFO recovery. Concurrent checks
   cover a forced delayed-tail schedule, repeated verified four-worker clients,
   and native 4-producer/4-consumer batches.

   Queue primitives use the mutex-backed MSQueue_atomics realization.
   Stress/permutation checks are not an exhaustive linearizability test,
   weak-memory validation, liveness proof, or lock-freedom benchmark. In
   particular, the concurrent F* harness does not itself prove the returned
   value permutation that is checked here.
*)

(** Parse through the extracted integer API to avoid host-int range assumptions. *)
let u32 n = FStar_UInt32.uint_to_t (Prims.parse_int n)

module MQ = MSQueueConcurrent

(** Short alias for the extracted producer; callers assign each ID once. *)
let produce = MQ.pulse_Lib_LogicalAtomicity_Example_MSQueue_Concurrent_produce
(** Short alias for the consumer that retries empty results. *)
let consume = MQ.pulse_Lib_LogicalAtomicity_Example_MSQueue_Concurrent_consume
(** Short alias for a single logical dequeue, which may return None. *)
let try_consume = MQ.pulse_Lib_LogicalAtomicity_Example_MSQueue_Concurrent_try_consume

(** Allocate one dummy and count fresh cells, with ID equal to value. Ghost
   sharing steps erase, so native callers can use the extracted handle
   directly; uniqueness of producer IDs below supplies the ticket discipline. *)
let make_queue count =
  let cells = List.init (count + 1) (fun n ->
    { MQ.next = ref (u32 "4294967295"); value = u32 (string_of_int n) }) in
  let q = MQ.pulse_Lib_LogicalAtomicity_Example_MSQueue_State_create cells () in
  cells, q

(** Pause producer 1 AFTER publication/commit but BEFORE its final tail CAS.
   Producer 2 completes, necessarily helping past that lagging tail. Resume
   producer 1 and check its now-stale maintenance CAS and FIFO contents. *)
let forced_tail_help () =
  let cells, q = make_queue 2 in
  let published = Atomic.make false in
  let resume = Atomic.make false in
  let first = Domain.spawn (fun () ->
    let tail =
      MQ.pulse_Lib_LogicalAtomicity_Example_MSQueue_Concurrent_produce_deferred
        cells q (u32 "1") in
    Atomic.set published true;
    while not (Atomic.get resume) do Domain.cpu_relax () done;
    MQ.pulse_Lib_LogicalAtomicity_Example_MSQueue_Concurrent_finish_produce
      cells q tail (u32 "1")) in
  while not (Atomic.get published) do Domain.cpu_relax () done;
  produce cells q (u32 "2");
  Atomic.set resume true;
  assert (not (Domain.join first));
  assert (try_consume cells q () = Some (u32 "1"));
  assert (try_consume cells q () = Some (u32 "2"));
  assert (try_consume cells q () = None)

(** Four producers use disjoint ID ranges; four consumers each take 16 values.
   Joining all domains establishes completion for the assertions. Sorting
   detects loss/duplication but does not check every concurrent FIFO history. *)
let mpmc_batch () =
  let workers = 4 and per_worker = 16 in
  let cells, q = make_queue (workers * per_worker) in
  let consumers = List.init workers (fun _ ->
    Domain.spawn (fun () -> List.init per_worker (fun _ -> consume cells q ()))) in
  let producers = List.init workers (fun worker ->
    Domain.spawn (fun () ->
      for k = 1 to per_worker do
        produce cells q (u32 (string_of_int (worker * per_worker + k)))
      done)) in
  List.iter Domain.join producers;
  let values = List.concat (List.map Domain.join consumers) in
  let expected = List.init (workers * per_worker) (fun k -> u32 (string_of_int (k + 1))) in
  assert (List.sort compare values = List.sort compare expected);
  assert (try_consume cells q () = None)

(** Run bounded regressions and fail on any violated observation. Native task
   teardown currently leaves workers running, so repeated clients reuse a pool. *)
let () =
  (* Repeat the verified ownership client both normally and with injected
     weak-CAS failures, checking exact payload values after extraction. *)
  let fifo () =
    let a, b =
      MSQueueClients.pulse_Lib_LogicalAtomicity_Example_MSQueue_Clients_fifo_ownership () in
    assert (a = u32 "101" && b = u32 "202") in
  fifo ();
  assert (MSQueueClients.pulse_Lib_LogicalAtomicity_Example_MSQueue_Clients_delayed_tail ());
  assert (MSQueueClients.pulse_Lib_LogicalAtomicity_Example_MSQueue_Clients_stale_tail_retry ());
  forced_tail_help ();
  MSQueue_atomics.fail_next 3;
  fifo ();
  assert (MSQueue_atomics.pending_failures () = 0);
  (* The F* client proves shared access, while these assertions additionally
     check its two-result permutation and final emptiness in each execution. *)
  let pool = MQ.pulse_Lib_Task_setup_pool (Prims.of_int 4) in
  for run = 1 to 64 do
    MSQueue_atomics.fail_next (run mod 5);
    let result =
      MQ.pulse_Lib_LogicalAtomicity_Example_MSQueue_Concurrent_two_producers_two_consumers_in_pool pool in
    let a, b = result.MQ.values, result.MQ.values1 in
    assert ((a = u32 "11" && b = u32 "22") || (a = u32 "22" && b = u32 "11"));
    assert (try_consume result.MQ.cells result.MQ.queue () = None);
    assert (MSQueue_atomics.pending_failures () = 0)
  done;
  MQ.pulse_Lib_Task_teardown_pool pool;
  for run = 1 to 16 do
    MSQueue_atomics.fail_next (run mod 7);
    mpmc_batch ();
    assert (MSQueue_atomics.pending_failures () = 0)
  done;
  print_endline "Michael--Scott queue extraction tests passed"
