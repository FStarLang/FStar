(**
   Native regressions for the verified lock-coupling set.

   The harness is handwritten, not verified. It respects key bounds, the
   producer's strictly sequential cursor, and the consumer's exclusive
   tombstone ownership. Unrestricted races use Shared, not the private-model
   wrapper. Node synchronization is Pulse.Lib.SpinLock's existing Mutex backend;
   plain link accesses are always protected by their node locks.

   Small histories are exhaustively checked for a legal set linearization
   respecting recorded real-time precedence. This checks those executions,
   not every schedule or a weak-memory model. One task pool is reused because
   logical pool teardown does not terminate the library's native workers.
*)

module C = SetConcurrent
module U = SetShared

let n = Prims.of_int
let create = U.pulse_Lib_LogicalAtomicity_Example_ConcurrentSet_Shared_create
let call = U.pulse_Lib_LogicalAtomicity_Example_ConcurrentSet_Shared_perform
let produce = C.pulse_Lib_LogicalAtomicity_Example_ConcurrentSet_Concurrent_produce
let remove = C.pulse_Lib_LogicalAtomicity_Example_ConcurrentSet_Concurrent_try_remove
let remove_again = C.pulse_Lib_LogicalAtomicity_Example_ConcurrentSet_Concurrent_remove_again

type op = Add | Remove | Contains

let perform set op key =
  let extracted = match op with
    | Add -> U.Pulse_Lib_LogicalAtomicity_Example_ConcurrentSet_Model_Add
    | Remove -> U.Pulse_Lib_LogicalAtomicity_Example_ConcurrentSet_Model_Remove
    | Contains -> U.Pulse_Lib_LogicalAtomicity_Example_ConcurrentSet_Model_Contains
  in
  call set extracted (n key)

(** The producer completes its next insertions between the two removals. *)
let forced_interference () =
  let c = C.pulse_Lib_LogicalAtomicity_Example_ConcurrentSet_Concurrent_create (n 4) in
  assert (produce c (n 1));
  assert (remove c (n 1));
  let producer = Domain.spawn (fun () ->
    for key = 2 to 4 do assert (produce c (n key)) done) in
  Domain.join producer;
  assert (not (remove_again c (n 1)));
  assert (not (remove c (n 1)));
  let future = C.pulse_Lib_LogicalAtomicity_Example_ConcurrentSet_Concurrent_create (n 3) in
  assert (not (remove future (n 3)));
  for key = 1 to 3 do assert (produce future (n key)) done;
  assert (remove future (n 3));
  assert (not (remove_again future (n 3)))

(** Insertion before node 2 can complete while node 2 itself is locked. *)
let locked_successor () =
  let set = create (n 4) in
  assert (perform set Add 2);
  assert (perform set Add 4);
  ignore (U.pulse_Lib_LogicalAtomicity_Example_ConcurrentSet_Storage_acquire set (n 2));
  Fun.protect
    ~finally:(fun () ->
      U.pulse_Lib_LogicalAtomicity_Example_ConcurrentSet_Storage_release set (n 2))
    (fun () -> assert (perform set Add 1));
  assert (perform set Contains 1)

(** Release every worker from a barrier, then join every native domain. *)
let race count f =
  let ready = Atomic.make 0 and start = Atomic.make false in
  let workers = List.init count (fun id -> Domain.spawn (fun () ->
    ignore (Atomic.fetch_and_add ready 1);
    while not (Atomic.get start) do Domain.cpu_relax () done;
    f id)) in
  while Atomic.get ready <> count do Domain.cpu_relax () done;
  Atomic.set start true;
  List.map Domain.join workers

(** Duplicate add/remove races exercise the same reusable nodes repeatedly. *)
let reuse_races () =
  let set = create (n 8) in
  for round = 0 to 31 do
    let key = 1 + round mod 8 in
    let count results = List.fold_left (fun n b -> n + if b then 1 else 0) 0 results in
    assert (count (race 4 (fun _ -> perform set Add key)) = 1);
    assert (perform set Contains key);
    assert (count (race 4 (fun _ -> perform set Remove key)) = 1);
    assert (not (perform set Contains key))
  done

type event = { op: op; key: int; result: bool; started: int; finished: int }

(** Backtracking respects every completed-before-started edge. Memoization
retains both placed-event mask and abstract set, not just the event order. *)
let linearizable history =
  let events = Array.of_list history in
  let count = Array.length events in
  assert (count < Sys.int_size - 1);
  let all = (1 lsl count) - 1 in
  let predecessors = Array.init count (fun i ->
    Array.fold_left (fun (j, mask) event ->
      j + 1, if event.finished < events.(i).started then mask lor (1 lsl j) else mask)
      (0, 0) events |> snd) in
  let rejected = Hashtbl.create 64 in
  let rec search placed members =
    if placed = all then true
    else if Hashtbl.mem rejected (placed, members) then false
    else
      let rec choose i =
        if i = count then (Hashtbl.add rejected (placed, members) (); false)
        else if placed land (1 lsl i) <> 0 ||
                predecessors.(i) land placed <> predecessors.(i) then choose (i + 1)
        else
          let event = events.(i) in
          let bit = 1 lsl event.key in
          let present = members land bit <> 0 in
          let expected, after = match event.op with
            | Add -> not present, members lor bit
            | Remove -> present, members land (lnot bit)
            | Contains -> present, members
          in
          (event.result = expected && search (placed lor (1 lsl i)) after) ||
          choose (i + 1)
      in
      choose 0
  in
  search 0 0

(** Reject a history that cannot be explained even by reordering overlapping calls. *)
let check_history_oracle () =
  let a = { op = Add; key = 1; result = true; started = 0; finished = 3 } in
  let b = { op = Add; key = 1; result = true; started = 1; finished = 2 } in
  assert (not (linearizable [a; b]));
  assert (linearizable [a; { b with result = false }]);
  assert (not (linearizable [{ a with op = Contains }]))

(** Nine racing operations plus final membership observations, over three keys.
The final observations are part of the checked history, not a separate oracle. *)
let history_batch seed =
  let set = create (n 3) in
  let clock = Atomic.make 0 in
  let record op key =
    let started = Atomic.fetch_and_add clock 1 in
    let result = perform set op key in
    let finished = Atomic.fetch_and_add clock 1 in
    { op; key; result; started; finished }
  in
  let histories = race 3 (fun worker ->
    List.init 3 (fun step ->
      let op = match (seed + worker + step) mod 3 with
        | 0 -> Add | 1 -> Remove | _ -> Contains in
      let key = 1 + (seed / 3 + worker + 2 * step) mod 3 in
      Domain.cpu_relax ();
      record op key)) in
  let final = List.init 3 (fun k -> record Contains (k + 1)) in
  let history = List.concat histories @ final in
  if not (linearizable history) then begin
    let describe e =
      let op = match e.op with Add -> "add" | Remove -> "remove" | Contains -> "contains" in
      Printf.sprintf "%s %d -> %b [%d,%d]" op e.key e.result e.started e.finished in
    failwith (Printf.sprintf "Nonlinearizable concurrent-set history, seed %d:\n%s"
      seed (String.concat "\n" (List.map describe history)))
  end

let () =
  let _, ok = SetClients.pulse_Lib_LogicalAtomicity_Example_ConcurrentSet_Clients_sequential () in
  assert ok;
  forced_interference ();
  locked_successor ();
  reuse_races ();
  check_history_oracle ();
  for seed = 0 to 63 do history_batch seed done;
  let pool = C.pulse_Lib_Task_setup_pool (n 2) in
  for run = 1 to 32 do
    let _, violation =
      C.pulse_Lib_LogicalAtomicity_Example_ConcurrentSet_Concurrent_run_in_pool pool (n (1 + run mod 32)) in
    assert (not violation)
  done;
  C.pulse_Lib_Task_teardown_pool pool;
  print_endline "Concurrent set: sequential, interference, reuse, 64 histories, 32 verified task runs passed"
