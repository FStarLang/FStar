
let profiling: bool ref = ref false

exception ProfilingException of string

type time = float
type counter = {name:string; total_time:time ref; nstarts:int ref; started_at:time ref;}
type ctrmap = (string, counter) BatHashtbl.t
type profiler = {name:string; counters: ctrmap}

let stack:profiler list ref = ref []

let empty_stack () =
  match !stack with | [] -> true | _ -> false

let cur_counters () = 
  match !stack with
  | hd::tl -> hd.counters
  | _ -> failwith "empty stack"

let find_counter (m: ctrmap) n =
  BatHashtbl.find_option m n

let now () = BatUnix.gettimeofday ()

let new_counter counters name =
  match find_counter counters name with
    | Some _ -> ()
    | None ->
        let ctr = {name=name; total_time= ref 0.0; nstarts=ref 0; started_at=ref (now())} in
        BatHashtbl.add counters name ctr

let rec add_counter counters elapsed name =
  match find_counter counters name with
    | Some ctr ->
        ctr.total_time := elapsed +. !(ctr.total_time)
    | None ->
        new_counter counters name;
        add_counter counters elapsed name

let rec start_counter counters name =
  match find_counter counters name with
    | Some ctr ->
        incr ctr.nstarts;
        if !(ctr.nstarts) = 1 then ctr.started_at := now()
    | None -> new_counter counters name; start_counter counters name

let stop_counter counters name =
  match find_counter counters name with
    | Some ctr ->
        decr ctr.nstarts;
        if !(ctr.nstarts) < 0 then raise (ProfilingException ("Starts and ends on counter "^name^" don't match up"));
        if !(ctr.nstarts) = 0 then
          let elapsed = now() -. !(ctr.started_at) in
            ctr.total_time := elapsed +. !(ctr.total_time);
            Some elapsed
        else None
    | None -> raise (ProfilingException ("Counter " ^name^ " does not exist"))

let push_stack p =
  stack := p::!stack

let start_profile s =
  let p = {name=s; counters=BatHashtbl.create(10)} in 
  push_stack p;
  p

let propogate_profile_info p =
  if (not (empty_stack())) then
    let counters = cur_counters () in
    let c = p.counters in
    (* propogate profile info from counter 'c' up the stack to the next level *)
    let all_keys_vals = BatHashtbl.to_list c in 
    all_keys_vals |> List.map (fun (k,v) -> add_counter counters !(v.total_time) k) |> ignore

let pop_stack  () =
  match !stack with
  | c::tl ->
    stack := tl;
    c
  | _ -> failwith "Impossible: Too many pops"

let print_profile p =
  let counters = p.counters in
  let name = p.name in
  let ctr2string (ctr:counter) =
    let n = 1 in
    let rec mk_pad out n = if n = 0 then out else mk_pad (" " ^ out) (n - 1) in
    let pad = mk_pad "" n in
    Printf.sprintf "%s:%s\t %sms " ctr.name pad (string_of_int (int_of_float (!(ctr.total_time)))) in
  let all_ctrs = BatHashtbl.to_list counters |> List.map snd in
  let output = List.fold_left
    (fun accum c ->
      if !(c.nstarts) > 0 then Printf.printf "Warning: counter %s is unreliable; %d starts were not stopped\n" c.name !(c.nstarts);
      accum ^ (ctr2string c)) (name ^ ": ") all_ctrs in
  Printf.printf "%s\n" output

let stop_profile name: profiler =
  let p = pop_stack () in
  if not (p.name = name) then 
    failwith "stack not matching";
  propogate_profile_info p;
  p

let profile' f name ctrname printout = 
  let counters = (start_profile name).counters in
  try
    let _ = start_counter counters ctrname in
    let result = f () in
    let time = match stop_counter counters ctrname with
      | Some elapsed -> add_counter counters elapsed ctrname; Z.of_float (elapsed *. 1000.0)
      | _ -> Z.of_float 0.0 in
    let p = stop_profile name in
    if printout then
      print_profile p; 
    result, time
  with
    e (* when (stop_counter counters ctrname; false) *) -> raise e
let profile f name ctrname printout =
  if !profiling then profile' f name ctrname printout else FStar_Util.record_time f

let init_profiler _ = 
  profiling := true

let disable_profiler _ = 
  profiling := false

