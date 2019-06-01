
let profiling: bool ref = ref false

exception ProfilingException of string

type counter = {total_time: int ref}
type ctrmap = (FStar_Options.profile_t, counter) BatHashtbl.t
type profiler = {pname:string; ptime: int ref; counters: ctrmap}

let stack:profiler list ref = ref []

let cur_counters () = 
  match !stack with
  | hd::tl -> Some (hd.counters)
  | _ -> None

let find_counter (m: ctrmap) n =
  BatHashtbl.find_option m n

let new_counter counters name =
  let ctr = {total_time= ref 0} in
  BatHashtbl.add counters name ctr;
  ctr

let rec add_counter counters name elapsed =
  match find_counter counters name with
    | Some ctr -> ctr.total_time := elapsed + !(ctr.total_time)
    | None ->
        let c = new_counter counters name in
        c.total_time := elapsed

let push_stack p =
  stack := p::!stack

let get_profile s new_level =
  if new_level then
    let p = {pname=s; ptime=ref 0;counters=BatHashtbl.create(10)} in 
    push_stack p;
    Some (p.counters)
  else
    cur_counters()

let propogate_profile_info p =
  match cur_counters() with
  | Some counters ->
    let c = p.counters in
    (* propogate profile info from counter 'c' up the stack to the next level *)
    let all_keys_vals = BatHashtbl.to_list c in 
    all_keys_vals |> List.map (fun (k,v) -> add_counter counters k !(v.total_time)) |> ignore
  | _ -> ()

let pop_stack  () =
  match !stack with
  | c::tl ->
    stack := tl;
    c
  | _ -> failwith "Impossible: Too many pops"

let print_profile p =
  let counters = p.counters in
  let ctr2string name =
    let ctr = 
      match find_counter counters name with 
      | Some ctr -> ctr 
      | _ ->  failwith ("counter for " ^(FStar_Options.profile_name name)^ "not found") in
    Printf.sprintf "%s:\t %sms " (FStar_Options.profile_name name) (string_of_int !(ctr.total_time)) in
  let all_keys = BatHashtbl.to_list counters |> List.map fst in
  let output = List.fold_left
    (fun accum c -> accum ^ (ctr2string c)) (p.pname ^ ": ") all_keys in
  Printf.printf "%s\t total: %sms\n" output (string_of_int !(p.ptime))

let pop_and_print_profiler name elapsed =
  let p = pop_stack () in
  if not (p.pname = name) then failwith "stack not matching";
  p.ptime := elapsed + !(p.ptime);
  propogate_profile_info p;
  print_profile p

let profile' f name phasename new_level new_phase = 
  let counters = get_profile name new_level in
  let (r, elapsed) = FStar_Util.record_time f in
  let ms = Z.to_int elapsed in
  let _ = match counters with
  | Some counters ->
    if new_phase then add_counter counters phasename ms;
    if new_level then pop_and_print_profiler name ms;
  | None -> 
    Printf.printf "%s: %s: %sms\n" name (FStar_Options.profile_name phasename)(string_of_int ms)
  in
  (r, elapsed)

let profile f msg phasename =
  let new_level = FStar_Options.profile_at_level phasename in
  let new_phase = FStar_Options.profile_phase phasename in
  (* Printf.printf "Profiling %s. name %s, phase: %s, new_profiler %s, new_phase %s\n" (string_of_bool !profiling) name (FStar_Options.profile_name phasename) (string_of_bool new_profiler) (string_of_bool new_phase); *)
  if (!profiling && (new_level || new_phase)) then 
    profile' f (msg()) phasename new_level new_phase
  else FStar_Util.record_time f

let init_profiler _ = 
  profiling := true

let disable_profiler _ = 
  profiling := false

