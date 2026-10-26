module Echo.Report

(** Result of an echo session, returned to the C caller. *)

type echo_status =
  | EchoClosed      (* peer closed the connection between frames / mid-frame *)
  | EchoMalformed   (* a frame header had length 0 or > max_payload *)
  | EchoBufferFull  (* receive buffer full without a complete frame (unreachable) *)
  | EchoOutOfFuel   (* the read budget was exhausted *)

type echo_report = {
  frames: FStar.UInt64.t;   (* number of frames echoed *)
  status: echo_status;
}
