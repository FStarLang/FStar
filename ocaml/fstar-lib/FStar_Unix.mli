(*
   Copyright 2024 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

   Authors: Brian G. Milnes 
*)

(* Wrapper of OCaml unix.mli minimized code, see the OCaml library for docs. *)

type error =
    E2BIG
  | EACCES
  | EAGAIN
  | EBADF
  | EBUSY
  | ECHILD
  | EDEADLK
  | EDOM
  | EEXIST
  | EFAULT
  | EFBIG
  | EINTR
  | EINVAL
  | EIO
  | EISDIR
  | EMFILE
  | EMLINK
  | ENAMETOOLONG
  | ENFILE
  | ENODEV
  | ENOENT
  | ENOEXEC
  | ENOLCK
  | ENOMEM
  | ENOSPC
  | ENOSYS
  | ENOTDIR
  | ENOTEMPTY
  | ENOTTY
  | ENXIO
  | EPERM
  | EPIPE
  | ERANGE
  | EROFS
  | ESPIPE
  | ESRCH
  | EXDEV
  | EWOULDBLOCK
  | EINPROGRESS
  | EALREADY
  | ENOTSOCK
  | EDESTADDRREQ
  | EMSGSIZE
  | EPROTOTYPE
  | ENOPROTOOPT
  | EPROTONOSUPPORT
  | ESOCKTNOSUPPORT
  | EOPNOTSUPP
  | EPFNOSUPPORT
  | EAFNOSUPPORT
  | EADDRINUSE
  | EADDRNOTAVAIL
  | ENETDOWN
  | ENETUNREACH
  | ENETRESET
  | ECONNABORTED
  | ECONNRESET
  | ENOBUFS
  | EISCONN
  | ENOTCONN
  | ESHUTDOWN
  | ETOOMANYREFS
  | ETIMEDOUT
  | ECONNREFUSED
  | EHOSTDOWN
  | EHOSTUNREACH
  | ELOOP
  | EOVERFLOW
  | EUNKNOWNERR of Z.t

exception Unix_error of error * string * string
val error_message : error -> string
val handle_unix_error : ('a -> 'b) -> 'a -> 'b
val environment : unit -> string array 
val unsafe_environment : unit -> string array 
val getenv : string -> string
val unsafe_getenv : string -> string
val putenv : string -> string -> unit

type process_status = 
    WEXITED of Z.t
  | WSIGNALED of Z.t
  | WSTOPPED of Z.t

type wait_flag = Unix.wait_flag = 
    WNOHANG
  | WUNTRACED

val execv : string -> string array -> 'a 
val execve : string -> string array -> string array -> 'a 
val execvp : string -> string array -> 'a 
val execvpe : string -> string array -> string array -> 'a 
val fork : unit -> Z.t
val wait : unit -> Z.t * process_status
val waitpid : wait_flag list -> Z.t -> Z.t * process_status
val system : string -> process_status
val _exit : Z.t -> 'a
val getpid : unit -> Z.t
val getppid : unit -> Z.t
val nice : Z.t -> Z.t

type file_descr = Unix.file_descr

val stdin  : file_descr
val stdout : file_descr
val stderr : file_descr

type open_flag = Unix.open_flag = 
    O_RDONLY
  | O_WRONLY
  | O_RDWR
  | O_NONBLOCK
  | O_APPEND
  | O_CREAT
  | O_TRUNC
  | O_EXCL
  | O_NOCTTY
  | O_DSYNC
  | O_SYNC
  | O_RSYNC
  | O_SHARE_DELETE
  | O_CLOEXEC
  | O_KEEPEXEC

type file_perm = Z.t

val openfile : string -> open_flag list -> file_perm -> file_descr
val close : file_descr -> unit
val fsync : file_descr -> unit
val read : file_descr -> bytes -> Z.t -> Z.t -> Z.t
val write : file_descr -> bytes -> Z.t -> Z.t -> Z.t
val single_write : file_descr -> bytes -> Z.t -> Z.t -> Z.t
val write_substring : file_descr -> string -> Z.t -> Z.t -> Z.t
val single_write_substring : file_descr -> string -> Z.t -> Z.t -> Z.t
val in_channel_of_descr : file_descr -> in_channel
val out_channel_of_descr : file_descr -> out_channel
val descr_of_in_channel : in_channel -> file_descr
val descr_of_out_channel : out_channel -> file_descr
type seek_command = Unix.seek_command = 
    SEEK_SET
  | SEEK_CUR
  | SEEK_END

val lseek : file_descr -> Z.t -> seek_command -> Z.t
val truncate : string -> Z.t -> unit
val ftruncate : file_descr -> Z.t -> unit

type file_kind = Unix.file_kind = 
    S_REG
  | S_DIR
  | S_CHR
  | S_BLK
  | S_LNK
  | S_FIFO
  | S_SOCK

type stats =
  { st_dev : Z.t;
    st_ino : Z.t;
    st_kind : file_kind;
    st_perm : file_perm;
    st_nlink : Z.t;
    st_uid : Z.t;
    st_gid : Z.t;
    st_rdev : Z.t;
    st_size : Z.t;
    st_atime : float;
    st_mtime : float;
    st_ctime : float;
  }

val stat : string -> stats
val lstat : string -> stats
val fstat : file_descr -> stats
val isatty : file_descr -> bool
val unlink : string -> unit
val rename : string -> string -> unit
val link : string -> string -> unit
val realpath : string -> string

type access_permission = Unix.access_permission = 
    R_OK
  | W_OK
  | X_OK
  | F_OK

val chmod : string -> file_perm -> unit
val fchmod : file_descr -> file_perm -> unit
val chown : string -> Z.t -> Z.t -> unit
val fchown : file_descr -> Z.t -> Z.t -> unit
val umask : file_perm -> file_perm
val access : string -> access_permission list -> unit
val dup : file_descr -> file_descr
val dup2 : file_descr -> file_descr -> unit
val set_nonblock : file_descr -> unit
val clear_nonblock : file_descr -> unit
val set_close_on_exec : file_descr -> unit
val clear_close_on_exec : file_descr -> unit
val mkdir : string -> file_perm -> unit
val rmdir : string -> unit
val chdir : string -> unit
val getcwd : unit -> string
val chroot : string -> unit

type dir_handle
val opendir : string -> dir_handle
val readdir : dir_handle -> string
val rewinddir : dir_handle -> unit
val closedir : dir_handle -> unit
val pipe : unit -> file_descr * file_descr
val mkfifo : string -> file_perm -> unit

val create_process : string -> string array -> file_descr -> file_descr -> file_descr -> Z.t
val create_process_env : string -> string array -> string array -> file_descr -> 
    file_descr -> file_descr -> Z.t 
val open_process_in : string -> in_channel
val open_process_out : string -> out_channel
val open_process : string -> in_channel * out_channel
val open_process_full : string -> string array -> in_channel * out_channel * in_channel
val open_process_args : string -> string array -> in_channel * out_channel
val open_process_args_in : string -> string array -> in_channel
val open_process_args_out : string -> string array -> out_channel
val open_process_args_full : string -> string array -> string array ->
    in_channel * out_channel * in_channel
val process_in_pid : in_channel -> Z.t
val process_out_pid : out_channel -> Z.t
val process_pid : in_channel * out_channel -> Z.t
val process_full_pid : in_channel * out_channel * in_channel -> Z.t
val close_process_in : in_channel -> process_status
val close_process_out : out_channel -> process_status
val close_process : in_channel * out_channel -> process_status
val close_process_full : in_channel * out_channel * in_channel -> process_status
val symlink : string -> string -> unit
val has_symlink : unit -> bool
val readlink : string -> string
val select : file_descr list -> file_descr list -> file_descr list ->
    float -> file_descr list * file_descr list * file_descr list

type lock_command = Unix.lock_command = 
    F_ULOCK
  | F_LOCK
  | F_TLOCK
  | F_TEST
  | F_RLOCK
  | F_TRLOCK

val lockf : file_descr -> lock_command -> Z.t -> unit
val kill :Z.t -> Z.t -> unit

type sigprocmask_command = Unix.sigprocmask_command = 
    SIG_SETMASK
  | SIG_BLOCK
  | SIG_UNBLOCK

val sigprocmask : sigprocmask_command -> Z.t list -> Z.t list
val sigpending : unit -> Z.t list
val sigsuspend :Z.t list -> unit
val pause : unit -> unit
(* Where is this?
val sigwait :Z.t list -> Z.t
 *)

type process_times = Unix.process_times = 
  { tms_utime : float;
    tms_stime : float;
    tms_cutime : float;
    tms_cstime : float;
  }

type tm = 
  { tm_sec :Z.t;
    tm_min :Z.t;
    tm_hour :Z.t;
    tm_mday :Z.t;
    tm_mon :Z.t;
    tm_year :Z.t;
    tm_wday :Z.t;
    tm_yday :Z.t;
    tm_isdst : bool;
  }

val time : unit -> float
val gettimeofday : unit -> float
val gmtime : float -> tm
val localtime : float -> tm 
val mktime : tm -> float * tm 
val alarm :Z.t -> Z.t
val sleep :Z.t -> unit
val sleepf : float -> unit
val times : unit -> process_times
val utimes : string -> float -> float -> unit
type interval_timer = Unix.interval_timer = 
 ITIMER_REAL | ITIMER_VIRTUAL | ITIMER_PROF 

type interval_timer_status = Unix.interval_timer_status = 
  { it_interval : float;
    it_value : float;
  }

val getitimer : interval_timer -> interval_timer_status
val setitimer : interval_timer -> interval_timer_status -> interval_timer_status
val getuid : unit -> Z.t
val geteuid : unit -> Z.t
val setuid :Z.t -> unit
val getgid : unit -> Z.t
val getegid : unit -> Z.t
val setgid :Z.t -> unit
val getgroups : unit -> Z.t array 
val setgroups :Z.t array -> unit
val initgroups : string -> Z.t -> unit

type passwd_entry =
  { pw_name : string;
    pw_passwd : string;
    pw_uid :Z.t;
    pw_gid :Z.t;
    pw_gecos : string;
    pw_dir : string;
    pw_shell : string
  }

type group_entry =
  { gr_name : string;
    gr_passwd : string;
    gr_gid :Z.t;
    gr_mem : string array
  }
val getlogin : unit -> string
val getpwnam : string -> passwd_entry
val getgrnam : string -> group_entry
val getpwuid :Z.t -> passwd_entry
val getgrgid :Z.t -> group_entry

type inet_addr = Unix.inet_addr

val inet_addr_of_string : string -> inet_addr
val string_of_inet_addr : inet_addr -> string
val inet_addr_any : inet_addr
val inet_addr_loopback : inet_addr
val inet6_addr_any : inet_addr
val inet6_addr_loopback : inet_addr
val is_inet6_addr : inet_addr -> bool

type socket_domain = Unix.socket_domain = 
 PF_UNIX | PF_INET | PF_INET6

type socket_type   = Unix.socket_type = 
 SOCK_STREAM | SOCK_DGRAM | SOCK_RAW  | SOCK_SEQPACKET

type sockaddr = ADDR_UNIX of string | ADDR_INET of inet_addr * Z.t

val socket : socket_domain -> socket_type -> Z.t -> file_descr
val domain_of_sockaddr: sockaddr -> socket_domain
val socketpair : socket_domain -> socket_type -> Z.t -> file_descr * file_descr
val accept : file_descr -> file_descr * sockaddr
val bind : file_descr -> sockaddr -> unit
val connect : file_descr -> sockaddr -> unit
val listen : file_descr -> Z.t -> unit

type shutdown_command = Unix.shutdown_command = 
    SHUTDOWN_RECEIVE
  | SHUTDOWN_SEND
  | SHUTDOWN_ALL

val shutdown : file_descr -> shutdown_command -> unit
val getsockname : file_descr -> sockaddr
val getpeername : file_descr -> sockaddr

type msg_flag = Unix.msg_flag = 
    MSG_OOB
  | MSG_DONTROUTE
  | MSG_PEEK

val recv :  file_descr -> bytes -> Z.t -> Z.t -> msg_flag list -> Z.t
val recvfrom : file_descr -> bytes -> Z.t -> Z.t -> msg_flag list -> Z.t * sockaddr
val send :  file_descr -> bytes -> Z.t -> Z.t -> msg_flag list -> Z.t
val send_substring : file_descr -> string -> Z.t -> Z.t -> msg_flag list -> Z.t
val sendto : file_descr -> bytes -> Z.t -> Z.t -> msg_flag list -> sockaddr -> Z.t
val sendto_substring : file_descr -> string -> Z.t -> Z.t -> msg_flag list  -> sockaddr -> Z.t

type socket_bool_option = Unix.socket_bool_option = 
    SO_DEBUG
  | SO_BROADCAST
  | SO_REUSEADDR
  | SO_KEEPALIVE
  | SO_DONTROUTE
  | SO_OOBINLINE
  | SO_ACCEPTCONN
  | TCP_NODELAY
  | IPV6_ONLY
  | SO_REUSEPORT

type socket_int_option = Unix.socket_int_option = 
    SO_SNDBUF
  | SO_RCVBUF
  | SO_ERROR
  | SO_TYPE
  | SO_RCVLOWAT
  | SO_SNDLOWAT

type socket_optint_option = Unix.socket_optint_option = 
 SO_LINGER 

type socket_float_option = Unix.socket_float_option  = 
 SO_RCVTIMEO | SO_SNDTIMEO

val getsockopt : file_descr -> socket_bool_option -> bool
val setsockopt : file_descr -> socket_bool_option -> bool -> unit
val getsockopt_int : file_descr -> socket_int_option -> Z.t
val setsockopt_int : file_descr -> socket_int_option -> Z.t -> unit
val getsockopt_optint : file_descr -> socket_optint_option -> Z.t option
val setsockopt_optint : file_descr -> socket_optint_option -> Z.t option -> unit
val getsockopt_float : file_descr -> socket_float_option -> float
val setsockopt_float : file_descr -> socket_float_option -> float -> unit
val getsockopt_error : file_descr -> error option
val open_connection : sockaddr -> in_channel * out_channel
val shutdown_connection : in_channel -> unit
val establish_server : (in_channel -> out_channel -> unit) -> sockaddr -> unit

type host_entry = Unix.host_entry = 
  { h_name : string;
    h_aliases : string array;
    h_addrtype : socket_domain;
    h_addr_list : inet_addr array
  }

type protocol_entry = (* Unix.protocol_entry = *)
  { p_name : string;
    p_aliases : string array;
    p_proto : Z.t
  }

type service_entry =
  { s_name : string;
    s_aliases : string array;
    s_port : Z.t;
    s_proto : string
  }
val gethostname : unit -> string
val gethostbyname : string -> host_entry
val gethostbyaddr : inet_addr -> host_entry
val getprotobyname : string -> protocol_entry
val getprotobynumber :Z.t -> protocol_entry
val getservbyname : string -> string -> service_entry
val getservbyport :Z.t -> string -> service_entry

type addr_info =
  { ai_family : socket_domain;
    ai_socktype : socket_type;
    ai_protocol : Z.t;
    ai_addr : sockaddr;
    ai_canonname : string
  }

type getaddrinfo_option =
    AI_FAMILY of socket_domain
  | AI_SOCKTYPE of socket_type
  | AI_PROTOCOL of Z.t
  | AI_NUMERICHOST
  | AI_CANONNAME
  | AI_PASSIVE

val getaddrinfo: string -> string -> getaddrinfo_option list -> addr_info list

type name_info = Unix.name_info = 
  { ni_hostname : string;
    ni_service : string;
  }

type getnameinfo_option = Unix.getnameinfo_option = 
    NI_NOFQDN
  | NI_NUMERICHOST
  | NI_NAMEREQD
  | NI_NUMERICSERV
  | NI_DGRAM

val getnameinfo : sockaddr -> getnameinfo_option list -> name_info

type terminal_io =
  {
     c_ignbrk : bool;
     c_brkint : bool;
     c_ignpar : bool;
     c_parmrk : bool;
     c_inpck : bool;
     c_istrip : bool;
     c_inlcr : bool;
     c_igncr : bool;
     c_icrnl : bool;
     c_ixon : bool;
     c_ixoff : bool;

     c_opost : bool;

     c_obaud :Z.t;
     c_ibaud :Z.t;
     c_csize :Z.t;
     c_cstopb :Z.t;
     c_cread : bool;
     c_parenb : bool;
     c_parodd : bool;
     c_hupcl : bool;
     c_clocal : bool;

     c_isig : bool;
     c_icanon : bool;
     c_noflsh : bool;
     c_echo : bool;
     c_echoe : bool;
     c_echok : bool;
     c_echonl : bool;

     c_vintr  : int;
     c_vquit  : int;
     c_verase : int;
     c_vkill  : int;
     c_veof   : int;
     c_veol   : int;
     c_vmin   : int;
     c_vtime  : int;
     c_vstart : int;
     c_vstop  : int;
  }

val tcgetattr : file_descr -> terminal_io

type setattr_when = Unix.setattr_when = 
    TCSANOW
  | TCSADRAIN
  | TCSAFLUSH

val tcsetattr : file_descr -> setattr_when -> terminal_io -> unit
val tcsendbreak : file_descr -> Z.t -> unit
val tcdrain : file_descr -> unit

type flush_queue = Unix.flush_queue = 
    TCIFLUSH
  | TCOFLUSH
  | TCIOFLUSH

val tcflush : file_descr -> flush_queue -> unit

type flow_action = Unix.flow_action = 
    TCOOFF
  | TCOON
  | TCIOFF
  | TCION

val tcflow : file_descr -> flow_action -> unit
val setsid : unit -> Z.t
