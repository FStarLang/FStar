module Negotiation.Writers.Aux2

(* TODO: all of these, along with their implementations in the .fst, should be automatically generated by QuackyDucky *)

module LWP = LowParseWriters.Parsers

val valid_rewrite_constr_clientHelloExtension_CHE_pre_shared_key : LWP.valid_rewrite_t
  (Parsers.ExtensionType.lwp_extensionType `LWP.parse_pair` Parsers.ClientHelloExtension.lwp_clientHelloExtension_CHE_pre_shared_key)
  Parsers.ClientHelloExtension.lwp_clientHelloExtension
  (fun (k, _) -> k == Parsers.ExtensionType.Pre_shared_key)
  (fun (_, ext) -> Parsers.ClientHelloExtension.CHE_pre_shared_key ext)

inline_for_extraction
noextract
let constr_clientHelloExtension_CHE_pre_shared_key
  #inv #pre #post #post_err
  ($f: (unit -> LWP.EWrite unit LWP.parse_empty Parsers.ClientHelloExtension.lwp_clientHelloExtension_CHE_pre_shared_key pre post post_err inv))
  ()
: LWP.EWrite
    unit
    LWP.parse_empty
    Parsers.ClientHelloExtension.lwp_clientHelloExtension
    (fun _ -> pre ())
    (fun _ _ msg ->
      pre () /\
      begin match LWP.destr_repr_spec _ _ _ _ _ _ _ f () with
      | LWP.Correct (_, pl) ->
        post () () pl /\
        msg == Parsers.ClientHelloExtension.CHE_pre_shared_key pl
      | _ -> False
      end
    )
    (fun _ ->
      pre () /\
      begin match LWP.destr_repr_spec _ _ _ _ _ _ _ f () with
      | LWP.Error _ ->
        post_err ()
      | _ -> False
      end
    )
    inv
= LWP.start Parsers.ExtensionType.lwp_extensionType Parsers.ExtensionType.extensionType_writer Parsers.ExtensionType.Pre_shared_key;
  LWP.frame _ _ _ _ _ _ _ (fun _ -> LWP.recast_writer _ _ _ _ _ _ _ f);
  LWP.valid_rewrite _ _ _ _ _ valid_rewrite_constr_clientHelloExtension_CHE_pre_shared_key

inline_for_extraction
noextract
let constr_clientHelloExtension_CHE_pre_shared_key'
  #inv
  (f: (unit -> LWP.EWrite unit LWP.parse_empty Parsers.ClientHelloExtension.lwp_clientHelloExtension_CHE_pre_shared_key (fun _ -> True) (fun _ _ _ -> True) (fun _ -> True) inv))
: LWP.EWrite
    unit
    LWP.parse_empty
    Parsers.ClientHelloExtension.lwp_clientHelloExtension
    (fun _ -> True)
    (fun _ _ msg ->
      begin match LWP.destr_repr_spec _ _ _ _ _ _ _ f () with
      | LWP.Correct (_, pl) ->
        msg == Parsers.ClientHelloExtension.CHE_pre_shared_key pl
      | _ -> False
      end
    )
    (fun _ ->
      LWP.Error? (LWP.destr_repr_spec _ _ _ _ _ _ _ f ())
    )
    inv
= LWP.start Parsers.ExtensionType.lwp_extensionType Parsers.ExtensionType.extensionType_writer Parsers.ExtensionType.Pre_shared_key;
  LWP.frame _ _ _ _ _ _ _ (fun _ -> LWP.recast_writer _ _ _ _ _ _ _ f);
  LWP.valid_rewrite _ _ _ _ _ valid_rewrite_constr_clientHelloExtension_CHE_pre_shared_key

val valid_rewrite_constr_clientHelloExtension_CHE_psk_key_exchange_modes : LWP.valid_rewrite_t
  (Parsers.ExtensionType.lwp_extensionType `LWP.parse_pair` Parsers.ClientHelloExtension.lwp_clientHelloExtension_CHE_psk_key_exchange_modes)
  Parsers.ClientHelloExtension.lwp_clientHelloExtension
  (fun (k, _) -> k == Parsers.ExtensionType.Psk_key_exchange_modes)
  (fun (_, ext) -> Parsers.ClientHelloExtension.CHE_psk_key_exchange_modes ext)

inline_for_extraction
noextract
let constr_clientHelloExtension_CHE_psk_key_exchange_modes
  #inv #pre #post #post_err
  ($f: (unit -> LWP.EWrite unit LWP.parse_empty Parsers.ClientHelloExtension.lwp_clientHelloExtension_CHE_psk_key_exchange_modes pre post post_err inv))
  ()
: LWP.EWrite
    unit
    LWP.parse_empty
    Parsers.ClientHelloExtension.lwp_clientHelloExtension
    (fun _ -> pre ())
    (fun _ _ msg ->
      pre () /\
      begin match LWP.destr_repr_spec _ _ _ _ _ _ _ f () with
      | LWP.Correct (_, pl) ->
        post () () pl /\
        msg == Parsers.ClientHelloExtension.CHE_psk_key_exchange_modes pl
      | _ -> False
      end
    )
    (fun _ ->
      pre () /\
      begin match LWP.destr_repr_spec _ _ _ _ _ _ _ f () with
      | LWP.Error _ ->
        post_err ()
      | _ -> False
      end
    )
    inv
= LWP.start Parsers.ExtensionType.lwp_extensionType Parsers.ExtensionType.extensionType_writer Parsers.ExtensionType.Psk_key_exchange_modes;
  LWP.frame _ _ _ _ _ _ _ (fun _ -> LWP.recast_writer _ _ _ _ _ _ _ f);
  LWP.valid_rewrite _ _ _ _ _ valid_rewrite_constr_clientHelloExtension_CHE_psk_key_exchange_modes

inline_for_extraction
noextract
let constr_clientHelloExtension_CHE_psk_key_exchange_modes'
  #inv
  (f: (unit -> LWP.EWrite unit LWP.parse_empty Parsers.ClientHelloExtension.lwp_clientHelloExtension_CHE_psk_key_exchange_modes (fun _ -> True) (fun _ _ _ -> True) (fun _ -> True) inv))
: LWP.EWrite
    unit
    LWP.parse_empty
    Parsers.ClientHelloExtension.lwp_clientHelloExtension
    (fun _ -> True)
    (fun _ _ msg ->
      begin match LWP.destr_repr_spec _ _ _ _ _ _ _ f () with
      | LWP.Correct (_, pl) ->
        msg == Parsers.ClientHelloExtension.CHE_psk_key_exchange_modes pl
      | _ -> False
      end
    )
    (fun _ ->
      LWP.Error? (LWP.destr_repr_spec _ _ _ _ _ _ _ f ())
    )
    inv
= LWP.start Parsers.ExtensionType.lwp_extensionType Parsers.ExtensionType.extensionType_writer Parsers.ExtensionType.Psk_key_exchange_modes;
  LWP.frame _ _ _ _ _ _ _ (fun _ -> LWP.recast_writer _ _ _ _ _ _ _ f);
  LWP.valid_rewrite _ _ _ _ _ valid_rewrite_constr_clientHelloExtension_CHE_psk_key_exchange_modes

val valid_rewrite_constr_clientHelloExtension_CHE_early_data : LWP.valid_rewrite_t
  (Parsers.ExtensionType.lwp_extensionType `LWP.parse_pair` Parsers.ClientHelloExtension.lwp_clientHelloExtension_CHE_early_data)
  Parsers.ClientHelloExtension.lwp_clientHelloExtension
  (fun (k, _) -> k == Parsers.ExtensionType.Early_data)
  (fun (_, ext) -> Parsers.ClientHelloExtension.CHE_early_data ext)

inline_for_extraction
noextract
let constr_clientHelloExtension_CHE_early_data
  #inv #pre #post #post_err
  ($f: (unit -> LWP.EWrite unit LWP.parse_empty Parsers.ClientHelloExtension.lwp_clientHelloExtension_CHE_early_data pre post post_err inv))
  ()
: LWP.EWrite
    unit
    LWP.parse_empty
    Parsers.ClientHelloExtension.lwp_clientHelloExtension
    (fun _ -> pre ())
    (fun _ _ msg ->
      pre () /\
      begin match LWP.destr_repr_spec _ _ _ _ _ _ _ f () with
      | LWP.Correct (_, pl) ->
        post () () pl /\
        msg == Parsers.ClientHelloExtension.CHE_early_data pl
      | _ -> False
      end
    )
    (fun _ ->
      pre () /\
      begin match LWP.destr_repr_spec _ _ _ _ _ _ _ f () with
      | LWP.Error _ ->
        post_err ()
      | _ -> False
      end
    )
    inv
= LWP.start Parsers.ExtensionType.lwp_extensionType Parsers.ExtensionType.extensionType_writer Parsers.ExtensionType.Early_data;
  LWP.frame _ _ _ _ _ _ _ (fun _ -> LWP.recast_writer _ _ _ _ _ _ _ f);
  LWP.valid_rewrite _ _ _ _ _ valid_rewrite_constr_clientHelloExtension_CHE_early_data

inline_for_extraction
noextract
let constr_clientHelloExtension_CHE_early_data'
  #inv
  (f: (unit -> LWP.EWrite unit LWP.parse_empty Parsers.ClientHelloExtension.lwp_clientHelloExtension_CHE_early_data (fun _ -> True) (fun _ _ _ -> True) (fun _ -> True) inv))
: LWP.EWrite
    unit
    LWP.parse_empty
    Parsers.ClientHelloExtension.lwp_clientHelloExtension
    (fun _ -> True)
    (fun _ _ msg ->
      begin match LWP.destr_repr_spec _ _ _ _ _ _ _ f () with
      | LWP.Correct (_, pl) ->
        msg == Parsers.ClientHelloExtension.CHE_early_data pl
      | _ -> False
      end
    )
    (fun _ ->
      LWP.Error? (LWP.destr_repr_spec _ _ _ _ _ _ _ f ())
    )
    inv
= LWP.start Parsers.ExtensionType.lwp_extensionType Parsers.ExtensionType.extensionType_writer Parsers.ExtensionType.Early_data;
  LWP.frame _ _ _ _ _ _ _ (fun _ -> LWP.recast_writer _ _ _ _ _ _ _ f);
  LWP.valid_rewrite _ _ _ _ _ valid_rewrite_constr_clientHelloExtension_CHE_early_data

val valid_rewrite_constr_clientHelloExtension_CHE_key_share : LWP.valid_rewrite_t
  (Parsers.ExtensionType.lwp_extensionType `LWP.parse_pair` Parsers.ClientHelloExtension.lwp_clientHelloExtension_CHE_key_share)
  Parsers.ClientHelloExtension.lwp_clientHelloExtension
  (fun (k, _) -> k == Parsers.ExtensionType.Key_share)
  (fun (_, ext) -> Parsers.ClientHelloExtension.CHE_key_share ext)

inline_for_extraction
noextract
let constr_clientHelloExtension_CHE_key_share
  #inv #pre #post #post_err
  ($f: (unit -> LWP.EWrite unit LWP.parse_empty Parsers.ClientHelloExtension.lwp_clientHelloExtension_CHE_key_share pre post post_err inv))
  ()
: LWP.EWrite
    unit
    LWP.parse_empty
    Parsers.ClientHelloExtension.lwp_clientHelloExtension
    (fun _ -> pre ())
    (fun _ _ msg ->
      pre () /\
      begin match LWP.destr_repr_spec _ _ _ _ _ _ _ f () with
      | LWP.Correct (_, pl) ->
        post () () pl /\
        msg == Parsers.ClientHelloExtension.CHE_key_share pl
      | _ -> False
      end
    )
    (fun _ ->
      pre () /\
      begin match LWP.destr_repr_spec _ _ _ _ _ _ _ f () with
      | LWP.Error _ ->
        post_err ()
      | _ -> False
      end
    )
    inv
= LWP.start Parsers.ExtensionType.lwp_extensionType Parsers.ExtensionType.extensionType_writer Parsers.ExtensionType.Key_share;
  LWP.frame _ _ _ _ _ _ _ (fun _ -> LWP.recast_writer _ _ _ _ _ _ _ f);
  LWP.valid_rewrite _ _ _ _ _ valid_rewrite_constr_clientHelloExtension_CHE_key_share

inline_for_extraction
noextract
let constr_clientHelloExtension_CHE_key_share'
  #inv
  (f: (unit -> LWP.EWrite unit LWP.parse_empty Parsers.ClientHelloExtension.lwp_clientHelloExtension_CHE_key_share (fun _ -> True) (fun _ _ _ -> True) (fun _ -> True) inv))
: LWP.EWrite
    unit
    LWP.parse_empty
    Parsers.ClientHelloExtension.lwp_clientHelloExtension
    (fun _ -> True)
    (fun _ _ msg ->
      begin match LWP.destr_repr_spec _ _ _ _ _ _ _ f () with
      | LWP.Correct (_, pl) ->
        msg == Parsers.ClientHelloExtension.CHE_key_share pl
      | _ -> False
      end
    )
    (fun _ ->
      LWP.Error? (LWP.destr_repr_spec _ _ _ _ _ _ _ f ())
    )
    inv
= LWP.start Parsers.ExtensionType.lwp_extensionType Parsers.ExtensionType.extensionType_writer Parsers.ExtensionType.Key_share;
  LWP.frame _ _ _ _ _ _ _ (fun _ -> LWP.recast_writer _ _ _ _ _ _ _ f);
  LWP.valid_rewrite _ _ _ _ _ valid_rewrite_constr_clientHelloExtension_CHE_key_share

val valid_rewrite_constr_clientHelloExtension_CHE_server_name : LWP.valid_rewrite_t
  (Parsers.ExtensionType.lwp_extensionType `LWP.parse_pair` Parsers.ClientHelloExtension.lwp_clientHelloExtension_CHE_server_name)
  Parsers.ClientHelloExtension.lwp_clientHelloExtension
  (fun (k, _) -> k == Parsers.ExtensionType.Server_name)
  (fun (_, ext) -> Parsers.ClientHelloExtension.CHE_server_name ext)

inline_for_extraction
noextract
let constr_clientHelloExtension_CHE_server_name'
  #inv
  (f: (unit -> LWP.EWrite unit LWP.parse_empty Parsers.ClientHelloExtension.lwp_clientHelloExtension_CHE_server_name (fun _ -> True) (fun _ _ _ -> True) (fun _ -> True) inv))
: LWP.EWrite
    unit
    LWP.parse_empty
    Parsers.ClientHelloExtension.lwp_clientHelloExtension
    (fun _ -> True)
    (fun _ _ msg ->
      begin match LWP.destr_repr_spec _ _ _ _ _ _ _ f () with
      | LWP.Correct (_, pl) ->
        msg == Parsers.ClientHelloExtension.CHE_server_name pl
      | _ -> False
      end
    )
    (fun _ ->
      LWP.Error? (LWP.destr_repr_spec _ _ _ _ _ _ _ f ())
    )
    inv
= LWP.start Parsers.ExtensionType.lwp_extensionType Parsers.ExtensionType.extensionType_writer Parsers.ExtensionType.Server_name;
  LWP.frame _ _ _ _ _ _ _ (fun _ -> LWP.recast_writer _ _ _ _ _ _ _ f);
  LWP.valid_rewrite _ _ _ _ _ valid_rewrite_constr_clientHelloExtension_CHE_server_name

let rec serverNameList_list_bytesize_correct
  (l: list Parsers.ServerName.serverName)
: Lemma
  (Parsers.ServerNameList.serverNameList_list_bytesize l == LWP.list_size Parsers.ServerName.lwp_serverName l)
  [SMTPat (Parsers.ServerNameList.serverNameList_list_bytesize l)]
= match l with
  | [] -> ()
  | a :: q ->
    Parsers.ServerName.serverName_bytesize_eq a;
    serverNameList_list_bytesize_correct q

val valid_serverNameList_intro : LWP.valid_rewrite_t
  (LWP.parse_vllist Parsers.ServerName.lwp_serverName 1ul 65535ul)
  Parsers.ServerNameList.lwp_serverNameList
  (fun _ -> True)
  (fun x -> x)
