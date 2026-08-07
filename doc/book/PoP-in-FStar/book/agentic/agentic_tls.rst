.. _Agentic_tls:

=====================================
A Verified TLS-1.3 Client and Server
=====================================

We went to some trouble in the last chapter to create a rubric for state
machines and their implementation refinements. In this chapter, we'll put that
rubric to work by using it to structure a verified implementation of the TLS-1.3
protocol.

Some background on TLS: Transport Layer Security (TLS) is a widely used
cryptographic protocol for secure communication over the Internet. It is used to
secure web traffic (e.g., for HTTPS) and is also used in many other applications
that require secure communication. TLS provides confidentiality, integrity, and
authenticity of data transmitted over a network. TLS-1.3 is the latest version
of the protocol, specified in `RFC 8446
<https://datatracker.ietf.org/doc/html/rfc8446>`_, which includes several
improvements over previous versions, including better security and performance.

Verifying implementations of TLS has been a long-standing challenge, due to the
complexity of the protocol and the need to reason about cryptographic
properties. `Project Everest <https://project-everest.github.io/>`_, a main
application of F*, targeted the verification of TLS, and produced verified
implementations of many of its components. However, some parts of the protocol
were not fully verified, in particular, the main state machine proof of the TLS
handshake protocol was not completed.

TLS supports many modes and optimizations. What we'll focus on here is verifying
a single, commonly used profile of the protocol, reusing some verified
components from Project Everest notably for the cryptographic primitives, and
focusing on the main handshake protocol in the following mode:

* 1-RTT (one round trip time) handshake, with no 0-RTT (zero round trip time) support.
* No session resumption, i.e., each handshake is a full handshake, or key update.
* X25519 key exchange
* Chacha20-Poly1305 as the symmetric cipher, with SHA-256 as the hash function.

This is a limited profile for TLS, but a common one and widely supported.

A Roadmap for an Agentic Implementation of TLS-1.3
--------------------------------------------------

An agentic implementation of TLS-1.3 took about 2 weeks of agentic programming
to get a first verified version, costing around $3000 in tokens using GPT-5.5
with GitHub Copilot CLI. Getting there took some planning and structure, with
templates, rubrics, and audits playing a central role. We outline a roadmap for
our process before getting into it in detail.


**Templates** Using the implementation of the Calculator Server as a template
for an agent, instructing it to first implement a TLS-1.3 client, and then using
the client as a template for the server. A lesson from this is to start small,
and build up to more complex systems, using the simpler systems as templates for
the more complex ones. 

**Rubrics** To ensure that the implementation follows a well-understood pattern
and to keep things comprehensible for a human, we use the state machine
typeclass to ensure that the relationship between the Calculator Server and the
TLS implementations are not just loosely related, but that they are both,
formally, instances of the same rubric. Understanding the rubric alone, and
convincing oneself that it enforces a state machine refinement, is enough to
understand that a TLS implementation refines a state machine specification.

**Audits** The state machine specification for the Caclulator Server is just a
few dozen lines of code and is easy to understand and review. In contrast, a
state machine specification for TLS, even for the limited profile we are
considering, is on the order of a few thousand lines of specification. While our
rubric gives us confidence that the implementation refines this specification,
there is still the question of whether the specification is correct. For this,
we use two main techniques:

    * Interoperability testing: An claimed implementation of TLS can only
      practically be considered an implementation of TLS if it can interoperate
      with other implementations of TLS. This is common practice for network
      protocol implementors, e.g., the IETF organizes interoperability testing
      events for the networking protocols it standardizes, ensuring that
      multiple implementations of a protocol interpret the natural language
      specification of the protocol in the same way. Our TLS implementation
      interoperates with OpenSSL in both directions, i.e., our client
      interoperates with an OpenSSL server, and our server interoperates with an
      OpenSSL client. This gives us confidence that our implementation really is
      a TLS.


    * State machine proofs: Knowing that the implementation refines the state
      machine, we can then ignore the implementation and focus on the state
      machine specification alone. We use agents to prove that the state machine
      specification guarantees some useful properties. Notably, we prove that if
      a client and server both agree on the messages exchanged, then they also
      agree on the session key that is derived by the handshake. In other words,
      subjecting the specification to further formal analysis allows us to gain
      confidence that the specification is also meaningful.

Note, we do not prove any *cryptographic security* properties of the protocol,
only functional correctness properties. Extending our state mahine specification
to also support security proofs would be an interesting direction to pursue in
the future.

Specifying the State Machine
-----------------------------

We start by sketching the state machine specification, first informally, using
this diagram from the RFC 8446.

.. code-block:: text

                Client                                           Server

        Key  ^ ClientHello
        Exch | + key_share*
             | + signature_algorithms*
             | + psk_key_exchange_modes*
             v + pre_shared_key*       -------->
                                                        ServerHello  ^ Key
                                                        + key_share*  | Exch
                                                   + pre_shared_key*  v
                                               {EncryptedExtensions}  ^  Server
                                               {CertificateRequest*}  v  Params
                                                    {Certificate*}    ^
                                                {CertificateVerify*}  | Auth
                                                        {Finished}    v
                                       <--------  [Application Data*]
            ^ {Certificate*}
       Auth | {CertificateVerify*}
            v {Finished}               -------->
            [Application Data]         <------->  [Application Data]



The client starts by preparing a ``ClientHello`` message, which includes the
client's key share and other supported cryptographic parameters. The server
responds with a ``ServerHello`` message, which includes the server's key share
and other selected cryptographic parameters. The server may also send additional
messages, such as ``EncryptedExtensions``, ``CertificateRequest``,
``Certificate``, ``CertificateVerify``, and ``Finished`` messages, depending on
the configuration and requirements of the handshake. The client may also send
its own ``Certificate`` and ``CertificateVerify`` messages if requested by the
server. Using the key shares, both parties derive a shared session key, which is
then used to encrypt and authenticate application data. The handshake is
complete when both parties have exchanged the necessary messages and derived the
session key. After the handshake, both parties can securely exchange application
data.

Specifying this state machine in F* takes a few steps and agents author this
entirely from background knowledge of the TLS protocol, using the RFC 8446 as a
reference. We sketch parts of this specification below, but omit many details.

The state machine follows our rubric, the typeclass of state machines that we
saw earlier.

.. code-block:: fstar

    let client_state_machine (initial:CS.connection_state)
    : SM.state_machine
            CS.connection_state
            CW.wire_message
            CTypes.client_local_event
            CTypes.local_output =
    {
        SM.sm_initial_state = initial;
        SM.sm_step = client_step;
    }

The state of the protocol is ``connection_state``, which includes a model of the
protocol state, a log of the messages sent and received on the wire, and a log
of the events that have occurred in the protocol.

.. code-block:: fstar

    type connection_state = {
        cs_model: connection_model;
        cs_wire_log: wire_log;
        cs_event_log: list conn_event;
    }

The connection model itself has many components, reflecting the state of the
various sub-protcols that are part of TLS, including the initial configuration,
the handshake state machine, etc.

.. code-block:: fstar

    type connection_model = {
        model_config: connection_config;
        model_control: connection_control_state;
        model_record: record_layer_state;
        model_handshake: handshake_state;
        model_application: application_state;
        model_failure: option T.tls_error;
    }

The handshake state machine is perhaps the most interesting part: we don't
discuss it in detail, but it records various parts of the handshake, e.g., the
messages sent and received so far, the state of the key schedule, the transcript
of the handshake, etc. The point is mainly to see that this is a detailed model 
of the TLS handshake.

.. code-block:: fstar

    type handshake_state = {
        hs_start: option handshake_start;
        hs_server_selection: option server_handshake_selection;
        hs_client_hello: option M.client_hello;
        hs_server_hello: option M.server_hello;
        hs_encrypted_extensions: option M.encrypted_extensions;
        hs_certificate: option M.certificate_msg;
        hs_validated_peer: option X.peer_identity;
        hs_certificate_verify: option M.certificate_verify;
        hs_certificate_verify_verified: bool;
        hs_server_finished: option M.finished;
        hs_server_finished_verified: bool;
        hs_client_finished: option M.finished;
        hs_transcript: Tr.transcript;
        hs_buffers: handshake_buffer_state;
        hs_keys: key_schedule_state;
    }

The transition relation is given by ``client_step``: we'll see a small part
of it below. A few things to point out:

    * Unlike for Calculator Server, the transition relation is not a simple
      function of the current but is instead a relation between the current
      state, the event, the next state, and the outputs.
      
    * There are both wire event and local events.

    * The core of the transition relation is ``legal_connection_delta``

.. code-block:: fstar

    let client_step
        (st0:CS.connection_state)
        (ev:SM.event CW.wire_message CTypes.client_local_event)
        (st1:CS.connection_state)
        (out:SM.step_output CW.wire_message CTypes.local_output)
    : prop =
    match ev with
    | SM.WireEvent wire ->
        exists msg.
            let conn_ev =
                CS.ConnNetworkEvent {
                    CL.message_direction = CL.Received;
                    CL.message_value = msg;
                } in
            CS.legal_connection_delta
                st0
                {
                    CS.delta_event = conn_ev;
                    CS.delta_raw_sent =
                        WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs;
                    CS.delta_raw_received = CW.wire_serialize wire;
                }
                st1 /\
            client_local_outputs_match conn_ev out.SM.so_local_outputs
    | SM.LocalEvent local ->
        let api = CTypes.client_local_event_api local in
        exists conn_ev raw_sent raw_received.
            client_api_event_matches st0 api conn_ev /\
            client_wire_outputs_match raw_sent out.SM.so_wire_outputs /\
            client_local_outputs_match conn_ev out.SM.so_local_outputs /\
            CS.legal_connection_delta
            st0
            {
                CS.delta_event = conn_ev;
                CS.delta_raw_sent = raw_sent;
                CS.delta_raw_received = raw_received;
            }
            st1

At the heart of ``legal_connection_delta`` is a step function, which is a ghost
function computing a single step of the state machine for network and local
events. We give a glimpse of it below.

For example, ``step_handshake_message`` transitions the handshake state,
appending messages to the transcript, and recording what was sent or received so
far.

.. code-block:: fstar

    let step_handshake_message
        (model:connection_model)
        (dir:direction)
        (msg:M.handshake_msg)
    : GTot (option connection_model) =
        let hs = model.model_handshake in
        match dir, msg, model.model_control with
        | CL.Sent, M.ClientHello ch, ControlHandshaking HsStarted ->
            let hs' =
            append_handshake_to_transcript
                { hs with
                    hs_client_hello = Some ch;
                    hs_buffers =
                    { hs.hs_buffers with hb_client_hello_bytes = W.serialize_handshake msg };
                }
                msg in
            Some (with_handshake_stage model hs' HsClientHelloSent)
        | CL.Received, M.ClientHello ch, ControlHandshaking HsAwaitingClientHello ->
            let hs' =
            append_handshake_to_transcript
                { hs with
                    hs_client_hello = Some ch;
                    hs_buffers =
                    { hs.hs_buffers with hb_client_hello_bytes = W.serialize_handshake msg };
                }
                msg in
            Some (with_handshake_stage model hs' HsClientHelloReceived)
        | ...

Local transitions include cases for deriving keys, callbacks to certificate
validation, and other local events. 

* Deriving shared secrets is a local event with a full specification of how
  secrets are derived based on a crypto API for key-derivation functions
  (``hkdf`` etc.).

* Callbacks to other local events, e.g., selecting server parameters, callbacks
  to certificate validation, and delivering application data, are all local
  events with their effects logged in the connection state.

.. code-block:: fstar

    let step_local_event (model:connection_model) (ev:local_event) : GTot (option connection_model) =
        let hs = model.model_handshake in
        match ev, model.model_control with
        | LocalDeriveSharedSecret shared, ControlHandshaking HsServerHelloReceived
        | LocalDeriveSharedSecret shared, ControlHandshaking HsClientHelloReceived ->
            Some (derive_shared_secret_model model hs shared)

        | LocalSelectServerParameters selection, ControlHandshaking HsClientHelloReceived ->
            Some (with_handshake_stage
            model
            { hs with
                hs_server_selection = Some selection;
                hs_client_hello = Some selection.server_selected_client_hello;
            }
            HsClientHelloReceived)
        | LocalVerifyCertificateSignature cv, ControlHandshaking HsCertificateVerifyReceived ->
            Some (with_handshake_stage
            model
            { hs with
                hs_certificate_verify = Some cv;
                hs_certificate_verify_verified = true;
            }
            HsCertificateVerifyVerified)
        | LocalDeliverApplicationData bytes, ControlApplicationData ->
            let app = model.model_application in
            Some {
            model with
                model_application =
                { app with app_log = CL.append_app_received app.app_log bytes };
            }
        | ...

Note, it might appear that the this transition relation is too permissive, e.g.,
a ``LocalVerifyCertificateSignature cv`` event could be fired even if the
certificate signature is invalid. However, transitions are guarded by a
``legal_local_event`` predicate, as shown below, ensuring that
``LocalVerifyCertificateSignature cv`` can only be fired if the certificate
signature is indeed valid according to ``C.verify_signature``, a pure function
specifying the behavior of a signature verification algorithm. 

.. code-block:: fstar

    let legal_local_event (model:connection_model) (ev:local_event) : prop =
        let hs = model.model_handshake in
        match ev, model.model_control with
        | LocalVerifyCertificateSignature cv, ControlHandshaking HsCertificateVerifyReceived ->
            model.model_config.config_role == ClientEndpoint /\
            (match hs.hs_validated_peer, hs.hs_certificate_verify, hs.hs_buffers.hb_certificate_verify_input with
            | Some peer, Some stored_cv, Some input ->
                stored_cv == cv /\
                C.verify_signature cv.M.scheme peer.X.leaf_public_key input cv.M.signature
            | _, _, _ -> False)
        | ...

Auditing State Machine Specification with Key Agreement Proofs
---------------------------------------------------------------

Of course, this is a large state machine specification (and we have only shown a
small part of it), and it is not obvious that it is correct. One way to audit
whether or not this is a good specification is to try to prove that it satisfies
various useful properties.

One property that one aims to ensure is that if the client and server might
expect is that if the client and server agree on the messages exchanged, then
they also agree on the session key that is derived by the handshake. It is worth
pointing out that this is not a small proof-oriented test (SPOT): it is a
universal property of the protocol specification, rather than a property a
single small example. Though, both SPOTs and proofs of such universal properties
share the idea of proving properties of the specification to judge its quality.

The lemma shown below gives us confidence that the state machine specification
is sufficiently precise to draw such meaningful conclusions.

.. code-block:: fstar

    val lemma_client_server_application_record_material_agrees_from_paired_handshake_event_trace
        (client:CS.connection_state)
        (server:CS.connection_state)
    : Lemma
      (requires
        CD.client_driver_application_ready client /\
        SD.server_driver_application_ready server /\
        paired_handshake_event_trace client server /\
        client_server_driver_first_epoch_no_key_update_state_inputs client server)
      (ensures
        paired_handshake_message_states client server /\
        paired_handshake_events client server /\
        client_server_driver_remaining_semantic_projection_inputs client server /\
        client_server_driver_supported_profile_state_inputs client server /\
        CS.supported_profile_client_server_key_material_inputs_agree client server /\
        CS.supported_profile_client_server_key_material_agrees client server /\
        CS.peer_record_material_agrees (CS.traffic_id CS.TrafficApplication CS.ClientTraffic) client server /\
        CS.peer_record_material_agrees (CS.traffic_id CS.TrafficApplication CS.ServerTraffic) client server)

Let's look at it closely. The preconditions state:

* The client and server are both in a state where they are ready to send and
  receive application data.

* The client and server have not performed any key updates during the
  handshake---our TLS profile does not support key updates, so this is a
  reasonable assumption.

* The client and server have a paired handshake event trace, i.e., they have
  exchanged the same handshake messages in the same order, which is the most
  significant assumption here. It states that

  1. The client hello sent by the client is the same as the client hello received by the server.
  2. The server hello sent by the server is the same as the server hello received by the client.
  3. The encrypted extensions sent by the server is the same as the encrypted extensions received.
  4. The certificate sent by the server is the same as the certificate received by the client.
  5. The certificate verify sent by the server is the same as the certificate verify received
  6. The finished sent by the server is the same as the finished received by the client.
  7. The finished sent by the client is the same as the finished received by the server; and
  8. All these messages appear in the event trace of the client and server logs.

Under these assumptions, we get several useful conclusions, including, most notably:

* ``supported_profile_client_server_key_material_agrees``, which guarantees that
  the client and server agree on all the derived key material, including the
  handshake traffic keys, the application traffic keys, and the master secret.

Underlying these proofs are also some assumptions about the underlying
cryptographic primitives, which we show below.

The first assumption is about the X25519 key agreement protocol, which is used
to derive a shared secret between the client and server. The lemma below states
that if the client and server have the same public keys, then they will derive
the same shared secret.

.. code-block:: fstar
    
    val lemma_x25519_shared_agreement:
        client_sk:x25519_private ->
        server_sk:x25519_private ->
        client_pub:x25519_public ->
        server_pub:x25519_public ->
        Lemma
        (requires
            x25519_public_from_private client_sk == client_pub /\
            x25519_public_from_private server_sk == server_pub)
        (ensures
            x25519_shared client_sk server_pub ==
            x25519_shared server_sk client_pub)

The second assumption states that chacha20-poly1305 is a functionally correct
authenticated encryption scheme:

.. code-block:: fstar

    val lemma_chacha20_poly1305_open_seal:
        key:B.bytes ->
        nonce:B.bytes ->
        aad:B.bytes ->
        plaintext:B.bytes ->
        Lemma
        (chacha20_poly1305_open
            key
            nonce
            aad
            (chacha20_poly1305_seal key nonce aad plaintext) ==
            Some plaintext)

Both of these properties could be proven from the underlying cryptographic
primitives. However, for this development, we focused on using pre-existing
verified cryptographic primitives from HACL*, rather than verifying these
properties again from scratch.

One should also attempt to prove other properties of the specification to
further increase confidence, e.g., one could prove that the server's parameter
selection always picks the strongest supported cipher suite that the client
offers.

Rubric Compliance
------------------

While we have a large state machine specification, our typeclass for state
machine refinement gives us an easy way to check that the Pulse implementation
of this TLS state machine is indeed a correct refinement. 

Reviewing this is just a matter of checking that the implementation satisfies
the typeclass, which is just a few lines of code. For example, the snippet below
is sufficient to guarantee that the client protocol implementation is a correct
refinement of the ``client_system`` state machine. An analogous instantiation 
is sufficient to check the server refinement.

The rest of the implementation, in excess of 130,000 lines of code, need not be
reviewed to check for compliance with the state machine.

 .. code-block:: fstar

  let client_protocol_implementation
    : CPI.protocol_implementation
        canonical_client
        CS.connection_state
        CW.wire_message
        CTypes.client_local_event
        CTypes.local_output
    =
    {
        CPI.pi_system = (fun cc -> client_system (Ghost.reveal cc.canonical_client_initial));
        ...
    }


Auditing with Interoperability Testing
--------------------------------------

Finally, as mentioned previously, to confirm that we have truly implemented a
TLS-1.3 client and server, we perform interoperability testing with OpenSSL.

Our implementation extracts to about 45,000 lines of C code (of which about
15,000 lines are generated by EverParse for wire format parsers and
serializers). We compile this to C, linking the HACL* libraries for
cryptographic primities, and OpenSSL libraries for certificate validation.

Together with a few hundred lines of unverified C code to implement a top-level
main function to launch a client or server, configure the network, and to
perform some basic testing to negotiate a connection, the resulting test client
and server interoperate with OpenSSL.

Of course, one would want to audit this further for a number of other
properties, e.g., for performance profiling, for side-channel resistance
(although the HACL* cryptographic primitives already do have some side-channel
resistance guarantees), and for other properties.

We don't mean to claim that our TLS client and server are production ready,
though it is a good start. What is important is that with a careful choice of
templates (starting with small demonstrations like Calculator Server), rubrics
(to easily check that an implementation is a refinement of a state machine), and
audits (e.g., by proving specification properties, and by interoperability
testing), we can use agents to produce a verified implementation of a complex
protocol like TLS-1.3 and have some confidence that it is correct.