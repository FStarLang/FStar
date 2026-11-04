module Pulse.Lib.NativeExceptions

// Runtime-only channels. The checker guarantees that a caught payload is
// unpacked at the type used to pack it. Lexical exits are never user payloads.
exception NativeException of FStar.Dyn.dyn
exception ControlFlow of string
