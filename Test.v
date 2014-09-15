(** Test the standard library. *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Computation.
Require Import Pervasives.
Require Import StdLib.

Import ListNotations.
Import C.Notations.
Open Local Scope string.

(** * An echo server logging all the incoming messages. *)

(** Start the program. *)
Definition start {sig : Signature.t} (_ : unit) : C sig unit :=
  TCPServerSocket.bind 8383.

(** Handle events. *)
Definition handler {sig : Signature.t} (input : Input.t) : C sig unit :=
  match input with
  | Input.socket input =>
    match input with
    | TCPServerSocket.Input.bound _ => Log.log "Server socket opened."
    | TCPServerSocket.Input.accepted _ => Log.log "Client connection accepted."
    | TCPServerSocket.Input.read id data =>
      do! Log.log ("Input: " ++ data) in
      do! TCPServerSocket.write id data in
      TCPServerSocket.close_connection id
    end
  | _ => C.ret tt
  end.

(** Run the program sequentially on a list of input events. *)
Definition run (inputs : list TCPServerSocket.Input.t) : list Output.t :=
  let inputs := List.map Input.socket inputs in
  let program :=
    do! start tt in
    List.iter inputs handler in
  match C.run Memory.Nil program with
  | (_, _, output) => output
  end.

Compute run [].
Compute run [TCPServerSocket.Input.bound (TCPServerSocket.Id.new 12)].
Compute run [
  TCPServerSocket.Input.bound (TCPServerSocket.Id.new 12);
  TCPServerSocket.Input.accepted (TCPServerSocket.ConnectionId.new 23);
  TCPServerSocket.Input.read (TCPServerSocket.ConnectionId.new 23) "hello"].