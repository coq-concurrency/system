(** The standard library. *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Computation.
Require Import Log.
Require Import Pervasives.

Import ListNotations.
Import C.Notations.

(** A computation using the output type of the standard library. *)
Definition C (sig : Signature.t) (A : Type) : Type :=
  C.t sig Output.t A.

Module Log.
  (** Log a message on the standard output. *)
  Definition log {sig : Signature.t} (message : string) : C sig unit :=
    C.write (Output.log (Log.Output.write message)).
End Log.

(** TCP server socket. *)
Module TCPServerSocket.
  (** Bind a socket. *)
  Definition bind {sig : Signature.t} (port : nat) : C sig unit :=
    C.write (Output.socket (TCPServerSocket.Output.bind port)).

  Definition write {sig : Signature.t} (id : TCPServerSocket.Id.t)
    (data : string) : C sig unit :=
    C.write (Output.socket (TCPServerSocket.Output.write id data)).

  Definition close_server {sig : Signature.t} (id : TCPServerSocket.Id.t)
    : C sig unit :=
    C.write (Output.socket (TCPServerSocket.Output.close_server id)).

  Definition close_connection {sig : Signature.t}
    (id : TCPServerSocket.ConnectionId.t) : C sig unit :=
    C.write (Output.socket (TCPServerSocket.Output.close_connection id)).
End TCPServerSocket.