(** The standard library. *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Computation.
Require Import Pervasives.

Import ListNotations.
Import C.Notations.

(** A computation using the output type of the standard library. *)
Definition C (sig : Signature.t) (A : Type) : Type :=
  C.t sig Output.t A.

(** Log data. *)
Module Log.
  (** Log a message on the standard output. *)
  Definition log {sig : Signature.t} (message : string) : C sig unit :=
    C.write (Output.log (Log.Output.write message)).
End Log.

(** Read a file. *)
Module File.
  (** Read all the content of a file. *)
  Definition read {sig : Signature.t} (file_name : string) : C sig unit :=
    C.write (Output.file (File.Output.read file_name)).
End File.

(** TCP client socket. *)
Module TCPClientSocket.
  (** Write a message. *)
  Definition write {sig : Signature.t} (id : TCPClientSocket.Id.t)
    (data : string) : C sig unit :=
    C.write (Output.client_socket (TCPClientSocket.Output.write id data)).

  (** Close a socket. *)
  Definition close {sig : Signature.t} (id : TCPClientSocket.Id.t)
    : C sig unit :=
    C.write (Output.client_socket (TCPClientSocket.Output.close id)).
End TCPClientSocket.

(** TCP server socket. *)
Module TCPServerSocket.
  (** Bind a socket. *)
  Definition bind {sig : Signature.t} (port : nat) : C sig unit :=
    C.write (Output.server_socket (TCPServerSocket.Output.bind port)).

  (** Close a socket. *)
  Definition close {sig : Signature.t} (id : TCPServerSocket.Id.t)
    : C sig unit :=
    C.write (Output.server_socket (TCPServerSocket.Output.close id)).
End TCPServerSocket.