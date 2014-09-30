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

(*
(** Log data. *)
Module Log.
  (** Log a message on the standard output. *)
  Definition write {sig : Signature.t} (message : string) : C sig unit :=
    C.Send (Output.Log (Log.Output.Write message)).
End Log.

(** Read a file. *)
Module File.
  (** Read all the content of a file. *)
  Definition read {sig : Signature.t} (file_name : string) : C sig unit :=
    C.Send (Output.File (File.Output.Read file_name)).
End File.

(** TCP client socket. *)
Module TCPClientSocket.
  (** Write a message. *)
  Definition write {sig : Signature.t} (id : TCPClientSocket.Id.t)
    (data : string) : C sig unit :=
    C.Send (Output.ClientSocket (TCPClientSocket.Output.Write id data)).

  (** Close a socket. *)
  Definition close {sig : Signature.t} (id : TCPClientSocket.Id.t)
    : C sig unit :=
    C.Send (Output.ClientSocket (TCPClientSocket.Output.Close id)).
End TCPClientSocket.

(** TCP server socket. *)
Module TCPServerSocket.
  (** Bind a socket. *)
  Definition bind {sig : Signature.t} (port : nat) : C sig unit :=
    C.Send (Output.ServerSocket (TCPServerSocket.Output.Bind port)).

  (** Close a socket. *)
  Definition close {sig : Signature.t} (id : TCPServerSocket.Id.t)
    : C sig unit :=
    C.Send (Output.ServerSocket (TCPServerSocket.Output.Close id)).
End TCPServerSocket.
*)