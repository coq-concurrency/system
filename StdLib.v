(** The standard library. *)
Require Import Coq.Lists.List.
Require Import Coq.NArith.NArith.
Require Import Coq.Strings.String.
Require Import Computation.
Require Import Events.

Import ListNotations.

(** Log data. *)
Module Log.
  (** Log a message on the standard output. *)
  Definition write {sig : Signature.t} (message : string)
    (call_back : bool -> C.t sig unit) : C.t sig unit :=
    C.Send Command.Log message call_back.
End Log.


(** Read a file. *)
Module File.
  (** Read all the content of a file. *)
  Definition read {sig : Signature.t} (file_name : string)
    (call_back : option string -> C.t sig unit) : C.t sig unit :=
    C.Send Command.FileRead file_name call_back.
End File.

(** TCP client socket. *)
Module ClientSocket.
  (** Read a message. *)
  Definition read {sig : Signature.t} (id : ClientSocketId.t)
    (call_back : option string -> C.t sig unit) : C.t sig unit :=
    C.Send Command.ClientSocketRead id call_back.

  (** Write a message. *)
  Definition write {sig : Signature.t} (id : ClientSocketId.t) (data : string)
    (call_back : bool -> C.t sig unit) : C.t sig unit :=
    C.Send Command.ClientSocketWrite (id, data) call_back.

  (** Close the socket. *)
  Definition close {sig : Signature.t} (id : ClientSocketId.t)
    (call_back : bool -> C.t sig unit) : C.t sig unit :=
    C.Send Command.ClientSocketClose id call_back.
End ClientSocket.

(** TCP server socket. *)
Module ServerSocket.
  (** Bind a socket. *)
  Definition bind {sig : Signature.t} (port : N)
    (call_back : option ClientSocketId.t -> C.t sig unit) : C.t sig unit :=
    C.Send Command.ServerSocketBind port call_back.
End ServerSocket.