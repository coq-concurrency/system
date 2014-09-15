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
  | Input.socket input => C.ret tt
  end.