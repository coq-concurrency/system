(** Events. *)
Require Import Coq.Lists.List.
Require Import Coq.NArith.NArith.
Require Import Coq.PArith.PArith.
Require Import ListString.All.

Import ListNotations.
Local Open Scope type.

Module ClientSocketId.
  Inductive t : Set :=
  | New : N -> t.
End ClientSocketId.

Module Command.
  Inductive t : Set :=
  | Log
  | FileRead
  | ServerSocketBind
  | ClientSocketRead | ClientSocketWrite | ClientSocketClose.

  (** The type of the parameters of a request. *)
  Definition request (command : t) : Set :=
    match command with
    | Log => LString.t
    | FileRead => LString.t
    | ServerSocketBind => N
    | ClientSocketRead => ClientSocketId.t
    | ClientSocketWrite => ClientSocketId.t * LString.t
    | ClientSocketClose => ClientSocketId.t
    end.

  (** The type of the parameters of an answer. *)
  Definition answer (command : t) : Set :=
    match command with
    | Log => bool
    | FileRead => option LString.t
    | ServerSocketBind => option ClientSocketId.t
    | ClientSocketRead => option LString.t
    | ClientSocketWrite => bool
    | ClientSocketClose => bool
    end.

  Definition eq_dec (command1 command2 : t) :
    {command1 = command2} + {command1 <> command2}.
    destruct command1; destruct command2;
      try (left; congruence);
      try (right; congruence).
  Defined.
End Command.

Module Input.
  Record t : Set := New {
    command : Command.t;
    id : positive;
    argument : Command.answer command }.
End Input.

Module Output.
  Record t : Set := New {
    command : Command.t;
    id : positive;
    argument : Command.request command }.
End Output.