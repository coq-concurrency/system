(** Experiments for a file system API. *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Computation.

Import ListNotations.

Module FileId.
  Definition t : Type := nat.
End FileId.

Module OutputEvent.
  Inductive t : Type :=
  | open : list string -> string -> t
  | read : FileId.t -> nat -> t.
End OutputEvent.

Module InputEvent.
  Inductive t : Type :=
  | opened : FileId.t -> bool -> t
  | read : FileId.t -> option string -> t.
End InputEvent.