(** An API to log text. *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Computation.

Import ListNotations.
Import C.Notations.

Module Output.
  Inductive t : Type :=
  | write : string -> t.
End Output.