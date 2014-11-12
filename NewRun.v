Require Import Coq.Lists.List.
Require Import Computation.
Require Import Events.

Import ListNotations.

Module World.
  Definition t : Set := nat -> forall (command : Command.t),
    list (Command.answer command).
End World.
