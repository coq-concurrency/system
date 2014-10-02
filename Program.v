Require Import Coq.Lists.List.
Require Import Computation.
Require Import Events.
Require Import Run.

Import ListNotations.
Import C.Notations.

Record t (sig : Signature.t) : Type := New {
  start : unit -> C.t sig unit;
  handle : Input.t -> C.t sig unit }.

Definition run (sig : Signature.t) (program : t sig) (mem : Memory.t sig)
  (inputs : list Input.t) : list Output.t :=
  let program :=
    do! start _ program tt in
    List.iter inputs (handle _ program) in
  match Run.run (CallBacks.empty _) mem [] program with
  | (_, _, _, outputs) => outputs
  end.