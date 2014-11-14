Require Import Coq.Lists.List.
Require Import Computation.
Require Import Events.

Import ListNotations.

Module Commands.
  Inductive t : Set :=
  | Ret : t
  | Bind : t -> t -> t
  | Send : forall (command : Command.t), (Command.answer command -> t) -> t.

  (*Fixpoint eval {A : Type} (x : C.t A) : t :=
    match x with
    | C.Ret _ _ => Ret
    | C.Bind _ _ x f =>
      Bind (eval x) (eval (f (C.run x)))
    | C.Send command _ handler =>
      Send command (fun answer => eval (handler answer))
    end.*)
End Commands.

Module SpecC.
  Inductive t : Type -> Commands.t -> Type :=
  | Ret : forall {A : Type}, A -> t A Commands.Ret
  | Bind : forall {A B : Type} {commands1 commands2 : Commands.t},
    t A commands1 -> (A -> t B commands2) -> t B (Commands.Bind commands1 commands2)
  | Send : forall (command : Command.t) (commands : Command.answer command -> Commands.t),
    Command.request command ->
    (forall (answer : Command.answer command), t unit (commands answer)) ->
    t unit (Commands.Send command commands).
End SpecC.

(*Module Outputs.
  Inductive t : Type :=
  | Ret : t
  | Bind : t -> t -> t
  | Send : forall (command : Command.t),
End Outputs.*)

Module System.
  Inductive t : Commands.t -> Type :=
  | Ret : t Commands.Ret
  | Bind : forall {commands_x commands_y : Commands.t},
    t commands_x -> t commands_y -> t (Commands.Bind commands_x commands_y)
  | Send : forall (command : Command.t)
    (handler : Command.answer command -> Commands.t),
    (Command.request command ->
      {answer : Command.answer command & t (handler answer)}) ->
    t (Commands.Send command handler).

  Fixpoint run {A : Type} (x : C.t A) (s : t (Commands.eval x)) : A.
    destruct x as [A x | A B x f | ].
    - exact x.
    - simpl in s.
      inversion_clear s.
      exact (
        let _ := run _ x X in
        run _ (f (C.run x)) X0).
    - simpl in s.
      inversion s.
      refine (let (answer, s_answer) := X r in
        run _ (t0 answer) _).
      assert (handler0 = (fun answer : Command.answer command => Commands.eval (t0 answer))).
      congruence.
intuition.

      assert (answer0 ).
      Check
        let (answer, s_answer) := X r in
        run _ (t0 answer) s_answer.
      

  Fixpoint run {A : Type} (x : C.t A) : t (snd (Outputs.run x)) -> A :=
    match x in C.t A return t (snd (Outputs.run x)) -> A with
    | C.Ret _ x => fun _ => x
    | C.Bind _ _ x f => fun s =>
      match s in t (Outputs.Bind _ _) return A with
      | Bind _ _ s_x s_f =>
        let x := run x s_x in
        run (f x) s_f
      end
    end.
End System.
