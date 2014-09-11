(** A beginning of a basic web server. *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Computation.

Import ListNotations.

(** * A definition of a toy web server. *)
(** Incoming event. *)
Module Event.
  Inductive t :=
  | Get : string -> t (* Get the profile of a user. *)
  | Put : string -> string -> t (* Update the profile of a user. *).
End Event.

(** Server's answer. *)
Module Answer.
  Inductive t :=
  | Ok : string -> t
  | Error : string -> t.
End Answer.

Module String.
  Require Import Coq.Strings.Ascii.

  Fixpoint eqb (s1 s2 : string) : bool :=
    match (s1, s2) with
    | (EmptyString, EmptyString) => true
    | (EmptyString, String _ _) => false
    | (String _ _, EmptyString) => false
    | (String c1 s1, String c2 s2) =>
      if ascii_dec c1 c2 then
        eqb s1 s2
      else
        false
    end.
End String.

(** The server's database. *)
Module Model.
  (** A association list of user / profile. *)
  Definition t := list (string * string).

  (** An empty model. *)
  Definition empty : t :=
    [].

  (** Add or update an user profile. *)
  Fixpoint add (model : t) (user : string) (profile : string) : t :=
    match model with
    | [] => [(user, profile)]
    | (user', profile') :: model =>
      if String.eqb user user' then
        (user, profile) :: model
      else
        (user', profile') :: add model user profile
    end.

  (** If the database contains the user name. *)
  Fixpoint does_contain (model : t) (user : string) : bool :=
    match model with
    | [] => false
    | (user', _) :: model => orb (String.eqb user user') (does_contain model user)
    end.

  (** Try to find the profile of the user. *)
  Fixpoint find (model : t) (user : string) : option string :=
    match model with
    | [] => None
    | (user', profile') :: model =>
      if String.eqb user user' then
        Some profile'
      else
        find model user
    end.
End Model.

(** The server. *)
Module TestServer.
  Import C.Notations.
  Open Local Scope string.

  (** The main function: handle an event. *)
  Definition process {env : Env.t} `{Ref.C Model.t env} `{Out.C Answer.t env}
    (event : Event.t) : C.t env unit :=
    match event with
    | Event.Get user =>
      let! model := C.get _ in
      match Model.find model user with
      | None => C.write _ (Answer.Error "user not found")
      | Some profile => C.write _ (Answer.Ok profile)
      end
    | Event.Put user profile =>
      let! model := C.get _ in
      do! C.set _ (Model.add model user profile) in
      if Model.does_contain model user then
        C.write _ (Answer.Ok "user updated")
      else
        C.write _ (Answer.Ok "user added")
    end.

  (** Run the server sequentially on a list of events. *)
  Definition run_on_events (events : list Event.t) : list Answer.t :=
    match C.run [Answer.t : Type] (Memory.Cons Model.empty Memory.Nil) (List.iter events process) with
    | (_, _, output) => Output.head output
    end.

  Compute run_on_events [Event.Get "me"].
  Compute run_on_events [Event.Put "me" "hello"; Event.Get "me"].
  Compute run_on_events [Event.Put "me" "hello"; Event.Put "me" "hi"; Event.Get "me"].
End TestServer.