(** A beginning of a basic web server. *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Import ListNotations.

(** A list of types to specify the shared memory or the output channels. *)
Module Signature.
  Definition t := list Type.
End Signature.

(** Shared memory. *)
Module Memory.
  Inductive t : Signature.t -> Type :=
  | Nil : t []
  | Cons : forall (A : Type) (sig : Signature.t), A -> t sig -> t (A :: sig).
  Arguments Cons [A sig] _ _.
  
  (** The first shared memory cell. *)
  Definition head (A : Type) (sig : Signature.t) (mem : t (A :: sig)) : A :=
    match mem with
    | Cons _ _ x _ => x
    end.
  Arguments head [A sig] _.
  
  (** The tail of the shared memory. *)
  Definition tail (A : Type) (sig : Signature.t) (mem : t (A :: sig)) : t sig :=
    match mem with
    | Cons _ _ _ mem => mem
    end.
  Arguments tail [A sig] _.
End Memory.

(** List of output channels. *)
Module Output.
  Inductive t : Signature.t -> Type :=
  | Nil : t []
  | Cons : forall (A : Type) (channels : Signature.t),
    list A -> t channels -> t (A :: channels).
  Arguments Cons [A channels] _ _.
  
  (** The first output channel. *)
  Definition head (A : Type) (channels : Signature.t)
    (output : t (A :: channels)) : list A :=
    match output with
    | Cons _ _ x _ => x
    end.
  Arguments head [A channels] _.
  
  (** The tail of the output channels. *)
  Definition tail (A : Type) (channels : Signature.t)
    (output : t (A :: channels)) : t channels :=
    match output with
    | Cons _ _ _ output => output
    end.
  Arguments tail [A channels] _.
  
  (** A list of empty output channels. *)
  Fixpoint init (channels : Signature.t) : t channels :=
    match channels with
    | [] => Nil
    | _ :: channels => Cons [] (init channels)
    end.
End Output.

(** The signatures of the shared memory and of the output channels. *)
Module Env.
  Record t := New {
    references : Signature.t;
    channels : Signature.t }.
End Env.

(** A reference to a shared memory cell. *)
Module Ref.
  Class C (A : Type) (env : Env.t) : Type := New {
    get : Memory.t (Env.references env) -> A;
    set : Memory.t (Env.references env) -> A -> Memory.t (Env.references env) }.

  Instance cons_left (A : Type) (references : Signature.t) (channels : Signature.t)
    : C A (Env.New (A :: references) channels) := {
    get mem := Memory.head mem;
    set mem x := Memory.Cons x (Memory.tail mem) }.

  Instance cons_right (A B : Type) (references : Signature.t) (channels : Signature.t)
    (I : C A (Env.New references channels)) : C A (Env.New (B :: references) channels) := {
    get mem := get (Memory.tail mem);
    set mem x := Memory.Cons (Memory.head mem) (set (Memory.tail mem) x) }.
End Ref.

(** A reference to an output channel. *)
Module Out.
  Class C (A : Type) (env : Env.t) : Type := New {
    write : Output.t (Env.channels env) -> A -> Output.t (Env.channels env) }.

  Instance cons_left (A : Type) (references : Signature.t) (channels : Signature.t)
    : C A (Env.New references (A :: channels)) := {
    write output x := Output.Cons (x :: Output.head output) (Output.tail output) }.

  Instance cons_right (A B : Type) (references : Signature.t) (channels : Signature.t)
    (I : C A (Env.New references channels)) : C A (Env.New references (B :: channels)) := {
    write output x := Output.Cons (Output.head output) (write (Output.tail output) x) }.
End Out.

(** Definition of a computation. *)
Module C.
  Inductive t (env : Env.t) : Type -> Type :=
  | ret : forall (A : Type), A ->
    t env A
  | bind : forall (A B : Type),
    t env A -> (A -> t env B) -> t env B
  | get : forall (A : Type), `{Ref.C A env} ->
    t env A
  | set : forall (A : Type), `{Ref.C A env} ->
    A -> t env unit
  | write : forall (A : Type), `{Out.C A env} ->
    A -> t env unit.
  Arguments ret [env A] _.
  Arguments bind [env A B] _ _.
  Arguments get [env A] {_}.
  Arguments set [env A] {_} _.
  Arguments write [env A] {_} _.

  Fixpoint run_aux (references channels : Signature.t) (A : Type)
    (mem : Memory.t references) (output : Output.t channels)
    (x : t (Env.New references channels) A)
    : A * Memory.t references * Output.t channels :=
    match x with
    | ret _ x => (x, mem, output)
    | bind _ _ x f =>
      match run_aux _ _ _ mem output x with
      | (x, mem, output) => run_aux _ _ _ mem output (f x)
      end
    | get _ _ => (Ref.get mem, mem, output)
    | set _ _ v => (tt, Ref.set mem v, output)
    | write _ _ v => (tt, mem, Out.write output v)
    end.

  (** Run a computation on an initialized shared memory. *)
  Definition run (references : Signature.t) (channels : Signature.t) (A : Type)
    (mem : Memory.t references) (x : t (Env.New references channels) A)
    : A * Memory.t references * Output.t channels :=
    run_aux _ _ _ mem (Output.init channels) x.
  Arguments run [references] _ [A] _ _.

  (** Monadic notation. *)
  Module Notations.
    Notation "'let!' X ':=' A 'in' B" := (bind A (fun X => B))
      (at level 200, X ident, A at level 100, B at level 200).

    Notation "'let!' X ':' T ':=' A 'in' B" := (bind (A := T) A (fun X => B))
      (at level 200, X ident, A at level 100, T at level 200, B at level 200).

    Notation "'do!' A 'in' B" := (bind A (fun _ => B))
      (at level 200, B at level 200).
  End Notations.
End C.

(** Functions on lists. *)
Module List.
  Import C.Notations.

  (** Iterate a computation over a list. *)
  Fixpoint iter {env : Env.t} (A : Type) (l : list A) (f : A -> C.t env unit)
    : C.t env unit :=
    match l with
    | [] => C.ret tt
    | x :: l =>
      do! f x in
      iter _ l f
    end.
  Arguments iter {env} [A] _ _.
End List.

(** Some basic tests. *)
Module Test.
  Import C.Notations.
  Open Local Scope string.

  Definition hello_world {env : Env.t} `{Out.C string env}
    (_ : unit) : C.t env unit :=
    do! C.write _ "Hello " in
    C.write _ "world!".

  Compute C.run [string : Type] Memory.Nil (hello_world tt).

  Definition read_and_print {env : Env.t} `{Ref.C nat env} `{Out.C nat env}
    (_ : unit) : C.t env unit :=
    let! n : nat := C.get _ in
    C.write _ n.

  Compute C.run [nat : Type] (Memory.Cons 12 Memory.Nil) (read_and_print tt).

  Definition hello_read_print {env : Env.t} `{Ref.C nat env} `{Out.C string env} `{Out.C nat env}
    (_ : unit) : C.t env unit :=
    do! hello_world tt in
    read_and_print tt.

  Compute C.run [nat : Type; string : Type] (Memory.Cons 12 Memory.Nil) (hello_read_print tt).

  Definition incr_by {env : Env.t} `{Ref.C nat env}
    (n : nat) : C.t env unit :=
    let! m : nat := C.get _ in
    C.set _ (m + n).

  Definition double_print {env : Env.t} `{Ref.C nat env} `{Out.C nat env}
    (n : nat) : C.t env unit :=
    do! C.set _ 0 in
    do! incr_by n in
    do! incr_by n in
    let! n : nat := C.get _ in
    C.write _ n.

  Compute C.run [nat : Type] (Memory.Cons 15 Memory.Nil) (double_print 12).
End Test.

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