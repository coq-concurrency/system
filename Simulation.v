Require Import Coq.Lists.List.
Require Import Coq.NArith.NArith.
Require Import Coq.Strings.String.
Require Import ErrorHandlers.All.
Require Import ListString.All.
Require Import Computation.
Require Socket.

Import ListNotations.
Local Open Scope type.
Local Open Scope string.
Local Open Scope list.

Module Run.
  Inductive t : C.t -> Type :=
  | Ret : t C.Ret
  | Par : forall {c1 c2 : C.t}, t c1 -> t c2 -> t (C.Par c1 c2)
  | Let : forall {input output : Type} (i : input) (o : output)
    {handler : input -> C.t}, t (handler i) -> t (C.Let input o handler).

  Definition do {output : Type} (o : output) {handler : unit -> C.t}
    (handler_run : t (handler tt)) : t (C.Let _ _ _) :=
    Let tt o handler_run.
End Run.

Module Examples.
  Import C.Notations.

  (** Hello world. *)
  Module HelloWorld.
    Definition program : C.t :=
      do! LString.s "Hello world!" in
      C.Ret.

    Definition run : Run.t program.
      apply (Run.do (LString.s "Hello world!")).
      exact Run.Ret.
    Defined.
  End HelloWorld.

  (** Echo one message. *)
  Module EchoOne.
    Definition program : C.t :=
      let! message : LString.t := tt in
      do! message in
      C.Ret.

    Definition run (message : LString.t) : Run.t program.
      apply (Run.Let message tt).
      apply (Run.do message).
      exact Run.Ret.
    Defined.
  End EchoOne.

  (** Echo a list of messages in sequence. *)
  Module EchoOrdered.
    Fixpoint program (fuel : nat) : C.t :=
      match fuel with
      | O => C.Ret
      | S fuel =>
        let! message : LString.t := tt in
        do! message in
        program fuel
      end.

    Fixpoint run (messages : list LString.t)
      : Run.t (program (List.length messages)).
      destruct messages as [|message messages].
      - exact Run.Ret.
      - apply (Run.Let message tt).
        apply (Run.do message).
        exact (run messages).
    Defined.
  End EchoOrdered.

  (** Echo a list of messages in parallel. *)
  Module EchoUnordered.
    Fixpoint program (fuel : nat) : C.t :=
      match fuel with
      | O => C.Ret
      | S fuel => C.Par EchoOne.program (program fuel)
      end.

    Fixpoint run (messages : list LString.t)
      : Run.t (program (List.length messages)).
      destruct messages as [|message messages].
      - exact Run.Ret.
      - apply Run.Par.
        * exact (EchoOne.run message).
        * exact (run messages).
    Defined.
  End EchoUnordered.

  (** A simple server giving the time to each connection. *)
  Module TimeServer.
    (** Convert a time into a string. *)
    Parameter string_of_time : N -> LString.t.

    (** Send the current time to a client. *)
    Definition handle_client (client_socket : Socket.Client.Id.t) : C.t :=
      let! time : N := "time" in
      let message := string_of_time time in
      let! is_written : bool := ("write", client_socket, message) in
      if is_written then
        let! is_closed : bool := ("close", client_socket) in
        C.Ret
      else
        C.Ret.

    (** Accept in parallel `fuel` clients. *)
    Fixpoint accept_clients (server_socket : Socket.Server.Id.t) (fuel : nat)
      : C.t :=
      match fuel with
      | O => C.Ret
      | S fuel =>
        C.Par (accept_clients server_socket fuel) (
          let! client_socket : option Socket.Client.Id.t :=
            ("accept", server_socket) in
          match client_socket with
          | None => C.Ret
          | Some client_socket => handle_client client_socket
          end)
      end.

    (** The main program. *)
    Definition program (port : N) (fuel : nat) : C.t :=
      let! server_socket : option Socket.Server.Id.t := ("bind", port) in
      match server_socket with
      | None => C.Ret
      | Some server_socket => accept_clients server_socket fuel
      end.

    (** Run a client, assuming the socket writing and closing succeed. *)
    Definition run_handle_client (client_socket : Socket.Client.Id.t) (time : N)
      : Run.t (handle_client client_socket).
      apply (Run.Let time "time").
      apply (Run.Let true ("write", client_socket, _)).
      apply (Run.Let true ("close", client_socket)).
      exact Run.Ret.
    Defined.

    (** Accept a list of clients. *)
    Fixpoint run_accept_clients (server_socket : Socket.Server.Id.t)
      (client_sockets_times : list (Socket.Client.Id.t * N))
      : Run.t (accept_clients server_socket (List.length client_sockets_times)).
      destruct client_sockets_times as [| [client_socket time] client_sockets_times].
      - exact Run.Ret.
      - apply Run.Par.
        * exact (run_accept_clients server_socket client_sockets_times).
        * apply (Run.Let (Some client_socket) ("accept", server_socket)).
          exact (run_handle_client client_socket time).
    Defined.

    (** Run but fail to bind the socket server. *)
    Definition run_unbound (port : N) (fuel : nat) : Run.t (program port fuel).
      apply (Run.Let None ("bind", port)).
      exact Run.Ret.
    Defined.

    (** Run and succeed to bind the socket server. *)
    Definition run_bound (port : N) (server_socket : Socket.Server.Id.t)
      (client_sockets_times : list (Socket.Client.Id.t * N))
      : Run.t (program port (List.length client_sockets_times)).
      apply (Run.Let (Some server_socket) ("bind", port)).
      exact (run_accept_clients server_socket client_sockets_times).
    Defined.
  End TimeServer.
End Examples.

Module Database.
  Import C.Notations.

  Module Kernel.
    Module Message.
      Inductive t (A : Type) : Type :=
      | Stop
      | Read
      | Write (data : A).
    End Message.

    CoFixpoint program (A : Type) (data : A) : C.t :=
      let! message : Message.t A := tt in
      match message with
      | Message.Stop => C.Ret
      | Message.Read =>
        C.Par (program A data) (
          do! data in
          C.Ret)
      | Message.Write data => program A data
      end.

    Module Run.
      Fixpoint only_reads (A : Type) (init : A) (times : nat)
        : Run.t (program A init).
        rewrite C.step_eq.
        destruct times as [|times].
        - apply (Run.Let (Message.Stop A) tt).
          exact Run.Ret.
        - apply (Run.Let (Message.Read A) tt).
          apply Run.Par.
          + exact (only_reads A init times).
          + apply (Run.do init).
            exact Run.Ret.
      Defined.

      Fixpoint writes_then_read (A : Type) (init : A) (datas : list A)
        : Run.t (program A init).
        rewrite C.step_eq.
        destruct datas as [|data datas].
        - apply (Run.Let (Message.Read A) tt).
          apply Run.Par.
          + rewrite C.step_eq.
            apply (Run.Let (Message.Stop A) tt).
            exact Run.Ret.
          + apply (Run.do init).
            exact Run.Ret.
        - apply (Run.Let (Message.Write A data) tt).
          exact (writes_then_read A data datas).
      Defined.      
    End Run.
  End Kernel.

  CoFixpoint handle_client (A : Type) (client : Socket.Client.Id.t) : C.t :=
    let! request : option A := ("read", client) in
    C.Par (handle_client A client) (
      let message :=
        match request with
        | None => Kernel.Message.Read A
        | Some data => Kernel.Message.Write A data
        end in
      do! message in C.Ret).

  CoFixpoint accept_clients (A : Type) (server : Socket.Server.Id.t) : C.t :=
    let! client : option Socket.Client.Id.t := ("accept", server) in
    C.Par (accept_clients A server) (
      match client with
      | None => C.Ret
      | Some client => handle_client A client
      end).

  Definition program (A : Type) (port : N) : C.t :=
    let! server : option Socket.Server.Id.t := ("bind", port) in
    match server with
    | None => C.Ret
    | Some server => accept_clients A server
    end.
End Database.

(** A group of clients can get connected. They must send their name as the
    first message. Next each message is considered as a text message and
    broadcast to other clients, with the sender name. On connection, all
    previous messages are sent to the new client. *)
Module ChatServer.
  Import C.Notations.

  Module Kernel.
    Module Client.
      Definition t := LString.t.
    End Client.

    Module Clients.
      Parameter t : Type.

      Parameter empty : t.
      Parameter add : t -> Socket.Client.Id.t -> Client.t -> t.
      Parameter remove : t -> Socket.Client.Id.t -> t.
      Parameter find : t -> Socket.Client.Id.t -> option Client.t.
      Parameter iter : t -> (Socket.Client.Id.t -> Client.t -> C.t -> C.t) -> C.t -> C.t.
    End Clients.

    Module Messages.
      Definition t := list (LString.t * LString.t).

      Definition add (messages : t) (name : LString.t) (message : LString.t)
        : t :=
        (name, message) :: messages.

      Fixpoint to_string (messages : t) : LString.t :=
        match messages with
        | [] => LString.s ""
        | (name, message) :: messages =>
          name ++ LString.s ": " ++ message ++ [LString.Char.n] ++
          to_string messages
        end.
    End Messages.

    Module Argument.
      Inductive t : Set :=
      | Stop
      | NewClient (name : LString.t)
      | Message (message : LString.t).
    End Argument.

    Module Input.
      Record t : Set := New {
        client : Socket.Client.Id.t;
        argument : Argument.t}.
    End Input.

    Definition welcome_client (client : Socket.Client.Id.t)
      (messages : Messages.t) : C.t :=
      let welcome_message := Messages.to_string messages in
      let! is_success : bool := ("write", client, welcome_message) in
      C.Ret.

    Definition broadcast_message (clients : Clients.t) (name : LString.t)
      (message : LString.t) : C.t :=
      let formatted_message := name ++ LString.s ": " ++ message in
      Clients.iter clients (fun client _ next =>
        let! is_success : bool := ("write", client, formatted_message) in
        next)
        C.Ret.

    CoFixpoint program (clients : Clients.t) (messages : Messages.t) : C.t :=
      let! input : Input.t := tt in
      let client := Input.client input in
      match Input.argument input with
      | Argument.Stop => C.Ret
      | Argument.NewClient name =>
        let clients := Clients.add clients client name in
        C.Par (program clients messages) (welcome_client client messages)
      | Argument.Message message =>
        match Clients.find clients client with
        | None => program clients messages
        | Some name =>
          let messages := Messages.add messages name message in
          C.Par (program clients messages)
            (broadcast_message clients name message)
        end
      end.
  End Kernel.
End ChatServer.
