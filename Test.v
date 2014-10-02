(** Test the standard library. *)
Require Import Coq.Lists.List.
Require Import Coq.NArith.NArith.
Require Import Coq.Strings.String.
Require Import Computation.
Require Import Events.
Require Import Extraction.
Require Import StdLib.

Import ListNotations.
Import C.Notations.
Open Local Scope string.

(** Do nothing. *)
Module DoNothing.
  Definition program : C.t [] unit :=
    C.Exit tt.

  Compute Run.run_on_inputs _ program Memory.Nil [].

  (*Definition do_nothing := Extraction.run _ Memory.Nil program.
  Extraction "tests/doNothing" do_nothing.*)
End DoNothing.


(** Say hello. *)
Module HelloWorld.
  Definition program : C.t [] unit :=
    Log.write "Hello" (fun _ =>
    Log.write "world!" (fun _ =>
    C.Exit tt)).

  Compute Run.run_on_inputs _ program Memory.Nil [
    Input.New Command.Log 1 true;
    Input.New Command.Log 2 true ].

  (*Definition hello_world := Extraction.run _ Memory.Nil start handle.
  Extraction "tests/helloWorld" hello_world.*)
End HelloWorld.

(*
(** Print the content of a file. *)
Module ReadFile.
  (** The file to open. *)
  Definition file_name : string := "README.md".

  (** Start the program. *)
  Definition start {sig : Signature.t} (_ : unit) : C sig unit :=
    C.Send (Output.New Command.FileRead 0 file_name).

  (** Handle events. *)
  Definition handle {sig : Signature.t} (input : Input.t) : C sig unit :=
    match input with
    | Input.New Command.FileRead _ (Some content) =>
      C.Send (Output.New Command.Log 0 content)
    | Input.New Command.Log _ _ => C.Exit tt
    | _ => C.Ret tt
    end.

  (*(** Run the program sequentially on a list of input events. *)
  Definition run (inputs : list File.Input.t) : list Output.t :=
    let inputs := List.map Input.File inputs in
    let program :=
      do! start tt in
      List.iter inputs handle in
    match C.run Memory.Nil program with
    | (_, _, output) => output
    end.


  Check eq_refl : run [] = [Output.File (File.Output.Read file_name)].
  Check eq_refl : run [File.Input.Read file_name "nameserver 34.123.45.46"] = [
    Output.Log (Log.Output.Write "nameserver 34.123.45.46");
    Output.File (File.Output.Read file_name)].*)

  Definition read_file := Extraction.run _ Memory.Nil start handle.
  Extraction "tests/readFile" read_file.
End ReadFile.

(** A server logging all the incoming messages. *)
Module LogServer.
  Definition port : N := 4 % N.

  (** Start the program. *)
  Definition start {sig : Signature.t} (_ : unit) : C sig unit :=
    C.Send (Output.New Command.ServerSocketBind 0 port).

  (** Handle events. *)
  Definition handle {sig : Signature.t} (input : Input.t) : C sig unit :=
    match input with
    | Input.New Command.ServerSocketBind _ None =>
        C.Send (Output.New Command.Log 0 "The server socket cannot open.")
    | Input.New Command.Log 0 _ => C.Exit tt
    | Input.New Command.ServerSocketBind _ (Some client_id) =>
      do! C.Send (Output.New Command.Log 1 "Client connection accepted.") in
      C.Send (Output.New Command.ClientSocketRead 0 client_id)
    | Input.New Command.ClientSocketRead _ (Some content) =>
      C.Send (Output.New Command.Log 2 content)
    | _ => C.Ret tt
    end.

  (*(** Run the program sequentially on a list of input events. *)
  Definition run (inputs : list Input.t) : list Output.t :=
    let program :=
      do! start tt in
      List.iter inputs handle in
    match C.run Memory.Nil program with
    | (_, _, output) => output
    end.

  Check eq_refl : run [] = [
    Output.ServerSocket (TCPServerSocket.Output.Bind port)].
  Check eq_refl : run [
    Input.ServerSocket (TCPServerSocket.Input.Bound (TCPServerSocket.Id.New 12))] = [
    Output.Log (Log.Output.Write "Server socket opened.");
    Output.ServerSocket (TCPServerSocket.Output.Bind port)].
  Check eq_refl : run [
    Input.ServerSocket (TCPServerSocket.Input.Bound (TCPServerSocket.Id.New 12));
    Input.ClientSocket (TCPClientSocket.Input.Accepted (TCPClientSocket.Id.New 23));
    Input.ClientSocket (TCPClientSocket.Input.Read (TCPClientSocket.Id.New 23) "hi")] = [
    Output.ClientSocket (TCPClientSocket.Output.Write (TCPClientSocket.Id.New 23) "hi");
    Output.Log (Log.Output.Write "Input: hi");
    Output.Log (Log.Output.Write "Client connection accepted.");
    Output.Log (Log.Output.Write "Server socket opened.");
    Output.ServerSocket (TCPServerSocket.Output.Bind port)].*)

  Definition log_server := Extraction.run _ Memory.Nil start handle.
  Extraction "tests/logServer" log_server.
End LogServer.
*)