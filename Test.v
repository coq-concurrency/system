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

  Definition test1 : Run.run_on_inputs _ program Memory.Nil [] = (true, []) :=
    eq_refl.

  Definition do_nothing := Extraction.run _ Memory.Nil program.
  Extraction "tests/doNothing" do_nothing.
End DoNothing.


(** Say hello. *)
Module HelloWorld.
  Definition program : C.t [] unit :=
    Log.write "Hello" (fun _ =>
    Log.write "world!" (fun _ =>
    C.Exit tt)).

  Definition test1 : Run.run_on_inputs _ program Memory.Nil [
    Input.New Command.Log 1 true;
    Input.New Command.Log 2 true ] =
    (true, [
      Output.New Command.Log 2 "world!";
      Output.New Command.Log 1 "Hello" ]) :=
    eq_refl.

  Definition test2 : Run.run_on_inputs _ program Memory.Nil [
    Input.New Command.Log 2 true;
    Input.New Command.Log 1 true ] =
    (false, [
      Output.New Command.Log 2 "world!";
      Output.New Command.Log 1 "Hello" ]) :=
    eq_refl.

  Definition hello_world := Extraction.run _ Memory.Nil program.
  Extraction "tests/helloWorld" hello_world.
End HelloWorld.

(** Print the content of a file. *)
Module ReadFile.
  (** The file to open. *)
  Definition file_name : string := "README.md".

  Definition program : C.t [] unit :=
    File.read file_name (fun content =>
    let message := match content with
      | None => "Error: cannot read the file."
      | Some content => content
      end in
    Log.write message (fun _ => C.Exit tt)).

  Definition read_file := Extraction.run _ Memory.Nil program.
  Extraction "tests/readFile" read_file.
End ReadFile.

(** A server responding to all incoming messages. *)
Module EchoServer.
  Definition port : N := 5 % N.

  Definition program : C.t [] unit :=
    ServerSocket.bind port (fun client_id =>
      match client_id with
      | None =>
        do! Log.write "Server socket failed." (fun _ => C.Ret tt) in
        C.Exit tt
      | Some client_id =>
        ClientSocket.read client_id (fun content =>
        match content with
        | None => C.Ret tt
        | Some content =>
          ClientSocket.write client_id content (fun _ =>
          Log.write content (fun _ => C.Ret tt))
        end)
      end).

  Definition echo_server := Extraction.run _ Memory.Nil program.
  Extraction "tests/echoServer" echo_server.
End EchoServer.