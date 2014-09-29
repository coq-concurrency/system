(** Test the standard library. *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Computation.
Require Import Pervasives.
Require Import StdLib.
Require Import Extraction.

Import ListNotations.
Import C.Notations.
Open Local Scope string.

(** Says hello. *)
Module HelloWorld.
  (** Start the program. *)
  Definition start {sig : Signature.t} (_ : unit) : C sig unit :=
    do! Log.write "Hello world!" in
    System.exit tt.

  (** Handle events (no event to handle). *)
  Definition handle {sig : Signature.t} (_ : Input.t) : C sig unit :=
    C.Ret tt.

  Check eq_refl : C.run Memory.Nil (start tt) =
    (tt, Memory.Nil, [
      Output.System System.Output.Exit;
      Output.Log (Log.Output.Write "Hello world!")]).

  Definition hello_world := Extraction.run _ Memory.Nil start handle.
  Extraction "tests/helloWorld" hello_world.
End HelloWorld.

(** Prints the content of a file. *)
Module ReadFile.
  (** The file to open. *)
  Definition resolv : string := "README.md".

  (** Start the program. *)
  Definition start {sig : Signature.t} (_ : unit) : C sig unit :=
    File.read resolv.

  (** Handle events. *)
  Definition handle {sig : Signature.t} (input : Input.t) : C sig unit :=
    match input with
    | Input.File input =>
      match input with
      | File.Input.Read _ data => Log.write data
      end
    | _ => C.Ret tt
    end.

  (** Run the program sequentially on a list of input events. *)
  Definition run (inputs : list File.Input.t) : list Output.t :=
    let inputs := List.map Input.File inputs in
    let program :=
      do! start tt in
      List.iter inputs handle in
    match C.run Memory.Nil program with
    | (_, _, output) => output
    end.


  Check eq_refl : run [] = [Output.File (File.Output.Read resolv)].
  Check eq_refl : run [File.Input.Read resolv "nameserver 34.123.45.46"] = [
    Output.Log (Log.Output.Write "nameserver 34.123.45.46");
    Output.File (File.Output.Read resolv)].

  Definition read_file := Extraction.run _ Memory.Nil start handle.
  Extraction "tests/readFile" read_file.
End ReadFile.

(** An echo server logging all the incoming messages. *)
Module EchoServer.
  Definition port : nat := 4.

  (** Start the program. *)
  Definition start {sig : Signature.t} (_ : unit) : C sig unit :=
    TCPServerSocket.bind port.

  (** Handle events. *)
  Definition handle {sig : Signature.t} (input : Input.t) : C sig unit :=
    match input with
    | Input.ServerSocket input =>
      match input with
      | TCPServerSocket.Input.Bound _ => Log.write "Server socket opened."
      end
    | Input.ClientSocket input =>
      match input with
      | TCPClientSocket.Input.Accepted _ =>
        Log.write "Client connection accepted."
      | TCPClientSocket.Input.Read id data =>
        do! Log.write ("Input: " ++ data) in
        TCPClientSocket.write id data
      end
    | _ => C.Ret tt
    end.

  (** Run the program sequentially on a list of input events. *)
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
    Output.ServerSocket (TCPServerSocket.Output.Bind port)].

  Definition echo_server := Extraction.run _ Memory.Nil start handle.
  Extraction "tests/echoServer" echo_server.
End EchoServer.