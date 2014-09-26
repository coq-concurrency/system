(** Test the standard library. *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Computation.
Require Import Pervasives.
Require Import StdLib.

Import ListNotations.
Import C.Notations.
Open Local Scope string.

(** Says hello. *)
Module HelloWorld.
  (** Start the program. *)
  Definition start {sig : Signature.t} (_ : unit) : C sig unit :=
    Log.write "Hello world!".

  (** Handle events (no event to handle). *)
  Definition handle {sig : Signature.t} (_ : Input.t) : C sig unit :=
    C.ret tt.

  Check eq_refl : C.run Memory.Nil (start tt) =
    (tt, Memory.Nil, [Output.log (Log.Output.write "Hello world!")]).

  Require Import Extraction.
  Definition hello_world := Extraction.run _ Memory.Nil start handle.
  Extraction "tests/hello_world" hello_world.
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
    | Input.file input =>
      match input with
      | File.Input.read _ data => Log.write data
      end
    | _ => C.ret tt
    end.

  (** Run the program sequentially on a list of input events. *)
  Definition run (inputs : list File.Input.t) : list Output.t :=
    let inputs := List.map Input.file inputs in
    let program :=
      do! start tt in
      List.iter inputs handle in
    match C.run Memory.Nil program with
    | (_, _, output) => output
    end.


  Check eq_refl : run [] = [Output.file (File.Output.read resolv)].
  Check eq_refl : run [File.Input.read resolv "nameserver 34.123.45.46"] = [
    Output.log (Log.Output.write "nameserver 34.123.45.46");
    Output.file (File.Output.read resolv)].

  Require Import Extraction.
  Definition read_file := Extraction.run _ Memory.Nil start handle.
  Extraction "tests/read_file" read_file.
End ReadFile.

(** An echo server logging all the incoming messages. *)
Module EchoServer.
  (** Start the program. *)
  Definition start {sig : Signature.t} (_ : unit) : C sig unit :=
    TCPServerSocket.bind 8383.

  (** Handle events. *)
  Definition handle {sig : Signature.t} (input : Input.t) : C sig unit :=
    match input with
    | Input.server_socket input =>
      match input with
      | TCPServerSocket.Input.bound _ => Log.write "Server socket opened."
      end
    | Input.client_socket input =>
      match input with
      | TCPClientSocket.Input.accepted _ =>
        Log.write "Client connection accepted."
      | TCPClientSocket.Input.read id data =>
        do! Log.write ("Input: " ++ data) in
        do! TCPClientSocket.write id data in
        TCPClientSocket.close id
      end
    | _ => C.ret tt
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
    Output.server_socket (TCPServerSocket.Output.bind 8383)].
  Check eq_refl : run [
    Input.server_socket (TCPServerSocket.Input.bound (TCPServerSocket.Id.new 12))] = [
    Output.log (Log.Output.write "Server socket opened.");
    Output.server_socket (TCPServerSocket.Output.bind 8383)].
  Check eq_refl : run [
    Input.server_socket (TCPServerSocket.Input.bound (TCPServerSocket.Id.new 12));
    Input.client_socket (TCPClientSocket.Input.accepted (TCPClientSocket.Id.new 23));
    Input.client_socket (TCPClientSocket.Input.read (TCPClientSocket.Id.new 23) "hi")] = [
    Output.client_socket (TCPClientSocket.Output.close (TCPClientSocket.Id.new 23));
    Output.client_socket (TCPClientSocket.Output.write (TCPClientSocket.Id.new 23) "hi");
    Output.log (Log.Output.write "Input: hi");
    Output.log (Log.Output.write "Client connection accepted.");
    Output.log (Log.Output.write "Server socket opened.");
    Output.server_socket (TCPServerSocket.Output.bind 8383)].

  Require Import Extraction.
  Definition echo_server := Extraction.run _ Memory.Nil start handle.
  Extraction "tests/echo_server" echo_server.
End EchoServer.