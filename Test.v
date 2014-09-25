(** Test the standard library. *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Computation.
Require Import Pervasives.
Require Import StdLib.

Import ListNotations.
Import C.Notations.
Open Local Scope string.

(** Print the content of a file. *)
Module ReadFile.
  (** The file to open. *)
  Definition resolv : string := "/etc/resolv.conf".

  (** Start the program. *)
  Definition start {sig : Signature.t} (_ : unit) : C sig unit :=
    File.read resolv.

  (** Handle events. *)
  Definition handler {sig : Signature.t} (input : Input.t) : C sig unit :=
    match input with
    | Input.file input =>
      match input with
      | File.Input.read _ data => Log.log data
      end
    | _ => C.ret tt
    end.

  (** Run the program sequentially on a list of input events. *)
  Definition run (inputs : list File.Input.t) : list Output.t :=
    let inputs := List.map Input.file inputs in
    let program :=
      do! start tt in
      List.iter inputs handler in
    match C.run Memory.Nil program with
    | (_, _, output) => output
    end.


  Check eq_refl : run [] = [Output.file (File.Output.read resolv)].
  Check eq_refl : run [File.Input.read resolv "nameserver 34.123.45.46"] = [
    Output.log (Log.Output.write "nameserver 34.123.45.46");
    Output.file (File.Output.read resolv)].
End ReadFile.

(** An echo server logging all the incoming messages. *)
Module EchoServer.
  (** Start the program. *)
  Definition start {sig : Signature.t} (_ : unit) : C sig unit :=
    TCPServerSocket.bind 8383.

  (** Handle events. *)
  Definition handler {sig : Signature.t} (input : Input.t) : C sig unit :=
    match input with
    | Input.server_socket input =>
      match input with
      | TCPServerSocket.Input.bound _ => Log.log "Server socket opened."
      end
    | Input.client_socket input =>
      match input with
      | TCPClientSocket.Input.accepted _ =>
        Log.log "Client connection accepted."
      | TCPClientSocket.Input.read id data =>
        do! Log.log ("Input: " ++ data) in
        do! TCPClientSocket.write id data in
        TCPClientSocket.close id
      end
    | _ => C.ret tt
    end.

  (** Run the program sequentially on a list of input events. *)
  Definition run (inputs : list Input.t) : list Output.t :=
    let program :=
      do! start tt in
      List.iter inputs handler in
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
End EchoServer.