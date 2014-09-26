(** Extraction of computations to OCaml. *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlIntConv.
Require Import ExtrOcamlString.
Require Import Computation.
Require Import Pervasives.
Require Import StdLib.

Import ListNotations.
Open Local Scope string.

Module Native.
  Parameter seq : forall A, (unit -> unit) -> (unit -> A) -> A.
  Arguments seq [A] _ _.
  Extract Constant seq => "fun f g ->
    f ();
    g ()".

  Module String.
    Parameter t : Set.
    Extract Constant t => "string".

    Parameter to_string : t -> string.
    Extract Constant to_string => "fun s ->
      let l = ref [] in
      for i = 0 to String.length s - 1 do
        l := s.[i] :: !l
      done;
      List.rev !l".

    Parameter of_string : string -> t.
    Extract Constant of_string => "fun s ->
      List.fold_right (fun c s -> String.make 1 c ^ s) s """"".

    Parameter to_int : t -> option int.
    Extract Constant to_int => "fun s ->
      try Some (int_of_string s)
      with Failure ""int_of_string"" -> None".

    Parameter of_int : int -> t.
    Extract Constant of_int => "string_of_int".

    Parameter append : t -> t -> t.
    Extract Constant append => "fun s1 s2 -> s1 ^ s2".

    Parameter tokenize : t -> list t.
    Extract Constant tokenize => "fun s ->
      Str.split (Str.regexp_string "" "") s".
  End String.

  Module Base64.
    Parameter encode : String.t -> String.t.
    Extract Constant encode => "Base64.encode".

    Parameter decode : String.t -> String.t.
    Extract Constant decode => "Base64.decode".
  End Base64.

  Module Process.
    Parameter t : Set.
    Extract Constant t => "in_channel * out_channel".

    Parameter run : String.t -> t.
    Extract Constant run => "Unix.open_process".

    Parameter print_line : String.t -> t -> unit.
    Extract Constant print_line => "fun message (_, output) ->
      output_string output (message ^ ""\n"");
      flush output".

    Parameter fold_lines : forall A, t -> A -> (A -> String.t -> A) -> unit.
    Extract Constant fold_lines => "fun (input, _) state f ->
      let rec aux state =
        try aux (f state (input_line input))
        with End_of_file -> () in
      aux state".
  End Process.

  Parameter print_error : String.t -> unit.
  Extract Constant print_error => "fun message ->
    prerr_endline message;
    flush stderr".
End Native.

(** Import input events. *)
Module Input.
  Module Command.
    Inductive t : Set :=
    | file_read
    | tcp_client_socket_accepted | tcp_client_socket_read
    | tcp_server_socket_bound.

    Definition of_string (command : string) : option t :=
      if String.eqb command "File.read" then
        Some file_read
      else if String.eqb command "TCPClientSocket.accepted" then
        Some tcp_client_socket_accepted
      else if String.eqb command "TCPClientSocket.read" then
        Some tcp_client_socket_read
      else if String.eqb command "TCPServerSocket.bound" then
        Some tcp_server_socket_bound
      else
        None.
  End Command.

  Definition import_file_read (file_name : Native.String.t) (content : Native.String.t)
    : Input.t :=
    let file_name := Native.String.to_string (Native.Base64.decode file_name) in
    let content := Native.String.to_string (Native.Base64.decode content) in
    Input.file (File.Input.read file_name content).

  Definition to_nat (n : Native.String.t) : option nat :=
    match Native.String.to_int n with
    | None => None
    | Some n => Some (nat_of_int n)
    end.

  Definition import (input : Native.String.t) : Input.t + string :=
    match Native.String.tokenize input with
    | [] => inr "The input cannot be empty."
    | command :: arguments =>
      let command := Command.of_string (Native.String.to_string command) in
      match (command, arguments) with
      | (None, _) => inr "Invalid command."
      | (Some Command.file_read, [file_name; content]) =>
        let file_name := Native.String.to_string (Native.Base64.decode file_name) in
        let content := Native.String.to_string (Native.Base64.decode content) in
        inl (Input.file (File.Input.read file_name content))
      | (Some Command.tcp_client_socket_accepted, [id]) =>
        match to_nat id with
        | None => inr "Expected an integer."
        | Some id =>
          let id := TCPClientSocket.Id.new id in
          inl (Input.client_socket (TCPClientSocket.Input.accepted id))
        end
      | (Some Command.tcp_client_socket_read, [id; content]) =>
        match to_nat id with
        | None => inr "Expected an integer."
        | Some id =>
          let id := TCPClientSocket.Id.new id in
          let content := Native.String.to_string (Native.Base64.decode content) in
          inl (Input.client_socket (TCPClientSocket.Input.read id content))
        end
      | (Some Command.tcp_server_socket_bound, [id]) =>
        match to_nat id with
        | None => inr "Expected an integer."
        | Some id =>
          let id := TCPServerSocket.Id.new id in
          inl (Input.server_socket (TCPServerSocket.Input.bound id))
        end
      | (Some _, _) => inr "Wrong number of arguments."
      end
    end.
End Input.

(** Export output events. *)
Module Output.
  Definition join (s1 s2 : Native.String.t) : Native.String.t :=
    Native.String.append (Native.String.append s1 (Native.String.of_string " ")) s2.

  Definition of_nat (n : nat) : Native.String.t :=
    Native.String.of_int (int_of_nat n).

  Definition export (output : Output.t) : Native.String.t :=
    let string s := Native.String.of_string s in
    let base64 s := Native.Base64.encode (Native.String.of_string s) in
    let client_id id :=
      of_nat (match id with TCPClientSocket.Id.new id => id end) in
    let server_id id :=
      of_nat (match id with TCPServerSocket.Id.new id => id end) in
    match output with
    | Output.log (Log.Output.write message) =>
      join (string "Log.write") (base64 message)
    | Output.file (File.Output.read file_name) =>
      join (string "File.read") (base64 file_name)
    | Output.system System.Output.exit => string "System.exit"
    | Output.client_socket (TCPClientSocket.Output.write id message) =>
      join (string "TCPClientSocket.write")
        (join (client_id id) (base64 message))
    | Output.client_socket (TCPClientSocket.Output.close id) =>
      join (string "TCPClientSocket.close") (client_id id)
    | Output.server_socket (TCPServerSocket.Output.bind port) =>
      let port := of_nat port in
      join (string "TCPServerSocket.bind") port
    | Output.server_socket (TCPServerSocket.Output.close id) =>
      join (string "TCPServerSocket.close") (server_id id)
    end.
End Output.

Definition run (sig : Signature.t) (mem : Memory.t sig)
  (start : unit -> C sig unit) (handle : Input.t -> C sig unit) : unit :=
  let last triple :=
    match triple with
    | (x, y, z) => (y, z)
    end in
  let system := Native.Process.run (Native.String.of_string "./systemProxy.native") in
  let fix print_outputs outputs :=
    match outputs with
    | [] => tt
    | output :: outputs =>
      Native.seq (fun _ => Native.Process.print_line (Output.export output) system)
        (fun _ => print_outputs outputs)
    end in
  let (mem, outputs) := last (C.run mem (start tt)) in
  Native.seq (fun _ => print_outputs outputs)
    (fun _ => Native.Process.fold_lines _ system mem (fun mem input =>
      match Input.import input with
      | inl input =>
        let (mem, outputs) := last (C.run mem (handle input)) in
        Native.seq (fun _ => print_outputs outputs) (fun _ => mem)
      | inr error_message =>
        let error_message := "Input ignored: " ++ error_message in
        Native.seq
          (fun _ => Native.print_error (Native.String.of_string error_message))
          (fun _ => mem)
      end)).