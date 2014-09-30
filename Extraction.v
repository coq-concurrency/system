(** Extraction of computations to OCaml. *)
Require Import Coq.Lists.List.
Require Import Coq.NArith.NArith.
Require Import Coq.Strings.String.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlBigIntConv.
Require Import ExtrOcamlString.
Require Import Computation.
Require Import Pervasives.
Require Import StdLib.

Import ListNotations.
Open Local Scope string.

Module Native.
  (** Sequence two instructions. *)
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

    Parameter append : t -> t -> t.
    Extract Constant append => "fun s1 s2 -> s1 ^ s2".

    Parameter tokenize : t -> list t.
    Extract Constant tokenize => "fun s ->
      Str.split (Str.regexp_string "" "") s".

    Parameter is_empty : t -> bool.
    Extract Constant is_empty => "fun s ->
      String.length s = 0".
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

    Parameter fold_lines : forall A, t -> A -> (A -> String.t -> option A) -> unit.
    Extract Constant fold_lines => "fun (input, _) state f ->
      let rec aux state =
        match input_line input with
        | line ->
          (match f state line with
          | None -> ()
          | Some state -> aux state)
        | exception End_of_file -> () in
      aux state".
  End Process.

  Module BigInt.
    Definition t : Type := bigint.

    Parameter to_string : t -> String.t.
    Extract Constant to_string => "Big_int.string_of_big_int".

    Parameter of_string : String.t -> option t.
    Extract Constant of_string => "fun n ->
      match Big_int.big_int_of_string n with
      | s -> Some s
      | exception _ -> None".

    Definition to_N : t -> N := n_of_bigint.
    Definition of_N : N -> t := bigint_of_n.
  End BigInt.

  Parameter print_error : String.t -> unit.
  Extract Constant print_error => "fun message ->
    prerr_endline message;
    flush stderr".
End Native.

(** Import input events. *)
Module Input.
  Definition import_command (command : Native.String.t) : option Command.t :=
    let command := Native.String.to_string command in
    if String.eqb command "Log" then
      Some Command.Log
    else if String.eqb command "FileRead" then
      Some Command.FileRead
    else if String.eqb command "ServerSocketBind" then
      Some Command.ServerSocketBind
    else if String.eqb command "ClientSocketRead" then
      Some Command.ClientSocketRead
    else if String.eqb command "ClientSocketWrite" then
      Some Command.ClientSocketWrite
    else
      None.
  
  Definition import_bool (b : Native.String.t) : option bool :=
    let b := Native.String.to_string b in
    if String.eqb b "false" then
      Some false
    else if String.eqb b "true" then
      Some true
    else
      None.

  Definition import_N (n : Native.String.t) : option N :=
    option_map Native.BigInt.to_N (Native.BigInt.of_string n).

  Definition import_string (s : Native.String.t) : string :=
    Native.String.to_string (Native.Base64.decode s).

  Definition import_option (s : Native.String.t) : option Native.String.t :=
    if Native.String.is_empty s then
      None
    else
      Some s.

  Definition import (input : Native.String.t) : Input.t + string :=
    match Native.String.tokenize input with
    | command :: id :: arguments =>
      match (import_command command, import_N id) with
      | (None, _) => inr "Unknown command."
      | (_, None) => inr "Invalid id."
      | (Some command, Some id) =>
        match (command, arguments) with
        | (Command.Log, [is_success]) =>
          match import_bool is_success with
          | None => inr "Invalid boolean."
          | Some is_success => inl (Input.New Command.Log id is_success)
          end
        | (Command.FileRead, [content]) =>
          let content := option_map import_string (import_option content) in
          inl (Input.New Command.FileRead id content)
        | (Command.ServerSocketBind, [client_id]) =>
          match import_option client_id with
          | None => inl (Input.New Command.ServerSocketBind id None)
          | Some client_id =>
            match import_N client_id with
            | None => inr "Invalid client_id."
            | Some client_id =>
              let client_id := ClientSocketId.New client_id in
              inl (Input.New Command.ServerSocketBind id (Some client_id))
            end
          end
        | (Command.ClientSocketRead, [content]) =>
          let content := option_map import_string (import_option content) in
          inl (Input.New Command.ClientSocketRead id content)
        | (Command.ClientSocketWrite, [is_success]) =>
          match import_bool is_success with
          | None => inr "Invalid boolean."
          | Some is_success => inl (Input.New Command.Log id is_success)
          end
        | _ => inr "Wrong number of arguments."
        end
      end
    | _ => inr "The input must have at least two elements."
    end.
End Input.

(** Export output events. *)
Module Output.
  (** Concatenate with a space in between. *)
  Definition join (s1 s2 : Native.String.t) : Native.String.t :=
    Native.String.append (Native.String.append s1 (Native.String.of_string " ")) s2.

  Definition export_bool (b : bool) : Native.String.t :=
    if b then
      Native.String.of_string "true"
    else
      Native.String.of_string "false".

  Definition export_N (n : N) : Native.String.t :=
    Native.BigInt.to_string (Native.BigInt.of_N n).

  Definition export_client_id (client_id : ClientSocketId.t) : Native.String.t :=
    match client_id with
    | ClientSocketId.New client_id => export_N client_id
    end.

  Definition export_string (s : string) : Native.String.t :=
    Native.Base64.encode (Native.String.of_string s).

  Definition export (output : Output.t) : Native.String.t :=
    let id := export_N (Output.id output) in
    match output with
    | Output.New Command.Log _ message =>
      let message := export_string message in
      join (Native.String.of_string "Log") message
    | Output.New Command.FileRead _ file_name =>
      join (Native.String.of_string "FileRead") (export_string file_name)
    | Output.New Command.ServerSocketBind _ port =>
      join (Native.String.of_string "ServerSocketBind") (export_N port)
    | Output.New Command.ClientSocketRead _ client_id =>
      join (Native.String.of_string "ClientSocketRead") (export_client_id client_id)
    | Output.New Command.ClientSocketWrite _ (client_id, content) =>
      join (Native.String.of_string "ClientSocketWrite")
        (join (export_client_id client_id) (export_string content))
    end.
End Output.

Definition run (sig : Signature.t) (mem : Memory.t sig)
  (start : unit -> C sig unit) (handle : Input.t -> C sig unit) : unit :=
  let system := Native.Process.run (Native.String.of_string "./systemProxy.native") in
  let fix print_outputs outputs :=
    match outputs with
    | [] => tt
    | output :: outputs =>
      Native.seq
        (fun _ => Native.Process.print_line (Output.export output) system)
        (fun _ => print_outputs outputs)
    end in
  match C.run mem (start tt) with
  | (result, mem, outputs) =>
    Native.seq
      (fun _ => print_outputs outputs)
      (fun _ =>
        match result with
        | None => tt
        | Some _ =>
          Native.Process.fold_lines _ system mem (fun mem input =>
          match Input.import input with
          | inl input =>
            match C.run mem (handle input) with
            | (result, mem, outputs) =>
              Native.seq
                (fun _ => print_outputs outputs)
                (fun _ =>
                  match result with
                  | None => None
                  | Some _ => Some mem
                  end)
            end
          | inr error_message =>
            let error_message := "Input ignored: " ++ error_message in
            Native.seq
              (fun _ => Native.print_error (Native.String.of_string error_message))
              (fun _ => None)
          end)
        end)
  end.