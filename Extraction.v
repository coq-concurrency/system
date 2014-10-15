(** Extraction of computations to OCaml. *)
Require Import Coq.Lists.List.
Require Import Coq.NArith.NArith.
Require Import Coq.PArith.PArith.
Require Import Coq.Strings.String.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlBigIntConv.
Require Import ExtrOcamlString.
Require Import LString.All.
Require Import "Computation".
Require Import "Events".
Require Import "Run".

Import ListNotations.
Local Open Scope string.
Local Open Scope list.

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

    Parameter to_string : t -> LString.t.
    Extract Constant to_string => "fun s ->
      let l = ref [] in
      for i = 0 to String.length s - 1 do
        l := (*Char.to_ascii*) s.[i] :: !l
      done;
      List.rev !l".

    Parameter of_string : LString.t -> t.
    Extract Constant of_string => "fun s ->
      List.fold_right (fun c s -> String.make 1 (*Char.of_ascii*) c ^ s) s """"".

    Parameter append : t -> t -> t.
    Extract Constant append => "fun s1 s2 -> s1 ^ s2".

    Parameter tokenize : t -> list t.
    Extract Constant tokenize => "fun s ->
      Str.split_delim (Str.regexp_string "" "") s".

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

    Definition to_positive : t -> positive := pos_of_bigint.
    Definition of_positive : positive -> t := bigint_of_pos.

    Definition to_N : t -> N := n_of_bigint.
    Definition of_N : N -> t := bigint_of_n.
  End BigInt.

  Parameter print_error : String.t -> unit.
  Extract Constant print_error => "fun message ->
    prerr_endline message;
    flush stderr".

  Parameter argv : list String.t.
  Extract Constant argv => "Array.to_list Sys.argv".
End Native.

(** Import input events. *)
Module Input.
  Definition import_command (command : Native.String.t) : option Command.t :=
    let command := Native.String.to_string command in
    if LString.eqb command (LString.s "Log") then
      Some Command.Log
    else if LString.eqb command (LString.s "FileRead") then
      Some Command.FileRead
    else if LString.eqb command (LString.s "ServerSocketBind") then
      Some Command.ServerSocketBind
    else if LString.eqb command (LString.s "ClientSocketRead") then
      Some Command.ClientSocketRead
    else if LString.eqb command (LString.s "ClientSocketWrite") then
      Some Command.ClientSocketWrite
    else if LString.eqb command (LString.s "ClientSocketClose") then
      Some Command.ClientSocketClose
    else
      None.
  
  Definition import_bool (b : Native.String.t) : option bool :=
    let b := Native.String.to_string b in
    if LString.eqb b (LString.s "false") then
      Some false
    else if LString.eqb b (LString.s "true") then
      Some true
    else
      None.

  Definition import_positive (n : Native.String.t) : option positive :=
    option_map Native.BigInt.to_positive (Native.BigInt.of_string n).

  Definition import_N (n : Native.String.t) : option N :=
    option_map Native.BigInt.to_N (Native.BigInt.of_string n).

  Definition import_string (s : Native.String.t) : LString.t :=
    Native.String.to_string (Native.Base64.decode s).

  Definition import_option (s : Native.String.t) : option Native.String.t :=
    if Native.String.is_empty s then
      None
    else
      Some s.

  Definition import (input : Native.String.t) : Input.t + LString.t :=
    match Native.String.tokenize input with
    | command :: id :: arguments =>
      match (import_command command, import_positive id) with
      | (None, _) => inr (LString.s "Unknown command.")
      | (_, None) => inr (LString.s "Invalid id.")
      | (Some command, Some id) =>
        match (command, arguments) with
        | (Command.Log, [is_success]) =>
          match import_bool is_success with
          | None => inr (LString.s "Invalid boolean.")
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
            | None => inr (LString.s "Invalid client_id.")
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
          | None => inr (LString.s "Invalid boolean.")
          | Some is_success => inl (Input.New Command.ClientSocketWrite id is_success)
          end
        | (Command.ClientSocketClose, [is_success]) =>
          match import_bool is_success with
          | None => inr (LString.s "Invalid boolean.")
          | Some is_success => inl (Input.New Command.ClientSocketClose id is_success)
          end
        | _ => inr (LString.s "Wrong number of arguments.")
        end
      end
    | _ => inr (LString.s "The input must have at least two elements.")
    end.
End Input.

(** Export output events. *)
Module Output.
  (** Concatenate with a space in between. *)
  Definition join (s1 s2 : Native.String.t) : Native.String.t :=
    Native.String.append (Native.String.append s1
      (Native.String.of_string (LString.s " "))) s2.

  Definition export_bool (b : bool) : Native.String.t :=
    if b then
      Native.String.of_string (LString.s "true")
    else
      Native.String.of_string (LString.s "false").

  Definition export_positive (n : positive) : Native.String.t :=
    Native.BigInt.to_string (Native.BigInt.of_positive n).

  Definition export_N (n : N) : Native.String.t :=
    Native.BigInt.to_string (Native.BigInt.of_N n).

  Definition export_client_id (client_id : ClientSocketId.t) : Native.String.t :=
    match client_id with
    | ClientSocketId.New client_id => export_N client_id
    end.

  Definition export_string (s : LString.t) : Native.String.t :=
    Native.Base64.encode (Native.String.of_string s).

  Definition export (output : Output.t) : Native.String.t :=
    let id := export_positive (Output.id output) in
    let start (s : string) :=
      join (Native.String.of_string (LString.s s)) id in
    match output with
    | Output.New Command.Log _ message =>
      let message := export_string message in
      join (start "Log") message
    | Output.New Command.FileRead _ file_name =>
      join (start "FileRead") (export_string file_name)
    | Output.New Command.ServerSocketBind _ port =>
      join (start "ServerSocketBind") (export_N port)
    | Output.New Command.ClientSocketRead _ client_id =>
      join (start "ClientSocketRead") (export_client_id client_id)
    | Output.New Command.ClientSocketWrite _ (client_id, content) =>
      join (start "ClientSocketWrite")
        (join (export_client_id client_id) (export_string content))
    | Output.New Command.ClientSocketClose _ client_id =>
      join (start "ClientSocketClose") (export_client_id client_id)
    end.
End Output.

Definition run (sig : Signature.t) (mem : Memory.t sig)
  (program : list LString.t -> C.t sig unit) : unit :=
  let system := Native.Process.run (Native.String.of_string
    (LString.s "coqConcurrencyProxy.native")) in
  let fix print_outputs outputs :=
    match outputs with
    | [] => tt
    | output :: outputs =>
      Native.seq
        (fun _ => Native.Process.print_line (Output.export output) system)
        (fun _ => print_outputs outputs)
    end in
  let argv := List.map Native.String.to_string Native.argv in
  match Run.run _ _ (CallBacks.empty _) mem [] (program argv) with
  | (result, call_backs, mem, outputs) =>
    Native.seq
      (fun _ => print_outputs outputs)
      (fun _ =>
        match result with
        | None => tt
        | Some _ =>
          let state := (call_backs, mem) in
          Native.Process.fold_lines _ system state (fun state input =>
            let (call_backs, mem) := state in
            match Input.import input with
            | inl (Input.New command id argument) =>
              match CallBacks.find _ call_backs command id with
              | None => Some state
              | Some (CallBack.New _ a handler) =>
                match Run.run _ _ call_backs mem [] (handler a argument) with
                | (result, call_backs, mem, outputs) =>
                  Native.seq
                    (fun _ => print_outputs outputs)
                    (fun _ =>
                      match result with
                      | None => None
                      | Some a =>
                        let call_backs :=
                          match a with
                          | None => call_backs
                          | Some a =>
                            let call_back := CallBack.New _ command _ a handler in
                            CallBacks.update _ call_backs id command call_back
                          end in
                        Some (call_backs, mem)
                      end)
                end
              end
            | inr error_message =>
              let error_message :=
                LString.s "Input '" ++ Native.String.to_string input ++
                LString.s "'ignored: " ++ error_message in
              Native.seq
                (fun _ => Native.print_error (Native.String.of_string error_message))
                (fun _ => Some state)
            end)
        end)
  end.