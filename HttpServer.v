(** A simple HTTP web server. *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Computation.
Require Import Pervasives.
Require Import StdLib.
Require Import String.

Import ListNotations.
Import C.Notations.
Open Local Scope string.

(** The kind of HTTP method. *)
Module Method.
  (** For now, only the GET method is handled. *)
  Inductive t : Type :=
  | get : t.

  Definition of_string (method : string) : option t :=
    if String.eqb method "GET" then
      Some get
    else
      None.
End Method.

(** An url. *)
Module Url.
  (** For now, an url is just a string. *)
  Inductive t : Type :=
  | new : string -> t.

  Definition to_string (url : t) : string :=
    match url with
    | new url => url
    end.

  Definition of_string (url : string) : option t :=
    Some (new url).

  Definition to_file_name (url : t) : option File.Name.t :=
    let names : list string := String.split (to_string url) "/" in
    match List.rev names with
    | base :: path => Some {|
      File.Name.path := List.rev path;
      File.Name.base := base |}
    | [] => None
    end.
End Url.

(** Parse an HTTP request. *)
Definition parse (request : string) : option (Method.t * Url.t) :=
  let items := String.split request " " in
  match items with
  | method :: url :: _ =>
    match (Method.of_string method, Url.of_string url) with
    | (Some method, Some url) => Some (method, url)
    | _ => None
    end
  | _ => None
  end.

Check eq_refl : parse "GET /page.html HTTP/1.0
Host: example.com
Referer: http://example.com/
User-Agent: CERN-LineMode/2.15 libwww/2.17b3" =
  Some (Method.get, Url.new "/page.html").

(** The list of connected clients. *)
Module Clients.
  (** A association list of connection ids / requested files. *)
  Definition t := list (TCPServerSocket.ConnectionId.t * File.Name.t).

  (** An empty table of clients. *)
  Definition empty : t :=
    [].

  (** Add (or update) a client's request. *)
  Fixpoint add (clients : t) (client : TCPServerSocket.ConnectionId.t)
    (file_name : File.Name.t) : t :=
    match clients with
    | [] => [(client, file_name)]
    | (client', file_name') :: clients =>
      if TCPServerSocket.ConnectionId.eqb client client' then
        (client, file_name) :: clients
      else
        (client', file_name') :: add clients client file_name
    end.

  (** Try to find a client for a file name. *)
  Fixpoint find (clients : t) (file_name : File.Name.t)
    : option TCPServerSocket.ConnectionId.t :=
    match clients with
    | [] => None
    | (client', file_name') :: clients =>
      if File.Name.eqb file_name file_name' then
        Some client'
      else
        find clients file_name
    end.

  (** Remove a client. *)
  Fixpoint remove (clients : t) (client : TCPServerSocket.ConnectionId.t) : t :=
    match clients with
    | [] => []
    | (client', file_name') :: clients =>
      if TCPServerSocket.ConnectionId.eqb client client' then
        clients
      else
        (client', file_name') :: remove clients client
    end.
End Clients.

(** Start the server. *)
Definition start {sig : Signature.t} (_ : unit) : C sig unit :=
  TCPServerSocket.bind 80.

(** Handle requests. *)
Definition handler {sig : Signature.t} `{Ref.C Clients.t sig} (input : Input.t)
  : C sig unit :=
  match input with
    | Input.socket input =>
      match input with
      | TCPServerSocket.Input.bound _ => Log.log "Server socket opened."
      | TCPServerSocket.Input.accepted _ =>
        Log.log "Client connection accepted."
      | TCPServerSocket.Input.read client request =>
        match parse request with
        | None => Log.log ("Invalid request: " ++ request)
        | Some (Method.get, url) =>
          match Url.to_file_name url with
          | Some file_name =>
            let! clients := C.get _ in
            do! C.set _ (Clients.add clients client file_name) in
            Log.log ("File " ++ File.Name.to_string file_name ++ " requested")
          | None => Log.log ("Invalid url: " ++ Url.to_string url)
          end
        end
      end
    | Input.file input =>
      match input with
      | File.Input.read file_name data =>
        let! clients := C.get _ in
        match Clients.find clients file_name with
        | Some client =>
          do! C.set _ (Clients.remove clients client) in
          do! TCPServerSocket.write client data in
          TCPServerSocket.close_connection client
        | None =>
          Log.log ("No client to receive the file " ++
            File.Name.to_string file_name)
        end
      end
    end.

(** Some tests *)
Module Test.
  (** Run the program sequentially on a list of input events. *)
  Definition run (inputs : list Input.t) : list Output.t :=
    let program :=
      do! start tt in
      List.iter inputs handler in
    match C.run (Memory.Cons Clients.empty Memory.Nil) program with
    | (_, _, output) => output
    end.

  Check eq_refl : run [] = [Output.socket (TCPServerSocket.Output.bind 80)].

  Definition client := TCPServerSocket.ConnectionId.new 12.
  Definition request :=
    "GET info/contact.html HTTP/1.0
Host: example.com
Referer: http://example.com/
User-Agent: CERN-LineMode/2.15 libwww/2.17b3".

  Check eq_refl : run [
    Input.socket (TCPServerSocket.Input.accepted client);
    Input.socket (TCPServerSocket.Input.read client "wrong request")] = [
    Output.log (Log.Output.write "Invalid request: wrong request");
    Output.log (Log.Output.write "Client connection accepted.");
    Output.socket (TCPServerSocket.Output.bind 80)].
  Check eq_refl : run [
    Input.socket (TCPServerSocket.Input.accepted client);
    Input.socket (TCPServerSocket.Input.read client request)] = [
    Output.log (Log.Output.write "File info/contact.html requested");
    Output.log (Log.Output.write "Client connection accepted.");
    Output.socket (TCPServerSocket.Output.bind 80)].
End Test.