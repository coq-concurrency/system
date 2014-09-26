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
  Inductive t : Set :=
  | get : t.

  Definition of_string (method : string) : option t :=
    if String.eqb method "GET" then
      Some get
    else
      None.
End Method.

(** Parse an HTTP request. *)
Definition parse (request : string) : option (Method.t * string) :=
  let items := String.split request " " in
  match items with
  | method :: url :: _ =>
    match Method.of_string method with
    | Some method => Some (method, url)
    | _ => None
    end
  | _ => None
  end.

Check eq_refl : parse "GET /page.html HTTP/1.0
Host: example.com
Referer: http://example.com/
User-Agent: CERN-LineMode/2.15 libwww/2.17b3" =
  Some (Method.get, "/page.html").

(** The list of connected clients. *)
Module Clients.
  (** A association list of client socket ids / requested files. *)
  Definition t := list (TCPClientSocket.Id.t * string).

  (** An empty table of clients. *)
  Definition empty : t :=
    [].

  (** Add (or update) a client's request. *)
  Fixpoint add (clients : t) (client : TCPClientSocket.Id.t)
    (file_name : string) : t :=
    match clients with
    | [] => [(client, file_name)]
    | (client', file_name') :: clients =>
      if TCPClientSocket.Id.eqb client client' then
        (client, file_name) :: clients
      else
        (client', file_name') :: add clients client file_name
    end.

  (** Try to find a client for a file name. *)
  Fixpoint find (clients : t) (file_name : string)
    : option TCPClientSocket.Id.t :=
    match clients with
    | [] => None
    | (client', file_name') :: clients =>
      if String.eqb file_name file_name' then
        Some client'
      else
        find clients file_name
    end.

  (** Remove a client. *)
  Fixpoint remove (clients : t) (client : TCPClientSocket.Id.t) : t :=
    match clients with
    | [] => []
    | (client', file_name') :: clients =>
      if TCPClientSocket.Id.eqb client client' then
        clients
      else
        (client', file_name') :: remove clients client
    end.
End Clients.

(** The initial memory. *)
Definition mem : Memory.t _ :=
  Memory.Cons Clients.empty Memory.Nil.

(** Start the server. *)
Definition start {sig : Signature.t} (_ : unit) : C sig unit :=
  TCPServerSocket.bind 80.

(** Handle server sockets. *)
Definition handle_server_sockets {sig : Signature.t}
  (input : TCPServerSocket.Input.t) : C sig unit :=
  match input with
  | TCPServerSocket.Input.bound _ => Log.write "Server socket opened."
  end.

(** Handle client sockets. *)
Definition handle_client_sockets {sig : Signature.t} `{Ref.C Clients.t sig}
  (input : TCPClientSocket.Input.t) : C sig unit :=
  match input with
  | TCPClientSocket.Input.accepted _ =>
    Log.write "Client connection accepted."
  | TCPClientSocket.Input.read client request =>
    match parse request with
    | None => Log.write ("Invalid request: " ++ request)
    | Some (Method.get, url) =>
      let! clients := C.get _ in
      do! C.set _ (Clients.add clients client url) in
      do! Log.write ("File " ++ url ++ " requested.") in
      File.read url
    end
  end.

Definition http_answer (content : string) : string :=
  "HTTP/1.0 200 OK
Content-Type: text/plain

" ++ content.

(** Handle files. *)
Definition handle_files {sig : Signature.t} `{Ref.C Clients.t sig}
  (input : File.Input.t) : C sig unit :=
  match input with
  | File.Input.read file_name data =>
    let! clients := C.get _ in
    match Clients.find clients file_name with
    | Some client =>
      do! C.set _ (Clients.remove clients client) in
      TCPClientSocket.write client (http_answer data)
    | None => Log.write ("No client to receive the file " ++ file_name)
    end
  end.

(** Handle all requests. *)
Definition handle {sig : Signature.t} `{Ref.C Clients.t sig} (input : Input.t)
  : C sig unit :=
  match input with
  | Input.client_socket input => handle_client_sockets input
  | Input.server_socket input => handle_server_sockets input
  | Input.file input => handle_files input
  end.

(** Some tests *)
Module Test.
  (** Run the program sequentially on a list of input events. *)
  Definition run (inputs : list Input.t) : list Output.t :=
    let program :=
      do! start tt in
      List.iter inputs handle in
    match C.run mem program with
    | (_, _, output) => output
    end.

  Check eq_refl : run [] = [
    Output.server_socket (TCPServerSocket.Output.bind 80)].

  Definition client := TCPClientSocket.Id.new 12.
  Definition request :=
    "GET info/contact.html HTTP/1.0
Host: example.com
Referer: http://example.com/
User-Agent: CERN-LineMode/2.15 libwww/2.17b3".

  Check eq_refl : run [
    Input.client_socket (TCPClientSocket.Input.accepted client);
    Input.client_socket (TCPClientSocket.Input.read client "wrong request")] = [
    Output.log (Log.Output.write "Invalid request: wrong request");
    Output.log (Log.Output.write "Client connection accepted.");
    Output.server_socket (TCPServerSocket.Output.bind 80)].

  Check eq_refl : run [
    Input.client_socket (TCPClientSocket.Input.accepted client);
    Input.client_socket (TCPClientSocket.Input.read client request)] = [
    Output.file (File.Output.read "info/contact.html");
    Output.log (Log.Output.write "File info/contact.html requested.");
    Output.log (Log.Output.write "Client connection accepted.");
    Output.server_socket (TCPServerSocket.Output.bind 80)].
End Test.

(** Extraction. *)
Require Import Extraction.

Definition http_server := Extraction.run _ mem start handle.
Extraction "tests/httpServer" http_server.