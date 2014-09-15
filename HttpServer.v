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

  Definition of_string (url : string) : option t :=
    Some (new url).
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