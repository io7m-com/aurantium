(*
 * Copyright © 2025 Mark Raynsford <code@io7m.com> https://www.io7m.com
 *
 * Permission to use, copy, modify, and/or distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 * WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
 * SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 * ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR
 * IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import Numbers.DecimalString.
From Stdlib Require Import Lists.List.

Local Open Scope string_scope.

Import ListNotations.

(** A JSON expression. *)
Inductive json : Set :=
  (** A boolean constant. *)
  | JsonBoolean : bool -> json
  (** An integer constant. *)
  | JsonInteger : nat -> json
  (** A floating point constant. *)
  | JsonFloat   : json
  (** A string constant. *)
  | JsonString  : string -> json
  (** An object. *)
  | JsonObject  : list (string * json) -> json
  (** An array. *)
  | JsonArray   : list json -> json
  .

(** The string representation of a boolean. *)
Definition boolString (b : bool) : string :=
  match b with
  | true  => "true"
  | false => "false"
  end.

(** The string representation of an integer. *)
Definition string_of_nat (n : nat) : string :=
  NilZero.string_of_uint (Nat.to_uint n).

(** The tokens that make up a serialized JSON expression. *)
Inductive jsonToken : Set :=
  | JTTrue        : jsonToken
  | JTFalse       : jsonToken
  | JTInteger     : nat -> jsonToken
  | JTFloat       : jsonToken
  | JTString      : string -> jsonToken
  | JTObjectStart : jsonToken
  | JTObjectEnd   : jsonToken
  | JTEquals      : jsonToken
  | JTComma       : jsonToken
  | JTArrayStart  : jsonToken
  | JTArrayEnd    : jsonToken
  .

(** Insert comma tokens between each element of the list. *)
Fixpoint jsonComma (ss : list (list jsonToken)) : list jsonToken :=
  match ss with
  | []        => []
  | (x :: []) => x
  | (x :: xs) => x ++ JTComma :: (jsonComma xs)
  end.

(** An example empty object. *)
Example objectEmpty0 :=
  JsonObject [

  ].

(** An example simple object. *)
Example objectSimple0 :=
  JsonObject [
    ("x", JsonInteger 23);
    ("y", JsonInteger 24);
    ("z", JsonInteger 25)
  ].

(** An example simple array. *)
Example arraySimple0 :=
  JsonArray [
    (JsonInteger 23);
    (JsonInteger 24);
    (JsonInteger 25)
  ].

(** Serialize a JSON expression to a list of JSON tokens. *)
Fixpoint jsonSerialize (j : json) : list jsonToken :=
  match j with
  | JsonBoolean true  => [JTTrue]
  | JsonBoolean false => [JTFalse] 
  | JsonInteger n     => [JTInteger n]
  | JsonFloat         => [JTFloat]
  | JsonString s      => [JTString s]
  | JsonObject o      =>
    let props := map (fun p => JTString (fst p) :: JTEquals :: jsonSerialize (snd p)) o in
      JTObjectStart :: (jsonComma props) ++ [JTObjectEnd]
  | JsonArray a       =>
    let values := map jsonSerialize a in
      JTArrayStart :: (jsonComma values) ++ [JTArrayEnd]
  end.

(** Convert a JSON token to a string. *)
Definition jsonStringOne (t : jsonToken) : string :=
  match t with
  | JTTrue        => "true"
  | JTFalse       => "false"
  | JTInteger n   => string_of_nat n
  | JTFloat       => "#"
  | JTString s    => """" ++ s ++ """"
  | JTObjectStart => "{"
  | JTObjectEnd   => "}"
  | JTEquals      => "="
  | JTComma       => ","
  | JTArrayStart  => "["
  | JTArrayEnd    => "]"
  end.

(** Serialize a JSON expression to a string. *)
Definition jsonSerializeString (j : json) : string :=
  let tokens := jsonSerialize j in
  let texts  := map jsonStringOne tokens in
    fold_left append texts "".

