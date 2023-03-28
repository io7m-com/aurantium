(*
 * Copyright © 2023 Mark Raynsford <code@io7m.com> https://www.io7m.com
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

Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.

Require Import Aurantium.Descriptor.

Open Scope string_scope.

Inductive hashAlgorithm : Set :=
  | HA_SHA256
  .

Theorem hashAlgorithmEqDec : forall (x y : hashAlgorithm),
  {x = y}+{x <> y}.
Proof.
  intros x.
  destruct x;
    (destruct y;
      try decide equality
    ).
Qed.

Definition hashAlgorithmDescribe (f : hashAlgorithm) : descriptor :=
  match f with
  | HA_SHA256   => "SHA-256"
  end.

Inductive hashValue : Set := hashValueMake {
  hvAlgorithm : hashAlgorithm;
  hvValue     : string
}.

Theorem hashValueEqDec : forall (x y : hashValue),
  {x = y}+{x <> y}.
Proof.
  intros x.
  destruct x;
    (destruct y;
      try decide equality;
      try apply string_dec;
      try decide equality
    ).
Qed.
