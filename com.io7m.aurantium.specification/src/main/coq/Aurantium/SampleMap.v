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

Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.

Import ListNotations.

Require Import Aurantium.Compatibility.
Require Import Aurantium.Identifier.
Require Import Aurantium.Sample.
Require Import Aurantium.KeyMapping.

(** The key assignment _k_ references sample _s_. *)
Definition keyAssignmentReferencesSample
  (k : keyAssignment)
  (s : sample)
: Prop :=
  (kaSampleId k) = (sampleId s).

(** The sample referenced by _k_ exists in _s_. *)
Definition keyAssignmentReferences
  (k : keyAssignment)
  (s : samples)
: Prop :=
  exists p, keyAssignmentReferencesSample k p /\ In p (samplesList s).

(** All key assignment in _k_ reference samples that exist in _s_. *)
Definition keyAssignmentsReferences
  (k : keyAssignments)
  (s : samples)
: Prop :=
  forall p, In p (kasList k) -> keyAssignmentReferences p s.

(** Every sample in _ss_ has at least one reference in _k_. *)
Definition samplesReferenced
  (k  : keyAssignments)
  (ss : samples)
: Prop :=
  Forall (fun s => exists a, keyAssignmentReferencesSample a s /\ In s (samplesList ss)) (samplesList ss).

Inductive sampleMap : Set := {
  smIdentifier               : identifier;
  smSamples                  : samples;
  smKeyAssignments           : keyAssignments;
  smKeyAssignmentsReferences : keyAssignmentsReferences smKeyAssignments smSamples;
  smSamplesReferenced        : samplesReferenced smKeyAssignments smSamples;
}.
