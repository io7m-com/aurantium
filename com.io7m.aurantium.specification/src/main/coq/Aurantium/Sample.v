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
Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.

Import ListNotations.

Set Mangle Names.

Require Import Aurantium.Descriptor.

(** The known sample formats. *)
Inductive sampleFormatType : Set :=
  (** Pulse code modulation using signed values. *)
  | SFPulseCodeModulationSigned : sampleFormatType
  (** Pulse code modulation using unsigned values. *)
  | SFPulseCodeModulationUnsigned : sampleFormatType
  (** FLAC-compressed audio. *)
  | SFFlac : sampleFormatType
  (** A format not known by this specification. *)
  | SFUnknown : descriptor -> sampleFormatType
  .

Open Scope char_scope.
Open Scope string_scope.

Definition sampleFormatDescribe (f : sampleFormatType) : descriptor :=
  match f with
  | SFPulseCodeModulationSigned   => "PCM_SIGNED"
  | SFPulseCodeModulationUnsigned => "PCM_UNSIGNED"
  | SFFlac                        => "FLAC"
  | SFUnknown d                   => d
  end.

#[export]
Instance sampleFormatDescribable : describable sampleFormatType := {
  descriptorOf c := sampleFormatDescribe c
}.

(** The endianness of the octets that make up one channel of an audio frame. *)
Inductive sampleEndiannessType : Set :=
  (** Sample data is big endian. *)
  | SEBigEndian    : sampleEndiannessType
  (** Sample data is little endian. *)
  | SELittleEndian : sampleEndiannessType
  .

(** A description of a single audio sample. *)
Inductive sample : Set := sampleMake {
  (** The unique identifier for the sample. *)
  sampleId         : nat;
  (** The sample name, for descriptive purposes. *)
  sampleName       : string;
  (** The sample format name. *)
  sampleFormat     : sampleFormatType;
  (** The sample rate in bits per second. *)
  sampleRate       : nat;
  (** The sample depth in bits per sample. *)
  sampleDepth      : nat;
  (** The number of channels in the sample. *)
  sampleChannels   : nat;
  (** The endianness of the sample data. *)
  sampleEndianness : sampleEndiannessType;
  (** The offset of the first octet of sample data. *)
  sampleOffset     : nat;
  (** The size of the sample in octets. *)
  sampleSize       : nat;
}.

Inductive samplesListIdIsSorted : list sample -> Prop :=
  | SampleIdOne  : forall s,
      samplesListIdIsSorted [s]
  | SampleIdCons : forall s0 s1 ss,
    (sampleId s0) < (sampleId s1) ->
      samplesListIdIsSorted (s0 :: ss) ->
        samplesListIdIsSorted (s1 :: s0 :: ss).

Inductive samplesListOffsetIsSorted : list sample -> Prop :=
  | SampleOffsetOne : forall s,
    samplesListOffsetIsSorted [s]
  | SampleOffsetCons : forall s0 s1 ss,
    ((sampleOffset s1) + (sampleSize s1)) < sampleOffset s0 ->
      samplesListOffsetIsSorted (s0 :: ss) ->
        samplesListOffsetIsSorted (s1 :: s0 :: ss).

Inductive samples : Set := samplesMake {
  samplesList         : list sample;
  samplesIdSorted     : samplesListIdIsSorted samplesList;
  samplesOffsetSorted : samplesListOffsetIsSorted samplesList;
}.

Lemma samplesNonEmpty : forall (s : samples),
  [] <> samplesList s.
Proof.
  intros s.
  destruct (samplesIdSorted s); discriminate.
Qed.

Definition sampleFirst : forall (s : samples), sample.
Proof.
  intro s.
  pose proof (samplesNonEmpty s) as H_ne.
  destruct (samplesList s) eqn:Hs.
  - contradiction.
  - intuition.
Qed.

