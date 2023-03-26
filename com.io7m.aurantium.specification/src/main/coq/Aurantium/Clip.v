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
Require Import Coq.Reals.Reals.
Require Import Psatz.

Import ListNotations.

Set Mangle Names.

Require Import Aurantium.Descriptor.
Require Import Aurantium.OctetOrder.

(** The known audio formats. *)
Inductive audioFormatType : Set :=
  (** Pulse code modulation using signed values. *)
  | AFPCMLinearIntegerSigned : audioFormatType
  (** Pulse code modulation using unsigned values. *)
  | AFPCMLinearIntegerUnsigned : audioFormatType
  (** Pulse code modulation using floating point values. *)
  | AFPCMLinearFloat : audioFormatType
  (** FLAC-compressed audio. *)
  | AFFlac : audioFormatType
  (** A format not known by this specification. *)
  | AFUnknown : descriptor -> audioFormatType
  .

Open Scope char_scope.
Open Scope string_scope.

Definition audioFormatDescribe (f : audioFormatType) : descriptor :=
  match f with
  | AFPCMLinearIntegerSigned   => "PCM_LINEAR_INTEGER_SIGNED"
  | AFPCMLinearIntegerUnsigned => "PCM_LINEAR_INTEGER_UNSIGNED"
  | AFPCMLinearFloat           => "PCM_LINEAR_FLOAT"
  | AFFlac                     => "FLAC"
  | AFUnknown d                => d
  end.

#[export]
Instance audioFormatDescribable : describable audioFormatType := {
  descriptorOf c := audioFormatDescribe c
}.

(** A description of a single audio clip. *)
Inductive clip : Set := clipMake {
  (** The unique identifier for the clip. *)
  clipId : nat;
  (** The clip name, for descriptive purposes. *)
  clipName : string;
  (** The clip audio format name. *)
  clipFormat : audioFormatType;
  (** The sample rate in bits per second. *)
  clipSampleRate : nat;
  (** The clip sample depth in bits per clip. *)
  clipSampleDepth : nat;
  (** The number of channels in the clip. *)
  clipChannels : nat;
  (** The endianness of the audio data. *)
  clipEndianness : octetOrder;
  (** The offset of the first octet of audio data. *)
  clipOffset : nat;
  (** The size of the audio data in octets. *)
  clipSize : nat;
}.

Inductive clipsListIdIsSorted : list clip -> Prop :=
  | ClipIdOne  : forall s,
      clipsListIdIsSorted [s]
  | ClipIdCons : forall s0 s1 ss,
    (clipId s0) < (clipId s1) ->
      clipsListIdIsSorted (s0 :: ss) ->
        clipsListIdIsSorted (s1 :: s0 :: ss).

Inductive clipsListOffsetIsSorted : list clip -> Prop :=
  | ClipOffsetOne : forall s,
    clipsListOffsetIsSorted [s]
  | ClipOffsetCons : forall s0 s1 ss,
    ((clipOffset s1) + (clipSize s1)) < clipOffset s0 ->
      clipsListOffsetIsSorted (s0 :: ss) ->
        clipsListOffsetIsSorted (s1 :: s0 :: ss).

Inductive clips : Set := clipsMake {
  clipsList         : list clip;
  clipsIdSorted     : clipsListIdIsSorted clipsList;
  clipsOffsetSorted : clipsListOffsetIsSorted clipsList;
}.

Lemma clipsNonEmpty : forall (s : clips),
  [] <> clipsList s.
Proof.
  intros s.
  destruct (clipsIdSorted s); discriminate.
Qed.

Definition clipFirst : forall (s : clips), clip.
Proof.
  intro s.
  pose proof (clipsNonEmpty s) as H_ne.
  destruct (clipsList s) eqn:Hs.
  - contradiction.
  - intuition.
Qed.

Open Scope R_scope.

Unset Mangle Names.

Definition pcmIntegerEncodeSigned
  (depth     : nat)
  (amplitude : R)
: R :=
  match Rle_dec 0 amplitude with
  | left _  => Rmult amplitude ((pow 2 (depth - 1)) - 1)
  | right _ => Rmult amplitude (pow 2 (depth - 1))
  end.

Remark pcmIntegerEncodeSigned16_Low : pcmIntegerEncodeSigned 16 (-1) = -32768.
Proof.
  unfold pcmIntegerEncodeSigned.
  destruct (Rle_dec 0 (-1)) as [HL|HR]. {
    contradict HL.
    lra.
  } {
    assert (sub 16 1 = 15%nat) as H0 by lia.
    rewrite H0.
    assert (2 ^ 15 = 32768) as H1 by lra.
    rewrite H1.
    lra.
  }
Qed.

Remark pcmIntegerEncodeSigned16_Mid : pcmIntegerEncodeSigned 16 0 = 0.
Proof.
  unfold pcmIntegerEncodeSigned.
  destruct (Rle_dec 0 0) as [HL|HR]. {
    lra.
  } {
    contradict HR; lra.
  }
Qed.

Remark pcmIntegerEncodeSigned16_High : pcmIntegerEncodeSigned 16 1 = 32767.
Proof.
  unfold pcmIntegerEncodeSigned.
  destruct (Rle_dec 0 1) as [HL|HR]. {
    assert (sub 16 1 = 15%nat) as H0 by lia.
    rewrite H0.
    assert (2 ^ 15 - 1 = 32767) as H1 by lra.
    rewrite H1.
    lra.
  } {
    contradict HR; lra.
  }
Qed.

Definition pcmIntegerEncodeUnsigned
  (depth     : nat)
  (amplitude : R)
: R :=
  let s : R := Rplus (Rdiv amplitude 2%R) 0.5%R in
    Rmult s (pow 2 depth).

Remark pcmIntegerEncodeUnsigned16_Low : pcmIntegerEncodeUnsigned 16 (-1) = 0.
Proof.
  unfold pcmIntegerEncodeUnsigned.
  lra.
Qed.

Remark pcmIntegerEncodeUnsigned16_Mid : pcmIntegerEncodeUnsigned 16 0 = 32768.
Proof.
  unfold pcmIntegerEncodeUnsigned.
  lra.
Qed.

Remark pcmIntegerEncodeUnsigned16_High : pcmIntegerEncodeUnsigned 16 1 = 65536.
Proof.
  unfold pcmIntegerEncodeUnsigned.
  lra.
Qed.
