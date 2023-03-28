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
Require Import Aurantium.Compatibility.
Require Import Aurantium.Intersection.
Require Import Aurantium.Hash.

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

Theorem audioFormatTypeEqDec : forall (x y : audioFormatType),
  {x = y}+{x <> y}.
Proof.
  intros x y.
  destruct x; (destruct y; decide equality; apply string_dec).
Qed.

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
  (** The hash of the audio data. *)
  clipHash : hashValue;
  (** The offset of the first octet of audio data. *)
  clipOffset : nat;
  (** The size of the audio data in octets. *)
  clipSize : nat;
}.

Theorem clipEqDec : forall (x y : clip),
  {x = y}+{x <> y}.
Proof.
  intros x y.
  destruct x; (
    destruct y; (
      try decide equality;
      try apply string_dec;
      try decide equality;
      try apply string_dec;
      try apply hashValueEqDec
    )
  ).
  apply hashAlgorithmEqDec.
Qed.

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

(** Find the clip with the given ID. *)
Fixpoint clipForId
  (i  : nat)
  (ca : list clip)
: option clip :=
  match ca with
  | nil         => None
  | cons a rest =>
    match Nat.eq_dec (clipId a) i with
    | left _  => Some a
    | right _ => clipForId i rest
    end
  end.

(** Determine all the elements of _ca_ that are not in _cb_. *)
Definition clipsRemoved
  (ca : list clip)
  (cb : list clip)
: list clip :=
  filter (fun c =>
    match clipForId (clipId c) cb with
    | None   => false
    | Some _ => true
    end) ca.

(** Determine all the elements of _cb_ that are not in _ca_. *)
Definition clipsAdded
  (ca : list clip)
  (cb : list clip)
: list clip :=
  clipsRemoved cb ca.

Definition clipsCompatCompareRemoved
  (r : list clip)
: list compatVersionChangeRecord :=
  map (fun a => CVRMake CVersionChangeMajor "A clip was removed.") r.

Lemma clipsCompatCompareRemovedForall : forall r,
  Forall (fun a => cvrChange a = CVersionChangeMajor)
    (clipsCompatCompareRemoved r).
Proof.
  intros r.
  apply Forall_map.
  induction r as [|y ys]; intuition.
Qed.

Definition clipsCompatCompareAdded
  (r : list clip)
: list compatVersionChangeRecord :=
  map (fun a => CVRMake CVersionChangeMinor "A clip was added.") r.

Lemma clipsCompatCompareAddedForall : forall r,
  [] <> r ->
    Forall (fun a => cvrChange a = CVersionChangeMinor)
      (clipsCompatCompareAdded r).
Proof.
  intros r Hneq.
  apply Forall_map.
  induction r as [|y ys IHy]. {
    contradict Hneq; reflexivity.
  } {
    constructor.
    reflexivity.
    destruct ys as [|z zs]. {
      constructor.
    } {
      apply IHy.
      discriminate.
    }
  }
Qed.

(** The rules that define the version number increments required for
    a pair of clips. *)
Definition clipCompatCompare
  (c0 c1 : clip)
: compatVersionChangeRecord :=
  match clipEqDec c0 c1 with
  | left _ => 
    CVRMake CVersionChangeNone ""
  | right _ => 
    CVRMake CVersionChangeMajor "The values of the clip were changed."
  end.

Definition clipsCompatCompareChanged
  (r : list (clip * clip))
: list compatVersionChangeRecord :=
  map (fun p => clipCompatCompare (fst p) (snd p)) r.

Definition clipsCompatCompareFull
  (ca cb : list clip)
: list compatVersionChangeRecord :=
  let f              := (fun c cs => clipForId (clipId c) cs) in
  let removed        := clipsRemoved ca cb in
  let added          := clipsAdded ca cb in
  let changed        := intersectionPairs f ca cb in
  let removedChanges := clipsCompatCompareRemoved removed in
  let addedChanges   := clipsCompatCompareAdded added in
  let changedChanges := clipsCompatCompareChanged changed in
    removedChanges ++ addedChanges ++ changedChanges.

(** If there's a non-empty list of removed clips, a major version change is required. *)
Theorem clipsCompatCompareMajor0 : forall ca cb,
  [] <> clipsRemoved ca cb ->
    compatVersionChangeRecordsMaximum (clipsCompatCompareFull ca cb)
      = CVersionChangeMajor.
Proof.
  intros ca cb H_ne.
  unfold clipsCompatCompareFull.
  apply compatVersionChangesMaximumCorrect0.
  apply in_map_iff.
  destruct (clipsRemoved ca cb) as [|y ys]. {
    contradict H_ne; reflexivity.
  } {
    simpl.
    exists {| cvrChange := CVersionChangeMajor; cvrReason := "A clip was removed." |}.
    intuition.
  }
Qed.

(** Adding a clip is a minor change. *)
Theorem clipsCompatCompareMinor0 : forall ca cb,
  [] = clipsRemoved ca cb ->
    [] <> clipsAdded ca cb ->
      (forall f, [] = intersectionPairs f ca cb) ->
        compatVersionChangeRecordsMaximum (clipsCompatCompareFull ca cb)
          = CVersionChangeMinor.
Proof.
  intros ca cb Hrm Hadd Hint.
  unfold clipsCompatCompareFull.
  rewrite <- Hrm.
  rewrite <- Hint.
  simpl.
  rewrite app_nil_r.
  clear Hrm.
  clear Hint.

  destruct (clipsAdded ca cb) as [|y ys]. {
    contradict Hadd; reflexivity.
  } {
    unfold compatVersionChangeRecordsMaximum.
    simpl.

    (* We can show that either one of the arguments _must_ be equal to Minor
       and the other to something minor or less. *)
    rewrite (
      compatVersionChangeMaxMinorInv
        CVersionChangeMinor
          (compatVersionChangesMaximum
            (map (fun r : compatVersionChangeRecord => cvrChange r)
               (clipsCompatCompareAdded ys)))
    ).

    unfold clipsCompatCompareAdded.
    rewrite map_map.
    simpl.

    (* We can prove that all elements map to a minor change. *)
    assert (
      Forall
        (fun c => c = CVersionChangeMinor) 
        (map (fun x : clip => CVersionChangeMinor) ys)
    ) as Hfa1. {
      rewrite Forall_map.
      rewrite Forall_forall.
      reflexivity.
    }

    apply CVMMinorLeft.
    constructor. {
      reflexivity.
    } {
      clear Hadd.
      induction (map (fun _ : clip => CVersionChangeMinor) ys) as [|z zs IHz]. {
        right; reflexivity.
      } {
        left.
        pose proof (Forall_inv Hfa1) as Hfb0.
        pose proof (Forall_inv_tail Hfa1) as Hfb1.
        simpl.
        rewrite Hfb0.
        destruct (IHz Hfb1) as [H0|H1]. {
          rewrite H0.
          reflexivity.
        } {
          rewrite H1.
          reflexivity.
        }
      }
    }
  }
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
