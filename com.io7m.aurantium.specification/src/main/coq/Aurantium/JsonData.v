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

Require Import Coq.Strings.String.
Require Import Coq.Numbers.DecimalString.
Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.

Local Open Scope R_scope.
Local Open Scope string_scope.

Import ListNotations.

Require Import Aurantium.Hash.
Require Import Aurantium.Metadata.
Require Import Aurantium.OctetOrder.
Require Import Aurantium.Json.
Require Import Aurantium.Clip.
Require Import Aurantium.KeyMapping.

Definition float (r : R) :=
  JsonFloat.

Definition flagJson (f : keyAssignmentFlag) : json :=
  JsonString (keyAssignmentFlagDescribe f).

(** The JSON encoding of a key assignment. *)
Definition jsonKeyAssignment (k : keyAssignment) : json :=
  JsonObject [
    ("ID",                        JsonInteger (kaId k));
    ("KeyValueStart",             JsonInteger (kaValueStart k));
    ("KeyValueCenter",            JsonInteger (kaValueCenter k));
    ("KeyValueEnd",               JsonInteger (kaValueEnd k));
    ("ClipID",                    JsonInteger (kaClipId k));
    ("AmplitudeAtKeyStart",       float (kaAmplitudeAtKeyStart k));
    ("AmplitudeAtKeyCenter",      float (kaAmplitudeAtKeyCenter k));
    ("AmplitudeAtKeyEnd",         float (kaAmplitudeAtKeyEnd k));
    ("AtVelocityStart",           float (kaAtVelocityStart k));
    ("AtVelocityCenter",          float (kaAtVelocityCenter k));
    ("AtVelocityEnd",             float (kaAtVelocityEnd k));
    ("AmplitudeAtVelocityStart",  float (kaAmplitudeAtVelocityStart k));
    ("AmplitudeAtVelocityCenter", float (kaAmplitudeAtVelocityCenter k));
    ("AmplitudeAtVelocityEnd",    float (kaAmplitudeAtVelocityEnd k));
    ("Flags",                     JsonArray (map flagJson (kaFlags k)))
  ].

(** The JSON encoding of a set of key assignments. *)
Definition jsonKeyAssignments (ks : list keyAssignment) : json :=
  JsonObject [
    ("%Schema", JsonString "urn:com.io7m.aurantium:1.0");
    ("Clips",   JsonArray (map jsonKeyAssignment ks))
  ].

(** The JSON encoding of a hash value. *)
Definition jsonHash (h : hashValue) : json :=
  JsonObject [
    ("Algorithm", JsonString (hashAlgorithmDescribe (hvAlgorithm h)));
    ("Value",     JsonString (hvValue h)) 
  ].

(** The JSON encoding of a loop range. *)
Definition jsonLoopRange (lr : loopRange) : json :=
  JsonObject [
    ("FrameStart",        JsonInteger (lrFrameStart lr));
    ("FrameEndInclusive", JsonInteger (lrFrameEndInclusive lr)) 
  ].

(** The JSON encoding of an optional loop range. *)
Definition jsonLoopRangeOptionProperty (lr : option loopRange) : list (string * json) :=
  match lr with
  | Some l => [("LoopRange", jsonLoopRange l)]
  | None   => []
  end.

(** The JSON encoding of a clip description. *)
Definition jsonClip (c : clip) : json :=
  JsonObject (app [
    ("ID",           JsonInteger (clipId c));
    ("Name",         JsonString (clipName c));
    ("Format",       JsonString (audioFormatDescribe (clipFormat c)));
    ("SampleRate",   JsonInteger (clipSampleRate c));
    ("SampleDepth",  JsonInteger (clipSampleDepth c));
    ("Channels",     JsonInteger (clipChannels c));
    ("Endianness",   JsonString (octetOrderDescribe (clipEndianness c)));
    ("Hash",         jsonHash (clipHash c));
    ("Offset",       JsonInteger (clipOffset c));
    ("Size",         JsonInteger (clipSize c))
  ] (jsonLoopRangeOptionProperty (clipLoopRange c))).

(** The JSON encoding of a set of clip descriptions. *)
Definition jsonClips (c : list clip) : json :=
  JsonObject [
    ("%Schema", JsonString "urn:com.io7m.aurantium:1.0");
    ("Clips",   JsonArray (map jsonClip c))
  ].

(** The JSON encoding of a list of metadata values. *)
Definition jsonMetadataM (mvs : list metadataValue) : json :=
  JsonObject (map (fun k => (mKey k, JsonString (mValue k))) mvs).

(** The JSON encoding of a list of metadata values. *)
Definition jsonMetadata (m : metadata) : json :=
  JsonObject [
    ("%Schema",  JsonString "urn:com.io7m.aurantium:1.0");
    ("Metadata", jsonMetadataM (mValues m))
  ].

