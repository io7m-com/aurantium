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
From Stdlib Require Import Strings.Ascii.
From Stdlib Require Import Lists.List.

Local Open Scope string_scope.

Import ListNotations.

Require Import Aurantium.Alignment.
Require Import Aurantium.AudioMap.
Require Import Aurantium.Binary.
Require Import Aurantium.Identifier.
Require Import Aurantium.KeyMapping.
Require Import Aurantium.Clip.
Require Import Aurantium.Json.
Require Import Aurantium.JsonData.
Require Import Aurantium.Metadata.

(** The file header. *)
Definition binaryExpFileHeader : binaryExp :=
  BiRecord [
    ("id",           u64 0x894155520D0A1A0A);
    ("versionMajor", u32 1);
    ("versionMinor", u32 0)
  ].

(** The binary encoding of an identifier. *)
Definition binaryIdentifier (i : identifier) : binaryExp :=
  BiRecord [
    ("name",         utf8 (idName i));
    ("versionMajor", u32 (idVersionMajor i));
    ("versionMinor", u32 (idVersionMinor i))
  ].

(** The AURM_ID! section. *)
Definition binaryIdentifierSection (i : identifier) : binaryExp :=
  BiRecord [
    ("id",   u64 0x4155524D5F494421);
    ("size", u64 (binarySizePadded16 (binaryIdentifier i)));
    ("data", binaryIdentifier i)
  ].

(** The AURMEND! section. *)
Definition binaryEndSection : binaryExp := BiRecord [
  ("id",   u64 0x4155524D454E4421);
  ("size", u64 0)
].

(** The AURMCDES section. *)
Definition binaryClipsDescriptionSection (c : list clip) : binaryExp :=
  let text     := jsonSerializeString (jsonClips c) in
  let textUTF8 := utf8 text in
    BiRecord [
      ("id",   u64 0x4155524D43444553);
      ("size", u64 (binarySizePadded16 textUTF8));
      ("data", textUTF8)
    ].

Definition binaryClipsDataSectionAudio (c : clips) : binaryExp :=
  let audioDataSize   := clipAudioDataSizeTotal c in
  let audioDataSize16 := asMultipleOf16 audioDataSize in
    BiRecord [
      ("data", BiReserve audioDataSize16)
    ].

(** The AURMCDAT section. *)
Definition binaryClipsDataSection (c : clips) : binaryExp :=
  BiRecord [
    ("id",   u64 0x4155524D434C4950);
    ("size", u64 (binarySizePadded16 (binaryClipsDataSectionAudio c)));
    ("data", binaryClipsDataSectionAudio c)
  ].

(** The AURMKEYS section. *)
Definition binaryKeyAssignmentsSection (c : list keyAssignment) : binaryExp :=
  let text     := jsonSerializeString (jsonKeyAssignments c) in
  let textUTF8 := utf8 text in
    BiRecord [
      ("id",   u64 0x4155524D4b455953);
      ("size", u64 (binarySizePadded16 textUTF8));
      ("data", textUTF8)
    ].

(** The AURMMETA section. *)
Definition binaryExpMetadataSection (m : metadata) : binaryExp :=
  let text     := jsonSerializeString (jsonMetadata m) in
  let textUTF8 := utf8 text in
    BiRecord [
      ("id",   u64 0x4155524D4D455441);
      ("size", u64 (binarySizePadded16 textUTF8));
      ("data", textUTF8)
    ].

(** An example audio map file as a binary expression. *)
Example binaryExampleFile (m : audioMap) : binaryExp :=
  BiRecord [
    ("file",              binaryExpFileHeader);
    ("id",                binaryIdentifierSection (amIdentifier m));
    ("clipsData",         binaryClipsDataSection (amClips m));
    ("clipsDescriptions", binaryClipsDescriptionSection (clipsList (amClips m)));
    ("keys",              binaryKeyAssignmentsSection (kasList (amKeyAssignments m)));
    ("end",               binaryEndSection)
  ].

