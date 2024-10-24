/*
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
 */

package com.io7m.aurantium.api;

import java.util.Objects;

/**
 * A clip declaration.
 *
 * @param id          The clip ID
 * @param name        The clip name
 * @param format      The clip audio format
 * @param sampleRate  The sample rate
 * @param sampleDepth The sample depth
 * @param channels    The channel count
 * @param endianness  The endianness
 * @param hash        The hash value
 * @param size        The audio size
 */

public record AUClipDeclaration(
  AUClipID id,
  String name,
  AUAudioFormatType format,
  long sampleRate,
  long sampleDepth,
  long channels,
  AUOctetOrder endianness,
  AUHashValue hash,
  long size)
{
  /**
   * A clip declaration.
   *
   * @param id          The clip ID
   * @param name        The clip name
   * @param format      The clip audio format
   * @param sampleRate  The sample rate
   * @param sampleDepth The sample depth
   * @param channels    The channel count
   * @param endianness  The endianness
   * @param hash        The hash value
   * @param size        The audio size
   */

  public AUClipDeclaration
  {
    Objects.requireNonNull(id, "id");
    Objects.requireNonNull(name, "name");
    Objects.requireNonNull(format, "format");
    Objects.requireNonNull(endianness, "endianness");
    Objects.requireNonNull(hash, "hash");

    if (sampleRate == 0L) {
      throw new IllegalArgumentException("Sample rate must be non-zero.");
    }
    if (sampleDepth == 0L) {
      throw new IllegalArgumentException("Sample depth must be non-zero.");
    }
    if (channels == 0L) {
      throw new IllegalArgumentException("Channels must be non-zero.");
    }
  }
}
