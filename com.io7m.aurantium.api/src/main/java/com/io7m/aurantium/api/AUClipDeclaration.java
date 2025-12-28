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
import java.util.Optional;

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
 * @param loopRange   The clip loop range
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
  long size,
  Optional<AUClipLoopRange> loopRange)
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
   * @param loopRange   The clip loop range
   */

  public AUClipDeclaration
  {
    Objects.requireNonNull(id, "id");
    Objects.requireNonNull(name, "name");
    Objects.requireNonNull(format, "format");
    Objects.requireNonNull(endianness, "endianness");
    Objects.requireNonNull(hash, "hash");
    Objects.requireNonNull(loopRange, "loopRange");

    if (sampleRate == 0L) {
      throw new IllegalArgumentException("Sample rate must be non-zero.");
    }
    if (sampleDepth == 0L) {
      throw new IllegalArgumentException("Sample depth must be non-zero.");
    }
    if (channels == 0L) {
      throw new IllegalArgumentException("Channels must be non-zero.");
    }

    loopRange.ifPresent(range -> {
      final var endInclusive = range.frameEndInclusive();
      final var endMax = size / (sampleDepth >>> 3L);
      if (Long.compareUnsigned(endInclusive, endMax) >= 0) {
        throw new IllegalArgumentException(
          "Loop range inclusive end %s must be < frame count %s"
            .formatted(
              Long.toUnsignedString(endInclusive),
              Long.toUnsignedString(endMax)
            )
        );
      }
    });
  }

  /**
   * @return The number of frames implied by the clip description
   */

  public long frames()
  {
    return this.size / this.sampleSizeOctets();
  }

  /**
   * @return The size of a single sample in octets
   */

  public long sampleSizeOctets()
  {
    return this.sampleDepth >>> 3L;
  }

  /**
   * @return The size of a single frame in octets
   */

  public long frameSizeOctets()
  {
    return this.sampleSizeOctets() * this.channels;
  }

  /**
   * @return The number of samples implied by the clip description
   */

  public long samples()
  {
    return this.frames() * this.channels;
  }
}
