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

import com.io7m.aurantium.api.AUAudioFormatType.AUAudioFormatStandard;
import com.io7m.aurantium.api.AUAudioFormatType.AUAudioFormatUnknown;
import com.io7m.lanark.core.RDottedName;

import java.util.Objects;

/**
 * Functions over audio formats.
 */

public final class AUAudioFormats
{
  private AUAudioFormats()
  {

  }

  /**
   * Parse an audio format.
   *
   * @param text The descriptor
   *
   * @return An audio format
   *
   * @throws IllegalArgumentException On unrecognized or invalid descriptors
   */

  public static AUAudioFormatType parse(
    final String text)
    throws IllegalArgumentException
  {
    final var name = new RDottedName(text);

    for (final var standard : AUAudioFormatStandard.values()) {
      if (Objects.equals(standard.descriptor(), name)) {
        return standard;
      }
    }

    return new AUAudioFormatUnknown(name);
  }
}
