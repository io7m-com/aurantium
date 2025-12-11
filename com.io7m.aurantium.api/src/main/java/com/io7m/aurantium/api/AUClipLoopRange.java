/*
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
 */

package com.io7m.aurantium.api;

/**
 * A loop range for a clip.
 *
 * @param frameStart        The starting frame
 * @param frameEndInclusive The inclusive ending frame
 */

public record AUClipLoopRange(
  long frameStart,
  long frameEndInclusive)
{
  /**
   * A loop range for a clip.
   *
   * @param frameStart        The starting frame
   * @param frameEndInclusive The inclusive ending frame
   */

  public AUClipLoopRange
  {
    if (Long.compareUnsigned(frameStart, frameEndInclusive) > 0) {
      throw new IllegalArgumentException(
        "Frame start %s must be <= frame inclusive end %s"
          .formatted(
            Long.toUnsignedString(frameStart),
            Long.toUnsignedString(frameEndInclusive)
          )
      );
    }
  }
}
