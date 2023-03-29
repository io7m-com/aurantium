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

import com.io7m.lanark.core.RDottedName;

/**
 * The endianness/octet order for the components of audio data that are larger
 * than a single byte.
 */

public enum AUOctetOrder implements AUDescribableType
{
  /**
   * The most significant octet appears first.
   */

  BIG_ENDIAN {
    @Override
    public RDottedName descriptor()
    {
      return new RDottedName("com.io7m.aurantium.endian_big");
    }
  },

  /**
   * The most significant octet appears last.
   */

  LITTLE_ENDIAN {
    @Override
    public RDottedName descriptor()
    {
      return new RDottedName("com.io7m.aurantium.endian_little");
    }
  }
}
