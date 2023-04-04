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
 * A hash algorithm.
 */

public enum AUHashAlgorithm
  implements AUDescribableType
{
  /**
   * The SHA-256 hash function.
   */

  HA_SHA256 {
    @Override
    public RDottedName descriptor()
    {
      return new RDottedName("com.io7m.aurantium.sha2_256");
    }
  };

  /**
   * Parse a hash function.
   *
   * @param name The name
   *
   * @return A hash function
   *
   * @throws IllegalArgumentException On unrecognized or invalid descriptors
   */

  public static AUHashAlgorithm parse(
    final String name)
  {
    final var value = new RDottedName(name);
    if (value.equals(HA_SHA256.descriptor())) {
      return HA_SHA256;
    }

    throw new IllegalArgumentException(
      "Unrecognized hash value: %s".formatted(name)
    );
  }
}
