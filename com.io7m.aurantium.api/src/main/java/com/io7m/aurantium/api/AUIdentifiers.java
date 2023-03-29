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

import java.util.Optional;

/**
 * The identifiers for standard sections.
 */

public final class AUIdentifiers
{
  private static final long FILE_IDENTIFIER =
    0x8941_5552_0D0A_1A0AL;
  private static final long SECTION_END_IDENTIFIER =
    0x4155_524D_454E_4421L;
  private static final long SECTION_IDENTIFIER_IDENTIFIER =
    0x4155_524D_5F49_4421L;
  private static final long SECTION_CLIPS_IDENTIFIER =
    0x4155_524D_434C_4950L;
  private static final long SECTION_KEY_ASSIGNMENTS_IDENTIFIER =
    0x4155_524D_4B45_5953L;
  private static final long SECTION_METADATA_IDENTIFIER =
    0x4155_524D_4D45_5441L;

  private AUIdentifiers()
  {

  }

  /**
   * @return The identifier used to identify {@code calino} files
   */

  public static long fileIdentifier()
  {
    return FILE_IDENTIFIER;
  }

  /**
   * @return The identifier used to identify {@code end} sections
   */

  public static long sectionEndIdentifier()
  {
    return SECTION_END_IDENTIFIER;
  }

  /**
   * @return The identifier used to identify {@code metadata} sections
   */

  public static long sectionMetadataIdentifier()
  {
    return SECTION_METADATA_IDENTIFIER;
  }

  /**
   * Determine a humanly-readable name of an identifier.
   *
   * @param identifier The identifier
   *
   * @return A humanly-readable name, if one is known
   */

  public static Optional<String> nameOf(
    final long identifier)
  {
    if (identifier == SECTION_END_IDENTIFIER) {
      return Optional.of("END");
    }
    if (identifier == SECTION_IDENTIFIER_IDENTIFIER) {
      return Optional.of("IDENTIFIER");
    }
    if (identifier == SECTION_CLIPS_IDENTIFIER) {
      return Optional.of("CLIPS");
    }
    if (identifier == SECTION_KEY_ASSIGNMENTS_IDENTIFIER) {
      return Optional.of("KEY_ASSIGNMENTS");
    }
    if (identifier == SECTION_METADATA_IDENTIFIER) {
      return Optional.of("METADATA");
    }
    return Optional.empty();
  }
}
