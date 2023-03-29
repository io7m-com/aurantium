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

import java.io.Closeable;
import java.util.List;
import java.util.Optional;

import static com.io7m.aurantium.api.AUIdentifiers.sectionEndIdentifier;
import static com.io7m.aurantium.api.AUIdentifiers.sectionMetadataIdentifier;

/**
 * A readable file.
 */

public interface AUFileReadableType extends Closeable
{
  /**
   * @return The list of sections in the file
   */

  List<AUFileSectionDescription> sections();

  /**
   * @return The file version
   */

  AUVersion version();

  /**
   * Open a section for reading.
   *
   * @param description The section description
   *
   * @return A readable section
   */

  AUSectionReadableType openSection(
    AUFileSectionDescription description);

  /**
   * @return The first available metadata section, if one exists
   */

  default Optional<AUSectionReadableMetadataType> openMetadata()
  {
    for (final var section : this.sections()) {
      final var description = section.description();
      if (description.identifier() == sectionMetadataIdentifier()) {
        return Optional.of(
          (AUSectionReadableMetadataType) this.openSection(section)
        );
      }
    }
    return Optional.empty();
  }

  /**
   * @return The first available end section, if one exists
   */

  default Optional<AUSectionReadableEndType> openEnd()
  {
    for (final var section : this.sections()) {
      final var description = section.description();
      if (description.identifier() == sectionEndIdentifier()) {
        return Optional.of(
          (AUSectionReadableEndType) this.openSection(section)
        );
      }
    }
    return Optional.empty();
  }

  /**
   * Obtain the number of trailing octets in the file. This value should always
   * be zero for valid files.
   *
   * @return The number of trailing octets
   */

  long trailingOctets();
}
