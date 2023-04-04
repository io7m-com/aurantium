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
import java.io.IOException;
import java.util.List;

import static com.io7m.aurantium.api.AUIdentifiers.sectionClipsIdentifier;
import static com.io7m.aurantium.api.AUIdentifiers.sectionEndIdentifier;
import static com.io7m.aurantium.api.AUIdentifiers.sectionKeyAssignmentsIdentifier;
import static com.io7m.aurantium.api.AUIdentifiers.sectionMetadataIdentifier;
import static com.io7m.aurantium.api.AUIdentifiers.sectionIdentifierIdentifier;

/**
 * A writable file.
 */

public interface AUFileWritableType extends Closeable
{
  /**
   * @return The sections currently declared within the file
   *
   * @throws IOException On errors
   */

  List<AUFileSectionDescription> sections()
    throws IOException;

  /**
   * @return The file version
   */

  AUVersion version();

  /**
   * Create a new section with the given identifier.
   *
   * @param identifier The identifier
   *
   * @return A new section
   *
   * @throws IOException On errors
   */

  AUSectionWritableType createSection(long identifier)
    throws IOException;

  /**
   * Create a new metadata section.
   *
   * @return A new section
   *
   * @throws IOException On errors
   */

  default AUSectionWritableMetadataType createSectionMetadata()
    throws IOException
  {
    return (AUSectionWritableMetadataType)
      this.createSection(sectionMetadataIdentifier());
  }

  /**
   * Create a new end section.
   *
   * @return A new section
   *
   * @throws IOException On errors
   */

  default AUSectionWritableEndType createSectionEnd()
    throws IOException
  {
    return (AUSectionWritableEndType)
      this.createSection(sectionEndIdentifier());
  }

  /**
   * Create a new identifier section.
   *
   * @return A new section
   *
   * @throws IOException On errors
   */

  default AUSectionWritableIdentifierType createSectionIdentifier()
    throws IOException
  {
    return (AUSectionWritableIdentifierType)
      this.createSection(sectionIdentifierIdentifier());
  }

  /**
   * Create a new clips section.
   *
   * @return A new section
   *
   * @throws IOException On errors
   */

  default AUSectionWritableClipsType createSectionClips()
    throws IOException
  {
    return (AUSectionWritableClipsType)
      this.createSection(sectionClipsIdentifier());
  }

  /**
   * Create a new key assignments section.
   *
   * @return A new section
   *
   * @throws IOException On errors
   */

  default AUSectionWritableKeyAssignmentsType createSectionKeyAssignments()
    throws IOException
  {
    return (AUSectionWritableKeyAssignmentsType)
      this.createSection(sectionKeyAssignmentsIdentifier());
  }
}
