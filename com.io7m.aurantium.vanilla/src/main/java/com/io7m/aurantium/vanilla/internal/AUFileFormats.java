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

package com.io7m.aurantium.vanilla.internal;

import com.io7m.aurantium.api.AUIdentifiers;
import com.io7m.entomos.core.EoFileDescription;
import com.io7m.entomos.core.EoFileSectionDescription;
import com.io7m.entomos.core.EoFileVersionsDescription;
import com.io7m.entomos.core.EoSectionCardinality;
import com.io7m.entomos.core.EoSectionOrdering;
import com.io7m.entomos.core.EoSectionsUnknown;

/**
 * File format definitions.
 */

public final class AUFileFormats
{
  private static final EoFileDescription FORMAT_1_0 =
    createDescription1p0();
  private static final EoFileVersionsDescription FORMATS =
    createDescriptions();

  private AUFileFormats()
  {

  }

  private static EoFileVersionsDescription createDescriptions()
  {
    return EoFileVersionsDescription.builder()
      .addDescriptions(FORMAT_1_0)
      .build();
  }

  private static EoFileDescription createDescription1p0()
  {
    final var sectionIdentifier =
      EoFileSectionDescription.builder()
        .setCardinality(EoSectionCardinality.ONE)
        .setOrdering(EoSectionOrdering.MUST_BE_FIRST)
        .setTag(AUIdentifiers.sectionIdentifierIdentifier())
        .build();

    final var sectionClipData =
      EoFileSectionDescription.builder()
        .setCardinality(EoSectionCardinality.ONE)
        .setOrdering(EoSectionOrdering.ANY_ORDER)
        .setTag(AUIdentifiers.sectionClipsDataIdentifier())
        .build();

    final var sectionClipDefinitions =
      EoFileSectionDescription.builder()
        .setCardinality(EoSectionCardinality.ONE)
        .setOrdering(EoSectionOrdering.ANY_ORDER)
        .setTag(AUIdentifiers.sectionClipsDescriptionsIdentifier())
        .build();

    final var sectionKeyAssignments =
      EoFileSectionDescription.builder()
        .setCardinality(EoSectionCardinality.ONE)
        .setOrdering(EoSectionOrdering.ANY_ORDER)
        .setTag(AUIdentifiers.sectionKeyAssignmentsIdentifier())
        .build();

    final var sectionMetadata =
      EoFileSectionDescription.builder()
        .setCardinality(EoSectionCardinality.ZERO_TO_ONE)
        .setOrdering(EoSectionOrdering.ANY_ORDER)
        .setTag(AUIdentifiers.sectionMetadataIdentifier())
        .build();

    return EoFileDescription.builder()
      .setVersionMajor(1)
      .setVersionMinor(0)
      .setFileTag(AUIdentifiers.fileIdentifier())
      .addSections(
        sectionIdentifier,
        sectionClipData,
        sectionClipDefinitions,
        sectionKeyAssignments,
        sectionMetadata
      )
      .setSectionsUnknown(EoSectionsUnknown.UNKNOWN_SECTIONS_PERMITTED)
      .setEndTag(AUIdentifiers.sectionEndIdentifier())
      .build();
  }

  /**
   * @return The file formats
   */

  public static EoFileVersionsDescription fileFormats()
  {
    return FORMATS;
  }
}
