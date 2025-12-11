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

package com.io7m.aurantium.vanilla.internal;


import com.io7m.aurantium.api.AUFileReadableType;
import com.io7m.aurantium.api.AUFileSectionDescription;
import com.io7m.aurantium.api.AUSectionDescription;
import com.io7m.aurantium.api.AUSectionReadableType;
import com.io7m.aurantium.api.AUVersion;
import com.io7m.aurantium.parser.api.AUParseRequest;
import com.io7m.entomos.core.EoException;
import com.io7m.entomos.core.EoFileReaderType;
import com.io7m.entomos.core.EoFileSection;
import com.io7m.jbssio.api.BSSReaderProviderType;
import com.io7m.seltzer.io.SIOException;

import java.io.IOException;
import java.util.List;
import java.util.Objects;

import static com.io7m.aurantium.api.AUIdentifiers.sectionClipsDataIdentifier;
import static com.io7m.aurantium.api.AUIdentifiers.sectionClipsDescriptionsIdentifier;
import static com.io7m.aurantium.api.AUIdentifiers.sectionEndIdentifier;
import static com.io7m.aurantium.api.AUIdentifiers.sectionIdentifierIdentifier;
import static com.io7m.aurantium.api.AUIdentifiers.sectionKeyAssignmentsIdentifier;
import static com.io7m.aurantium.api.AUIdentifiers.sectionMetadataIdentifier;


/**
 * The main readable file implementation.
 */

public final class AU1FileReadable implements AUFileReadableType
{
  private final BSSReaderProviderType readers;
  private final EoFileReaderType reader;
  private final AUParseRequest request;
  private final List<FileSectionMapping> fileSections;

  private record FileSectionMapping(
    EoFileSection eoFileSection,
    AUFileSectionDescription description)
  {

  }

  /**
   * Construct a readable file.
   *
   * @param inReaders The reader provider
   * @param inReader  The base reader
   * @param inRequest The request
   */

  public AU1FileReadable(
    final BSSReaderProviderType inReaders,
    final EoFileReaderType inReader,
    final AUParseRequest inRequest)
  {
    this.readers = inReaders;
    this.reader = inReader;
    this.request = inRequest;
    this.fileSections =
      this.reader.sections()
        .stream()
        .map(eoSection -> {
          return new FileSectionMapping(
            eoSection,
            new AUFileSectionDescription(
              eoSection.offset(),
              new AUSectionDescription(
                eoSection.tag(),
                eoSection.dataSize()
              )
            )
          );
        })
        .toList();
  }

  @Override
  public List<AUFileSectionDescription> sections()
  {
    this.checkNotClosed();
    return this.fileSections.stream()
      .map(x -> x.description)
      .toList();
  }

  @Override
  public AUVersion version()
  {
    return new AUVersion(
      this.reader.version().major(),
      this.reader.version().minor()
    );
  }

  private void checkNotClosed()
  {

  }

  @Override
  public AUSectionReadableType openSection(
    final AUFileSectionDescription description)
    throws IOException
  {
    this.checkNotClosed();

    final var mapping =
      this.fileSections.stream()
        .filter(x -> Objects.equals(x.description, description))
        .findFirst()
        .orElseThrow(() -> {
          return new IllegalArgumentException(
            "File does not contain the provided section.");
        });

    final var identifier =
      description.description().identifier();

    try {
      if (identifier == sectionEndIdentifier()) {
        return new AU1SectionReadableEnd(
          this.readers,
          this.reader.dataChannel(mapping.eoFileSection),
          this.request,
          description
        );
      }

      if (identifier == sectionClipsDataIdentifier()) {
        return new AU1SectionReadableClipsData(
          this.readers,
          this.reader.dataChannel(mapping.eoFileSection),
          this.request,
          description
        );
      }

      if (identifier == sectionClipsDescriptionsIdentifier()) {
        return new AU1SectionReadableClipsDescriptions(
          this.readers,
          this.reader.dataChannel(mapping.eoFileSection),
          this.request,
          description
        );
      }

      if (identifier == sectionMetadataIdentifier()) {
        return new AU1SectionReadableMetadata(
          this.readers,
          this.reader.dataChannel(mapping.eoFileSection),
          this.request,
          description
        );
      }

      if (identifier == sectionIdentifierIdentifier()) {
        return new AU1SectionReadableIdentifier(
          this.readers,
          this.reader.dataChannel(mapping.eoFileSection),
          this.request,
          description
        );
      }

      if (identifier == sectionKeyAssignmentsIdentifier()) {
        return new AU1SectionReadableKeyAssignments(
          this.readers,
          this.reader.dataChannel(mapping.eoFileSection),
          this.request,
          description
        );
      }

      return new AU1SectionReadableOther(
        this.readers,
        this.reader.dataChannel(mapping.eoFileSection),
        this.request,
        description
      );
    } catch (final EoException e) {
      throw new SIOException(
        e,
        e.errorCode(),
        e.attributes(),
        e.remediatingAction()
      );
    }
  }

  @Override
  public void close()
    throws IOException
  {
    try {
      this.reader.close();
    } catch (final EoException e) {
      throw new SIOException(
        e,
        e.errorCode(),
        e.attributes(),
        e.remediatingAction()
      );
    }
  }
}
