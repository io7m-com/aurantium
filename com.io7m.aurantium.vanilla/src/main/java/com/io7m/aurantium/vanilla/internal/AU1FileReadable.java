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
import com.io7m.aurantium.api.AUSectionReadableType;
import com.io7m.aurantium.api.AUVersion;
import com.io7m.aurantium.parser.api.AUParseRequest;
import com.io7m.jbssio.api.BSSReaderRandomAccessType;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import java.util.Objects;

import static com.io7m.aurantium.api.AUIdentifiers.sectionClipsIdentifier;
import static com.io7m.aurantium.api.AUIdentifiers.sectionEndIdentifier;
import static com.io7m.aurantium.api.AUIdentifiers.sectionIdentifierIdentifier;
import static com.io7m.aurantium.api.AUIdentifiers.sectionKeyAssignmentsIdentifier;
import static com.io7m.aurantium.api.AUIdentifiers.sectionMetadataIdentifier;


/**
 * The main readable file implementation.
 */

public final class AU1FileReadable implements AUFileReadableType
{
  private final BSSReaderRandomAccessType reader;
  private final AUParseRequest request;
  private final AUVersion version;
  private final List<AUFileSectionDescription> fileSections;
  private final long remainingOctets;

  AU1FileReadable(
    final BSSReaderRandomAccessType inReader,
    final AUParseRequest inRequest,
    final AUVersion inVersion,
    final ArrayList<AUFileSectionDescription> inFileSections,
    final long inRemainingOctets)
  {
    this.reader =
      Objects.requireNonNull(inReader, "reader");
    this.request =
      Objects.requireNonNull(inRequest, "request");
    this.version =
      Objects.requireNonNull(inVersion, "version");
    this.fileSections =
      List.copyOf(
        Objects.requireNonNull(inFileSections, "fileSections"));
    this.remainingOctets = inRemainingOctets;
  }

  @Override
  public List<AUFileSectionDescription> sections()
  {
    this.checkNotClosed();
    return this.fileSections;
  }

  @Override
  public AUVersion version()
  {
    return this.version;
  }

  private void checkNotClosed()
  {
    if (this.reader.isClosed()) {
      throw new IllegalStateException("File is closed.");
    }
  }

  @Override
  public AUSectionReadableType openSection(
    final AUFileSectionDescription description)
  {
    this.checkNotClosed();

    if (!this.fileSections.contains(description)) {
      throw new IllegalArgumentException(
        "File does not contain the provided section.");
    }

    final var identifier =
      description.description().identifier();

    if (identifier == sectionEndIdentifier()) {
      return new AU1SectionReadableEnd(
        this.reader,
        this.request,
        description
      );
    }

    if (identifier == sectionMetadataIdentifier()) {
      return new AU1SectionReadableMetadata(
        this.reader,
        this.request,
        description
      );
    }

    if (identifier == sectionIdentifierIdentifier()) {
      return new AU1SectionReadableIdentifier(
        this.reader,
        this.request,
        description
      );
    }

    if (identifier == sectionClipsIdentifier()) {
      return new AU1SectionReadableClips(
        this.reader,
        this.request,
        description
      );
    }

    if (identifier == sectionKeyAssignmentsIdentifier()) {
      return new AU1SectionReadableKeyAssignments(
        this.reader,
        this.request,
        description
      );
    }

    return new AU1SectionReadableOther(this.reader, this.request, description);
  }

  @Override
  public long trailingOctets()
  {
    return this.remainingOctets;
  }

  @Override
  public void close()
    throws IOException
  {
    this.reader.close();
  }
}
