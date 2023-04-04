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


import com.io7m.aurantium.api.AUFileSectionDescription;
import com.io7m.aurantium.api.AUFileWritableType;
import com.io7m.aurantium.api.AUSectionWritableType;
import com.io7m.aurantium.api.AUVersion;
import com.io7m.aurantium.writer.api.AUWriteRequest;
import com.io7m.jaffirm.core.Preconditions;
import com.io7m.jbssio.api.BSSWriterProviderType;
import com.io7m.jbssio.api.BSSWriterRandomAccessType;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.IOException;
import java.util.List;
import java.util.Objects;

import static com.io7m.aurantium.api.AUIdentifiers.sectionClipsIdentifier;
import static com.io7m.aurantium.api.AUIdentifiers.sectionEndIdentifier;
import static com.io7m.aurantium.api.AUIdentifiers.sectionIdentifierIdentifier;
import static com.io7m.aurantium.api.AUIdentifiers.sectionKeyAssignmentsIdentifier;
import static com.io7m.aurantium.api.AUIdentifiers.sectionMetadataIdentifier;


/**
 * The main writable file implementation.
 */

public final class AU1FileWritable implements AUFileWritableType
{
  private static final Logger LOG =
    LoggerFactory.getLogger(AU1FileWritable.class);

  private final BSSWriterRandomAccessType writer;
  private final AUWriteRequest request;
  private final BSSWriterProviderType writers;
  private AUSectionWritableType sectionOpen;
  private long sectionLastClosed;

  AU1FileWritable(
    final BSSWriterProviderType inWriters,
    final BSSWriterRandomAccessType inWriter,
    final AUWriteRequest inRequest)
  {
    this.writers =
      Objects.requireNonNull(inWriters, "writers");
    this.writer =
      Objects.requireNonNull(inWriter, "writer");
    this.request =
      Objects.requireNonNull(inRequest, "request");
  }

  @Override
  public List<AUFileSectionDescription> sections()
    throws IOException
  {
    throw new IOException();
  }

  @Override
  public AUVersion version()
  {
    return this.request.version();
  }

  @Override
  public AUSectionWritableType createSection(
    final long identifier)
    throws IOException
  {
    if (this.sectionOpen != null) {
      throw new IllegalStateException(
        String.format(
          "Section %s is already open for writing", this.sectionOpen));
    }

    final var offsetCurrentAbsolute =
      this.writer.offsetCurrentAbsolute();

    Preconditions.checkPreconditionV(
      offsetCurrentAbsolute % 16L == 0L,
      "Sections must be aligned to 16 octet boundaries (offset is %s)",
      Long.toUnsignedString(offsetCurrentAbsolute, 16)
    );
    Preconditions.checkPreconditionV(
      Long.compareUnsigned(offsetCurrentAbsolute, this.sectionLastClosed) >= 0,
      "Offset %s would damage existing section that closed at %s",
      Long.toUnsignedString(offsetCurrentAbsolute),
      Long.toUnsignedString(this.sectionLastClosed)
    );

    final var section =
      this.openTypedSection(identifier);

    this.writer.writeU64BE(identifier);
    this.writer.writeU64BE(0L);
    return section;
  }

  private AU1SectionWritableAbstract openTypedSection(
    final long identifier)
  {
    if (identifier == sectionEndIdentifier()) {
      return new AU1SectionWritableEnd(
        this.writer,
        this.request,
        identifier,
        this::onSectionClosed
      );
    }
    if (identifier == sectionMetadataIdentifier()) {
      return new AU1SectionWritableMetadata(
        this.writers,
        this.writer,
        this.request,
        identifier,
        this::onSectionClosed
      );
    }
    if (identifier == sectionIdentifierIdentifier()) {
      return new AU1SectionWritableIdentifier(
        this.writers,
        this.writer,
        this.request,
        identifier,
        this::onSectionClosed
      );
    }
    if (identifier == sectionClipsIdentifier()) {
      return new AU1SectionWritableClips(
        this.writers,
        this.writer,
        this.request,
        identifier,
        this::onSectionClosed
      );
    }
    if (identifier == sectionKeyAssignmentsIdentifier()) {
      return new AU1SectionWritableKeyAssignments(
        this.writers,
        this.writer,
        this.request,
        identifier,
        this::onSectionClosed
      );
    }

    return new AU1SectionWritableOther(
      this.writer,
      this.request,
      identifier,
      this::onSectionClosed
    );
  }

  private void onSectionClosed(
    final AUSectionWritableType section)
  {
    if (LOG.isTraceEnabled()) {
      LOG.trace(
        "closed section 0x{} @ {}",
        Long.toUnsignedString(section.identifier(), 16),
        Long.toUnsignedString(this.writer.offsetCurrentAbsolute())
      );
    }

    this.sectionLastClosed = this.writer.offsetCurrentAbsolute();
    this.sectionOpen = null;
  }

  @Override
  public void close()
    throws IOException
  {
    this.writer.close();
  }
}
