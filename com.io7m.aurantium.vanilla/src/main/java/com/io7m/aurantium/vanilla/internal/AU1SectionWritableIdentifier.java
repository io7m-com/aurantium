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

import com.io7m.aurantium.api.AUIdentifier;
import com.io7m.aurantium.api.AUSectionWritableIdentifierType;
import com.io7m.aurantium.api.AUSectionWritableType;
import com.io7m.aurantium.writer.api.AUWriteRequest;
import com.io7m.jbssio.api.BSSWriterProviderType;
import com.io7m.jbssio.api.BSSWriterRandomAccessType;

import java.io.IOException;
import java.util.Objects;

import static java.lang.Integer.toUnsignedLong;

/**
 * A writable identifier section.
 */

public final class AU1SectionWritableIdentifier
  extends AU1SectionWritableAbstract
  implements AUSectionWritableIdentifierType
{
  private final BSSWriterProviderType writers;

  /**
   * A writable identifier section.
   *
   * @param inWriters    A writer provider
   * @param inOnClose    A function executed on closing
   * @param inRequest    A write request
   * @param inIdentifier An identifier
   * @param inWriter     A writer
   */

  public AU1SectionWritableIdentifier(
    final BSSWriterProviderType inWriters,
    final BSSWriterRandomAccessType inWriter,
    final AUWriteRequest inRequest,
    final long inIdentifier,
    final AUOnCloseOperationType<AUSectionWritableType> inOnClose)
  {
    super(inWriter, inRequest, inIdentifier, inOnClose);
    this.writers = Objects.requireNonNull(inWriters, "inWriters");
  }

  @Override
  public void setIdentifier(
    final AUIdentifier identifier)
    throws IOException
  {
    Objects.requireNonNull(identifier, "identifier");

    try (var channel = this.sectionDataChannel()) {
      final var targetURI = this.request().target();
      try (var writer =
             this.writers.createWriterFromChannel(
               targetURI, channel, "identifier")) {

        final var e = this.expressions();
        e.writeUTF8(writer, identifier.name().value());
        final var v = identifier.version();
        e.writeU32(writer, "major", toUnsignedLong(v.major()));
        e.writeU32(writer, "minor", toUnsignedLong(v.minor()));
      }
    }
  }
}
