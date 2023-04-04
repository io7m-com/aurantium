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
import com.io7m.aurantium.api.AUIdentifier;
import com.io7m.aurantium.api.AUSectionReadableIdentifierType;
import com.io7m.aurantium.api.AUVersion;
import com.io7m.aurantium.parser.api.AUParseRequest;
import com.io7m.jbssio.api.BSSReaderRandomAccessType;
import com.io7m.lanark.core.RDottedName;

import java.io.IOException;

/**
 * A readable identifier section.
 */

public final class AU1SectionReadableIdentifier
  extends AU1SectionReadableAbstract implements AUSectionReadableIdentifierType
{
  /**
   * A readable identifier section.
   *
   * @param inDescription The description
   * @param inReader      The reader
   * @param inRequest     The request
   */

  AU1SectionReadableIdentifier(
    final BSSReaderRandomAccessType inReader,
    final AUParseRequest inRequest,
    final AUFileSectionDescription inDescription)
  {
    super(inReader, inRequest, inDescription);
  }

  @Override
  public AUIdentifier identifier()
    throws IOException
  {
    final var reader =
      this.reader();
    final var fileOffset =
      this.fileSectionDescription().fileOffset();
    final var sectionSize =
      this.description().size();

    reader.seekTo(fileOffset);
    reader.skip(16L);

    final String name;
    final int major;
    final int minor;

    try (var subReader =
           reader.createSubReaderAtBounded(
             "identifier", 0L, sectionSize)) {

      final var e = this.expressions();

      name = e.readUTF8(
        subReader,
        Math.toIntExact(this.request().descriptorLengthLimit()),
        "name"
      );
      major = (int) e.readU32(subReader, "versionMajor");
      minor = (int) e.readU32(subReader, "versionMinor");
    }

    return new AUIdentifier(
      new RDottedName(name),
      new AUVersion(major, minor)
    );
  }
}
