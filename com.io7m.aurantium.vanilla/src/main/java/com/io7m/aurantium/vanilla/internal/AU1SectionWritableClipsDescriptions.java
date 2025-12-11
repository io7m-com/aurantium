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

import com.io7m.aurantium.api.AUClipDescription;
import com.io7m.aurantium.api.AUClipID;
import com.io7m.aurantium.api.AUClipLoopRange;
import com.io7m.aurantium.api.AUHashValue;
import com.io7m.aurantium.api.AUSectionWritableClipDefinitionsType;
import com.io7m.aurantium.api.AUSectionWritableType;
import com.io7m.aurantium.vanilla.internal.json.AU1ClipDescription;
import com.io7m.aurantium.vanilla.internal.json.AU1ClipDescriptions;
import com.io7m.aurantium.vanilla.internal.json.AU1ClipLoopRange;
import com.io7m.aurantium.vanilla.internal.json.AU1HashString;
import com.io7m.aurantium.vanilla.internal.json.AU1HashValue;
import com.io7m.aurantium.vanilla.internal.json.AU1Mappers;
import com.io7m.aurantium.writer.api.AUWriteRequest;
import com.io7m.jbssio.api.BSSWriterProviderType;
import com.io7m.jbssio.api.BSSWriterRandomAccessType;

import java.io.IOException;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Objects;
import java.util.SortedMap;

/**
 * A writable clip description section.
 */

public final class AU1SectionWritableClipsDescriptions
  extends AU1SectionWritableAbstract
  implements AUSectionWritableClipDefinitionsType
{
  private final BSSWriterProviderType writers;

  /**
   * A writable clip description section.
   *
   * @param inWriters    A writer provider
   * @param inOnClose    A function executed on closing
   * @param inRequest    A write request
   * @param inIdentifier An identifier
   * @param inWriter     A writer
   */

  public AU1SectionWritableClipsDescriptions(
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
  public void writeClipDescriptions(
    final SortedMap<AUClipID, AUClipDescription> clips)
    throws IOException
  {
    final var output = new ArrayList<AU1ClipDescription>();
    for (final var entry : clips.entrySet()) {
      final var clip = entry.getValue();
      output.add(
        new AU1ClipDescription(
          bigUnsigned(clip.id().value()),
          clip.name(),
          clip.format().descriptor(),
          bigUnsigned(clip.sampleRate()),
          bigUnsigned(clip.sampleDepth()),
          bigUnsigned(clip.channels()),
          clip.endianness().descriptor(),
          hash(clip.hash()),
          bigUnsigned(clip.offset()),
          bigUnsigned(clip.size()),
          clip.loopRange().map(AU1SectionWritableClipsDescriptions::loopRange)
        )
      );
    }

    final var mapper =
      AU1Mappers.mapper();
    final var data =
      mapper.writeValueAsBytes(
        new AU1ClipDescriptions(AU1Mappers.SCHEMA_1, output)
      );

    try (var channel = this.sectionDataChannel()) {
      final var targetURI = this.request().target();
      try (var writer =
             this.writers.createWriterFromChannel(
               targetURI, channel, "clips")) {
        final var e = this.expressions();
        e.writeBytes(writer, "Data", data);
        writer.align(16);
      }
    }
  }

  private static AU1ClipLoopRange loopRange(
    final AUClipLoopRange range)
  {
    return new AU1ClipLoopRange(
      bigUnsigned(range.frameStart()),
      bigUnsigned(range.frameEndInclusive())
    );
  }

  private static AU1HashValue hash(
    final AUHashValue hash)
  {
    return new AU1HashValue(
      hash.algorithm().descriptor(),
      new AU1HashString(hash.value())
    );
  }

  private static BigInteger bigUnsigned(
    final long value)
  {
    return new BigInteger(Long.toUnsignedString(value));
  }
}
