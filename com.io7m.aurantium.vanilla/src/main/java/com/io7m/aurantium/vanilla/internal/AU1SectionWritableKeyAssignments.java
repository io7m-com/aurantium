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

import com.io7m.aurantium.api.AUKeyAssignment;
import com.io7m.aurantium.api.AUKeyAssignmentFlagType;
import com.io7m.aurantium.api.AUKeyAssignments;
import com.io7m.aurantium.api.AUSectionWritableKeyAssignmentsType;
import com.io7m.aurantium.api.AUSectionWritableType;
import com.io7m.aurantium.vanilla.internal.json.AU1KeyAssignment;
import com.io7m.aurantium.vanilla.internal.json.AU1KeyAssignments;
import com.io7m.aurantium.vanilla.internal.json.AU1Mappers;
import com.io7m.aurantium.writer.api.AUWriteRequest;
import com.io7m.jbssio.api.BSSWriterProviderType;
import com.io7m.jbssio.api.BSSWriterRandomAccessType;

import java.io.IOException;
import java.math.BigInteger;
import java.util.Objects;
import java.util.Set;
import java.util.SortedSet;
import java.util.TreeSet;

/**
 * A writable key assignments section.
 */

public final class AU1SectionWritableKeyAssignments
  extends AU1SectionWritableAbstract
  implements AUSectionWritableKeyAssignmentsType
{
  private final BSSWriterProviderType writers;

  /**
   * A writable key assignments section.
   *
   * @param inWriters    A writer provider
   * @param inOnClose    A function executed on closing
   * @param inRequest    A write request
   * @param inIdentifier An identifier
   * @param inWriter     A writer
   */

  public AU1SectionWritableKeyAssignments(
    final BSSWriterProviderType inWriters,
    final BSSWriterRandomAccessType inWriter,
    final AUWriteRequest inRequest,
    final long inIdentifier,
    final AUOnCloseOperationType<AUSectionWritableType> inOnClose)
  {
    super(inWriter, inRequest, inIdentifier, inOnClose);
    this.writers = Objects.requireNonNull(inWriters, "inWriters");
  }

  private static BigInteger bigUnsigned(
    final long value)
  {
    return new BigInteger(Long.toUnsignedString(value));
  }

  private static AU1KeyAssignment keyAssignment(
    final AUKeyAssignment ka)
  {
    return new AU1KeyAssignment(
      bigUnsigned(ka.id().value()),
      bigUnsigned(ka.keyValueStart()),
      bigUnsigned(ka.keyValueCenter()),
      bigUnsigned(ka.keyValueEnd()),
      bigUnsigned(ka.clipId().value()),
      ka.amplitudeAtKeyStart(),
      ka.amplitudeAtKeyCenter(),
      ka.amplitudeAtKeyEnd(),
      ka.atVelocityStart(),
      ka.atVelocityCenter(),
      ka.atVelocityEnd(),
      ka.amplitudeAtVelocityStart(),
      ka.amplitudeAtVelocityCenter(),
      ka.amplitudeAtVelocityEnd(),
      flags(ka.flags())
    );
  }

  private static SortedSet<String> flags(
    final Set<AUKeyAssignmentFlagType> flags)
  {
    final var out = new TreeSet<String>();
    for (final var flag : flags) {
      out.add(flag.descriptor().toString());
    }
    return out;
  }

  @Override
  public void setKeyAssignments(
    final AUKeyAssignments assignments)
    throws IOException
  {
    Objects.requireNonNull(assignments, "assignments");

    try (var channel = this.sectionDataChannel()) {
      final var targetURI = this.request().target();
      try (var writer =
             this.writers.createWriterFromChannel(
               targetURI, channel, "key assignments")) {

        final var e = this.expressions();
        final var input = assignments.assignments();

        final var output =
          input.stream()
            .map(AU1SectionWritableKeyAssignments::keyAssignment)
            .toList();

        final var mapper =
          AU1Mappers.mapper();
        final var data =
          mapper.writeValueAsBytes(
            new AU1KeyAssignments(AU1Mappers.SCHEMA_1, output)
          );

        e.writeBytes(writer, "Data", data);
        writer.align(16);
      }
    }
  }
}
