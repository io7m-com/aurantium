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

import com.io7m.aurantium.api.AUKeyAssignments;
import com.io7m.aurantium.api.AUSectionWritableKeyAssignmentsType;
import com.io7m.aurantium.api.AUSectionWritableType;
import com.io7m.aurantium.writer.api.AUWriteRequest;
import com.io7m.jbssio.api.BSSWriterProviderType;
import com.io7m.jbssio.api.BSSWriterRandomAccessType;

import java.io.IOException;
import java.util.Comparator;
import java.util.Objects;

import static java.lang.Integer.toUnsignedLong;

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
        e.writeU32(writer, "count", toUnsignedLong(input.size()));

        for (final var ka : input) {
          e.writeU32(writer, "id", ka.id());

          e.writeU32(writer, "keyValueStart", ka.keyValueStart());
          e.writeU32(writer, "keyValueCenter", ka.keyValueCenter());
          e.writeU32(writer, "keyValueEnd", ka.keyValueEnd());

          e.writeU32(writer, "clipId", ka.clipId());

          e.writeF64(writer, "amplitudeAtKeyStart", ka.amplitudeAtKeyStart());
          e.writeF64(writer, "amplitudeAtKeyCenter", ka.amplitudeAtKeyCenter());
          e.writeF64(writer, "amplitudeAtKeyEnd", ka.amplitudeAtKeyEnd());

          e.writeF64(writer, "atVelocityStart", ka.atVelocityStart());
          e.writeF64(writer, "atVelocityCenter", ka.atVelocityCenter());
          e.writeF64(writer, "atVelocityEnd", ka.atVelocityEnd());

          e.writeF64(
            writer,
            "amplitudeAtVelocityStart",
            ka.amplitudeAtVelocityStart());
          e.writeF64(
            writer,
            "amplitudeAtVelocityCenter",
            ka.amplitudeAtVelocityCenter());
          e.writeF64(
            writer,
            "amplitudeAtVelocityEnd",
            ka.amplitudeAtVelocityEnd());

          final var flags = ka.flags();
          e.writeU32(writer, "flagsSize", toUnsignedLong(flags.size()));

          final var sortedFlags =
            flags.stream()
              .sorted(Comparator.comparing(o -> o.descriptor().value()))
              .toList();

          for (final var flag : sortedFlags) {
            e.writeUTF8(writer, flag.descriptor().value());
          }
        }
      }
    }
  }
}
