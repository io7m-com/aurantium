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

import com.io7m.aurantium.api.AUClipID;
import com.io7m.aurantium.api.AUFileSectionDescription;
import com.io7m.aurantium.api.AUKeyAssignment;
import com.io7m.aurantium.api.AUKeyAssignmentFlagType;
import com.io7m.aurantium.api.AUKeyAssignmentFlags;
import com.io7m.aurantium.api.AUKeyAssignmentID;
import com.io7m.aurantium.api.AUKeyAssignments;
import com.io7m.aurantium.api.AUSectionReadableKeyAssignmentsType;
import com.io7m.aurantium.parser.api.AUParseRequest;
import com.io7m.jbssio.api.BSSReaderRandomAccessType;
import com.io7m.jdeferthrow.core.ExceptionTracker;
import com.io7m.seltzer.io.SIOException;

import java.io.IOException;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Map;

/**
 * A readable key assignments section.
 */

public final class AU1SectionReadableKeyAssignments
  extends AU1SectionReadableAbstract
  implements AUSectionReadableKeyAssignmentsType
{
  /**
   * A readable key assignments section.
   *
   * @param inDescription The description
   * @param inReader      The reader
   * @param inRequest     The request
   */

  AU1SectionReadableKeyAssignments(
    final BSSReaderRandomAccessType inReader,
    final AUParseRequest inRequest,
    final AUFileSectionDescription inDescription)
  {
    super(inReader, inRequest, inDescription);
  }

  @Override
  public AUKeyAssignments keyAssignments()
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

    final var assignments =
      new ArrayList<AUKeyAssignment>();

    final var exceptions =
      new ExceptionTracker<IOException>();

    try (var r =
           reader.createSubReaderAtBounded(
             "keyAssignments", 0L, sectionSize)) {

      final var e =
        this.expressions();
      final var count =
        (int) e.readU32(r, "count");

      for (int index = 0; index < count; ++index) {
        final var id =
          e.readU32(r, "id");
        final var keyValueStart =
          e.readU32(r, "keyValueStart");
        final var keyValueCenter =
          e.readU32(r, "keyValueCenter");
        final var keyValueEnd =
          e.readU32(r, "keyValueEnd");
        final var clipId =
          e.readU32(r, "clipId");

        final var amplitudeAtKeyStart =
          e.readF64(r, "amplitudeAtKeyStart");
        final var amplitudeAtKeyCenter =
          e.readF64(r, "amplitudeAtKeyCenter");
        final var amplitudeAtKeyEnd =
          e.readF64(r, "amplitudeAtKeyEnd");

        final var atVelocityStart =
          e.readF64(r, "atVelocityStart");
        final var atVelocityCenter =
          e.readF64(r, "atVelocityCenter");
        final var atVelocityEnd =
          e.readF64(r, "atVelocityEnd");

        final var amplitudeAtVelocityStart =
          e.readF64(r, "amplitudeAtVelocityStart");
        final var amplitudeAtVelocityCenter =
          e.readF64(r, "amplitudeAtVelocityCenter");
        final var amplitudeAtVelocityEnd =
          e.readF64(r, "amplitudeAtVelocityEnd");

        final var flagsSize =
          (int) e.readU32(r, "flagsSize");

        final var flags =
          new HashSet<AUKeyAssignmentFlagType>();

        for (int flagIndex = 0; flagIndex < flagsSize; ++flagIndex) {
          try {
            flags.add(
              AUKeyAssignmentFlags.parse(
                e.readUTF8(
                  r,
                  Math.toIntExact(this.request().descriptorLengthLimit()),
                  "flag"
                )
              )
            );
          } catch (final IllegalArgumentException ex) {
            exceptions.addException(
              r.createException(
                ex.getMessage(),
                ex,
                Map.of(),
                (message, cause, attributes) -> {
                  return new SIOException(
                    message,
                    cause.orElseThrow(),
                    "error-invalid",
                    attributes
                  );
                }
              )
            );
          }
        }

        try {
          assignments.add(
            new AUKeyAssignment(
              new AUKeyAssignmentID(id),
              keyValueStart,
              keyValueCenter,
              keyValueEnd,
              new AUClipID(clipId),
              amplitudeAtKeyStart,
              amplitudeAtKeyCenter,
              amplitudeAtKeyEnd,
              atVelocityStart,
              atVelocityCenter,
              atVelocityEnd,
              amplitudeAtVelocityStart,
              amplitudeAtVelocityCenter,
              amplitudeAtVelocityEnd,
              flags
            )
          );
        } catch (final Exception ex) {
          exceptions.addException(
            r.createException(
              ex.getMessage(),
              ex,
              Map.of(),
              (message, cause, attributes) -> {
                return new SIOException(
                  message,
                  cause.orElseThrow(),
                  "error-invalid",
                  attributes
                );
              }
            )
          );
        }
      }
    }

    exceptions.throwIfNecessary();
    return new AUKeyAssignments(List.copyOf(assignments));
  }
}
