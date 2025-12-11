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
import com.io7m.aurantium.api.AUKeyAssignmentID;
import com.io7m.aurantium.api.AUKeyAssignments;
import com.io7m.aurantium.api.AUSectionReadableKeyAssignmentsType;
import com.io7m.aurantium.parser.api.AUParseRequest;
import com.io7m.aurantium.vanilla.internal.json.AU1KeyAssignment;
import com.io7m.aurantium.vanilla.internal.json.AU1KeyAssignments;
import com.io7m.aurantium.vanilla.internal.json.AU1Mappers;
import com.io7m.jbssio.api.BSSReaderProviderType;
import com.io7m.lanark.core.RDottedName;
import com.io7m.seltzer.io.SIOException;
import com.io7m.wendover.core.SubrangeSeekableByteChannel;
import tools.jackson.core.type.TypeReference;

import java.io.IOException;
import java.math.BigInteger;
import java.nio.channels.Channels;
import java.nio.channels.SeekableByteChannel;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.SortedSet;

import static com.io7m.aurantium.api.AUKeyAssignmentFlagType.AUKeyAssignmentFlagStandard;
import static com.io7m.aurantium.api.AUKeyAssignmentFlagType.AUKeyAssignmentFlagUnknown;

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
   * @param readers       The reader provider
   * @param inDescription The description
   * @param inReader      The reader
   * @param inRequest     The request
   */

  AU1SectionReadableKeyAssignments(
    final BSSReaderProviderType readers,
    final SeekableByteChannel inReader,
    final AUParseRequest inRequest,
    final AUFileSectionDescription inDescription)
    throws SIOException
  {
    super(readers, inReader, inRequest, inDescription);
  }

  @Override
  public AUKeyAssignments keyAssignments()
    throws IOException
  {
    final var reader =
      this.sectionDataReader();
    final var size =
      reader.readU32BE("Size");
    final var mapper =
      AU1Mappers.mapper();

    final var baseChannel = this.sectionDataChannel();
    try (var bounded =
           new SubrangeSeekableByteChannel(baseChannel, 4L, size)) {
      try (var stream = Channels.newInputStream(bounded)) {
        final AU1KeyAssignments rawKeyAssignments =
          mapper.readValue(
            stream,
            new TypeReference<>()
            {
            }
          );

        final List<AUKeyAssignment> keyAssignments =
          new ArrayList<>(rawKeyAssignments.keyAssignments().size());

        for (final var k : rawKeyAssignments.keyAssignments()) {
          keyAssignments.add(keyAssignment(k));
        }

        return new AUKeyAssignments(keyAssignments);
      }
    }
  }

  private static AUKeyAssignment keyAssignment(
    final AU1KeyAssignment k)
    throws SIOException
  {
    final AUKeyAssignmentID keyAssignmentID;
    try {
      keyAssignmentID = new AUKeyAssignmentID(k.id().longValueExact());
    } catch (final ArithmeticException e) {
      throw new SIOException(
        "Out-of-range integer value.",
        "error-integer-range",
        Map.ofEntries(
          Map.entry("KeyAssignmentID", k.id().toString()),
          Map.entry("Element", "KeyAssignmentID"),
          Map.entry("MinimumValue", "0"),
          Map.entry("MaximumValue", "18446744073709551615"),
          Map.entry("Value", k.id().toString())
        )
      );
    }

    return new AUKeyAssignment(
      keyAssignmentID,
      bigUnsigned(keyAssignmentID, "KeyValueStart", k.keyValueStart()),
      bigUnsigned(keyAssignmentID, "KeyValueCenter", k.keyValueCenter()),
      bigUnsigned(keyAssignmentID, "KeyValueEnd", k.keyValueEnd()),
      clipID(keyAssignmentID, k.clipId()),
      doubleNormal(
        keyAssignmentID,
        "AmplitudeAtKeyStart",
        k.amplitudeAtKeyStart()),
      doubleNormal(
        keyAssignmentID,
        "AmplitudeAtKeyCenter",
        k.amplitudeAtKeyCenter()),
      doubleNormal(keyAssignmentID, "AmplitudeAtKeyEnd", k.amplitudeAtKeyEnd()),
      doubleNormal(keyAssignmentID, "AtVelocityStart", k.atVelocityStart()),
      doubleNormal(keyAssignmentID, "AtVelocityCenter", k.atVelocityCenter()),
      doubleNormal(keyAssignmentID, "AtVelocityEnd", k.atVelocityEnd()),
      doubleNormal(
        keyAssignmentID,
        "AmplitudeAtVelocityStart",
        k.amplitudeAtVelocityStart()),
      doubleNormal(
        keyAssignmentID,
        "AmplitudeAtVelocityCenter",
        k.amplitudeAtVelocityCenter()),
      doubleNormal(
        keyAssignmentID,
        "AmplitudeAtVelocityEnd",
        k.amplitudeAtVelocityEnd()),
      flags(keyAssignmentID, "Flags", k.flags())
    );
  }

  private static Set<AUKeyAssignmentFlagType> flags(
    final AUKeyAssignmentID keyAssignmentID,
    final String name,
    final SortedSet<String> flags)
    throws SIOException
  {
    final var output = new HashSet<AUKeyAssignmentFlagType>(flags.size());
    FLAG_LOOP:
    for (final var flag : flags) {
      for (final var v : AUKeyAssignmentFlagStandard.values()) {
        if (Objects.equals(v.descriptor().value(), flag)) {
          output.add(v);
          continue FLAG_LOOP;
        }
      }

      try {
        output.add(new AUKeyAssignmentFlagUnknown(new RDottedName(flag)));
      } catch (final IllegalArgumentException e) {
        throw new SIOException(
          "Illegal flag value.",
          e,
          "error-flag-illegal",
          Map.ofEntries(
            Map.entry("KeyAssignmentID", keyAssignmentID.toString()),
            Map.entry("Element", name),
            Map.entry("Value", flag)
          )
        );
      }
    }
    return output;
  }

  private static double doubleNormal(
    final AUKeyAssignmentID keyAssignmentID,
    final String name,
    final double x)
    throws SIOException
  {
    if (x >= 0.0 && x <= 1.0) {
      return x;
    }

    throw new SIOException(
      "Out-of-range double value.",
      "error-double-range",
      Map.ofEntries(
        Map.entry("KeyAssignmentID", keyAssignmentID.toString()),
        Map.entry("Element", name),
        Map.entry("MinimumValue", "0.0"),
        Map.entry("MaximumValue", "1.0"),
        Map.entry("Value", Double.toString(x))
      )
    );
  }

  private static AUClipID clipID(
    final AUKeyAssignmentID keyAssignmentID,
    final BigInteger x)
    throws SIOException
  {
    return new AUClipID(bigUnsigned(keyAssignmentID, "ClipID", x));
  }

  private static long bigUnsigned(
    final AUKeyAssignmentID keyAssignmentID,
    final String name,
    final BigInteger value)
    throws SIOException
  {
    try {
      return value.longValueExact();
    } catch (final ArithmeticException e) {
      throw new SIOException(
        "Out-of-range integer value.",
        "error-integer-range",
        Map.ofEntries(
          Map.entry("KeyAssignmentID", keyAssignmentID.toString()),
          Map.entry("Element", name),
          Map.entry("MinimumValue", "0"),
          Map.entry("MaximumValue", "18446744073709551615"),
          Map.entry("Value", value.toString())
        )
      );
    }
  }
}
