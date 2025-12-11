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

import com.io7m.aurantium.api.AUAudioFormatType;
import com.io7m.aurantium.api.AUClipDescription;
import com.io7m.aurantium.api.AUClipID;
import com.io7m.aurantium.api.AUClipLoopRange;
import com.io7m.aurantium.api.AUFileSectionDescription;
import com.io7m.aurantium.api.AUHashAlgorithm;
import com.io7m.aurantium.api.AUHashValue;
import com.io7m.aurantium.api.AUOctetOrder;
import com.io7m.aurantium.api.AUSectionReadableClipDefinitionsType;
import com.io7m.aurantium.parser.api.AUParseRequest;
import com.io7m.aurantium.vanilla.internal.json.AU1ClipDescription;
import com.io7m.aurantium.vanilla.internal.json.AU1ClipDescriptions;
import com.io7m.aurantium.vanilla.internal.json.AU1ClipLoopRange;
import com.io7m.aurantium.vanilla.internal.json.AU1HashValue;
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
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;

import static com.io7m.aurantium.api.AUAudioFormatType.AUAudioFormatStandard;
import static com.io7m.aurantium.api.AUAudioFormatType.AUAudioFormatUnknown;

/**
 * A readable clips section.
 */

public final class AU1SectionReadableClipsDescriptions
  extends AU1SectionReadableAbstract
  implements AUSectionReadableClipDefinitionsType
{
  /**
   * A readable clips section.
   *
   * @param inDescription The description
   * @param inReader      The reader
   * @param inRequest     The request
   */

  AU1SectionReadableClipsDescriptions(
    final BSSReaderProviderType readers,
    final SeekableByteChannel inReader,
    final AUParseRequest inRequest,
    final AUFileSectionDescription inDescription)
    throws SIOException
  {
    super(readers, inReader, inRequest, inDescription);
  }

  @Override
  public List<AUClipDescription> clips()
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
        final AU1ClipDescriptions rawDescriptions =
          mapper.readValue(
            stream,
            new TypeReference<>()
            {
            }
          );

        final var output =
          new ArrayList<AUClipDescription>(rawDescriptions.clips().size());
        for (final var description : rawDescriptions.clips()) {
          output.add(clipDescription(description));
        }
        return List.copyOf(output);
      }
    }
  }

  private static AUClipDescription clipDescription(
    final AU1ClipDescription x)
    throws SIOException
  {
    final AUClipID clipID;
    try {
      clipID = new AUClipID(x.id().longValueExact());
    } catch (final ArithmeticException e) {
      throw new SIOException(
        "Out-of-range integer value.",
        "error-integer-range",
        Map.ofEntries(
          Map.entry("ClipID", x.id().toString()),
          Map.entry("Element", "ClipID"),
          Map.entry("MinimumValue", "0"),
          Map.entry("MaximumValue", "18446744073709551615"),
          Map.entry("Value", x.id().toString())
        )
      );
    }

    return new AUClipDescription(
      clipID,
      x.name(),
      audioFormat(x.format()),
      bigUnsigned(clipID, "SampleRate", x.sampleRate()),
      bigUnsigned(clipID, "SampleDepth", x.sampleDepth()),
      bigUnsigned(clipID, "Channels", x.channels()),
      octetOrder(clipID, x.endianness()),
      hash(clipID, x.hash()),
      bigUnsigned(clipID, "Offset", x.offset()),
      bigUnsigned(clipID, "Size", x.size()),
      loopRangeOpt(clipID, x.loopRange())
    );
  }

  private static long bigUnsigned(
    final AUClipID clipID,
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
          Map.entry("ClipID", clipID.toString()),
          Map.entry("Element", name),
          Map.entry("MinimumValue", "0"),
          Map.entry("MaximumValue", "18446744073709551615"),
          Map.entry("Value", value.toString())
        )
      );
    }
  }

  private static AUHashValue hash(
    final AUClipID clipID,
    final AU1HashValue hash)
    throws SIOException
  {
    return new AUHashValue(
      algorithm(clipID, hash.algorithm()),
      hash.value().value()
    );
  }

  private static AUHashAlgorithm algorithm(
    final AUClipID clipID,
    final RDottedName algorithm)
    throws SIOException
  {
    for (final var value : AUHashAlgorithm.values()) {
      if (Objects.equals(value.descriptor(), algorithm)) {
        return value;
      }
    }

    throw new SIOException(
      "Unrecognized hash algorithm descriptor.",
      "error-hash-algorithm-unrecognized",
      Map.ofEntries(
        Map.entry("ClipID", clipID.toString()),
        Map.entry("Algorithm", algorithm.value())
      )
    );
  }

  private static Optional<AUClipLoopRange> loopRangeOpt(
    final AUClipID clipID,
    final Optional<AU1ClipLoopRange> opt)
    throws SIOException
  {
    if (opt.isPresent()) {
      return Optional.of(loopRange(clipID, opt.get()));
    }
    return Optional.empty();
  }

  private static AUClipLoopRange loopRange(
    final AUClipID clipID,
    final AU1ClipLoopRange x)
    throws SIOException
  {
    return new AUClipLoopRange(
      bigUnsigned(clipID, "LoopRange.FrameStart", x.frameStart()),
      bigUnsigned(clipID, "LoopRange.FrameEndInclusive", x.frameEndInclusive())
    );
  }

  private static AUOctetOrder octetOrder(
    final AUClipID clipID,
    final RDottedName endianness)
    throws SIOException
  {
    for (final var value : AUOctetOrder.values()) {
      if (Objects.equals(value.descriptor(), endianness)) {
        return value;
      }
    }

    throw new SIOException(
      "Unrecognized endianness descriptor.",
      "error-endianness-unrecognized",
      Map.ofEntries(
        Map.entry("ClipID", clipID.toString()),
        Map.entry("Endianness", endianness.value())
      )
    );
  }

  private static AUAudioFormatType audioFormat(
    final RDottedName format)
  {
    for (final var value : AUAudioFormatStandard.values()) {
      if (Objects.equals(value.descriptor(), format)) {
        return value;
      }
    }
    return new AUAudioFormatUnknown(format);
  }
}
