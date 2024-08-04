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

import com.io7m.aurantium.api.AUAudioFormats;
import com.io7m.aurantium.api.AUClipDescription;
import com.io7m.aurantium.api.AUClipID;
import com.io7m.aurantium.api.AUFileSectionDescription;
import com.io7m.aurantium.api.AUHashAlgorithm;
import com.io7m.aurantium.api.AUHashValue;
import com.io7m.aurantium.api.AUOctetOrder;
import com.io7m.aurantium.api.AUSectionReadableClipsType;
import com.io7m.aurantium.parser.api.AUParseRequest;
import com.io7m.jbssio.api.BSSReaderRandomAccessType;
import com.io7m.jdeferthrow.core.ExceptionTracker;
import com.io7m.seltzer.io.SIOException;
import com.io7m.wendover.core.CloseShieldSeekableByteChannel;
import com.io7m.wendover.core.ReadOnlySeekableByteChannel;
import com.io7m.wendover.core.SubrangeSeekableByteChannel;

import java.io.IOException;
import java.nio.channels.SeekableByteChannel;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Objects;

/**
 * A readable clips section.
 */

public final class AU1SectionReadableClips
  extends AU1SectionReadableAbstract implements AUSectionReadableClipsType
{
  /**
   * A readable clips section.
   *
   * @param inDescription The description
   * @param inReader      The reader
   * @param inRequest     The request
   */

  AU1SectionReadableClips(
    final BSSReaderRandomAccessType inReader,
    final AUParseRequest inRequest,
    final AUFileSectionDescription inDescription)
  {
    super(inReader, inRequest, inDescription);
  }

  @Override
  public List<AUClipDescription> clips()
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

    try (var r =
           reader.createSubReaderAtBounded(
             "identifier", 0L, sectionSize)) {

      final var e =
        this.expressions();
      final var count =
        (int) e.readU32(r, "count");

      final var limit =
        Math.toIntExact(this.request().descriptorLengthLimit());

      final var clips =
        new ArrayList<AUClipDescription>();

      final var exceptions =
        new ExceptionTracker<IOException>();

      var offStart = 0L;
      for (int index = 0; index < count; ++index) {
        try {
          offStart = r.offsetCurrentAbsolute();

          final var id =
            e.readU32(r, "id");
          final var name =
            e.readUTF8(r, limit, "name");
          final var formatName =
            e.readUTF8(r, limit, "formatName");
          final var sampleRate =
            e.readU32(r, "sampleRate");
          final var sampleDepth =
            e.readU32(r, "sampleDepth");
          final var channels =
            e.readU32(r, "channels");
          final var endiannessName =
            e.readUTF8(r, limit, "endiannessName");
          final var hashAlgoName =
            e.readUTF8(r, limit, "hashAlgorithm");
          final var hashValue =
            e.readUTF8(r, limit, "hashValue");
          final var offset =
            e.readU64(r, "offset");
          final var size =
            e.readU64(r, "size");

          final var offNow =
            r.offsetCurrentAbsolute();

          final var format =
            AUAudioFormats.parse(formatName);
          final var endianness =
            AUOctetOrder.parse(endiannessName);
          final var hashAlgo =
            AUHashAlgorithm.parse(hashAlgoName);
          final var hash =
            new AUHashValue(hashAlgo, hashValue);

          clips.add(
            new AUClipDescription(
              new AUClipID(id),
              name,
              format,
              sampleRate,
              sampleDepth,
              channels,
              endianness,
              hash,
              offset,
              size
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

      exceptions.throwIfNecessary();
      return List.copyOf(clips);
    }
  }

  @Override
  public SeekableByteChannel audioDataForClip(
    final AUClipDescription description)
    throws IOException
  {
    Objects.requireNonNull(description, "description");

    final var fileOffset =
      this.fileSectionDescription()
        .fileOffsetData();
    final var dataOffset =
      fileOffset + description.offset();

    final var baseChannel =
      this.request().channel();

    baseChannel.position(dataOffset);

    final var closeShield =
      new CloseShieldSeekableByteChannel(baseChannel);
    final var readOnlyChannel =
      new ReadOnlySeekableByteChannel(closeShield);

    return new SubrangeSeekableByteChannel(
      readOnlyChannel,
      dataOffset,
      description.size()
    );
  }
}
