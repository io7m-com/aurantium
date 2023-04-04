/*
 * Copyright © 2021 Mark Raynsford <code@io7m.com> https://www.io7m.com
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

import com.io7m.aurantium.api.AUClipDeclarations;
import com.io7m.aurantium.api.AUClipDescription;
import com.io7m.aurantium.api.AUSectionWritableClipsType;
import com.io7m.aurantium.api.AUSectionWritableType;
import com.io7m.aurantium.api.AUWritableClipsType;
import com.io7m.aurantium.writer.api.AUWriteRequest;
import com.io7m.jbssio.api.BSSWriterProviderType;
import com.io7m.jbssio.api.BSSWriterRandomAccessType;
import com.io7m.wendover.core.CloseShieldSeekableByteChannel;
import com.io7m.wendover.core.SubrangeSeekableByteChannel;

import java.io.IOException;
import java.nio.channels.SeekableByteChannel;
import java.nio.channels.WritableByteChannel;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Objects;

import static java.lang.Integer.toUnsignedLong;

/**
 * A writable clips section.
 */

public final class AU1SectionWritableClips
  extends AU1SectionWritableAbstract
  implements AUSectionWritableClipsType
{
  private final BSSWriterProviderType writers;

  /**
   * A writable clips section.
   *
   * @param inWriters    A writer provider
   * @param inOnClose    A function executed on closing
   * @param inRequest    A write request
   * @param inIdentifier An identifier
   * @param inWriter     A writer
   */

  public AU1SectionWritableClips(
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
  public AUWritableClipsType createClips(
    final AUClipDeclarations clips)
    throws IOException
  {
    Objects.requireNonNull(clips, "mipMaps");

    final var declarations =
      clips.declarations();
    final var descriptions =
      new ArrayList<AUClipDescription>(declarations.size());

    try (var channel = this.sectionDataChannel()) {
      final var targetURI = this.request().target();
      try (var writer =
             this.writers.createWriterFromChannel(
               targetURI, channel, "clips")) {

        final var e = this.expressions();
        e.writeU32(writer, "size", toUnsignedLong(declarations.size()));

        final var offsetsByClipId = new HashMap<Long, Long>();

        /*
         * Write out all the clip declarations, leaving the offset
         * fields at 0. Afterwards, we'll go back and update the offsets.
         */

        for (final var clip : declarations) {
          e.writeU32(writer, "id", clip.id());
          e.writeUTF8(writer, clip.name());
          e.writeUTF8(writer, clip.format().descriptor().value());
          e.writeU32(writer, "sampleRate", clip.sampleRate());
          e.writeU32(writer, "sampleDepth", clip.sampleDepth());
          e.writeU32(writer, "channels", clip.channels());
          e.writeUTF8(writer, clip.endianness().descriptor().value());

          final var hash = clip.hash();
          e.writeUTF8(writer, hash.algorithm().descriptor().value());
          e.writeUTF8(writer, hash.value());

          offsetsByClipId.put(
            Long.valueOf(clip.id()),
            Long.valueOf(writer.offsetCurrentRelative())
          );
          e.writeU64(writer, "offset", 0L);
          e.writeU64(writer, "size", clip.size());
        }

        writer.align(16);

        /*
         * Reserve space for the audio data for each clip. Save
         * a clip description for each with the offset included.
         */

        for (final var clip : declarations) {
          descriptions.add(
            new AUClipDescription(
              clip.id(),
              clip.name(),
              clip.format(),
              clip.sampleRate(),
              clip.sampleDepth(),
              clip.channels(),
              clip.endianness(),
              clip.hash(),
              writer.offsetCurrentRelative(),
              clip.size()
            )
          );

          e.writeReserve(writer, clip.size());
          writer.align(16);
        }

        /*
         * Update offset values for the clips.
         */

        for (final var clip : descriptions) {
          final var idBox =
            Long.valueOf(clip.id());
          final var offsetField =
            offsetsByClipId.get(idBox).longValue();

          writer.seekTo(offsetField);
          e.writeU64(writer, "offset", clip.offset());
        }
      }
    }

    return new Clips(
      this.request().channel(),
      this.offsetStartData(),
      descriptions
    );
  }

  private static final class Clips implements AUWritableClipsType
  {
    private final SeekableByteChannel fileChannel;
    private final long fileSectionDataStart;
    private final List<AUClipDescription> descriptions;

    Clips(
      final SeekableByteChannel inChannel,
      final long inFileSectionDataStart,
      final List<AUClipDescription> inDescriptions)
    {
      this.fileChannel =
        Objects.requireNonNull(inChannel, "channel");
      this.fileSectionDataStart =
        inFileSectionDataStart;
      this.descriptions =
        Objects.requireNonNull(inDescriptions, "descriptions");
    }

    @Override
    public WritableByteChannel writeAudioDataForClip(
      final long id)
      throws IOException
    {
      for (final var description : this.descriptions) {
        if (description.id() == id) {
          final var offset =
            this.fileSectionDataStart + description.offset();

          this.fileChannel.position(offset);

          final var closeShieldChannel =
            new CloseShieldSeekableByteChannel(this.fileChannel);

          return new SubrangeSeekableByteChannel(
            closeShieldChannel,
            offset,
            description.size()
          );
        }
      }

      throw new IllegalArgumentException("No such clip with ID " + id);
    }
  }
}
