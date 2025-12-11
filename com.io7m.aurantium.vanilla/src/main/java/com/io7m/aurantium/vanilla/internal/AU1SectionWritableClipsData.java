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

import com.io7m.aurantium.api.AUClipDeclarations;
import com.io7m.aurantium.api.AUClipDescription;
import com.io7m.aurantium.api.AUClipID;
import com.io7m.aurantium.api.AUSectionWritableClipDataType;
import com.io7m.aurantium.api.AUSectionWritableType;
import com.io7m.aurantium.api.AUWritableClipsType;
import com.io7m.aurantium.writer.api.AUWriteRequest;
import com.io7m.jbssio.api.BSSWriterProviderType;
import com.io7m.jbssio.api.BSSWriterRandomAccessType;
import com.io7m.wendover.core.SubrangeSeekableByteChannel;

import java.io.IOException;
import java.nio.channels.SeekableByteChannel;
import java.nio.channels.WritableByteChannel;
import java.util.Objects;
import java.util.SortedMap;
import java.util.TreeMap;

/**
 * A writable clip data section.
 */

public final class AU1SectionWritableClipsData
  extends AU1SectionWritableAbstract
  implements AUSectionWritableClipDataType
{
  private final BSSWriterProviderType writers;

  /**
   * A writable clip data section.
   *
   * @param inWriters    A writer provider
   * @param inOnClose    A function executed on closing
   * @param inRequest    A write request
   * @param inIdentifier An identifier
   * @param inWriter     A writer
   */

  public AU1SectionWritableClipsData(
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
    Objects.requireNonNull(clips, "clips");

    final var declarations =
      clips.declarations();
    final var descriptions =
      new TreeMap<AUClipID, AUClipDescription>();

    try (var channel = this.sectionDataChannel()) {
      final var targetURI = this.request().target();
      try (var writer =
             this.writers.createWriterFromChannel(
               targetURI, channel, "clips")) {

        final var e = this.expressions();

        /*
         * Reserve space for the audio data for each clip. Save
         * a clip description for each with the offset included.
         */

        for (final var clip : declarations) {
          descriptions.put(
            clip.id(),
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
              clip.size(),
              clip.loopRange()
            )
          );

          e.writeReserve(writer, clip.size());
          writer.align(16);
        }
      }
    }

    return new Clips(
      this,
      this.request().channel(),
      descriptions
    );
  }

  private static final class Clips
    implements AUWritableClipsType
  {
    private final SeekableByteChannel channel;
    private final TreeMap<AUClipID, AUClipDescription> descriptions;
    private final AU1SectionWritableClipsData parent;

    Clips(
      final AU1SectionWritableClipsData inParent,
      final SeekableByteChannel inChannel,
      final TreeMap<AUClipID, AUClipDescription> inDescriptions)
    {
      this.parent = inParent;
      this.channel = inChannel;
      this.descriptions = inDescriptions;
    }

    @Override
    public SortedMap<AUClipID, AUClipDescription> clipDescriptions()
    {
      return this.descriptions;
    }

    @Override
    public WritableByteChannel writeAudioDataForClip(
      final AUClipID id)
      throws IOException
    {
      final var baseChannel =
        this.parent.sectionDataChannel();
      final var description =
        this.descriptions.get(id);

      return new SubrangeSeekableByteChannel(
        baseChannel,
        description.offset(),
        description.size()
      );
    }
  }
}
