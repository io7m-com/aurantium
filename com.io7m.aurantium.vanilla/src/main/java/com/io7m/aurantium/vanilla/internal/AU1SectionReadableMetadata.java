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
import com.io7m.aurantium.api.AUSectionReadableMetadataType;
import com.io7m.aurantium.parser.api.AUParseRequest;
import com.io7m.aurantium.vanilla.internal.json.AU1Mappers;
import com.io7m.aurantium.vanilla.internal.json.AU1Metadata;
import com.io7m.jbssio.api.BSSReaderProviderType;
import com.io7m.seltzer.io.SIOException;
import com.io7m.wendover.core.SubrangeSeekableByteChannel;
import tools.jackson.core.type.TypeReference;

import java.io.IOException;
import java.nio.channels.Channels;
import java.nio.channels.SeekableByteChannel;
import java.util.List;
import java.util.Map;

/**
 * A readable metadata section.
 */

public final class AU1SectionReadableMetadata
  extends AU1SectionReadableAbstract implements AUSectionReadableMetadataType
{
  /**
   * A readable metadata section.
   *
   * @param readers       The reader provider
   * @param inDescription The description
   * @param inReader      The reader
   * @param inRequest     The request
   */

  AU1SectionReadableMetadata(
    final BSSReaderProviderType readers,
    final SeekableByteChannel inReader,
    final AUParseRequest inRequest,
    final AUFileSectionDescription inDescription)
    throws SIOException
  {
    super(readers, inReader, inRequest, inDescription);
  }

  @Override
  public Map<String, List<String>> metadata()
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
        return mapper.readValue(
          stream,
          new TypeReference<AU1Metadata>()
          {
          }
        ).metadata();
      }
    }
  }
}
