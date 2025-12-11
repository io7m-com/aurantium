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

import com.io7m.aurantium.api.AUClipDescription;
import com.io7m.aurantium.api.AUFileSectionDescription;
import com.io7m.aurantium.api.AUSectionReadableClipDataType;
import com.io7m.aurantium.parser.api.AUParseRequest;
import com.io7m.jbssio.api.BSSReaderProviderType;
import com.io7m.seltzer.io.SIOException;
import com.io7m.wendover.core.CloseShieldSeekableByteChannel;
import com.io7m.wendover.core.SubrangeSeekableByteChannel;

import java.io.IOException;
import java.nio.channels.SeekableByteChannel;

/**
 * A readable clip data section.
 */

public final class AU1SectionReadableClipsData
  extends AU1SectionReadableAbstract implements AUSectionReadableClipDataType
{
  /**
   * A readable clips section.
   *
   * @param inDescription The description
   * @param inReader      The reader
   * @param inRequest     The request
   */

  AU1SectionReadableClipsData(
    final BSSReaderProviderType readers,
    final SeekableByteChannel inReader,
    final AUParseRequest inRequest,
    final AUFileSectionDescription inDescription)
    throws SIOException
  {
    super(readers, inReader, inRequest, inDescription);
  }

  @Override
  public SeekableByteChannel audioDataForClip(
    final AUClipDescription description)
    throws IOException
  {
    return new SubrangeSeekableByteChannel(
      new CloseShieldSeekableByteChannel(this.sectionDataChannel()),
      description.offset(),
      description.size()
    );
  }
}
