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
import com.io7m.aurantium.api.AUSectionDescription;
import com.io7m.aurantium.api.AUSectionReadableType;
import com.io7m.aurantium.parser.api.AUParseRequest;
import com.io7m.jbssio.api.BSSReaderRandomAccessType;
import com.io7m.wendover.core.CloseShieldSeekableByteChannel;
import com.io7m.wendover.core.ReadOnlySeekableByteChannel;
import com.io7m.wendover.core.SubrangeSeekableByteChannel;

import java.io.IOException;
import java.nio.channels.SeekableByteChannel;
import java.util.Objects;

/**
 * An abstract readable section.
 */

public abstract class AU1SectionReadableAbstract
  implements AUSectionReadableType
{
  private final BSSReaderRandomAccessType reader;
  private final AUParseRequest request;
  private final AUFileSectionDescription description;
  private final AU1BinaryExpressions expressions;

  protected AU1SectionReadableAbstract(
    final BSSReaderRandomAccessType inReader,
    final AUParseRequest inRequest,
    final AUFileSectionDescription inDescription)
  {
    this.reader =
      Objects.requireNonNull(inReader, "reader");
    this.request =
      Objects.requireNonNull(inRequest, "request");
    this.description =
      Objects.requireNonNull(inDescription, "description");
    this.expressions =
      new AU1BinaryExpressions();
  }

  protected final AU1BinaryExpressions expressions()
  {
    return this.expressions;
  }

  protected final AUParseRequest request()
  {
    return this.request;
  }

  @Override
  public final AUFileSectionDescription fileSectionDescription()
  {
    return this.description;
  }

  protected final BSSReaderRandomAccessType reader()
  {
    return this.reader;
  }

  @Override
  public final AUSectionDescription description()
  {
    return this.description.description();
  }

  @Override
  public final SeekableByteChannel sectionDataChannel()
    throws IOException
  {
    final var baseNotCloseable =
      new CloseShieldSeekableByteChannel(this.request.channel());
    final var baseReadable =
      new ReadOnlySeekableByteChannel(baseNotCloseable);

    final var channel =
      new SubrangeSeekableByteChannel(
        baseReadable,
        this.description.fileOffsetData(),
        this.description.description().size()
      );

    channel.position(0L);
    return channel;
  }

  @Override
  public final void close()
  {

  }
}
