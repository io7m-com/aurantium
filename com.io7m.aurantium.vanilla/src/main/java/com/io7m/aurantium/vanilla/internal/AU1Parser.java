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


import com.io7m.aurantium.api.AUFileReadableType;
import com.io7m.aurantium.parser.api.AUParseRequest;
import com.io7m.aurantium.parser.api.AUParserType;
import com.io7m.entomos.core.EoException;
import com.io7m.entomos.core.EoFileReaderType;
import com.io7m.jbssio.api.BSSReaderProviderType;
import com.io7m.seltzer.io.SIOException;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.IOException;
import java.util.Map;
import java.util.Objects;
import java.util.concurrent.atomic.AtomicBoolean;

/**
 * The main parser implementation.
 */

public final class AU1Parser implements AUParserType
{
  private static final Logger LOG =
    LoggerFactory.getLogger(AU1Parser.class);

  private final AUParseRequest request;
  private final EoFileReaderType reader;
  private final AtomicBoolean closed;
  private final BSSReaderProviderType readers;

  /**
   * The main parser implementation.
   *
   * @param inReaders The reader provider
   * @param inRequest The read request
   * @param inReader  A reader
   */

  public AU1Parser(
    final BSSReaderProviderType inReaders,
    final AUParseRequest inRequest,
    final EoFileReaderType inReader)
  {
    this.readers =
      inReaders;
    this.request =
      Objects.requireNonNull(inRequest, "request");
    this.reader =
      Objects.requireNonNull(inReader, "reader");
    this.closed =
      new AtomicBoolean(false);
  }

  @Override
  public AUFileReadableType execute()
    throws SIOException
  {
    if (this.reader.version().major() == 1) {
      return new AU1FileReadable(
        this.readers,
        this.reader,
        this.request
      );
    }

    throw new SIOException(
      "Unsupported file format version.",
      "error-file-format",
      Map.ofEntries(
        Map.entry("Version", this.reader.version().toString())
      )
    );
  }

  @Override
  public void close()
    throws IOException
  {
    if (this.closed.compareAndSet(false, true)) {
      try {
        this.reader.close();
      } catch (final EoException e) {
        throw new SIOException(
          e,
          e.errorCode(),
          e.attributes(),
          e.remediatingAction()
        );
      }
    }
  }
}
