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

package com.io7m.aurantium.vanilla;

import com.io7m.aurantium.parser.api.AUParseRequest;
import com.io7m.aurantium.parser.api.AUParserFactoryType;
import com.io7m.aurantium.parser.api.AUParserType;
import com.io7m.aurantium.vanilla.internal.AU1Parser;
import com.io7m.jbssio.api.BSSReaderProviderType;
import com.io7m.seltzer.io.SIOException;

import java.util.Objects;
import java.util.ServiceConfigurationError;
import java.util.ServiceLoader;

/**
 * A parser factory supporting major version 1.
 */

public final class AU1Parsers implements AUParserFactoryType
{
  private final BSSReaderProviderType readers;

  /**
   * A parser factory supporting major version 1.
   */

  public AU1Parsers()
  {
    this(loadReadersFromServiceLoader());
  }

  /**
   * A parser factory supporting major version 1.
   *
   * @param inReaders A provider of readers
   */

  public AU1Parsers(
    final BSSReaderProviderType inReaders)
  {
    this.readers = Objects.requireNonNull(inReaders, "readers");
  }

  private static BSSReaderProviderType loadReadersFromServiceLoader()
  {
    return ServiceLoader.load(BSSReaderProviderType.class)
      .findFirst()
      .orElseThrow(() -> new ServiceConfigurationError(
        "No services available of type %s".formatted(BSSReaderProviderType.class))
      );
  }

  @Override
  public int supportedMajorVersion()
  {
    return 1;
  }

  @Override
  public int highestMinorVersion()
  {
    return 0;
  }

  @Override
  public AUParserType createParser(
    final AUParseRequest request)
    throws SIOException
  {
    return new AU1Parser(
      request,
      this.readers.createReaderFromChannel(
        request.source(),
        request.channel(),
        "root")
    );
  }
}
