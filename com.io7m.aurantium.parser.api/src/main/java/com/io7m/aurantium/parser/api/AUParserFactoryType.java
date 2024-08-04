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

package com.io7m.aurantium.parser.api;

import com.io7m.seltzer.io.SIOException;

/**
 * A factory of parsers.
 */

public interface AUParserFactoryType
{
  /**
   * @return The major file format version that this parser supports
   */

  int supportedMajorVersion();

  /**
   * @return The highest known minor version for this parser factory
   */

  int highestMinorVersion();

  /**
   * Create a new parser for the given request.
   *
   * @param request A parse request
   *
   * @return A new parser
   *
   * @throws SIOException On errors
   */

  AUParserType createParser(
    AUParseRequest request)
    throws SIOException;
}
