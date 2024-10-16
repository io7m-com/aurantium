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

import com.io7m.aurantium.parser.api.AUParserFactoryType;
import com.io7m.aurantium.validation.api.AUValidatorFactoryType;
import com.io7m.aurantium.writer.api.AUWriterFactoryType;
import com.io7m.jbssio.api.BSSReaderProviderType;
import com.io7m.jbssio.api.BSSWriterProviderType;

/**
 * Aurantium format (Vanilla implementation)
 */

module com.io7m.aurantium.vanilla
{
  requires static org.osgi.annotation.bundle;
  requires static org.osgi.annotation.versioning;

  requires com.io7m.aurantium.api;
  requires com.io7m.aurantium.parser.api;
  requires com.io7m.aurantium.validation.api;
  requires com.io7m.aurantium.writer.api;

  requires com.io7m.jaffirm.core;
  requires com.io7m.jbssio.api;
  requires com.io7m.jbssio.ext.bounded;
  requires com.io7m.jdeferthrow.core;
  requires com.io7m.jxtrand.vanilla;
  requires com.io7m.lanark.core;
  requires com.io7m.wendover.core;
  requires org.slf4j;
  requires com.io7m.seltzer.io;

  opens com.io7m.aurantium.vanilla.internal
    to com.io7m.jxtrand.vanilla;

  uses BSSReaderProviderType;
  uses BSSWriterProviderType;

  provides AUValidatorFactoryType
    with com.io7m.aurantium.vanilla.AU1Validators;
  provides AUParserFactoryType
    with com.io7m.aurantium.vanilla.AU1Parsers;
  provides AUWriterFactoryType
    with com.io7m.aurantium.vanilla.AU1Writers;

  exports com.io7m.aurantium.vanilla;
}