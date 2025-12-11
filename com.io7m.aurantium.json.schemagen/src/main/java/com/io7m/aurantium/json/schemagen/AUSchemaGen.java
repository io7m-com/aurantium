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

package com.io7m.aurantium.json.schemagen;

import com.io7m.aurantium.vanilla.internal.json.AU1Mappers;
import com.io7m.aurantium.vanilla.internal.json.AU1SchemaObjectType;
import com.io7m.sumjack.core.SjGeneratorConfiguration;
import com.io7m.sumjack.core.SjGenerators;
import com.io7m.sumjack.core.SjSchemaVersion;
import tools.jackson.databind.json.JsonMapper;

import java.net.URI;
import java.nio.file.Paths;

import static com.io7m.aurantium.json.schemagen.AU1Double.AU1_DOUBLE;
import static com.io7m.aurantium.json.schemagen.AU1HashStringDefinition.AU1_HASH_STRING;
import static com.io7m.aurantium.json.schemagen.AU1UnsignedInteger.AU1_UNSIGNED_INTEGER;
import static com.io7m.sumjack.core.standard.SjOffsetDateTime.OFFSET_DATE_TIME;
import static com.io7m.sumjack.lanark.SjDottedName.DOTTED_NAME;

public final class AUSchemaGen
{
  private AUSchemaGen()
  {

  }

  static void main(
    final String[] args)
    throws Exception
  {
    final var outputFile =
      Paths.get(args[0]).toAbsolutePath();

    final var configuration =
      SjGeneratorConfiguration.builder()
        .addDefinitions(AU1_DOUBLE)
        .addDefinitions(AU1_HASH_STRING)
        .addDefinitions(AU1_UNSIGNED_INTEGER)
        .addDefinitions(DOTTED_NAME)
        .addDefinitions(OFFSET_DATE_TIME)
        .setId(URI.create(AU1Mappers.SCHEMA_1))
        .setMapper(JsonMapper.shared())
        .setRootType(AU1SchemaObjectType.class)
        .setSchemaVersion(SjSchemaVersion.DRAFT_2020_12)
        .setTitle("Aurantium 1.0")
        .build();

    SjGenerators.create(configuration)
      .executeAndWrite(outputFile);
  }
}
