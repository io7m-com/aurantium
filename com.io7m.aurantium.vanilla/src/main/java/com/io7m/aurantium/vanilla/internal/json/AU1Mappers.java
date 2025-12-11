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

package com.io7m.aurantium.vanilla.internal.json;

import com.fasterxml.jackson.annotation.JsonInclude;
import com.io7m.dixmont.core.DmJsonRestrictedDeserializers;
import com.io7m.lanark.core.RDottedName;
import tools.jackson.databind.json.JsonMapper;
import tools.jackson.databind.module.SimpleModule;

import java.math.BigInteger;

/**
 * JSON mappers for the file format.
 */

public final class AU1Mappers
{
  /**
   * The JSON schema identifier.
   */

  public static final String SCHEMA_1 =
    "urn:com.io7m.aurantium:1.0";

  private static final JsonMapper MAPPER =
    createMapper();

  private static JsonMapper createMapper()
  {
    final var dixBuilder =
      DmJsonRestrictedDeserializers.builder();

    dixBuilder.allowClass(AU1ClipDescriptions.class);
    dixBuilder.allowClass(AU1HashString.class);
    dixBuilder.allowClass(AU1HashValue.class);
    dixBuilder.allowClass(AU1KeyAssignments.class);
    dixBuilder.allowClass(AU1Metadata.class);
    dixBuilder.allowClass(BigInteger.class);
    dixBuilder.allowClass(RDottedName.class);
    dixBuilder.allowClass(String.class);
    dixBuilder.allowClass(double.class);
    dixBuilder.allowClassName("java.util.SortedMap<java.lang.String,java.util.List<java.lang.String>>");
    dixBuilder.allowClassName("java.util.SortedSet<java.lang.String>");
    dixBuilder.allowListsOfClass(AU1ClipDescription.class);
    dixBuilder.allowListsOfClass(AU1KeyAssignment.class);
    dixBuilder.allowListsOfClass(String.class);
    dixBuilder.allowOptionalOfClass(AU1ClipLoopRange.class);

    final var serializers =
      dixBuilder.build();

    final var simpleModule = new SimpleModule();
    simpleModule.setDeserializers(serializers);
    simpleModule.addDeserializer(
      RDottedName.class,
      new AU1DottedNameDeserializer()
    );
    simpleModule.addSerializer(
      RDottedName.class,
      new AU1DottedNameSerializer()
    );

    simpleModule.addDeserializer(
      AU1HashString.class,
      new AU1HashStringDeserializer()
    );
    simpleModule.addSerializer(
      AU1HashString.class,
      new AU1HashStringSerializer()
    );

    final var builder = JsonMapper.builder();
    builder.addModule(simpleModule);
    builder.changeDefaultPropertyInclusion(incl -> incl.withValueInclusion(JsonInclude.Include.NON_ABSENT));
    builder.changeDefaultPropertyInclusion(incl -> incl.withContentInclusion(JsonInclude.Include.NON_ABSENT));
    return builder.build();
  }

  /**
   * @return The main mapper
   */

  public static JsonMapper mapper()
  {
    return MAPPER;
  }

  private AU1Mappers()
  {

  }
}
