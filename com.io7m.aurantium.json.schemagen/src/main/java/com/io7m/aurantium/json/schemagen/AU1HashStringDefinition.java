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

import com.io7m.aurantium.vanilla.internal.json.AU1HashString;
import com.io7m.sumjack.core.SjDefinitionProviderType;
import com.io7m.sumjack.core.SjDefinitionType;
import com.io7m.sumjack.core.SjGeneratorConfiguration;

/**
 * A hash string schema definition.
 */

public enum AU1HashStringDefinition
  implements SjDefinitionProviderType
{
  /**
   * A hash string schema definition.
   */

  AU1_HASH_STRING;

  @Override
  public String typeName()
  {
    return AU1HashString.class.getSimpleName();
  }

  @Override
  public SjDefinitionType create(
    final SjGeneratorConfiguration configuration)
  {
    return () -> {
      final var mapper = configuration.mapper();
      final var object = mapper.createObjectNode();
      object.put("type", "string");
      object.put("description", "A hexadecimal hash string.");
      object.put("pattern", "[a-f0-9]+");
      return object;
    };
  }
}
