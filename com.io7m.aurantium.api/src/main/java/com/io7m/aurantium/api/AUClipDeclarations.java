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

package com.io7m.aurantium.api;

import java.util.List;
import java.util.Objects;

/**
 * A list of clip declarations.
 *
 * @param declarations The declarations
 */

public record AUClipDeclarations(
  List<AUClipDeclaration> declarations)
{
  /**
   * A list of clip declarations.
   *
   * @param declarations The declarations
   */

  public AUClipDeclarations
  {
    Objects.requireNonNull(declarations, "declarations");

    AUClipDeclaration declarationPrevious = null;
    for (final var declaration : declarations) {
      if (declarationPrevious != null) {
        if (declarationPrevious.id().compareTo(declaration.id()) >= 0) {
          throw new IllegalArgumentException(
            "Clip IDs must be strictly increasing."
          );
        }
      }
      declarationPrevious = declaration;
    }
  }
}
