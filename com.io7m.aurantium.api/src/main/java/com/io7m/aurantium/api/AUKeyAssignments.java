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
 * A list of key assignments.
 *
 * @param assignments The assignments
 */

public record AUKeyAssignments(
  List<AUKeyAssignment> assignments)
{
  /**
   * A list of key assignments.
   *
   * @param assignments The assignments
   */

  public AUKeyAssignments
  {
    Objects.requireNonNull(assignments, "declarations");

    AUKeyAssignment declarationPrevious = null;
    for (final var declaration : assignments) {
      if (declarationPrevious != null) {
        if (Long.compareUnsigned(
          declarationPrevious.id(),
          declaration.id()) >= 0) {
          throw new IllegalArgumentException(
            "Key assignment IDs must be strictly increasing."
          );
        }
      }
      declarationPrevious = declaration;
    }
  }
}
