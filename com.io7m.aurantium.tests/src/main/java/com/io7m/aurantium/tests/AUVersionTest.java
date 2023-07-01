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

package com.io7m.aurantium.tests;

import com.io7m.aurantium.api.AUVersion;
import net.jqwik.api.ForAll;
import net.jqwik.api.Property;
import org.junit.jupiter.api.DynamicTest;
import org.junit.jupiter.api.TestFactory;

import java.text.ParseException;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

public final class AUVersionTest
{
  /**
   * Check that version number ordering is correct.
   *
   * @param majorA The major version A
   * @param minorA The minor version A
   * @param majorB The major version B
   * @param minorB The minor version B
   */

  @Property
  public void testOrdering(
    @ForAll final int majorA,
    @ForAll final int minorA,
    @ForAll final int majorB,
    @ForAll final int minorB)
  {
    final var vA =
      new AUVersion(majorA, minorA);
    final var vB =
      new AUVersion(majorB, minorB);

    if (majorA == majorB && minorA == minorB) {
      assertEquals(vA, vB);
      return;
    }

    if (Integer.compareUnsigned(majorA, majorB) > 0) {
      assertTrue(vA.compareTo(vB) > 0);
    } else {
      if (majorA == majorB) {
        assertEquals(
          vA.compareTo(vB),
          Integer.compareUnsigned(minorA, minorB)
        );
      } else {
        assertTrue(vA.compareTo(vB) < 0);
      }
    }
  }

  /**
   * Check that parsing is correct.
   *
   * @param major The major version
   * @param minor The minor version
   *
   * @throws ParseException On errors
   */

  @Property
  public void testParsing(
    @ForAll final int major,
    @ForAll final int minor)
    throws ParseException
  {
    final var v =
      new AUVersion(major, minor);

    assertEquals(
      v,
      AUVersion.parse(v.toString())
    );
  }

  /**
   * Check that parsing fails correctly.
   *
   * @return A stream of test cases
   */

  @TestFactory
  public Stream<DynamicTest> testParseInvalid()
  {
    return Stream.of("", "x.2", "3.y")
      .map(s -> {
        return DynamicTest.dynamicTest("testParseInvalid_" + s, () -> {
          assertThrows(ParseException.class, () -> {
            AUVersion.parse(s);
          });
        });
      });
  }
}
