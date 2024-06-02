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

import com.io7m.aurantium.api.AUFileSectionDescription;
import com.io7m.aurantium.api.AUSectionReadableType;
import com.io7m.aurantium.validation.api.AUValidationError;

import java.net.URI;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;
import java.util.UUID;

import static com.io7m.aurantium.validation.api.AUValidationStatus.STATUS_ERROR;
import static com.io7m.aurantium.validation.api.AUValidationStatus.STATUS_WARNING;
import static com.io7m.aurantium.vanilla.internal.AUStringConstants.ERROR_NO_END_SECTION;
import static com.io7m.aurantium.vanilla.internal.AUStringConstants.WARN_END_SECTION_NOT_ZERO;
import static com.io7m.aurantium.vanilla.internal.AUStringConstants.WARN_SECTION_UNALIGNED;
import static com.io7m.aurantium.vanilla.internal.AUStringConstants.WARN_TRAILING_DATA;

/**
 * A factory of errors.
 */

public final class AU1ValidationErrors
{
  private final AU1ValidationStrings strings;
  private final URI source;

  /**
   * A factory of errors.
   *
   * @param inSource  The source file
   * @param inStrings The error strings
   */

  public AU1ValidationErrors(
    final URI inSource,
    final AU1ValidationStrings inStrings)
  {
    this.source =
      Objects.requireNonNull(inSource, "source");
    this.strings =
      Objects.requireNonNull(inStrings, "strings");
  }

  private static String formatSet(
    final Set<Integer> set)
  {
    return set.toString()
      .replace('[', '{')
      .replace(']', '}');
  }

  /**
   * Construct an error.
   *
   * @param section The section
   * @param e       The exception
   *
   * @return An error
   */

  public AUValidationError errorOfException(
    final AUSectionReadableType section,
    final Exception e)
  {
    return new AUValidationError(
      this.source,
      section.fileSectionDescription().fileOffsetData(),
      STATUS_ERROR,
      Optional.empty(),
      e.getMessage(),
      Optional.of(e)
    );
  }

  /**
   * Construct an error.
   *
   * @param section The section
   * @param e       The exception
   * @param message The message
   *
   * @return An error
   */

  public AUValidationError errorOfException(
    final AUSectionReadableType section,
    final Exception e,
    final String message)
  {
    return new AUValidationError(
      this.source,
      section.fileSectionDescription().fileOffsetData(),
      STATUS_ERROR,
      Optional.empty(),
      "%s: %s".formatted(message, e.getMessage()),
      Optional.of(e)
    );
  }


  /**
   * Construct an error.
   *
   * @param section The section
   *
   * @return An error
   */

  public AUValidationError warnSectionUnaligned(
    final AUFileSectionDescription section)
  {
    return new AUValidationError(
      this.source,
      section.fileOffset(),
      STATUS_WARNING,
      Optional.of(UUID.fromString("2ccedb5d-d5ec-40ba-a965-04bba40ce4ec")),
      this.strings.format(
        WARN_SECTION_UNALIGNED,
        Long.toUnsignedString(section.description().identifier(), 16),
        Long.toUnsignedString(section.fileOffset(), 16)
      ),
      Optional.empty()
    );
  }

  /**
   * Construct an error.
   *
   * @param section The section
   *
   * @return An error
   */

  public AUValidationError warnEndSectionNotZeroSize(
    final AUFileSectionDescription section)
  {
    return new AUValidationError(
      this.source,
      section.fileOffset(),
      STATUS_WARNING,
      Optional.of(UUID.fromString("75b25aca-58ce-4dfe-9c1b-c3140fda18e3")),
      this.strings.format(
        WARN_END_SECTION_NOT_ZERO,
        Long.toUnsignedString(section.description().size())
      ),
      Optional.empty()
    );
  }

  /**
   * Construct an error.
   *
   * @return An error
   */

  public AUValidationError errorNoEndSection()
  {
    return new AUValidationError(
      this.source,
      0L,
      STATUS_ERROR,
      Optional.of(UUID.fromString("a24164fd-3bdb-41fc-b04f-f7ebd4d65c4a")),
      this.strings.format(ERROR_NO_END_SECTION),
      Optional.empty()
    );
  }

  /**
   * Construct an error.
   *
   * @param octets The octets
   * @param offset The offset of the data
   *
   * @return An error
   */

  public AUValidationError warnTrailingData(
    final long offset,
    final long octets)
  {
    return new AUValidationError(
      this.source,
      offset,
      STATUS_WARNING,
      Optional.of(UUID.fromString("e5108d48-42fd-4de3-8137-f42aafc44e20")),
      this.strings.format(WARN_TRAILING_DATA, Long.toUnsignedString(octets)),
      Optional.empty()
    );
  }
}
