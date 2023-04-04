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

import com.io7m.aurantium.api.AUFileReadableType;
import com.io7m.aurantium.api.AUFileSectionDescription;
import com.io7m.aurantium.api.AUSectionReadableEndType;
import com.io7m.aurantium.api.AUSectionReadableMetadataType;
import com.io7m.aurantium.validation.api.AUValidationError;
import com.io7m.aurantium.validation.api.AUValidatorType;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import java.util.Objects;

/**
 * A validator.
 */

public final class AU1Validator implements AUValidatorType
{
  private static final Logger LOG =
    LoggerFactory.getLogger(AU1Validator.class);

  private final AUFileReadableType file;
  private final AU1ValidationErrors errorFactory;
  private List<AUValidationError> errors;

  /**
   * A validator.
   *
   * @param inErrors An error factory
   * @param inFile   The file to be validated
   */

  public AU1Validator(
    final AU1ValidationErrors inErrors,
    final AUFileReadableType inFile)
  {
    this.file =
      Objects.requireNonNull(inFile, "file");
    this.errorFactory =
      Objects.requireNonNull(inErrors, "errors");
  }

  @Override
  public List<AUValidationError> execute()
  {
    this.errors = new ArrayList<>();

    for (final var section : this.file.sections()) {
      this.checkSectionAlignment(section);
    }

    this.file.openMetadata()
      .ifPresent(this::checkMetadata);
    this.file.openEnd()
      .ifPresentOrElse(this::checkEnd, () -> {
        this.publishError(this.errorFactory.errorNoEndSection());
      });


    if (this.file.trailingOctets() != 0L) {
      this.publishError(
        this.errorFactory.warnTrailingData(0L, this.file.trailingOctets()
        ));
    }

    return this.errors;
  }

  private void checkEnd(
    final AUSectionReadableEndType section)
  {
    if (section.description().size() != 0L) {
      this.publishError(this.errorFactory.warnEndSectionNotZeroSize(
        section.fileSectionDescription()));
    }
  }

  private void checkSectionAlignment(
    final AUFileSectionDescription section)
  {
    if (section.fileOffset() % 16L != 0L) {
      this.publishError(this.errorFactory.warnSectionUnaligned(section));
    }
  }

  private boolean publishError(
    final AUValidationError error)
  {
    LOG.debug("{}", error.message());
    return this.errors.add(error);
  }

  private void checkMetadata(
    final AUSectionReadableMetadataType section)
  {
    try {
      section.metadata();
    } catch (final IOException e) {
      this.publishError(this.errorFactory.errorOfException(
        section, e, "I/O error reading metadata values"));
    }
  }
}
