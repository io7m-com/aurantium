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

import java.io.IOException;
import java.nio.channels.WritableByteChannel;

/**
 * <p>The writable audio data for clips.</p>
 *
 * <p>Users are expected to retrieve the byte channel associated with each clip
 * using {@link #writeAudioDataForClip(AUClipID)}, and are expected to write
 * audio data to the byte channel in accordance with the declared clip.</p>
 */

public interface AUWritableClipsType
{
  /**
   * Retrieve the byte channel associated with a clip's audio.
   *
   * @param id The clip ID
   *
   * @return A byte channel that must receive audio data
   *
   * @throws IOException On errors
   */

  WritableByteChannel writeAudioDataForClip(AUClipID id)
    throws IOException;
}
