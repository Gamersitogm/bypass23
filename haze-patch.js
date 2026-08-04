/**
 * haze-patch.js — pure-JS local video optimizer (Haze core engine).
 *
 * This is the in-browser port of the canonical Haze core (core-payload.js) and
 * the AlterEditingMethod v5 patcher. It runs entirely on the client — the video
 * never leaves the device and the server does no work.
 *
 * Pipeline (matches the reference, minus native ffmpeg):
 *   1. Faststart normalize (pure JS): reorder to [ftyp][moov][mdat] and rebase
 *      every chunk offset. Stands in for ffmpeg `-c copy -movflags +faststart`.
 *   2. Frame-inflation inject: append fake zero-cost samples to the video track's
 *      stsz (count only — stts timing is LEFT UNTOUCHED so playback/duration are
 *      unchanged), add an stsc run, point fake chunk offsets at one 8-byte sample
 *      appended to mdat, insert a `free` box, normalize mdhd language + handler
 *      names. A naive frame-count reader sees a huge sample count; a real decoder
 *      plays the identical frames at full resolution.
 *
 * H.264/AVC only (matches the reference — HEVC would need a transcode we can't do
 * in the browser). Exposes quickPatch plus a read-only inspect compatibility
 * helper on window.HazePatch. Also module.exports for Node tests.
 */

(function () {
  'use strict';

  const FAKE_SAMPLE = new Uint8Array([0, 0, 0, 4, 0, 0, 0, 0]);
  const CONTAINERS = new Set(['moov', 'trak', 'mdia', 'minf', 'dinf', 'edts', 'stbl', 'udta', 'meta', 'ilst']);

  // ─── Binary helpers ─────────────────────────────────────────────────────────
  function u32(u8, off) { return ((u8[off] << 24) | (u8[off + 1] << 16) | (u8[off + 2] << 8) | u8[off + 3]) >>> 0; }
  function u64(u8, off) { return Number((BigInt(u32(u8, off)) << 32n) | BigInt(u32(u8, off + 4))); }
  function w32(val) {
    const b = new Uint8Array(4);
    b[0] = (val >>> 24) & 0xFF; b[1] = (val >>> 16) & 0xFF; b[2] = (val >>> 8) & 0xFF; b[3] = val & 0xFF;
    return b;
  }
  function w64(val) {
    const b = new Uint8Array(8); const v = BigInt(val);
    b.set(w32(Number(v >> 32n)), 0); b.set(w32(Number(v & 0xFFFFFFFFn)), 4);
    return b;
  }
  function box(type, content) {
    const out = new Uint8Array(content.length + 8);
    out.set(w32(content.length + 8), 0);
    for (let i = 0; i < 4; i++) out[i + 4] = type.charCodeAt(i);
    out.set(content, 8);
    return out;
  }
  function boxType(u8, off) { return String.fromCharCode(u8[off + 4], u8[off + 5], u8[off + 6], u8[off + 7]); }

  function parseBoxes(u8, start, end) {
    const boxes = [];
    let p = start;
    while (p + 8 <= end) {
      let size = u32(u8, p); let header = 8;
      if (size === 1) { if (p + 16 > end) break; size = u64(u8, p + 8); header = 16; }
      else if (size === 0) { size = end - p; }
      if (!size || p + size > end) break;
      const type = boxType(u8, p);
      const b = { type, start: p, end: p + size, size, header, children: null };
      let cstart = p + header;
      if (type === 'meta') cstart += 4;
      if (CONTAINERS.has(type) && cstart < p + size) b.children = parseBoxes(u8, cstart, p + size);
      boxes.push(b);
      p += size;
    }
    return boxes;
  }

  function raw(u8, b) { return u8.subarray(b.start, b.end); }
  function payload(u8, b) { return u8.subarray(b.start + b.header, b.end); }
  function findChild(b, type) {
    if (!b.children) return null;
    for (let i = 0; i < b.children.length; i++) if (b.children[i].type === type) return b.children[i];
    return null;
  }
  function childPath(b, path) { let c = b; for (const t of path) { c = findChild(c, t); if (!c) return null; } return c; }
  function isVideoTrak(u8, trak) {
    const hdlr = childPath(trak, ['mdia', 'hdlr']);
    if (!hdlr) return false;
    const p = payload(u8, hdlr);
    return String.fromCharCode(p[8], p[9], p[10], p[11]) === 'vide';
  }
  function findStbl(trak) { return childPath(trak, ['mdia', 'minf', 'stbl']); }
  function stszInfo(u8, stsz) { const p = payload(u8, stsz); return { sampleSize: u32(p, 4), count: u32(p, 8) }; }
  function concatBuffers(bufs) {
    let total = 0; for (const b of bufs) total += b.length;
    const out = new Uint8Array(total); let off = 0;
    for (const b of bufs) { out.set(b, off); off += b.length; }
    return out;
  }

  // ─── Codec + fps detection (for the fps-based fake-sample multiplier) ────────

  // Video codec fourCC from the sample-description box (stsd → first entry type).
  function videoCodec(u8, videoTrak) {
    const stbl = findStbl(videoTrak);
    if (!stbl) return '';
    const stsd = findChild(stbl, 'stsd');
    if (!stsd) return '';
    const p = payload(u8, stsd); // [ver/flags 4][entryCount 4][ size 4 | fourCC 4 ...]
    if (p.length < 16) return '';
    return String.fromCharCode(p[12], p[13], p[14], p[15]);
  }

  // fps = media timescale / most-common sample delta. Pure-container equivalent
  // of ffprobe avg_frame_rate, so we never need ffprobe.
  function videoFps(u8, videoTrak) {
    const mdhd = childPath(videoTrak, ['mdia', 'mdhd']);
    const stbl = findStbl(videoTrak);
    if (!mdhd || !stbl) return 30;
    const mp = payload(u8, mdhd);
    const ver = mp[0];
    const timescale = ver === 1 ? u32(mp, 20) : u32(mp, 12);
    const stts = findChild(stbl, 'stts');
    if (!stts || !timescale) return 30;
    const sp = payload(u8, stts);
    const n = u32(sp, 4);
    let bestDelta = 0, bestCount = -1;
    for (let i = 0, off = 8; i < n && off + 8 <= sp.length; i++, off += 8) {
      const c = u32(sp, off), d = u32(sp, off + 4);
      if (c > bestCount) { bestCount = c; bestDelta = d; }
    }
    if (!bestDelta) return 30;
    return timescale / bestDelta;
  }

  // Reference multiplier: <=25fps -> 10x, <=30fps -> 8x, else 20/3 (~6.667x).
  function fakeMultiplier(fps) {
    if (fps <= 25.1) return 10;
    if (fps <= 30.1) return 8;
    return 20 / 3;
  }

  // ─── Box patchers (identical semantics to core-payload.js) ──────────────────

  function patchMdhdLang(u8, mdhd) {
    const p = payload(u8, mdhd);
    const out = new Uint8Array(p.length); out.set(p);
    const off = out[0] === 1 ? 28 : 16;
    if (off + 2 <= out.length) { out[off] = (0x55c4 >> 8) & 0xFF; out[off + 1] = 0x55c4 & 0xFF; }
    return box('mdhd', out);
  }

  function patchHdlrName(u8, hdlr) {
    const p = payload(u8, hdlr);
    let name = '';
    if (p.length >= 12) name = String.fromCharCode(p[8], p[9], p[10], p[11]);
    const newName = name === 'vide' ? 'VideoHandler' : (name === 'soun' ? 'SoundHandler' : null);
    if (!newName) return raw(u8, hdlr);
    const out = new Uint8Array(24 + newName.length + 1);
    out.set(p.subarray(0, 24), 0);
    for (let i = 0; i < newName.length; i++) out[24 + i] = newName.charCodeAt(i);
    out[24 + newName.length] = 0;
    return box('hdlr', out);
  }

  function patchStsz(u8, stsz, fakeSamples) {
    if (fakeSamples < 1) return raw(u8, stsz);
    const p = payload(u8, stsz);
    const verFlags = p.subarray(0, 4);
    const defaultSize = u32(p, 4);
    const count = u32(p, 8);
    const sizes = [];
    if (defaultSize !== 0) { for (let i = 0; i < count; i++) sizes.push(defaultSize); }
    else { for (let i = 0, off = 12; i < count && off + 4 <= p.length; i++, off += 4) sizes.push(u32(p, off)); }
    for (let i = 0; i < fakeSamples; i++) sizes.push(8);
    const out = new Uint8Array(12 + sizes.length * 4);
    out.set(verFlags, 0); out.set(w32(0), 4); out.set(w32(sizes.length), 8);
    for (let i = 0; i < sizes.length; i++) out.set(w32(sizes[i]), 12 + i * 4);
    return box('stsz', out);
  }

  function patchStsc(u8, stsc, chunkCount) {
    if (chunkCount < 1) return raw(u8, stsc);
    const p = payload(u8, stsc);
    const verFlags = p.subarray(0, 4);
    const count = u32(p, 4);
    const entries = [];
    for (let i = 0, off = 8; i < count && off + 12 <= p.length; i++, off += 12) {
      entries.push([u32(p, off), u32(p, off + 4), u32(p, off + 8)]);
    }
    const lastId = entries.length ? entries[entries.length - 1][2] : 1;
    entries.push([chunkCount + 1, 1, lastId]);
    const out = new Uint8Array(8 + entries.length * 12);
    out.set(verFlags, 0); out.set(w32(entries.length), 4);
    for (let i = 0; i < entries.length; i++) {
      out.set(w32(entries[i][0]), 8 + i * 12);
      out.set(w32(entries[i][1]), 12 + i * 12);
      out.set(w32(entries[i][2]), 16 + i * 12);
    }
    return box('stsc', out);
  }

  function patchStco(u8, stco, moovDiff, fakeOffset, fakeSamples) {
    const p = payload(u8, stco);
    const verFlags = p.subarray(0, 4);
    const count = u32(p, 4);
    const offsets = [];
    for (let i = 0, off = 8; i < count && off + 4 <= p.length; i++, off += 4) offsets.push(u32(p, off) + moovDiff);
    for (let i = 0; i < fakeSamples; i++) offsets.push(fakeOffset);
    const out = new Uint8Array(8 + offsets.length * 4);
    out.set(verFlags, 0); out.set(w32(offsets.length), 4);
    for (let i = 0; i < offsets.length; i++) out.set(w32(offsets[i]), 8 + i * 4);
    return box('stco', out);
  }

  function patchCo64(u8, co64, moovDiff, fakeOffset, fakeSamples) {
    const p = payload(u8, co64);
    const verFlags = p.subarray(0, 4);
    const count = u32(p, 4);
    const offsets = [];
    for (let i = 0, off = 8; i < count && off + 8 <= p.length; i++, off += 8) offsets.push(u64(p, off) + moovDiff);
    for (let i = 0; i < fakeSamples; i++) offsets.push(fakeOffset);
    const out = new Uint8Array(8 + offsets.length * 8);
    out.set(verFlags, 0); out.set(w32(offsets.length), 4);
    for (let i = 0; i < offsets.length; i++) out.set(w64(offsets[i]), 8 + i * 8);
    return box('co64', out);
  }

  // ─── Step 1: pure-JS faststart normalize (ffmpeg `-c copy +faststart`) ───────
  // Produces [ftyp][moov][mdat] with chunk offsets rebased to the relocated mdat.
  // Robust to input order (moov-first or moov-last) and drops free/skip/wide/uuid.
  function faststartNormalize(u8) {
    const boxes = parseBoxes(u8, 0, u8.length);
    const ftyp = boxes.find(b => b.type === 'ftyp');
    const moov = boxes.find(b => b.type === 'moov');
    const mdat = boxes.find(b => b.type === 'mdat');
    if (!moov || !mdat) throw new Error('Invalid MP4 — missing moov or mdat.');

    // Strip whatever mdat header the source used (8-byte or 64-bit 16-byte, e.g.
    // After Effects / Media Encoder exports) and re-emit a clean 32-bit mdat.
    const mdatData = u8.subarray(mdat.start + mdat.header, mdat.end);
    if (mdatData.length + 8 > 0xFFFFFFFF) {
      throw new Error('Video is too large to optimize in the browser (media over 4 GB).');
    }
    const ftypLen = ftyp ? (ftyp.end - ftyp.start) : 0;
    const oldMdatDataStart = mdat.start + mdat.header;

    // Rebuild moov with every stco/co64 offset shifted by `delta` so chunks
    // still resolve into the relocated mdat. stsz/stts/stsc copied verbatim.
    function shift(b, delta) {
      if (b.type === 'stco') {
        const p = payload(u8, b); const n = u32(p, 4);
        const out = new Uint8Array(p.length); out.set(p);
        for (let i = 0, off = 8; i < n && off + 4 <= p.length; i++, off += 4) out.set(w32((u32(p, off) + delta) >>> 0), off);
        return box('stco', out);
      }
      if (b.type === 'co64') {
        const p = payload(u8, b); const n = u32(p, 4);
        const out = new Uint8Array(p.length); out.set(p);
        for (let i = 0, off = 8; i < n && off + 8 <= p.length; i++, off += 8) out.set(w64(u64(p, off) + delta), off);
        return box('co64', out);
      }
      if (b.children) {
        const parts = [];
        if (b.type === 'meta') parts.push(payload(u8, b).subarray(0, 4));
        for (const c of b.children) parts.push(shift(c, delta));
        return box(b.type, concatBuffers(parts));
      }
      return raw(u8, b);
    }

    // CRITICAL: the rebuilt moov's length can differ from the source moov —
    // parseBoxes drops trailing padding / unparsed bytes inside containers, so
    // re-boxing children can come out shorter. `delta` must be based on the
    // ACTUAL emitted moov length, not the source length; otherwise every chunk
    // offset is mis-shifted and chunks point outside mdat (a "partial file" the
    // platform rejects). stco/co64 entry widths are fixed, so the moov length is
    // independent of the offset VALUES — probe once with delta 0 to measure the
    // real length, then rebuild with the correct delta.
    const probeMoov = shift(moov, 0);
    const newMdatDataStart = ftypLen + probeMoov.length + 8; // ftyp + moov + 32-bit mdat header
    const delta = newMdatDataStart - oldMdatDataStart;

    if (delta === 0 && ftyp && mdat.header === 8 && moov.start < mdat.start && boxes.filter(b => b.type !== 'ftyp' && b.type !== 'moov' && b.type !== 'mdat').length === 0) {
      return u8; // already clean [ftyp][moov][mdat] with a 32-bit mdat header
    }

    const newMoov = delta === 0 ? probeMoov : shift(moov, delta);
    const newMdat = box('mdat', mdatData); // always a 32-bit mdat box
    const parts = [];
    if (ftyp) parts.push(raw(u8, ftyp));
    parts.push(newMoov);
    parts.push(newMdat);
    return concatBuffers(parts);
  }

  // ─── Step 2: frame-inflation inject (core-payload.js logic) ──────────────────
  function inject(u8) {
    const boxes = parseBoxes(u8, 0, u8.length);
    const moovBox = boxes.find(b => b.type === 'moov');
    const mdatBox = boxes.find(b => b.type === 'mdat');
    if (!moovBox || !mdatBox) throw new Error('Invalid MP4 — missing moov or mdat.');
    if (mdatBox.header !== 8) throw new Error('Unsupported 64-bit mdat header.');

    const trakBoxes = (moovBox.children || []).filter(b => b.type === 'trak');
    const videoTrak = trakBoxes.find(b => isVideoTrak(u8, b));
    if (!videoTrak) throw new Error('No video track found.');

    // H.264/AVC only. HEVC was tried (the container ops are codec-agnostic) but
    // the fake-sample injection produces files TikTok rejects for real HEVC
    // sources — the trick is only reliable on H.264. HEVC clips (e.g. iPhone
    // 4K/60 or 4K/120) must be re-encoded to H.264 first.
    const codec = videoCodec(u8, videoTrak);
    if (codec !== 'avc1' && codec !== 'avc3') {
      throw new Error(`This looks like an ${codec === 'hvc1' || codec === 'hev1' ? 'HEVC (H.265)' : (codec || 'unsupported')} video, which can't be optimized. Record or export in H.264 — on iPhone: Settings ▸ Camera ▸ Formats ▸ "Most Compatible", or drop to 4K/60 or 1080p.`);
    }

    const stbl = findStbl(videoTrak);
    if (!stbl) throw new Error('Video sample table (stbl) not found.');
    const stszBox = findChild(stbl, 'stsz');
    const stscBox = findChild(stbl, 'stsc');
    const stcoBox = findChild(stbl, 'stco') || findChild(stbl, 'co64');
    if (!stszBox || !stscBox || !stcoBox) throw new Error('Video sample tables (stsz/stsc/stco) missing.');

    const info = stszInfo(u8, stszBox);
    const fps = videoFps(u8, videoTrak);
    const targetCount = Math.floor(info.count * fakeMultiplier(fps));
    const fakeSamples = Math.max(0, targetCount - info.count);
    const originalChunkCount = u32(payload(u8, stcoBox), 4);

    let activeTrak = null;

    function processBox(b, moovDiff, fakeOffset, fakeSamplesCount) {
      if (b.type === 'free' || b.type === 'udta' || b.type === 'uuid') return null;
      if (b.type === 'mdhd') return patchMdhdLang(u8, b);
      if (b.type === 'hdlr') return patchHdlrName(u8, b);

      const isVideo = activeTrak === videoTrak;
      if (isVideo && b.type === 'stsz') return patchStsz(u8, b, fakeSamplesCount);
      if (isVideo && b.type === 'stts') return raw(u8, b); // timing untouched — key to the method
      if (isVideo && b.type === 'stsc' && fakeSamplesCount > 0) return patchStsc(u8, b, originalChunkCount);
      if (b.type === 'stco') return patchStco(u8, b, moovDiff, fakeOffset, isVideo ? fakeSamplesCount : 0);
      if (b.type === 'co64') return patchCo64(u8, b, moovDiff, fakeOffset, isVideo ? fakeSamplesCount : 0);

      if (b.children) {
        const chunks = [];
        if (b.type === 'meta') chunks.push(payload(u8, b).subarray(0, 4));
        for (const child of b.children) {
          const oldTrak = activeTrak;
          if (child.type === 'trak') activeTrak = child;
          const patched = processBox(child, moovDiff, fakeOffset, fakeSamplesCount);
          activeTrak = oldTrak;
          if (patched) chunks.push(patched);
        }
        return box(b.type, concatBuffers(chunks));
      }
      return raw(u8, b);
    }

    function recomputeMoov(moovDiff, fakeOffset, fakeSamplesCount) {
      activeTrak = null;
      return processBox(moovBox, moovDiff, fakeOffset, fakeSamplesCount);
    }

    const freeBox = box('free', new Uint8Array(0));

    // Compute the exact physical shift of mdat once the free box is inserted and
    // moov is rebuilt (absolute, so it's correct regardless of input layout).
    let newMdatOffset = 0;
    for (const b of boxes) {
      if (b.type === 'mdat') break;
      if (b.type === 'ftyp') newMdatOffset += raw(u8, b).length + 8; // ftyp + freeBox
      else if (b.type === 'moov') newMdatOffset += recomputeMoov(0, mdatBox.end, fakeSamples).length;
      else if (b.type !== 'free' && b.type !== 'skip' && b.type !== 'uuid') newMdatOffset += raw(u8, b).length;
    }
    const trueMoovDiff = newMdatOffset - mdatBox.start;
    const fakeOffset = mdatBox.end + trueMoovDiff;
    const currentMoov = recomputeMoov(trueMoovDiff, fakeOffset, fakeSamples);

    const mdatContent = raw(u8, mdatBox);
    const mdatWithFake = fakeSamples > 0
      ? concatBuffers([
          w32(mdatContent.length + FAKE_SAMPLE.length),
          new Uint8Array([0x6d, 0x64, 0x61, 0x74]), // 'mdat'
          mdatContent.subarray(8),
          FAKE_SAMPLE
        ])
      : mdatContent;

    const outChunks = [];
    for (const b of boxes) {
      if (b.type === 'ftyp') { outChunks.push(raw(u8, b)); outChunks.push(freeBox); }
      else if (b.type === 'moov') outChunks.push(currentMoov);
      else if (b.type === 'mdat') outChunks.push(mdatWithFake);
      else if (b.type !== 'free' && b.type !== 'skip' && b.type !== 'uuid') outChunks.push(raw(u8, b));
    }
    return concatBuffers(outChunks);
  }

  // ─── Step 3: integrity validation (never hand back a broken file) ────────────
  // Walks every track's sample tables and confirms each chunk's bytes fall
  // wholly inside mdat. Catches the offset-past-end corruption class (which the
  // platform reports as "couldn't process") before the user ever downloads it.
  // Throws HazePatchError on failure so the caller can log it and show an error.
  function HazePatchError(message) { const e = new Error(message); e.name = 'HazePatchError'; return e; }

  function validatePatched(u8) {
    const boxes = parseBoxes(u8, 0, u8.length);
    const moov = boxes.find(b => b.type === 'moov');
    const mdat = boxes.find(b => b.type === 'mdat');
    if (!moov || !mdat) throw HazePatchError('Output is missing moov or mdat.');
    const mdatStart = mdat.start + mdat.header;
    const mdatEnd = mdat.end;

    const traks = (moov.children || []).filter(b => b.type === 'trak');
    for (let t = 0; t < traks.length; t++) {
      const stbl = findStbl(traks[t]);
      if (!stbl) continue;
      const stszB = findChild(stbl, 'stsz');
      const stscB = findChild(stbl, 'stsc');
      const stcoB = findChild(stbl, 'stco') || findChild(stbl, 'co64');
      if (!stszB || !stscB || !stcoB) continue;

      const sp = payload(u8, stszB);
      const defSize = u32(sp, 4);
      const sampCount = u32(sp, 8);
      const sizeAt = (i) => (defSize !== 0 ? defSize : u32(sp, 12 + i * 4));

      const cp = payload(u8, stcoB);
      const is64 = stcoB.type === 'co64';
      const chunkCount = u32(cp, 4);
      const offAt = (i) => (is64 ? u64(cp, 8 + i * 8) : u32(cp, 8 + i * 4));

      const scp = payload(u8, stscB);
      const runCount = u32(scp, 4);
      const runs = [];
      for (let i = 0, o = 8; i < runCount && o + 12 <= scp.length; i++, o += 12) {
        runs.push([u32(scp, o), u32(scp, o + 4)]); // [firstChunk (1-based), samplesPerChunk]
      }

      let sampleIdx = 0;
      for (let c = 1; c <= chunkCount; c++) {
        let spc = 1;
        for (let r = 0; r < runs.length; r++) {
          if (runs[r][0] <= c && (r + 1 >= runs.length || runs[r + 1][0] > c)) { spc = runs[r][1]; break; }
        }
        let bytes = 0;
        for (let s = 0; s < spc && sampleIdx < sampCount; s++, sampleIdx++) bytes += sizeAt(sampleIdx);
        const off = offAt(c - 1);
        if (off < mdatStart || off + bytes > mdatEnd) {
          throw HazePatchError(`Track ${t + 1} chunk ${c}/${chunkCount} points outside the media data (offset ${off}, ${bytes} bytes, valid ${mdatStart}..${mdatEnd}). Aborting to avoid a corrupt file.`);
        }
      }
    }
  }

  /**
   * Optimize an MP4 buffer entirely in the browser. Returns a new Uint8Array.
   * Throws (name 'HazePatchError') if the result fails integrity validation —
   * the caller must catch this, log it, and NOT offer the file for download.
   * @param {Uint8Array|ArrayBuffer} input raw MP4 bytes
   * @returns {Uint8Array} patched MP4
   */
  function quickPatch(input) {
    const u8 = input instanceof Uint8Array ? input : new Uint8Array(input);
    const normalized = faststartNormalize(u8);
    const out = inject(normalized);
    validatePatched(out);
    return out;
  }

  /**
   * Read the video codec and sample count without modifying the input.
   * This preserves the current optimizer's loader contract while quickPatch
   * remains the reverted H.264-only e200bef implementation.
   * @param {Uint8Array|ArrayBuffer} input raw MP4 bytes
   * @returns {{codec:string,isAvc:boolean,isHevc:boolean,sampleCount:number}}
   */
  function inspect(input) {
    const u8 = input instanceof Uint8Array ? input : new Uint8Array(input);
    const boxes = parseBoxes(u8, 0, u8.length);
    const moov = boxes.find(b => b.type === 'moov');
    const videoTrak = moov && (moov.children || []).find(
      b => b.type === 'trak' && isVideoTrak(u8, b)
    );
    const codec = videoTrak ? videoCodec(u8, videoTrak) : '';
    const stbl = videoTrak ? findStbl(videoTrak) : null;
    const stsz = stbl ? findChild(stbl, 'stsz') : null;
    const sampleCount = stsz ? stszInfo(u8, stsz).count : 0;

    return {
      codec,
      isAvc: codec === 'avc1' || codec === 'avc3',
      isHevc: codec === 'hvc1' || codec === 'hev1' || codec === 'hvc2' || codec === 'hev2',
      sampleCount,
    };
  }

  const api = { quickPatch, inspect };
  if (typeof window !== 'undefined') window.HazePatch = api;
  if (typeof module !== 'undefined' && module.exports) module.exports = api;

})();
