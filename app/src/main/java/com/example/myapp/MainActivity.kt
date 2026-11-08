package com.example.myapp

import android.app.Activity
import android.content.Context
import android.content.Intent
import android.content.SharedPreferences
import android.graphics.Bitmap
import android.graphics.BitmapFactory
import android.graphics.Canvas
import android.graphics.Color
import android.graphics.Typeface
import android.net.Uri
import android.os.Bundle
import android.provider.DocumentsContract
import android.provider.OpenableColumns
import android.view.Gravity
import android.view.ViewGroup
import android.widget.Button
import android.widget.EditText
import android.widget.LinearLayout
import android.widget.ProgressBar
import android.widget.ScrollView
import android.widget.TextView
import android.widget.Toast
import java.io.BufferedOutputStream
import java.io.ByteArrayOutputStream
import java.io.File
import java.io.FileInputStream
import java.io.FileOutputStream
import java.io.OutputStream
import java.nio.ByteBuffer
import java.nio.channels.FileChannel
import java.util.Locale
import java.util.TreeMap
import java.util.zip.DataFormatException
import java.util.zip.Inflater

// ============================================================================
//  Minimal PDF engine.
//  Strategy: the original file is NEVER parsed fully or loaded into memory.
//  We read only the tail (startxref), the cross-reference data and the few
//  objects of the page tree that we need. Replacement pages are written as an
//  "incremental update" appended to a streamed copy of the original file.
//  Cost = one sequential copy of the file + a few KB of reads. Memory stays flat
//  (a few MB) whether the PDF is 50 KB or 50 GB.
// ============================================================================

typealias PDict = HashMap<String, Any?>

class PdfName(val v: String)
class PdfRef(val num: Int, val gen: Int)
class PdfKw(val v: String)
class PdfStream(val dict: PDict, val dataPos: Long)
class XEnt(val type: Int, val a: Long, val b: Int)
class PdfEof : Exception("Unexpected end of data")
class PdfException(msg: String) : Exception(msg)
class CancelEx : Exception("Cancelled by user.")

class Inh(val mediaBox: Any?, val cropBox: Any?, val rotate: Any?) {
    fun merge(d: PDict): Inh {
        return Inh(d["MediaBox"] ?: mediaBox, d["CropBox"] ?: cropBox, d["Rotate"] ?: rotate)
    }
}

class PageHit(val num: Int, val gen: Int, val parent: Int, val dict: PDict, val inh: Inh)

class ObjStm(val data: ByteArray, val first: Int, val nums: IntArray, val offs: IntArray)

fun numToLong(o: Any?): Long {
    return when (o) {
        is Long -> o
        is Int -> o.toLong()
        is Double -> o.toLong()
        else -> 0L
    }
}

fun numToDouble(o: Any?): Double {
    return when (o) {
        is Long -> o.toDouble()
        is Int -> o.toDouble()
        is Double -> o
        else -> 0.0
    }
}

@Suppress("UNCHECKED_CAST")
fun asDict(o: Any?): PDict? {
    if (o is HashMap<*, *>) {
        return o as PDict
    }
    return null
}

fun isWsInt(c: Int): Boolean {
    return c == 0 || c == 9 || c == 10 || c == 12 || c == 13 || c == 32
}

fun startsWithAt(buf: ByteArray, at: Int, s: String): Boolean {
    if (at < 0 || at + s.length > buf.size) return false
    for (i in 0 until s.length) {
        if ((buf[at + i].toInt() and 0xFF) != s[i].code) return false
    }
    return true
}

fun fmtNum(d: Double): String {
    return String.format(Locale.US, "%.4f", d)
}

fun fmtSize(n: Long): String {
    val kb = 1024.0
    val mb = kb * 1024.0
    val gb = mb * 1024.0
    val d = n.toDouble()
    return when {
        d >= gb -> String.format(Locale.US, "%.2f GB", d / gb)
        d >= mb -> String.format(Locale.US, "%.1f MB", d / mb)
        d >= kb -> String.format(Locale.US, "%.1f KB", d / kb)
        else -> "$n bytes"
    }
}

fun inflateBytes(raw: ByteArray): ByteArray {
    val inf = Inflater()
    inf.setInput(raw)
    val out = ByteArrayOutputStream(maxOf(raw.size * 3, 1024))
    val buf = ByteArray(65536)
    try {
        while (!inf.finished()) {
            val n = inf.inflate(buf)
            if (n == 0) {
                if (inf.needsInput() || inf.needsDictionary()) break
            }
            out.write(buf, 0, n)
        }
    } catch (e: DataFormatException) {
        // keep whatever was decoded
    } finally {
        inf.end()
    }
    return out.toByteArray()
}

fun pngUnpredict(d: ByteArray, columns: Int, colors: Int, bpc: Int): ByteArray {
    val bpp = maxOf(1, (colors * bpc + 7) / 8)
    val rowLen = (columns * colors * bpc + 7) / 8
    val rows = d.size / (rowLen + 1)
    val out = ByteArray(rows * rowLen)
    for (r in 0 until rows) {
        val tag = d[r * (rowLen + 1)].toInt()
        val src = r * (rowLen + 1) + 1
        val dst = r * rowLen
        for (i in 0 until rowLen) {
            val x = d[src + i].toInt() and 0xFF
            val a = if (i >= bpp) (out[dst + i - bpp].toInt() and 0xFF) else 0
            val b = if (r > 0) (out[dst - rowLen + i].toInt() and 0xFF) else 0
            val c = if (r > 0 && i >= bpp) (out[dst - rowLen + i - bpp].toInt() and 0xFF) else 0
            val v: Int = when (tag) {
                0 -> x
                1 -> x + a
                2 -> x + b
                3 -> x + ((a + b) / 2)
                4 -> {
                    val p = a + b - c
                    val pa = Math.abs(p - a)
                    val pb = Math.abs(p - b)
                    val pc = Math.abs(p - c)
                    x + (if (pa <= pb && pa <= pc) a else if (pb <= pc) b else c)
                }
                else -> x
            }
            out[dst + i] = v.toByte()
        }
    }
    return out
}

// ---------------------------------------------------------------- lexer ------

class Lex(val b: ByteArray, var p: Int, val complete: Boolean) {

    private fun ws(c: Int): Boolean = isWsInt(c)

    // ( ) < > [ ] { } / %
    private fun delim(c: Int): Boolean {
        return c == 40 || c == 41 || c == 60 || c == 62 || c == 91 || c == 93 ||
            c == 123 || c == 125 || c == 47 || c == 37
    }

    fun cur(): Int {
        if (p >= b.size) throw PdfEof()
        return b[p].toInt() and 0xFF
    }

    fun skipWs() {
        while (p < b.size) {
            val c = b[p].toInt() and 0xFF
            if (ws(c)) {
                p++
            } else if (c == 37) {
                while (p < b.size && b[p].toInt() != 10 && b[p].toInt() != 13) p++
            } else {
                break
            }
        }
    }

    private fun token(): String {
        val s = p
        while (p < b.size) {
            val c = b[p].toInt() and 0xFF
            if (ws(c) || delim(c)) break
            p++
        }
        if (p >= b.size && !complete) throw PdfEof()
        return String(b, s, p - s, Charsets.ISO_8859_1)
    }

    private fun nameTok(): String {
        val t = token()
        if (t.indexOf('#') < 0) return t
        val sb = StringBuilder()
        var i = 0
        while (i < t.length) {
            val ch = t[i]
            if (ch == '#' && i + 2 < t.length + 0 && i + 2 <= t.length - 1) {
                val hv = t.substring(i + 1, i + 3).toIntOrNull(16)
                if (hv != null) {
                    sb.append(hv.toChar())
                    i += 3
                    continue
                }
            }
            sb.append(ch)
            i++
        }
        return sb.toString()
    }

    private fun tryRef(num: Int): PdfRef? {
        skipWs()
        if (p >= b.size) {
            if (!complete) throw PdfEof()
            return null
        }
        val c = cur()
        if (c < 48 || c > 57) return null
        val g = token().toIntOrNull() ?: return null
        skipWs()
        if (p >= b.size) {
            if (!complete) throw PdfEof()
            return null
        }
        if (cur() != 82) return null
        if (p + 1 < b.size) {
            val n = b[p + 1].toInt() and 0xFF
            if (!(ws(n) || delim(n))) return null
        } else if (!complete) {
            throw PdfEof()
        }
        p++
        return PdfRef(num, g)
    }

    fun value(): Any? {
        skipWs()
        val c = cur()
        if (c == 47) {
            p++
            return PdfName(nameTok())
        }
        if (c == 60) {
            if (p + 1 >= b.size) throw PdfEof()
            if ((b[p + 1].toInt() and 0xFF) == 60) {
                p += 2
                return dict()
            }
            p++
            return hexStr()
        }
        if (c == 91) {
            p++
            return arr()
        }
        if (c == 40) {
            p++
            return litStr()
        }
        if (c == 41 || c == 93 || c == 62 || c == 123 || c == 125) {
            throw PdfException("Unexpected delimiter at $p")
        }
        val t = token()
        if (t.isEmpty()) throw PdfException("Bad token at $p")
        val ch = t[0]
        if ((ch >= '0' && ch <= '9') || ch == '+' || ch == '-' || ch == '.') {
            if (t.indexOf('.') < 0) {
                val n = t.toLongOrNull()
                if (n != null) {
                    if (n >= 0L && n <= 2147483647L) {
                        val save = p
                        val r = tryRef(n.toInt())
                        if (r != null) return r
                        p = save
                    }
                    return n
                }
            } else {
                val dd = t.toDoubleOrNull()
                if (dd != null) return dd
            }
            return 0L
        }
        return when (t) {
            "true" -> true
            "false" -> false
            "null" -> null
            else -> PdfKw(t)
        }
    }

    private fun arr(): ArrayList<Any?> {
        val l = ArrayList<Any?>()
        while (true) {
            skipWs()
            if (cur() == 93) {
                p++
                return l
            }
            l.add(value())
        }
    }

    private fun dict(): PDict {
        val d = PDict()
        while (true) {
            skipWs()
            val c = cur()
            if (c == 62) {
                if (p + 1 >= b.size) throw PdfEof()
                p += 2
                return d
            }
            if (c != 47) throw PdfException("Dictionary key expected at $p")
            p++
            val k = nameTok()
            d[k] = value()
        }
    }

    private fun hexStr(): ByteArray {
        val out = ByteArrayOutputStream()
        var hi = -1
        while (true) {
            val c = cur()
            p++
            if (c == 62) break
            val v = Character.digit(c, 16)
            if (v < 0) continue
            if (hi < 0) {
                hi = v
            } else {
                out.write(hi * 16 + v)
                hi = -1
            }
        }
        if (hi >= 0) out.write(hi * 16)
        return out.toByteArray()
    }

    private fun litStr(): ByteArray {
        val out = ByteArrayOutputStream()
        var depth = 1
        while (true) {
            val c = cur()
            p++
            if (c == 92) {
                val d = cur()
                p++
                if (d == 110) out.write(10)
                else if (d == 114) out.write(13)
                else if (d == 116) out.write(9)
                else if (d == 98) out.write(8)
                else if (d == 102) out.write(12)
                else if (d >= 48 && d <= 55) {
                    var v = d - 48
                    var k = 0
                    while (k < 2 && p < b.size) {
                        val e = b[p].toInt() and 0xFF
                        if (e >= 48 && e <= 55) {
                            v = v * 8 + (e - 48)
                            p++
                            k++
                        } else {
                            break
                        }
                    }
                    out.write(v and 0xFF)
                } else if (d == 13) {
                    if (p < b.size && b[p].toInt() == 10) p++
                } else if (d == 10) {
                    // line continuation
                } else {
                    out.write(d)
                }
            } else if (c == 40) {
                depth++
                out.write(c)
            } else if (c == 41) {
                depth--
                if (depth == 0) break
                out.write(c)
            } else {
                out.write(c)
            }
        }
        return out.toByteArray()
    }
}

// ----------------------------------------------------------- PDF document ----

class PdfDoc(val ch: FileChannel) {
    val fileSize: Long = ch.size()
    val xref = HashMap<Int, XEnt>()
    var trailer: PDict = PDict()
    var newestIsStream: Boolean = false
    var lastStartXref: Long = 0L
    var pageCount: Int = 0
    private val objStmCache = LinkedHashMap<Int, ObjStm>()
    private var tokEnd: Int = 0
    private var remaining: Int = 0

    fun readAt(pos: Long, len: Int): ByteArray {
        if (pos < 0L || pos >= fileSize || len <= 0) return ByteArray(0)
        val n = minOf(len.toLong(), fileSize - pos).toInt()
        val bb = ByteBuffer.allocate(n)
        var off = pos
        while (bb.hasRemaining()) {
            val r = ch.read(bb, off)
            if (r < 0) break
            off += r.toLong()
        }
        return bb.array().copyOf(bb.position())
    }

    fun genOf(num: Int): Int {
        val e = xref[num]
        return if (e != null && e.type == 1) e.b else 0
    }

    fun maxObjNum(): Int {
        var mx = 0
        for (k in xref.keys) {
            if (k > mx) mx = k
        }
        return mx
    }

    fun open() {
        val tailLen = minOf(fileSize, 4096L).toInt()
        if (tailLen <= 0) throw PdfException("The PDF file is empty")
        val tail = readAt(fileSize - tailLen.toLong(), tailLen)
        val s = String(tail, Charsets.ISO_8859_1)
        val i = s.lastIndexOf("startxref")
        if (i < 0) throw PdfException("startxref not found (damaged PDF?)")
        val lx = Lex(tail, i + 9, true)
        val v = lx.value()
        lastStartXref = (v as? Long) ?: throw PdfException("Bad startxref value")
        readXrefChain(lastStartXref)
        if (trailer["Encrypt"] != null) {
            throw PdfException("Encrypted PDFs are not supported")
        }
        val rootRef = trailer["Root"] as? PdfRef ?: throw PdfException("PDF trailer has no Root")
        val root = loadDict(rootRef.num)
        val pagesRef = root["Pages"] as? PdfRef ?: throw PdfException("PDF has no page tree")
        val pagesDict = loadDict(pagesRef.num)
        pageCount = numToLong(resolve(pagesDict["Count"])).toInt()
        if (pageCount <= 0) throw PdfException("Could not determine the page count")
    }

    // ---- xref ----

    private fun readXrefChain(start: Long) {
        val visited = HashSet<Long>()
        var next: Long = start
        var first = true
        while (next >= 0L) {
            if (!visited.add(next)) break
            val tr = readXrefSection(next, first)
            if (first) {
                trailer = tr
                first = false
            }
            val xs = tr["XRefStm"]
            if (xs is Long) {
                if (visited.add(xs)) {
                    readXrefSection(xs, false)
                }
            }
            val prev = tr["Prev"]
            next = if (prev is Long) prev else if (prev is Double) prev.toLong() else -1L
        }
    }

    private fun readXrefSection(pos: Long, first: Boolean): PDict {
        val head = readAt(pos, 32)
        val full = String(head, Charsets.ISO_8859_1)
        val idx = full.indexOf("xref")
        if (idx >= 0 && full.substring(0, idx).isBlank()) {
            if (first) newestIsStream = false
            return readXrefTable(pos + idx.toLong() + 4L)
        }
        if (first) newestIsStream = true
        return readXrefStream(pos)
    }

    private fun intTok(blk: ByteArray, from: Int): Long {
        var i = from
        while (i < blk.size && isWsInt(blk[i].toInt() and 0xFF)) i++
        val s = i
        while (i < blk.size) {
            val c = blk[i].toInt()
            if (c < 48 || c > 57) break
            i++
        }
        tokEnd = i
        if (i == s) return -1L
        return String(blk, s, i - s, Charsets.ISO_8859_1).toLongOrNull() ?: -1L
    }

    private fun readXrefTable(afterKeyword: Long): PDict {
        var p = afterKeyword
        while (true) {
            val blk = readAt(p, 256)
            if (blk.isEmpty()) throw PdfException("Damaged xref table")
            var i = 0
            while (i < blk.size && isWsInt(blk[i].toInt() and 0xFF)) i++
            if (startsWithAt(blk, i, "trailer")) {
                val tp = p + i.toLong() + 7L
                val tb = readAt(tp, 65536)
                val complete = tp + tb.size.toLong() >= fileSize
                val lx = Lex(tb, 0, complete)
                val t = asDict(lx.value()) ?: throw PdfException("Bad trailer")
                return t
            }
            val start = intTok(blk, 0)
            if (start < 0L) throw PdfException("Bad xref subsection")
            val cnt = intTok(blk, tokEnd)
            if (cnt < 0L || cnt > 200000000L) throw PdfException("Bad xref subsection")
            var dpos = p + tokEnd.toLong()
            var left = cnt
            var k0 = start
            while (left > 0L) {
                val m = minOf(left, 50000L).toInt()
                val eb = readAt(dpos, m * 21 + 64)
                var q = 0
                for (k in 0 until m) {
                    val off = intTok(eb, q)
                    q = tokEnd
                    val gen = intTok(eb, q)
                    q = tokEnd
                    if (off < 0L || gen < 0L) throw PdfException("Bad xref entry")
                    while (q < eb.size && isWsInt(eb[q].toInt() and 0xFF)) q++
                    if (q >= eb.size) throw PdfException("Bad xref entry")
                    val flag = eb[q].toInt()
                    q++
                    val num = (k0 + k.toLong()).toInt()
                    if (!xref.containsKey(num)) {
                        if (flag == 110) {
                            xref[num] = XEnt(1, off, gen.toInt())
                        } else {
                            xref[num] = XEnt(0, 0L, 0)
                        }
                    }
                }
                dpos += q.toLong()
                left -= m.toLong()
                k0 += m.toLong()
            }
            p = dpos
        }
    }

    private fun field(d: ByteArray, off: Int, len: Int): Long {
        var v = 0L
        for (i in 0 until len) {
            v = (v shl 8) or (d[off + i].toLong() and 0xFFL)
        }
        return v
    }

    private fun readXrefStream(pos: Long): PDict {
        val obj = parseIndirectAt(pos, -1)
        val st = obj as? PdfStream ?: throw PdfException("Damaged xref stream")
        val data = streamData(st)
        val wl = st.dict["W"] as? List<*> ?: throw PdfException("xref stream has no W")
        if (wl.size < 3) throw PdfException("Bad W in xref stream")
        val w0 = numToLong(wl[0]).toInt()
        val w1 = numToLong(wl[1]).toInt()
        val w2 = numToLong(wl[2]).toInt()
        val size = numToLong(resolve(st.dict["Size"])).toInt()
        val idxList = st.dict["Index"] as? List<*>
        val ranges = ArrayList<Int>()
        if (idxList != null) {
            for (o in idxList) ranges.add(numToLong(o).toInt())
        } else {
            ranges.add(0)
            ranges.add(size)
        }
        val row = w0 + w1 + w2
        if (row <= 0) throw PdfException("Bad xref stream")
        var q = 0
        var ri = 0
        while (ri + 1 < ranges.size) {
            val s0 = ranges[ri]
            val cnt = ranges[ri + 1]
            ri += 2
            for (k in 0 until cnt) {
                if (q + row > data.size) break
                val type = if (w0 == 0) 1L else field(data, q, w0)
                val a = field(data, q + w0, w1)
                val b = field(data, q + w0 + w1, w2)
                q += row
                val num = s0 + k
                if (!xref.containsKey(num)) {
                    if (type == 1L) {
                        xref[num] = XEnt(1, a, b.toInt())
                    } else if (type == 2L) {
                        xref[num] = XEnt(2, a, b.toInt())
                    } else {
                        xref[num] = XEnt(0, 0L, 0)
                    }
                }
            }
        }
        return st.dict
    }

    // ---- objects ----

    fun resolve(o: Any?): Any? {
        if (o is PdfRef) return loadObject(o.num)
        return o
    }

    fun loadObject(num: Int): Any? {
        val e = xref[num] ?: return null
        return when (e.type) {
            1 -> parseIndirectAt(e.a, num)
            2 -> fromObjStm(e.a.toInt(), e.b, num)
            else -> null
        }
    }

    fun loadDict(num: Int): PDict {
        val o = loadObject(num)
        val d = asDict(o)
        if (d != null) return d
        if (o is PdfStream) return o.dict
        throw PdfException("Object $num is not a dictionary")
    }

    private fun parseIndirectAt(offset: Long, expectNum: Int): Any? {
        var size = 16384
        while (true) {
            val buf = readAt(offset, size)
            val complete = offset + buf.size.toLong() >= fileSize
            try {
                return parseIndirectBuf(buf, offset, expectNum, complete)
            } catch (e: PdfEof) {
                if (complete || size >= 64 * 1024 * 1024) {
                    throw PdfException("Unexpected end of data at offset $offset")
                }
                size *= 8
            }
        }
    }

    private fun parseIndirectBuf(buf: ByteArray, offset: Long, expectNum: Int, complete: Boolean): Any? {
        val lx = Lex(buf, 0, complete)
        val n = lx.value()
        lx.value()
        val kw = lx.value()
        if (n !is Long || kw !is PdfKw || kw.v != "obj") {
            throw PdfException("Damaged object at offset $offset")
        }
        if (expectNum >= 0 && n.toInt() != expectNum) {
            throw PdfException("Object number mismatch at offset $offset")
        }
        val v = lx.value()
        if (v is HashMap<*, *>) {
            lx.skipWs()
            if (lx.p + 6 <= buf.size) {
                if (startsWithAt(buf, lx.p, "stream")) {
                    var q = lx.p + 6
                    if (q < buf.size && buf[q].toInt() == 13) q++
                    if (q < buf.size && buf[q].toInt() == 10) q++
                    val dd = asDict(v) ?: throw PdfException("Bad stream dictionary")
                    return PdfStream(dd, offset + q.toLong())
                }
            } else if (!complete) {
                throw PdfEof()
            }
        }
        return v
    }

    fun streamData(st: PdfStream): ByteArray {
        val len = numToLong(resolve(st.dict["Length"]))
        if (len < 0L || len > 2000000000L) throw PdfException("Stream too large")
        val raw = readAt(st.dataPos, len.toInt())
        return decodeStream(st.dict, raw)
    }

    private fun decodeStream(dict: PDict, raw: ByteArray): ByteArray {
        val f = dict["Filter"]
        var fname: String? = null
        if (f is PdfName) {
            fname = f.v
        } else if (f is List<*>) {
            if (f.size == 1) {
                val f0 = f[0]
                if (f0 is PdfName) fname = f0.v
            } else if (f.size > 1) {
                throw PdfException("Unsupported chained stream filters")
            }
        }
        if (fname == null) return raw
        if (fname != "FlateDecode" && fname != "Fl") {
            throw PdfException("Unsupported stream filter: $fname")
        }
        val data = inflateBytes(raw)
        val dp = dict["DecodeParms"]
        var pd: PDict? = null
        if (dp is List<*>) {
            if (dp.isNotEmpty()) pd = asDict(dp[0])
        } else {
            pd = asDict(dp)
        }
        if (pd == null) return data
        val predictor = numToLong(pd["Predictor"]).toInt()
        if (predictor < 10) return data
        var columns = numToLong(pd["Columns"]).toInt()
        if (columns <= 0) columns = 1
        var colors = numToLong(pd["Colors"]).toInt()
        if (colors <= 0) colors = 1
        var bpc = numToLong(pd["BitsPerComponent"]).toInt()
        if (bpc <= 0) bpc = 8
        return pngUnpredict(data, columns, colors, bpc)
    }

    private fun getObjStm(stmNum: Int): ObjStm {
        val cached = objStmCache[stmNum]
        if (cached != null) return cached
        val st = loadObject(stmNum) as? PdfStream ?: throw PdfException("Object stream $stmNum missing")
        val data = streamData(st)
        val n = numToLong(resolve(st.dict["N"])).toInt()
        val first = numToLong(resolve(st.dict["First"])).toInt()
        val lx = Lex(data, 0, true)
        val nums = IntArray(n)
        val offs = IntArray(n)
        for (i in 0 until n) {
            nums[i] = numToLong(lx.value()).toInt()
            offs[i] = numToLong(lx.value()).toInt()
        }
        val os = ObjStm(data, first, nums, offs)
        objStmCache[stmNum] = os
        if (objStmCache.size > 6) {
            val k = objStmCache.keys.iterator().next()
            objStmCache.remove(k)
        }
        return os
    }

    private fun fromObjStm(stmNum: Int, index: Int, wantNum: Int): Any? {
        val os = getObjStm(stmNum)
        var i = index
        if (i < 0 || i >= os.nums.size || os.nums[i] != wantNum) {
            i = os.nums.indexOf(wantNum)
            if (i < 0) return null
        }
        val lx = Lex(os.data, os.first + os.offs[i], true)
        return lx.value()
    }

    // ---- page tree ----

    fun findPage(index0: Int): PageHit {
        val rootRef = trailer["Root"] as? PdfRef ?: throw PdfException("PDF trailer has no Root")
        val root = loadDict(rootRef.num)
        val pagesRef = root["Pages"] as? PdfRef ?: throw PdfException("PDF has no page tree")
        val d = loadDict(pagesRef.num)
        remaining = index0
        return walk(pagesRef.num, d, Inh(null, null, null), pagesRef.num)
            ?: throw PdfException("Page ${index0 + 1} not found in the page tree")
    }

    private fun walk(num: Int, d: PDict, inh: Inh, parent: Int): PageHit? {
        val kids = d["Kids"] as? List<*>
        if (kids == null) {
            if (remaining == 0) return PageHit(num, genOf(num), parent, d, inh)
            remaining--
            return null
        }
        val inh2 = inh.merge(d)
        for (k in kids) {
            val kr = k as? PdfRef ?: continue
            val kd = loadDict(kr.num)
            if (kd["Kids"] is List<*>) {
                val c = numToLong(resolve(kd["Count"])).toInt()
                if (c > 0 && remaining >= c) {
                    remaining -= c
                    continue
                }
            }
            val r = walk(kr.num, kd, inh2, num)
            if (r != null) return r
        }
        return null
    }

    private fun rect(o: Any?): DoubleArray? {
        val l = resolve(o) as? List<*> ?: return null
        if (l.size < 4) return null
        val a = DoubleArray(4)
        for (i in 0 until 4) a[i] = numToDouble(resolve(l[i]))
        return doubleArrayOf(
            minOf(a[0], a[2]), minOf(a[1], a[3]),
            maxOf(a[0], a[2]), maxOf(a[1], a[3])
        )
    }

    // Displayed page size in points (width, height), like PyMuPDF's page.rect
    fun pageSize(h: PageHit): DoubleArray {
        val box = rect(h.dict["CropBox"] ?: h.inh.cropBox)
            ?: rect(h.dict["MediaBox"] ?: h.inh.mediaBox)
            ?: doubleArrayOf(0.0, 0.0, 612.0, 792.0)
        var w = box[2] - box[0]
        var hh = box[3] - box[1]
        if (w <= 0.0 || hh <= 0.0) {
            w = 612.0
            hh = 792.0
        }
        val rotRaw = numToLong(resolve(h.dict["Rotate"] ?: h.inh.rotate)).toInt()
        val rot = ((rotRaw % 360) + 360) % 360
        if (rot == 90 || rot == 270) {
            val t = w
            w = hh
            hh = t
        }
        return doubleArrayOf(w, hh)
    }
}

// ------------------------------------------------------------- app part ------

class PreparedImage(val file: File, val width: Int, val height: Int, val comps: Int)

class ReplaceJob(
    val pageNum: Int,
    val hit: PageHit,
    val img: PreparedImage,
    val pw: Double,
    val ph: Double
)

class CountOut(val out: OutputStream) {
    var pos: Long = 0L
    fun write(b: ByteArray, off: Int, len: Int) {
        out.write(b, off, len)
        pos += len.toLong()
    }
    fun write(b: ByteArray) {
        write(b, 0, b.size)
    }
    fun str(s: String) {
        write(s.toByteArray(Charsets.ISO_8859_1))
    }
}

class MainActivity : Activity() {

    companion object {
        const val REQ_PDF = 1
        const val REQ_IMG = 2
        const val REQ_OUT = 3
    }

    private val MATCH = ViewGroup.LayoutParams.MATCH_PARENT
    private val WRAP = ViewGroup.LayoutParams.WRAP_CONTENT
    private val imageExts = setOf(".jpg", ".jpeg", ".png", ".bmp", ".webp", ".gif")

    private lateinit var prefs: SharedPreferences
    private var pdfUri: Uri? = null
    private var imgTree: Uri? = null
    private var outTree: Uri? = null

    private lateinit var pdfInfo: TextView
    private lateinit var imgInfo: TextView
    private lateinit var outInfo: TextView
    private lateinit var mappingEdit: EditText
    private lateinit var outNameEdit: EditText
    private lateinit var buildBtn: Button
    private lateinit var cancelBtn: Button
    private lateinit var progressBar: ProgressBar
    private lateinit var statusText: TextView
    private lateinit var logText: TextView
    private lateinit var logScroll: ScrollView

    @Volatile private var cancelFlag = false
    @Volatile private var running = false
    @Volatile private var partialOut: Uri? = null
    private val logBuf = StringBuilder()

    private fun dp(v: Int): Int = (v * resources.displayMetrics.density + 0.5f).toInt()

    // ------------------------------------------------------------ UI --------

    private fun heading(text: String): TextView {
        val t = TextView(this)
        t.text = text
        t.textSize = 15f
        t.setTypeface(null, Typeface.BOLD)
        t.setPadding(0, dp(16), 0, dp(4))
        return t
    }

    private fun note(text: String): TextView {
        val t = TextView(this)
        t.text = text
        t.textSize = 12f
        t.setTextColor(Color.LTGRAY)
        t.setPadding(0, dp(2), 0, dp(2))
        return t
    }

    private fun makeBtn(text: String, l: () -> Unit): Button {
        val b = Button(this)
        b.text = text
        b.isAllCaps = false
        b.setOnClickListener { l() }
        return b
    }

    override fun onCreate(savedInstanceState: Bundle?) {
        super.onCreate(savedInstanceState)
        prefs = getSharedPreferences("pdfpagereplacer", Context.MODE_PRIVATE)

        val root = ScrollView(this)
        val col = LinearLayout(this)
        col.orientation = LinearLayout.VERTICAL
        col.setPadding(dp(14), dp(14), dp(14), dp(24))
        root.addView(col, ViewGroup.LayoutParams(MATCH, WRAP))

        val title = TextView(this)
        title.text = "PDF Page Replacer"
        title.textSize = 22f
        title.setTypeface(null, Typeface.BOLD)
        col.addView(title)
        col.addView(note("Replace pages of any size PDF (KB to 10 GB+) with images. The PDF is never loaded into memory."))

        col.addView(heading("1. Choose the large PDF file"))
        col.addView(makeBtn("Choose PDF...") { pickPdf() }, LinearLayout.LayoutParams(MATCH, WRAP))
        pdfInfo = note("No PDF chosen")
        col.addView(pdfInfo)

        col.addView(heading("2. Choose the folder with replacement page images"))
        col.addView(makeBtn("Choose images folder...") { pickTree(REQ_IMG) }, LinearLayout.LayoutParams(MATCH, WRAP))
        imgInfo = note("No folder chosen")
        col.addView(imgInfo)

        col.addView(heading("3. Page number = replacement filename (one per line)"))
        col.addView(note("Example:\n    634 = 634.jpg\n    760 = 760.png\nYou can also write just the page number (634) and the app auto-finds a file named 634.* in the folder. Page numbers are 1-based, as shown in a PDF viewer."))
        mappingEdit = EditText(this)
        mappingEdit.typeface = Typeface.MONOSPACE
        mappingEdit.textSize = 14f
        mappingEdit.minLines = 6
        mappingEdit.gravity = Gravity.TOP or Gravity.START
        mappingEdit.setText("634 = 634.jpg\n760 = 760.jpg\n")
        col.addView(mappingEdit, LinearLayout.LayoutParams(MATCH, WRAP))

        col.addView(heading("4. Output location"))
        col.addView(makeBtn("Choose output folder...") { pickTree(REQ_OUT) }, LinearLayout.LayoutParams(MATCH, WRAP))
        outInfo = note("No folder chosen")
        col.addView(outInfo)
        col.addView(note("Output file name (the original file is never changed):"))
        outNameEdit = EditText(this)
        outNameEdit.setSingleLine(true)
        outNameEdit.textSize = 14f
        col.addView(outNameEdit, LinearLayout.LayoutParams(MATCH, WRAP))

        val row = LinearLayout(this)
        row.orientation = LinearLayout.HORIZONTAL
        buildBtn = makeBtn("Build New PDF") { startBuild() }
        cancelBtn = makeBtn("Cancel") { cancelBuild() }
        cancelBtn.isEnabled = false
        row.addView(buildBtn, LinearLayout.LayoutParams(0, WRAP, 1f))
        row.addView(cancelBtn, LinearLayout.LayoutParams(0, WRAP, 1f))
        val rowLp = LinearLayout.LayoutParams(MATCH, WRAP)
        rowLp.topMargin = dp(16)
        col.addView(row, rowLp)

        progressBar = ProgressBar(this, null, android.R.attr.progressBarStyleHorizontal)
        progressBar.max = 1000
        col.addView(progressBar, LinearLayout.LayoutParams(MATCH, WRAP))
        statusText = note("Ready.")
        col.addView(statusText)

        col.addView(heading("Log"))
        logScroll = ScrollView(this)
        logText = TextView(this)
        logText.typeface = Typeface.MONOSPACE
        logText.textSize = 11f
        logText.setTextColor(Color.rgb(0, 230, 0))
        logText.setBackgroundColor(Color.rgb(17, 17, 17))
        logText.setPadding(dp(8), dp(8), dp(8), dp(8))
        logScroll.addView(logText, ViewGroup.LayoutParams(MATCH, WRAP))
        logScroll.setOnTouchListener { v, _ ->
            v.parent.requestDisallowInterceptTouchEvent(true)
            false
        }
        col.addView(logScroll, LinearLayout.LayoutParams(MATCH, dp(240)))

        setContentView(root)
        restoreState()
        log("Ready.")
    }

    override fun onPause() {
        super.onPause()
        saveState()
    }

    // ---------------------------------------------------------- state --------

    private fun hasPerm(u: Uri): Boolean {
        try {
            for (p in contentResolver.persistedUriPermissions) {
                if (p.uri == u) return true
            }
        } catch (e: Exception) {
        }
        return false
    }

    private fun saveState() {
        val ed = prefs.edit()
        ed.putString("pdf", pdfUri?.toString())
        ed.putString("img", imgTree?.toString())
        ed.putString("out", outTree?.toString())
        ed.putString("mapping", mappingEdit.text.toString())
        ed.putString("outname", outNameEdit.text.toString())
        ed.apply()
    }

    private fun restoreState() {
        val m = prefs.getString("mapping", null)
        if (m != null) mappingEdit.setText(m)
        val on = prefs.getString("outname", null)
        if (on != null) outNameEdit.setText(on)

        val ps = prefs.getString("pdf", null)
        if (ps != null) {
            val u = Uri.parse(ps)
            if (hasPerm(u)) {
                pdfUri = u
                showPdf(u, false)
            }
        }
        val isr = prefs.getString("img", null)
        if (isr != null) {
            val u = Uri.parse(isr)
            if (hasPerm(u)) {
                imgTree = u
                imgInfo.text = treeLabel(u)
            }
        }
        val os = prefs.getString("out", null)
        if (os != null) {
            val u = Uri.parse(os)
            if (hasPerm(u)) {
                outTree = u
                outInfo.text = treeLabel(u)
            }
        }
    }

    private fun treeLabel(u: Uri): String {
        return try {
            Uri.decode(DocumentsContract.getTreeDocumentId(u))
        } catch (e: Exception) {
            u.toString()
        }
    }

    // ------------------------------------------------------ file pickers -----

    private fun pickPdf() {
        val i = Intent(Intent.ACTION_OPEN_DOCUMENT)
        i.addCategory(Intent.CATEGORY_OPENABLE)
        i.type = "application/pdf"
        startActivityForResult(i, REQ_PDF)
    }

    private fun pickTree(req: Int) {
        val i = Intent(Intent.ACTION_OPEN_DOCUMENT_TREE)
        i.addFlags(
            Intent.FLAG_GRANT_READ_URI_PERMISSION or
                Intent.FLAG_GRANT_WRITE_URI_PERMISSION or
                Intent.FLAG_GRANT_PERSISTABLE_URI_PERMISSION or
                Intent.FLAG_GRANT_PREFIX_URI_PERMISSION
        )
        startActivityForResult(i, req)
    }

    private fun persist(uri: Uri, write: Boolean) {
        try {
            var f = Intent.FLAG_GRANT_READ_URI_PERMISSION
            if (write) f = f or Intent.FLAG_GRANT_WRITE_URI_PERMISSION
            contentResolver.takePersistableUriPermission(uri, f)
        } catch (e: Exception) {
        }
    }

    override fun onActivityResult(requestCode: Int, resultCode: Int, data: Intent?) {
        super.onActivityResult(requestCode, resultCode, data)
        if (resultCode != RESULT_OK || data == null) return
        val uri = data.data ?: return
        when (requestCode) {
            REQ_PDF -> {
                persist(uri, false)
                pdfUri = uri
                showPdf(uri, true)
            }
            REQ_IMG -> {
                persist(uri, true)
                imgTree = uri
                imgInfo.text = treeLabel(uri)
            }
            REQ_OUT -> {
                persist(uri, true)
                outTree = uri
                outInfo.text = treeLabel(uri)
            }
        }
    }

    private fun queryNameSize(uri: Uri): Pair<String, Long> {
        var name = "document.pdf"
        var size = 0L
        try {
            val c = contentResolver.query(
                uri,
                arrayOf(OpenableColumns.DISPLAY_NAME, OpenableColumns.SIZE),
                null, null, null
            )
            if (c != null) {
                try {
                    if (c.moveToFirst()) {
                        val n = c.getString(0)
                        if (n != null) name = n
                        size = c.getLong(1)
                    }
                } finally {
                    c.close()
                }
            }
        } catch (e: Exception) {
        }
        return Pair(name, size)
    }

    private fun showPdf(uri: Uri, setOutName: Boolean) {
        val ns = queryNameSize(uri)
        pdfInfo.text = ns.first + "  (" + fmtSize(ns.second) + ")\nReading page count..."
        if (setOutName) {
            var base = ns.first
            if (base.lowercase(Locale.US).endsWith(".pdf")) base = base.substring(0, base.length - 4)
            outNameEdit.setText(base + "_modified.pdf")
        }
        val label = ns.first + "  (" + fmtSize(ns.second) + ")"
        Thread {
            var msg: String
            try {
                val pfd = contentResolver.openFileDescriptor(uri, "r")
                    ?: throw PdfException("Cannot open the PDF")
                try {
                    val doc = PdfDoc(FileInputStream(pfd.fileDescriptor).channel)
                    doc.open()
                    msg = label + "\nPages: " + doc.pageCount
                } finally {
                    try {
                        pfd.close()
                    } catch (e: Exception) {
                    }
                }
            } catch (e: Throwable) {
                msg = label + "\nCould not read page count: " + (e.message ?: e.toString())
            }
            val finalMsg = msg
            runOnUiThread { pdfInfo.text = finalMsg }
        }.start()
    }

    // ------------------------------------------------------------ logging ----

    private fun log(message: String) {
        runOnUiThread {
            logBuf.append(message).append('\n')
            if (logBuf.length > 40000) {
                logBuf.delete(0, logBuf.length - 30000)
            }
            logText.text = logBuf.toString()
            logScroll.post { logScroll.fullScroll(ScrollView.FOCUS_DOWN) }
        }
    }

    private fun toast(s: String) {
        Toast.makeText(this, s, Toast.LENGTH_LONG).show()
    }

    // -------------------------------------------------------- build flow -----

    private fun parseMapping(text: String): TreeMap<Int, String> {
        val map = TreeMap<Int, String>()
        val r1 = Regex("^(\\d+)\\s*[:=]\\s*(.*)$")
        val r2 = Regex("^(\\d+)$")
        for (raw in text.split("\n")) {
            val line = raw.trim()
            if (line.isEmpty() || line.startsWith("#")) continue
            val m1 = r1.find(line)
            if (m1 != null) {
                map[m1.groupValues[1].toInt()] = m1.groupValues[2].trim()
            } else {
                val m2 = r2.find(line)
                if (m2 != null) {
                    map[m2.groupValues[1].toInt()] = ""
                } else {
                    throw IllegalArgumentException("Could not parse line: $raw\nExpected format: 634 = 634.jpg")
                }
            }
        }
        return map
    }

    private fun startBuild() {
        if (running) {
            toast("A build is already running.")
            return
        }
        val pdf = pdfUri
        val imgT = imgTree
        val outT = outTree
        if (pdf == null) {
            toast("Please choose a PDF file.")
            return
        }
        if (imgT == null) {
            toast("Please choose the replacement-images folder.")
            return
        }
        if (outT == null) {
            toast("Please choose the output folder.")
            return
        }
        var outName = outNameEdit.text.toString().trim()
        if (outName.isEmpty()) {
            toast("Please type an output file name.")
            return
        }
        if (!outName.lowercase(Locale.US).endsWith(".pdf")) outName += ".pdf"
        val mapping: TreeMap<Int, String> = try {
            parseMapping(mappingEdit.text.toString())
        } catch (e: IllegalArgumentException) {
            toast(e.message ?: "Mapping error")
            return
        }
        if (mapping.isEmpty()) {
            toast("Please enter at least one page mapping.")
            return
        }
        saveState()

        running = true
        cancelFlag = false
        partialOut = null
        buildBtn.isEnabled = false
        cancelBtn.isEnabled = true
        progressBar.progress = 0
        log("============================================================")
        log("Starting build...")
        val finalName = outName

        Thread {
            var ok = false
            var msg = ""
            try {
                msg = doBuild(pdf, imgT, outT, finalName, mapping)
                ok = true
                partialOut = null
            } catch (e: CancelEx) {
                msg = "Cancelled by user."
                cleanupPartial()
            } catch (e: Throwable) {
                msg = e.message ?: e.toString()
                cleanupPartial()
            }
            val fOk = ok
            val fMsg = msg
            runOnUiThread {
                running = false
                buildBtn.isEnabled = true
                cancelBtn.isEnabled = false
                statusText.text = if (fOk) "Done." else "Stopped."
                if (fOk) progressBar.progress = 1000
                log(if (fOk) fMsg else "ERROR: $fMsg")
                toast(fMsg)
            }
        }.start()
    }

    private fun cancelBuild() {
        if (!running) return
        cancelFlag = true
        log("Cancel requested - stopping as soon as possible...")
    }

    private fun checkCancel() {
        if (cancelFlag) throw CancelEx()
    }

    private fun cleanupPartial() {
        val u = partialOut
        partialOut = null
        if (u != null) {
            try {
                DocumentsContract.deleteDocument(contentResolver, u)
            } catch (e: Exception) {
            }
        }
    }

    private fun setStatus(s: String) {
        runOnUiThread { statusText.text = s }
    }

    // ---------------------------------------------------- folder & images ----

    private fun listFolder(tree: Uri): LinkedHashMap<String, Uri> {
        val map = LinkedHashMap<String, Uri>()
        val parentId = DocumentsContract.getTreeDocumentId(tree)
        val childrenUri = DocumentsContract.buildChildDocumentsUriUsingTree(tree, parentId)
        val c = contentResolver.query(
            childrenUri,
            arrayOf(
                DocumentsContract.Document.COLUMN_DOCUMENT_ID,
                DocumentsContract.Document.COLUMN_DISPLAY_NAME
            ),
            null, null, null
        )
        if (c != null) {
            try {
                while (c.moveToNext()) {
                    val id = c.getString(0)
                    val name = c.getString(1)
                    if (id != null && name != null) {
                        map[name] = DocumentsContract.buildDocumentUriUsingTree(tree, id)
                    }
                }
            } finally {
                c.close()
            }
        }
        return map
    }

    private fun findByName(files: LinkedHashMap<String, Uri>, fname: String): Uri? {
        val exact = files[fname]
        if (exact != null) return exact
        for (e in files.entries) {
            if (e.key.equals(fname, ignoreCase = true)) return e.value
        }
        return null
    }

    private fun findForPage(files: LinkedHashMap<String, Uri>, page: Int): Uri? {
        val stem = page.toString()
        for (e in files.entries) {
            val name = e.key
            val dot = name.lastIndexOf('.')
            if (dot <= 0) continue
            val s = name.substring(0, dot)
            val ext = name.substring(dot).lowercase(Locale.US)
            if (s == stem && imageExts.contains(ext)) return e.value
        }
        return null
    }

    private fun jpegInfo(b: ByteArray): IntArray? {
        if (b.size < 12) return null
        if ((b[0].toInt() and 0xFF) != 0xFF || (b[1].toInt() and 0xFF) != 0xD8) return null
        var i = 2
        while (i + 9 < b.size) {
            if ((b[i].toInt() and 0xFF) != 0xFF) {
                i++
                continue
            }
            val m = b[i + 1].toInt() and 0xFF
            if (m == 0xFF) {
                i++
                continue
            }
            if (m == 0xD8 || m == 0x01 || (m >= 0xD0 && m <= 0xD7)) {
                i += 2
                continue
            }
            if (m == 0xD9) break
            val len = ((b[i + 2].toInt() and 0xFF) shl 8) or (b[i + 3].toInt() and 0xFF)
            if (m == 0xC0 || m == 0xC1 || m == 0xC2) {
                val h = ((b[i + 5].toInt() and 0xFF) shl 8) or (b[i + 6].toInt() and 0xFF)
                val w = ((b[i + 7].toInt() and 0xFF) shl 8) or (b[i + 8].toInt() and 0xFF)
                val comps = b[i + 9].toInt() and 0xFF
                if (w > 0 && h > 0 && (comps == 1 || comps == 3)) {
                    return intArrayOf(w, h, comps)
                }
                return null
            }
            i += 2 + len
        }
        return null
    }

    private fun prepareImage(uri: Uri, outFile: File): PreparedImage {
        val ins = contentResolver.openInputStream(uri) ?: throw PdfException("Cannot open image file")
        val bytes: ByteArray
        try {
            bytes = ins.readBytes()
        } finally {
            try {
                ins.close()
            } catch (e: Exception) {
            }
        }
        val ji = jpegInfo(bytes)
        if (ji != null) {
            val fos = FileOutputStream(outFile)
            try {
                fos.write(bytes)
            } finally {
                fos.close()
            }
            return PreparedImage(outFile, ji[0], ji[1], ji[2])
        }
        val bo = BitmapFactory.Options()
        bo.inJustDecodeBounds = true
        BitmapFactory.decodeByteArray(bytes, 0, bytes.size, bo)
        if (bo.outWidth <= 0 || bo.outHeight <= 0) {
            throw PdfException("Cannot decode image (unsupported format?)")
        }
        var sample = 1
        while ((bo.outWidth / sample).toLong() * (bo.outHeight / sample).toLong() > 40000000L) {
            sample *= 2
        }
        val o2 = BitmapFactory.Options()
        o2.inSampleSize = sample
        o2.inPreferredConfig = Bitmap.Config.ARGB_8888
        val bmp = BitmapFactory.decodeByteArray(bytes, 0, bytes.size, o2)
            ?: throw PdfException("Cannot decode image")
        var finalBmp: Bitmap = bmp
        if (bmp.hasAlpha()) {
            val flat = Bitmap.createBitmap(bmp.width, bmp.height, Bitmap.Config.ARGB_8888)
            val cv = Canvas(flat)
            cv.drawColor(Color.WHITE)
            cv.drawBitmap(bmp, 0f, 0f, null)
            bmp.recycle()
            finalBmp = flat
        }
        val w = finalBmp.width
        val h = finalBmp.height
        val fos = FileOutputStream(outFile)
        try {
            finalBmp.compress(Bitmap.CompressFormat.JPEG, 95, fos)
        } finally {
            fos.close()
        }
        finalBmp.recycle()
        return PreparedImage(outFile, w, h, 3)
    }

    // -------------------------------------------------------- the big job ----

    private fun doBuild(
        pdf: Uri,
        imgT: Uri,
        outT: Uri,
        outName: String,
        mapping: TreeMap<Int, String>
    ): String {
        val temps = ArrayList<File>()
        try {
            log("Listing images folder...")
            setStatus("Looking for images...")
            val files = listFolder(imgT)
            val resolved = TreeMap<Int, Uri>()
            for (entry in mapping.entries) {
                checkCancel()
                val pn = entry.key
                val fname = entry.value
                val u: Uri? = if (fname.isNotEmpty()) findByName(files, fname) else findForPage(files, pn)
                if (u == null) {
                    if (fname.isNotEmpty()) {
                        throw IllegalStateException("Page $pn: file '$fname' not found in the images folder")
                    }
                    throw IllegalStateException("Page $pn: no file named '$pn.*' found in the images folder")
                }
                resolved[pn] = u
                log("  Page $pn  <-  " + (if (fname.isNotEmpty()) fname else "$pn.* (auto)"))
            }

            setStatus("Reading PDF structure...")
            val pfd = contentResolver.openFileDescriptor(pdf, "r")
                ?: throw IllegalStateException("Cannot open the PDF file")
            try {
                val ch = FileInputStream(pfd.fileDescriptor).channel
                val doc = PdfDoc(ch)
                log("Opening PDF (" + fmtSize(doc.fileSize) + ")...")
                doc.open()
                val total = doc.pageCount
                log("Total pages in original PDF: $total")

                val jobs = ArrayList<ReplaceJob>()
                for (entry in resolved.entries) {
                    checkCancel()
                    val pn = entry.key
                    if (pn < 1 || pn > total) {
                        throw IllegalStateException("Page $pn is out of range (PDF has $total pages).")
                    }
                    setStatus("Preparing image for page $pn...")
                    val hit = doc.findPage(pn - 1)
                    val sz = doc.pageSize(hit)
                    val tmp = File(cacheDir, "pg_" + pn + ".jpg")
                    temps.add(tmp)
                    log("Building replacement for page $pn (size " + sz[0].toInt() + "x" + sz[1].toInt() + " pt)...")
                    val prep = prepareImage(entry.value, tmp)
                    jobs.add(ReplaceJob(pn, hit, prep, sz[0], sz[1]))
                }

                // ---- create output ----
                checkCancel()
                val outDir = DocumentsContract.buildDocumentUriUsingTree(
                    outT, DocumentsContract.getTreeDocumentId(outT)
                )
                val outDoc = DocumentsContract.createDocument(contentResolver, outDir, "application/pdf", outName)
                    ?: throw IllegalStateException("Could not create the output file in the chosen folder")
                partialOut = outDoc
                val os = contentResolver.openOutputStream(outDoc, "w")
                    ?: throw IllegalStateException("Could not open the output file for writing")
                val out = BufferedOutputStream(os, 1 shl 20)
                val w = CountOut(out)
                try {
                    // ---- 1) stream-copy the original ----
                    log("Copying original PDF (streamed, low memory)...")
                    val buf = ByteArray(4 shl 20)
                    val bb = ByteBuffer.wrap(buf)
                    val size = doc.fileSize
                    var off = 0L
                    var lastUi = 0L
                    while (off < size) {
                        checkCancel()
                        bb.clear()
                        val r = ch.read(bb, off)
                        if (r <= 0) break
                        w.write(buf, 0, r)
                        off += r.toLong()
                        val now = System.currentTimeMillis()
                        if (now - lastUi > 250L) {
                            lastUi = now
                            val pct = (off * 1000L / size).toInt()
                            val offNow = off
                            runOnUiThread {
                                progressBar.progress = pct
                                statusText.text = "Copying original PDF... " + (pct / 10) + "%  (" +
                                    fmtSize(offNow) + " / " + fmtSize(size) + ")"
                            }
                        }
                    }
                    if (off != size) throw IllegalStateException("Copy incomplete (read $off of $size bytes)")

                    // ---- 2) append replacement pages (incremental update) ----
                    setStatus("Adding replacement pages...")
                    log("Swapping in " + jobs.size + " page(s)...")
                    var nextObj = maxOf(numToLong(doc.trailer["Size"]).toInt(), doc.maxObjNum() + 1)
                    val entries = ArrayList<LongArray>()
                    w.str("\n")

                    for (job in jobs) {
                        checkCancel()
                        val imgNum = nextObj
                        nextObj++
                        val cntNum = nextObj
                        nextObj++

                        // image object
                        val img = job.img
                        val cs = if (img.comps == 1) "DeviceGray" else "DeviceRGB"
                        entries.add(longArrayOf(imgNum.toLong(), w.pos, 0L))
                        w.str(
                            "$imgNum 0 obj\n<< /Type /XObject /Subtype /Image /Width ${img.width} " +
                                "/Height ${img.height} /ColorSpace /$cs /BitsPerComponent 8 " +
                                "/Filter /DCTDecode /Length ${img.file.length()} >>\nstream\n"
                        )
                        val fi = FileInputStream(img.file)
                        try {
                            val cb = ByteArray(1 shl 16)
                            while (true) {
                                val rr = fi.read(cb)
                                if (rr < 0) break
                                w.write(cb, 0, rr)
                            }
                        } finally {
                            fi.close()
                        }
                        w.str("\nendstream\nendobj\n")

                        // content stream: white background + image scaled to fit, centered
                        val scale = minOf(job.pw / img.width.toDouble(), job.ph / img.height.toDouble())
                        val dw = img.width.toDouble() * scale
                        val dh = img.height.toDouble() * scale
                        val ox = (job.pw - dw) / 2.0
                        val oy = (job.ph - dh) / 2.0
                        val content = "q 1 1 1 rg 0 0 ${fmtNum(job.pw)} ${fmtNum(job.ph)} re f Q\n" +
                            "q ${fmtNum(dw)} 0 0 ${fmtNum(dh)} ${fmtNum(ox)} ${fmtNum(oy)} cm /Im0 Do Q\n"
                        val cbytes = content.toByteArray(Charsets.ISO_8859_1)
                        entries.add(longArrayOf(cntNum.toLong(), w.pos, 0L))
                        w.str("$cntNum 0 obj\n<< /Length ${cbytes.size} >>\nstream\n")
                        w.write(cbytes)
                        w.str("\nendstream\nendobj\n")

                        // page object (same object number as the original page)
                        val hit = job.hit
                        entries.add(longArrayOf(hit.num.toLong(), w.pos, hit.gen.toLong()))
                        w.str(
                            "${hit.num} ${hit.gen} obj\n<< /Type /Page /Parent ${hit.parent} " +
                                "${doc.genOf(hit.parent)} R /MediaBox [0 0 ${fmtNum(job.pw)} ${fmtNum(job.ph)}] " +
                                "/Resources << /XObject << /Im0 $imgNum 0 R >> /ProcSet [/PDF /ImageB /ImageC] >> " +
                                "/Contents $cntNum 0 R >>\nendobj\n"
                        )
                        log("  Page ${job.pageNum} replaced.")
                    }

                    // ---- 3) cross-reference section ----
                    val rootRef = doc.trailer["Root"] as? PdfRef
                        ?: throw IllegalStateException("PDF trailer has no Root")
                    val infoRef = doc.trailer["Info"] as? PdfRef
                    val infoStr = if (infoRef != null) " /Info ${infoRef.num} ${infoRef.gen} R" else ""
                    val prev = doc.lastStartXref
                    val useStream = doc.newestIsStream || w.pos >= 9999999999L

                    if (useStream) {
                        val xnum = nextObj
                        nextObj++
                        val xpos = w.pos
                        entries.add(longArrayOf(xnum.toLong(), xpos, 0L))
                        entries.sortBy { it[0] }
                        val idx = StringBuilder()
                        val data = ByteArrayOutputStream()
                        var i = 0
                        while (i < entries.size) {
                            var j = i
                            while (j + 1 < entries.size && entries[j + 1][0] == entries[j][0] + 1L) j++
                            idx.append(entries[i][0]).append(' ').append(j - i + 1).append(' ')
                            for (k in i..j) {
                                val e = entries[k]
                                data.write(1)
                                var sh = 56
                                while (sh >= 0) {
                                    data.write(((e[1] shr sh) and 0xFFL).toInt())
                                    sh -= 8
                                }
                                data.write(((e[2] shr 8) and 0xFFL).toInt())
                                data.write((e[2] and 0xFFL).toInt())
                            }
                            i = j + 1
                        }
                        val xb = data.toByteArray()
                        w.str(
                            "$xnum 0 obj\n<< /Type /XRef /Size $nextObj /W [1 8 2] /Index [${idx.toString().trim()}] " +
                                "/Root ${rootRef.num} ${rootRef.gen} R$infoStr /Prev $prev /Length ${xb.size} >>\nstream\n"
                        )
                        w.write(xb)
                        w.str("\nendstream\nendobj\nstartxref\n$xpos\n%%EOF\n")
                    } else {
                        entries.sortBy { it[0] }
                        val xpos = w.pos
                        w.str("xref\n")
                        var i = 0
                        while (i < entries.size) {
                            var j = i
                            while (j + 1 < entries.size && entries[j + 1][0] == entries[j][0] + 1L) j++
                            w.str("${entries[i][0]} ${j - i + 1}\n")
                            for (k in i..j) {
                                w.str(String.format(Locale.US, "%010d %05d n \n", entries[k][1], entries[k][2]))
                            }
                            i = j + 1
                        }
                        w.str(
                            "trailer\n<< /Size $nextObj /Root ${rootRef.num} ${rootRef.gen} R$infoStr /Prev $prev >>\n" +
                                "startxref\n$xpos\n%%EOF\n"
                        )
                    }
                    out.flush()
                } finally {
                    try {
                        out.close()
                    } catch (e: Exception) {
                    }
                }
                return "New PDF created: $outName  (" + fmtSize(w.pos) + ")"
            } finally {
                try {
                    pfd.close()
                } catch (e: Exception) {
                }
            }
        } finally {
            for (f in temps) {
                try {
                    f.delete()
                } catch (e: Exception) {
                }
            }
        }
    }
}
