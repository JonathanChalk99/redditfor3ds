// 3DS Reddit viewer
//
// LIST view   top: post cards      bottom: preview + Prev/Next/Open + Search/Sub/Sort
// POST view   top: image/GIF + title   bottom: scrollable nested comments + Back
//
// Controls: D-pad up/down  move / scroll     A  open post     B  back
//           X  search all of Reddit   Y  Home feed   B  leave search   L/R  jump 3 pages   START  exit
//           SELECT / START  change Top's time range (while sorting by Top; START exits otherwise)
// Touch:    on-screen buttons; drag the comments area to scroll.
//
// Data comes from your own proxy (see functions/api/[[path]].js). Put its address in
//   sdmc:/3ds/redditviewer/server.txt     e.g.  https://my-project.pages.dev/api
// Nothing is ever written to the console's NAND; this app only reads that one SD file.
#include <3ds.h>
#include <citro2d.h>
#include <citro3d.h>
#include <ctype.h>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <sys/stat.h>

#define STB_IMAGE_IMPLEMENTATION
#define STBI_ONLY_JPEG
#define STBI_NO_STDIO
#include "stb_image.h"

// ---------------------------------------------------------------- types ----
enum { MEDIA_NONE = 0, MEDIA_PHOTO = 1, MEDIA_GIF = 2 };

#define MAX_POSTS 30
#define SEARCH_MAX_POSTS 20   // searches show the top 20 results
#define MAX_COMMENTS 50
#define MAX_LINE 80

typedef struct {
    char id[16], sub[40], author[32];
    int score, ncomments, media;
    char *key;            // URL-encoded media URL (malloc'd) or NULL
    char title[204], body[404];
} Post;

typedef struct {
    int depth, score;
    char author[32], text[304];
} Comment;

typedef struct {
    C3D_Tex tex;
    Tex3DS_SubTexture sub;
    C2D_Image img;
    int w, h;
    bool ok;
} Img;

enum { VIEW_LIST, VIEW_POST };

// media loading state machine for the open post
enum { MS_NONE, MS_PHOTO, MS_GIFINFO, MS_GIFFRAMES, MS_DONE, MS_FAILED };

// ---------------------------------------------------------------- state ----
static Post posts[MAX_POSTS];
static int postCount = 0;
static Comment cms[MAX_COMMENTS];
static int cmCount = 0;

static char apiBase[256] = "";
static char subName[200] = "all";
static bool isHome = true;          // true while showing the adaptive Home feed
static char homeLabel[96] = "";     // readable list of the subreddits Home is built from
static bool prevIsHome = true;      // the feed you were in before searching, so you can go back to it
static char prevSub[200] = "all";
static char query[64] = "";
static const char *sorts[] = {"hot", "new", "top", "rising"};
static int sortIdx = 0;
#define SORT_TOP 2                       // index of "top" in sorts[]
static const char *tRanges[] = {"day", "week", "month", "year", "all"};   // sent to the proxy as &t=
static int tIdx = 0;                     // which time range Top is using
static void sortText(char *out, size_t n) {
    if (sortIdx == SORT_TOP) snprintf(out, n, "top: %s", tRanges[tIdx]);
    else snprintf(out, n, "%s", sorts[sortIdx]);
}
static char lastErr[200] = "";

static C3D_RenderTarget *topT, *botT;
static C2D_TextBuf textBuf;
static u32 cBg, cCard, cCardSel, cAccent, cText, cDim, cHeader, cBtn;

#define PHOTO_W 256
#define PHOTO_H 192
#define GIF_W 256
#define GIF_H 192
#define GIF_MAX 8
static Img photo, gif[GIF_MAX];
static int mediaState = MS_NONE;
static int gifSrcFrames = 1, gifTotal = 0, gifLoaded = 0, gifDelayMs = 100;

#define CARD_H 50.0f
#define CARD_PITCH 54.0f
#define LIST_TOP 30.0f
#define CARDS_PER_PAGE 4     // about how many post cards fit on the top screen
#define PAGES_PER_JUMP 3     // L/R jump this many screens of posts (fewer if the list runs out)

// -------------------------------------------------------------- helpers ----
static void initColors(void) {
    cBg      = C2D_Color32(24, 26, 27, 255);
    cCard    = C2D_Color32(39, 41, 43, 255);
    cCardSel = C2D_Color32(58, 61, 64, 255);
    cAccent  = C2D_Color32(255, 69, 0, 255);
    cText    = C2D_Color32(235, 237, 240, 255);
    cDim     = C2D_Color32(140, 146, 152, 255);
    cHeader  = C2D_Color32(18, 19, 20, 255);
    cBtn     = C2D_Color32(52, 55, 58, 255);
}

static bool utf8Decode(const char *p, u32 *out) {
    if (!p || !*p || !out) return false;
    const unsigned char *s = (const unsigned char*)p;
    if (s[0] < 0x80) { *out = s[0]; return true; }
    if ((s[0] & 0xE0) == 0xC0 && s[1]) {
        *out = ((u32)(s[0] & 0x1F) << 6) | (s[1] & 0x3F);
        return *out >= 0x80;
    }
    if ((s[0] & 0xF0) == 0xE0 && s[1] && s[2]) {
        *out = ((u32)(s[0] & 0x0F) << 12) | ((u32)(s[1] & 0x3F) << 6) | (s[2] & 0x3F);
        return *out >= 0x800;
    }
    if ((s[0] & 0xF8) == 0xF0 && s[1] && s[2] && s[3]) {
        *out = ((u32)(s[0] & 0x07) << 18) | ((u32)(s[1] & 0x3F) << 12) |
               ((u32)(s[2] & 0x3F) << 6) | (s[3] & 0x3F);
        return *out >= 0x10000 && *out <= 0x10FFFF;
    }
    *out = 0xFFFD;
    return false;
}

static int emojiUtf8Len(const char *p) {
    if (!p || !*p) return 0;
    unsigned char c = (unsigned char)*p;
    if (c < 0x80) return 1;
    if ((c & 0xE0) == 0xC0) return 2;
    if ((c & 0xF0) == 0xE0) return 3;
    if ((c & 0xF8) == 0xF0) return 4;
    return 1;
}

static bool isEmojiCodepoint(u32 cp) {
    return
        (cp >= 0x1F300 && cp <= 0x1FAFF) ||
        (cp >= 0x2600 && cp <= 0x27BF) ||
        cp == 0x2764 || cp == 0xFE0F;
}

/*
 * Small built-in emoji renderer.
 *
 * The 3DS system font does parse UTF-8, but its glyph sheets do not contain
 * modern emoji.  Instead of relying on a missing system glyph, draw a
 * deliberately small set of common emoji directly with citro2d primitives.
 *
 * This is intentionally self-contained: no NAND font, external font, PNG,
 * texture atlas, or SD asset is required.
 */
static bool drawEmojiGlyph(u32 cp, float x, float y, float z, float scale) {
    const float sz = 28.0f * scale;
    const float cx = x + sz * 0.50f;
    const float cy = y + sz * 0.50f;
    const float r = sz * 0.43f;

    u32 yellow = C2D_Color32(255, 204, 0, 255);
    u32 yellow2 = C2D_Color32(255, 221, 60, 255);
    u32 white = C2D_Color32(255, 255, 255, 255);
    u32 black = C2D_Color32(25, 25, 25, 255);
    u32 red = C2D_Color32(235, 50, 65, 255);
    u32 orange = C2D_Color32(255, 145, 25, 255);
    u32 blue = C2D_Color32(65, 145, 235, 255);
    u32 green = C2D_Color32(55, 190, 95, 255);
    u32 brown = C2D_Color32(120, 75, 40, 255);
    u32 pink = C2D_Color32(255, 125, 170, 255);

    switch (cp) {
        // 😀 😃 😄 😁 😆 😅
        case 0x1F600: case 0x1F603: case 0x1F604:
        case 0x1F601: case 0x1F606: case 0x1F605:
            C2D_DrawCircleSolid(cx, cy, z, r, yellow);
            C2D_DrawCircleSolid(cx - sz*.15f, cy - sz*.08f, z+.01f, sz*.045f, black);
            C2D_DrawCircleSolid(cx + sz*.15f, cy - sz*.08f, z+.01f, sz*.045f, black);
            if (cp == 0x1F605) {
                C2D_DrawEllipseSolid(x+sz*.31f, y+sz*.61f, z+.01f, sz*.38f, sz*.12f, black);
            } else {
                C2D_DrawEllipseSolid(x+sz*.31f, y+sz*.59f, z+.01f, sz*.38f, sz*.17f, black);
            }
            return true;

        // 😂
        case 0x1F602:
            C2D_DrawCircleSolid(cx, cy, z, r, yellow);
            C2D_DrawCircleSolid(cx - sz*.15f, cy - sz*.08f, z+.01f, sz*.05f, black);
            C2D_DrawCircleSolid(cx + sz*.15f, cy - sz*.08f, z+.01f, sz*.05f, black);
            C2D_DrawEllipseSolid(x+sz*.29f, y+sz*.56f, z+.01f, sz*.42f, sz*.20f, black);
            C2D_DrawCircleSolid(cx - sz*.36f, cy + sz*.04f, z+.01f, sz*.055f, blue);
            C2D_DrawCircleSolid(cx + sz*.36f, cy + sz*.04f, z+.01f, sz*.055f, blue);
            return true;

        // 🤣
        case 0x1F923:
            C2D_DrawCircleSolid(cx, cy, z, r, yellow);
            C2D_DrawEllipseSolid(x+sz*.28f, y+sz*.56f, z+.01f, sz*.44f, sz*.20f, black);
            C2D_DrawLine(x+sz*.28f, y+sz*.39f, black, x+sz*.42f, y+sz*.48f, black, sz*.035f, z+.01f);
            C2D_DrawLine(x+sz*.72f, y+sz*.39f, black, x+sz*.58f, y+sz*.48f, black, sz*.035f, z+.01f);
            return true;

        // 😊
        case 0x1F60A:
            C2D_DrawCircleSolid(cx, cy, z, r, yellow2);
            C2D_DrawCircleSolid(cx - sz*.15f, cy - sz*.07f, z+.01f, sz*.04f, black);
            C2D_DrawCircleSolid(cx + sz*.15f, cy - sz*.07f, z+.01f, sz*.04f, black);
            C2D_DrawEllipseSolid(x+sz*.35f, y+sz*.56f, z+.01f, sz*.30f, sz*.12f, red);
            return true;

        // 😍
        case 0x1F60D:
            C2D_DrawCircleSolid(cx, cy, z, r, yellow);
            C2D_DrawCircleSolid(cx - sz*.17f, cy - sz*.08f, z+.01f, sz*.07f, red);
            C2D_DrawCircleSolid(cx + sz*.17f, cy - sz*.08f, z+.01f, sz*.07f, red);
            C2D_DrawLine(x+sz*.12f, y+sz*.25f, red, x+sz*.22f, y+sz*.18f, red, sz*.025f, z+.01f);
            C2D_DrawLine(x+sz*.22f, y+sz*.18f, red, x+sz*.31f, y+sz*.25f, red, sz*.025f, z+.01f);
            C2D_DrawLine(x+sz*.69f, y+sz*.25f, red, x+sz*.78f, y+sz*.18f, red, sz*.025f, z+.01f);
            C2D_DrawLine(x+sz*.78f, y+sz*.18f, red, x+sz*.88f, y+sz*.25f, red, sz*.025f, z+.01f);
            return true;

        // 😎
        case 0x1F60E:
            C2D_DrawCircleSolid(cx, cy, z, r, yellow);
            C2D_DrawRectSolid(x+sz*.16f, y+sz*.29f, z+.01f, sz*.28f, sz*.15f, black);
            C2D_DrawRectSolid(x+sz*.56f, y+sz*.29f, z+.01f, sz*.28f, sz*.15f, black);
            C2D_DrawLine(x+sz*.44f, y+sz*.35f, black, x+sz*.56f, y+sz*.35f, black, sz*.035f, z+.01f);
            C2D_DrawEllipseSolid(x+sz*.34f, y+sz*.60f, z+.01f, sz*.32f, sz*.12f, black);
            return true;

        // 😢 😭
        case 0x1F622: case 0x1F62D:
            C2D_DrawCircleSolid(cx, cy, z, r, yellow);
            C2D_DrawCircleSolid(cx - sz*.15f, cy - sz*.08f, z+.01f, sz*.045f, black);
            C2D_DrawCircleSolid(cx + sz*.15f, cy - sz*.08f, z+.01f, sz*.045f, black);
            C2D_DrawEllipseSolid(x+sz*.37f, y+sz*.57f, z+.01f, sz*.26f, sz*.10f, black);
            C2D_DrawEllipseSolid(x+sz*.21f, y+sz*.49f, z+.02f, sz*.09f, cp == 0x1F62D ? sz*.22f : sz*.14f, blue);
            C2D_DrawEllipseSolid(x+sz*.70f, y+sz*.49f, z+.02f, sz*.09f, cp == 0x1F62D ? sz*.22f : sz*.14f, blue);
            return true;

        // 😡 😠
        case 0x1F621: case 0x1F620:
            C2D_DrawCircleSolid(cx, cy, z, r, red);
            C2D_DrawLine(x+sz*.18f, y+sz*.29f, black, x+sz*.38f, y+sz*.36f, black, sz*.035f, z+.01f);
            C2D_DrawLine(x+sz*.62f, y+sz*.36f, black, x+sz*.82f, y+sz*.29f, black, sz*.035f, z+.01f);
            C2D_DrawEllipseSolid(x+sz*.34f, y+sz*.61f, z+.01f, sz*.32f, sz*.09f, black);
            return true;

        // 🤔
        case 0x1F914:
            C2D_DrawCircleSolid(cx, cy, z, r, yellow);
            C2D_DrawCircleSolid(cx - sz*.15f, cy - sz*.08f, z+.01f, sz*.04f, black);
            C2D_DrawCircleSolid(cx + sz*.15f, cy - sz*.08f, z+.01f, sz*.04f, black);
            C2D_DrawEllipseSolid(x+sz*.38f, y+sz*.56f, z+.01f, sz*.25f, sz*.09f, black);
            C2D_DrawLine(x+sz*.27f, y+sz*.73f, brown, x+sz*.20f, y+sz*.92f, brown, sz*.07f, z+.01f);
            C2D_DrawLine(x+sz*.20f, y+sz*.92f, brown, x+sz*.40f, y+sz*.95f, brown, sz*.07f, z+.01f);
            return true;

        // 👍 👎
        case 0x1F44D:
            C2D_DrawEllipseSolid(x+sz*.34f, y+sz*.13f, z, sz*.30f, sz*.70f, yellow2);
            C2D_DrawEllipseSolid(x+sz*.16f, y+sz*.48f, z+.01f, sz*.55f, sz*.27f, yellow2);
            C2D_DrawRectSolid(x+sz*.43f, y+sz*.52f, z+.02f, sz*.32f, sz*.23f, yellow2);
            return true;
        case 0x1F44E:
            C2D_DrawEllipseSolid(x+sz*.34f, y+sz*.28f, z, sz*.30f, sz*.65f, yellow2);
            C2D_DrawEllipseSolid(x+sz*.17f, y+sz*.22f, z+.01f, sz*.54f, sz*.28f, yellow2);
            return true;

        // ❤️
        case 0x2764:
            C2D_DrawCircleSolid(x+sz*.35f, y+sz*.40f, z, sz*.20f, red);
            C2D_DrawCircleSolid(x+sz*.65f, y+sz*.40f, z, sz*.20f, red);
            C2D_DrawTriangle(x+sz*.10f, y+sz*.45f, red,
                             x+sz*.90f, y+sz*.45f, red,
                             x+sz*.50f, y+sz*.94f, red, z);
            return true;

        // 🔥
        case 0x1F525:
            C2D_DrawTriangle(x+sz*.50f, y+sz*.04f, orange,
                             x+sz*.86f, y+sz*.55f, red,
                             x+sz*.50f, y+sz*.92f, red, z);
            C2D_DrawTriangle(x+sz*.50f, y+sz*.28f, yellow,
                             x+sz*.70f, y+sz*.63f, yellow,
                             x+sz*.47f, y+sz*.82f, yellow, z+.01f);
            return true;

        // 🎉
        case 0x1F389:
            C2D_DrawEllipseSolid(x+sz*.30f, y+sz*.28f, z, sz*.40f, sz*.45f, blue);
            C2D_DrawTriangle(x+sz*.15f, y+sz*.75f, red,
                             x+sz*.82f, y+sz*.20f, yellow,
                             x+sz*.45f, y+sz*.45f, green, z+.01f);
            C2D_DrawCircleSolid(x+sz*.78f, y+sz*.76f, z+.02f, sz*.08f, yellow);
            return true;

        // 💀
        case 0x1F480:
            C2D_DrawCircleSolid(cx, cy-sz*.02f, z, r*.88f, white);
            C2D_DrawRectSolid(x+sz*.28f, y+sz*.62f, z+.01f, sz*.44f, sz*.25f, white);
            C2D_DrawCircleSolid(x+sz*.36f, y+sz*.42f, z+.02f, sz*.10f, black);
            C2D_DrawCircleSolid(x+sz*.64f, y+sz*.42f, z+.02f, sz*.10f, black);
            C2D_DrawTriangle(x+sz*.46f, y+sz*.55f, black,
                             x+sz*.54f, y+sz*.55f, black,
                             x+sz*.50f, y+sz*.68f, black, z+.02f);
            return true;

        // 💩
        case 0x1F4A9:
            C2D_DrawEllipseSolid(x+sz*.23f, y+sz*.33f, z, sz*.54f, sz*.55f, brown);
            C2D_DrawEllipseSolid(x+sz*.32f, y+sz*.20f, z+.01f, sz*.36f, sz*.34f, brown);
            C2D_DrawCircleSolid(x+sz*.39f, y+sz*.45f, z+.02f, sz*.04f, white);
            C2D_DrawCircleSolid(x+sz*.61f, y+sz*.45f, z+.02f, sz*.04f, white);
            return true;

        // 🚗
        case 0x1F697:
            C2D_DrawRectSolid(x+sz*.14f, y+sz*.45f, z, sz*.72f, sz*.28f, blue);
            C2D_DrawTriangle(x+sz*.25f, y+sz*.45f, blue,
                             x+sz*.38f, y+sz*.24f, blue,
                             x+sz*.64f, y+sz*.24f, blue, z);
            C2D_DrawCircleSolid(x+sz*.30f, y+sz*.76f, z+.01f, sz*.10f, black);
            C2D_DrawCircleSolid(x+sz*.70f, y+sz*.76f, z+.01f, sz*.10f, black);
            return true;

        default:
            return false;
    }
}

static bool emojiSequence(const char *p, u32 *cp, int *bytes) {
    if (!utf8Decode(p, cp)) return false;
    *bytes = emojiUtf8Len(p);
    // Ignore variation selectors and zero-width joiners when they follow a
    // supported base emoji. The base emoji is still rendered by our fallback.
    return isEmojiCodepoint(*cp) && *cp != 0xFE0F;
}

static void drawPlainTextSegment(const char *s, size_t len, float *x, float y, float z, float scale, u32 clr) {
    if (!len) return;
    char tmp[512];
    if (len >= sizeof(tmp)) len = sizeof(tmp) - 1;
    memcpy(tmp, s, len);
    tmp[len] = 0;

    C2D_Text t;
    C2D_TextParse(&t, textBuf, tmp);
    C2D_TextOptimize(&t);
    C2D_DrawText(&t, C2D_WithColor, *x, y, z, scale, scale, clr);

    float w = 0.0f;
    C2D_TextGetDimensions(&t, scale, scale, &w, NULL);
    *x += w;
}

static void drawText(const char *s, float x, float y, float z, float scale, u32 clr) {
    if (!s || !*s) return;

    const char *run = s;
    const char *p = s;

    while (*p) {
        u32 cp = 0;
        int bytes = 0;

        if (emojiSequence(p, &cp, &bytes)) {
            if (p > run)
                drawPlainTextSegment(run, (size_t)(p - run), &x, y, z, scale, clr);

            float emojiSize = 28.0f * scale;
            if (drawEmojiGlyph(cp, x, y - 1.0f * scale, z + 0.01f, scale))
                x += emojiSize + 1.0f * scale;
            else
                x += emojiSize;

            p += bytes;

            // Variation selector U+FE0F, skin-tone modifiers and ZWJ are
            // consumed here so they do not become stray missing-glyph boxes.
            while (*p) {
                u32 next = 0;
                int nb = emojiUtf8Len(p);
                if (!utf8Decode(p, &next)) break;
                if (next == 0xFE0F || next == 0x200D ||
                    (next >= 0x1F3FB && next <= 0x1F3FF)) {
                    p += nb;
                } else {
                    break;
                }
            }
            run = p;
        } else {
            p += (*p == '\n') ? 1 : emojiUtf8Len(p);
        }
    }

    if (p > run)
        drawPlainTextSegment(run, (size_t)(p - run), &x, y, z, scale, clr);
}

static void fmtCount(char *out, size_t n, int v) {
    if (v >= 1000) snprintf(out, n, "%d.%dk", v / 1000, (v % 1000) / 100);
    else snprintf(out, n, "%d", v);
}

static const char *utf8Next(const char *p) {
    if (!p || !*p) return p;
    unsigned char c = (unsigned char)*p;
    if (c < 0x80) return p + 1;
    if ((c & 0xE0) == 0xC0 && p[1]) return p + 2;
    if ((c & 0xF0) == 0xE0 && p[1] && p[2]) return p + 3;
    if ((c & 0xF8) == 0xF0 && p[1] && p[2] && p[3]) return p + 4;
    return p + 1;
}

static size_t utf8Count(const char *s) {
    size_t n = 0; while (s && *s) { s = utf8Next(s); n++; } return n;
}

static void truncated(char *out, size_t n, const char *s, size_t maxChars) {
    if (utf8Count(s) <= maxChars) { snprintf(out, n, "%s", s); return; }
    if (maxChars < 4 || n < 4) { if (n) out[0] = 0; return; }
    size_t keep = maxChars - 3, bytes = 0; const char *p = s;
    for (size_t i = 0; i < keep && *p; i++) { const char *q = utf8Next(p); bytes += (size_t)(q-p); p=q; }
    if (bytes + 4 > n) bytes = n - 4;
    memcpy(out, s, bytes); memcpy(out + bytes, "...", 4);
}

static void urlEncode(char *out, size_t n, const char *in) {
    static const char *hex = "0123456789ABCDEF";
    size_t o = 0;
    for (; *in && o + 4 < n; in++) {
        unsigned char c = (unsigned char)*in;
        if ((c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z') || (c >= '0' && c <= '9') || c == '-' || c == '_' || c == '.' || c == '~') {
            out[o++] = c;
        } else {
            out[o++] = '%'; out[o++] = hex[c >> 4]; out[o++] = hex[c & 15];
        }
    }
    out[o] = 0;
}

// Greedy word wrap into fixed lines (we wrap ourselves so heights are known).
static int wrapText(const char *s, int maxChars, char lines[][MAX_LINE], int maxLines) {
    if (maxChars > MAX_LINE - 1) maxChars = MAX_LINE - 1;
    int n = 0; const char *p = s;
    while (*p && n < maxLines) {
        while (*p == ' ') p++; if (!*p) break;
        const char *q = p, *lastSpace = NULL; int chars = 0;
        while (*q && chars < maxChars) { const char *next = utf8Next(q); if (*q == ' ') lastSpace = q; q = next; chars++; }
        const char *end = (q < p || (*q && lastSpace)) ? (lastSpace ? lastSpace : q) : q;
        size_t len = (size_t)(end-p); if (len >= MAX_LINE) len = MAX_LINE-1;
        memcpy(lines[n], p, len); lines[n][len] = 0; n++; p = end; while (*p == ' ') p++;
    }
    return n;
}

typedef struct { float x, y, w, h; const char *label; } Button;
static bool inButton(const Button *b, int tx, int ty) {
    return tx >= b->x && tx <= b->x + b->w && ty >= b->y && ty <= b->y + b->h;
}
static void drawButton(const Button *b, bool down, bool primary) {
    u32 fill = down ? cAccent : (primary ? C2D_Color32(110, 40, 12, 255) : cBtn);
    C2D_DrawRectSolid(b->x, b->y, 0.3f, b->w, b->h, fill);
    float tx = b->x + b->w / 2 - strlen(b->label) * 3.5f;
    drawText(b->label, tx, b->y + b->h / 2 - 9, 0.4f, 0.5f, cText);
}

// ----------------------------------------------------------- networking ----
// Plain HTTPS GET through the 3DS system HTTP service. Returns malloc'd buffer (NUL-terminated).
// NOTE: certificate verification is turned off (SSLCOPT_DisableVerify) because the 3DS's built-in
// certificate store is old and rejects many modern sites. This app only reads public, non-secret
// data from your own proxy, but be aware the connection is encrypted yet not authenticated.
static bool httpGet(const char *url, u8 **out, u32 *outSize, u32 maxSize) {
    char cur[2048];
    snprintf(cur, sizeof cur, "%s", url);

    for (int redirects = 0; redirects < 5; redirects++) {
        httpcContext ctx;
        Result rc = httpcOpenContext(&ctx, HTTPC_METHOD_GET, cur, 1);
        if (R_FAILED(rc)) { snprintf(lastErr, sizeof lastErr, "Can't open connection (%08lX)", (unsigned long)rc); return false; }
        httpcSetSSLOpt(&ctx, SSLCOPT_DisableVerify);
        httpcSetKeepAlive(&ctx, HTTPC_KEEPALIVE_ENABLED);
        httpcAddRequestHeaderField(&ctx, "User-Agent", "3ds-reddit-viewer/0.1");

        rc = httpcBeginRequest(&ctx);
        if (R_FAILED(rc)) {
            httpcCloseContext(&ctx);
            snprintf(lastErr, sizeof lastErr, "Request failed (%08lX). Is Wi-Fi on?", (unsigned long)rc);
            return false;
        }

        u32 status = 0;
        httpcGetResponseStatusCode(&ctx, &status);
        if (status >= 300 && status < 400) {
            char loc[1024];
            if (R_SUCCEEDED(httpcGetResponseHeader(&ctx, "Location", loc, sizeof loc))) {
                httpcCloseContext(&ctx);
                snprintf(cur, sizeof cur, "%s", loc);
                continue;
            }
        }
        if (status != 200) {
            httpcCloseContext(&ctx);
            snprintf(lastErr, sizeof lastErr, "Server returned HTTP %lu", (unsigned long)status);
            return false;
        }

        u32 cap = 0x8000, size = 0;
        u8 *buf = malloc(cap + 1);
        if (!buf) { httpcCloseContext(&ctx); snprintf(lastErr, sizeof lastErr, "Out of memory"); return false; }
        Result r;
        do {
            if (size + 0x4000 > cap) {
                cap *= 2;
                u8 *nb = realloc(buf, cap + 1);
                if (!nb) { free(buf); httpcCloseContext(&ctx); snprintf(lastErr, sizeof lastErr, "Out of memory"); return false; }
                buf = nb;
            }
            u32 got = 0;
            r = httpcDownloadData(&ctx, buf + size, 0x4000, &got);
            size += got;
            if (size > maxSize) { free(buf); httpcCloseContext(&ctx); snprintf(lastErr, sizeof lastErr, "Response too large"); return false; }
        } while (r == (Result)HTTPC_RESULTCODE_DOWNLOADPENDING);

        httpcCloseContext(&ctx);
        if (R_FAILED(r)) { free(buf); snprintf(lastErr, sizeof lastErr, "Download failed (%08lX)", (unsigned long)r); return false; }
        buf[size] = 0;
        *out = buf;
        *outSize = size;
        return true;
    }
    snprintf(lastErr, sizeof lastErr, "Too many redirects");
    return false;
}

static int splitTabs(char *s, char **f, int max) {
    int n = 0;
    f[n++] = s;
    for (; *s && n < max; s++) {
        if (*s == '\t') { *s = 0; f[n++] = s + 1; }
    }
    return n;
}

static void copyStr(char *dst, size_t n, const char *src) { snprintf(dst, n, "%s", src); }

// Checks the first line ("OK<TAB>..." or "ERR<TAB>message"); returns pointer to the rest.
static char *checkReply(char *buf) {
    char *nl = strchr(buf, '\n');
    if (nl) *nl = 0;
    if (strncmp(buf, "OK", 2) == 0) return nl ? nl + 1 : buf + strlen(buf);
    if (strncmp(buf, "ERR\t", 4) == 0) snprintf(lastErr, sizeof lastErr, "%s", buf + 4);
    else snprintf(lastErr, sizeof lastErr, "Unexpected reply from server");
    return NULL;
}

static void freePosts(void) {
    for (int i = 0; i < postCount; i++) { free(posts[i].key); posts[i].key = NULL; }
    postCount = 0;
}

static bool fetchPosts(void) {
    char subE[640], qE[160], url[1024];
    // Searches are global (all of Reddit, best matches first) and never limited to the current feed.
    urlEncode(subE, sizeof subE, query[0] ? "all" : subName);
    urlEncode(qE, sizeof qE, query);
    const char *sortName = query[0] ? "hot" : sorts[sortIdx];  // for searches the proxy turns this into "relevance"
    if (query[0]) snprintf(url, sizeof url, "%s/posts?sub=%s&sort=%s&q=%s", apiBase, subE, sortName, qE);
    else snprintf(url, sizeof url, "%s/posts?sub=%s&sort=%s&t=%s", apiBase, subE, sortName, tRanges[tIdx]);

    u8 *buf; u32 size;
    lastErr[0] = 0;
    if (!httpGet(url, &buf, &size, 400 * 1024)) return false;
    char *rest = checkReply((char *)buf);
    if (!rest) { free(buf); return false; }

    freePosts();
    char *line = rest;
    int maxShown = query[0] ? SEARCH_MAX_POSTS : MAX_POSTS;
    while (*line && postCount < maxShown) {
        char *nl = strchr(line, '\n');
        if (nl) *nl = 0;
        if (line[0] == 'P' && line[1] == '\t') {
            char *f[10];
            if (splitTabs(line, f, 10) == 10) {
                Post *p = &posts[postCount];
                copyStr(p->id, sizeof p->id, f[1]);
                copyStr(p->sub, sizeof p->sub, f[2]);
                copyStr(p->author, sizeof p->author, f[3]);
                p->score = atoi(f[4]);
                p->ncomments = atoi(f[5]);
                p->media = atoi(f[6]);
                p->key = f[7][0] ? strdup(f[7]) : NULL;
                if (!p->key) p->media = MEDIA_NONE;
                copyStr(p->title, sizeof p->title, f[8]);
                copyStr(p->body, sizeof p->body, f[9]);
                postCount++;
            }
        }
        if (!nl) break;
        line = nl + 1;
    }
    free(buf);
    if (postCount == 0) snprintf(lastErr, sizeof lastErr, query[0] ? "No posts matched your search." : "No posts returned.");
    return true;
}

static bool fetchComments(const Post *p) {
    char url[256];
    snprintf(url, sizeof url, "%s/post?id=%s", apiBase, p->id);
    cmCount = 0;
    u8 *buf; u32 size;
    if (!httpGet(url, &buf, &size, 200 * 1024)) return false;
    char *rest = checkReply((char *)buf);
    if (!rest) { free(buf); return false; }

    char *line = rest;
    while (*line && cmCount < MAX_COMMENTS) {
        char *nl = strchr(line, '\n');
        if (nl) *nl = 0;
        if (line[0] == 'C' && line[1] == '\t') {
            char *f[5];
            if (splitTabs(line, f, 5) == 5) {
                Comment *c = &cms[cmCount++];
                c->depth = atoi(f[1]);
                if (c->depth < 0) c->depth = 0;
                if (c->depth > 2) c->depth = 2;
                copyStr(c->author, sizeof c->author, f[2]);
                c->score = atoi(f[3]);
                copyStr(c->text, sizeof c->text, f[4]);
            }
        }
        if (!nl) break;
        line = nl + 1;
    }
    free(buf);
    return true;
}

// ----------------------------------------------------- images / textures ----
static int pow2(int v) { int p = 8; while (p < v) p <<= 1; return p; }

// PICA200 RGBA8 textures use the 3DS/tex3ds 8x8 tile swizzle.
// This is the same per-tile permutation used by devkitPro's tex3ds runtime format.
static void swizzleTileRGBA8(u32 *p) {
    static const u8 table[][4] = {
        { 2, 8, 16, 4 }, { 3, 9, 17, 5 },
        { 6, 10, 24, 20 }, { 7, 11, 25, 21 },
        { 14, 26, 28, 22 }, { 15, 27, 29, 23 },
        { 34, 40, 48, 36 }, { 35, 41, 49, 37 },
        { 38, 42, 56, 52 }, { 39, 43, 57, 53 },
        { 46, 58, 60, 54 }, { 47, 59, 61, 55 }
    };

    for (size_t i = 0; i < sizeof(table) / sizeof(table[0]); i++) {
        const u8 *e = table[i];
        u32 t = p[e[0]];
        p[e[0]] = p[e[1]];
        p[e[1]] = p[e[2]];
        p[e[2]] = p[e[3]];
        p[e[3]] = t;
    }
    u32 t = p[12]; p[12] = p[18]; p[18] = t;
    t = p[13]; p[13] = p[19]; p[19] = t;
    t = p[44]; p[44] = p[50]; p[50] = t;
    t = p[45]; p[45] = p[51]; p[51] = t;
}

static void imgFree(Img *im) {
    if (im->ok) { C3D_TexDelete(&im->tex); im->ok = false; }
}

// Decodes a JPEG and uploads it as a GPU texture. The image is stored with its top row at the
// top of the (power-of-two) texture; texture v=1 is the top row in citro3d's convention.
static bool imgFromJpeg(Img *im, const u8 *data, int len) {
    int w, h, n;
    u8 *px = stbi_load_from_memory(data, len, &w, &h, &n, 4);
    if (!px) return false;
    int tw = pow2(w), th = pow2(h);
    if (tw > 1024 || th > 1024 || !C3D_TexInit(&im->tex, tw, th, GPU_RGBA8)) {
        stbi_image_free(px);
        return false;
    }
    memset(im->tex.data, 0, (size_t)tw * th * 4);
    u32 *dst = (u32 *)im->tex.data;

    // Build each 8x8 tile in normal top-to-bottom image order, apply the exact
    // tex3ds swizzle, then copy the tile into the corresponding GPU tile.
    // Keeping the decoded rows unflipped avoids the previous double vertical
    // inversion between the CPU upload and C2D texture coordinates.
    u32 tile[64];
    for (int ty = 0; ty < th; ty += 8) {
        for (int tx = 0; tx < tw; tx += 8) {
            memset(tile, 0, sizeof(tile));
            for (int y = 0; y < 8; y++) {
                int sy = ty + y;
                if (sy >= h) continue;
                for (int x = 0; x < 8; x++) {
                    int sx = tx + x;
                    if (sx >= w) continue;
                    const u8 *sp = px + ((size_t)sy * w + sx) * 4;
                    tile[y * 8 + x] = ((u32)sp[0] << 24) | ((u32)sp[1] << 16) |
                                      ((u32)sp[2] << 8) | sp[3];
                }
            }
            swizzleTileRGBA8(tile);
            size_t tileIndex = (size_t)(ty / 8) * (tw / 8) + (tx / 8);
            memcpy(dst + tileIndex * 64, tile, sizeof(tile));
        }
    }
    stbi_image_free(px);
    C3D_TexFlush(&im->tex);
    C3D_TexSetFilter(&im->tex, GPU_LINEAR, GPU_LINEAR);
    C3D_TexSetWrap(&im->tex, GPU_CLAMP_TO_EDGE, GPU_CLAMP_TO_EDGE);

    im->w = w; im->h = h;
    im->sub.width = (u16)w;
    im->sub.height = (u16)h;
    im->sub.left = 0.0f;
    // C2D/tex3ds uses the top/bottom ordering to describe texture orientation.
    // Keep this as the normal, non-rotated orientation and let the decoded image
    // retain its natural top-to-bottom row order.
    im->sub.top = 1.0f;
    im->sub.right = (float)w / tw;
    im->sub.bottom = 1.0f - (float)h / th;
    im->img.tex = &im->tex;
    im->img.subtex = &im->sub;
    im->ok = true;
    return true;
}

static void drawImgFit(const Img *im, float x, float y, float w, float h, float z) {
    float s = fminf(w / im->w, h / im->h);
    float dw = im->w * s, dh = im->h * s;
    float dx = x + (w - dw) / 2.0f;
    float dy = y + (h - dh) / 2.0f;

    // The fit calculation normally keeps the image inside the slot, but use the
    // GPU scissor as a hard boundary so filtering/rounding can never leak pixels
    // outside the frame.
    u32 left = (u32)fmaxf(0.0f, floorf(x));
    u32 top = (u32)fmaxf(0.0f, floorf(y));
    u32 right = (u32)fminf(400.0f, ceilf(x + w));
    u32 bottom = (u32)fminf(240.0f, ceilf(y + h));
    C3D_SetScissor(GPU_SCISSOR_NORMAL, left, top, right, bottom);
    C2D_DrawImageAt(im->img, dx, dy, z, NULL, s, s);
    C3D_SetScissor(GPU_SCISSOR_DISABLE, 0, 0, 0, 0);
}

static void freeMedia(void) {
    imgFree(&photo);
    for (int i = 0; i < GIF_MAX; i++) imgFree(&gif[i]);
    gifLoaded = gifTotal = 0;
    mediaState = MS_NONE;
}

// Does ONE blocking step of media loading, so the UI can redraw (and B can cancel) between steps.
static void mediaStep(const Post *p) {
    char url[2048];
    u8 *buf = NULL; u32 size = 0;

    if (mediaState == MS_PHOTO) {
        snprintf(url, sizeof url, "%s/img?u=%s&w=%d&h=%d", apiBase, p->key, PHOTO_W, PHOTO_H);
        if (httpGet(url, &buf, &size, 400 * 1024) && imgFromJpeg(&photo, buf, (int)size)) mediaState = MS_DONE;
        else mediaState = MS_FAILED;
        free(buf);
    } else if (mediaState == MS_GIFINFO) {
        snprintf(url, sizeof url, "%s/gif?u=%s", apiBase, p->key);
        if (httpGet(url, &buf, &size, 4096)) {
            char *rest = checkReply((char *)buf);
            if (rest) {
                // first line was cut at newline by checkReply: it is "OK\t<frames>\t<delay>" -> re-parse
                int frames = 1, delay = 100;
                const char *t1 = strchr((char *)buf, '\t');
                if (t1) {
                    frames = atoi(t1 + 1);
                    const char *t2 = strchr(t1 + 1, '\t');
                    if (t2) delay = atoi(t2 + 1);
                }
                if (frames < 1) frames = 1;
                gifSrcFrames = frames;
                gifTotal = frames < GIF_MAX ? frames : GIF_MAX;
                gifDelayMs = delay;
                if (frames > GIF_MAX) gifDelayMs = delay * frames / GIF_MAX;  // we skip frames, so stretch time
                if (gifDelayMs < 80) gifDelayMs = 80;
                if (gifDelayMs > 300) gifDelayMs = 300;
                gifLoaded = 0;
                mediaState = (frames <= 1) ? MS_PHOTO : MS_GIFFRAMES;
            } else mediaState = MS_FAILED;
        } else mediaState = MS_FAILED;
        free(buf);
    } else if (mediaState == MS_GIFFRAMES) {
        int page = gifTotal > 1 ? gifLoaded * gifSrcFrames / gifTotal : 0;
        snprintf(url, sizeof url, "%s/frame?u=%s&p=%d&w=%d&h=%d", apiBase, p->key, page, GIF_W, GIF_H);
        if (httpGet(url, &buf, &size, 300 * 1024) && imgFromJpeg(&gif[gifLoaded], buf, (int)size)) {
            gifLoaded++;
            if (gifLoaded >= gifTotal) mediaState = MS_DONE;
        } else {
            // keep whatever frames we have; if none, fail
            mediaState = gifLoaded > 0 ? MS_DONE : MS_FAILED;
        }
        free(buf);
    }
}

// ------------------------------------------------------------ rendering ----
static void loadingFrame(const char *msg) {
    C2D_TextBufClear(textBuf);
    C3D_FrameBegin(C3D_FRAME_SYNCDRAW);
    C2D_TargetClear(topT, cBg);
    C2D_SceneBegin(topT);
    drawText(msg, 150, 110, 0.5f, 0.6f, cText);
    C2D_TargetClear(botT, cBg);
    C2D_SceneBegin(botT);
    C3D_FrameEnd(0);
}

static void drawMediaSlot(float x, float y, float w, float h, const Post *p) {
    C2D_DrawRectSolid(x, y, 0.2f, w, h, cCard);
    bool isGif = p->media == MEDIA_GIF && gifTotal > 1;
    if (mediaState == MS_DONE && !isGif && photo.ok) {
        drawImgFit(&photo, x, y, w, h, 0.25f);
    } else if (isGif && gifLoaded > 0) {
        int f = (mediaState == MS_DONE) ? (int)((osGetTime() / (u64)gifDelayMs) % (u64)gifLoaded) : 0;
        drawImgFit(&gif[f], x, y, w, h, 0.25f);
    } else if (mediaState == MS_FAILED) {
        drawText("image unavailable", x + 40, y + h / 2 - 8, 0.3f, 0.45f, cDim);
    } else {
        drawText("loading image...", x + 44, y + h / 2 - 8, 0.3f, 0.45f, cDim);
    }

    char badge[24];
    if (p->media == MEDIA_GIF && mediaState == MS_GIFFRAMES) snprintf(badge, sizeof badge, "GIF %d/%d", gifLoaded, gifTotal);
    else snprintf(badge, sizeof badge, "%s", p->media == MEDIA_GIF ? "GIF" : "PHOTO");
    C2D_DrawRectSolid(x + 6, y + 6, 0.3f, 8 + strlen(badge) * 6, 16, C2D_Color32(0, 0, 0, 170));
    drawText(badge, x + 10, y + 5, 0.4f, 0.4f, cText);
}

// ---- LIST view
static const Button bPrev   = {10, 150, 96, 34, "Prev"};
static const Button bNext   = {112, 150, 96, 34, "Next"};
static const Button bOpen   = {214, 150, 96, 34, "Open"};
static const Button bSearch = {10, 192, 96, 38, "Search"};
static const Button bSub    = {112, 192, 96, 38, "Subreddit"};
static const Button bSort   = {214, 192, 96, 38, "Sort"};
static const Button bRefresh = {6, 2, 66, 18, "Refresh"};
static const Button bHome   = {244, 2, 66, 18, "Home"};  // sits in the bottom screen's header strip
static const Button bFeed   = {172, 2, 66, 18, "< Feed"}; // only shown while viewing search results

static void renderListTop(float scroll, int sel) {
    C2D_TargetClear(topT, cBg);
    C2D_SceneBegin(topT);

    for (int k = 0; k < postCount; k++) {
        const Post *p = &posts[k];
        float y = LIST_TOP + k * CARD_PITCH - scroll;
        if (y > 240.0f || y + CARD_H < LIST_TOP) continue;
        bool isSel = (k == sel);

        C2D_DrawRectSolid(8, y, 0.1f, 384, CARD_H, isSel ? cCardSel : cCard);
        if (isSel) C2D_DrawRectSolid(8, y, 0.2f, 4, CARD_H, cAccent);

        char sc[16];
        fmtCount(sc, sizeof sc, p->score);
        drawText("^", 20, y + 4, 0.3f, 0.5f, isSel ? cAccent : cDim);
        drawText(sc, 18, y + 18, 0.3f, 0.5f, cText);

        char title[64];
        truncated(title, sizeof title, p->title, 38);
        drawText(title, 62, y + 5, 0.3f, 0.5f, cText);

        char meta[96], cm[16], line3[32];
        snprintf(meta, sizeof meta, "%s  u/%s", p->sub, p->author);
        drawText(meta, 62, y + 22, 0.3f, 0.42f, cDim);
        fmtCount(cm, sizeof cm, p->ncomments);
        snprintf(line3, sizeof line3, "%s comments", cm);
        drawText(line3, 62, y + 35, 0.3f, 0.42f, cDim);

        if (p->media != MEDIA_NONE) {
            C2D_DrawRectSolid(350, y + 8, 0.3f, 34, 16, p->media == MEDIA_GIF ? cAccent : C2D_Color32(70, 110, 190, 255));
            drawText(p->media == MEDIA_GIF ? "GIF" : "IMG", 355, y + 7, 0.4f, 0.4f, cText);
        }
    }

    if (postCount == 0) {
        drawText(lastErr[0] ? "Couldn't load posts" : "Nothing to show", 120, 100, 0.3f, 0.55f, cDim);
    }

    C2D_DrawRectSolid(0, 0, 0.5f, 400, 26, cHeader);
    C2D_DrawRectSolid(0, 26, 0.5f, 400, 2, cAccent);
    drawText("3DS Reddit", 10, 4, 0.6f, 0.6f, cText);
    char h[96], q[40];
    if (query[0]) {
        truncated(q, sizeof q, query, 18);
        snprintf(h, sizeof h, "all Reddit: %s (%d)", q, postCount);
        drawText(h, 170, 8, 0.6f, 0.45f, cAccent);
    } else {
        char st[24];
        sortText(st, sizeof st);
        if (isHome) {
            char lab[48];
            truncated(lab, sizeof lab, homeLabel, 20);
            snprintf(h, sizeof h, "Home: %s - %s", lab, st);
        } else {
            snprintf(h, sizeof h, "r/%s - %s", subName, st);
        }
        drawText(h, 400 - 14 - strlen(h) * 6.2f, 8, 0.6f, 0.45f, cDim);
    }
}

static void renderListBottom(int sel, int held) {
    C2D_TargetClear(botT, cBg);
    C2D_SceneBegin(botT);

    C2D_DrawRectSolid(0, 0, 0.1f, 320, 22, cHeader);
    C2D_DrawRectSolid(0, 22, 0.1f, 320, 2, cAccent);

    char lines[4][MAX_LINE];
    if (postCount > 0) {
        const Post *p = &posts[sel];
        drawText(p->sub, 10, 3, 0.2f, 0.5f, cAccent);
        if (lastErr[0] && !query[0]) {  // e.g. a failed reload: the old list stays, the error shows in the header
            char e[40];
            truncated(e, sizeof e, lastErr, 22);
            drawText(e, 112, 6, 0.2f, 0.4f, C2D_Color32(255, 120, 90, 255));
        }

        int n = wrapText(p->title, 40, lines, 3);
        for (int i = 0; i < n; i++) drawText(lines[i], 12, 30 + i * 15, 0.3f, 0.5f, cText);

        char sc[16], cm[16], meta[96];
        fmtCount(sc, sizeof sc, p->score);
        fmtCount(cm, sizeof cm, p->ncomments);
        snprintf(meta, sizeof meta, "u/%s   %s pts   %s comments", p->author, sc, cm);
        drawText(meta, 12, 78, 0.3f, 0.42f, cDim);

        if (p->media != MEDIA_NONE)
            drawText(p->media == MEDIA_GIF ? "[ animated GIF ]" : "[ photo ]", 12, 94, 0.3f, 0.42f, cAccent);
        char pos[40];
        snprintf(pos, sizeof pos, "%d/%d   L/R: %d pages", sel + 1, postCount, PAGES_PER_JUMP);
        drawText(pos, 190, 94, 0.3f, 0.4f, cDim);

        n = wrapText(p->body, 46, lines, 3);
        for (int i = 0; i < n; i++) drawText(lines[i], 12, 108 + i * 12, 0.3f, 0.45f, cText);
    } else {
        drawText("Reddit", 10, 3, 0.2f, 0.5f, cAccent);
        int n = wrapText(lastErr[0] ? lastErr : "Nothing here yet.", 44, lines, 4);
        for (int i = 0; i < n; i++) drawText(lines[i], 12, 34 + i * 14, 0.3f, 0.45f, cText);
    }

    drawButton(&bPrev, held == 1, false);
    drawButton(&bNext, held == 2, false);
    drawButton(&bOpen, held == 3, true);
    drawButton(&bSearch, held == 4, false);
    drawButton(&bSub, held == 5, false);
    char sortLabel[24];
    bool topMode = (sortIdx == SORT_TOP && !query[0]);
    if (query[0]) snprintf(sortLabel, sizeof sortLabel, "Sort: best");
    else if (topMode) snprintf(sortLabel, sizeof sortLabel, "Top: %s", tRanges[tIdx]);
    else snprintf(sortLabel, sizeof sortLabel, "Sort: %s", sorts[sortIdx]);
    Button sb = bSort; sb.label = sortLabel;
    if (topMode) {
        // two-line button: the current range plus a reminder of the shortcut keys
        C2D_DrawRectSolid(sb.x, sb.y, 0.3f, sb.w, sb.h, held == 6 ? cAccent : cBtn);
        drawText(sortLabel, sb.x + sb.w / 2 - strlen(sortLabel) * 3.5f, sb.y + 3, 0.4f, 0.5f, cText);
        drawText("SELECT / START", sb.x + 11, sb.y + 21, 0.4f, 0.36f, cAccent);
    } else {
        drawButton(&sb, held == 6, false);
    }
    drawButton(&bRefresh, held == 7, false);
    drawButton(&bHome, held == 8, isHome && !query[0]);
    if (query[0]) drawButton(&bFeed, held == 9, true);
}

// ---- POST view
static const Button bBack = {10, 208, 120, 28, "Back"};
#define CM_TOP 26.0f
#define CM_BOTTOM 204.0f

static int commentLines(int i, char lines[][MAX_LINE], int maxLines) {
    return wrapText(cms[i].text, 44 - cms[i].depth * 3, lines, maxLines);
}

static float commentsTotalHeight(void) {
    char lines[10][MAX_LINE];
    float h = 0;
    for (int i = 0; i < cmCount; i++) h += 16 + commentLines(i, lines, 10) * 12 + 8;
    return h;
}

static void renderPostTop(const Post *p) {
    C2D_TargetClear(topT, cBg);
    C2D_SceneBegin(topT);

    C2D_DrawRectSolid(0, 0, 0.5f, 400, 26, cHeader);
    C2D_DrawRectSolid(0, 26, 0.5f, 400, 2, cAccent);
    drawText(p->sub, 10, 4, 0.6f, 0.6f, cAccent);
    drawText("B: back", 340, 8, 0.6f, 0.45f, cDim);

    float textX = 12;
    bool hasMedia = p->media != MEDIA_NONE;
    if (hasMedia) {
        drawMediaSlot(10, 36, 180, 135, p);
        textX = 202;
    }

    char lines[6][MAX_LINE];
    int n = wrapText(p->title, hasMedia ? 26 : 56, lines, 6);
    for (int i = 0; i < n; i++) drawText(lines[i], textX, 36 + i * 16, 0.3f, 0.55f, cText);

    char sc[16], cm[16], meta[96];
    fmtCount(sc, sizeof sc, p->score);
    fmtCount(cm, sizeof cm, p->ncomments);
    snprintf(meta, sizeof meta, "u/%s", p->author);
    drawText(meta, textX, 36 + n * 16 + 4, 0.3f, 0.45f, cDim);
    snprintf(meta, sizeof meta, "%s pts  %s comments", sc, cm);
    drawText(meta, textX, 36 + n * 16 + 20, 0.3f, 0.45f, cDim);

    float bodyY = hasMedia ? 182.0f : 36.0f + (float)(wrapText(p->title, 56, lines, 6)) * 16 + 42;
    n = wrapText(p->body, 58, lines, 3);
    for (int i = 0; i < n; i++) drawText(lines[i], 12, bodyY + i * 13, 0.3f, 0.45f, cText);
}

static void renderPostBottom(float scroll, bool backHeld) {
    C2D_TargetClear(botT, cBg);
    C2D_SceneBegin(botT);

    float y = CM_TOP - scroll;
    char lines[10][MAX_LINE];
    for (int i = 0; i < cmCount; i++) {
        int n = commentLines(i, lines, 10);
        float h = 16 + n * 12 + 8;
        if (y + h >= CM_TOP && y <= CM_BOTTOM) {
            float x = 14 + cms[i].depth * 14;
            C2D_DrawRectSolid(x - 5, y + 2, 0.1f, 2, h - 6, cms[i].depth ? cDim : cAccent);
            char head[64], sc[16];
            fmtCount(sc, sizeof sc, cms[i].score);
            snprintf(head, sizeof head, "u/%s  %s pts", cms[i].author, sc);
            drawText(head, x, y, 0.2f, 0.4f, cDim);
            for (int j = 0; j < n; j++) drawText(lines[j], x, y + 14 + j * 12, 0.2f, 0.45f, cText);
        }
        y += h;
    }
    if (cmCount == 0) drawText(lastErr[0] ? lastErr : "No comments yet.", 14, 40, 0.2f, 0.45f, cDim);

    // Opaque bars on top hide comments scrolling past the edges (z above comments, below buttons)
    C2D_DrawRectSolid(0, 0, 0.25f, 320, 24, cHeader);
    C2D_DrawRectSolid(0, 22, 0.26f, 320, 2, cAccent);
    drawText("Comments", 10, 3, 0.6f, 0.5f, cText);
    C2D_DrawRectSolid(0, CM_BOTTOM, 0.25f, 320, 240 - CM_BOTTOM, cBg);
    drawButton(&bBack, backHeld, false);
    drawText("drag or D-pad to scroll", 150, 214, 0.6f, 0.4f, cDim);
}

// ------------------------------------------------------------ user input ---
static bool askText(const char *hint, const char *initial, char *out, size_t outSize, int maxLen) {
    SwkbdState swkbd;
    swkbdInit(&swkbd, SWKBD_TYPE_NORMAL, 2, maxLen);
    swkbdSetHintText(&swkbd, hint);
    swkbdSetButton(&swkbd, SWKBD_BUTTON_LEFT, "Cancel", false);
    swkbdSetButton(&swkbd, SWKBD_BUTTON_RIGHT, "OK", true);
    if (initial && initial[0]) swkbdSetInitialText(&swkbd, initial);
    char buf[128] = "";
    if (swkbdInputText(&swkbd, buf, sizeof buf) != SWKBD_BUTTON_RIGHT) return false;
    snprintf(out, outSize, "%s", buf);
    return true;
}

// Built-in proxy address. On first launch it is also written to server.txt on the SD card, so
// anyone can change the server later just by editing that file (a present file wins over this).
#define DEFAULT_API "https://delicate-fire-c4d0.rhubix74.workers.dev/api"
#define CONFIG_DIR "sdmc:/3ds/redditviewer"
#define CONFIG_PATH "sdmc:/3ds/redditviewer/server.txt"

static bool pathExists(const char *path) {
    struct stat st;
    return stat(path, &st) == 0;
}

// Never touches anything that already exists: folders are only created when missing, and
// server.txt is only written when it is definitely absent (never overwritten or truncated).
static void createDefaultConfig(void) {
    if (!pathExists("sdmc:/3ds")) mkdir("sdmc:/3ds", 0777);
    if (!pathExists(CONFIG_DIR)) mkdir(CONFIG_DIR, 0777);
    if (pathExists(CONFIG_PATH)) return;
    FILE *f = fopen(CONFIG_PATH, "w");
    if (f) { fprintf(f, "%s\n", DEFAULT_API); fclose(f); }
}

static void loadConfig(void) {
    snprintf(apiBase, sizeof apiBase, "%s", DEFAULT_API);
    FILE *f = fopen(CONFIG_PATH, "r");
    if (!f) {
        createDefaultConfig();  // first boot; does nothing if the file exists but couldn't be read
        return;
    }
    char buf[256] = "";
    if (fgets(buf, sizeof buf, f)) {
        size_t n = strlen(buf);
        while (n && (buf[n - 1] == '\n' || buf[n - 1] == '\r' || buf[n - 1] == ' ')) buf[--n] = 0;
        while (n && buf[n - 1] == '/') buf[--n] = 0;
        if (strncmp(buf, "http", 4) == 0) snprintf(apiBase, sizeof apiBase, "%s", buf);
    }
    fclose(f);
}

static bool configured(void) { return strstr(apiBase, "YOUR-PROJECT") == NULL; }

// ------------------------------------------------------- adaptive Home feed ----
// Home learns from what you open. Every time you open a post, its subreddit gets +1 in
// history.txt (inside this app's own redditviewer folder). Home then shows one combined feed of
// your most-opened subreddits ("r/a+b+c"), so it drifts toward what you actually read.
// Old interests fade (counts are halved once the totals get large). Delete history.txt to reset.
#define HIST_PATH CONFIG_DIR "/history.txt"
#define MAX_HIST 40
#define HOME_MAX_SUBS 6
#define HOME_MIN_SUBS 3      // until you've opened posts from this many subreddits, Home is r/all
#define HOME_MAX_CHARS 58    // keeps the combined name inside the proxy's 60-character limit

typedef struct { char name[32]; int count, seq; } Interest;
static Interest hist[MAX_HIST];
static int histCount = 0, histSeq = 0;

static bool validSubName(const char *s) {
    size_t n = strlen(s);
    if (n < 2 || n > 24) return false;
    for (; *s; s++) if (!isalnum((unsigned char)*s) && *s != '_') return false;
    return true;
}

static void saveHistory(void) {
    if (!pathExists(CONFIG_DIR)) return;  // only ever writes inside our own folder
    FILE *f = fopen(HIST_PATH, "w");
    if (!f) return;
    for (int i = 0; i < histCount; i++) fprintf(f, "%s\t%d\t%d\n", hist[i].name, hist[i].count, hist[i].seq);
    fclose(f);
}

static void loadHistory(void) {
    FILE *f = fopen(HIST_PATH, "r");
    if (!f) return;
    char line[128];
    while (fgets(line, sizeof line, f) && histCount < MAX_HIST) {
        char *t1 = strchr(line, '\t');
        if (!t1) continue;
        *t1 = 0;
        char *t2 = strchr(t1 + 1, '\t');
        int count = atoi(t1 + 1), seq = t2 ? atoi(t2 + 1) : 0;
        if (!validSubName(line) || count < 1) continue;
        for (char *c = line; *c; c++) *c = (char)tolower((unsigned char)*c);
        Interest *it = &hist[histCount++];
        snprintf(it->name, sizeof it->name, "%s", line);
        it->count = count;
        it->seq = seq;
        if (seq > histSeq) histSeq = seq;
    }
    fclose(f);
}

static void recordView(const char *prefixedSub) {
    if (strncmp(prefixedSub, "r/", 2) != 0) return;
    char name[32];
    snprintf(name, sizeof name, "%s", prefixedSub + 2);
    if (!validSubName(name)) return;
    for (char *c = name; *c; c++) *c = (char)tolower((unsigned char)*c);

    int idx = -1;
    for (int i = 0; i < histCount; i++) if (strcmp(hist[i].name, name) == 0) { idx = i; break; }
    if (idx < 0) {
        if (histCount < MAX_HIST) {
            idx = histCount++;
        } else {  // full: replace the least-opened entry (oldest on ties)
            idx = 0;
            for (int i = 1; i < MAX_HIST; i++)
                if (hist[i].count < hist[idx].count ||
                    (hist[i].count == hist[idx].count && hist[i].seq < hist[idx].seq)) idx = i;
        }
        snprintf(hist[idx].name, sizeof hist[idx].name, "%s", name);
        hist[idx].count = 0;
    }
    hist[idx].count++;
    hist[idx].seq = ++histSeq;

    int total = 0;
    for (int i = 0; i < histCount; i++) total += hist[i].count;
    if (total > 120) for (int i = 0; i < histCount; i++) hist[i].count = (hist[i].count + 1) / 2;

    saveHistory();
}

// Picks the top subreddits and sets subName ("a+b+c") and homeLabel ("a, b, c").
static void computeHome(void) {
    bool used[MAX_HIST] = {false};
    char combined[64] = "", label[96] = "";
    int picked = 0;
    while (picked < HOME_MAX_SUBS) {
        int best = -1;
        for (int i = 0; i < histCount; i++) {
            if (used[i]) continue;
            if (best < 0 || hist[i].count > hist[best].count ||
                (hist[i].count == hist[best].count && hist[i].seq > hist[best].seq)) best = i;
        }
        if (best < 0) break;
        used[best] = true;
        size_t add = strlen(hist[best].name) + (picked ? 1 : 0);
        if (strlen(combined) + add > HOME_MAX_CHARS) continue;  // too long, try a shorter one
        if (picked) { strcat(combined, "+"); strcat(label, ", "); }
        strcat(combined, hist[best].name);
        strcat(label, hist[best].name);
        picked++;
    }
    if (picked < HOME_MIN_SUBS) {
        snprintf(subName, sizeof subName, "all");
        snprintf(homeLabel, sizeof homeLabel, "r/all (open posts to personalize)");
    } else {
        snprintf(subName, sizeof subName, "%s", combined);
        snprintf(homeLabel, sizeof homeLabel, "%s", label);
    }
}

// Reloads the post list from the server (blocking, with a loading screen).
static void reloadPosts(int *sel, float *scroll) {
    loadingFrame("Loading posts...");
    if (!fetchPosts() && postCount == 0) { /* lastErr already set */ }
    *sel = 0;
    *scroll = 0;
}

static void goHome(int *sel, float *scroll) {
    isHome = true;
    query[0] = 0;
    computeHome();
    reloadPosts(sel, scroll);
    if (lastErr[0] && strchr(subName, '+')) {  // e.g. one of the subreddits is private or banned
        snprintf(subName, sizeof subName, "all");
        snprintf(homeLabel, sizeof homeLabel, "r/all (fallback)");
        reloadPosts(sel, scroll);
    }
}

// Leaves search results and returns to the feed you were in before searching.
static void leaveSearch(int *sel, float *scroll) {
    query[0] = 0;
    if (prevIsHome) { goHome(sel, scroll); return; }
    isHome = false;
    snprintf(subName, sizeof subName, "%s", prevSub);
    reloadPosts(sel, scroll);
}

// ----------------------------------------------------------------- main ----
int main(void) {
    gfxInitDefault();
    C3D_Init(C3D_DEFAULT_CMDBUF_SIZE);
    C2D_Init(C2D_DEFAULT_MAX_OBJECTS);
    C2D_Prepare();
    topT = C2D_CreateScreenTarget(GFX_TOP, GFX_LEFT);
    botT = C2D_CreateScreenTarget(GFX_BOTTOM, GFX_LEFT);
    textBuf = C2D_TextBufNew(8192);
    initColors();
    httpcInit(0);

    loadConfig();
    loadHistory();

    int view = VIEW_LIST;
    int sel = 0;
    float listScroll = 0, cmScroll = 0;
    int lastTouchY = -1;

    if (configured()) goHome(&sel, &listScroll);
    else snprintf(lastErr, sizeof lastErr,
                  "Server not set. Create sdmc:/3ds/redditviewer/server.txt containing your proxy address, "
                  "e.g. https://my-project.pages.dev/api");

    while (aptMainLoop()) {
        hidScanInput();
        u32 down = hidKeysDown(), held = hidKeysHeld();
        // START exits, except in the list while sorting by Top, where START/SELECT pick the time range.
        bool rangeKeys = (view == VIEW_LIST && sortIdx == SORT_TOP && !query[0]);
        if ((down & KEY_START) && !rangeKeys) break;

        touchPosition touch;
        hidTouchRead(&touch);
        bool touching = (held & KEY_TOUCH) != 0;
        int heldBtn = 0;

        if (view == VIEW_LIST) {
            const Button *btns[9] = {&bPrev, &bNext, &bOpen, &bSearch, &bSub, &bSort, &bRefresh, &bHome, &bFeed};
            int press = 0;
            for (int i = 0; i < 9; i++) {
                if (i == 8 && !query[0]) continue;  // the Feed button only exists during a search
                if (touching && inButton(btns[i], touch.px, touch.py)) heldBtn = i + 1;
                if ((down & KEY_TOUCH) && inButton(btns[i], touch.px, touch.py)) press = i + 1;
            }
            if ((down & KEY_UP) || press == 1) { if (sel > 0) sel--; }
            if ((down & KEY_DOWN) || press == 2) { if (sel < postCount - 1) sel++; }
            if (down & KEY_L) { sel -= CARDS_PER_PAGE * PAGES_PER_JUMP; if (sel < 0) sel = 0; }
            if (down & KEY_R) {
                sel += CARDS_PER_PAGE * PAGES_PER_JUMP;
                if (sel > postCount - 1) sel = postCount - 1;  // not enough posts left: stop at the last one
                if (sel < 0) sel = 0;
            }

            if (((down & KEY_A) || press == 3) && postCount > 0) {
                view = VIEW_POST;
                recordView(posts[sel].sub);  // teach the Home feed what you read
                cmScroll = 0;
                lastTouchY = -1;
                freeMedia();
                loadingFrame("Loading comments...");
                lastErr[0] = 0;
                fetchComments(&posts[sel]);
                const Post *p = &posts[sel];
                mediaState = (p->media == MEDIA_GIF) ? MS_GIFINFO : (p->media == MEDIA_PHOTO ? MS_PHOTO : MS_NONE);
            }
            if (((down & KEY_X) || press == 4) && configured()) {
                char buf[64];
                if (askText("Search all of Reddit...", query, buf, sizeof buf, 60)) {
                    bool wasSearching = query[0] != 0;
                    if (!wasSearching && buf[0]) {  // remember the feed so "Feed" / B can return to it
                        prevIsHome = isHome;
                        snprintf(prevSub, sizeof prevSub, "%s", subName);
                    }
                    snprintf(query, sizeof query, "%s", buf);
                    if (buf[0]) reloadPosts(&sel, &listScroll);
                    else if (wasSearching) leaveSearch(&sel, &listScroll);  // empty search = back to the feed
                }
            }
            if (press == 7 && configured()) reloadPosts(&sel, &listScroll);
            if (((down & KEY_Y) || press == 8) && configured()) goHome(&sel, &listScroll);
            if (((down & KEY_B) || press == 9) && query[0] && configured()) leaveSearch(&sel, &listScroll);
            if (press == 5 && configured()) {
                char buf[48];
                if (askText("Subreddit (e.g. gaming), empty = all", "", buf, sizeof buf, 40)) {
                    const char *s = buf;
                    if ((s[0] == 'r' || s[0] == 'R') && s[1] == '/') s += 2;
                    snprintf(subName, sizeof subName, "%s", s[0] ? s : "all");
                    isHome = false;
                    query[0] = 0;
                    reloadPosts(&sel, &listScroll);
                }
            }
            if (rangeKeys && configured() && ((down & KEY_START) || (down & KEY_SELECT))) {
                tIdx = (tIdx + ((down & KEY_START) ? 1 : 4)) % 5;  // START = next range, SELECT = previous
                reloadPosts(&sel, &listScroll);
            }
            if (press == 6 && configured() && !query[0]) {  // search results have a fixed order
                sortIdx = (sortIdx + 1) % 4;
                reloadPosts(&sel, &listScroll);
            }
        } else {
            if (touching && inButton(&bBack, touch.px, touch.py)) heldBtn = 1;
            if (((down & KEY_TOUCH) && inButton(&bBack, touch.px, touch.py)) || (down & KEY_B)) {
                view = VIEW_LIST;
                freeMedia();
                lastErr[0] = 0;
            }

            float maxScroll = commentsTotalHeight() - (CM_BOTTOM - CM_TOP);
            if (maxScroll < 0) maxScroll = 0;

            if (down & KEY_TOUCH) lastTouchY = (touch.py > CM_TOP && touch.py < CM_BOTTOM) ? touch.py : -1;
            else if (touching && lastTouchY >= 0) { cmScroll -= (touch.py - lastTouchY); lastTouchY = touch.py; }
            else lastTouchY = -1;

            if (held & KEY_DOWN) cmScroll += 4;
            if (held & KEY_UP) cmScroll -= 4;
            circlePosition cp;
            hidCircleRead(&cp);
            if (cp.dy > 20 || cp.dy < -20) cmScroll -= cp.dy * 0.06f;

            if (cmScroll < 0) cmScroll = 0;
            if (cmScroll > maxScroll) cmScroll = maxScroll;
        }

        // smooth list scroll
        float maxScroll = postCount * CARD_PITCH - (240.0f - LIST_TOP);
        if (maxScroll < 0) maxScroll = 0;
        float target = sel * CARD_PITCH - 90.0f;
        if (target < 0) target = 0;
        if (target > maxScroll) target = maxScroll;
        listScroll += (target - listScroll) * 0.25f;

        C2D_TextBufClear(textBuf);
        C3D_FrameBegin(C3D_FRAME_SYNCDRAW);
        if (view == VIEW_LIST) {
            renderListTop(listScroll, sel);
            renderListBottom(sel, heldBtn);
        } else {
            renderPostTop(&posts[sel]);
            renderPostBottom(cmScroll, heldBtn == 1);
        }
        C3D_FrameEnd(0);

        // One blocking media-download step per frame, after the frame (with its "loading" label) is shown.
        if (view == VIEW_POST && (mediaState == MS_PHOTO || mediaState == MS_GIFINFO || mediaState == MS_GIFFRAMES))
            mediaStep(&posts[sel]);
    }

    freeMedia();
    freePosts();
    httpcExit();
    C2D_TextBufDelete(textBuf);
    C2D_Fini();
    C3D_Fini();
    gfxExit();
    return 0;
}
