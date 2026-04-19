# inline_fallthroughs.awk — dispatch-body normalizer for the cpp shim.
#
# Three transformations, applied in order to the extracted dispatch region:
#   1. Inline `/* Fallthrough */` bodies from the next Instruct block so
#      cpp doesn't split a fallthrough into two separate functions.
#   2. Strip the outer `{` from `Instruct(X): {` lines and drop the matching
#      `}` so block-form handlers collapse to flat bodies (matches the old
#      sed extractor, which started its range at `Instruct(...)` and ended
#      at `Next;`, excluding the trailing `}`).
#   3. Everything else passes through.
#
# Expects the caller to have already stripped the trailing `:` from
# `Instruct(X):` — so our input sees `Instruct(X)` or `Instruct(X) {`.

BEGIN { n = 0 }

{ L[NR] = $0 }

function is_instruct(s) { return s ~ /Instruct\([A-Z0-9_]+\)/ }
function has_next(s)    { return s ~ /[^a-zA-Z0-9_]Next;|^Next;/ }

# Count top-level `{` minus `}`, ignoring /*...*/ comments on the same line.
function net_braces(s,    t) {
    t = s
    gsub(/\/\*[^*]*\*+([^\/*][^*]*\*+)*\//, "", t)
    return gsub(/\{/, "&", t) - gsub(/\}/, "&", t)
}

END {
    # First sweep: if a line ends in `Instruct(X) {` (trailing `{` only), drop
    # the `{` and remember we owe a matching `}` at block depth 0.
    outer_pending = 0   # 1 if we owe a `}` drop
    depth = 0
    for (i = 1; i <= NR; i++) {
        line = L[i]
        if (is_instruct(line) && line ~ /\{[[:space:]]*$/) {
            sub(/[[:space:]]*\{[[:space:]]*$/, "", line)
            L[i] = line
            outer_pending = 1
            depth = 0
            continue
        }
        if (outer_pending) {
            d = net_braces(line)
            if (d < 0 && depth + d == -1) {
                # This line closes the outer block; delete only the *outer* `}`
                sub(/\}/, "", line)
                L[i] = line
                outer_pending = 0
                depth = 0
                continue
            }
            depth += d
        }
    }

    # Second sweep: emit lines, inlining fallthroughs.
    i = 1
    while (i <= NR) {
        line = L[i]
        print line
        if (line ~ /\/\*[[:space:]]*[Ff]allthrough[[:space:]]*\*\//) {
            j = i + 1
            while (j <= NR && !is_instruct(L[j])) j++
            if (j <= NR) {
                # Copy the next block's body up to and including its Next; line
                k = j + 1
                while (k <= NR && !has_next(L[k]) && !is_instruct(L[k])) k++
                if (k <= NR && has_next(L[k])) {
                    for (m = j + 1; m <= k; m++) print L[m]
                }
            }
        }
        i++
    }
}
