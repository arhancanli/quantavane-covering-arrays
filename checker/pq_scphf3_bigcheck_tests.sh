#!/bin/zsh
# pq_scphf3_bigcheck_tests.sh WORKDIR: evidence that independent/pq_scphf3_bigcheck is right (3 Nov 2026).
# 1. Random arrays (with forced point coincidences): its count of uncovered triples must equal that of
#    independent/scphf_check (every triple by determinant), for every field type, also summed over three shards.
# 2. Every strength-3 family of the public release must PASS.
# 3. Broken copies must FAIL: a column overwritten by another (exactly k - 2 uncovered), one entry moved so that
#    a triple covered by a single row is covered by none (that triple found in its shard), and ca-tools
#    conversions done without the field isomorphism (q 9, 25), checked in the Conway field.
# Prints one line per test and "ALL TESTS PASSED" or "SOME TEST FAILED".
W=${1:?work dir}; mkdir -p $W
# QV_ENGINE: a checkout of the engine that holds independent/pq_scphf3_bigcheck and engine/ca_certificates.py;
# the repository is found from this script's own path.
E=${QV_ENGINE:?set QV_ENGINE to the engine checkout}; R=${QV_REPO:-${0:A:h:h}}
BIG=$E/independent/pq_scphf3_bigcheck; OLD=$E/independent/scphf_check
ok=1
cat > $W/pq_randarr.py <<'EOF'
import random, sys
q, n, k, seed, out = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), sys.argv[5]
rng = random.Random(seed); P = q * q; rows = []
for r in range(n):
    pool = [rng.randrange(P) for _ in range(max(2, k // 6))] if rng.random() < 0.5 else None
    rows.append([rng.choice(pool) if pool and rng.random() < 0.5 else rng.randrange(P) for _ in range(k)])
with open(out, "w") as f:
    f.write(f"best k {k} (random q {q} n {n} seed {seed})\n")
    for row in rows: f.write(" ".join(map(str, row)) + "\n")
EOF
cnt() { sed -E -n '1s/.*(checked|\)), ([0-9]+) never.*/\2/p'; }
for spec in "2 4 40" "3 4 50" "4 3 60" "4 6 90" "4 8 400" "4 10 700" "5 4 80" "5 7 500" "7 3 120" "7 6 600" \
            "8 4 100" "8 6 900" "9 3 140" "9 5 600" "11 3 120" "13 2 90" "16 3 110" "16 4 700" "17 2 100" \
            "19 2 90" "23 2 100" "25 2 120" "25 4 800" "27 2 80" "32 2 80"; do
  set -- ${=spec}; f=$W/r_$1_$2_$3.txt
  python3 -I $W/pq_randarr.py $1 $2 $3 $(( $1 * 1000 + $2 * 10 + $3 )) $f
  a=$($OLD $1 $f 10 | cnt); b=$($BIG $1 $f 10 | cnt)
  s1=$($BIG $1 $f 10 0 $(( $3 / 3 )) | cnt); s2=$($BIG $1 $f 10 $(( $3 / 3 )) $(( 2 * $3 / 3 )) | cnt); s3=$($BIG $1 $f 10 $(( 2 * $3 / 3 )) $3 | cnt)
  st=OK; [ -n "$a" ] && [ "$a" = "$b" ] && [ "$a" = "$(( s1 + s2 + s3 ))" ] || { st=MISMATCH; ok=0; }
  echo "random q $1 n $2 k $3: scphf_check $a, pq_scphf3_bigcheck $b, shards $s1+$s2+$s3: $st"
done
awk -F, '$1==3 {print $2, $6}' $R/families.csv | while read qq fam; do
  res=$($BIG $qq $R/$fam 500 | tail -1); echo "release $fam: $res"; [ "$res" = PASS ] || ok=0
done
cat > $W/pq_breakfam.py <<'EOF'
import random, sys
q, src, out, mode = int(sys.argv[1]), sys.argv[2], sys.argv[3], sys.argv[4]
rows = [list(map(int, l.split())) for l in open(src) if l[0].isdigit()]
n, k = len(rows), len(rows[0]); rng = random.Random(7)
def tri(r, a, b, c):
    xa, ya = divmod(rows[r][a], q); xb, yb = divmod(rows[r][b], q); xc, yc = divmod(rows[r][c], q)
    return ((xb - xa) * (yc - ya) - (yb - ya) * (xc - xa)) % q != 0
if mode == "dup":
    for r in range(n): rows[r][777] = rows[r][4242]
    print("dup 777 4242")
else:
    while True:
        a, b, c = rng.sample(range(k), 3); cov = [r for r in range(n) if tri(r, a, b, c)]
        if len(cov) == 1: break
    r = cov[0]; xa, ya = divmod(rows[r][a], q); xb, yb = divmod(rows[r][b], q)
    rows[r][c] = ((xa + 2 * (xb - xa)) % q) * q + (ya + 2 * (yb - ya)) % q
    assert not any(tri(s, a, b, c) for s in range(n)); print("one", *sorted((a, b, c)))
with open(out, "w") as f:
    f.write("best k %d (deliberately broken copy, %s)\n" % (k, mode))
    for row in rows: f.write(" ".join(map(str, row)) + "\n")
EOF
F=$R/families/CA_13117_3_10000_13.cphf.txt
python3 -I $W/pq_breakfam.py 13 $F $W/broken_dup.txt dup > /dev/null
d=$($BIG 13 $W/broken_dup.txt 200 | cnt); res=$($BIG 13 $W/broken_dup.txt 200 | tail -1)
echo "broken (column 777 := column 4242), q 13 k 10000: $d uncovered (expected 9998), $res"; [ "$d" = 9998 ] && [ "$res" = FAIL ] || ok=0
set -- $(python3 -I $W/pq_breakfam.py 13 $F $W/broken_one.txt one)
res=$($BIG 13 $W/broken_one.txt 200 | tail -1); sh=$($BIG 13 $W/broken_one.txt 10 $4 $(( $4 + 1 )) | head -1)
echo "broken (one entry; planted triple $2 $3 $4): $res; shard of column $4: $(echo $sh | sed -E 's/.*\), ([0-9]+ never non-collinear[^;]*);.*/\1/')"
[ "$res" = FAIL ] && echo $sh | grep -q "first: columns $2, $3, $4" || ok=0
cat > $W/pq_conway_conv.py <<'EOF'
import os, sys
sys.path.insert(0, os.path.join(os.environ["QV_ENGINE"], "engine"))
import ca_certificates as cc
src, q, out, mode = sys.argv[1], int(sys.argv[2]), sys.argv[3], sys.argv[4]
if mode == "nomap": cc.isomorphism = lambda qq: list(range(qq))
rows, vecs, ints = cc.convert(src, 3, q)
with open(out, "w") as f:
    f.write("# test conversion (%s)\n" % mode)
    for row in ints: f.write(" ".join(map(str, row)) + "\n")
EOF
for spec in "9 CA_5049_3_10000_9 2,2" "25 CA_62425_3_3738_25 2,4"; do
  set -- ${=spec}
  for m in map nomap; do
    python3 -I $W/pq_conway_conv.py $R/families/$2.cphf.txt $1 $W/conv_$1_$m.txt $m
    out=$(PQ_CERT=1 PQ_FIELDPOLY=$3 $BIG $1 $W/conv_$1_$m.txt 200 2>/dev/null); res=$(echo "$out" | tail -1)
    echo "ca-tools conversion of $2 ($m), checked in the Conway field: $(echo "$out" | cnt) uncovered, $res"
    { [ $m = map ] && [ "$res" = PASS ]; } || { [ $m = nomap ] && [ "$res" = FAIL ]; } || ok=0
  done
done
[ $ok = 1 ] && echo "ALL TESTS PASSED" || echo "SOME TEST FAILED"
