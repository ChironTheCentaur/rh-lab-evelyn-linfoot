#!/usr/bin/env python3
"""Statement fidelity for EvelynLinfootFC/{Defs,FC}.lean against formal-conjectures.

    python3 -I controls/evelyn_linfoot_fc_fidelity.py FC_CHECKOUT [--self-test]

FC_CHECKOUT is a checkout of google-deepmind/formal-conjectures at PIN (the script refuses another commit).
Compares, after whitespace normalisation,
  * the definitions `squarefreeCounting` and `squarefreeCountingError` (statement and body),
  * the test `squarefreeCounting_ten` (statement and proof),
  * the statement of `erdos_969.variants.evelyn_linfoot` (up to `:= by`),
  * the namespace and the `open` line in force (`=o[atTop]` must elaborate the same way), at every occurrence in
    our two files.
Exit 0 iff every item is equal. --self-test mutates one token in each of our items and requires each mutation to be
reported (set comparison of the failing items against the mutated ones).
"""
import pathlib, re, subprocess, sys

PIN = "ea8e3e198ded6fc73efb7f5653b74b28ac4ae1a8"
HERE = pathlib.Path(__file__).resolve().parent.parent
OURS = [HERE / "EvelynLinfootFC" / "Defs.lean", HERE / "EvelynLinfootFC" / "FC.lean"]
FC = "FormalConjectures/ErdosProblems/969.lean"

# (name, keyword, statement_only, mutation (old, new) applied once inside our declaration)
ITEMS = [
    ("squarefreeCounting", "def squarefreeCounting (", False, ("Icc 1 x", "Icc 0 x")),
    ("squarefreeCountingError", "noncomputable def squarefreeCountingError ", False, ("6 / Real.pi ^ 2", "6 / Real.pi ^ 3")),
    ("squarefreeCounting_ten", "theorem squarefreeCounting_ten ", False, ("= 7", "= 6")),
    ("evelyn_linfoot", "theorem erdos_969.variants.evelyn_linfoot ", True, ("(1 / 4 : ℝ)", "(1 / 2 : ℝ)")),
    ("namespace", "namespace Erdos969", False, ("Erdos969", "Erdos696")),
    ("open", "open Filter Asymptotics", False, ("Filter Asymptotics", "Filter")),
]


def block(text, keyword, statement_only):
    i = text.find(keyword)
    if i < 0:
        return None
    rest = text[i:]
    end = re.search(r"\n\s*\n", rest)  # a declaration ends at the first blank line
    body = rest[: end.start()] if end else rest
    if statement_only:
        body = body.split(":= by")[0]
    return " ".join(body.split())


# items that must hold at EVERY line-start occurrence of their stem in our files (our proof is split over two files,
# each with its own namespace/open lines; a first-occurrence check would let the second one drift)
EVERY = {"namespace": "namespace ", "open": "open "}


def every_block(text, stem):
    return [" ".join(m.group(0).split()) for m in re.finditer(r"(?m)^" + re.escape(stem) + r".*$", text)]


def compare(ours_text, fc_text):
    bad = set()
    for name, kw, stmt_only, _ in ITEMS:
        b = block(fc_text, kw, stmt_only)
        if name in EVERY:
            ours_all = every_block(ours_text, EVERY[name])
            ok = b is not None and len(ours_all) > 0 and all(x == b for x in ours_all)
        else:
            a = block(ours_text, kw, stmt_only)
            ok = a is not None and b is not None and a == b
        print(f"{'EQUAL' if ok else 'DIFFERENT'}  {name}")
        if not ok:
            bad.add(name)
    return bad


def main():
    fc = pathlib.Path(sys.argv[1])
    head = subprocess.run(["git", "-C", str(fc), "rev-parse", "HEAD"], capture_output=True, text=True).stdout.strip()
    if head != PIN:
        print(f"FAIL: formal-conjectures checkout is at {head}, want {PIN}")
        return 1
    fc_text = (fc / FC).read_text()
    ours = "\n\n".join(p.read_text() for p in OURS)
    bad = compare(ours, fc_text)
    if "--self-test" in sys.argv:
        caught = set()
        for name, kw, _, (old, new) in ITEMS:
            i = ours.find(kw)
            j = ours.find("\n\n", i)
            seg = ours[i:j]
            m = seg.replace(old, new, 1)
            if m == seg:
                print(f"SELF-TEST BROKEN: no mutation site in {name}")
                return 1
            print(f"-- plant {name}: {old!r} -> {new!r}")
            if name in compare(ours[:i] + m + ours[j:], fc_text):
                caught.add(name)
        want = {n for n, *_ in ITEMS}
        print(f"self-test: caught {sorted(caught)} want {sorted(want)}")
        if caught != want:
            print("FAIL: self-test")
            return 1
    print("FAIL" if bad else "PASS: every item equal to formal-conjectures " + PIN[:8])
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
