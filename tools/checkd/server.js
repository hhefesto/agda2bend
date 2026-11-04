
// agda2bend's check daemon (tools/checkd): appended by gen.sh to the JS of the
// `bend` it is given, in place of its command line, so the checker is exactly that
// bend's. `bend FILE --check-only` loads and checks FILE and every file it imports,
// each time: on a deep module of a corpus that is most of an emit's time, for the
// same imports over and over. This holds the imports in one book: a file the gate
// has finished is read once and not checked again (it passed), and a check is of
// FILE's own definitions, on a seeded copy of the book, as `--checkup` does with
// Base. What it prints and how it exits are the command's.
{
  const [port, root0] = process.argv.slice(2);
  const root = fs4.realpathSync(root0);
  const seenG = new Map();
  const G = book_nil();
  await book_load(G, BASE_BEND, "", seenG);
  book_valid(G, 0);
  let out = [];
  cli_say = (fd, text) => { out.push(text); };
  const importsOf = (text) => {
    const r = [];
    for (const l of text.split("\n")) {
      const line = l.trim();
      if (line === "" || line.startsWith("#")) continue;
      if (!/^import(\s|$)/.test(line)) break;
      const m = /^import\s+(\S+)(?:\s+as\s+([A-Za-z_]\w*))?\s*(?:#.*)?$/.exec(line);
      if (m !== null && m[2] !== undefined) r.push(m[1]);
    }
    return r;
  };
  // FILE's imports into the book, unchecked; what goes wrong here is said by
  // the load of FILE itself
  const take = async (real) => {
    const dir = path3.dirname(real);
    const had = G.order.length;
    for (const rel of importsOf(fs4.readFileSync(real, "utf8"))) {
      const got = path3.resolve(dir, rel);
      if (!fs4.existsSync(got)) continue;
      const sub = path3.relative(root, fs4.realpathSync(got)).replace(/\.bend$/, "");
      await book_load(G, got, sub, seenG, undefined, root);
    }
    if (G.order.length !== had) book_valid(G, G.order.length);
  };
  // The gate checks a module again after each repair, and the checker stops at the
  // first failure, in order. So from the last check of a file: what lies before its first
  // changed line, and before the definition that failed, passed then and is not checked
  // again. A file that passes that way is checked whole before it is said to pass.
  const last = new Map();
  const tops = (lines) => {
    const r = [];
    lines.forEach((l, i) => {
      const m = /^(?:@\w+\s+)*(?:def|type)\s+([^\s(<:]+)/.exec(l);
      if (m !== null) r.push([i, m[1]]);
    });
    return r;
  };
  const skipOf = (lines, order, base, prev) => {
    if (prev === undefined || prev.fail === null) return 0;
    let L = 0;
    while (L < lines.length && L < prev.lines.length && lines[L] === prev.lines[L]) L++;
    const ts = tops(lines);
    const same = new Set();
    ts.forEach(([at, k], j) => {
      const end = j + 1 < ts.length ? ts[j + 1][0] : lines.length;
      if (end <= L) same.add(k);
    });
    let n = 0;
    for (let i = base; i < order.length; i++) {
      const k = order[i];
      if (k === prev.fail || !same.has(k)) break;
      n++;
    }
    return n;
  };
  const verdict = async (real, lines, prev) => {
    const base = G.order.length;
    const book = book_seed(G);
    const seen = new Map(seenG);
    await book_load(book, real, "", seen, undefined, root);
    const skip = skipOf(lines, book.order, base, prev);
    book_valid(book, base + skip);
    if (book.hols > 0) {
      throw "Error: " + String(book.hols) + " TODO" + (book.hols === 1 ? "" : "s")
        + " found.\nThe code is incomplete, and not a valid proof yet.";
    }
    return skip === 0 ? book : null;
  };
  const check = async (file) => {
    out = [];
    let rc = 1;
    let real = file;
    let lines = [];
    try {
      real = fs4.realpathSync(file);
      lines = fs4.readFileSync(real, "utf8").split("\n");
      try { await take(real); } catch (e) {}
      const book = (await verdict(real, lines, last.get(real))) ?? (await verdict(real, lines, undefined));
      last.set(real, { lines, fail: null });
      rc = cli_verdict(book, false);
    } catch (e) {
      last.set(real, { lines, fail: e?.$ === "Err" && typeof e.def === "string" ? e.def : null });
      cli_say(2, book_err(new Check_Fail(e)) + "\n");
      rc = 1;
    }
    return "RC " + rc + "\n" + out.join("");
  };
  let chain = Promise.resolve();
  Bun.listen({
    hostname: "127.0.0.1",
    port: Number(port),
    socket: {
      data(s, b) {
        const file = b.toString().trim();
        chain = chain.then(async () => {
          const t0 = Date.now();
          const r = await check(file);
          console.error(path3.basename(file) + " " + (Date.now() - t0) + " ms " + r.slice(0, 5).trim());
          s.write(r);
          s.end();
        });
      },
    },
  });
  console.error("checkd: " + port + " over " + root + ", " + G.order.length + " defs of Base");
}
