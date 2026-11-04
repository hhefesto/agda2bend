
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
  const check = async (file) => {
    out = [];
    let rc = 1;
    try {
      const real = fs4.realpathSync(file);
      try { await take(real); } catch (e) {}
      const book = book_seed(G);
      const seen = new Map(seenG);
      await book_load(book, real, "", seen, undefined, root);
      book_valid(book, G.order.length);
      if (book.hols > 0) {
        throw "Error: " + String(book.hols) + " TODO" + (book.hols === 1 ? "" : "s")
          + " found.\nThe code is incomplete, and not a valid proof yet.";
      }
      rc = cli_verdict(book, false);
    } catch (e) {
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
          const r = await check(file);
          s.write(r);
          s.end();
        });
      },
    },
  });
  console.error("checkd: " + port + " over " + root + ", " + G.order.length + " defs of Base");
}
