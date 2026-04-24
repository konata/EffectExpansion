# EffectExpansion

A bytecode optimizer for the JVM that performs **interprocedural constant folding** — it finds call sites where the target is a pure function called with compile-time-known arguments, evaluates the call concretely, and rewrites the bytecode to replace the call with its result.

```java
// before
String encoded = Base64.encode("hello world");

// after (rewritten bytecode — no runtime call)
String encoded = "aGVsbG8gd29ybGQ=";
```

This is essentially **partial evaluation** applied to JVM bytecode: evaluate what can be determined statically, leave everything else untouched.

## How it works

EffectExpansion operates in three phases:

**1. Purity analysis**
Walks the call graph to identify *side-effect-free* methods — functions that read no global/static state, perform no I/O, and call only other pure functions. Soot's `SideEffectAnalysis` provides the baseline; EffectExpansion propagates purity through the call graph.

**2. Constant propagation**
Tracks which values at each call site are statically known (literal constants, or the result of previously folded calls). A call site is foldable when its target is pure *and* all its arguments are known.

**3. Concrete execution & rewrite**
Runs the pure function concretely using the interpreter (built over Soot's Jimple IR), captures the return value, then replaces the call site in the bytecode with the computed constant.

## Architecture

```
Soot / Jimple IR
      │
      ├── Purity analysis        (side-effect-free detection)
      ├── Constant propagation   (which call sites are foldable?)
      │
      └── Interpreter            (concrete execution of pure functions)
              │
              ├── Needle         (program counter over a method body)
              ├── Scope          (stack frame: locals, args, receiver)
              └── Types          (value domain: primitives + references)
```

The interpreter is written in Scala 3 on top of [Soot 4.x](https://github.com/soot-oss/soot). Jimple — Soot's typed three-address-code IR — is used as the execution target, which makes the interpreter significantly simpler than working directly on bytecode.

## Roadmap

- [ ] Complete interpreter: arithmetic, bitwise, and comparison operators
- [ ] Complete interpreter: field reads, array accesses, type casts
- [ ] Function call dispatch (`invokevirtual`, `invokestatic`, `invokespecial`)
- [ ] `<init>` and `<clinit>` handling
- [ ] Purity analysis pass
- [ ] Constant propagation pass
- [ ] Bytecode rewrite pass (replace foldable call sites)
- [ ] Stub registry — register handlers for native/built-in methods (e.g. `Math.abs`, `String.length`) so they can participate in folding without needing a Jimple body
- [ ] Embedded debugger (step through the concrete interpreter)

## Non-goals

EffectExpansion is **not** a general-purpose JVM. It only executes the subset of code reachable from a foldable call site, and it intentionally aborts when it encounters side effects (I/O, field writes, native calls without a registered stub). The goal is to do less, correctly — not to emulate the full JVM semantics.
