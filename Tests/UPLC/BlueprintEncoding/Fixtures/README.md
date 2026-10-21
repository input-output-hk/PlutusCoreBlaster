# Blueprint test fixtures

These files make the blueprint parser tests reproducible in a clean checkout.

- `Acme.golden.json` is from `IntersectMBO/plutus` commit
  `e047551d8078e3c2b77a7fcba9c28a8aad745738`, path
  `plutus-tx-plugin/test/Blueprint/Acme.golden.json`.
- The `ctf-*.json` files are from `Invariant-0/cardano-ctf` commit
  `cba601de9bdf4a7938c9abed4fb041b5e1cf094e`.

The tests intentionally pin the exact documents because generated declaration
names, schema shapes, and script hashes are part of their assertions.
