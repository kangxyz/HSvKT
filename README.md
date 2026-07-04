# HSvKT

In [`HSvKT-warnd.agda`](/HSvKT-warnd.agda), it proves the direct colimit of the inductive family `Word` admits the eliminator introduced by [Kraus-von Raumer](https://arxiv.org/abs/1901.06022). The inductive family should be in principle equivalent to the zig-zag construction presented by [Wärn](https://arxiv.org/abs/2402.12339).

## Dependencies

This project is checked with:

- Agda 2.8.0
- Cubical Agda library 0.9-compatible checkout (`v0.9-70-g92166033`)

To check the project, run:

```sh
agda HSvKT-warnd.agda
```
