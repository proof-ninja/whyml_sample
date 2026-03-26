# whyml_sample

[Why3](https://www.why3.org/) をライブラリとして使う OCamlのコードのサンプル

### build
- `opam install . --deps-only` でパッケージをインストール

- `why3 config detect` を実行して Coq を認識させる

- `dune build` でビルド， `dune exec (/bin フォルダのファイルから .ml を取った名前)` で実行