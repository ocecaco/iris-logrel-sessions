with import <nixpkgs> {};
stdenv.mkDerivation {
  name = "iris-logrel-sessions";
  buildInputs = [
    ocaml
    m4
    opam
  ];

  shellHook = ''
eval $(opam env)
  '';
}
