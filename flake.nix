{
  inputs = {
    fenix = {
      url = "github:nix-community/fenix";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    flake-utils.url = "github:numtide/flake-utils";
    nixpkgs.url = "nixpkgs/nixos-unstable";
  };

  outputs =
    {
      self,
      fenix,
      flake-utils,
      nixpkgs,
    }:
    flake-utils.lib.eachDefaultSystem (
      system:

      let
        target = "aarch64-unknown-linux-musl";
        toolchain = with fenix.packages.${system}; combine [
            stable.cargo
            stable.rustc
            targets.${target}.stable.rust-std
          ];
        pkgs = nixpkgs.legacyPackages.${system};
        platform = pkgs.makeRustPlatform {
          cargo = toolchain;
          rustc = toolchain;
        };
      in
      {
        packages = {
          default =

            platform.buildRustPackage {
              pname = "package";
              nativeBuildInputs = with pkgs; [ cmake ];
              buildInputs = with pkgs; [ stdenv.cc.cc.lib ];
              version = "0.1.0";

              src = ./.;

              cargoLock.lockFile = ./Cargo.lock;
            };
          doc = platform.buildRustPackage {
            name = "package-doc";
            dontCheck = true;
            dontInstall = true;
            nativeBuildInputs = with pkgs; [ cmake ];
            cargoLock.lockFile = ./Cargo.lock;
            src = ./.;
            buildPhase = ''
              mkdir -p $out
              cargo doc --offline
              cp -a target/doc $out/'';
          };

          # Combined documentation: rustdoc + mdBook
          docs = platform.buildRustPackage {
            pname = "fossil-mcp-docs";
            version = "0.1.0";
            src = ./.;

            cargoLock.lockFile = ./Cargo.lock;

            nativeBuildInputs = with pkgs; [
              mdbook
              cmake
            ];

            buildInputs = with pkgs; [
              stdenv.cc.cc.lib
            ];

            # Don't run tests during doc build
            doCheck = false;

            buildPhase = ''
              echo "Building API documentation..."
              cargo doc --no-deps --offline

              echo "Building user guide..."
              mdbook build book
            '';

            installPhase = ''
              mkdir -p $out/share/doc/fossil-mcp
              cp -r target/doc $out/share/doc/fossil-mcp/api
              cp -r book/output $out/share/doc/fossil-mcp/book

              cat > $out/share/doc/fossil-mcp/index.html <<'EOF'
<!DOCTYPE html>
<html>
<head>
  <title>Fossil MCP Documentation</title>
  <style>
    body { font-family: system-ui; max-width: 800px; margin: 50px auto; padding: 20px; }
    .docs-section { border: 1px solid #ddd; border-radius: 8px; padding: 20px; margin: 20px 0; }
    h1 { color: #333; }
    a { color: #0066cc; text-decoration: none; }
  </style>
</head>
<body>
  <h1>📚 Fossil MCP Documentation</h1>
  <div class="docs-section">
    <h2>📖 User Guide</h2>
    <p>Complete documentation for using the Fossil MCP server</p>
    <a href="book/index.html">Open User Guide →</a>
  </div>
  <div class="docs-section">
    <h2>🔧 API Reference</h2>
    <p>Rust API documentation for developers</p>
    <a href="api/fossil_mcp/index.html">Open API Docs →</a>
  </div>
</body>
</html>
EOF

              mkdir -p $out/bin
              cat > $out/bin/view-docs <<'SCRIPT'
#!/usr/bin/env bash
if command -v xdg-open &> /dev/null; then
  xdg-open $out/share/doc/fossil-mcp/index.html
elif command -v open &> /dev/null; then
  open $out/share/doc/fossil-mcp/index.html
else
  echo "Documentation: $out/share/doc/fossil-mcp/index.html"
fi
SCRIPT
              chmod +x $out/bin/view-docs
            '';
          };
        };
        devShells = {
          default = pkgs.mkShell {
            buildInputs = [
              (fenix.packages.${system}.stable.withComponents [
                "cargo"
                "clippy"
                "rust-src"
                "rustc"
                "rustfmt"
              ])
              pkgs.jq
              pkgs.fossil
              pkgs.tlaplus18
              pkgs.mdbook
            ];

            shellHook = ''
              export CARGO_HOME="$PWD/.cargo"
              export PATH="$CARGO_HOME/bin:$PATH"
              export LD_LIBRARY_PATH="${pkgs.stdenv.cc.cc.lib}/lib";
              mkdir -p .cargo
              echo '*' > .cargo/.gitignore
            '';
          };
        };
      }
    );
}
