FROM ocaml/opam:debian-12-ocaml-5.3

# Install system build tools
RUN sudo apt-get update \
    && sudo apt-get install -y --no-install-recommends \
        make \
        build-essential \
        pkg-config \
        libgmp-dev \
        linux-libc-dev \
    && sudo rm -rf /var/lib/apt/lists/*

# Install Rocq and decompress (pure-OCaml DEFLATE/gzip), clean up opam cache
RUN opam install -y rocq-prover decompress \
    && opam clean --all

WORKDIR /workspace
USER opam
