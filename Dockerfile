# Builds the whole development from a clean Ubuntu image and checks the
# assumptions of its claims.  See ARTIFACT.md.
#
#   docker build -t spo-lr-df .
#   docker run --rm -it spo-lr-df          # a shell in the built tree
#
# BASE selects the base image (for a registry mirror, e.g.
# --build-arg BASE=public.ecr.aws/docker/library/ubuntu:24.04).
ARG BASE=ubuntu:24.04
FROM ${BASE}

ENV DEBIAN_FRONTEND=noninteractive
RUN apt-get update \
 && apt-get install -y --no-install-recommends \
      opam build-essential m4 pkg-config libgmp-dev git unzip patch \
      ca-certificates curl rsync python3 time \
 && rm -rf /var/lib/apt/lists/*

RUN useradd -m rocq
USER rocq
WORKDIR /home/rocq
ENV OPAMYES=1 OPAMCONFIRMLEVEL=unsafe-yes

# The OCaml compiler and the Rocq repositories.
RUN opam init --bare --disable-sandboxing --no-setup \
 && opam switch create default ocaml-base-compiler.5.3.0 \
 && opam repo add rocq-released https://rocq-prover.org/opam/released \
 && opam clean -a -c -s --logs

# The dependencies at the versions of spo-lr-df.opam.locked: rocq-core
# 9.2.0, rocq-stdlib 9.2.0, rocq-stdpp 1.13.0 and theirs.
COPY --chown=rocq spo-lr-df.opam spo-lr-df.opam.locked /home/rocq/deps/
RUN opam install --deps-only --locked /home/rocq/deps \
 && opam list \
 && opam clean -a -c -s --logs

# The development.
COPY --chown=rocq . /home/rocq/spo-lr-df
WORKDIR /home/rocq/spo-lr-df
RUN eval "$(opam env)" \
 && ulimit -s 1000000 \
 && (make -j"$(nproc)" || make -j"$(nproc)") \
 && make check

CMD ["opam", "exec", "--", "bash"]
