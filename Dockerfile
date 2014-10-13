FROM ubuntu
MAINTAINER Guillaume Claret

RUN apt-get update && apt-get upgrade -y
RUN apt-get install -y gcc make git

# Opam
RUN apt-get install -y opam
RUN opam init
ENV OPAMJOBS 4
RUN opam install -y coq

# Tools
RUN apt-get install -y inotify-tools

# Stable dependencies
RUN opam repo add coq https://github.com/coq/opam-coq-repo.git

# Unstable dependencies
RUN opam repo add coq-unstable https://github.com/coq/opam-coq-repo-unstable.git
RUN opam install -y coq-list-string
RUN opam install -y coq-fun-combinators

# Build
ADD . /root/coq-concurrency
WORKDIR /root/coq-concurrency
RUN eval `opam config env`; ./configure.sh && make

# Continuous build
CMD eval `opam config env`; while inotifywait *.v; do make; done