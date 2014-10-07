FROM ubuntu
MAINTAINER Guillaume Claret

RUN apt-get update && apt-get upgrade -y
RUN apt-get install -y gcc make git

# Opam
RUN apt-get install -y opam
RUN opam init
RUN opam install -y coq

# The Coq repository
RUN v=1 opam repo add coq https://github.com/coq/opam-coq-repo.git
ENV OPAMJOBS 4

# coq-list-string
RUN opam install -y coq-list-string

# Build
ADD . /root/coq-concurrency
WORKDIR /root/coq-concurrency
RUN eval `opam config env`; ./configure.sh
RUN eval `opam config env`; make -j