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

# The Coq repository
RUN opam repo add coq https://github.com/coq/opam-coq-repo.git

# Dependencies
# RUN opam install -y coq-list-string
WORKDIR /root
RUN git clone https://github.com/clarus/coq-list-string.git
WORKDIR coq-list-string
RUN eval `opam config env`; ./configure.sh && make -j && make install

# Build
ADD . /root/coq-concurrency
WORKDIR /root/coq-concurrency
CMD eval `opam config env`; while inotifywait *.v; do make; done