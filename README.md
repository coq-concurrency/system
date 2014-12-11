# ![Logo](https://raw.githubusercontent.com/clarus/icons/master/street-light-48.png) System
The monad and API definitions.

## Install with OPAM
Add the Coq repositories:

    opam repo add coq-stable https://github.com/coq/repo-stable.git
    opam repo add coq-unstable https://github.com/coq/repo-unstable.git

Run:

    opam install coq:concurrency:system

## Install from the sources
Install the dependencies through OPAM:

    opam repo add coq-stable https://github.com/coq/repo-stable.git
    opam repo add coq-unstable https://github.com/coq/repo-unstable.git
    opam install coq:list-string coq:function-ninjas

Run:

    ruby pp.rb
    ./configure.sh
    make
    make install
