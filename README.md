# Concurrency
Experiments to write concurrent applications in Coq.

## Build
To compile:

    docker build --tag=coq-concurrency .

To access the results of the compilation, run the `coq-concurrency` image:

    docker run -ti coq-concurrency /bin/bash

To launch a watching loop recompiling the project at each `.v` file change:

    docker run -ti -v `pwd`:/root/coq-concurrency coq-concurrency