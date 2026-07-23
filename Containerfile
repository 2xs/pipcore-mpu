FROM ocaml/opam:alpine-ocaml-4.14

RUN sudo apk add --no-cache binutils-arm-none-eabi\
                            newlib-arm-none-eabi\
                            gcc-arm-none-eabi\
                            make\
                            py3-elftools

RUN opam install rocq-core=9.1.1 rocq-stdlib=9.0.0\
 && opam clean -a -c -s --logs
