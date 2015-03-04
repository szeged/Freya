Valgrind 3.11 with Freya
========================

Build steps:
------------

```shell
./autogen.sh
./configure --prefix=`pwd`/inst
make
make install

cd freya
make
make install
```

Cross-Compile for ARM:
----------------------

```shell
export CROSS_COMPILE=arm-linux-gnueabihf-
export CC=${CROSS_COMPILE}gcc
export CPP=${CROSS_COMPILE}cpp
export CXX=${CROSS_COMPILE}g++
export LD=${CROSS_COMPILE}ld
export AR=${CROSS_COMPILE}ar

./configure --prefix=`pwd`/inst --host=armv7-linux-gnueabihf
make
make install

cd freya
make
make install
```

Usage:
------

```shell
./inst/bin/valgrind --tool=freya [ --config=config_file --mmap=no --log-file=log_file ] prog
```

Or without install:

```shell
./vg-in-place --tool=freya [ --config=config_file --mmap=no --log-file=log_file ] prog
```

The flags in [ ] are optional. Run with --help for more information.

More info:
------
You can read more about Freya at this blogpost:

http://webkit.sed.hu/node/29
