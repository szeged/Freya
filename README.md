Valgrind 3.11 with Freya
=====

Build steps:

./autogen.sh

./configure --prefix=`pwd`/inst

make 

make install


cd freya

make 

make install

Run it from inst directory.


Cross-Compile for ARM:

export CROSS_COMPILE=arm-linux-gnueabihf-
export CC=${CROSS_COMPILE}gcc
export CPP=${CROSS_COMPILE}cpp
export CXX=${CROSS_COMPILE}g++
export LD=${CROSS_COMPILE}ld
export AR=${CROSS_COMPILE}ar

./configure --prefix=`pwd`/inst \
			--host=armv7-linux-gnueabihf

make

make install


cd freya

make 

make install

Run it from inst directory.

Usage:

valgrind --tool=freya prog

You can read more about Freya at this blogpost:

http://webkit.sed.hu/node/29