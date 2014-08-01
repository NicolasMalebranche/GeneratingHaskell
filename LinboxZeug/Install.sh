#!/bin/bash

apt-get install cabal-install
cabal update
cabal install MemoTrie
cabal install permutation 


apt-get install libgmp3c2 libgmp3-dev libblas3gf libblas-dev liblapack3gf liblapack-dev libntl-dev
apt-get remove libgivaro-dev libgivaro0

# ( cd /usr/share/gap; ln -s /usr/include/gap src; )

cd /home/skapfer/GAP_Packages/

tar -xzf givaro-3.7.2.tar.gz
cd givaro-3.7.2
./configure --with-pic
make
make install
cd ..

tar -xzf fflas-ffpack-1.6.0.tar.gz
cd fflas-ffpack-1.6.0
./configure  # --with-givaro=/tmp/givaro-exec
make 
make install
cd .. 

tar -xzf linbox-1.3.2.tar.gz
cd linbox-1.3.2/
./configure  # --with-givaro=/tmp/givaro-exec
make
make install


# Bemerkung für linboxing: ./configure --with-gaproot=/usr/share/gap
