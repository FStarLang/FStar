FROM ubuntu:trusty
MAINTAINER josh < joshjdevl [at] gmail dot com >

RUN apt-get update && apt-get -y install python-software-properties software-properties-common && \
add-apt-repository "deb http://gb.archive.ubuntu.com/ubuntu $(lsb_release -sc) universe" && \
apt-get update
RUN add-apt-repository ppa:saiarcot895/myppa && \
apt-get update && \
apt-get -y install apt-fast

RUN apt-fast -y install mono-complete fsharp wget build-essential
RUN apt-fast -y install unzip

RUN mozroots --import --sync

RUN mkdir -p /installs && cd /installs && wget "http://download-codeplex.sec.s-msft.com/Download/Release?ProjectName=z3&DownloadId=891122&FileTime=130523828556400000&Build=20959" -O z3-4.3.2.5a45711f22d9-x64-ubuntu-13.10.zip 
RUN cd /installs && unzip z3-4.3.2.5a45711f22d9-x64-ubuntu-13.10.zip && export PATH=/installs/z3-4.3.2.5a45711f22d9-x64-ubuntu-13.10/bin:$PATH

RUN apt-fast -y install git
RUN cd /installs && git clone https://github.com/FStarLang/FStar.git && cd FStar &&  make -C src
RUN cd /installs/FStar && /bin/bash -c "source setenv.sh && make test -C src"
