FROM python:3

RUN pip3 install pygithub==1.47
RUN pip3 install satsuki==0.1.23

ARG SATS_TAG
ARG SATS_COMMITISH
ARG SATS_TOKEN
ARG SATS_SLUG

ENV LANG C.UTF-8
ENV LC_ALL C.UTF-8

# Create or update the release
RUN satsuki --pre

# Upload the file to the release
ARG SATS_FILE
COPY $SATS_FILE $SATS_FILE
RUN satsuki --pre
