#!/usr/bin/perl

# Filename: header.pl

# Author : A.G.Raja

# Website : agraja.wordpress.com

# License : GPL

# pass files as arguments to this script

# this script will add the header text

use strict;

use warnings;

sub addheader{

my($infile,$header)=@_;

my $text = do { local( @ARGV, $/ ) = $infile ; <> } ;

open(FILE,">$infile");

print FILE $header;

print FILE $text;

close FILE

}

my $argnum;

foreach $argnum (0 .. $#ARGV){

my $infile = $ARGV[$argnum];

# Edit line below to change header text

use File::Slurp;
my $header =  read_file('header.txt');
print $header;
&addheader($infile,$header);

}

# chmod +x header.pl

# ./header.pl *.txt