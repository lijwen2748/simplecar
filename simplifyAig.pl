#!/usr/bin/perl

#########
# usage: ./simplifyAig.pl
#########

use strict;
use POSIX qw/strftime/;
use Time::HiRes qw( time );

my $root = "/home/jianwen-public/"; ##change your root directory here
my $input_dir = "${root}hwmcc/benchmark/single/";
my $output_dir = "${root}hwmcc/benchmark/single-simp/";

my $timeout_file = "timeout.log";

open (TIMEOUT, ">${timeout_file}") or die "cannot open ${timeout_file}\n";

my $timeout = 600;

if (! (-d $output_dir)) {
    mkdir("$output_dir", 0755) or die "Cannot mkdir $output_dir: $!";;
}


opendir my $dh, $input_dir or die "Could not open '$input_dir' for reading: $!\n";

my @files = readdir $dh;
foreach my $file (@files) {
    if ($file eq '.' or $file eq '..') {
        next;
    }
    
    print "simplify $file\n";
    my $in_file = $input_dir.$file;
    my $out_file = $output_dir.$file;

    my $abc_command = "&read ${in_file}; &scorr; &dc2; &put; dretime; &get; &dc2; &write -n ${out_file}";
    eval {
        local $SIG{ALRM} = sub { die "timeout\n" };
	    alarm($timeout);
        `abc -c "${abc_command}"`;
    };
	if($@) {
        `killall -9 abc`;
        `cp ${in_file} ${out_file}`;
        print TIMEOUT "${file}\n";
	    sleep 1;		 
	}
}
close TIMEOUT;

closedir $dh;

exit;


