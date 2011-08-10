#!/usr/bin/perl

use subs;
use strict;
use warnings;

# test.pl
#
# runs a test and check its output

sub run($$$$) {
  my ($input, $cmd, $options, $output) = @_;
  my $cmdline = "$cmd $options $input >$output 2>&1";

  print LOG "Running $cmdline\n";
  system $cmdline;
  my $exit_value = $? >> 8;
  my $signal_num = $? & 127;
  my $dumped_core = $? & 128;
  my $failed = 0;

  print LOG "  Exit: $exit_value\n";
  print LOG "  Signal: $signal_num\n";
  print LOG "  Core: $dumped_core\n";

  if($signal_num != 0) {
    $failed = 1;
    print "Killed by signal $signal_num";
    if($dumped_core) {
      print " (code dumped)";
    }
  }

  system "echo EXIT=$exit_value >>$output";
  system "echo SIGNAL=$signal_num >>$output";

  return $failed;
}

sub load($) {
  my ($fname) = @_;

  open FILE, "<$fname";
  my @data = grep { !/^\/\// } <FILE>;
  close FILE;

  chomp @data;
  return @data;
}

sub test($$$$) {
  my ($name, $test, $t_level, $cmd) = @_;
  my ($level, $input, $options, @results) = load($test);

  my $output = $input;
  $output =~ s/\.c$/.out/;
  $output =~ s/\.i$/.out/;
  $output =~ s/\.cpp$/.out/;

  if($output eq $input) {
    print("Error in test file -- $test\n");
    return 1;
  }

  print LOG "Test '$name'\n";
  print LOG "  Level: $level\n";
  print LOG "  Input: $input\n";
  print LOG "  Output: $output\n";
  print LOG "  Options: $options\n";
  print LOG "  Results:\n";
  foreach my $result (@results) {
    print LOG "    $result\n";
  }

  if($level eq "CORE") {
    $level = 1;
  } elsif($level eq "THOROUGH") {
    $level = 2;
  } elsif($level eq "FUTURE") {
    $level = 4;
  } elsif($level eq "KNOWNBUG") {
    $level = 8;
  } else {
    die "Level must be one of CORE, THOROUGH, FUTURE or KNOWNBUG\n";
  }

  my $failed = -1;
  if($level & $t_level) {
    $failed = run($input, $cmd, $options, $output);

    if(!$failed) {
      print LOG "Execution [OK]\n";
      my $included = 1;
      foreach my $result (@results) {
        last if($included == -1);
        if($result eq "--") {
          $included--;
        } else {
          my $r;
          system "grep '$result' '$output' >/dev/null";
          $r = ($included ? $? != 0 : $? == 0);
          if($r) {
            print LOG "$result [FAILED]\n";
            $failed = 1;
          } else {
            print LOG "$result [OK]\n";
          }
        }
      }
    } else {
      print LOG "Execution [FAILED]\n";
    }
  } else {
    print LOG "Execution [SKIPPED]\n";
  }

  print LOG "\n";

  return $failed;
}

sub dirs() {
  my @list;

  opendir CWD, ".";
  @list = grep { !/^\./ && -d "$_" && !/CVS/ } readdir CWD;
  closedir CWD;

  @list = sort @list;

  return @list;
}

sub usage() {
  print << "EOF";
test.pl -- run a series of regression tests

Usage: test.pl -c CMD [OPTIONS] [DIRECTORIES ...]
  where OPTIONS are one or more options as listed below; one or more directories
  may be passed as arguments to test only those. Otherwise all directories in
  the current location will be used.

  -c CMD     run tests on CMD - required option
  -h         show this help and exit
  -C         core: run all tests of level 1 (default if none of C/T/F/K are given)
  -T         thorough: run expensive tests (level 2)
  -F         future: run checks for future features (level 4)
  -K         known: run tests associated with known bugs (level 8)


test.pl expects a test.desc file in each subdirectory. The file test.desc
follows the format specified below. Any line starting with // will be ignored.

<level>
<main source>
<options>
<required patterns>
--
<disallowed patterns>
--
<comment text>

where
  <level>                is one of CORE, THOROUGH, FUTURE or KNOWNBUG
  <main source>          is a file with extension .c/.i/.cpp 
  <options>              additional options to be passed to CMD
  <required patterns>    one or more lines of regualar expressions that must occur in the output
  <disallowed patterns>  one or more lines of expressions that must not occur in output
  <comment text>         free form text

EOF
  exit 1;
}

use Getopt::Std;
$main::VERSION = 0;
$Getopt::Std::STANDARD_HELP_VERSION = 1;
our ($opt_c, $opt_h, $opt_C, $opt_T, $opt_F, $opt_K); # the variables for getopt
getopts('c:hCTFK') or usage;
$opt_c or usage;
$opt_h and usage;
my $t_level = 0;
$t_level += 2 if($opt_T);
$t_level += 4 if($opt_F);
$t_level += 8 if($opt_K);
$t_level += 1 if($opt_C || 0 == $t_level);



open LOG,">tests.log";

print "Loading\n";
my @tests = @ARGV != 0 ? @ARGV : dirs();
my $count = @tests;
print "  $count " . (1==$count?"test":"tests") . " found\n\n";

my $failures = 0;
my $skips = 0;
print "Running tests\n";
foreach my $test (@tests) {
  print "  Running $test";

  chdir $test;
  my $failed_skipped = test($test, "test.desc", $t_level, $opt_c);
  chdir "..";

  if($failed_skipped < 0) {
    $skips++;
    print "  [SKIPPED]\n";
  } elsif(0 == $failed_skipped) {
    print "  [OK]\n";
  } else {
    $failures++;
    print "  [FAILED]\n";
  }
}
print "\n";

if($failures == 0) {
  print "All tests were successful";
} else {
  print "Tests failed\n";
  print "  $failures of $count " . (1==$count?"test":"tests") . " failed";
}
print ", $skips " . (1==$skips?"test":"tests") . " skipped" if($skips > 0);
print "\n";


close LOG;

exit $failures;

