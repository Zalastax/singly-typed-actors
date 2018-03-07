#!/usr/bin/env perl

use strict;
use warnings;

use Regexp::Common;

my $bp = $RE{balanced}{-parens=>'{}'};
my $tag_prefix = "AgdaTag";
my $underscore = "AgdaUnderscore";
my $dash = "AgdaDash";
my $commands   = qr"(InductiveConstructor|CoinductiveConstructor\
                    |Datatype|Field|Function|Module|Postulate|Record)";
my $refs   = qr"(Target|Ref)";

while (<>) {

  s|(\\Agda$commands)($bp)

   | my $cmd = $1;
     $3 =~ /\{(.*)\}/;
     my $arg = $1;
     my $tag = "$tag_prefix-$arg" =~ s/\\_/$underscore/gr =~ s/\{-\}/$dash/gr;

     $_ = "%\n%<*$tag>\n$cmd\{$arg\}%\n%</$tag>\n";
   |gxe;
  
  s|(\\Agda$refs(?:\[.*?\])?)($bp)

   | my $cmd = $1;
     $3 =~ /\{(.*)\}/;
     my $arg = $1;
     my $fixed = $arg =~ s/_/$underscore/gr =~ s/-/$dash/gr;
     $_ = "$cmd\{$fixed\}";
    |gxe;

  print;

}
