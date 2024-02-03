# SATABS

SATABS ( https://www.cprover.org/satabs/ ) was a predicate abstraction
model checker built using the components of
CBMC ( https://github.com/diffblue/cbmc/ ).  The original version was
described in "SATABS: SAT-based Predicate Abstraction for ANSI-C", TACAS'05.

This repository also contains the boppo model checker, an early
version of the loopfrog loop and function summarising tool and the tan
termination checker.

This is a snapshot of revision 506 from 13th December 2015 and is the
last known version. The last released version was 3.2 but it is not
clear which revision this was.

At some point between early 2016 and 2018 or so, the subversion server
hosting the source code was decommissioned and the source code is no
longer available.  Every year or so, someone asks where the source
code is so I am posting the version I have.

This is not my work.  The DOxygen lists the following people as authors:

Alastair Donaldson
Aliaksei Tsitovich
CM Wintersteiger
Daniel Kroening
Georg Weissenbacher
Michael Tautschnig
Karen Yorav

The website also includes:

Alexander Kaiser
Natasha Sharygina
Thomas Wahl

This is not going to be my work.  The repository is hosted for
archival and archaeological purposes only.  I'm not going to update it
to the latest CBMC.  I'm not going to fix bugs.  If you want to, feel
free!  If it breaks, you get to keep both halves!  If it works, send
me a link!

The COMPILING instructions are incorrect; this will not build with
CBMC 4.7.  The "right" version is unclear but based on file renaming
and the dates of commits, it must be between:

a2f1fad8d638ec9fe30aa07b2ed77acb12f696d4 2015-12-13 12:22:17
81d28e7009fcf71c9a958d76414f433baf2b516e 2015-02-04 19:22:53

inclusive.  This time period includes three releases, 5.1, 5.2 and
5.3.  I have added a submodule for CBMC version 5.3 (with some fixes
so it builds) and it seems to build.  YMMV.
