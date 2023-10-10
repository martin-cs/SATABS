# SATABS

SATABS ( https://www.cprover.org/satabs/ ) was a predicate abstraction
model checker built using the components of
CBMC ( https://github.com/diffblue/cbmc/ ).  The original version was
described in "SATABS: SAT-based Predicate Abstraction for ANSI-C", TACAS'05.

Active development ended before 2012 and after that there were a few
updates for new CBMC versions.  This is a snapshot of revision 408 and
dates from late 2015.  It is approximately the same state as the last
release, version 3.2.  I don't know if this is was the last revision.

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
free!  If it breaks, you get to keep both halves!

I have added a submodule for CBMC version 4.7 (with some fixes so it
builds) as is described in the documentation.  There is some evidence
(see commit history) that actually this version should be built with
4.8 or later but YMMV.
