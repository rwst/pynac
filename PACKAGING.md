Don't package versions that are newer than the one in the newest Sage beta. If you really insist don't use github's default tarballs, use the one that is created with "make dist", which is always on top of the release tarball list.

### Why not package newer versions?

Pynac is not an independent library. Every Pynac version is associated with a specific Sage version, because the library interface changes frequently. Versions that are newer than the one in the newest Sage beta may need the Pynac upgrade ticket branch in Sage trac (search for pynac). The upgrade ticket also always has a link to the correct official Pynac tarball. The ticket may also have last-minute fixes as patches---of course they are also in Pynac-github master but they probably don't warrant a new release.
