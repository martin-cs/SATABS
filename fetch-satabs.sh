#!/bin/bash

git rebase -i
git pull --rebase
git svn -R svn-satabs fetch
git merge -s recursive -X ours remotes/svn-satabs/trunk

