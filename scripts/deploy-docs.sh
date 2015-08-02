#!/usr/bin/env bash

cwd="$( cd "${BASH_SOURCE[0]%/*}" && pwd )"
cd "$cwd/.."
f=`mktemp -d`
git clone "git@github.com:relrod/idris-split.git" "$f/idris-split.git"
idris --mkdoc split.ipkg
pushd "$f/idris-split.git"
  git checkout gh-pages && git rm -rf *
popd
mv split_doc/* "$f/idris-split.git/"
pushd "$f/idris-split.git"
  git add -A
  git commit -m "Manual docs deploy."
  git push origin gh-pages
popd
rm -rf "$f"

if [ $? == 0 ]; then
  echo "*** Done: http://relrod.github.io/idris-split/"
  exit 0
else
  echo "*** ERROR!!! Fix the above and try again."
  exit 1
fi