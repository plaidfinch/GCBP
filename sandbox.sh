#!/bin/bash

cabal sandbox init
cabal install shake -fpgf -frasterific diagrams diagrams-builder random-shuffle QuickCheck
