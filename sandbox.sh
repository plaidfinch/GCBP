#!/bin/bash

cabal sandbox init
cabal install shake diagrams -fpgf diagrams-builder
