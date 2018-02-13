#!/bin/sh

stack build shake diagrams diagrams-builder random-shuffle QuickCheck
stack runghc Shake.hs
