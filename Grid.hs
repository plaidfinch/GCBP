{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE TemplateHaskell           #-}
{-# LANGUAGE TypeFamilies              #-}


module Grid where

import           Diagrams.Backend.Rasterific.CmdLine
import           Diagrams.Prelude

import           Data.List

data GridOpts = GridOpts
  { _colsep :: Double
  , _rowsep :: Double
  }

makeLenses ''GridOpts

instance Default GridOpts where
  def = GridOpts 0 0

grid :: (V a ~ V2, N a ~ Double, Transformable a, Enveloped a, Monoid a)
     => [[a]] -> a
grid = grid' def

grid' :: (V a ~ V2, N a ~ Double, Transformable a, Enveloped a, Monoid a)
      => GridOpts -> [[a]] -> a
grid' opts as = layoutCol . map layoutRow $ as
  where
    rowHts    = map (maximum . map height) as
    colWds    = map (maximum . map width) (transpose as)
    centers s = scanl (+) 0 . map (+s)

    layoutRow ds = mconcat $ zipWith translateX            (centers (opts ^. colsep) colWds) ds
    layoutCol ds = mconcat $ zipWith (translateY . negate) (centers (opts ^. rowsep) rowHts) ds

dias :: [[Diagram B]]
dias = [[circle 1, square 3, circle 10], [triangle 2, hexagon 1, circle 0.2]]
  # map (map centerXY)

main = mainWith $ grid' (with & colsep .~ 1 & rowsep .~ 3) dias
