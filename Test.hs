import           Bijections
import           Diagrams.Backend.Rasterific.CmdLine
import           Diagrams.Prelude

main = defaultMain $ drawBComplex (bij01'c)
  where
    cm = orbitsToColorMap [green, red, yellow, pink, orange] (bijToRel bij0)
    bij0c = colorBij cm bij0
    bij01'c = bc01 +- (reversing bij0c +++ empty) -.. (a0 +++ a1)
