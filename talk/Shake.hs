import           Development.Shake
import           Development.Shake.FilePath

lhs2TeX, pdflatex :: String
lhs2TeX  = "lhs2TeX"
pdflatex = "pdflatex"

main :: IO ()
main = shake shakeOptions $ do

    want ["GCBP-talk.pdf"]

    "*.tex" %> \output -> do
        let input = replaceExtension output "lhs"
        need [input]
        cmd lhs2TeX $ ["-o", output] ++ [input]

    "*.pdf" %> \output -> do
        let input = replaceExtension output "tex"
        need [input, "Bijections.hs"]

        () <- cmd pdflatex $ ["--enable-write18", input]
        cmd pdflatex $ ["--enable-write18", input]
