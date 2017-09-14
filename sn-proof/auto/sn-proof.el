(TeX-add-style-hook
 "sn-proof"
 (lambda ()
   (TeX-run-style-hooks
    "latex2e"
    "prelude"
    "article"
    "art10"
    "amsmath"
    "amsthm"
    "latexsym"
    "amsfonts"
    "listings"
    "srcltx"
    "charter"
    "euler"
    "amssymb"
    "comment"
    "proof"
    "cdsty"
    "graphics"
    "graphicx"
    "lstextract")
   (TeX-add-symbols
    '("Den" ["argument"] 2)
    '("recnat" 3)
    '("caseof" 3)
    '("dent" 2)
    '("den" 1)
    '("clos" 1)
    "nl"
    "B"
    "C"
    "G"
    "Q"
    "SN"
    "SNe"
    "csn"
    "CR"
    "red"
    "redsn"
    "redSN"
    "imply"
    "A"
    "zero"
    "lv"
    "rv")
   (LaTeX-add-labels
    "def:norm"
    "fig:sn"
    "fig:sncase")
   (LaTeX-add-environments
    '("SOLUTION" 1)
    '("ADDITIONAL" 1)
    "exercise"
    "problem"
    "sol"
    "axiom")))

