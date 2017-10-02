(TeX-add-style-hook
 "sn-proof"
 (lambda ()
   (TeX-run-style-hooks
    "latex2e"
    "prelude"
    "article"
    "art10"
    "enumitem"
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
    '("ext" 1)
    '("hs" 1)
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
    "rv"
    "ednote")
   (LaTeX-add-labels
    "def:norm"
    "lem:psn"
    "pp2"
    "pp3"
    "pp4"
    "pp5"
    "pp6"
    "pp7"
    "cor:psn"
    "pp1"
    "lm:ecxt"
    "lm:closn"
    "cp2"
    "cp3"
    "cp3b"
    "cp5"
    "fig:sn"
    "csn1"
    "csn2"
    "fig:sncase")
   (LaTeX-add-environments
    '("SOLUTION" 1)
    '("ADDITIONAL" 1)
    "exercise"
    "problem"
    "sol"
    "axiom")))

