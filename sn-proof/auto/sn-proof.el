(TeX-add-style-hook
 "sn-proof"
 (lambda ()
   (TeX-add-to-alist 'LaTeX-provided-package-options
                     '(("natbib" "authoryear")))
   (add-to-list 'LaTeX-verbatim-environments-local "lstlisting")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "lstinline")
   (add-to-list 'LaTeX-verbatim-macros-with-delims-local "lstinline")
   (TeX-run-style-hooks
    "latex2e"
    "prelude"
    "article"
    "art10"
    "lmodern"
    "enumitem"
    "natbib"
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
    '("inden" 3)
    '("denot" 1)
    '("neu" 2)
    '("nf" 2)
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
    "id"
    "wk"
    "A"
    "zero"
    "lv"
    "rv"
    "ednote")
   (LaTeX-add-labels
    "lem:redprop"
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
    "lm:renameSN"
    "lm:anti-renameSN"
    "lem:SNsubst"
    "lm:pSN"
    "lm:pSN1"
    "lm:pSN2"
    "csn1"
    "csn2"
    "thm:redcand"
    "cr1"
    "cr2"
    "cr3"
    "fig:sncase")
   (LaTeX-add-environments
    '("SOLUTION" 1)
    '("ADDITIONAL" 1)
    "problem"
    "sol"
    "axiom"
    "lemma")
   (LaTeX-add-bibliographies
    "../../bibliography/bibi"
    "../../bibliography/bp")
   (LaTeX-add-amsthm-newtheorems
    "exercise")))

