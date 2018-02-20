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
    "hole"
    "holetype"
    "one"
    "SN"
    "SNe"
    "csn"
    "CR"
    "mred"
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
    "lem:redsubst"
    "lm:mredprop"
    "lm:mredtrans"
    "lm:mredappl"
    "lm:mredappr"
    "lm:mredabs"
    "lm:mredsubs"
    "def:norm"
    "lm:mredsn"
    "lm:wksn"
    "lm:strsn"
    "lem:psn"
    "pp3"
    "pp4"
    "pp6"
    "pp7"
    "def:ectx"
    "lm:pectx"
    "def:snectx"
    "lm:psnectx"
    "lm:invrectx"
    "lm:mredecxt"
    "lm:ecxt"
    "lm:closn"
    "cp2"
    "cp3"
    "lem:appsnclosure"
    "fig:sn"
    "lm:renameSN"
    "lm:anti-renameSN"
    "lm:pSN0"
    "lm:pSN"
    "lm:bclosed"
    "lm:confsn"
    "lm:backclosn"
    "lem:SNsn"
    "csn1"
    "thm:redcand"
    "cr1"
    "cr2"
    "cr3"
    "sec:unit"
    "fig:sncase")
   (LaTeX-add-environments
    '("SOLUTION" 1)
    '("ADDITIONAL" 1)
    "problem"
    "sol"
    "axiom"
    "lemma"
    "theorem")
   (LaTeX-add-bibliographies
    "bibi-extract")
   (LaTeX-add-amsthm-newtheorems
    "exercise"))
 :latex)

