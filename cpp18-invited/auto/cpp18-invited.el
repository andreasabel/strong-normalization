(TeX-add-style-hook
 "cpp18-invited"
 (lambda ()
   (TeX-add-to-alist 'LaTeX-provided-class-options
                     '(("acmart" "sigplan" "screen")))
   (TeX-run-style-hooks
    "latex2e"
    "acmart"
    "acmart10"
    "booktabs"
    "subcaption")
   (TeX-add-symbols
    '("showeprint" ["argument"] 1)
    '("natexlab" 1)
    '("bibinfo" 2)
    '("bibfield" 2))))

