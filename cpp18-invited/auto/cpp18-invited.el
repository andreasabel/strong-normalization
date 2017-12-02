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
   (LaTeX-add-bibliographies
    "cpp")))

