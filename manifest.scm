(use-modules
 (guix)
 (gnu packages agda)
 (gnu packages emacs)
 (gnu packages haskell)
 (gnu packages haskell-xyz)
 (gnu packages version-control))

(packages->manifest
 (list
  agda
  emacs
  emacs-agda2-mode
  ghc
  ghc-ieee754
  git
  ))
