(use-modules (gnu packages agda)
             (guix build-system copy)
             (guix gexp)
             (guix git-download)
             ((guix licenses) #:prefix license:)
             (guix packages)
             (yellowsquid packages agda)
             (yellowsquid build-system agda))
(define %source-dir (dirname (current-filename)))

(define-public agda-helium
  (package
    (name "agda-helium")
    (version "0.1")
    (home-page "https://git.yellowsquid.uk/yellowsquid/helium.git")
    (source (local-file %source-dir
                        #:recursive? #t
                        #:select? (git-predicate %source-dir)))
    (build-system agda-build-system)
    (inputs (list agda-stdlib-1.7.1))
    (synopsis "Semantics of the Arm M-profile Vector Extension (MVE) in Agda")
    (description "")
    (license license:expat)))

agda-helium
