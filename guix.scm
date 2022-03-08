(use-modules (gnu packages agda)
             (guix build-system copy)
             (guix gexp)
             (guix git-download)
             ((guix licenses) #:prefix license:)
             (guix packages)
             (yellowsquid packages agda)
             (yellowsquid build-system agda))
(define %source-dir (dirname (current-filename)))

;; NOTE: still a dev build
(define agda-stdlib-2.0-dev
  (package
    (inherit agda-stdlib-1.7.1)
    (name "agda-stdlib")
    (version "2.0")
    (home-page "https://github.com/agda/agda-stdlib")
    (source (origin
              (method git-fetch)
              (uri (git-reference (url home-page)
                                  (commit "a9e97a33e2796d9ce4f8ed6da5a927ae33daf0b1")))
              (file-name (git-file-name name version))
              (sha256
               (base32
                "0m5f0x8jygvl9ackqpxxjx70kb2jb2qv6irj5wzxx8bd9q423m85"))))))

(define-public agda-helium
  (package
    (name "agda-helium")
    (version "0.1")
    (home-page "https://git.yellowsquid.uk/yellowsquid/helium.git")
    (source (local-file %source-dir
                        #:recursive? #t
                        #:select? (git-predicate %source-dir)))
    (build-system agda-build-system)
    (inputs (list agda-stdlib-2.0-dev))
    (synopsis "Semantics of the Arm M-profile Vector Extension (MVE) in Agda")
    (description "")
    (license license:expat)))

agda-helium
