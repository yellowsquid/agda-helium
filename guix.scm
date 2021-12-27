(use-modules (gnu packages agda)
             (guix build-system copy)
             (guix gexp)
             (guix git-download)
             ((guix licenses) #:prefix license:)
             (guix packages)
             (yellowsquid packages agda))
(define %source-dir (dirname (current-filename)))



(define-public agda-helium
  (package
    (name "agda-helium")
    (version "0.1")
    (home-page "https://git.yellowsquid.uk/yellowsquid/helium.git")
    (source (local-file %source-dir
                        #:recursive? #t
                        #:select? (git-predicate %source-dir)))
    (build-system copy-build-system)
    (inputs (list agda-stdlib))
    (native-inputs (list agda))
    (arguments
     `(#:install-plan
       '(("src" "/share/agda/lib/helium/" #:include-regexp ("\\.agdai?")))
       #:phases
       (modify-phases %standard-phases
         (add-before 'install 'build
           (lambda* (#:key inputs #:allow-other-keys)
             (call-with-output-file "libraries"
               (lambda (port)
                 (format port
                         "~a\n"
                         (string-append
                          (search-input-file
                           inputs
                           "/share/agda/lib/standard-library.agda-lib"))
                          port)
                 (display "./agda-helium.agda-lib\n" port)))
             (invoke "agda"
                     "--library-file=libraries"
                     "--library=agda-helium"
                     "-i."
                     "Everything.agda"))))))
    (synopsis "Semantics of the Arm M-profile Vector Extension (MVE) in Agda")
    (description "")
    (license license:expat)))

agda-helium
