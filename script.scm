#!/run/current-system/profile/bin/env guile
!#

(add-to-load-path (string-append (getenv"HOME") "/src/guile-gocardless/"))

(define-module (script)
  #:use-module (config)
  #:use-module (config api)
  #:use-module (config licenses)
  #:use-module (config parser sexp)
  #:use-module (dsv)
  #:use-module (gocardless)
  #:use-module (ice-9 pretty-print)
  #:use-module (ice-9 match)
  #:use-module (ice-9 futures)
  #:use-module (ice-9 threads)
  #:use-module (srfi srfi-1)
  #:use-module (srfi srfi-9)
  #:use-module (srfi srfi-19)
  #:use-module (srfi srfi-26)
  #:use-module (web uri)
  #:export ())

(define %configuration
  (configuration
   (name 'script)
   (keywords
    (list
     (switch
      (name 'out) (example "/path/to/out-file-directory")
      (default (string-append (getenv "HOME") "/tmp/"))
      (synopsis "Directory to write the CSV file to."))
     (switch
      (name 'blacklists) (example "/path/to/blacklist/csvs")
      (default (string-append (getenv "HOME") "/fawcett/rituals/members+/blacklists/"))
      (synopsis "Source for our blacklists."))
     (switch
      (name 'target) (example "sandbox|standard|pro")
      (default "sandbox")
      (synopsis "Account for which to generate the payfile."))))
   (synopsis "Easily generate a Gocardless payfile reconciliation.")))

;;;; API Filter

(define (selector sub)
  ;; Conditions for selection
  ;; Either:
  (match (map (cute <> sub)
              `(,subscription-interval_unit ,subscription-interval))
    ;; - Annually && < x 8800
    ;;   + (yearly . 1)
    ;;   + (monthly . 12)
    ((or ("monthly" 12) ("yearly" 1))
     (< (subscription-amount sub) 8800))
    ;; - Bi-Annually && < x 4400
    ;;   + (monthly . 6)
    ((or ("monthly" 6))
     (< (subscription-amount sub) 4400))
    ;; - Quarterly && < x 2200
    ;;   + (monthly . 3)
    ((or ("monthly" 3))
     (< (subscription-amount sub) 2200))
    ;; - Monthly && < x 800
    ;;   + monthly 1
    ((or ("monthly" 1))
     (< (subscription-amount sub) 800))
    (e (throw 'selector "unexpected interval_unit:" e))))

;;;; Blacklist Filters
(define (concessionary-filter conc-blckl candidates)
  (filter (lambda (candidate)
            (let ((cust (assq-ref candidate 'customer))
                  (sub (assq-ref candidate 'subscription)))
              ;; Custom URN
              (not
               (any (cute <> <>)
                    `(,(lambda (stmnt-1-idx)
                         (or (hash-ref stmnt-1-idx
                                       (access cust 'metadata 'URN))
                             (hash-ref stmnt-1-idx
                                       (subscription-id sub))))
                      ,(lambda (stmnt-2-idx)
                         (or (hash-ref stmnt-2-idx
                                       (access cust 'metadata 'URN))
                             (hash-ref stmnt-2-idx
                                       (subscription-id sub))))
                      ,(lambda (email-idx)
                         (hash-ref email-idx (customer-email cust)))
                      ,(lambda (keyname-idx)
                         (hash-ref keyname-idx
                                   (customer-family_name cust))))
                    conc-blckl))))
          candidates))

(define (not-contactable-filter nc-blckl candidates)
  (filter (lambda (candidate)
            (let ((cust (assq-ref candidate 'customer))
                  (sub (assq-ref candidate 'subscription)))
              ;; Custom URN
              (not
               (any (cute <> <>)
                    `(,(lambda (stmnt-1-idx)
                         (or (hash-ref stmnt-1-idx
                                       (access cust 'metadata 'URN))
                             (hash-ref stmnt-1-idx
                                       (subscription-id sub))))
                      ,(lambda (stmnt-2-idx)
                         (or (hash-ref stmnt-2-idx
                                       (access cust 'metadata 'URN))
                             (hash-ref stmnt-2-idx
                                       (subscription-id sub))))
                      ,(lambda (keyname-idx)
                         (hash-ref keyname-idx
                                   (customer-family_name cust))))
                    nc-blckl))))
          candidates))

(define (analysis subs)
  (format #t "All Monthly, Annually? ~a ~%"
          (every (lambda (sub)
                   (and (= 1 (subscription-interval sub))
                        (member (subscription-interval_unit sub)
                                '("monthly" "yearly"))))
                 subs))
  (format #t "Those not Monthly, Annually: ~a ~%"
          (filter-map (lambda (sub)
                        (if (and (= 1 (subscription-interval sub))
                                 (member (subscription-interval_unit sub)
                                         '("monthly" "yearly")))
                            #f
                            (cons (subscription-interval_unit sub)
                                  (subscription-interval sub))))
                      subs)))

;;;; Candidate data structure

(define (candidate customer subscription)
  `((customer . ,customer)
    (subscription . ,subscription)))

;; This one is slow because it makes ton of requests to the API!
(define (derive-candidate subscription)
  (candidate (customers
              (get-customer
               (mandate-links-customer
                (mandates
                 (get-mandate
                  (subscription-links-mandate subscription))))))
             subscription))

;; This one is fast but requires us to have collected all mandates and
;; customers
(define (local-derive-candidate subscription mans custs)
  (let ((mtable (let ((htable (make-hash-table)))
                  (for-each (lambda (m)
                              (hash-set! htable (mandate-id m) m))
                            mans)
                  htable))
        (ctable (let ((htable (make-hash-table)))
                  (for-each (lambda (c)
                              (hash-set! htable (customer-id c) c))
                            custs)
                  htable)))
    (candidate
     (hash-ref
      ctable (mandate-links-customer
              (hash-ref
               mtable (subscription-links-mandate subscription))))
     subscription)))

(define (full-candidate-report candidate)
  ;; A candidate is an assoc consisting of
  ;; '((customer . $cust) (subscription . $sub))
  (let ((cust (assq-ref candidate 'customer))
        (sub (assq-ref candidate 'subscription)))
    (pretty-print
     `((email . ,(customer-email cust))
       (surname . ,(customer-family_name cust))
       (firstname . ,(customer-given_name cust))
       ;; FIXME: Needs to be set correctly for GC Context
       (cust_urn . ,(access cust 'metadata 'URN))
       ;; Standard has no URN
       (interval . ,(subscription-interval sub))
       (interval_unit . ,(subscription-interval_unit sub))
       (amount . ,(subscription-amount sub))
       (sub_id . ,(subscription-id sub))))))

;;;; CSV Utilities

(define (scm->hash-table index-proc in)
  (let ((htable (make-hash-table)))
    (for-each (lambda (n)
                (hash-set! htable (index-proc n) n))
              in)
    htable))

(define (csv-assoc header lst key)
  (cons key (csv-assoc-ref key lst header)))

(define (csv-assoc-ref key lst header)
  (list-ref lst (or (list-index (cute equal? <> key) header)
                    (throw 'tst key lst))))

;;;; Main

(define (main cmdline)
  (let* ((options (getopt-config-auto cmdline %configuration))
         (secret (with-input-from-file "./secrets.scm"
                   (lambda _
                     (assoc-ref (read) (option-ref options 'target)))))
         (filename (string-append "membership+"
                                  (string-upcase (option-ref options 'target))
                                  "-"
                                  (date->string (current-date) "~1_~H~M~S")
                                  ".scm"))
         ;; Generate Concessionary Blacklist Indexes
         (conc-blckl (with-input-from-file (string-append (option-ref options 'blacklists)
                                                          "Concessionary-Blacklist.csv")
                       (lambda _
                         (let ((in (dsv->scm (current-input-port) #\, #:format 'rfc4180)))
                           (list
                            (scm->hash-table
                             (cute csv-assoc-ref "Statement Text 1" <> (first in))
                             (cdr in))
                            (scm->hash-table
                             (cute csv-assoc-ref "Statement Text 2" <> (first in))
                             (cdr in))
                            (scm->hash-table
                             (cute csv-assoc-ref "Email" <> (first in))
                             (cdr in))
                            (scm->hash-table
                             (cute csv-assoc-ref "Key Name" <> (first in))
                             (cdr in)))))))
         (nc-blckl (with-input-from-file (string-append (option-ref options 'blacklists)
                                                        "Not-Contactable-blacklist.csv")
                     (lambda _
                       (let ((in (dsv->scm (current-input-port) #\, #:format 'rfc4180)))
                         (list
                          (scm->hash-table
                           (cute csv-assoc-ref "Statement Text 1" <> (first in))
                           (cdr in))
                          (scm->hash-table
                           (cute csv-assoc-ref "Statement Text 2" <> (first in))
                           (cdr in))
                          (scm->hash-table
                           (cute csv-assoc-ref "Keyname" <> (first in))
                           (cdr in))))))))
    ;; Fetch our data pool
    (parameterize ((access-token (string-append "Bearer " secret))
                   (base-host (match (option-ref options 'target)
                                ("sandbox" (base-host))
                                (_ (build-uri 'https
                                              #:host "api.gocardless.com"))))
                   (debug? #f))
      (format #t "Fetching Subscriptions, Mandates & Customers from API...")
      (let ((subs (gc:map (lambda* (#:key limit after)
                            (list-subscriptions #:limit limit #:after after
                                                #:status "active"))
                          subscriptions
                          identity))
            (mans (gc:map (lambda* (#:key limit after)
                            (list-mandates #:limit limit #:after after))
                          mandates
                          identity))
            (custs (gc:map (lambda* (#:key limit after)
                             (list-customers #:limit limit #:after after))
                           customers
                           identity)))
        (format #t "[DONE]~%")
        ;; (analysis subs)                 ; Reveal interval info
        ;; Basic Job Info
        (format #t "Full count: ~a - Candidate count: ~a~%"
                (length subs)
                (length (filter selector subs)))
        (let ((candidates (map (cute local-derive-candidate <> mans custs)
                               (filter selector subs))))
          (format
           #t "Candidate count: ~a~%  Post-conc count: ~a~%Filtered count: ~a~%"
           (length candidates)
           ;; Filter against conc-blckls
           (length (concessionary-filter conc-blckl candidates))
           ;; Filter against conc-blckls & nc-blckl
           (length (and=> (concessionary-filter conc-blckl candidates)
                          (cute not-contactable-filter nc-blckl <>))))
          (let ((out-name (string-append (option-ref options 'out)
                                         "Candidates-"
                                         (option-ref options 'target)
                                         ".scm")))
            (with-output-to-file out-name
              (lambda _
                (for-each full-candidate-report
                          (and=> (concessionary-filter conc-blckl candidates)
                                 (cute not-contactable-filter nc-blckl <>)))))
            (format #t "Written to: ~a~%" out-name)))))))

;; Sandbox!
;; (main '("script" "-t" "sandbox"))

;; Of roughly 302 subs on standard, 251 are candidates for update
;; (main '("script" "-t" "standard"))

;; Of roughly 2479 subs on Pro, 2139 are candidates for update
;; (main '("script" "-t" "pro"))

(main (command-line))

;;;; Requirements:
;;
;; For each candidate, I require:
;; - Sub request: interval, interval_unit, sub ID,
;; - Linked Person request: email addr, surname, firstname, custom URN
;;
;;;; Lemma: Advanced filtering
;;
;;;;; Cross-referencing against blacklist
;;
;; We have a blacklist keyed by email address.
;;
;; We must cross-ref each candidate against this blacklist.
;;
;; If candidate is member of blacklist, remove from candidate list.
;;
;;;;; Cross-referencing against concessionary membership type
;;
;; We have a list of all Concessionary memberships, keyed by
;; a) Statement Text 1 (sub ID, custom URN)
;; b) Statement Text 2 (sub ID, custom URN)
;; c) email
;; d) surname (if more than one match -> firstname)
;;
;; For each candidate in concessionary, remove from candidate list.
;;
;;;;; Cross-referencing against non-contactables
;;
;; We have a list of all non-contacable pledges, keyed by
;; a) Statement Text 1 (sub ID, custom URN)
;; b) Statement Text 2 (sub ID, custom URN)
;; d) surname (if more than one match -> firstname)
;;
;; For each candidate in concessionary, remove from candidate list.
;;
;;;;; Result
;;
;; I will be left with a candidate list of people whose sub must be increased.
;;
;;;; Create new sub data
;;
;; We require: Sub ID, new amount.
;;
;; New amount is generated from:
;; - old interval
;; - old interval_unit
;;
;; e.g. if interval_unit=month & interval=3, then new amount is:
;; - ruleset: (quarterly . 22)        [Because (/ 88 4) -> 22]
;; e.g. if interval_unit=month & interval=6, then new amount is:
;; - ruleset: (biannually . 44)       [Because (/ 88 2) -> 44]
;; e.g. if interval_unit=month & interval=1, then new amount is:
;; - ruleset: (monthly . 8)           [Because -> 8]
;; e.g. if interval_unit=yearly & interval=1, then new amount is:
;; - ruleset: (annual . 88)           [Because 88]
;;
;;;; Submit to GoCardless
;;
;; Put with Sub ID, new amount
;;
