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
   (subcommands
    (list
     (configuration
      (name 'calculate-gains)
      (alias 'calc)
      (wanted '((keywords out target))))
     (configuration
      (name 'update!)
      (alias 'upd!)
      (wanted '((keywords out target)))
      (keywords
       (list
        (switch
         (name 'enact)
         (default #f)
         (test boolean?)
         (synopsis "Actually perform the updates."))))
      (description  "Perform the membership payment increase.

Out in this context refers to the source file for the updates to be
performed."))))
   (synopsis "Tool to prep and carry out our membership dues increase.")))

;;;; Calculators

(define (derive-new-amount sub)
  (match (map (cute <> sub)
              `(,subscription-interval_unit ,subscription-interval))
    ;; - Annually -> 8800
    ;;   + (yearly . 1)
    ;;   + (monthly . 12)
    ((or ("monthly" 12) ("yearly" 1)) 8800)
    ;; - Bi-Annually -> 4400
    ;;   + (monthly . 6)
    ((or ("monthly" 6)) 4400)
    ;; - Quarterly -> 2200
    ;;   + (monthly . 3)
    ((or ("monthly" 3)) 2200)
    ;; - Monthly -> 800
    ;;   + monthly 1
    ((or ("monthly" 1)) 800)
    (e (throw 'selector "unexpected interval_unit:" e))))

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

;;;; Reporters
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
       (new_amount . ,(derive-new-amount sub))
       (sub_id . ,(subscription-id sub))))))

;;;; Main

(define (main cmdline)
  (let* ((options (getopt-config-auto cmdline %configuration))
         (filename (string-append (option-ref options 'out) "Candidates-"
                                  (option-ref options 'target) ".scm"))
         (secret (with-input-from-file "./secrets.scm"
                   (lambda _
                     (assoc-ref (read) (option-ref options 'target))))))

    (match (full-command options)
      (("script")
       (let (;; Generate Concessionary Blacklist Indexes
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
               (with-output-to-file filename
                 (lambda _
                   (for-each full-candidate-report
                             (and=> (concessionary-filter conc-blckl candidates)
                                    (cute not-contactable-filter nc-blckl <>)))))
               (format #t "Written to: ~a~%" filename))))))
      (("script" "update!")
       (parameterize ((access-token (string-append "Bearer " secret))
                       (base-host (match (option-ref options 'target)
                                    ("sandbox" (base-host))
                                    (_ (build-uri 'https
                                                  #:host "api.gocardless.com"))))
                       (debug? (not (option-ref options 'enact))))
          (with-input-from-file filename
            (lambda _
              (let ((in (let lp ((content '())
                                 (current (read)))
                          (if (eof-object? current)
                              (reverse content)
                              (lp (cons current content)
                                  (read))))))
                (format (current-output-port) "Updating ~a subscriptions.~%"
                        (length in))
                (let lp ((done '())
                         (errors '())
                         (outstanding in))
                  (if (null? outstanding)
                      (begin
                        (pretty-print (reverse done) (current-output-port))
                        (pretty-print (reverse errors) (current-error-port))
                        (format (current-output-port) "Done~%"))
                      (let ((current (first outstanding))
                            (rest (cdr outstanding)))
                        (catch #t
                          (lambda _
                            (format (current-output-port) "Working on ~a (~a)..."
                                    (assoc-ref current 'email)
                                    (assoc-ref current 'sub_id))
                            (let ((result (update-subscription
                                           (assoc-ref current 'sub_id)
                                           (assoc-ref current 'sub_id)
                                           #:amount (assoc-ref current 'new_amount))))
                              (format (current-output-port) "[DONE]~%")
                              (lp (cons `((customer . ,current)
                                          (response . ,result))
                                        done)
                                  errors
                                  rest)))
                          (lambda (key . args)
                            (format (current-output-port) "[ERROR]~%")
                            (lp done
                                (cons `((customer . ,current)
                                        (response . ,args))
                                      errors)
                                rest)))))))))))
      (("script" "calculate-gains")
       (with-input-from-file filename
         (lambda _
           (format (current-output-port)
                   "We would gain ~a GBP over 1 year.~%"
                   (/ (fold (lambda (entry total)
                              (+ total
                                 (* (- (assoc-ref entry 'new_amount)
                                       (assoc-ref entry 'amount))
                                    (match (list (assoc-ref entry 'interval_unit)
                                                 (assoc-ref entry 'interval))
                                      ;; - Annually -> * 1
                                      ;;   + (yearly . 1)
                                      ;;   + (monthly . 12)
                                      ((or ("monthly" 12) ("yearly" 1)) 1)
                                      ;; - Bi-Annually -> * 2
                                      ;;   + (monthly . 6)
                                      ((or ("monthly" 6)) 2)
                                      ;; - Quarterly -> * 4
                                      ;;   + (monthly . 3)
                                      ((or ("monthly" 3)) 4)
                                      ;; - Monthly -> * 12
                                      ;;   + monthly 1
                                      ((or ("monthly" 1)) 12)
                                      (e (throw 'selector "unexpected interval_unit:"
                                                e))))))
                            0 (let lp ((content '())
                                       (current (read)))
                                (if (eof-object? current)
                                    (reverse content)
                                    (lp (cons current content)
                                        (read)))))
                      100.00))))))))

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
