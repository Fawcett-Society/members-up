#!/run/current-system/profile/bin/env guile
!#

;;; Commentary
;;
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
;;; Code:

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
performed."))
     (configuration
      (name 'create!)
      (alias 'crt!)
      (wanted '((keywords out target)))
      (keywords
       (list
        (switch
         (name 'enact)
         (default #f)
         (test boolean?)
         (synopsis "Actually perform the updates against standard."))))
      (description  "Perform the membership payment increase in Standard context.

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

(define (gc-clean-custom-reference urn)
  ;; If we have trailing "/[0-9]", store it.
  (if urn
      (let* ((clean (string-split urn #\/))
             (suffix (match clean
                       ((a b) (string-append "/" b))
                       (_ ""))))
        ;; If our URN has leading 0s, strip them.
        (string-append (match (string->number (first clean))
                         (#f urn)
                         (num (number->string num)))
                       suffix))
      #f))

;;;; Blacklist Filters
(define (concessionary-filter conc-blckl candidates)
  (let ((stmnt-1-matches 0)
        (stmnt-2-matches 0)
        (email-matches 0)
        (keyname-matches 0))
    (let ((result
           (filter (lambda (candidate)
                     (let ((cust (assq-ref candidate 'customer))
                           (sub (assq-ref candidate 'subscription)))
                       ;; Custom URN
                       (not
                        (any (cute <> <>)
                             `(,(lambda (stmnt-1-idx)
                                 (if (or (hash-ref stmnt-1-idx
                                                   (gc-clean-custom-reference
                                                    (access cust 'metadata 'custom_reference)))
                                         (hash-ref stmnt-1-idx
                                                   (subscription-id sub)))
                                     (begin
                                       (set! stmnt-1-matches (1+ stmnt-1-matches))
                                       #t)
                                     #f))
                              ,(lambda (stmnt-2-idx)
                                 (if (or (hash-ref stmnt-2-idx
                                                   (access cust 'metadata 'custom_reference))
                                         (hash-ref stmnt-2-idx
                                                   (subscription-id sub)))
                                     (begin
                                       (set! stmnt-2-matches (1+ stmnt-2-matches))
                                       #t)
                                     #f))
                              ,(lambda (email-idx)
                                 (if (hash-ref email-idx
                                               (string-downcase
                                                (customer-email cust)))
                                     (begin
                                       (set! email-matches (1+ email-matches))
                                       #t)
                                     #f))
                              ,(lambda (keyname-idx)
                                 (if (hash-ref keyname-idx
                                               (string-append
                                                (string-downcase
                                                 (customer-given_name cust))
                                                (string-downcase
                                                 (customer-family_name cust))))
                                     (begin
                                       (set! keyname-matches (1+ keyname-matches))
                                       #t)
                                     #f)))
                             conc-blckl))))
                   candidates)))
      (format #t "Statement 1 matches: ~a; Statement 2 matches: ~a; Email matches: ~a; Keyname matches: ~a.~%"
              stmnt-1-matches stmnt-2-matches email-matches keyname-matches)
      result)))

(define (not-contactable-filter nc-blckl candidates)
  (let ((stmnt-1-matches 0)
        (stmnt-2-matches 0)
        (keyname-matches 0))
    (let ((result
           (filter (lambda (candidate)
                     (let ((cust (assq-ref candidate 'customer))
                           (sub (assq-ref candidate 'subscription)))
                       ;; Custom URN
                       (not
                        (any (cute <> <>)
                             `(,(lambda (stmnt-1-idx)
                                  (if (or (hash-ref stmnt-1-idx
                                                    (gc-clean-custom-reference
                                                     (access cust 'metadata 'custom_reference)))
                                          (hash-ref stmnt-1-idx
                                                    (subscription-id sub)))
                                      (begin
                                        (set! stmnt-1-matches (1+ stmnt-1-matches))
                                        #t)
                                      #f))
                               ,(lambda (stmnt-2-idx)
                                  (if (or (hash-ref stmnt-2-idx
                                                    (gc-clean-custom-reference
                                                     (access cust 'metadata 'custom_reference)))
                                          (hash-ref stmnt-2-idx
                                                    (subscription-id sub)))
                                      (begin
                                        (set! stmnt-2-matches (1+ stmnt-2-matches))
                                        #t)
                                      #f))
                               ,(lambda (keyname-idx)
                                  (if (hash-ref keyname-idx
                                                (string-append
                                                 (string-downcase
                                                  (customer-given_name cust))
                                                 (string-downcase
                                                  (customer-family_name cust))))
                                      (begin
                                        (set! keyname-matches (1+ keyname-matches))
                                        #t)
                                      #f)))
                             nc-blckl))))
                   candidates)))
      (format #t "Statement 1 matches: ~a; Statement 2 matches: ~a; Keyname matches: ~a.~%"
              stmnt-1-matches stmnt-2-matches keyname-matches)
      result)))

(define (opt-out-filter oo-blckl candidates)
  (let ((email-matches 0)
        (keyname-matches 0))
    (let ((result
           (filter (lambda (candidate)
                     (let ((cust (assq-ref candidate 'customer))
                           (sub (assq-ref candidate 'subscription)))
                       ;; Custom URN
                       (not
                        (any (cute <> <>)
                             `(,(lambda (email-idx)
                                  (if (hash-ref email-idx
                                                (string-downcase
                                                 (customer-email cust)))
                                      (begin
                                        (set! email-matches (1+ email-matches))
                                        #t)
                                      #f))
                               ,(lambda (keyname-idx)
                                  (if (hash-ref keyname-idx
                                                (string-append
                                                 (string-downcase
                                                  (customer-given_name cust))
                                                 (string-downcase
                                                  (customer-family_name cust))))
                                      (begin
                                        (set! keyname-matches (1+ keyname-matches))
                                        #t)
                                      #f)))
                             oo-blckl))))
                   candidates)))
      (format #t "Email matches: ~a; Keyname matches: ~a.~%"
              email-matches keyname-matches)
      result)))

;;;; Candidate data structure

(define (candidate customer subscription mandate)
  `((customer . ,customer)
    (subscription . ,subscription)
    (mandate . ,mandate)))

;; This one is slow because it makes ton of requests to the API!
(define (derive-candidate subscription)
  (let ((mandate (mandates
                  (get-mandate (subscription-links-mandate subscription)))))
    (candidate (customers (get-customer (mandate-links-customer mandate)))
               subscription mandate)))

;; This one is fast but requires us to have collected all mandates and
;; customers
(define (local-derive-candidate subscription mans custs)
  (let* ((mtable (let ((htable (make-hash-table)))
                   (for-each (lambda (m)
                               (hash-set! htable (mandate-id m) m))
                             mans)
                   htable))
         (ctable (let ((htable (make-hash-table)))
                   (for-each (lambda (c)
                               (hash-set! htable (customer-id c) c))
                             custs)
                   htable))
         (mandate (hash-ref mtable
                            (subscription-links-mandate subscription))))
    (candidate (hash-ref ctable (mandate-links-customer mandate))
               subscription mandate)))

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
        (sub (assq-ref candidate 'subscription))
        (man (assq-ref candidate 'mandate)))
    (pretty-print
     `((email . ,(customer-email cust))
       (surname . ,(customer-family_name cust))
       (firstname . ,(customer-given_name cust))
       ;; FIXME: Needs to be set correctly for GC Context
       (cust_urn . ,(access cust 'metadata 'URN))
       (cust_statement_text_1
        . ,(access cust 'metadata 'custome_reference))
       (metadata . ,(rsp->assoc (access cust 'metadata)))
       (interval . ,(subscription-interval sub))
       (interval_unit . ,(subscription-interval_unit sub))
       (day_of_month . ,(subscription-day_of_month sub))
       (amount . ,(subscription-amount sub))
       (new_amount . ,(derive-new-amount sub))
       (sub_id . ,(subscription-id sub))
       (man_id . ,(mandate-id man))))))

(define (generate-source-files filename secret options)
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
                            (compose string-downcase
                                     (cute csv-assoc-ref "Email" <> (first in)))
                            (cdr in))
                           (scm->hash-table
                            (lambda (row)
                              (string-append
                               (string-downcase
                                (csv-assoc-ref "First Name" row (first in)))
                               (string-downcase
                                (csv-assoc-ref "Key Name" row (first in)))))

                            (cdr in)))))))
        ;; Generate the non-contactable Blacklist Indexes
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
                          (lambda (row)
                            (string-append
                             (string-downcase
                              (csv-assoc-ref "First Name" row (first in)))
                             (string-downcase
                              (csv-assoc-ref "Keyname" row (first in)))))
                          (cdr in)))))))
        ;; Generate Opt Out Blacklist Indexes
        (oo-blckl (with-input-from-file (string-append (option-ref options 'blacklists)
                                                       "Follow-Up-Blacklist.csv")
                    (lambda _
                      (let ((in (dsv->scm (current-input-port) #\, #:format 'rfc4180)))
                        (list
                         (scm->hash-table
                          (compose string-downcase
                                   (cute csv-assoc-ref "Email" <> (first in)))
                          (cdr in))
                         (scm->hash-table
                          (lambda (row)
                            (string-append
                             (string-downcase
                              (csv-assoc-ref "First Name" row (first in)))
                             (string-downcase
                              (csv-assoc-ref "Surname" row (first in)))))
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
        (let* ((candidates (map (cute local-derive-candidate <> mans custs)
                                (filter selector subs)))
               ;; Filter against conc-blckls
               (conc-filtered (concessionary-filter conc-blckl candidates))
               ;; Filter against conc-blckls & nc-blckl
               (nc-filtered (not-contactable-filter nc-blckl conc-filtered))
               ;; Filter against conc-blckls, nc-blckl & oo-blckl
               (oo-filtered (opt-out-filter oo-blckl nc-filtered)))
          (format
           #t "
Candidate count: ~a
  Post-conc count: ~a
  Post-conc/Post-nc count: ~a
Filtered count: ~a
"
           (length candidates) (length conc-filtered)
           (length nc-filtered) (length oo-filtered))
          (with-output-to-file filename
            (lambda _
              (for-each full-candidate-report
                        oo-filtered)))
          (format #t "Written to: ~a~%" filename))))))

(define (update-pro! filename secret options)
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
          (let ((errors-file
                 (open-file
                  (string-append (option-ref options 'out)
                                 "Errors-"
                                 (option-ref options 'target)
                                 ".scm")
                  "a"))
                (done-file
                 (open-file
                  (string-append (option-ref options 'out)
                                 "Done-"
                                 (option-ref options 'target)
                                 ".scm")
                  "a")))
            (let lp ((outstanding in))
              ;; Non-functional logging is way safer in case of the
              ;; program hanging for some reason: it writes at least some
              ;; of the data.
              ;; The first run logged nothing because we were collecting
              ;; in memory, and it crashed before it ended.
              (if (null? outstanding)
                  (begin
                    (close-port errors-file)
                    (close-port done-file)
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
                          (pretty-print `((customer . ,current)
                                          (response . ,(rsp->assoc result)))
                                        done-file)
                          (format (current-output-port) "[DONE]~%")
                          (lp rest)))
                      (lambda (key . args)
                        (pretty-print `((customer . ,current)
                                        (response . ,args))
                                      errors-file)
                        (format (current-output-port) "[ERROR]~%")
                        (lp rest))))))))))))

(define (update-standard! filename secret options)
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
                            (read)))))
              (file (lambda (type)
                      (string-append (option-ref options 'out) type "-"
                                     (option-ref options 'target) ".scm"))))
          (format (current-output-port) "Updating ~a subscriptions.~%"
                  (length in))
          (let ((errors-file (open-file (file "Errors") "a"))
                (done-file (open-file (file "Done") "a")))
            (let lp ((outstanding in))
              ;; Non-functional logging is way safer in case of the
              ;; program hanging for some reason: it writes at least some
              ;; of the data.
              ;; The first run logged nothing because we were collecting
              ;; in memory, and it crashed before it ended.
              (if (null? outstanding)
                  (begin
                    (close-port errors-file)
                    (close-port done-file)
                    (format (current-output-port) "Done~%"))
                  (let ((current (first outstanding))
                        (rest (cdr outstanding)))
                    (catch #t
                      (lambda _
                        (format (current-output-port) "Working on ~a (~a)..."
                                (assoc-ref current 'email)
                                (assoc-ref current 'sub_id))
                        (let* ((ia (format (current-output-port)
                                           "Creating "))
                               (crt (create-subscription
                                     (assoc-ref current 'new_amount)
                                     "GBP"
                                     (assoc-ref current 'interval_unit)
                                     (assoc-ref current 'man_id)
                                     (assoc-ref current 'sub_id)
                                     #:interval (assoc-ref current 'interval)
                                     #:day_of_month (assoc-ref current 'day_of_month)
                                     #:metadata `(("Statement Text 1"
                                                   . ,(assoc-ref current 'sub_id)))))
                               (l1 (pretty-print `((customer . ,current)
                                                   (create-response . ,(rsp->assoc crt)))
                                                 done-file))
                               (ib (format (current-output-port)
                                           "[DONE]; Deleting..."))
                               (del (cancel-subscription
                                     (assoc-ref current 'sub_id))))
                          (pretty-print `((customer . ,current)
                                          (delete-response . ,(rsp->assoc del)))
                                        done-file)
                          (format (current-output-port) "[DONE]~%")
                          (lp rest)))
                      (lambda (key . args)
                        (pretty-print `((customer . ,current)
                                        (response . ,args))
                                      errors-file)
                        (format (current-output-port) "[ERROR]~%")
                        (lp rest))))))))))))

(define (calculate-gains filename)
  (with-input-from-file filename
    (lambda _
      (let ((in (let lp ((content '())
                         (current (read)))
                  (if (eof-object? current)
                      (reverse content)
                      (lp (cons current content)
                          (read))))))
        (format (current-output-port)
                "There are ~a candidates in ~a.
On the basis of this data, would gain ~a GBP over 1 year.~%"
                (length in) filename
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
                         0 in)
                   100.00))))))

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
       (format #t "~%~%NOTE: Please ensure you have the latest blockfiles!~%~%")
       (generate-source-files filename secret options)
       (format #t "~%~%NOTE: Please ensure you have the latest blockfiles!~%~%"))
      (("script" "update!")
       (update-pro! filename secret options))
      (("script" "create!")
       (update-standard! filename secret options))
      (("script" "calculate-gains")
       (calculate-gains filename)))))

;; Sandbox!
;; (main '("script" "-t" "sandbox"))

;; Of roughly 302 subs on standard, 251 are candidates for update
;; (main '("script" "-t" "standard"))

;; Of roughly 2479 subs on Pro, 2139 are candidates for update
;; (main '("script" "-t" "pro"))

(main (command-line))
