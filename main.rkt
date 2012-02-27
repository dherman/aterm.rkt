#lang racket/base

(require (lib "lex.ss" "parser-tools")
         (lib "yacc.ss" "parser-tools")
         (prefix-in : (lib "lex-sre.ss" "parser-tools"))
         (lib "string.ss" "srfi" "13")
         (lib "class.ss"))
(provide make-aterm-reader unescape)

;; TODO: make a test suite

;; "Top([Foo(\"bar\"),Bar(\"foo\")],23) 200 100"
;; "100"
;; "[]" "[1]" "[1,2]" "[1,2,3]" "[1,2,3,4]"
;; "()" "(1)" "(1,2)" "(1,2,3)" "(1,2,3,4)"
;; "Top" "Top()" "Top(1)" "Top(1,2)" "Top(1,2,3)"
;; "Top{cons(\"ToTerm\")}" "Top(1,2,3){cons(\"ToTerm\")}"
;; "\"abc\"" "\"abc\" \"def\""
;; "\"ab\\\"cd\""

;; unescape tests:
;; #<<END "ab\"cd" END
;; #<<END "ab\ncd" END
;; #<<END "ab\\cd" END
;; #<<END "ab\\\qcd" END

(define (test str)
  (let ([reader (make-aterm-reader (open-input-string str))])
    (let loop ([result null])
      (cond
        [(reader) => (lambda (next)
                       (loop (cons next result)))]
        [else (reverse result)]))))

;; Grammar of ATerms given at:
;;
;; http://nix.cs.uu.nl/dist/stratego/strategoxt-manual-unstable-latest/manual/chunk-chapter/ref-baffle.html
;;
;;   t  ::= bt                 -- basic term
;;       | bt { t }            -- annotated term
;;
;;   bt ::= C                  -- constant
;;       | C(t1,...,tn)        -- n-ary constructor
;;       | (t1,...,tn)         -- n-ary tuple
;;       | [t1,...,tn]         -- list
;;       | "ccc"               -- quoted string
;;       | int                 -- integer
;;       | real                -- floating point number
;;       | blob                -- binary large object

;; TODO: handle reals and blobs

(define-tokens regular (ID NUMBER STRING))
(define-empty-tokens operators (LBRACE RBRACE LPAREN RPAREN LBRACK RBRACK COMMA EOF))

(define-lex-abbrevs
  (lower-letter (:/ "a" "z"))
  (upper-letter (:/ #\A #\Z))
  (id-start (:or lower-letter upper-letter "_"))
  (digit (:/ "0" "9"))
  (id-cont (:or id-start digit)))

(define (regexp-replace** ls str)
  (if (null? ls)
      str
      (regexp-replace** (cdr ls) (regexp-replace* (caar ls) str (cdar ls)))))

(define (unescape str)
  (regexp-replace** '((#rx"\\\\a" . "\a")
                      (#rx"\\\\b" . "\b")
                      (#rx"\\\\t" . "\t")
                      (#rx"\\\\n" . "\n")
                      (#rx"\\\\v" . "\v")
                      (#rx"\\\\f" . "\f")
                      (#rx"\\\\r" . "\r")
                      (#rx"\\\\\\\\" . "\\")
                      (#rx"\\\\" . ""))
                    str))

(define aterm-lexer 
  (lexer ((eof) (token-EOF))
         (whitespace (aterm-lexer input-port))
         ("{" (token-LBRACE))
         ("}" (token-RBRACE))
         ("(" (token-LPAREN))
         (")" (token-RPAREN))
         ("[" (token-LBRACK))
         ("]" (token-RBRACK))
         ("," (token-COMMA))
         ((:+ digit) (token-NUMBER (string->number lexeme)))
         ;; TODO: what's the real grammar for ID's?
         ((:: id-start (:* id-cont)) (token-ID lexeme))
         ((:: #\" (:* (:or (:~ #\") "\\\"")) #\")
          (token-STRING (substring lexeme 1 (- (string-length lexeme) 1))))))

(define (make-lexer in)
  (lambda ()
    (aterm-lexer in)))

(define-struct annotated (term annotation))

#;(print-struct #t)

(define token-error-strings
  '((ID . "identifier")
    (STRING . "string")
    (NUMBER . "number")
    (LPAREN . "'('")
    (RPAREN . "')'")
    (LBRACK . "'['")
    (RBRACK . "']'")
    (LBRACE . "'{'")
    (RBRACE . "'}'")
    (COMMA . "','")
    (EOF . "<eof>")))

(define (token-error-string token)
  (cdr (assq token token-error-strings)))

(define-syntax begin1
  (syntax-rules ()
    [(_ e0 e1 e2 ...)
     (begin e0 (begin0 e1 e2 ...))]))

;; scanner% : { peek : -> token
;;              next-token : token
;;              matches? : symbol ... -> (optional token)
;;              try? : symbol ... -> (optional token)
;;              expect : symbol ... -> token
;;             }
(define scanner%
  (class object%
    (init-field in)

    (define lexer (make-lexer in))
    (define look-ahead #f)

    (define/public (next-token)
      (if look-ahead
          (begin0 look-ahead (set! look-ahead #f))
          (lexer)))

    (define/public (peek)
      (set! look-ahead (next-token))
      look-ahead)

    (define (parse-error expected)
      (let ([actual (peek)])
        (error 'parse-aterm
               (format "expected ~a; found ~v"
                       (string-join expected ", ")
                       (or (and (token? actual) (token-value actual)) actual)))))

    (define/public (matches? . expected)
      (let ([actual (peek)])
        (or (and (token? actual)
                 (memq (token-name actual) expected))
            (memq actual expected))))

    (define/public (try? . expected)
      (and (send/apply this matches? expected)
           (next-token)))

    (define/public (expect . expected)
      (unless (send/apply this matches? expected)
        (parse-error (map token-error-string expected)))
      (next-token))

    (super-make-object)))

;; reader% : { read : -> sexp }
(define reader%
  (class object%
    (init in)

    (define scanner (make-object scanner% in))

    (define (parse-aterm-list terminator)
      (if (send scanner matches? 'ID 'NUMBER 'STRING 'LPAREN 'LBRACK)
          (let ([first (parse-aterm)]
                [rest (cond
                        [(send scanner try? 'COMMA) (parse-aterm-list terminator)]
                        [(send scanner matches? terminator) null]
                        [else (send scanner expect 'COMMA terminator)])])
            (cons first rest))
          null))

    (define (parse-tuple)
      (begin1 (send scanner expect 'LPAREN)
              (parse-aterm-list 'RPAREN)
              (send scanner expect 'RPAREN)))

    (define (parse-list)
      (begin1 (send scanner expect 'LBRACK)
              (cons 'list (parse-aterm-list 'RBRACK))
              (send scanner expect 'RBRACK)))
 
    (define (parse-annotation)
      (begin1 (send scanner expect 'LBRACE)
              (parse-aterm)
              (send scanner expect 'RBRACE)))

    (define (parse-aterm)
      (let* ([next (send scanner peek)]
             [term (cond
                     [(and (token? next) (eq? (token-name next) 'ID))
                      (send scanner next-token)
                      (if (eq? (send scanner peek) 'LPAREN)
                          (cons (string->symbol (token-value next)) (parse-tuple))
                          (string->symbol (token-value next)))]
                     [(token? next) (token-value (send scanner next-token))]
                     [(eq? next 'LPAREN) (parse-tuple)]
                     [(eq? next 'LBRACK) (parse-list)]
                     [else (send scanner expect 'ID 'STRING 'NUMBER 'LPAREN 'LBRACK)])])
        (if (send scanner matches? 'LBRACE)
            (make-annotated term (parse-annotation))
            term)))

    (define/public (read)
      (and (not (eq? (send scanner peek) 'EOF))
           (parse-aterm)))

    (super-make-object)))

;(define aterm-parser
;  (parser (start aterm)
;          (tokens regular operators)
;          (grammar (aterm [(term) $1]
;                          [(term LBRACE aterm RBRACE) (make-annotated $1 $3)])
;                   (term [(ID) (string->symbol $1)]
;                         [(ID LPAREN aterm-list RPAREN) (cons (string->symbol $1) $3)]
;                         [(LPAREN aterm-list RPAREN) $2]
;                         [(LBRACK aterm-list RBRACK) (cons 'list $2)]
;                         [(STRING) $1]
;                         [(NUMBER) $1])
;                   (aterm-list [() null]
;                               [(aterm) (list $1)]
;                               [(aterm-list COMMA aterm) (append $1 (list $3))]))
;          (end EOF)
;          (error (lambda (a b c)
;                   (error 'aterm-parser "error occured, ~v ~v ~v" a b c)))))

(define (make-aterm-reader in)
  (let ([reader (make-object reader% in)])
    (lambda ()
      (send reader read))))
