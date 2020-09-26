(import
  (except (rnrs)
         string-ci-hash
         string-hash)
(rnrs r5rs (6)) ;; Thang: for methods like remainder, modulo, quotient http://www.r6rs.org/final/html/r6rs-lib/r6rs-lib-Z-H-20.html
(only (ikarus) 
       gensym
       inexact->exact)
 ; (srfi :1)
 (scheme-tools srfi-compat :1)
 ;;(srfi :13) ;; Thang: for string-concatenate
 (srfi :69)
 )

(define pair cons)
(define rest cdr)
(define is-debug #f)
(define debug-opt 0) 
(define *individual* #f)
(define *wug-score* 1)

(define (flatten lol)
  (if (null? lol)
      '()
      (if (list? (first lol))
          (append (flatten (first lol)) (flatten (rest lol)))
          (cons (first lol) (flatten (rest lol))))))

;; yield surface word 
(define (concat terminals)
  (fold-left (lambda (a v) (string-append a (symbol->string v)) ) "" terminals))

  
;; Thang: terminal sequence
(define (yield tree)
  (if (not (list? tree))
    tree
    (let ([head (first tree)]
          [children (rest tree)])
      (flatten (map yield children)))))

;; return root label nodes of children, e.g., (N@0 (V@0 extract) or) -> (N V or)
(define (trees->labels tree-list)
  (map (lambda (t) (if (list? t)
                       (first t)
                       t))
       tree-list))

;; Thang: create new hash with a single pair of key, value
(define (initialize-hash key value) 
  (define new-hash (make-hash-table))
  (hash-table-set! new-hash key value)

  new-hash)

(define (print-result-grammar hash-hash-table msg)
  (disp msg)
  (hash-table-walk hash-hash-table
                   (lambda (key value)
                     (print-hash value key))))


(define (print-hash hash-table msg)
  (disp msg)
  (hash-table-walk hash-table
                   (lambda (key value)
                     (begin
                       (display key)(display ": ")(disp value)
                       ))))


;; Thang: print grammar to screen
(define (print-grammar-to-screen result-grammar)
    (disp "# result-grammar:")
    (hash-table-walk result-grammar
                     (lambda (head rhsHash)
                       (begin
                         (display "## ")(disp head)
                         (hash-table-walk rhsHash 
                                          (lambda (rhs prob)
                                            (display rhs)(display "\t")(disp prob))
                         ))))
    )

(define (tree-to-string tree)
  (if (not (list? tree))
      (symbol->string tree)
      (let ([head (first tree)]
            [children (rest tree)])
        (string-append "(" (symbol->string head) "(" (string-append (map tree-to-string children)) ")" ))))

(define (print-hash-to-file hash outputport)
  (hash-table-walk hash
                   (lambda (rule ruleCount)
                     (let ([head (first rule)]
                           [rhs (rest rule)])
                       (display (string-append (symbol->string head) "->[") outputport)
                       (display (fold-left (lambda (a v) (string-append a (if (string=? a "") "" " ") (symbol->string v)) ) "" rhs) outputport)
                       (display "] : " outputport)
                       (write ruleCount outputport)
                       (newline outputport)))))


(define disp
  (lambda args
    (begin
      (for-each display args)
      (display "\n"))))

;; read file, and return a list of lines
(define (read-all file-handle)
  (let ([next (read file-handle)])
    (if (eof-object? next)
        '()
        (cons next (read-all file-handle)))))

;; convert a derivational tree, e.g. (ROOT (A un (A realistic))), into a morphological segmentation, e.g. un_A/PRE realistic_A/STM
(define (morpho-representation tree)
   (if (not (list? tree))
    tree
    (let ([head (first tree)]
          [children (rest tree)])
      (if (= (length children) 1)
        ;; length == 1
        (if (list? (first children))
          (morpho-representation (first children)) ;; head is ROOT, tree is (ROOT (A un (A realistic))), so children ((A un (A realistic)))
          (string-append (symbol->string (first children)) "_" (symbol->string head) "/STM")) ;; base case (A realistic)

        
        (if (> (length children) 2)
          ;; length > 2
          (begin (display "! problem: length children > 2 ")(disp children) (exit 1))
      
          ;; length == 2
          (let ([firstChild (first children)]
              
                [secondChild (second children)])
          
            (display "# ")(disp tree)(disp firstChild)(disp secondChild)
          
            (if (not (list? firstChild))
              (if (not (list? secondChild))
                (begin (display "! problem: both terminals ")(display firstChild)(display " ")(disp secondChild))
                (string-append (symbol->string firstChild) "_" (symbol->string head) "/PRE " (morpho-representation secondChild))) ;; first child: prefix with head being its tag
              
              (if (not (list? secondChild))
                 (string-append (morpho-representation firstChild) " " (symbol->string secondChild) "_" (symbol->string head) "/SUF") ;; second child: suffix with head being its tags
                 (begin (display "! problem: both lists ")(display firstChild)(display " ")(disp secondChild))
          ))))))))

;; process derivational file
(define (process-derivational tree-file)
  (let ([data (make-hash-table)]
        [trees (read-all (open-input-file tree-file))])
    (let loop ([trs trees]
               [lineId 1]) ;; Thang: add lineId to know the progress
      (if (null? trs)
          (begin
            (disp "Done! Total lines = " (- lineId 1))
            data)
          (let* ([tree (list 'ROOT (first (first trs)))]) ;;note that we are assuming trees are in ((...)) format
              ;; print lineId
              (when (= (remainder lineId 10000) 0)
                (begin (display " (")(display lineId)(display ") ")))
              
              ;; update hash
              (when (not (hash-table-exists? data tree))
                ;;(hash-table-set! data tree (concat (yield tree))))
                (hash-table-set! data tree (morpho-representation tree)))
                           
              ;; loop through the remaining lines
              (loop (rest trs) (+ lineId 1)))))))

(define unary-hash (make-hash-table)) ;; count of unary rules
;; list of recursive unary rules
(define unary-lhs '())
(define unary-rhs '())

;;;;;;;;;;;;;;;;;;;;
;; find unary rules, keep track of recursive ones 
;;;;;;;;;;;;;;;;;;;;
(define (find-unary tree)
  (when (list? tree) ;; non-terminal
    (let ([head (first tree)]
          [children (rest tree)])
      (if (= (length children) 1)
        ;; single child
        (when (list? (first children)) ;; non-terminal
          ;; unary rule
          (let ([pair (string-append (symbol->string head) "->" (symbol->string (first (first children))))]) 
            (when (not (hash-table-exists? unary-hash pair)) ;; new unary rule
              (let ([reverse-pair (string-append (symbol->string (first (first children))) "->" (symbol->string head))]) 
                ;; check for recursive unary rule
                (when (hash-table-exists? unary-hash reverse-pair)
                  (begin
                    (set! unary-lhs (cons unary-lhs (symbol->string head))) ;;
                    (set! unary-rhs (cons unary-rhs (symbol->string (first (first children)))))
                    ))))
            ;; update unary rule counts
            (hash-table-update! unary-hash pair (lambda (c) (+ c 1)) (lambda () 1)) 

            (find-unary (first children)))) ;; recurse

        ;; multiple children
        (map find-unary children)))))

(define remove-unaries (make-hash-table)) ;; mark unaries to be removed

;;;;;;;;;;;;;;;;;;;;
;; remove recursive unary rules 
;; return a new tree in which the removed rule, e.g. (NP (S ...))  has been conflated into a single node (NP->S ...)
;;;;;;;;;;;;;;;;;;;;
(define (remove-unary tree)
  (if (not (list? tree))
    tree ;; terminal

    ;; non-terminal
    (let ([head (first tree)]
          [children (rest tree)])
      (if (= (length children) 1)
        ;; single child
        (if (not (list? (first children)))
          tree ;; preterminal and terminal
          
          ;; non-terminali or unary rule
          ;; (NP (S ))
          (let ([pair (string-append (symbol->string head) "->" (symbol->string (first (first children))))]) 
            (if (hash-table-exists? remove-unaries pair) 
              
              ;; remove unary rule
              (cons (string->symbol pair) (map remove-unary (rest (first children)))) 
              ;; keep going, recurse
              (list head (remove-unary (first children))))
            ))

        ;; multiple children
        (cons head (map remove-unary children))))))

(define new-trees '())
;;;;;;;;;;;;;;;;;;;;;;
;; process WSJ file
;;;;;;;;;;;;;;;;;;;;;;
(define (process-WSJ tree-file option)
  (let ([data (make-hash-table)]
        [trees (read-all (open-input-file tree-file))])
    (let loop ([trs trees]
               [lineId 1]) ;; Thang: add lineId to know the progress
      (if (null? trs)
          (begin
            (disp "Done! Total lines = " (- lineId 1))
            data)
          (let* ([tree (list 'ROOT (first (first trs)))]) ;;note that we are assuming trees are in ((...)) format
              ;; print lineId
              (when (= (remainder lineId 10000) 0)
                (begin (display " (")(display lineId)(display ") ")))
              (when (= option 0) ;; find unary rules
                (find-unary tree)) 
              (when (= option 1) ;; remove unary rules
                  (set! new-trees (cons new-trees (list (second (remove-unary tree))))))
              ;; loop through the remaining lines
              (loop (rest trs) (+ lineId 1)))))))

(define (print-list-to-file a-list outputport)
  (when (not (null? a-list)) 
    (begin
      (print-list-to-file (car a-list) outputport)
      (display (cdr a-list) outputport)
      ;;(display "\n" outputport)
      (newline outputport)
      )))

;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;; MAIN ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(begin
  ;; Command-line processing
  (when (< (length (command-line)) 6)
    (begin 
      (disp "Usage: " (first (command-line)) " inName outName inDir outDir option [debug]")
      (disp "  option -- 0 (process derivational dataset), 1 (process WSJ dataset")
      (exit 1)))
  (disp "# Args: " (command-line)) 
  
  ;; debug opt
  (when (> (length (command-line)) 6)
    (begin
      (set! debug-opt (string->number (seventh (command-line))))))

  (let* ([prefix (second (command-line))]
         [out-prefix (third (command-line))]
         [inputdir (fourth (command-line))]
         [outputdir (fifth (command-line))]
         [option (string->number (sixth (command-line)))]
         [tree-file (string-append inputdir "/" prefix ".forms.txt")]
         [count-file (string-append inputdir "/" prefix ".counts.txt")]
          )
    (begin
      (define trees 0) 
      (disp "# Option = " option)
     
      ;; handle derivational data 
      (when (= option 0) 
        (begin
          (disp "# Handling derivational data " tree-file " ... ")
          (let ([trees (process-derivational tree-file)])
            (begin
              (hash-table-walk trees (lambda (key value)
                                       (begin
                                         (display key)(display "\t")(disp value)))))))) 
 

      ;; handle WSJ data
      (when (= option 1)
        (begin
          (disp "# Handling WSJ data " tree-file " ... ")
          
          ;; count unary rules, identy recursive ones
          ;; output: unary-lhs, unary-rhs, unary-hash
          (process-WSJ tree-file 0)

          ;; decide which one to remove, the one with lower counts
          (disp "# recursive unary rules:")
          (let loop([lhs unary-lhs] [rhs unary-rhs])
            (when (not (null? lhs))
              (let* ([pair (string-append (cdr lhs) "->" (cdr rhs))]
                     [reverse-pair (string-append (cdr rhs) "->" (cdr lhs))]
                     [count (hash-table-ref unary-hash pair)]
                     [reverse-count (hash-table-ref unary-hash reverse-pair)])
                (disp pair ":" count "\t" reverse-pair ":" reverse-count)
                (if (< count reverse-count)
                    (hash-table-set! remove-unaries pair 1)
                    (hash-table-set! remove-unaries reverse-pair 1))

                (loop (car lhs) (car rhs)))
            ))
          (print-hash remove-unaries "# remove pairs:")
          
          ;; remove unaries
          (process-WSJ tree-file 1)

          ;; output
          (let ([out-file (string-append outputdir "/output.txt")])
            (print-list-to-file new-trees (open-output-file out-file)))

          
          ))
      )))
