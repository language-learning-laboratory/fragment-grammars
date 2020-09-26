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

 ;; Thang July 2013: this version fixes several bugs (note that for AG, use generate-AG.ss instead):
 ;; (a) prefix terminals with "_" during reading (merge-tree-set) not during outputing (print-grammar). The old version used a hash table ``terminals'' which failed to distinguish cases where the same symbol is used for both terminals and non-terminals, e.g. punctuations
 ;; (b) there's a bug in all usages of hash-table-update! (due to latest release of srfi) when the key is not present we need to explicitly initialize it
 ;; For example:
 ;;   incorrect: hash-table-update! data tree (lambda (c) (+ c count)) (lambda () 0))
 ;;   correct: hash-table-update! data tree (lambda (c) (+ c count)) (lambda () count))
 ;; Note also the use of function initialize-hash to correctly initialize hash of hash.
 
(define pair cons)
(define rest cdr)
(define is-debug #f) ; Thang
(define *individual* #f)
(define *wug-score* 1)

;; Thang: print a hash table for debugging purposes
(define (print-hash hash-table msg)
  (disp msg)
  (hash-table-walk hash-table
                   (lambda (key value)
                     (begin
                       (display key)(display ": ")(disp value)
                       ))))

;; Thang: add "_" for terminal
(define (annotate-terminals tree)
  (if (not (list? tree))
    (string->symbol (string-append "_" (symbol->string tree))) ;; terminal
      (let ([head (first tree)]
            [children (rest tree)])
        (cons head (map annotate-terminals children)))))

;; Thang: create new hash with a single pair of key, value
(define (initialize-hash key value) 
  (define new-hash (make-hash-table))
  (hash-table-set! new-hash key value)

  new-hash)

  
(define (flatten lol)
  (if (null? lol)
      '()
      (if (list? (first lol))
          (append (flatten (first lol)) (flatten (rest lol)))
          (cons (first lol) (flatten (rest lol))))))

(define (yield tree)
  (if (not (list? tree))
      tree
      (let ([head (first tree)]
            [children (rest tree)])
        (flatten (map yield children)))))

(define disp
  (lambda args
    (begin
      (for-each display args)
      (display "\n"))))

(define (read-all file-handle)
  (let ([next (read file-handle)])
    (if (eof-object? next)
        '()
        (cons next (read-all file-handle)))))

(define (merge-tree-set tree-file count-file)
  (let ([data (make-hash-table)]
        [trees (read-all (open-input-file tree-file))]
        [counts (read-all (open-input-file count-file))])
    (let loop ([trs trees]
               [cnts counts] [lineId 1]) ;; Thang: add lineId to know the progress
      (if (and (null? trs) (null? cnts))
          (begin
            (display "Done! Total lines = ") (disp (- lineId 1))
            data)
          (let ([tree (list 'START (first (first trs)))] ;;note that we are assuming trees are in ((...)) format
                [count (inexact->exact (first cnts))])
            (begin
			  (set! tree (annotate-terminals tree)) ;; Thang: add _ to nonterminals
			  
			  ;; print lineId
              (when (= (remainder lineId 10000) 0)
                (begin (display " (")(display lineId)(display ") ")))
				
			  ;; update hash
              (hash-table-update! data tree (lambda (c) (+ c count)) (lambda () count)) ; Thang 0))
              (loop (rest trs) (rest cnts) (+ lineId 1))))))))	

;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; GENSYMS ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define gensyms (make-hash-table))

(define (my-gensym symb)
  (let* ([generator (if (hash-table-exists? gensyms symb)
                        (hash-table-ref gensyms symb)
                        (begin
                          (hash-table-set! gensyms symb (let ([count -1])
                                                          (lambda ()
                                                            (begin
                                                              (set! count (+ count 1))
                                                              count))))
                          (hash-table-ref gensyms symb)))]
         [num (generator)])
      (string->symbol (string-append (symbol->string symb) "@" (number->string num)))))

;; strip off the unique id from this symbol
(define (my-gensym->symbol gs)
  (if (equal? gs 'START)
      'START
      (let* ([l (string->list (symbol->string gs))]
             [suffix (memq #\@ l)])
        (if suffix
            (let ([len (length suffix)])
              (string->symbol (list->string (drop-right l len))))
            gs))))

(define (trees->labels tree-list)
  (map (lambda (t) (if (list? t)
                       (my-gensym->symbol (first t))
                       t))
       tree-list))

(define terminals (make-hash-table))              
(define minimal-rule-counts (make-hash-table))  ;; stored PCFG rules
(define tree-cache (make-hash-table))

(define (tree->annotated-tree tree)
  (if (hash-table-exists? tree-cache tree)
      (hash-table-ref tree-cache tree)
      (if (not (list? tree))
          tree
          (let* ([label (first tree)]
                 [children (rest tree)]
                 [annotated-children (map (lambda (t) (tree->annotated-tree t)) children)]
                 [annotated-label (if (equal? label 'START) 'START (my-gensym label))]
                 [annotated-tree (cons annotated-label annotated-children)])
            (begin
              (hash-table-set! tree-cache tree annotated-tree)
              annotated-tree)))))


(define (count-tree tree type-count root)
    (if (not (list? tree)) ; It is a terminal
		(begin
            (hash-table-set! terminals tree 0)
            tree)
        
        (let* ([current-node-gensym (first tree)] ;;nonterminal
               [label (my-gensym->symbol current-node-gensym)]
			   [children (rest tree)]
               [children-gensyms  (map (lambda (t) (count-tree t type-count #f)) children)]              
               [update-minimal (hash-table-update! minimal-rule-counts
                                                   (cons label (trees->labels children))
                                                   (lambda (old-count) (+ old-count type-count)) (lambda () type-count))] ; Thang 0))]
	           
							   )
          current-node-gensym))) 


(define (inner? symb)
  (memq #\@ (string->list (symbol->string symb))))

(define (terminal? x)
  (hash-table-exists? terminals x))

(define (simple-rule? r)
  (hash-table-exists? minimal-rule-counts r))

;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Print a Grammar ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (print-grammar grammar outputport)
  (hash-table-walk
   grammar
   (lambda (head rhss)
     (let ([total 0])
       (hash-table-walk
        rhss
        (lambda (rhs prob)
          (write (log prob) outputport)
          ;(display (string-append  " " (symbol->string head)  (fold-left (lambda (a v) (string-append a " " (if (terminal? v) "_" "") (symbol->string v)) ) "" rhs)) outputport)
		  (display (string-append  " " (symbol->string head)  (fold-left (lambda (a v) (string-append a " " (symbol->string v)) ) "" rhs)) outputport) ;;  Thang: we do not need this code, (if (terminal? v) "_" ""), to add _ since the tree has been annotated with _ during reading 

		  
          (newline outputport)))))))


(define (remove-unity-prob-rules grammar) grammar)

(define (make-mdpcfg pi rules)
    (let ([total-per-category (make-hash-table)]
          [types-per-category (make-hash-table)]
          [result-grammar (make-hash-table)])
      (begin
        (disp "Making MDPCFG grammar")
		;; Thang: debug info
		(when is-debug (print-hash rules "\n### base-rule-counts"))
	
        (hash-table-walk rules
                         (lambda (rule rule-count )
                           (let ([head (first rule)]
                                 [rhs (rest rule)])
                             (begin 
                               (hash-table-update! total-per-category
                                                   head
                                                   (lambda (old-count) (+ old-count rule-count)) (lambda () rule-count)) ; Thang 0))
                               (hash-table-update! types-per-category
                                                   head
                                                   (lambda (old-count) (+ old-count 1)) (lambda () 1)))))) ; Thang  0))))))
        
        (hash-table-walk rules
                         (lambda (rule rule-count)
                           (let* ([head (first rule)]
                                  [rhs (rest rule)]
                                  [category-total (hash-table-ref total-per-category head)]
                                  [category-types (hash-table-ref types-per-category head)]
                                  ;;[dummy (disp rule " " rule-count)]
                                  [prob (/ (+ rule-count pi) (+ category-total (* category-types pi)))])
                             (hash-table-update! result-grammar
                                                 head
                                                 (lambda (old-rhss)
                                                   (begin
                                                     (hash-table-update! old-rhss rhs (lambda (old-prob) (+ old-prob prob)) (lambda () prob)) ; Thang 0))
                                                     old-rhss))
                                                 (lambda () 
												 (initialize-hash rhs prob); Thang: make-hash-table)
												 )))))
        (remove-unity-prob-rules result-grammar))))


;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;; MAIN ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(let* ([prefix (second (command-line))]
       [out-prefix (third (command-line))]
       [inputdir (fourth (command-line))]
       [outputdir (fifth (command-line))]
       [tree-file (string-append inputdir prefix ".forms.txt")]
       [count-file (string-append inputdir prefix ".counts.txt")]
       [trees (merge-tree-set tree-file count-file)]
       [pi (inexact->exact 1.0)]
       [a  (inexact->exact 1/2)]
       [b (inexact->exact  100.0)])
  (begin
	(define treeCount 0) ;; tree type count
	(display "\n### Counting trees ...")
    (if *individual*
        (hash-table-walk trees (lambda (tree count)
                                 (do ([i 0 (+ i 1)])
                                     ((= i count) count)
                                   (count-tree tree 1 #t))))
        (hash-table-walk trees (lambda (tree count)
                                 (begin
                                   ;; print progress
                                   (set! treeCount (+ treeCount 1))
                                   (when (= (remainder treeCount 100) 0)
                                     (begin
                                       (display " (")(display treeCount)(display ") ")))
									   
                                   (count-tree (tree->annotated-tree tree) count #t)
								   ))))
								   
	(display "Done! Total trees = ") (disp treeCount)
    (let* ([mdpcfg (make-mdpcfg pi minimal-rule-counts)]
          )
      (print-grammar mdpcfg (open-output-file (string-append outputdir out-prefix  ".MDPCFG-gram.txt")))
	  )))





