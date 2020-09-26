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

(define *individual* #f)
(define *wug-score* 1)

(define (flatten lol)
  (if (null? lol)
      '()
      (if (list? (first lol))
          (append (flatten (first lol)) (flatten (rest lol)))
          (cons (first lol) (flatten (rest lol))))))

;; Thang: terminal sequence
(define (yield tree)
  (if (not (list? tree))
      tree
      (let ([head (first tree)]
            [children (rest tree)])
        (flatten (map yield children)))))

;; Thang: add "_" for terminal
(define (annotate-terminals tree)
  (if (not (list? tree))
    (string->symbol (string-append "_" (symbol->string tree))) ;; terminal
      (let ([head (first tree)]
            [children (rest tree)])
        (cons head (map annotate-terminals children)))))

(define disp
  (lambda args
    (begin
      (for-each display args)
      (display "\n"))))

;; Thang doc: read file, and return a list of lines
(define (read-all file-handle)
  (let ([next (read file-handle)])
    (if (eof-object? next)
        '()
        (cons next (read-all file-handle)))))

;; Thang add progress info by printing out lineId
(define (merge-tree-set tree-file count-file)
  (display "# merge-tree-set, reading data ... ")
  (let ([data (make-hash-table)]
        [trees (read-all (open-input-file tree-file))]
        [counts (read-all (open-input-file count-file))])
    (let loop ([trs trees]
               [cnts counts] [lineId 1]) ;; Thang: add lineId to know the progress
      (if (and (null? trs) (null? cnts))
          (begin
            (display "Done! Total lines = ") (disp (- lineId 1))
            data)
          (let* ([tree (list 'START (first (first trs)))] ;;note that we are assuming trees are in ((...)) format
                [count (inexact->exact (first cnts))])
              (set! tree (annotate-terminals tree)) ;; add _ to nonterminals
              ;; print lineId
              (when (= (remainder lineId 100) 0)
                (begin (display " (")(display lineId)(display ") ")))
              
              ;; update hash
              (hash-table-update! data tree (lambda (c) (+ c count)) (lambda () count)) 
              
              ;; loop through the remaining lines
              (loop (rest trs) (rest cnts) (+ lineId 1)))))))

;; return root label nodes of children, e.g., (N@0 (V@0 extract) or) -> (N V or)
(define (trees->labels tree-list)
  (map (lambda (t) (if (list? t)
                       (first t)
                       t))
       tree-list))

;;(define terminals (make-hash-table))
;;(define (terminal? x)
;;  (hash-table-exists? terminals x))

;; Store the counts of base rules
(define base-rule-counts (make-hash-table))

;; Store counts of subtrees
(define observed-trees (make-hash-table))

;; Preterminals & lexicon-rule-counts
(define preterminals (make-hash-table))
(define lexicon-rule-counts (make-hash-table))

(define (count-tree tree count parent-label)
  
  (when (list? tree) ; It is a non-terminal
    (begin
      (when (not (hash-table-exists? observed-trees tree));; If this is the first time we are seeing the tree, create it
        (begin
          ;; Update the corresponding base rules
          (let* ([label (first tree)]
                 [children (rest tree)])
            ;; count rules
            (hash-table-update! base-rule-counts
                                (cons label (trees->labels children))
                                (lambda (old-count) (+ old-count 1)) (lambda () 1))
            
            ;; Recurse on children
            (map (lambda (t) (count-tree t 1 label)) children))))
       

      ;; update lexicon-rule-counts when it is a preterminal
      (when (and (= 2 (length tree))(not (list? (second tree)))) ; It is a preterminal
        (begin
          (hash-table-update! lexicon-rule-counts
                              tree 
                              (lambda (old-count) (+ old-count count))
                              (lambda () count))       
          (hash-table-set! preterminals (first tree) 0) ;; maintain a list of preterminals
          ))

      ;;unpdate count of current tree in every case
      (hash-table-update! observed-trees ;; create tree
                        tree
                        (lambda (old-count) (+ old-count count)) (lambda () count)))))

;; aggregate counts of trees with the same root + yield
(define maximal-rule-counts (make-hash-table))
(define (approximate-pcfg observed-trees)
  (hash-table-walk observed-trees
                   (lambda (tree count)
                     (let ([label (first tree)]
                           [tree-yield (yield tree)])
                       (begin
                         ;; update maximal-rule-counts
                         (hash-table-update! maximal-rule-counts
                                             (cons label tree-yield)
                                             (lambda (old-count) (+ old-count count)) (lambda () count)) 
                     )))))


;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Print a Grammar ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (print-grammar grammar outputport is-log)
  (hash-table-walk
   grammar
   (lambda (head rhss)
     (let ([total 0])
       (hash-table-walk
        rhss
        (lambda (rhs prob)
            (begin
              (if is-log
                (write (log prob) outputport)
                (write prob outputport))
              (display (string-append  " " (symbol->string head)  (fold-left (lambda (a v) (string-append a " " (symbol->string v)) ) "" rhs)) outputport) ;;  Thang: we do not need this since the tree has been annotated with _ during reading (if (terminal? v) "_" "")
              (newline outputport))))))))

(define (remove-unity-prob-rules grammar) grammar)


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

                       ;; )
                       ;; outputport) ;;  Thang: we do not need this since the tree has been annotated with _ during reading (if (terminal? v) "_" "")
                       (newline outputport)))))

;; convert rule hash into grammar hahs of hash
(define (convert-hash-to-grammar rules)
  ;; result-gammar: hash of hash, index by head, then by rhs, value is rule prob
  (let ([result-grammar (make-hash-table)])
   (begin
      (hash-table-walk rules
                       (lambda (rule rule-count)
                         (let* ([head (first rule)]
                                [rhs (rest rule)])
                           (begin
                             (hash-table-update! result-grammar
                                                 head
                                                 (lambda (old-rhss)
                                                   (begin
         
         ;;                                            (display head)(display " -> ")(display rhs)(display "\t")(disp rule-count)
                                                     (hash-table-update! old-rhss rhs 
                                                                         (lambda (old-count) 
                                                                           (+ old-count rule-count)) 
                     
                                                                         (lambda () rule-count)) 
                                                     old-rhss))
                                                 (lambda () (
                                                             initialize-hash rhs rule-count )))))));;make-hash-table
       
          
      (remove-unity-prob-rules result-grammar))))

(define (make-mdpcfg pi rules)
    (let ([total-per-category (make-hash-table)]
          [types-per-category (make-hash-table)]
          [result-grammar (make-hash-table)])
      (begin
        (disp "## Making MDPCFG grammar")

        ;; total-per-category/types-per-category: counts subtree tokens/types rooted at non-terminal head
        (hash-table-walk rules
                         (lambda (rule rule-count )
                           (let ([head (first rule)]
                                 [rhs (rest rule)])
                             (begin 
                               (hash-table-update! total-per-category
                                                   head
                                                   (lambda (old-count) (+ old-count rule-count)) (lambda () rule-count))
                               (hash-table-update! types-per-category
                                                   head
                                                   (lambda (old-count) (+ old-count 1)) (lambda () 1)))))) 
        
        ;; (pi + rule-count) / (pi*category-types + category-total)
        ;; result-gammar: hash of hash, index by head, then by rhs, value is rule prob
        (hash-table-walk rules
                         (lambda (rule rule-count)
                           (let* ([head (first rule)]
                                  [rhs (rest rule)]
                                  [category-total (hash-table-ref total-per-category head)]
                                  [category-types (hash-table-ref types-per-category head)]
                                  [prob (/ (+ rule-count pi) (+ category-total (* category-types pi)))])
                              (begin
                              (when is-debug (begin (display rule)(display "\t")(display rule-count)(display "\t")(display prob)(display "=(")(display rule-count)(display "+")(display pi)(display ")/(")(display category-total)(display "+")(display category-types)(display "*")(display pi)(display ")\n")))
                             (hash-table-update! result-grammar
                                                 head
                                                 (lambda (old-rhss)
                                                   (begin
                                                     (hash-table-update! old-rhss rhs 
                                                                         (lambda (old-prob) 
                                                                           (+ old-prob prob)) 

                                                                         (lambda () prob)) 
                                                     old-rhss))
                                                 (lambda () (
                                                             ;make-hash-table
                                                             initialize-hash rhs prob 
                                                             ))))))
                              )

        (remove-unity-prob-rules result-grammar))))


;;   n - a    Ka + b
;;  -------, --------
;;   N + b    N + b
(define (make-adaptor-grammar a b rules mdpcfg)
    (let ([total-per-category (make-hash-table)] ;; # customers per restaurant (category)
          [types-per-category (make-hash-table)] ;; # tables per restaurant
          [result-grammar (make-hash-table)]
          [num-rules 0]
          [num-tags 0])
      (begin
        (disp "## Making Adaptor grammar ...")
        (disp "# Computing category total/type ...")
        (hash-table-walk rules
                         (lambda (rule rule-count )
                           (let* ([head (first rule)]
                                 [rhs (rest rule)]
                                 )
                             (begin 
                               (set! num-rules (+ num-rules 1))
                               (when (= (remainder num-rules 10000) 0)
                                     (begin
                                       (display " (")(display num-rules)(display ") ")))
 
                               (hash-table-update! total-per-category
                                                   head
                                                   (lambda (old-count) (+ old-count rule-count)) (lambda () rule-count)) 
                               (hash-table-update! types-per-category
                                                   head
                                                   (lambda (old-count) (+ old-count 1)) (lambda () 1))))))
        (display "Done! Total rules = ")(disp num-rules)
        (when is-debug (print-hash total-per-category "# total"))
        (when is-debug (print-hash types-per-category "# types"))
        
        (disp "# Computing probabilities for reused tables (PYP) ...")
        (set! num-rules 0)
        (hash-table-walk rules
                         (lambda (rule rule-count )
                           (let* ([head (first rule)]
                                  [rhs (rest rule)]
                                  [category-total (hash-table-ref total-per-category head)]
                                  [prob (/ (- rule-count a) (+ category-total b))]
                                  )
                             (begin
                               (set! num-rules (+ num-rules 1))
                               (when (= (remainder num-rules 10000) 0)
                                     (begin
                                       (display " (")(display num-rules)(display ") ")))
 
                               (hash-table-update! result-grammar
                                                 head
                                                 (lambda (old-rhss)
                                                   (begin (hash-table-update! old-rhss rhs (lambda (old-prob) (+ old-prob prob)) (lambda () prob)) 
                                                          old-rhss))
                                                 (lambda () (
                                                             ;; make-hash-table
                                                             initialize-hash rhs prob)))))))
        (display "Done! Total rules = ")(disp num-rules)
        (when is-debug (print-result-grammar result-grammar "# result grammar for reused tables"))
        
        
        (disp "# Computing probabilities for new tables (base PCFG) ...")
        (set! num-tags 0)        
        (set! num-rules 0)        
        (hash-table-walk mdpcfg
                         (lambda (head rhss)
                           (let* ([category-total (hash-table-ref total-per-category head)]
                                  [category-types (hash-table-ref types-per-category head)]
                                  [scale (/ (+ (* category-types a) b) (+ category-total b))])
                             (begin
                               (set! num-tags (+ num-tags 1))
                               
                               (hash-table-walk
                                rhss
                                (lambda (rhs prob)
                                  (begin
                                    (set! num-rules (+ num-rules 1))
                                    (when (= (remainder num-rules 10000) 0)
                                      (begin
                                        (display " (")(display num-rules)(display ") ")))

                                    (hash-table-update! result-grammar
                                                        head
                                                        (lambda (old-rhss)
                                                          (begin (hash-table-update! old-rhss rhs (lambda (old-prob) (+ old-prob (* scale prob))) (lambda () (* scale prob))) 
                                                                 old-rhss))
                                                        (lambda () (
                                                                    ;;make-hash-table
                                                                    initialize-hash rhs (* scale prob)
))))))))))
        (display "Done! Total tags = ")(display num-tags)(display ", total rules = ")(disp num-rules)
        (when is-debug (print-result-grammar result-grammar "# result grammar final"))
                         
        (remove-unity-prob-rules result-grammar))))


;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;; MAIN ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(let* ([prefix (second (command-line))]       ;; e.g. pasttense-adult-SWBD.num-25000
       [out-prefix (third (command-line))]    ;; 
       [inputdir (fourth (command-line))]     ;; e.g. /Users/timo/Projects/fragment-grammar/Simulations/PastTense/Runs/SWBD/Inputs
       [outputdir (fifth (command-line))]     ;;
       [tree-file (string-append inputdir "/" prefix ".forms.txt")]   
       [count-file (string-append inputdir "/" prefix ".counts.txt")] 
       [trees (merge-tree-set tree-file count-file)]
       [pi (inexact->exact 1.0)]
       [a  (inexact->exact 1/2)]
       [b (inexact->exact  100.0)]
        )
  (begin
    (define treeCount 0) ;; tree type count
 
    ;; handle arguments
    (display "# Args: ")(disp (command-line)) 
    (when (> (length (command-line)) 5)
      ;; get debug flag
      (let ([debugflag (sixth (command-line))])
        (when (string=? debugflag "true")
          (set! is-debug #t))))
 
    ;; count trees
    (display "\n### Counting trees ...")
    (if *individual*
        (hash-table-walk trees (lambda (tree count)
                                 (begin
                                    (do ([i 0 (+ i 1)])
                                     ((= i count) count)
                                   (count-tree tree 1 "")))))
        (hash-table-walk trees (lambda (tree count)
                                 (begin
                                   ;; print progress
                                   (set! treeCount (+ treeCount 1))
                                   (when (= (remainder treeCount 10000) 0)
                                     (begin
                                       (display " (")(display treeCount)(display ") ")))
 
                                   (count-tree tree count "")))))
    (display " Done! Total tree types = ")(disp treeCount)
    (display "# Preterminals: ")(disp (hash-table-keys preterminals))
   
  
    ;; debug info
    (when is-debug (print-hash base-rule-counts "\n### base-rule-counts"))
 
    ;; compute ag-base-pcfg then map-ag       
    (let ([out-file (string-append outputdir "/" out-prefix ".AG-gram.txt")])
      (display "\n# Output file ")(disp out-file)
      (if (file-exists? out-file)
        (begin (display "#! AG file exists ")(disp out-file))
        (let* ([ag-base-pcfg (make-mdpcfg pi base-rule-counts)]) ;; Thang's adaptor grammar base distribution
          (display "\n### Print grammars to ")(disp out-file)
          ;; compute maximal-rule-counts  
		  (disp "\n### Approximating AG-PCFG")
		  (approximate-pcfg observed-trees)
		  (when is-debug (print-hash maximal-rule-counts "\n### maximal-rule-counts"))
		  
		  ;; output
		  (print-grammar (make-adaptor-grammar a b maximal-rule-counts ag-base-pcfg) (open-output-file out-file) #t)
          
          )))))





