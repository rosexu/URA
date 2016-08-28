(load "PatMatch.cl")
(load "RuleUse.cl")
(require "sb-rt")
(setq q1 '((query (x y) ((definition (A C) x)) ())))
(setq q2 '((query (x y z) ((relation f x y) (relation f x z)) ())))
(setq q3 '((query (x y) ((relation f x z) (relation f y z)) ())))
(setq q4 '((query (x y) ((definition (A B) x)) ())))
(setq q5 '((query (x) ((definition (A1 A2 A3) y) (relation g x y)) ())))
(setq q6 '((query (x) ((definition (A1 A2 A3) y) (relation f y x)) ())))
(setq q8 '((query (x) ((definition (C1 C2 C3) z) (relation f x z) (relation f y z)) ())))
(setq q9 '((query (x) ((definition (A1 String A2) x)) ())))

(setq q8test '((query (x) ((definition (A B) x) (definition (C D) x)) ())))

; Exercises all rules.
(setq comp3 '((query (x y z)
					((definition (A C) x) (definition (C) y) (relation x y z)) ; rule 1
					())
			  (query (x y z h i j u v)
					((definition (M N) x) ; rule 4
					 (definition (String) y) ; rule 9
					 (definition (E1 E2 E3) i) ; rule 8
					 (definition (D1 D2 D3) fr) ; rule5
					 (relation f x y) (relation f x z) ; rule 2
					 (relation f h i) (relation f j i) ; rule 3 and 8
					 (relation g h fr)) ; for rule 5 to match b1, b2, b3
					())
				))
(setq temp '((query (x y z)
					((definition (A C) x) (definition (C) y) (relation x y z)) ; rule 1
					())
			  (query (x y z h i j u v)
					((definition (M N) x) ; rule 4
					 (definition (String) y) ; rule 9
					 (definition (E1 E2 E3) i) ; rule 8
					 (definition (D1 D2 D3) fr) ; rule5
					 (relation f x y) (relation f x z) ; rule 2
					 (relation f h i) (relation f j i) ; rule 3 and 8
					 (relation g h fr)) ; for rule 5 to match b1, b2, b3
					())
				))
(initPatMatch)

(defvar intermediate '())

;*****************************************************************
; query-parts is created to reduce the number of parameters passed
; into helper functions that is used to generate multiple queries.
;*****************************************************************
; vars: list of symbols
; lf (list front): front of list of defs and rels
; lm1 (list middle 1) : middle 1 of list of defs and rels
; lm2 (list middle 2) : middle 2 of list of defs and rels
; lb (list back): back of list of defs and rels
; cf (concept front): front of list of concept symbols
; cb (concept back): back of list of concept symbols
; f: a symbol denoting a function
; v1: a symbol
; v2: a symbol
(defstruct query-parts (vars) (lf) (lm1) (lm2) (lb) (cf) (cb) (f) (v1) (v2))

(loadrules '(
	(rule8Main
		(>* front
			(query > vars
				(>* lf
					(definition > clst > mid)
				>* lm1
					(relation > f > v1 < mid)
				>* lm2
					(relation < f > v2 < mid)
						where (not (eq <q v1 <q v2)) ; v1 != v2
				>* lb)
				> apdRules
					where (not (exist '(r8 < mid < v1 < v2) <q apdRules)))
		>* back)
		(<< front
			(query < vars
				(<< lf
					(definition < clst < mid)
				<< lm1
					(relation < f < v1 < mid)
				<< lm2
					(relation < f < v2 < mid)
				<< lb)
				< newApdRules)
		<< back
		<< newQueries)
		(Bindq newApdRules '(<< apdRules (r8 < mid < v1 < v2))
			   newQueries (genR8Queries <q f
			   						    <q clst
			   						    (make-query-parts
										   	:vars <q vars
										   	:lf <q lf
										   	:lb <q lb
										   	:lm1 <q lm1
										   	:lm2 <q lm2
										   	:v1 <q v1
										   	:v2 <q v2)
			   						   )))
))

; Used to mock what is returned from the TBox.
; A [ B : f1, ..., fk -> f belong to T
(defun getPFDs (f)
	'(f1 f2 f3))
(defun getA (f) 'A)
(defun getB (f) 'B)

(defun getMaximalSuccessors (As)
	'(B21 B22))

; Given a list of functions lstf (f1, ..., fk) and variables x
; and y, generate a list of relations as follows:
; '((relation f1 x z1) (relation f1 y z1) ...
;   (relation fk x zk) (relation fk y zk))
(defun makeRelations (lstf x y)
	(cond
		((null lstf) nil)
		(t (let ((freshVar (gensym)))
			(cons `(relation ,(car lstf) ,x ,freshVar)
				(cons
				 	`(relation ,(car lstf) ,y ,freshVar)
				 	(makeRelations (cdr lstf) x y)))))))

;Test: (makeRelations '(f1 f2 f3) 'x 'y)

; Helper for getAllBCombinations: adds item to the front of each
; list in lstOflst.
(defun addToFront (item lstOflst)
	(cond
		((null lstOflst) nil)
		(t (cons (cons item (car lstOflst))
				 (addToFront item (rest lstOflst))))))

(sb-rt:deftest addToFront-empty (addToFront 'Something '()) nil)
(sb-rt:deftest addToFront-empty2 (addToFront 'Something '(() ())) ((Something) (Something)))
(sb-rt:deftest addToFront-one (addToFront 'Something '((x) (y) (z))) ((Something x) (Something y) (Something z)))

; Get all combination of Bs such that for each B, we either
; choose a definition for x or y.
; It should yield 2^(length Bs) results.
(defun getAllBCombinations (Bs var1 var2)
	(cond
		((null Bs) '(nil))
		(t (append (addToFront `(definition (,(car Bs)) ,var1) (getAllBCombinations (cdr Bs) var1 var2))
				 (addToFront `(definition (,(car Bs)) ,var2) (getAllBCombinations (cdr Bs) var1 var2))))))

(sb-rt:deftest getAllBCombinations-one (getAllBCombinations '(B1) 'x 'y) (((definition (B1) x)) ((definition (B1) y))))
(sb-rt:deftest getAllBCombinations-zero (getAllBCombinations '() 'x 'y) (nil))
; (sb-rt:deftest getAllBCombinations-multi (getAllBCombinations '(B1 B2) 'x 'y)
; 	(((relation B1 x) (relation B2 x))
; 	 ((relation B1 x) (relation B2 y))
; 	 ((relation B2 y) (relation B2 x))
; 	 ((relation B2 y) (relation B2 y))))

;*************************************************************
; Helper function for genR8Queries
;*************************************************************
; part1: (A x)
; Cs: list of symbols
; queryInfo: query-parts struct containing query information.
; Returns: list of queries
;*************************************************************
(defun genR8QueriesHelper (part1 BComb relations queryInfo)
	(cond
		((null BComb) nil)
		(t (cons `(query ,(query-parts-vars queryInfo)
						  (,@(query-parts-lf queryInfo)
						  		,@part1
						  		,@(car BComb)
						   ,@(query-parts-lm1 queryInfo)
						   ,@(query-parts-lm2 queryInfo)
						   ,@(query-parts-lb queryInfo)
						   ,@relations
						   	)
						  (
						  	;(r3 ,(query-parts-v1 queryInfo) ,(query-parts-v2 queryInfo))
						  ))
				(genR8QueriesHelper part1 (cdr BComb) relations queryInfo)
			)
		)
	)
)

;*************************************************************
; Generates Queries for Rule 8.
; v1 -f-> z <-f- v2, (definition (C1, ..., Ck) z)
;*************************************************************
; f: function
; Cs: list of symbols
; queryInfo: query-parts struct containing query information.
; Returns: list of queries
;*************************************************************
(defun genR8Queries (f Cs queryInfo)
	(let* ((fs (getPFDs f))
		   (A (getA f))
		   (B (getB f))
		   (BComb (getAllBCombinations (getMaximalSuccessors Cs)
		   							   (query-parts-v1 queryInfo)
		   							   (query-parts-v2 queryInfo)))
		   (rels (makeRelations fs (query-parts-v1 queryInfo) (query-parts-v2 queryInfo))))
	(append (genR8QueriesHelper `((definition (,A) ,(query-parts-v1 queryInfo))
								  (definition (,B) ,(query-parts-v2 queryInfo)))
								  BComb
								  rels
								  queryInfo)
		 	(genR8QueriesHelper `((definition (,A) ,(query-parts-v1 queryInfo))
								  (definition (,B) ,(query-parts-v2 queryInfo)))
		 						  BComb
		 						  rels
		 						  queryInfo))
	)
)

; To be applied after rule8 is applied to merge duplicate
; definitions of the form (definition (x1 ... xk) x)
; (definition (y1 ... yk) x) in a single query.
(loadrules '(
	(mergeDuplicateDef
		(>* front
			(query > vars
				(>* lf
					(definition > clst1 > v1)
				>* lm
					(definition > clst2 < v1)
				>* lb)
				> apdRules)
		>* back)
		(<< front
			(query < vars
				(<< lf
					(definition < mergedlst < v1)
				<< lm
				<< lb)
				< apdRules)
		<< back)
		(Bindq mergedlst (append <q clst1 <q clst2)))))

(loadrules '(
    (removeDupRelAfterSubstitution
        (>* front
            (query > vars
                (>* lf
                    (relation > f > v1 > v2)
                >* lm
                    (relation < f < v1 < v2)
                >* lb)
            > apdRules)
         >* back)
        (<< front
            (query < vars
                (<< lf
                    (relation < f < v1 < v2)
                << lm
                << lb)
            < apdRules)
        << back)
    )
))

; Primitive types
(loadrules '(
	(rule9
		(>* front
			(query > vars
				(>* lf
					(definition (>* cf >or (String Int) c >* cb) > v1)
						where (not (null (getMaximalPredecessors2 <q c)))
				>* lb)
				> apdRules
					(where (not (exist '(r9 < c < v1) <q apdRules))))
		>* back)
		(<< front
			(query < vars
				(<< lf
					(definition (<< cf < c << cb) < v1)
				<< lb)
				< newApdRules)
			<< back
			<< queries
			)
		(Bindq maxPreds (getMaximalPredecessors2 <q c)
			   queries (genR9Queries
			   	<q c
			   	(getMaximalPredecessors2 <q c)
			   	(make-query-parts
				   	:vars <q vars
				   	:lf <q lf
				   	:lb <q lb
				   	:cf <q cf
				   	:cb <q cb
				   	:v1 <q v1))
			   newApdRules '(<< apdRules (r9 < c < v1)))
	)
))

; (setq queryInfo (make-query-parts :vars '(x y) :lf '(definition front) :lb '(definition back)
; 	:cf '(C1 C2) :cb '(C4 C5) :v1 'x))

;*********************************************************************
; Generate Quries for Rule 9.
;*********************************************************************
; Concept: a symbol.
; maxPreds: list of symbols of Maximal Predecessors.
; queryInfo: query-parts struct containing query information.
;*********************************************************************
(defun genR9Queries (Concept maxPreds queryInfo)
	(cond
		((null maxPreds) nil)
		(t (let* ((freshVar (getFreshVar Concept))
				  (rel (getRelation Concept (car maxPreds))))
			(cons `(query ,(query-parts-vars queryInfo)
						  (,@(query-parts-lf queryInfo)
						   		(definition (,@(query-parts-cf queryInfo)
						   					,@(query-parts-cb queryInfo))
						   					,(query-parts-v1 queryInfo))
						   		(definition (,(first maxPreds)) ,freshVar)
						   ,@(query-parts-lb queryInfo)
						   		(relation ,rel ,freshVar ,(query-parts-v1 queryInfo)))
						  ())
					(genR9Queries Concept (rest maxPreds) queryInfo))
		))
	)
)

; Helper for rule 9, returns whether a concept is a datatype.
(defun isDataType (Concept)
	(cond
		((eq Concept 'String) t)
		((eq Concept 'Int) t)
		(t nil)))

(sb-rt:deftest isDataType-string (isDataType 'String) t)
(sb-rt:deftest isDataType-int (isDataType 'Int) t)
(sb-rt:deftest isDataType-other (isDataType 'Something) nil)

; Get the function that maps concept c1 to concept c2.
(defun getRelation (c1 c2)
	'name)

(sb-rt:deftest getrelation-test (getRelation 'A 'B) name)

; Create a new symbol given the concept it is a predecessor of.
; 'A -> 'A_PRED (predecessor of A)
(defun getFreshVar (Concept)
	(intern (concatenate 'string (string Concept) "_PRED")))

(loadrules '(
	(rule6
		(>* front
			(query > vars
				(>* lf (definition > clst > v1)
				>* lm (relation > f < v1 > v2)
					where (not (or (existInVars <q v1 <q vars)
								   (existInList <q v1 <q lf)
								   (existInList <q v1 <q lm)
								   (existInList <q v1 <q lb)))
				>* lb)
				> apdRules
					where (not (exist '(r6 < v1) <q apdRules)))
		>* back)
		(<< front
			(query < vars
				(<< lf (definition < clst < v1)
				<< lm (relation < f < v1 < v2)
				<< lb)
				< newApdRules)
			<< back
			; start new query
			(query < vars
				((definition < maxSucc < v2)
				<< lf
				<< lm
				<< lb)
				()))
		(Bindq maxSucc (getMaximalSuccessors <q clst)
			   newApdRules '(<< apdRules (r6 < v1)))
	)
))

(loadrules '(
(rule5
	(>* front
		(query > vars
			(>* lf (definition > clst > var)
			>* lm (relation > f > v1 < var)
			>* lb
				where (not (or (existInVars <q var <q vars)
						  	   (existInList <q var <q lf)
						  	   (existInList <q var <q lm)
						  	   (existInList <q var <q lb))))
			> apdRules
				where (not (exist '(r5 < var) <q apdRules)))
	>* back)
	(<< front
		(query < vars
			(<< lf (definition < clst < var)
			<< lm (relation < f < v1 < var)
			<< lb)
			< newApdRules)
		<< back
		; start new query
		;<< newQuery
		(query < vars
 			((definition < maxPred < v1)
 			<< lf
 			<< lm
 			<< lb)
 			()))
	(Bindq maxPred (getMaximalPredecessors <q clst)
		   ; newQuery (filterQueries
		   ; 				`((query < vars
					; 		((definition < maxPred < v1)
					; 		<< lf
					; 		<< lm
					; 		<< lb)
					; 	())) ; queries to be added
					; 	'(<< front
					; 		(query < vars
					; 			(<< lf (definition < clst < var)
					; 			<< lm (relation < f < v1 < var)
					; 			<< lb)
					; 			< newApdRules)
					; 		<< back) ; existing queries
					; 	'() ; result
					; )
		   newApdRules '(<< apdRules (r5 < var)))
)))

(defun existInVars (var lst)
	(PutBindVal 'var var)
	(Match
		'(>* vf > v where (eq <q v <q var) >* vback)
		lst))

(sb-rt:deftest existinvars-empty (existInVars 'x '()) nil)
(sb-rt:deftest existinvars-one (existInVars 'x '(x)) t)
(sb-rt:deftest existinvars-multi (existInVars 'x '(y x z)) t)
(sb-rt:deftest existinvars-none (existInVars 'x '(s u v)) nil)


(defun existInList (var lst)
	(PutBindVal 'var var)
	(Match
		'(>* front2
			(relation > func > var1 > var2)
				where (or (eq <q var1 <q var) (eq <q var2 <q var))
			>* back)
		lst))

(sb-rt:deftest existInList-empty (existInList 'x '()) nil)
(sb-rt:deftest existInList-left (existInList 'x '((relation f x y))) t)
(sb-rt:deftest existInList-right (existInList 'x '((relation f y x))) t)

(defun getMaximalPredecessors (As)
	'(B11 B12 B13 B14))

(defun getMaximalPredecessors2 (A)
	(cond
		((eq A 'String) '(Person Dept))
		((eq A 'Int) '(Student Class))
		(t nil)))

(sb-rt:deftest getMaximalPredecessor-string (getMaximalPredecessors2 'String) (Person Dept))

(loadrules '(
(rule1
 	(>* front
 		(query > vars
			(>* lf (definition (>* cf > c1 >* cm > c2 >* cb) > var)
				where (or (isSubsetOfNotType <q c1 <q c2)
						  (isSubsetOfNotType <q c2 <q c1))
			 >* lb)
			> apdRules)
  		>* back)
 	(<< front << back))))

(loadrules '(
(rule2Main
	(>* front
		(query > vars
		   	(>* lf (relation > f > v1 > v2)
			 >* lm (relation < f < v1 > v3
			 			where (not (eq <q v2 <q v3))
			 		)
			 >* lb)
		   	> apdRules)
		>* back)
	(<< front (query < subbedVars < subbedBody (<< apdRules (r2 < f < v1))) << back)
	;(<< front << newQuery << back)
	(Bindq subbedVars (substitute <q v2 <q v3 <q vars)
		   subbedBody (subBody '(<< lf (relation < f < v1 < v2) << lm << lb) <q v2 <q v3)
		   ; mutation (setq intermediate (list (list 'query (substitute <q v2 <q v3 <q vars) (subBody '(<< lf (relation < f < v1 < v2) << lm << lb) <q v2 <q v3) '(<< apdRules (r2 < f < v1)))))
		   ; mutation2 (applyRuleControl '(Call repRemoveDupRelAndMergeDupDefs) intermediate)
		   ; newQuery (filterQueries intermediate
		   ; 						   '(<< front << back) ; existing queries
		   ; 						   '())
		   ))))

(loadrules '(
(rule3Main
	(>* front
		(query > vars
			(>* lf (relation > f > v1 > v2)
			 >* lm (relation < f > v3 < v2
			 			(where (not (eq <q v1 <q v3)))
			 		)
			 >* lb)
			> apdRules
				where (not (exist '(r3 < v1 < v3) <q apdRules)))
		>* back)
	(<< front (query < vars
					(<< lf (relation < f < v1 < v2)
					<< lm (relation < f < v3 < v2)
					<< lb)
					< newApdRules)
		<< back (query < subbedVars < subbedBody ()))
	(Bindq subbedVars (substitute <q v3 <q v1 <q vars)
		   subbedBody (subBody '(<< lf << lm (relation < f < v3 < v2) << lb) <q v3 <q v1)
		   newApdRules '(<< apdRules (r3 < v1 < v3)))))
)

(loadrules '(
(rule4
	(>* front
		(query > vars
		   (>* lf (definition (>* cf > c1 >* cm > c2 >* cb) > var)
		   		where (or (isSubsetOfType <q c1 <q c2)
		   				  (isSubsetOfType <q c2 <q c1))
		   	>* lb)
		   > apdRules)
		>* back)
	(<< front < new << back)
	(Bindq new (cond
				((isSubsetOfType <q c1 <q c2) '(query < vars (<< lf (definition (<< cf << cm < c2 << cb) < var) << lb) (<< apdRules (r4 < var))))
				(t '(query < vars (<< lf (definition (<< cf << cm < c1 << cb) < var) << lb) (<< apdRules (r4 < var)))))))))

(defun exist (rule ruleLst)
	(cond
		((null ruleLst) nil)
		((equal (car ruleLst) rule) t)
		(t (exist rule (cdr ruleLst)))))

; substitute y for all x in a list of definitions and relations
; (subBody '((relation x y z) (definition A x)) y x)
; => '((relation y y z) (definition A y))
(defun subBody (lst y x)
	(cond
		((not (listp lst)) nil)
		((null lst) nil)
		((listp (car lst))
			(cons (substitute y x (car lst) :start 1) (subBody (cdr lst) y x)))
		))

; Return whether A is a subset of B.
(defun isSubsetOfType (A B)
	(cond
		((and (eq A 'N) (eq B 'M)) t)
		(t nil)))

; Returns true if A is a subset of (not B).
(defun isSubsetOfNotType (A B)
	(cond
		((and (eq A 'C) (eq B 'A)) t)
		(t nil)))

(loadrules '(
	(removeDups
		(>* front > q >* mid < q >* back)
		(<< front < q << mid << back))))

(LoadControl
	'(removeAllDups (Rep removeDups)))

(LoadControl
	'(rule8
		(Seq rule8Main
			 (Rep mergeDuplicateDef))))

(LoadControl
    '(rule2
        (Seq rule2Main
             (Rep removeDupRelAfterSubstitution)
             (Rep mergeDuplicateDef))))

(LoadControl
    '(rule3
        (Seq rule3Main
             (Rep removeDupRelAfterSubstitution)
             (Rep mergeDuplicateDef))))

(LoadControl '(repMergeDupDefs
	(Rep mergeDuplicateDef)))

(LoadControl '(repRemoveDupRelAndMergeDupDefs
	(Seq (Rep removeDupRelAfterSubstitution)
		 (Rep mergeDuplicateDef))))

; Sort by length of x.
;(stable-sort tt #'(lambda (x y) (> (length x) (length y))))

(defvar matchings (make-hash-table))

; returns hash of all the matchings, return nil if none found.
; Match vars2 -> vars1
(defun matchVars (vars1 vars2 hash)
    (cond
        ((null vars1) hash)
        (t (let* ((firstVar1 (car vars1))
                  (firstVar2 (car vars2))
                  (matchedSym (gethash firstVar2 hash)))
            (cond
                ((null matchedSym) (setf (gethash firstVar2 hash) firstVar1)
                                   (matchVars (cdr vars1) (cdr vars2) hash))
                ((eq firstVar1 matchedSym) (matchVars (cdr vars1) (cdr vars2) hash))
                (t nil)
            ))
        )))

(sb-rt:deftest matchVars-empty (matchVars '(X Y) '(X X) (make-hash-table)) nil)
; (sb-rt:deftest matchVars-empty (matchVars '() '() (make-hash-table)) (make-hash-table))
; (sb-rt:deftest matchVars-one (matchVars '(X) '(Y) (make-hash-table))
;                                (progn (defparameter ht (make-hash-table))
;                                       (setf (gethash 'Y ht) 'X)
;                                       ht))

; variable -> set of past binded values
; variables must be free, those that are not free are taken care of in matchVars.
; TODO: populate pastMatchings
(defvar pastMatchings (make-hash-table))

; TODO: Is deleting past matching after backtrack needed? Yes I think so.
(defun backtrack (cont qbody1 qbody2)
	; (print "backtrack")
	; (print cont)
	(cond
		((null cont) nil) ; backtrack fails if continuation is empty, nothing has been executed before
		((eq (caar cont) 'definition) ; definition
			(let* ((def (car cont))
				   (clst (cadr def))
				   (var (caddr def)))
				(cond
					((member var boundVars) (backtrack (rest cont) qbody1 (cons (car cont) qbody2)))
					((existInCont var (rest cont))
						(backtrack (rest cont) qbody1 (cons (car cont) qbody2)))
					((null (matchDefFree clst var qbody1)) ; can't match because no available free matching
						; (print (format t "reset ~a" def))
						(setf (gethash var pastMatchings) nil) ; only set to nil if it doesn't exist in rest cont
						(backtrack (rest cont) qbody1 (cons (car cont) qbody2)))
					(t (matchBody cont qbody1 qbody2)) ; new match for definition => keep matching body
				)))
		((eq (caar cont) 'relation) ; relation
			(let* ((rel (car cont))
				   (f (cadr rel))
				   (x (caddr rel))
				   (y (cadddr rel)))
				(cond
					((and (member x boundVars) (member y boundVars)) ; skip and keep backtracking
						(backtrack (rest cont) qbody1 (cons (car cont) qbody2)))
					((or (and (existInCont x (rest cont)) (existInCont y (rest cont)))
						 (and (existInCont x (rest cont)) (member y boundVars))
						 (and (member x boundVars) (existInCont y (rest cont))))
						; (print "exist previously")
						(backtrack (rest cont) qbody1 (cons (car cont) qbody2)))
					((null (matchRel f x y qbody1)) ; no available free matching
						; (print (format t "reset ~a" rel))
						(setf (gethash x pastMatchings) nil)
						(setf (gethash y pastMatchings) nil)
						(backtrack (rest cont) qbody1 (cons (car cont) qbody2)))
					(t ;(print "found new match")
					   (matchBody cont qbody1 qbody2)) ; found new match and updated current matching
			))
		)))

(defun existInCont (var cont)
	(cond
		((null cont) nil)
		((eq (caar cont) 'definition)
			(let ((def (car cont)))
				(or (equal (caddr def) var) (existInCont var (rest cont)))))
		((eq (caar cont) 'relation)
			(let ((rel (car cont)))
				(or (equal (caddr rel) var) (equal (cadddr rel) var) (existInCont var (rest cont)))))))

(sb-rt:deftest existInCont-empty (existInCont 'x '()) nil)

(sb-rt:deftest existInCont-y1 (existInCont 'x
  '((DEFINITION (B21 B22) Y) (DEFINITION (B11 B12 B13 B14 A) H)
   (DEFINITION (M) X) (DEFINITION (B B21 B22) J) (RELATION F X Y)
   (RELATION F1 H #:G1035) (RELATION F1 J #:G1035) (RELATION F2 H #:G1036)
   (RELATION F2 J #:G1036) (RELATION F3 H #:G1037) (RELATION F3 J #:G1037)))
	t)

(sb-rt:deftest existInCont-y2 (existInCont 'STRING_PRED
	'((DEFINITION (DEPT) STRING_PRED) (DEFINITION NIL Y) (DEFINITION (M) X)
 	  (DEFINITION (B11 B12 B13 B14 A B B21 B22) J)))
    t)

; returns true if there's a match, nil otherwise.
; Matches qbody2 -> qbody1
(defun matchBody (cont qbody1 qbody2)
    (cond
        ((null qbody2) t)
        ((eq (caar qbody2) 'definition) ; definition
            (let* ((def (car qbody2))
            	   (defMatched (matchDef (cadr def) (caddr def) qbody1 (gethash (caddr def) matchings))))
            	(cond
            		((null defMatched)
            			; (maphash #'print-hash-entry matchings)
            			; (print (format t "failed to match ~a with ~a" def (gethash (caddr def) matchings)))
            			; (maphash #'print-hash-entry pastMatchings)
		     			(backtrack cont qbody1 qbody2))
            		(t (matchBody (cons def cont) qbody1 (rest qbody2))) ; def matched
            		)))
                ; (and (matchDef (cadr def) (caddr def) qbody1 (gethash (caddr def) matchings))
                ; 	 (matchBody qbody1 (rest qbody2)))))
        ((eq (caar qbody2) 'relation) ; relation
        	(let* ((rel (car qbody2))
        		   (relMatched (matchRel (cadr rel) (caddr rel) (cadddr rel) qbody1)))
        		(cond
        			((null relMatched)
        				; (maphash #'print-hash-entry matchings)
        				; (print (format t "failed to match ~a with ~a and ~a" rel (gethash (caddr rel) matchings) (gethash (cadddr rel) matchings)))
        				; (maphash #'print-hash-entry pastMatchings)
        				(backtrack cont qbody1 qbody2))
        			(t (matchBody (cons rel cont) qbody1 (rest qbody2)))
    			)))
        		; (and (matchRel (cadr rel) (caddr rel) (cadddr rel) qbody1)
        		; 	 (matchBody (cons rel cont) qbody1 (rest qbody2)))))
    ))

; match relations
; TODO: check pastMatchings so matchRel don't use any from there.
(defun matchRel (f x y qbody)
	(cond
		((null qbody) nil) ; backtrack
		((eq (caar qbody) 'definition) (matchRel f x y (rest qbody)))
		(t (let* ((bindx (gethash x matchings))
				  (bindy (gethash y matchings))
				  (rel (car qbody))
				  (matchf (cadr rel))
				  (matchx (caddr rel))
				  (matchy (cadddr rel)))
			 ; (print rel)
			 ; (print bindx)
			 ; (print bindy)
			(cond
				((and (null bindx) (null bindy)) ; x, y free
				 (cond
				 	((equal f matchf)
				 		(let* ((pastMatchingx (gethash x pastMatchings))
				 			   (pastMatchingy (gethash y pastMatchings)))
				 		(cond
				 			((null (member matchx pastMatchingx)) ; x matching works
				 				(progn
				 					(setf (gethash x matchings) matchx)
				 					(setf (gethash x pastMatchings) (adjoin matchx pastMatchingx))
				 					(setf (gethash y matchings) matchy)
				 					(setf (gethash y pastMatchings) (adjoin matchy pastMatchingy))
				 					t
				 				))
				 			((null (member matchy pastMatchingy)) ; y matching works, x does not
				 				(progn
				 					(setf (gethash y matchings) matchy)
				 					(setf (gethash y pastMatchings) (adjoin matchy pastMatchingy))
				 					t
				 					))
				 			(t (matchRel f x y (rest qbody))) ; none of the matching works
				 			)
				 		))
				 	(t (matchRel f x y (rest qbody))))
				)
				((null bindx) ; x free
				 (cond
					((and (equal f matchf) (equal y matchy))
						(let ((pastMatchingx (gethash x pastMatchings)))
							(cond
								((null (member matchx pastMatchingx))
									(progn
										(setf (gethash x matchings) matchx)
										(setf (gethash x pastMatchings) (adjoin matchx pastMatchingx))
										t
									)
								)
								(t (matchRel f x y (rest qbody)))
							)))
					(t (matchRel f x y (rest qbody)))))
				((null bindy) ; y free
			     (cond
			     	((and (equal f matchf) (equal x matchx))
						(let ((pastMatchingy (gethash y pastMatchings)))
							(cond
								((null (member matchy pastMatchingy))
									(progn
										(setf (gethash y matchings) matchy)
										(setf (gethash y pastMatchings) (adjoin matchy pastMatchingy))
										t
									)
								)
								(t (matchRel f x y (rest qbody)))
							)))
			     	(t (matchRel f x y (rest qbody)))))
				(t (cond ; x, y bound
						((equal (car qbody) `(relation ,f ,bindx ,bindy)) t)
						(t (matchRel f x y (rest qbody))))
				)
			)
		))))

(defun matchDef (clst var qbody binding)
    (cond
        ((null binding) (matchDefFree clst var qbody))
        (t (matchDefBound clst var qbody binding))))

; When the matching for var is unknown, match a definition.
(defun matchDefFree (clst var qbody)
	(cond
		((null qbody) nil) ; empty => no match
		((eq (caar qbody) 'relation) (matchDefFree clst var (rest qbody))) ; relation => match rest
		(t (let* ((def (car qbody)) ; is definition
				  (clstToMatch (cadr def))
				  (v (caddr def)))
			(cond
				((subsetp clstToMatch clst)
					(let ((pastMatching (gethash var pastMatchings)))
						(cond
							((null (member v pastMatching)) ; not in past matching
								 (progn (setf (gethash var pastMatchings) (adjoin v pastMatching))
   									    (setf (gethash var matchings) v)
									 	t))
							(t (matchDefFree clst var (rest qbody))) ; in past matchings
							)))
							 ; is subset, change set hashtable of mappings
				(t (matchDefFree clst var (rest qbody))))
			))))

; When the matching for var is known, match a definition.
(defun matchDefBound (clst var qbody val)
	; (print var)
	; (print val)
	; (print clst)
	; (print qbody)
    (cond
        ((null qbody) nil)
        ((eq (caar qbody) 'definition)
            (let* ((def (car qbody))
                   (clstToMatch (cadr def))
                   (varToMatch (caddr def)))
            (cond
                ((and (eq varToMatch val) (subsetp clstToMatch clst)) t)
                (t (matchDefBound clst var (rest qbody) val)))))
        (t (matchDefBound clst var (rest qbody) val))
    	))

; query: query to check
; querylst: lst of queries to check against
; returns: whether query is subsumed in one of the queries in querylst
(defun isQuerySubsumed (query querylst)
	(cond
		((null querylst) nil)
		((isIncluded query (car querylst)) t)
		(t (isQuerySubsumed query (cdr querylst)))))

; returns: whether q1 is subsumed by q2
(defun isIncluded (q1 q2)
	(setq matchings (make-hash-table))
	(setq pastMatchings (make-hash-table))
	(let ((mapping (matchVars (cadr q2) (cadr q1) (make-hash-table))))
		(cond
			((null mapping) nil)
			(t (setq matchings mapping)
			   (setq boundVars (cadr q1))
			   (matchBody '() (caddr q2) (caddr q1))))))

; result is empty lst to start
(defun filterQueries (queries existingQueries result)
	;(print "filter")
	;(print (car queries))
	(cond
		((null existingQueries) queries)
		((null queries) result)
		((isQuerySubsumed (car queries) existingQueries)
			(filterQueries (rest queries) existingQueries result))
		(t (filterQueries (rest queries) existingQueries (cons (car queries) result)))))


(defun filterAll (queries front result)
	(setq counter (+ counter 1))
	(cond
		((null queries) result)
		((null (filterQueries (list (car queries)) front '())) ; subsumed by front
			(filterAll (rest queries) front result)) ; no need to add to front
		((null (filterQueries (list (car queries)) (rest queries) '())) ; subsumed by back
			(filterAll (rest queries) front result)) ; no need to add to front since deleted
		(t (filterAll (rest queries) (cons (car queries) front) (cons (car queries) result))) ; not subsumed
	)
)

(sb-rt:deftest subsume-y1 (isQuerySubsumed
	'(QUERY (X Y Y J I J U V)
  	((DEFINITION (B21 B22) Y) (DEFINITION (B11 B12 B13 B14 A B21 B B22) J)
   	(DEFINITION (M) X) (RELATION F X Y) (RELATION F1 J #:G1035)
   	(RELATION F2 J #:G1036) (RELATION F3 J #:G1037))
  	NIL)
  	'((QUERY (X Y Y J I J U V)
  	((DEFINITION (B21 B22) Y) (DEFINITION (B11 B12 B13 B14 A B22 B B21) J)
   	(DEFINITION (M) X) (RELATION F X Y) (RELATION F1 J #:G1035)
   	(RELATION F2 J #:G1036) (RELATION F3 J #:G1037))
  	NIL))) t)

(sb-rt:deftest subsume-y2 (isQuerySubsumed
'(QUERY (X Y Y J I J U V)
  ((DEFINITION (B11 B12 B13 B14 A B21 B B22) J) (DEFINITION (M) X)
   (DEFINITION NIL Y) (DEFINITION (DEPT) STRING_PRED) (RELATION F X Y)
   (RELATION NAME STRING_PRED Y) (RELATION F1 J #:G635) (RELATION F2 J #:G636)
   (RELATION F3 J #:G637))
  ((R6 STRING_PRED)))
 '((QUERY (X Y Y J I J U V)
  ((DEFINITION (B11 B12 B13 B14 A B21 B22 B) J) (DEFINITION (M) X)
   (DEFINITION NIL Y) (DEFINITION (DEPT) STRING_PRED) (RELATION F X Y)
   (RELATION NAME STRING_PRED Y) (RELATION F1 J #:G635) (RELATION F2 J #:G636)
   (RELATION F3 J #:G637))
  ((R6 STRING_PRED))))) t)

(sb-rt:deftest subsume-n2 (isQuerySubsumed
	'(QUERY (X Y Y H I J U V)
  ((DEFINITION (B21 B22) Y) (DEFINITION (B11 B12 B13 B14 A) H)
   (DEFINITION (M) X) (DEFINITION (B B21 B22) J) (RELATION F X Y)
   (RELATION F1 H #:G1035) (RELATION F1 J #:G1035) (RELATION F2 H #:G1036)
   (RELATION F2 J #:G1036) (RELATION F3 H #:G1037) (RELATION F3 J #:G1037))
  ((R3 H J)))
 	'((QUERY (X Y Y J I J U V)
  ((DEFINITION (B21 B22) Y) (DEFINITION (B11 B12 B13 B14 A B B21 B22) J)
   (DEFINITION (M) X) (RELATION F X Y) (RELATION F1 J #:G1035)
   (RELATION F2 J #:G1036) (RELATION F3 J #:G1037))
  NIL)))
	nil)


(sb-rt:deftest subsume-n1 (isQuerySubsumed
'(QUERY (X Y Y H I J U V)
  ((DEFINITION (M) X) (DEFINITION (STRING) Y) (DEFINITION (E1 E2 E3) I)
   (DEFINITION (D1 D2 D3) FR) (RELATION F X Y) (RELATION F H I)
   (RELATION F J I) (RELATION G H FR))
  ((R2 F X) (R4 X) (R3 H J) (R5 FR) (R8 I H J) (R9 STRING Y)))
'((QUERY (X Y Y H I J U V)
  ((DEFINITION (B11 B12 B13 B14) H) (DEFINITION (M) X) (DEFINITION (STRING) Y)
   (DEFINITION (E1 E2 E3) I) (RELATION F X Y) (RELATION F H I)
   (RELATION F J I))
  ((R3 H J) (R8 I H J) (R9 STRING Y)))))
nil)

(sb-rt:deftest subsume-n3 (isQuerySubsumed
	'(QUERY (X Y Y J I J U V)
  ((DEFINITION (B11 B12 B13 B14 A B B21 B22) J) (DEFINITION (M) X)
   (DEFINITION NIL Y) (DEFINITION (DEPT) STRING_PRED) (RELATION F X Y)
   (RELATION NAME STRING_PRED Y) (RELATION F1 J #:G638) (RELATION F2 J #:G639)
   (RELATION F3 J #:G640))
  NIL)
 '((QUERY (X Y Y J I J U V)
  ((DEFINITION (B11 B12 B13 B14) J) (DEFINITION (M) X) (DEFINITION NIL Y)
   (DEFINITION (DEPT) STRING_PRED) (DEFINITION (E1 E2 E3) I) (RELATION F X Y)
   (RELATION F J I) (RELATION NAME STRING_PRED Y))
  NIL)))
 nil)

; TODO: pass this test.
; (isQuerySubsumed
; 	'(QUERY (X Y Y H I J U V)
;   ((DEFINITION (M) X) (DEFINITION NIL Y) (DEFINITION (PERSON) STRING_PRED)
;    (DEFINITION (A) H) (DEFINITION (B B21 B22) J) (DEFINITION (D1 D2 D3) FR)
;    (RELATION F X Y) (RELATION G H FR) (RELATION F1 H #:G690)
;    (RELATION F1 J #:G690) (RELATION F2 H #:G691) (RELATION F2 J #:G691)
;    (RELATION F3 H #:G692) (RELATION F3 J #:G692) (RELATION NAME STRING_PRED Y))
;   NIL)
;  '(
;  (QUERY (X Y Y H I J U V)
;   ((DEFINITION (M) X) (DEFINITION NIL Y) (DEFINITION (DEPT) STRING_PRED)
;    (DEFINITION (A) H) (DEFINITION (B B21 B22) J) (DEFINITION (D1 D2 D3) FR)
;    (RELATION F X Y) (RELATION G H FR) (RELATION F1 H #:G690)
;    (RELATION F1 J #:G690) (RELATION F2 H #:G691) (RELATION F2 J #:G691)
;    (RELATION F3 H #:G692) (RELATION F3 J #:G692) (RELATION NAME STRING_PRED Y))
;   NIL)))

(loadrules '(
(subsumption
 	(>* lst
 		where (progn (Bindq filtered (filterAll <q lst '() '()))
 			         (! < (length <q filtered) (length <q lst))))
 	(<< filtered)
 	;(Bindq filtered (filterAll <q lst '() '()))
 	)))

(LoadControl
	'(ApplyAllRules
		(Rep
			(Seq (Call removeAllDups) rule1 (Call rule2) rule4 (Call rule3) rule5 rule6 subsumption (Call rule8) rule9))
			 ))

(defun print-hash-entry (key value)
    (format t "The value associated with the key ~S is ~S~%" key value))

;(applyRuleControl '(Call ApplyAllRules) comp3)
;(applyRuleControl '(Call rule8) comp3)
;(applyRuleControl 'subsumption comp3)
(setq counter 0)

(sb-rt:do-tests)

(applyRuleControl 'rule1 q1)
(applyRuleControl 'rule2Main q2)
(applyRuleControl 'rule3Main q3)
(applyRuleControl 'rule4 q4)
(applyrulecontrol 'rule5 q5)
(applyrulecontrol 'rule6 q6)
(applyrulecontrol 'rule8Main q8)
(applyrulecontrol 'rule9 q9)