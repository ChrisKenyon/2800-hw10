; **************** BEGIN INITIALIZATION FOR ACL2s B MODE ****************** ;
; (Nothing to see here!  Your actual file is after this initialization code);

#|
Pete Manolios
Fri Jan 27 09:39:00 EST 2012
----------------------------

Made changes for spring 2012.


Pete Manolios
Thu Jan 27 18:53:33 EST 2011
----------------------------

The Beginner level is the next level after Bare Bones level.

|#

; Put CCG book first in order, since it seems this results in faster loading of this mode.
#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading the CCG book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "ccg/ccg" :uncertified-okp nil :dir :acl2s-modes :ttags ((:ccg)) :load-compiled-file nil);v4.0 change

;Common base theory for all modes.
#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s base theory book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "base-theory" :dir :acl2s-modes)

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s customizations book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "custom" :dir :acl2s-modes :uncertified-okp nil :ttags :all)

;Settings common to all ACL2s modes
(acl2s-common-settings)

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading trace-star and evalable-ld-printing books.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "trace-star" :uncertified-okp nil :dir :acl2s-modes :ttags ((:acl2s-interaction)) :load-compiled-file nil)
(include-book "hacking/evalable-ld-printing" :uncertified-okp nil :dir :system :ttags ((:evalable-ld-printing)) :load-compiled-file nil)

;theory for beginner mode
#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s beginner theory book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "beginner-theory" :dir :acl2s-modes :ttags :all)


#+acl2s-startup (er-progn (assign fmt-error-msg "Problem setting up ACL2s Beginner mode.") (value :invisible))
;Settings specific to ACL2s Beginner mode.
(acl2s-beginner-settings)

; why why why why 
(acl2::xdoc acl2s::defunc) ; almost 3 seconds

(cw "~@0Beginner mode loaded.~%~@1"
    #+acl2s-startup "${NoMoReSnIp}$~%" #-acl2s-startup ""
    #+acl2s-startup "${SnIpMeHeRe}$~%" #-acl2s-startup "")


(acl2::in-package "ACL2S B")

; ***************** END INITIALIZATION FOR ACL2s B MODE ******************* ;
;$ACL2s-SMode$;Beginner
#|

CS 2800 Homework 10 - Spring 2017


This homework is to be done in a group of 2-3 students. 

If your group does not already exist:

 * One group member will create a group in BlackBoard
 
 * Other group members then join the group
 
 Submitting:
 
 * Homework is submitted by one group member. Therefore make sure the person
   submitting actually does so. In previous terms when everyone needed
   to submit we regularly had one person forget but the other submissions
   meant the team did not get a zero. Now if you forget, your team gets 0.
   - It wouldn't be a bad idea for group members to send confirmation 
     emails to each other to reduce anxiety.

 * Submit the homework file (this file) on Blackboard.  Do not rename 
   this file.  There will be a 10 point penalty for this.

 * You must list the names of ALL group members below, using the given
   format. This way we can confirm group membership with the BB groups.
   If you fail to follow these instructions, it costs us time and
   it will cost you points, so please read carefully.


Names of ALL group members: Chris Kenyon, Izaak Branch

Note: There will be a 10 pt penalty if your names do not follow 
this format.
|#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
#|
 Inductive Proofs:
 - For all proofs below, solutions must be in the format described in class and
   in the notes. This includes:
     * Explicitly identifying an induction scheme and the function that gives
       rise to it.
     * Labeling general context (C1, C2....) and derived context.
     * Providing justifications for each piece of derived context.
     * Explicitly identifying axioms and theorems used
     * The if axioms and theorem substitutions are not required. You can use
       any other shortcuts previously identified.
     * PL can be given as justification for any propositional logic rules with the
      exceptions of Modus Ponens (MP) and Modus Tollens (MT)
     * Hocus Pocus (HP) is not permissible justification.
     * All arithmetic rules can be justified by writing "Arithmetic".
     
Previous homeworks (such as HW05) identify these requirements in more detail.

|#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
#|
For this homework you may want to use ACL2s to help you.

Technical instructions:

- open this file in ACL2s as hw10.lisp

- make sure you are in BEGINNER mode. This is essential! Note that you can
  only change the mode when the session is not running, so set the correct
  mode before starting the session.

- insert your solutions into this file where indicated (usually as "...")

- only add to the file. Do not remove or comment out anything pre-existing
  unless asked to.

- make sure the entire file is accepted by ACL2s. In particular, there must
  be no "..." left in the code. If you don't finish all problems, comment
  the unfinished ones out. Comments should also be used for any English
  text that you may add. This file already contains many comments, so you
  can see what the syntax is.

- when done, save your file and submit it as hw10.lisp

- avoid submitting the session file (which shows your interaction with the
  theorem prover). This is not part of your solution. Only submit the lisp
  file!

|#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
#|
Instructions for programming problems:

For each function definition, you must provide both contracts and a body.

You must also ALWAYS supply your own tests (unless otherwise noted). This is in 
addition to the tests sometimes provided. Make sure you produce sufficiently 
many new test cases. This means: cover at least the possible scenarios 
according to the data definitions of the involved types. For example, 
a function taking two lists should have at least 4 tests: all combinations 
of each list beingempty and non-empty.

Beyond that, the number of tests should reflect the difficulty of the
function. For very simple ones, the above coverage of the data definition
cases may be sufficient. For complex functions with numerical output, you
want to test whether it produces the correct output on a reasonable
number of inputs.

Use good judgment. For unreasonably few test cases we will deduct points.

|#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Part I: Induction schemes
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
#|

Below, you are given the proof obligations generated by
induction schemes. Your job is to define admissible functions, 
using defunc that give rise to these induction schemes. 
phi|(...) denotes phi under substitution ...
IF an admissible function is possible, write it and make sure 
that ACL2s accepts your function definition.
Otherwise, briefly explain why no admissible function can generate
that induction scheme and provide a sample call that would 
be problematic.

For these functions (f1-f7) you do not need to provide
tests (i.e., no check= forms are required). It is also
a good idea to make these functions as simple as possible.
|#

#|
Question 1A)
1. (not (rationalp x)) => phi
2. (and (rationalp x) (< x 0)) => phi
3. (and (rationalp x) (not (< x 0)) phi|((x (- x 1)))  => phi

|#
      
(defunc q1a (x)
  :input-contract (rationalp x)
  :output-contract (rationalp (q1a x))
  (if (< x 0)
    x
    (q1a (- x 1))))

#|
Question 1B)
1. (not (and (listp x)(integerp y))) => phi
2. (and (listp x)(integerp y)(endp x)) => phi
3. (and (listp x)(integerp y)(not (endp x))(equal y 0)) 
    => phi
4. (and (listp x)(integerp y)(not (endp x))
        (not (equal y 0)) (> y 0) phi|((x (rest x))(y (- y 1))) )
    => phi
5. (and (listp x)(integerp y)(not (endp x))
        (not (equal y 0)) (not (> y 0)) phi|((x (rest x))(y (+ y 1))) )
    => phi

|#

(defunc q1b (x y)
  :input-contract (and (listp x)(integerp y))
  :output-contract (integerp (q1b x y))
  (cond ((endp x) y)
        ((equal y 0) y)
        ((> y 0) (q1b (rest x) (- y 1)))
        (t (q1b (rest x) (+ y 1)))))

#|
Question 1C)
1. (not (and (listp x)(natp y))) => phi
2. (and (listp x)(natp y)(endp x)) => phi
3. (and (listp x)(natp y)(not (endp x)) phi|((x (rest x))(y (- y 1)))
    => phi

(defunc q1c (x y)
  :input-contract (and (listp x)(natp y))
  :output-contract (natp (q1c x y))
  (if (endp x) 
    y
    (q1c (rest x)(- y 1))))
 
This function which would give rise to the induction scheme above is not
admissible because its recursive case can violate the contract of inputting
a nat into q1c, as (- 0 1) is no longer a nat. A simple violating call
would be (q1c '(1 2 3) 0)

|#


#|
Question 1D)
NOTE: The induction scheme below has been slightly simplified to avoid
the expression being too unruly (eg for obligation 3 you would see 
(not (equal x 1)))
1. (not (natp x)) => phi
2. (and (natp x) (equal x 1)) => phi
3. (and (natp x) (equal x 2)) => phi
4. (and (natp x) (equal x 0)) => phi
5. (and (natp x) (not (equal x 1)) (not (equal x 2))
        (not (equal x 0)) phi|((x (- x 3))))  => phi

|#

(defunc q1d (x)
  :input-contract (natp x)
  :output-contract (natp (q1d x))
  (cond ((equal x 1) x)
        ((equal x 2) x)
        ((equal x 0) x)
        (t (q1d (- x 3)))))

;; The following functions are not trivial to admit into ACL2s in logic
;; mode. For f5-f7, if the function is "theoretically admissible" just 
;; convince yourself that it terminates, there are no body contract 
;; violations and IC=>OC.
;; Again, if no such function exists, explain why and provide a 
;; problematic input.
:program

#|
Question 1E)
1. (not (integerp x)) => phi
2. (and (integerp x) (< x -1)) => phi
4. (and (integerp x) (not (< x -1)) 
        phi|((x (- x 1))) phi|((x (- x 2)))  => phi

|#

(defunc q1e (x)
  :input-contract (integerp x)
  :output-contract (integerp (q1e x))
  (if (< x -1)
    x
    (+ (q1e (- x 1)) (q1e (- x 2)))))

#|
Question 1F)
1. (not (and (listp x)(natp y))) => phi
2. (and (listp x)(natp y)(equal (len x) y)) => phi
3. (and (listp x)(natp y)(not (equal (len x) y)))(> (len x) y)
   phi|((x (rest x)(+ y 1))) => phi
4. (and (listp x)(natp y)(not (equal (len x) y)))(not (> (len x) y))
   phi|((x (cons y x))(y (- y (len x)))) => phi

|#

(defunc q1f (x y)
  :input-contract (and (listp x)(natp y))
  :output-contract (natp (q1f x y))
  (cond ((equal (len x) y) y)
        ((> (len x) y) (q1f (rest x)(+ y 1)))
        (t (q1f (cons y x)(- y (len x))))))
        

#|
Question 1G)
1. (not (and (listp x) (integerp y))) => phi
2. (and (listp x) (integerp y) (endp x) (equal y -1)) => phi
3. (and (listp x) (integerp y) (not (and (endp x) (equal y -1)))
        (endp x)(< y -1) phi|((y (+ y 1)))) => phi 
4. (and (listp x) (integerp y) (not (and (endp x) (equal y -1)))
        (not (and (endp x)(< y -1)))
        (endp x) (phi|((x (cons 1 x)) (y (- y 1))))) => phi 
5. (and (listp x) (integerp y) (not (and (endp x) (equal y -1)))
        (not (and (endp x)(< y -1)))
        (not (endp x)) (phi|((x (rest x))))) => phi 

Hint: phi|((a (rest a)) (b b)) is the same as 
      phi|((a (rest a))).  You can leave off variable parameters 
      that don't change.
|#
(defunc q1g (x y)
  :input-contract (and (listp x)(integerp y))
  :output-contract (integerp (q1g x y))
  (cond ((and (endp x)(equal y -1)) y)
        ((and (endp x)(< y -1)) (q1g x (+ y 1)))
        ((endp x) (q1g (cons 1 x)(- y 1)))
        ((not (endp x)) (q1g (rest x) y))))


:logic
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; PART II: Quicksort
;; You will now write various functions involved
;; in the quicksort algorithm. 
;; See https://en.wikipedia.org/wiki/Quicksort for 
;; additional information about the algorithm.
;; You will also have to prove 
;; several conjectures along the way.
;; For each test? below, PROVE the conjecture (induction will 
;; probably be needed somewhere).  The conjecture  will be provided
;; in the comment.
;; Ex: (test? (implies (lorp l) (sortedp (qsort l))))
;; You will need to prove
;; phi: (lorp l) => (sortedp (qsort l))
;;
;; Make sure you clearly identify your induction scheme and what 
;; function it comes from for EACH proof.
;;
;; Please also note that since you are writing the functions before
;; you do the proofs, your implementation may change the proof. Some
;; implementations are easier to prove than others.  
;; *** If you get stuck with your proofs, consider revising your code
;; If everyone is getting stuck, I'm willing to provide function bodies, 
;; but I would like to wait and see if problems arise ***
;;
;; Some induction schemes are also easier to use than others.  
;; My stategy for choosing an I.S. is:
;; 1) Choose the simplest I.S. that changes variables like your functions will
;;    -> As a first pass, I always look at nind and listp in case they work.
;; 2) Make sure there are no variables in the I.S. that are not in the conjecture
;; 3) Choose an I.S. that provides useful context in your proof.
;; 4) Try to have your base cases in the I.S. match the recursive base cases.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#|

We start with some familiar definitions just in case they
are useful. You will be asked to
define functions later on. Make sure to use defunc.

(defunc listp (x)
  :input-contract t
  :output-contract (booleanp (listp x))
  (if (consp x)
      (listp (rest x))
    (equal x nil)))

(defunc app (a b) 
  :input-contract (and (listp a) (listp b))
  :output-contract (listp (app a b))
  (if (endp a)
      b
    (cons (first a) (app (rest a) b))))

(defunc rev (a) 
  :input-contract (listp a) 
  :output-contract (listp (rev a))
  (if (endp a)
      nil
    (app (rev (rest a)) (list (first a)))))

;; NOTICE: We slightly modified the definition of in
;; to help make the induction scheme easier to follow.
(defunc in (a X) 
  :input-contract (listp X)
  :output-contract (booleanp (in a X))
  (if (endp X)
      nil
    (if (equal a (first X))
        t
        (in a (rest X)))))

        
|#
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; GIVEN
;; del: Any x List -> List
;; (del e l) takes an element e and a list l
;; and removes the FIRST occurance of e from l
;; If e is not in l then l is returned.
(defunc del (e l)
  :input-contract (listp l)
  :output-contract (listp (del e l))
  (if (endp l)
    l
    (if (equal e (first l))
      (rest l)
      (cons (first l) (del e (rest l))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; GIVEN
;; perm: List x List -> Boolean
;; (perm l1 l2) takes two lists (l1 and l2) and
;; returns true if and only if l1 and l2 have
;; the same elements (and the same number of each)
;; Essentially, is l2 a reordering of l1.
(defunc perm (l1 l2)
  :input-contract (and (listp l1)(listp l2))
  :output-contract (booleanp (perm l1 l2))
  (if (equal l1 l2)
    t
    (if (endp l1)
      nil
      (and (in (first l1) l2)
           (perm (rest l1) (del (first l1) l2))))))

;; Assume by "Def of lor" that each element is a rational
;; and a lor is (cons rational lor) | nil
;; A similar claim can be made about a lon
(defdata lor (listof rational))
(defdata lon (listof nat))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; min-l: LOR (non empty) -> Rational
;; Here I will define min-l because different implementations lead 
;; to different proofs in the following conjecture.  Min-l takes a 
;; lorp and determines the smallest number in the list.
;; NOTICE: I made this more efficient using let but you can redefine the 
;; function if you want to prove (sortedp (ssort l)) for yourself. 
;; To do this you should prove the following conjecture (if you want 
;; more practice):
;; (implies (and (lorp l) (in e l)) (<= (min-l l) e))
;; For proofs, you can pretend all instances of minrest are 
;; actually (min-l (rest l))
(defunc min-l (l)
  :input-contract (and (lorp l)(consp l))
  :output-contract (rationalp (min-l l))
  (if (endp (rest l))                  
    (first l)
    (let ((minrest (min-l (rest l))))
      (if (>= minrest (first l)) 
        (first l)
        minrest))))

(check= (min-l '(1)) 1)
(check= (min-l '(1 5/2 17/2 13 -47)) -47)
(check= (min-l '(-48 5/2 17/2 13 -47)) -48)
(test? (implies (and (lorp l)(consp l))
                (in (min-l l) l)))

;; Let's do some warm-up proofs....which may be useful later.

(test? (implies (and (listp l1)(listp l2))
                (equal (in e (app l1 l2))
                       (or (in e l1)(in e l2)))))
#|

2) 
Prove phi_in_app: (implies (and (listp l1)(listp l2))
                           (equal (in e (app l1 l2))
                                  (or (in e l1)(in e l2))))
I.S. for in

1. Trivial
~((listp  l1)/\(listp l2)) => phi_in_app
C1. ~((listp  l1)/\(listp l2))
C2. (listp l1)
C3. (listp l2)
={C1, C2, C3, PL}
t 

2. Base 
(listp l1)/\(listp l2)/\(endp l1) => phi_in_app
C1. (listp l1)
C2. (listp l2)
C3. (endp l1)
-------------
C4. (app l1 l2) = l2 {C1,C2,C3,def.app}
C5. (in e l1) = nil {C1,C3,def. in}
(in e (app l1 l2)) = (or (in e l1)(in e l2))
= {C4,C5,PL}
(in e l2) = (in e l2)
= {PL}
t

3. Base
(listp l1)/\(listp l2)/\~(endp l1)/\(equal e (first l1)) => phi_in_app
C1. (listp l1)
C2. (listp l2)
C3. ~(endp l1)
C4. (equal e (first l1))
--------------
C5. (app l1 l2) = (cons (first l1)(app (rest l1) l2)) {C1,C2,C3,def.app}

(in e (app l1 l2)) = (or (in e l1)(in e l2))
= {C5,first-rest ax}
(in e (cons (first l1)(app (rest l1) l2))) = (or (in e (cons (first l1)(rest l1)))(in e l2))
= {first-rest ax, def. in}
t = (or t (in e l2))
= {PL}
t

4. Recursive
(listp l1)/\(listp l2)/\~(endp l1)/\~(equal e (first l1))/\phi_in_app|((l1 (rest l1))) => phi_in_app
C1. (listp l1)
C2. (listp l2)
C3. ~(endp l1)
C4. ~(equal e (first l1))
C5. (in e (app (rest l1) l2)) = (or (in e (rest l1))(in e l2))
--------------
C6. (app l1 l2) = (cons (first l1)(app (rest l1) l2)) {C1,C2,C3,def.app}

(in e (app l1 l2)) = (or (in e l1)(in e l2))
= {C5,first-rest ax}
(in e (cons (first l1)(app (rest l1) l2))) = (or (in e (cons (first l1)(rest l1)))(in e l2))
= {C4, def. in, first-rest ax}
(in e (app (rest l1) l2)) = (or (in e (rest l1))(in e l2))
= {C5}
t

QED


|#

(test? (implies (listp l)(equal (in e l)(in e (rev l)))))
#|
3) 
Prove phi_in_rev: (implies (listp l)
                           (equal (in e l)(in e (rev l))))
                           
(listp l) => (in e l) = (in e (rev l))

Use IS for in
1. Trivial case, ~IC
2. IC /\ (endp l)
3. IC /\ (not (endp l)) /\ (equal (first l) e)
4. IC /\ (not (endp l)) /\ (not (equal (first l) e) /\ (phi_in_rev|((l (rest l))

1.
C1. (not (listp l))
C2. (listp l)
---------
C3. nil {C1, C2, PL}

2. (listp l) /\ (endp l) => phi_in_rev
C1. (listp l)
C2. (endp l)
--------
(in e l) = (in e (rev l))
= {def in|((X l)), C2, if-axioms}
nil = (in e (rev l))
= {def rev|((a l)), C2, if-axioms}
nil = (in e nil)
= {def in|((X nil))}
nil = nil
= {PL}
t
QED

3. (listp l) /\ (not (endp l)) /\ (equal e (first l)) => phi_in_rev
C1. (listp l)
C2. (not (endp l))
C3. (equal e (first l))
---------
(in e l) = (in e (rev l))
= {def in|((X l) (a e)), def rev|((a l)), if-axioms x2, C2, C3}
t = (in e (app (rev (rest l)) (list (first l))))
= {assoc of app}
t = (in e (app (list (first l)) (rev (rest l))))
= {def app|((a (list (first l)) (b (rev (rest l)))), if-axioms, C2}
t = (in e (cons (list (first l) (app (rest (list (first l))) (rev (rest l)))))
= {first-rest axioms, def app|((a (rest (list (first l)))))}
t = (in e (cons (list (first l)) (rev (rest l))))
= {def in|((X (cons (list (first l)) (rev (rest l))))), C3, if-axioms, first-rest axioms}
t = t
QED

4. (listp l) /\ (not (endp l)) /\ (not (equal e (first l))) /\ phi_in_rev|((l (rest l)))
C1. (listp l)
C2. (not (endp l))
C3. (not (equal e (first l)))
C4. (listp (rest l) => (equal (in e (rest l)) (in e (rev (rest l))))
----------
C5. (listp (rest l)) {C1, C2, def listp}
C6. (in e (rest l)) = (in e (rev (rest l))) {C4, C5, MP}

(in e l) = (in e (rev l))
= {def in|((X l) (a e)), c2, c3, if-axioms x2; def rev|((a l)), c2}
(in e (rest l)) = (in e (app (rev (rest l)) (list (first l))))
= {assoc of app}
(in e (rest l)) = (in e (app (list (first l)) (rev (rest l))))
= {def in|((a e) (X (app (list (first l)) (rev (rest l))))), C2, C3, if-axioms x2}
(in e (rest l)) = (in e (rest (app (list (first l)) (rev (rest l)))))
= {first-rest axioms}
(in e (rest l)) = (in e (rev (rest l)))
= {c6}
t
QED


|#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; GIVEN
;; sortedp: lor -> boolean
;; (sortedp l) takes a list of rationals
;; and returns true if and only if the elements 
;; are in non-decreasing order (ie they are sorted)
(defunc sortedp (l)
  :input-contract (lorp l)
  :output-contract (booleanp (sortedp l))
  (if (or (endp l)(endp (rest l)))
    t
    (and (<= (first l) (second l)) (sortedp (rest l)))))

(check= (sortedp '(-1 -1/2 0 4 9/2)) t)
(check= (sortedp '(-1 -1/2 0 4 7/2)) nil)
(check= (sortedp nil) t)

;; Remember to add tests to all functions you define.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; DEFINE:
;; filter-less: rational x lor -> lor
;; filter-less r l) takes a rational number r to filter-by
;; plus a list of rationals l and returns all elements of
;; l that are strictly less than r.
(defunc filter-less (r l)
  :input-contract (and (rationalp r) (lorp l))
  :output-contract (lorp (filter-less r l))
  (cond ((endp l) nil)
        ((< (first l) r) (app (list (first l)) (filter-less r (rest l))))
        (t (filter-less r (rest l)))))
  
(check= (filter-less 4 '(1 2 4 7 3 19 -19 8)) '(1 2 3 -19))
(check= (filter-less 4 nil) nil)

(check= (filter-less 10 '(1 2 3)) '(1 2 3))
(check= (filter-less 4 '(4)) nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; DEFINE:
;; filter-gte: rational x lor -> lor
;; filter-gte r l) takes a rational number r to filter-by
;; plus a list of rationals l and returns all elements of
;; l that are Greater Than or Equal (GTE) to r.
(defunc filter-gte (r l)
  :input-contract (and (rationalp r) (lorp l))
  :output-contract (lorp (filter-gte r l))
  (cond ((endp l) nil)
        ((>= (first l) r) (app (list (first l)) (filter-gte r (rest l))))
        (t (filter-gte r (rest l)))))

(check= (filter-gte 4 '(1 2 4 7 3 19 -19 8)) '(4 7 19 8))
(check= (filter-gte 4 nil) nil)

(check= (filter-gte 10 '(11 12 13)) '(11 12 13))
(check= (filter-gte 10 '(10)) '(10))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; GIVEN
;; qsort: lor -> lor
;; (qsort l) takes a list of rationals l and sorts the
;; list using the Quicksort algorithm. This involves
;; removing the first element of l (the pivot) and assigning elements
;; in (rest l) to a less-than group or a GTE group. Quicksort
;; is called on each of these new lists.  Finally, the new lists
;; are appended together with the pivot value in the middle.
(defunc qsort (l)
  :input-contract (lorp l)
  :output-contract (lorp (qsort l))
  (if (or (endp l)(endp (rest l)))
    l
    (app (qsort (filter-less (first l)(rest l)))
         (cons (first l)(qsort (filter-gte (first l)(rest l)))))))

;; To think about: what would be a measure function for qsort and what 
;; are the proof obligations? How big are the lists returned from 
;; filter-gte and filter-less?
;;.......These are rhetorical questions. You do not have to provide an answer.

(test? (implies (and (lorp l1)(lorp l2)
                     (sortedp l1)(sortedp l2)
                     (consp l1)(consp l2)
                     (< (first (rev l1))(first l2)))
                (sortedp (app l1 l2))))

#|
4) Prove phi_app_sort: 
(lorp l1) /\ (lorp l2) /\ (sortedp l1) /\ (sortedp l2) /\ (consp l1)
  /\ (consp l2) /\ (< (first (rev l1)) (first l2)) => (sortedp (app l1 l2))

To do induction, you need to ensure l1 is not empty. Are there 
any functions that stop before (endp l1)? 

You may also need a lemma showing the last of a list STAYS 
the last of the list for (rest l) 

Re-written sortedp
(defunc sortedp (l)
  :input-contract (lorp l)
  :output-contract (booleanp (sortedp l))
  (cond ((endp l) t)
        ((endp (rest l)) t)
        ((<= (first l) (second l)) (sortedp (rest l)))))
        
I.S. for sortedp
1. Trivial
~(lorp l1) => phi_app_sort
C1. ~(lorp l1)
C2. (lorp l1)
= {C1,C2}
nil

2. Base (Trivial 2)
(lorp l1)/\(endp l1) => phi_app_sort
C1. (lorp l1)
C2. (endp l1)
(lorp l1) /\ (lorp l2) /\ (sortedp l1) /\ (sortedp l2) /\ (consp l1)
  /\ (consp l2) /\ (< (first (rev l1)) (first l2)) => (sortedp (app l1 l2))
= {C2,PL}
nil => (sortedp (app l1 l2))
= {PL}
t
 
 3. Base
(lorp l1)/\~(endp l1)/\(endp (rest l1)) => phi_app_sort

|#

(defthm L1 (implies (and (lorp l)(not (endp l)))
                    (equal (second (cons 'a l))(first l))))
#|
C1. (lorp l1)
C2. ~(endp l1)
C3. (endp (rest l1))
C4. (lorp l2)
C5. (sortedp l1)
C6. (sortedp l2)
C7. (consp l1)
C8. (consp l2)
C9. (< (first (rev l1)) (first l2))
-----------------------------------
C10. (rev l1) = l1 {C1,C3,def. rev(twice), def. app, if ax}
C11. (< (first l1)(first l2)) {C9,C10}
C12. (<= (first l1)(first l2)) {C11,PL}

(sortedp (app l1 l2))
= {C1,C3,C4, def. app (twice), if ax}
(sortedp (cons (first l1) l2))
= {def. sortedp|((l (cons (first l1) l2))),C7,C8,if ax}
(and (<= (first (cons (first l1) l2))(second (cons (first l1) l2))) (sortedp (rest (cons (first l1) l2))))
= {first-rest ax,C1,C2,L1}
(and (<= (first l1)(first l2)) (sortedp l2))
= {C12,C6,PL}
t

4. Recursive
(lorp l1)/\~(endp l1)/\~(endp (rest l1))/\(<= (first l1)(second l1))/\phi_app_sort|((l1 (rest l1))) => phi_app_sort
|#

(defthm L2 (implies (and (lorp l)(not (endp l))(not (endp (rest l))))
                    (equal (first (rev (rest l))) (first (rev l)))))

#|
C1. (lorp l1)
C2. ~(endp l1)
C3. ~(endp (rest l1))
C4. (<= (first l1)(second l1))
C5. (lorp (rest l1)) /\ (lorp l2) /\ (sortedp (rest l1)) /\ (sortedp l2) /\ (consp (rest l1))
  /\ (consp l2) /\ (< (first (rev (rest l1))) (first l2)) => (sortedp (app (rest l1) l2))
C6. (lorp l2)
C7. (sortedp l1)
C8. (sortedp l2)
C9. (consp l1)
C10. (consp l2)
C11. (< (first (rev l1)) (first l2))
-----------------------------------
C12. (lorp (rest l1)) {C1,C9}
C13. (sortedp (rest l1)) {C7,def.sortedp,C2,C3,C4,if-ax}
C14. (< (first (rev (rest l1))) (first l2)) {C1,C2,C3,L2,C11}
C15. (sortedp (app (rest l1) l2)) {C12,C6,C13,C8,C9,C3,def.cons,C10,C14,MP}

(sortedp (app l1 l2))
= {C1,C6,def. app}
(sortedp (cons (first l1) (app (rest l1) l2)))
= {C2,C3,C9,C4,def. sortedp|((l (cons (first l1) (app (rest l1) l2)))), if ax, first-rest ax}
(sortedp (app (rest l1) l2))
= {C15}
t

QED

|#

;; GIVEN: No need to prove this.
(defthm phi_in_gte (implies (and (rationalp e)(rationalp r)(lorp l)(in e (filter-gte r l)))
                            (>= e r)))
(test? (implies (and (rationalp e)(rationalp r)(lorp l)(in e (filter-less r l)))
                (< e r)))

#|
5) Prove phi_in_less: 
(rationalp e)/\(rationalp r)/\(lorp l)/\(in e (filter-less r l)) => (< e r)
                             
You may assume that if (in e (filter-less r l)) is true and e = (first l)
then you MUST take the (cons (first l)(filter-less r (rest l))) branch
of filter-less.

(defunc filter-less (r l)
  :input-contract (and (rationalp r) (lorp l))
  :output-contract (lorp (filter-less r l))
  (cond ((endp l) nil)
        ((< (first l) r) (app (list (first l)) (filter-less r (rest l))))
        (t (filter-less r (rest l)))))

I.S. for filter-less
Case 1: (endp l)
Case 2: (not (endp l)) /\ (< (first l) r) /\ phi_in_less|((l (rest l)))
Case 3: (not (endp l)) /\ (not (< (first l) r)) /\ phi_in_less|((l (rest l)))

Case 1
C1. (rationalp e)
C2. (rationalp r)
C3. (lorp l)
C4. (in e (filter-less r l))
C5. (endp l)
--------------

(< e r)
= {def filter-less, C5}
nil
QED

Case 2
C1. (not (endp l))
C2. (rationalp e)
C3. (rationalp r)
C4. (lorp l)
C5. (in e (filter-less r l))
C6. (< (first l) r)
C7. (rationalp e)/\(rationalp r)/\(lorp (rest l))/\(in e (filter-less r (rest l))) => (< e r)
-----------------
C8. (lorp (rest l)) {C1,C4,first-rest ax}
C9. (in e (app (list(first l))(filter-less r (rest l)))) {def. filter-less, assumption listed above, C5,C6}
C10. (in e (filter-less r (rest l)))  {C9,def. in, first-rest ax}
C11. (< e r) {C2,C3,C8,C10,C7,MP}
(< e r)
={C11}
t

Case 3
C1. (not (endp l))
C2. (rationalp e)
C3. (rationalp r)
C4. (lorp l)
C5. (in e (filter-less r l))
C6. ~(< (first l) r)
C7. (rationalp e)/\(rationalp r)/\(lorp (rest l))/\(in e (filter-less r (rest l))) => (< e r)
-----------------
C8. (lorp (rest l)) {C1,C4,first-rest ax}
C9. (in e (filter-less r (rest l))) {def. filter-less,C1,C6}
C10. (< e r)
(< e r)
= {C10}
t

|#

(test? (implies (lorp l)(equal (in e (qsort l))(in e l))))
#|
**Presume the following is a theorem.**
(defthm phi_perm_qsort (implies (lorp l)(equal (in e l)(in e (qsort l)))))
|#

(test? (implies (lorp l) (sortedp (qsort l))))

#|
6)
Prove: phi_qsort: (implies (lorp l) (sortedp (qsort l)))

Show that you are smarter than ACL2s: Prove that qsort produces a 
sorted list.ACL2s can't prove this without help (and proving the 
assumed theorem phi_perm_qsort is much more difficult than it looks) 
maybe you can.
Notice that the test? above, however, should pass.

Think about what a good induction scheme to use would be.
Remember, that EACH recursive call provides an inductive
assumption where variables are substituted to their value
at the next recursive call (so variable changes can be more
complex than just (- n 1) or (rest l)).
HINT: You may also want to do a proof-by-cases
within one of the induction scheme cases if you don't know whether
a list is empty or not.
................

|#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; PART III: Comparing Sorting Algorithms
;; Now let's do something familiar.  Let's define another
;; sorting algorithm (ssort or selection sort) and then
;; let's race the two algorithms to see which one is faster.
;; ACL2s does not necessarily scale well with large lists
;; or access list elements as efficiently as one can access
;; an array.  Thus I didn't expect massive savings like we see
;; with an imperative language but let's see the difference just
;; the same......
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Let's make your life easier.
:program
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; DEFINE
;; ssort: lor -> lor
;; (ssort l) or selection sort takes a lorp l as input,
;; and returns a permutation of l with elements in non-decreasing order.
;; ALGORITHM: if l is empty, return nil. If not,
;; find the smallest element in l and add to the sorted list.  
;; Keep SELECTING and removing the smallest element from the 
;; input list and cons it onto the sorted list (the output list 
;; from the recursive call).  Stop recursively calling ssort 
;; when l is empty. 
(defunc ssort (l)
  :input-contract (lorp l)
  :output-contract (lorp (ssort l))
  (if (endp l)
    nil
    (cons (min-l l) (ssort (del (min-l l) l)))))
  
(check= (ssort '(1 5/2 3 8 -8 2/3)) '(-8 2/3 1 5/2 3 8))

(check= (qsort '(1 5/2 3 8 -8 2/3)) '(-8 2/3 1 5/2 3 8))

;; Add more tests to ensure qsort and ssort both sort
(check= (ssort nil) nil)
(check= (qsort nil) nil)
(check= (ssort '(0)) '(0))
(check= (qsort '(0)) '(0))
(check= (ssort '(1 2 5 4 3)) '(1 2 3 4 5))
(check= (qsort '(1 2 5 4 3)) '(1 2 3 4 5))
(check= (ssort '(-1 -2 -5 -4 -3)) '(-5 -4 -3 -2 -1))
(check= (qsort '(-1 -2 -5 -4 -3)) '(-5 -4 -3 -2 -1))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; GIVEN
;; gen-lor-t: nat x integer x pos x lorp
;; (gen-lor n i denom acc) takes a list size 
;; n, an increment value i and a divisor value denom and
;; an accumulator list of rationals acc and
;; returns a "random" list of n rationals.
;; gen-lor-t can be used to test your sorting algorithm
;; speed for non-trivial lengths
(defunc gen-lor-t (n i max denom acc)
  :input-contract (and (natp n)(integerp i)(posp max)(lorp acc)
                       (posp denom))
  :output-contract (lorp (gen-lor-t n i max denom acc))
  (cond ((equal n 0) (cons i acc))
        ((> i max) (gen-lor-t (- n 1) (unary-- i) max denom
                              (cons (/ (+ n i) denom) acc)))
        (t         (gen-lor-t (- n 1) (unary-- (+ i n)) max denom
                              (cons (/ (+ n i) denom) acc)))))
    
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; GIVEN
;; gen-lor*: nat -> lor
;; (gen-lor* n) generates a list of rationals length
;; n with "semi-random" values inside.
;; This is a wrapper function for gen-lor-t to extract
;; away complexity for generating a list. Modify
;; the numbers all you want.
(defunc gen-lor* (n)
  :input-contract (natp n)
  :output-contract (lorp (gen-lor* n))
  (gen-lor-t n -4 17 3 nil))
  
(check= (qsort (gen-lor* 40))(ssort (gen-lor* 40)))
(check= (qsort (gen-lor* 10))(ssort (gen-lor* 10)))
(check= (qsort (gen-lor* 400))(ssort (gen-lor* 400)))

;; Now let's see the speed differences:
(defconst *med-list* (gen-lor* 2000))
(defconst *large-list* (gen-lor* 20000))

(acl2::er-progn
   (acl2::time$ (acl2::value-triple (qsort *med-list*)))
   (acl2::value-triple nil))
;; How long does this take (in seconds)? The value is output in the REPL.
; 0.28 seconds realtime, 0.28 seconds runtime

(acl2::er-progn
   (acl2::time$ (acl2::value-triple (ssort *med-list*)))
   (acl2::value-triple nil))
;; How long does this take (in seconds)? The value is output in the REPL.
; 0.22 seconds realtime, 0.22 seconds runtime

(acl2::er-progn
   (acl2::time$ (acl2::value-triple (qsort *large-list*)))
   (acl2::value-triple nil))
;; How long does this take (in seconds)? The value is output in the REPL.
; 26.59 seconds realtime, 26.09 seconds runtime

(acl2::er-progn
   (acl2::time$ (acl2::value-triple (ssort *large-list*)))
   (acl2::value-triple nil))

;; How long does this take (in seconds)? The value is output in the REPL.
; 44.22 seconds realtime, 43.73 seconds runtime

;; Generate a list of rationals that ensures that ssort is as fast or 
;; faster than qsort for any list size (you can write your own function)
;; For testing purposes make (len *slow-list*) = 16000
;; Hint: What is the worst possible input for our implementation of qsort
;; where the pivot element is the first element in the list?
; LOL one where the list is already sorted I see what you did there

(defconst *slow-list* (ssort (gen-lor* 16000)))

(acl2::er-progn
   (acl2::time$ (acl2::value-triple (ssort *slow-list*)))
   (acl2::value-triple nil))
;; How long does this take?
; 12.16 seconds realtime, 12.16 seconds runtime

(acl2::er-progn
   (acl2::time$ (acl2::value-triple (qsort *slow-list*)))
   (acl2::value-triple nil))#|ACL2s-ToDo-Line|#

;; How long does this take?
; This caused ACL2s to hang for about 10 minutes before giving 'ACL2 died unexpectedly'
; so I would say > 10 minutes. (I did reboot the session and try again)

#|
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
Part V: Feedback (5 points)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
#|

Each week we will ask a couple questions to monitor how the course
is progressing.  This should be the same length as the HW07 survey. 

Please fill out the following form.

https://goo.gl/forms/tGE0FMdiPLoV57j13

As before, feedback is anonymous and each team member should fill out
the form (only once per person).

After you fill out the form, write your name below in this file, not
on the questionnaire. We have no way of checking if you submitted the
file, but by writing your name below you are claiming that you did,
and we'll take your word for it.  

5 points will be awarded to each team member for filling out the 
questionnaire.

The following team members filled out the feedback survey provided by 
the link above:
---------------------------------------------
Chris Kenyon
Izaak Branch

|#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
Part V: Extra credit (5 points)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
Get ACL2s to prove all of the theorems you were asked to prove by
hand for qsort, including any lemmas you needed to discover. Here is how you
do that.  

Suppose that the theorem you want to prove is 

(listp x) => (app x nil) = x

First, turn it into a legal ACL2s expression and second use
the "defthm" form, which requires giving the theorem a name. Here
is what the defthm will look like:

(defthm app-x-nil-thm
  (implies (listp x)
           (equal (app x nil)
                  x)))

One thing to keep in mind is that if you have a defthm of 
the form 

(1) hyp1 /\ hyp2 /\ ... /\ hypn => (f ...) = (g ...)

then you could write it as

(2) hyp1 /\ hyp2 /\ ... /\ hypn => (g ...) = (f ...)

Logically there is no difference, but in ACL2s there is a big
difference. Put the more "complicated" of (g ...) and (f ...) on
the left of the equality because ACL2s uses the defthms as what
are called rewrite rules, i.e., if you defthm is of form (1) then
ACL2s replaces (f ...) by (g ...) but not the other way around.

Finally place the defthms in the same order as you were asked to
prove them and lemmas that were used in the proof of a theorem
should come before the theorem.

Unlike in previous terms, this may not be easy. There may be some
trial and error necessary to find additional theorems that can help
you in your proofs.  Hence the bonus.  Do this problem for fun or
personal interest.  I wouldn't do this for the points.

** YOU CAN STILL GET 100% ON THIS ASSIGNMENT WITHOUT DOING THIS BONUS
QUESTION.  I WOULD JUST LIKE TO GIVE PEOPLE THE OPPORTUNITY TO GO
BEYOND THE BASIC ASSIGNMENT REQUIREMENTS.**

|#