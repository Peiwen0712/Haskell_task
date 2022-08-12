# Haskell_task
CM50262 Functional programming

Assignment 1:
In your file you are given the implementation of the λ -calculus from the tutorials. We will first extend this to the simply-typed calculus.

a) Complete the datatype Type to represent simple types following the grammar above. For the base type, use the constuctor Base , and for the arrow type, use the (infix) constructor :-> . Un-comment the function nice , the Show instance, and the ex- amples type1 and type2 to see if everything type-checks.
b) Make the datatype Type a member of the type class Eq so that (==) gives equality of types.
c) Adapt the datatype Term for λ -terms from the tutorials to simply-typed terms, follow- ing the grammar above. Un-comment the function pretty and the Show instance to see if everything type-checks.
d) Un-comment the function numeral from the tutorials and adapt it to work with simply- typed terms, following the definition here:
Nn = λfo→o.λxo.Ln L0 = x Ln+1 = f Ln
Un-comment also the other functions and examples for numerals, from sucterm to
example7 .
e) Un-comment the functions used , rename , substitute , and beta from the tu-
torials and adapt them to work with simply-typed terms.
f) Un-comment normalize and prepare it to display a number before each term. We will adapt this to display the upper bound to reductions later, but any number will do for now.
*Main> type2
(o -> o) -> o -> o
*Main> type2 == type1 :-> type1
True
*Main> type2 == type1
False
*Main> numeral 4
\f: o -> o . \x: o . f (f (f (f x)))
*Main> example1
(\m: (o -> o) -> o -> o . \f: o -> o . \x: o . m f (f x))
                                        (\f: o -> o . \x: o . x)
*Main> normalize it
  0 -- (\m: (o -> o) -> o -> o . \f: o -> o . \x: o . m f (f x))
                                        (\f: o -> o . \x: o . x)
  0 -- \a: o -> o . \b: o . (\f: o -> o . \x: o . x) a (a b)
  0 -- \a: o -> o . \b: o . (\b: o . b) (a b)
  0 -- \a: o -> o . \b: o . a b
  
  Type checking
The types we have added so far are only an annotation, but really we want those terms that are well-typed: where the types of functions and arguments match in the expected way. To check if a given term is well-typed is a simple inductive algorithm that we will implement here. (Note that this is different from type inference, which is the more involved algorithm that decides whether an untyped term can be given a type.) The definitions are as follows.
A context Γ is a finite function from variables to types, written as a comma-separated list. Γ ::= x1 : τ1,...,xn : τn
Aterm M hastype τ inacontext Γ,written Γ⊢M :τ,ifthatstatementcanbederived using the following type checking rules.
Γ, x : σ ⊢ M : τ Γ ⊢ M : σ → τ Γ ⊢ M : σ Γ,x:τ ⊢x:τ Γ⊢λxσ.M :σ→τ Γ⊢MN :τ
The type checking rules then give an inductive algorithm. To find a type for M , the inputs are Γ and M , and the algorithm either outputs a type τ if M is well-typed, or fails if M is not well-typed. The conclusion of a rule is what is computed, and premises of a rule (the parts above the line) give the recursive calls.
Assignment 2: (20 marks)
a) Complete the type Context as a list of pairs of variables and types, replacing the () with the correct definition.
b) Implement the type-checking algorithm described above as the function typeof . If the term is well-typed, return its Type ; if it is not, you may throw an exception (any will do; it doesn’t need to match the examples). Un-comment example8 for testing.
 *Main> typeof [] (numeral 3)
 (o -> o) -> o -> o
 *Main> typeof [] example7
 (o -> o) -> o -> o
 *Main> example8
 \x: o . f x x
 *Main> typeof [("f",Base :-> (Base :-> Base))] example8
 o -> o
 *Main> typeof [] example8
 o -> *** Exception: Variable f not found
 *Main> typeof [("f",Base)] example8
 o -> *** Exception: Expecting ARROW type, but given BASE type
 *Main> typeof [("f",(Base :-> Base) :-> Base)] example8
 o -> *** Exception: Expecting type o -> o, but given type o
 
 Higher-order numeric functions
Now, we will start on the constructions we need for counting reduction steps. This docu- ment will explain the ideas behind them, but note that it is not necessary to fully understand everything: you can build each function by following the specification closely.
We want to build a function from simply-typed terms to natural numbers, such that when a term reduces, the number gets smaller. It then follows that all reduction paths must eventu- ally end, and that the term is strongly normalizing.
The problematic case is an application: suppose that for a term M N we know that M reduces in at most m steps, and N reduces in at most n steps. But that does not help us to give the number of steps for M N . For example, if M and N are normal (at most zero reduction steps), then M N might not be normal. The solution is to give for M not just a number, but a function that, given a bound for N , produces a bound for M N .
The types will make sure that everything works out. We will build a function that interprets terms as functionals, higher-order functions over numbers, as follows:
A term ...
M:o
M:o→o M:o→o→o M :(o→o)→o etc.
becomes a ...
number n ∈ N
functionf :N→N functionf :N→N→N functionf :(N→N)→N etc.
 This gives us a higher-order function over numbers, but not yet a number. To get that, we evaluate the functional with dummy arguments: zero for N, the function g(x) = 0 for N → N , etc:
A term ...
M:o
M:o→o M:o→o→o M :(o→o)→o etc.
becomesa... numbern∈N
functionf :N→N functionf :N→N→N functionf :(N→N)→N etc.
and gives a number . . .
n
f0
f00 fgwhereg(x)=0 etc.
 We will now start making these ideas precise, using the following definitions.
• The sets of functionals we need are given by the following grammar. F ::= N | F → F
Coursework CM20256/CM50262 Functional Programming
 The function |τ| takes every type τ to a set of functionals, defined by: |o| = N
|σ→τ| = |σ|→|τ|
Note that since a type is of the form τ = τ1 → . . . → τn → o , a set of functionals
that type is of the following form.
|τ1|→···→|τn|→|o|=F1 →···→Fn →N
• For every type τ , the dummy element ⊥τ ∈ |τ| is defined by:
⊥o =0∈N
⊥σ→τ = f∈|σ→τ| wheref(x)=⊥τ
That is, the functional f above takes one argument x ∈ |σ|, throws it away, and returns ⊥τ . Informally, if τ = τ1 → ... → τn → o then the dummy element
⊥τ ∈ |τ1|→···→|τn|→N takes n arguments, discards them all, and returns zero.
• For a functional f ∈ |τ|, the counting operation ⌊f⌋τ ∈ N returns a number by providing the necessary dummy arguments, defined by:
⌊n⌋o =n∈N ⌊f⌋σ→τ = ⌊f(⊥σ)⌋τ
Informally, if τ = τ1 → ... → τn → o then for f ∈ |τ| the counting operation gives the following (verify for yourself that this is indeed a number).
⌊f⌋τ = f (⊥τ1)...(⊥τn)
• The increment function f +τ n increments a functional f ∈ |τ| by a number n,
defined by:
m +o n = m + n
f+σ→τ n = g whereg(x)=f(x)+τ n Informally, for τ = τ1 → ... → τn → o and any functional in the set
|τ1| → · · · → |τn| → N the increment function +τ adds a number “to the last N ”.

Assignment 3: (30 marks)
We will now implement these definitions. You are given a data type Functional , with a constructor Num for N and a constructor Fun for F → F . The data type comes with a Show instance, but since we cannot show functions, it will only properly display a functional if it is a number. Further, to apply a functional F → F as a function, the constructor Fun gets in the way. The function fun is included for this purpose: it takes Fun f and extracts f , which is a function of type Functional -> Functional .
a) Complete the following example functionals: plussix of type N → N , which adds six to a given input; plus of type N → N → N that implements addition; and twice of type (N → N) → N → N which takes a functional f and an input n and applies f to n twice.
b) Complete the function dummy that returns the dummy element ⊥τ for each type τ .
c) Implement ⌊f⌋τ as the function count, which takes as input the type τ and a functional f ∈ |τ|. (You do not need to check if f belongs to |τ|, and you may throw an error if it doesn’t.)
d) Implement +τ as the function increment . You do not need the type τ as an argument; instead, you may pattern-match on the input Functional .
 *Main> fun plussix (Num 3)
 Num 9
 *Main> fun (fun plus (Num 3)) (Num 4)
 Num 7
 *Main> fun (fun twice plussix) (Num 1)
 Num 13
 *Main> dummy Base
 Num 0
 *Main> dummy type1
 Fun ??
 *Main> fun (dummy type1) (Num 4)
 Num 0
 *Main> count type1 plussix
 6
 *Main> count type2 twice
 0
 *Main> count type1 (fun twice plussix)
 12
 *Main> increment (dummy Base) 5
 
 
 Num 5
 *Main> fun (increment plussix 3) (Num 1)
 Num 10
 *Main> fun (fun (increment twice 4) plussix) (Num 1)
 Num 17
 *Main> count type1 (fun (increment twice 4) plussix)
 16
Counting reduction steps
To give an upper bound to the number of reduction steps, we will define a function ∥M∥ that takes a term M : τ to a function f ∈ |τ|. This will be a straightforward induction on M . As with the type checking function, where we needed a context Γ to know the types of the free variables of M , here we need a valuation which assigns to each variable x : τ a functional f ∈ |τ|. We write v for a valuation, and v[x 􏰀→ f] for the valuation that maps x to f and any other variable y to v(y) .
The interpretation of M is then constructed as follows.
• If M isavariable x:τ,welookupthefunctionalin v,andreturn v(x)∈|τ|.
• For an abstraction λxσ.M : σ → τ , we construct a functional f ∈ |σ| → |τ| as follows: for any g ∈ |σ|, we define f(g) to be the interpretation of M : τ for the valuation v[x 􏰀→ g] . Intuitively, if we consider x in M to represent an arbitrary term, then g represents the bound on reduction steps for x , and f uses g to compute the bound for M .
• Foranapplication MN :τ where N :σ,iftheinterpretationof M is f ∈|σ|→ |τ| and that of N is g ∈ |σ|, then the basis of our bound for M N is f(g). This measures the steps in M , given that N is an argument. We then need to adjust this in two ways:
– Since M N could be a redex (or could become one after reduction or substitution in M),weincrement f(g) byone,to f(g)+τ 1.
– In the case that M discards N , for instance if M = λx.y , also f will discard g . But we still need to count reduction steps in N , which we do separately: we increment our answer with the number ⌊g⌋σ , which gives the bound for N , to f(g)+τ (1+⌊g⌋σ).
Notethatinthecase MN,weneedtoknowthetypeof N tocompute ⌊g⌋σ,andforthat we need a context Γ with the type of its free variables. The interpretation of M is then defined with a context Γ and a valuation v , as ∥ M ∥ Γv
and is defined inductively as follows.
∥ x ∥ Γv ∥λxτ.M∥Γv
= v ( x )
= f where f(g) = ∥M∥Γ, x:σ
v[x 􏰀→ g] = f(g)+τ (1+⌊g⌋σ) where f = ∥M∥Γv ,
∥MN∥Γv
Then the bound ∥M∥ of a closed term M : τ (one without free variables) is given by
g = ∥ N ∥ Γv ,
⌊f⌋τ , where f is the interpretation of M with the empty context and empty valuation.
Assignment 4: (30 marks) We will implement the interpretation and bound functions, and adapt normalize to show
the bound for each term, so we can see that it indeed goes down during reduction.
a) Complete the type Valuation as a mapping from variables to functionals, given as a list of pairs.
b) Complete the function interpret to give the interpretation ∥M∥Γv of a well-typed term M as a functional.
c) Complete the function bound that takes a closed, well-typed term M : τ , computes its interpretation f , and returns ⌊f⌋τ .
d) Adapt normalize to show the bound of the term at each step.
 *Main> bound example1
 5
 *Main> bound example2
 68
 *Main> bound example3
 24
 *Main> bound example4
 2060
 *Main> bound example5
 1880
 *Main> bound example6
 18557
 
 *Main> bound example7
 3867842
 *Main> normalize example1
   5 -- (\m: (o -> o) -> o -> o . \f: o -> o . \x: o . m f (f x))
                                         (\f: o -> o . \x: o . x)
   4 -- \a: o -> o . \b: o . (\f: o -> o . \x: o . x) a (a b)
   3 -- \a: o -> o . \b: o . (\b: o . b) (a b)
   1 -- \a: o -> o . \b: o . a b
That concludes our implementation. Note that a normal form does not need to have a bound of zero, since we are counting applications, not redexes. But that is fine: as long as the bound always goes down for a reduction step, terms will be strongly normalizing. You can use the example terms to convince yourself that this is the case, and you can change the evaluation strategy used by normalize to see that this works for any reduction step, or use randomIO to choose arbitrary redexes.
To make this construction into a strong normalization proof, we would have to prove that the bound always goes down. This is a nice challenge—contact me if you would like to try it.
