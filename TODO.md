
Convenience stuff :
* Introduce a more convenient syntax
* Add explicit import
* Pretty print the environment in a better way
* Log events during typechecking

Unification :
* Be more precise in the unification. In particular, be able to simplify during unification.
* Make sure eliminators in the environment are used correctly.

Extract :
* propagate elims : "let y = f x in a -> b" --> "(let y = f x in a, let y = f x in b)"

Typecheck :
* typecheck App in the same way than Proj and Case.
* when calling subs, construct the complete normal form of the substituant (n').

Substitution :
* Optim : when "subs n x n'" and there is no x in n, we can get rid of n'

Features :
* Add inference for sorts.

Examples :
* Encode X bits numbers.
* Encode datatypes.

Refactoring/Coding style :
* Replace some handmade functions by generic ones
