# The COMPLETE Pawn programming language semantics in Agda
The Pawn programming language is the 4th semester project at Aalborg University I'm developing alongside Tobias, Lasse, and Jonas.

This project is **complete**, meaning the entire PAWN semantic is described in Agda.

We've developed some of the semantics in "normal" mathematical notation on paper, but I am not satisfied with the vagueness of this style of making the semantic due to how frequent mistakes are. I am therefore in my free time developing this agda-replica of it.

The Agda version of the semantic is really similar to the standard one.

The official non-Agda semantics of the Pawn programming language is not public, nor under any license.

## Mistakes in the official non-agda semantic:
1. The abstract syntax only allows function calls with a minimum of one positional argument.
2. MEMBER-1 doesn't change sigma and location in the result of the transition.
3. ASSIGN-4 has result transition of it's Member transition return phi which is impossible.
4. STACKFRAME-3 evaluates a statement but doesn't have any reason to.
5. Phi is called as the lookup function in \[VAR\] instead of ψ
6. CALL-USER-8 wrongly adds values to a environment instead of locations.
7. The abstract syntax is missing a rule to handle Member in expressions. This would handle indexing, variable lookup, etc, which are impossible in the semantic's current (non-Agda) state.
8. Missing rules for "&" and "|". Should be moved to simpleOp or have rules assigned.

All these mistakes have been fixed in the Agda version, except for misatke 8.

### Minor
8. Store instead of Sto in 2 places.
9. Function calls in statements have to not return anything. It's because there's a missing EXPR-STMT rule for escaping a scope that uses `return v` to escape.
10. INDEX-4 used `a` instead of `L` in a list-expansion
11. `𝒮ₚ`  should be replaced with `𝒮ₛ` to standardize stackframe stack variable.
12. in APPLY-2 it barely makes sense to do a `∀Li ∈ {L_1, ... , L_n}`, since there's an index in the variable. `∀i ∈ {1, · · · , n}` is better.
13. CALL-USER-5 (and some other call rules) don't allow expressions to modify the function that's being called. Modifying it isn't possible with any syntax, but impl defined funcs could.
14. The implementation defined Call function shouldn't be allowed to modify *all* state. Ideally it would be given a function to allocate space that it could itself use, and it'd be able to modify any locations it'd be the maker of.

All minor mistakes have been fixed in the Agda version.
