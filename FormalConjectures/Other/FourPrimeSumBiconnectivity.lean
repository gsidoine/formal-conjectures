/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import FormalConjecturesUtil

/-!
# Four prime sums without cut vertices

*Reference:* [The Scottish Book, "Four prime sums without cut vertices"]
(https://github.com/gsidoine/the-scottish-book/blob/main/problems/graph-theory/P034-four-prime-sum-biconnectivity.md).

For a finite set of primes S, the graph on {1, ..., n} joins two distinct
integers if their sum belongs to S.

The conjecture asks whether four prime sums suffice for 2-vertex-connectivity
at every odd order n >= 7. Four labels are necessary at odd orders: the
two endpoints 1 and n each require two distinct incident sum labels, and
the sets of possible prime labels at those endpoints are disjoint.

The related three-prime ordinary-connectivity theorem is recorded in
[The Scottish Book](https://github.com/gsidoine/the-scottish-book/blob/main/theorems/P033-universal-three-prime-sum-connectivity.md).
-/

@[expose] public section

namespace FourPrimeSumBiconnectivity

/-- The graph on 1, ..., n formed by choosing the permitted edge sums S. -/
def sumGraph (n : ℕ) (S : Finset ℕ) : SimpleGraph (Fin n) where
  Adj x y := x ≠ y ∧ x.val + y.val + 2 ∈ S
  symm := by
    intro x y h
    exact ⟨h.1.symm, by simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h.2⟩
  loopless := by
    intro x h
    exact h.1 rfl

/-- Every pair of vertices is connected, even after deleting any one vertex. -/
def IsTwoVertexConnected {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  (∀ x y : Fin n, G.Reachable x y) ∧
    ∀ v : Fin n, ∀ x y : {u : Fin n // u ≠ v},
      (G.induce {u : Fin n | u ≠ v}).Reachable x y

/--
For every odd n >= 7 there is a set of four primes whose sum-edge graph
is 2-vertex-connected.
-/
@[category research open, AMS 5 11]
theorem four_prime_sums_biconnected
    (n : ℕ) (hn : 7 ≤ n) (hodd : Odd n) :
    ∃ S : Finset ℕ,
      S.card = 4 ∧
      (∀ p ∈ S, Nat.Prime p) ∧
      IsTwoVertexConnected (sumGraph n S) := by
  sorry

end FourPrimeSumBiconnectivity
