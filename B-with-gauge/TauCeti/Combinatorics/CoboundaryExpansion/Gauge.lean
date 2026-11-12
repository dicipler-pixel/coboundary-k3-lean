/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.CoboundaryExpansion.Cochain

/-!
# Cochains: coboundaries and the gauge action

* `Cochain.IsCoboundary`: some gauge trivializes every edge;
* `Cochain.gauge β α` and the notation `β • α`: the gauge action
  `(β • α) u v = (β u)⁻¹ * α u v * β v` on edges;
* `Cochain.one_smul`: the identity gauge acts trivially;
* `Cochain.smul_smul`: `β • (γ • α) = (γ * β) • α` with the pointwise product of gauges.
-/

public section

open Finset

namespace TauCeti.CoboundaryExpansion

variable {V : Type*} [LinearOrder V] {G : Type*} [Group G] {X : TwoComplex V}

namespace Cochain

/-- `α` is a coboundary when some gauge trivializes every edge. -/
def IsCoboundary (α : Cochain X G) : Prop :=
  ∃ β : V → G, ∀ u v, ({u, v} : Finset V) ∈ X.edges → α.toFun u v = β u * (β v)⁻¹

/-- The gauge action: on an edge `(u, v)` the value becomes `(β u)⁻¹ * α u v * β v`; off the
edges it stays `1`. -/
def gauge (β : V → G) (α : Cochain X G) : Cochain X G where
  toFun u v := if ({u, v} : Finset V) ∈ X.edges then (β u)⁻¹ * α.toFun u v * β v else 1
  inv_symm u v h := by
    have h' : ({v, u} : Finset V) ∈ X.edges := by rwa [Finset.pair_comm]
    show (if ({v, u} : Finset V) ∈ X.edges then (β v)⁻¹ * α.toFun v u * β u else 1) =
      (if ({u, v} : Finset V) ∈ X.edges then (β u)⁻¹ * α.toFun u v * β v else 1)⁻¹
    rw [if_pos h', if_pos h, α.inv_symm u v h]
    simp [mul_assoc]
  one_of_not_mem u v h := if_neg h

/-- The value of a gauged cochain on an edge. -/
theorem gauge_toFun_of_mem (β : V → G) (α : Cochain X G) {u v : V}
    (h : ({u, v} : Finset V) ∈ X.edges) :
    (gauge β α).toFun u v = (β u)⁻¹ * α.toFun u v * β v :=
  if_pos h

/-- The identity gauge acts trivially. -/
theorem gauge_one (α : Cochain X G) : gauge (1 : V → G) α = α :=
  ext_edges fun u v h => by
    rw [gauge_toFun_of_mem _ _ h]
    simp

/-- Gauging twice is gauging by the pointwise product, in the order `γ * β`. -/
theorem gauge_gauge (β γ : V → G) (α : Cochain X G) :
    gauge β (gauge γ α) = gauge (γ * β) α :=
  ext_edges fun u v h => by
    rw [gauge_toFun_of_mem _ _ h, gauge_toFun_of_mem _ _ h, gauge_toFun_of_mem _ _ h]
    simp [mul_assoc]

/-- The gauge action as scalar multiplication: `β • α = gauge β α`. -/
instance : SMul (V → G) (Cochain X G) := ⟨gauge⟩

/-- `β • α` is `gauge β α`. -/
theorem smul_def (β : V → G) (α : Cochain X G) : β • α = gauge β α := rfl

/-- The identity gauge acts trivially. -/
theorem one_smul (α : Cochain X G) : (1 : V → G) • α = α :=
  gauge_one α

/-- `β • (γ • α) = (γ * β) • α`, with the pointwise product `(γ * β) u = γ u * β u`. -/
theorem smul_smul (β γ : V → G) (α : Cochain X G) : β • γ • α = (γ * β) • α :=
  gauge_gauge β γ α

end Cochain

end TauCeti.CoboundaryExpansion
