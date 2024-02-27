/-
Lemmas irrelavant to `PowerSeries` or `Padic`.

Current goals:
1. prove `Polynomial.eval₂_trunc_at_nilp`
-/

import Mathlib.Tactic


-- noncomputable section
noncomputable section noncom
open Classical

example {p q : Prop} : p ∨ q ↔ (¬p → q) := Decidable.or_iff_not_imp_left

section ideal

variable {R : Type _} [CommRing R]

def Ring.quot_bot (R) [CommRing R] :
    R ⧸ (⊥ : Ideal R) ≃+* R :=
  RingHom.quotientKerEquivOfSurjective (f := RingHom.id R) fun _ ↦ ⟨_, rfl⟩

def Ideal.quotientMap_bot  {S} [CommRing S] {I : Ideal R} (f : R →+* S) (hI : I ≤ RingHom.ker f) :
    R ⧸ I →+* S :=
  (Ring.quot_bot S).toRingHom.comp (Ideal.quotientMap (0 : Ideal S) f hI)

end ideal

section nilp

variable {R : Type u} [CommRing R]

-- `a` is nilpotent in `ℤ ⧸ a ^ n`.
lemma nat_mod_pow_nilp {a n : ℕ} : IsNilpotent (a : ZMod (a ^ n)) :=
  ⟨n, (Trans.trans (a.cast_pow n).symm (ZMod.nat_cast_self (a ^ n)))⟩

theorem choose_IsNilpotent_ne_zero [Nontrivial R] {r : R} (h : IsNilpotent r) : choose h ≠ 0 :=
  fun x ↦ (show r ^ (choose h) ≠ 0 by rw [x, pow_zero]; exact one_ne_zero) (choose_spec h)

theorem nilp_pow_ge_choose_eq_zero {r : nilradical R} {n : ℕ} (h : n ≥ choose r.2) : r.1 ^ n = 0 := by
  rw [(pow_mul_pow_sub _ h).symm, choose_spec r.2]
  exact zero_mul _

end nilp

section polynomial
open BigOperators Finset
namespace Polynomial
variable {R : Type _} [Semiring R] {p q : R[X]}
variable {S : Type _} [CommSemiring S]
variable {f : R →+* S}
-- truncation map
#check PowerSeries.trunc
def trunc (n : ℕ) (p : R[X]) : R[X] :=
  ∑ k in Ico 0 n, monomial k (coeff p k)

#check PowerSeries.coeff_trunc
theorem coeff_trunc (m n) (p : R[X]) :
    (p.trunc n).coeff m = if m < n then p.coeff m else 0 := by
  simp only [trunc, Nat.Ico_zero_eq_range, finset_sum_coeff, coeff_monomial, sum_ite_eq', mem_range]

theorem eval₂_trunc_at_nilp (h : s ^ n = 0):
    (p.trunc n).eval₂ f s = p.eval₂ f s := by
  simp [eval₂, sum, coeff_trunc]
  sorry

end Polynomial
end polynomial

end noncom

-- computable section
section com

end com
