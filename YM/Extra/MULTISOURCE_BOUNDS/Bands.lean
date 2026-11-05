import YM.Axis.Matrix
import YM.Extra.MULTISOURCE_BOUNDS.Root

/-!
# Actual-address budget and change of radii on Overlay.Bands

Nonfactorial (slightly stronger mixed output ask), complex regular and forced
kernels, physical cover exponents, and true finite-order left derivatives
on the entire healthy set. `Active` is separate. κ denotes the *positive*
forced divisor in physical applications, i.e. forced absolute sums must be
small enough BEFORE division; we write the conditions multiplicatively.
No assumption of sign or lower bound on a vacuum entry at marked addresses.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Multi
open Lattice RG Wilson Overlay Marker Finset
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical

variable {n : Side} {ι V : Type*} [DecidableEq V]

lemma grain_of_sup {G : Gauge} {f : Config G n → ℂ} {o : Site n} {b : ℝ} {P : BudgetPoint} {X : Support n}
    (h : P.supBounds o X f b) : Mix.grain P X f o (Real.exp 1*b) := by
  refine ⟨fun _ => b, fun _ => h.1, ?_, fun k hk hd U hU => h.2 U hU k hk hd⟩
  have he := mul_le_mul_of_nonneg_right (Real.sum_le_exp_of_nonneg (x:=1) zero_le_one (P.order+1)) h.1
  rw [sum_mul] at he; apply le_trans (le_of_eq ?_) he; exact sum_congr rfl fun i _ => by ring

variable {G : Gauge} {R : Census V} {P : Rep G n}

def mixed (q : R.Mode) : Prop := 2 ≤ q.val.card
def single (q : R.Mode) : Prop := q.val.card = 1
def entire (_ : R.Mode) := True

def Weighted (q : ι → R.Mode) (X : ι → Support n) (p : BudgetPoint) (w : V → ℝ) (δ : ℝ) (f : ι → ℝ) :=
    Rooted (fun i => (q i).val) X p.B (p.supportExponent+δ) (fun i => Poly.toll w (q i) * f i)

namespace Weighted
variable {q : ι → R.Mode} {X : ι → Support n} {p : BudgetPoint} {u w : V → ℝ} {δ b c : ℝ}
  {f g : ι → ℝ}

theorem add (h : Weighted q X p w δ f b) (hg : Weighted q X p w δ g c) : Weighted q X p w δ (fun i => f i+g i) (b+c) := by
  unfold Weighted; simp only [mul_add]; exact Rooted.add h hg



theorem mono (h : Weighted q X p u δ f b) (hw : ∀ v, 0 ≤ w v) (hg : ∀ i, 0 ≤ g i)
    (he : ∀ v, w v ≤ u v) (hy : ∀ i, g i ≤ f i) (hc : b ≤ c) : Weighted q X p w δ g c :=
  Rooted.mono h (fun i => mul_nonneg (prod_nonneg fun v _ => hw v : 0≤Poly.toll w _) (hg i))
    (fun i => mul_le_mul (prod_le_prod (fun v _ => hw v) fun v _ => he v : Poly.toll w _ ≤ Poly.toll u _)
      (hy i) (hg i) (prod_nonneg fun v _ => (hw v).trans (he v))) le_rfl hc

variable [Fintype V]

theorem reset {o : V → Site n} {μ : ℕ} (hot : Finset V) {D r : ℝ} (hμ : 0 < μ)
    (h : Weighted q X p u δ f b) (hh : Occupancy o μ) (hB : 8 ≤ p.B) (hw : ∀ v, 0 ≤ w v)
    (hu : ∀ v, 0 ≤ u v) (hD : 1 ≤ D) (hr : 1 ≤ r) (he : 0 ≤ δ)
    (hi : ∀ v∈hot, D*w v ≤ u v*r) (hc : ∀ v∉hot, D*w v ≤ u v/r)
    (hp : r ≤ Real.exp (δ*p.B/(64*μ))) (hf : ∀ i, 0 ≤ f i)
    (pin : ∀ i, 0<f i → ((q i).val∩hot).image o ⊆ X i)
    (pack : ∀ i, 0<f i → let s := (q i).val; let y := (s∩hot).image o
      s.Nonempty ∧ ((s∩hot).card ≤ (s\hot).card ∨
        2 ≤ y.card ∧ (↑y : Set (Site n)).Pairwise (fun x y => p.B^2 ≤ separation x y))) :
    Weighted q X p w 0 f (b/D) := by
  have hD' : 0 < D := zero_lt_one.trans_le hD
  intro s
  apply Budget.mono (Budget.scale (h s) (inv_pos.mpr hD').le)
  · intro i; split
    · exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (prod_nonneg fun v _ => hw v : 0≤ Poly.toll w _) (hf i))
    exact le_rfl
  · intro i; split_ifs
    · dsimp only; rw [add_zero]
      rcases (hf i).eq_or_lt with e|e
      · rw [← e]; simp
      have hg : D*Poly.toll w (q i) ≤ Poly.toll u (q i) * Real.exp (δ*coverNumber p.B (X i)) := by
        obtain ⟨hne,hg⟩ := pack i e
        apply toll_reset (μ:=μ) hot _ (fun v _ => hu v) (fun v _ => hw v) hr hD he hμ
          (fun v hv => hi v (mem_inter.mp hv).2) (fun v hv => hc v (mem_sdiff.mp hv).2) hp hne
          (hg.imp_right (fun ⟨hy,hz⟩ => mixed_pack hB hh _ hy hz (X i) (pin i e)))
      rw [inv_mul_eq_div,le_div_iff₀ hD',add_mul,Real.exp_add]
      have h' := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hg (hf i))
        (Real.exp_pos (p.supportExponent * coverNumber p.B (X i))).le
      linarith only [h']
    rw [mul_zero]
  rw [inv_mul_eq_div]

end Weighted

variable {A : Bands R P}

abbrev forced (P : Rep G n) (i : ℕ × ℕ) := (P.activities.forced i.1).support
abbrev tags (A : Bands R P) (i : ℕ × ℕ) := A.marks i.1 i.2

/-- Pre-unit absolute budget; a strengthening of the two separate parts of
JMtheta (they can be added at twice the displayed cost). Marker names distinct
within each surviving square-free monomial. Use nonfactorial order THROUGH
P.p.order for regular kernels. No derivatives on forced terms. -/
structure Spent (ok : R.Mode → Prop) (A : Bands R P) (w : V → ℝ) (δ κ c : ℝ) : Prop where
  exponent : ∃ a : ℕ → ℝ, (∀ i, 0 ≤ a i) ∧ (∀ i, ok (A.rays i) → ∀ v∈ (A.rays i).val,
    P.p.supBounds (A.origins v) (A.support i) (A.H i) (a i)) ∧ Weighted A.rays A.support P.p w δ a c
  gas : ∃ b : ℕ × ℕ → ℝ, (∀ i, 0 ≤ b i) ∧ (∀ i, ok (tags A i) → ∀ U, ‖A.entries i.1 i.2 U‖ ≤ b i) ∧
    Weighted (tags A) (forced P) P.p w δ b (κ*c)

namespace Spent
variable {ok ok' : R.Mode → Prop} {w u : V → ℝ} {δ κ b c : ℝ}

theorem add (h : Spent ok A w δ κ b) (H : Spent ok' A w δ κ c) :
    Spent (fun i => ok i ∨ ok' i) A w δ κ (b+c) := by
  obtain ⟨⟨a,h1,h2,h3⟩,⟨α,h₁,h₂,h₃⟩⟩ := h
  obtain ⟨⟨z,g1,g2,g3⟩,⟨β,g₁,g₂,g₃⟩⟩ := H
  refine ⟨⟨fun i => a i + z i,fun i => add_nonneg (h1 i) (g1 i),?_,h3.add g3⟩,
    ⟨fun i => α i + β i,fun i => add_nonneg (h₁ i) (g₁ i),?_,by rw [mul_add]; exact h₃.add g₃⟩⟩
  · intro i hi v hv
    refine ⟨add_nonneg (h1 i) (g1 i),fun U hu l hl ht => ?_⟩
    rcases hi with hi|hi
    · exact ((h2 i hi v hv).2 U hu l hl ht).trans (le_add_of_nonneg_right (g1 i))
    exact ((g2 i hi v hv).2 U hu l hl ht).trans (le_add_of_nonneg_left (h1 i))
  rintro i (hi|hi) U
  · exact (h₂ i hi U).trans (le_add_of_nonneg_right (g₁ i))
  exact (g₂ i hi U).trans (le_add_of_nonneg_left (h₁ i))

theorem mono (h : Spent ok A u δ κ b) (hw : ∀ v, 0 ≤ w v) (he : ∀ v, w v ≤ u v)
    (hκ : 0≤κ) (hc : b≤c) (hX : ∀ i, ok' (A.rays i) → ok (A.rays i))
    (hK : ∀ i, ok' (tags A i) → ok (tags A i)) : Spent ok' A w δ κ c := by
  obtain ⟨⟨a,h1,h2,h3⟩,⟨k,g1,g2,g3⟩⟩ := h
  exact ⟨⟨a,h1,fun i hi => h2 i (hX i hi),h3.mono hw h1 he (fun _ => le_rfl) hc⟩,
    ⟨k,g1,fun i hi => g2 i (hK i hi),g3.mono hw g1 he (fun _ => le_rfl) (by gcongr)⟩⟩

theorem complete (h : A.Active) (hw : ∀ v, 0 ≤ w v) (hκ : 0 ≤ κ) (h1 : Spent single A w δ κ b)
    (h2 : Spent mixed A w δ κ c) : Spent entire A w δ κ (b+c) := by
  have he (i : R.Mode) (hi : i.val.Nonempty) : single i ∨ mixed i := by
    unfold single mixed; have := Finset.card_pos.mpr hi; omega
  exact (h1.add h2).mono hw (fun _ => le_rfl) hκ le_rfl
    (fun i _ => he _ (h.proper i)) (fun i _ => he _ (h.occurs i.1 i.2))

theorem radial (h : Spent entire A w 0 κ c) (hw : ∀ v, 0<w v) (hk : 0<κ)
    (hu : ∀ i, w i * ‖A.units i‖ ≤ b) : A.Radial w b c c κ := by
  obtain ⟨⟨a,h1,h2,h3⟩,⟨k,g1,g2,g3⟩⟩ := h
  refine ⟨hw,hu,hk,⟨a,fun i => ⟨h1 i,h2 i trivial⟩,fun v => ?_⟩,
    ⟨k,fun i j => ⟨g1 (i,j),g2 (i,j) trivial⟩,fun v => ?_⟩⟩
  · simpa [BudgetPoint.mass,mul_left_comm] using h3 v
  simpa [BudgetPoint.mass,mul_left_comm,tags,mul_comm c κ] using g3 v

theorem reset [Fintype V] (h : Spent ok A u δ κ b) (H : A.Active) {μ : ℕ} (hot : Finset V) {D r : ℝ} (hμ : 0 < μ)
    (hh : Occupancy A.origins μ) (hB : 8 ≤ P.p.B) (hw : ∀ v, 0 ≤ w v) (hu : ∀ v, 0 ≤ u v)
    (hD : 1 ≤ D) (hr : 1 ≤ r) (he : 0 ≤ δ) (hi : ∀ v∈hot, D*w v ≤ u v*r) (hc : ∀ v∉hot, D*w v ≤ u v/r)
    (hp : r ≤ Real.exp (δ*P.p.B/(64*μ)))
    (pack : ∀ i, ok i → let s := i.val; let y := (s∩hot).image A.origins
      s.Nonempty ∧ ((s∩hot).card ≤ (s\hot).card ∨
        2 ≤ y.card ∧ (↑y : Set (Site n)).Pairwise (fun x y => P.p.B^2 ≤ separation x y))) :
    Spent ok A w 0 κ (b/D) := by
  obtain ⟨⟨a,h1,h2,h3⟩,⟨k,g1,g2,g3⟩⟩ := h
  let a' i := if ok (A.rays i) then a i else 0
  let k' i := if ok (tags A i) ∧ A.entries i.1 i.2 ≠ 0 then k i else 0
  have ha i : 0≤a' i := by dsimp only [a']; split <;> simp [h1]
  have hk i : 0≤k' i := by dsimp only [k']; split <;> simp [g1]
  replace h3 := h3.mono hu ha (fun _ => le_rfl) (fun i => by dsimp [a']; split <;> simp [h1]) le_rfl
  replace g3 := g3.mono hu hk (fun _ => le_rfl) (fun i => by dsimp [k']; split <;> simp [g1]) le_rfl
  refine ⟨⟨a',ha,fun i hi => ?_,Weighted.reset hot hμ h3 hh hB hw hu hD hr he hi hc hp ha ?_ ?_⟩,
    ⟨k',hk,fun i hi => ?_,?_⟩⟩
  · simpa only [a',if_pos hi] using h2 i hi
  · intro i _ x hx
    obtain ⟨v,hv,rfl⟩ := mem_image.mp hx
    exact H.pins i v (mem_inter.mp hv).1
  · intro i hi
    apply pack
    by_contra hh; simp [a',hh] at hi
  · dsimp only [k']; split
    next => exact g2 i hi
    next hh => simp [show A.entries i.1 i.2=0 by tauto]
  rw [← mul_div_assoc]; refine Weighted.reset hot hμ g3 hh hB hw hu hD hr he hi hc hp hk ?_ ?_
  · intro i hi x hx
    obtain ⟨v,hv,rfl⟩ := mem_image.mp hx
    apply H.retained i.1 i.2 _ v (mem_inter.mp hv).1
    intro hh; simp [k',hh] at hi
  intro i hi
  apply pack
  by_contra hh; simp [k',hh] at hi

variable {V : Type} [DecidableEq V] [Fintype V] {R : Census V} {A : Bands R P} {w : V → ℝ}

omit [Fintype V] in
private lemma resell {ι : Type*} (i : V) {q : ι → R.Mode} {X : ι → Support n} {f g : ι → ℝ} {c r d : ℝ}
    (h : Weighted q X P.p w 0 f c) (hw : ∀ v, 0 ≤ w v) (hp : 0≤d) (hg : ∀ i, 0≤g i)
    (hk : ∀ i, g i ≤ d*f i) (hc : d*c ≤ r) (b : Bool) :
    SumBudget (fun j => if Mix.ranked (q j) = b ∧ i∈(q j).val then
      Poly.toll w (q j)*Mix.loaf P.p (X j) 0 (g j) else 0) r := by
  apply Budget.mono (Budget.scale (h i) hp) _ _ hc
  · intro j; split
    · exact mul_nonneg (prod_nonneg fun v _ => hw v : 0≤Poly.toll w _) (mul_nonneg (Real.exp_pos _).le (hg j))
    exact le_rfl
  intro j; split
  next ht =>
    rw [if_pos ht.2]
    unfold Mix.loaf; dsimp only
    have := mul_le_mul_of_nonneg_left (hk j) (mul_nonneg (prod_nonneg fun v _ => hw v : 0≤Poly.toll w (q j))
      (Real.exp_pos ((P.p.supportExponent+0)*coverNumber P.p.B (X j))).le)
    unfold Poly.toll; linarith only [this]
  next ht => exact mul_nonneg hp ((h i).1 _)

omit [Fintype V] in
theorem stubs {W : ℝ} (h : Spent entire A (fun _ => W) 0 κ c) (hW : 0≤W)
    (hc : Real.exp 1*c ≤ 1) (hk : κ*c ≤ 1) (H : A.Active) (hy : Mix.Stubs.far (A:=A))
    (hu : ∀ v, W*‖A.units v‖ ≤ 1) : Mix.Stubs.Holds A W := by
  obtain ⟨⟨a,h1,h2,h3⟩,⟨k,g1,g2,g3⟩⟩ := h
  let k' j := if A.entries j.1 j.2 ≠ 0 then k j else 0
  have he i : 0 ≤ k' i := by unfold k'; split <;> simp [g1]
  let T : Mix.Stubs A := {
    a := fun i => Real.exp 1 * a i
    k := k'
    nonnegative := fun i => mul_nonneg (Real.exp_pos _).le (h1 _)
    usable := he
    kernels := fun i v hv => grain_of_sup (h2 i trivial v hv)
    supplies := fun i j U => by
      unfold k'; dsimp only; split <;> rename_i hn
      · exact g2 (i,j) trivial U
      simp [not_ne_iff.mp hn]
    paid := fun i hi hh => by simp [k',hh] at hi }
  have paid (b : Bool) : T.funded (fun _ => W) 0 b 1 := ⟨fun i => resell i h3 (fun _ => hW) (Real.exp_pos _).le
      T.nonnegative (fun _ => le_rfl) hc b,
    fun i => resell i g3 (fun _ => hW) zero_le_one he (fun j => by dsimp [k']; split <;> simp [g1]) (by simpa using hk : 1*(κ*c) ≤ 1) b⟩
  exact ⟨hu,H,hy,T,paid false, Or.inl (paid true)⟩

end Spent
end YM.Extra.Multi
