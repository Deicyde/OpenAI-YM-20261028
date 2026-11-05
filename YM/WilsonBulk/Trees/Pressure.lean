import YM.WilsonBulk.Trees.Predictor

/-! # Flat covariance and mean cutoff pricing

No strict-event path costs here. This is `Width` on unperiodized coarse-to-fine
Fourier cover coefficients (test ONE root). After pre-length width choices &
foot bounds (a fixed d list announced before length choice), permit polynomial
post-L costs for these outputs in log spacing age. Caller admits them via schedule
as in `HessRates` and `age` and supplies purchase receipts. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk
open Lattice Laurent Filter Function Bloch
open RG Finset Precision Exterior Stationary Audience Matrix FreeResolvent Tree
open Work.F08 Lifted
open scoped Topology BigOperators Matrix Classical

variable {α β γ : Type}
variable {A B : Row α β} {H : Row β γ} {σ p q r s : ℝ} {t u d : ℕ}
section arithmetic
lemma opposite_width (h : (minusRows A B).strip σ p) : (minusRows B A).strip σ p := by
  intro i j
  simpa only [Width,minusRows, norm_sub_rev (B i j _) (A i j _)] using (h i j)

variable [Fintype β]
lemma collapseDifference (h : A.strip σ p) (he : B.strip σ q) (hg : H.strip σ r) (hs : 0≤ σ)
    (hc : (minusRows A B).strip σ s) (a : ℝ) :
    (minusRows (scaleRows a (composeRows A H)) (scaleRows a (composeRows B H))).strip σ (‖a‖*((Fintype.card β:ℝ)*(s*r))) := by
  let X:= scaleRows a (composeRows A H); let Y:=scaleRows a (composeRows B H)
  let Z:=scaleRows a (composeRows (minusRows A B) H)
  have hx:= strip_scale (strip_compose hs h hg) a; have hy:= strip_scale (strip_compose hs he hg) a
  have hZ:= strip_scale (strip_compose hs hc hg) a
  suffices hb: minusRows X Y = Z by rw [show scaleRows a (composeRows A H)=X from rfl,show scaleRows a (composeRows B H)=Y from rfl,hb]; exact hZ
  apply Next.Free.bank_injective (Row.rights _ _ (strip_minus hx hy) hs) (Row.rights _ _ hZ hs)
  intro n; rw [acts_minus hs hx hy, acts_scale, acts_scale, acts_scale,acts_compose hs hc hg,acts_compose hs h hg,acts_compose hs he hg, acts_minus hs h he]; simp only [Matrix.sub_mul,smul_sub]
end arithmetic

variable {G : Gauge} {P : Patch} {K : KernelChoices} {B V : Bed} {T : Model P K}

-- joint arbitrary cutoff comparisons
lemma beam_bill (h : Serves G T B σ p) (hb : Serves G T V σ q) (hs : 0 ≤ σ) (hC : (minusRows (fluct G T B) (fluct G T V)).strip σ r)
    (hX : (flare G P).strip σ s) :
    (minusRows (beams G T B) (beams G T V)).strip σ (‖K.penalty‖*((Fintype.card (Co P.L (Loc G 1)):ℝ)*(r*s))) := by
  exact collapseDifference h.width hb.width hX hs hC _

lemma Serves.lower {η M : ℝ} (h : Serves G T V σ p) (he : η ≤ σ) (hg : p≤ M) : Serves G T V η M :=
  ⟨strip_mono h.width he hg,h.covers⟩

-- tie to actual `Levels`
variable {A : Levels G} {F : MapPrices} (V : Horizon A)
abbrev historyPatch (A : Levels G) (i : ℕ) := (A.clock.op i 0).patch
abbrev historyModel (A : Levels G) (i : ℕ) := Model (historyPatch A i) A.clock.kernel

-- include conditional packing service stages in theorem type leaving path estimates reachable.
lemma sites_forecast (K : KernelChoices) (j : ℕ) (F : MapPrices) (h : 0≤F.Ω j) :
    ∃ σ, 0 < σ ∧ σ ≤ F.α j ∧ ∀ P : Patch, P.J=j → P.Branches K G →
      ∀ (T : Model P K), ∃ C, 0 ≤ C ∧ (flare G P).strip σ C ∧
        ∀ (A : Levels G) (H : Horizon A), H.Suffices F →
        ∀ (m N), m≤N → stage A m=j → Serves G T (H.H N m) σ C := by
  obtain ⟨u,hu,hC⟩:= packing_bill G j K (F.α j) (F.η j) (F.Ω j) (F.alpha_pos j) (F.eta_pos j) h
  refine ⟨min u (F.α j), lt_min hu (F.alpha_pos _), min_le_right .., fun P hj hP T=> ?_⟩
  obtain ⟨C,hc,hX⟩:= hC P hj hP T; obtain ⟨B,hB,hK⟩:= (Stamped.flare (P:=P) (G:=G)).bound (F.α j)
  refine ⟨C+B,add_nonneg hc hB, strip_mono hK (min_le_right ..) (by linarith), fun A H h m N hm he=>?_⟩
  apply Serves.lower (hX (H.H N m) (A.params m).clip (F.Ω j) ?_ ?_) (min_le_left ..) (by linarith)
  · rw [← he]; apply strip_mono (h.rows _ _ hm).2.1 ?_ le_rfl; exact mul_le_of_le_one_left (F.alpha_pos (stage A m)).le (inch_le _)
  rw [← he]; exact h.all _ _ hm

-- simpler forecast uniform all even for dummy j (Padded Ω, actually nonnegative whenever used)
lemma preflight (G : Gauge) (K : KernelChoices) (F : MapPrices) :
    ∃ σ : ℕ→ℝ,(∀ j, 0 < σ j ∧ σ j ≤ F.α j) ∧
      ∀ j : ℕ, ∀ (P : Patch), P.J=j → P.Branches K G →
          ∀ T : Model P K, ∃ C, 0 ≤ C ∧ (flare G P).strip (σ j) C ∧
            ∀ (U : Levels G) (H : Horizon U), H.Suffices F → ∀ (m N), m≤N → stage U m=j →
               Serves G T (H.H N m) (σ j) C := by
  have ht j : ∃ σ, (0 < σ ∧ σ ≤ F.α j) ∧ ∀ P : Patch, P.J=j → P.Branches K G →
      ∀ T : Model P K, ∃ C, 0 ≤ C ∧ (flare G P).strip σ C ∧ ∀ (U : Levels G) (H : Horizon U), H.Suffices F →
        ∀ (m N), m ≤ N → stage U m=j → Serves G T (H.H N m) σ C := by
    by_cases hu: 0≤F.Ω j
    · obtain ⟨σ,h,h',H⟩:= sites_forecast (G:=G) K j F hu; exact ⟨σ,⟨h,h'⟩,H⟩
    refine ⟨F.α j,⟨F.alpha_pos _,le_rfl⟩, fun P he hP T=>?_⟩
    obtain ⟨B,hB,hT⟩:= (Stamped.flare (P:=P) (G:=G)).bound (F.α j); refine ⟨B,hB,hT,fun U H h m N hm he=>False.elim (hu (he ▸ Pert.Bulk.merit (h.rows N m hm)))⟩
  choose S hs ht using ht; exact ⟨S,hs,ht⟩

-- Release multiple families; e.g. `b < a` use for flat estimate & Γ. Ages & cutoff fine.
variable {i N N' : ℕ} {P₀ : historyModel A i}
set_option quotPrecheck false
local notation "Qv" => (A.params (i+1)).clip
local notation "j₀" => stage A (i+1)
lemma glimpse (h : V.Suffices F)
    (ht : Serves G P₀ (V.H N (i+1)) σ p)
    (hQ : Serves G P₀ (V.H N' (i+1)) σ q)
    (hs : 0≤ σ) (hF : 0 ≤ r) (hi : i<N) (hj : i<N') (hK : (minusRows (flat V N (i+1)) (flat V N' (i+1))).strip σ r) :
    let A' : ℝ:= Fintype.card (Co (A.S.block i) (Loc G 1)); let b' : ℝ:= Fintype.card PotentialForm
    (minusRows (fluct G P₀ (V.H N (i+1))) (fluct G P₀ (V.H N' (i+1)))).strip σ (A'*A'*b'*r*p*q) := by
  intro A' b'; apply opposite_width; exact packing_cost (A.blocks i 0).branches P₀ _ _ hs (F.alpha_pos j₀).le Qv (F.eta_pos j₀) hF (h.all _ _ hi) (h.all _ _ hj)
    (h.rows _ _ hi).2.1 (h.rows _ _ hj).2.1 ht hQ hK

end YM.WilsonBulk
