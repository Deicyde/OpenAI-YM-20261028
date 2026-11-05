import YM.AnalyticNext.QUARTIC_MATCH.Costed
import YM.AnalyticNext.QUARTIC_MATCH.Local.Realized


/-!
# Charging the actual prescriptions

Both base costs at *actual* charged path width. Occurrence pricing of
lifts on the cover. Serve pre-L epoch with output besides periods used.
Cubic must come first. Output width, price explicit relations; don't assume
next Ledger compatibility (prove separately at Quote rates).
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch.Local
open Filter Function Lattice Laurent Matrix Hessian Analysis RG Precision Exterior Bid Wilson Branch Bloch
open Progress.StationaryScenes Work.F03 YM.Next.Free Work.F08 Pre.Centered Tree
open Joint Estimate Estimate.Purse Estimate.Logfee Estimate.Depot BoxChain Premium Evoke Budget Analyzers
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace
namespace Wages
open Green (wt)
open Tracks

lemma budget (G : Gauge) {k : ℕ} (hk : k ≤ 4) {w : Fin k} {u : ℝ} (he : 0<u) (R : ℝ) : ∃ C : ℝ, 0≤C ∧
    ∀ {c : Side} (p : Clip) (W : PathData G) {σ τ K Λ R3 R4 : ℝ}, W.Bounds p τ K Λ → Rotate.Led W 1 k (boom u) σ R R3 R4 →
    Alive (c:=c) w (Residual.baseAt p W) (rate u) (C*assistance 1 R3 R4) := by
  let r := factor (boom u); have hp := zero_le_one.trans (factor_ge (booms he).le)
  refine ⟨feeDown G k (boom u) R u*r^k,mul_nonneg (fee_paid ..).le (pow_nonneg hp _),?_⟩
  intro c p W σ τ K Λ R3 R4 hW hh x z
  let X i := (x i).1
  let d (i) := sparse (x i) (z i)
  let η i := r*‖z i‖
  have hx i : 0 ≤ η i := mul_nonneg hp (norm_nonneg _)
  let Q := Wages.account 1 none X (fun _ => boom u) η hx
  have he' i := coarse_enough Q (booms he).le i (by simp [Purse.tagged,Q,Wages.account]) (x i) (z i) rfl (fun j => by
    change wt (boom u/(↑(1:ℕ):ℝ)) j _ = _; simp only [Nat.cast_one,div_one,X])
  let M := span (rate u) (X w) X
  have hq : Stamp Q Finset.univ 1 u M (X w) := by
    have ht := journey he Q w X 1 hk (fun _ _ => rfl);
    simpa only [M,PNat.val_ofNat, Nat.cast_one,div_one] using ht
  have hV : Linkbill 1 Q d := fun i j => by
    change Q.Pays {i} _ (↑(1:ℕ):ℝ)⁻¹
    rw [Nat.cast_one,inv_one]; exact (he' i).1 j
  have hs : Plaque.BendBill 1 Q d := fun i j => by
    simpa only [PNat.val_ofNat,Nat.cast_one,one_pow,inv_one,d] using (he' i).2 j
  have hu := base_amount Finset.univ (show (Finset.univ:Finset (Fin k)).card≤k from (by simp))
    hW hh (booms he) (show tollRate Q 1 (boom u) from travels _ _ _ _ hx _ fun _ => (abs_of_pos (booms he)).le) rfl hV hs (span_pos ..).le he (X w) hq
  change M*_ ≤ _ at hu
  rw [show bill Finset.univ d (fun x => mainTerm p W (represent (x : Dir G c))) 0=_ from
    (univEstimate d _ 0 (Residual.base_smooth hW))] at hu
  exact hu.trans_eq (by unfold target Q Wages.account η; simp only [Finset.prod_mul_distrib,Finset.prod_const, Finset.card_univ,Fintype.card_fin]; ring)

open Mail Sheets
variable (G : Gauge) (j : ℕ) (D D' u κ η C a : ℝ) (hp : 0<u) (he : boom u ≤ η) (hκ : 0<κ) (ha : 0<a)
include hp he hκ ha




/-- specify lower three exact at these probes, with a paid cube. Quantifier
of `C3` can be given within its width reservation as stated (fits plateau).
Bounds on R beyond that reservation NOT used to erase its fourth jet. -/
theorem charge_four (P : Printed 3) (C3 : ℝ) (h3 : 0≤C3) (hK : u ≤ Tracks.purchase j a η C κ) :
    ∃ δ Z : ℝ,0<δ ∧ 0≤Z ∧ ∀ {K : Patch} {L : KernelChoices} {W R : PathData G} {M N : Bed} {p q : Clip}
        {σ τ v Λ t σ' u' C' R3 R4 T' : ℝ} (S : Analyzers.Series K L G M p W v),
      K.J=j → L.penalty=κ → W.Bounds p τ u' Λ → R.Bounds q t C' T' →
      Rotate.Led W K.L 4 (boom u) σ D R3 R4 → Rotate.Led R 1 4 (boom u) σ' D' (C3*assistance K.L R3 0) 0 →
      Attached M W → (∀ c,Floor M p c a C) → (∀ c,Sworn M c G) → M.metric.strip η C → (∀ i,(R.quartic i).coeff=0) →
      ∀ U : Cross K.L (TypeFace 1) (TypeFace 1), (∀ c : Side, allowanceSide K ≤ c.val →
        Evoke.motion (stepAt K L c) U η C ∧
        Inputs (stepAt K L c) (installed (stepAt K L c).ratio U) (M.metric.acts (c*K.L)) (N.metric.acts c)) →
      ∀ d : ℕ→Side, (∀ i, allowanceSide K ≤ (d i).val) → Tendsto (fun i => (d i).val) atTop atTop →
        (∀ i : ℕ, ∀ k<4, iteratedFDeriv ℝ k (S.canonical (d i)) 0=iteratedFDeriv ℝ k (Residual.baseAt q R (c:=d i)) 0) →
        ∃ A : rootArray G 3, SumBudget (fun i => (letters P A i).budget δ) (Z*(assistance K.L R3 R4+assistance K.L R3 0^2)) ∧
          ∀ i j : ℕ, j≤4 → SameJet j (S.canonical (d i)) (Residual.baseAt q (fourth R (letters P A))) := by
  obtain ⟨R,hR,H⟩ := buys4 G j D u κ η C a hp he hκ ha hK
  obtain ⟨B,hB,D₁⟩ := budget G (w:=(0:Fin 4)) (by omega) hp D'
  let s := rate u; let b := (Nat.factorial 4:ℝ)⁻¹*(R+B*(1+C3))
  obtain ⟨δ,Q,hδ,hQ,HQ⟩ := Series.open_four G P _ (show 0 < s/4 by unfold s; have h := after hp; positivity)
  refine ⟨δ,Q*b,hδ, mul_nonneg hQ (mul_nonneg (by positivity) (by positivity)),?_⟩
  intro K L W Z M N p q σ τ v Λ t σ' u' C' R3 R4 T' S hj hk hw ht H' H'' hy hM hN hQ' hr U hU d hd hD hc
  let k := assistance K.L R3 R4+assistance K.L R3 0^2
  have h₁ c (hp : allowanceSide K ≤ c.val) := H _ _ (stepAt K L c) p W (S.choice c) σ _ _ _ _ _ hj hk S.society hw H' U
    (hU c hp).1 M N hy (hN _) (hM _) hQ' (hU c hp).2 (S.tree c) (S.controller c hp) v S.cheap (S.gap c hp) _ (S.solved c hp)
  have hu : 1≤k := le_trans (cost_support H') (le_add_of_nonneg_right (sq_nonneg _))
  have h₂ c (h' : allowanceSide K ≤ c.val) : Spatial ((S.debt hw ht 4).raw c) (s/4) (b*k) := by
    have heM := (S.debt hw ht 4).raw_buys h'
    rw [heM]
    have hq : Alive (c:=c) (0:Fin 4) (Residual.baseAt q Z) s (B*(1+C3)*k) := by
      refine (D₁ q Z ht H'').earns ?_; rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ hB
      simp only [assistance,PNat.val_ofNat,Nat.cast_one,one_pow,div_one,add_zero]
      have he : 1 ≤ assistance K.L R3 0 := cost_support (Rotate.led_lower H' (booms hp).le)
      rw [add_mul,one_mul]; apply add_le_add hu
      apply mul_le_mul_of_nonneg_left _ h3
      change _ ≤ assistance _ _ _ + assistance _ _ _ ^ 2
      have ht : 1 ≤ assistance K.L R3 R4 := cost_support H'
      change assistance K.L R3 0 ≤ _ + _
      nlinarith only [he,ht, sq_nonneg (assistance K.L R3 0-1)]
    rw [show b*k=(Nat.factorial 4:ℝ)⁻¹*(R*k+B*(1+C3)*k) by unfold b; ring]
    have h₀ : 0 ≤ k := zero_le_one.trans hu
    exact Alive.gives (f:=S.canonical c) (h₁ c h') hq (S.leg_value c h') (Residual.base_smooth ht) (after hp) (show 0≤R*k+_ by positivity) _
  rw [mul_assoc]; exact HQ S hw ht hr ⟨s/4,b*k,h₂⟩ d hd hD (fun i => h₂ (d i) (hd i)) hc
end Wages
end YM.AnalyticNext.QuarticMatch.Local
