import YM.Planned.PRIMARY_INTEGRAL_295.Junction
import YM.Planned.PRIMARY_INTEGRAL_295.Postcards
import YM.Planned.PRIMARY_INTEGRAL_295.Radical

/-!
# Primary term temperatures and readout budgets at chosen d

`Entry` is the remaining stationary/sector part for the principal regular
term's owner ONLY. Other Raw-format terms must also pay. `yield_price`
specializes all finite calls, obtaining BEFORE-L price, then the
necessary ENTIRE envelope of true regular supBounds plus primary projection
error. k,r the genuine norm parameters, paid b+t constants for this
specific order. Budget convention local-producer must buy the corresponding
δ e.g. after L.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Radical
open Function Filter Set Metric MeasureTheory
open Labels Lattice Source Source.Drops Tones Oval Emits Junction Postcards WardBin.Lies
open Place Carrier Precision Bloch Next.Free RG
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
open Wilson
open Push.Local (Probe runProbe)

variable {G : Gauge} {d j t : ℕ} {F : Labels.Frame G d} {n L : Side}

noncomputable def probes (F : Labels.Frame G d) := (Push.Local.probe_budget F).choose
private def headPrice (F : Labels.Frame G d) := (Push.Local.probe_budget F).choose_spec.choose

/-- The analytic part that has not been supplied. Calls at every healthy
V, all incl ordered Lie increments, B true budget. Second part calls with
testLinks (actual paths; no guessing coefficient scaling near winding).
Configuration n is actual P-determined side as called, families on full
configs. `Gate` covers all primary atoms of the frame. -/
structure Entry (T : SectionData F) (A : Hol G) (Y : F.Index→Config G n→ℂ) (L : Side) (K : Lines L)
    (o : Site n) (B : BudgetPoint) (X : Support n) (f R M δ : ℝ) : Prop where
  station : ∀ U : Config G n, Healthy B.threshold X U → ∀ b ≤ B.order, ∀ V : Slab G n b, (∀ i, B.dirBound o (V i)) →
    ∃ (g:Window G.Color) (v: Fin b→Window G.Color), Guard g v B.power M ∧ Gate T L Y (journey U b V) (model K T.stencil g v) f b R δ
  charge : ∀ p∈probes F, Gate T L Y (A.testLinks d o (B.threshold • p.1))
      (forecast T.stencil p K B.threshold f) f p.2.val R δ

section
variable (T : SectionData F) (A : Hol G) (h : T.Sound A) (b : Bid.pop T) (i : F.Index)
variable (k : ℝ) (hk : 0 < k) (hj : 4≤j) (ht : 4 ≤ t) (r : ℕ) (hr : d ≤ r) (hd : d≤ j-2) (R M : ℝ) (hp : 0 ≤ M)

private lemma cart_filled (n : ℕ) : ‖(cart : Fin n → Panels n)‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr; intro i
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr; intro j; by_cases he : j=i <;> simp [cart,he]

include h b hk hj ht hr hd i hp in
private lemma perVisit (v : ℕ) : ∃ C:ℝ, 0≤C ∧ ∀ (P : Flight j t) {n : Side} (B : BudgetPoint)
    (Y : F.Index→Config G n→ℂ) o X (f δ : ℝ), i≠0 → B.power=r → 0≤δ → B.Regular X (Y i) → f∈Ioc (0:ℝ) 1 →
    Entry T A Y P.L (linesOf P k) o B X f R M δ → ∀ U, Healthy B.threshold X U → ∀ (w:Slab G n v),
      v ≤ B.order → (∀ i, B.dirBound o (w i)) → ‖leftDerivs (Y i) (List.ofFn w) U‖ ≤ C*(P.L.val:ℝ)^d*
          (unitStep P.L^((F.grades i).1) + δ) := by
  obtain ⟨Z,hZ,H⟩:=shadeJourney A T h b i M hp r v hr hd k hk hj ht
  obtain ⟨u,hu,u'⟩:=predictor (G:=G) T.stencil d v r hr hd k hk hj ht
  obtain ⟨D,hD,h'⟩:=pouch T b i v (u*M) R
  refine ⟨Z+D,add_nonneg hZ hD,fun P n nB Y o X f δ hi hN hδ hg hf hE U hU w hw hw' => ?_⟩
  obtain ⟨g,a,hg',hA⟩:=hE.station U hU v hw w hw'
  rw [hN] at hg'
  let Y':=Y i ∘ journey U v w; let Q:=model (linesOf P k) T.stencil g a
  have he : Oval.Envelope 0 v Q (u*M) := ⟨by positivity,fun b _=> u' P M g a hg' b⟩
  have hv : ContDiffAt ℝ v Q 0 := (model_smooth ..).contDiffAt.of_le le_top
  have hh := h' Y (journey U v w) Q f δ hi hδ hA hf hv he
  let A':=tint T i f ∘ Q
  let c:=(P.L.val:ℝ)^d; have hc:0≤c:=by unfold c; positivity
  let t:=unitStep P.L^((F.grades i).1); have ht' := unitStep_pos P.L
  have hF : ‖iteratedFDeriv ℝ v Y' 0 cart - iteratedFDeriv ℝ v (c • A') 0 cart‖ ≤ D*c*δ := by
    let F:=iteratedFDeriv ℝ v Y' 0 - iteratedFDeriv ℝ v (c • A') 0
    apply (F.unit_le_opNorm (cart_filled v)).trans; exact hh.2 v le_rfl
  have hy := (show Germ nB.order (Y i) U from hg.smooth U hU).prod hw
  rw [hy.ordered]; change ‖iteratedFDeriv ℝ v Y' 0 cart‖ ≤ _
  have hu' : ContDiffAt ℝ v A' 0 := ((coat_smooth (column_smooth T i) ..).contDiffAt.of_le le_top).comp _ hv
  have hI : ‖iteratedFDeriv ℝ v (c • A') 0 cart‖≤c*(Z*t) := by
    rw [iteratedFDeriv_const_smul_apply hu',smul_apply,norm_smul,Real.norm_of_nonneg hc]; exact mul_le_mul_of_nonneg_left (H _ _ _ hg' _ hf) hc
  apply (norm_le_norm_sub_add _ (iteratedFDeriv ℝ v (c • A') 0 cart)).trans
  apply (add_le_add hF hI).trans
  change _ ≤ (Z+D)*c*(t+δ)
  have hl : 0≤t:=by unfold t; positivity
  nlinarith only [mul_nonneg (mul_nonneg hZ hc) hδ, mul_nonneg (mul_nonneg hD hc) hl]

include h b hk hj ht hd i in
private lemma perProbe (π : ℝ) (hπ : 1≤π) (p : Probe G d) : ∃ C:ℝ,0 ≤ C ∧ ∀ P : Flight j t, ∀ {n : Side} (B : BudgetPoint)
    (Y : F.Index→Config G n→ℂ) o X (f δ : ℝ) (hB : PPX.Blend π f B.threshold), i≠0 → p∈probes F → 0≤δ → B.Regular X (Y i) →
    Nonwrapping X o → d≤B.order → Entry T A Y P.L (linesOf P k) o B X f R M δ →
      let Z := PPX.Seal.donne T h hk ht b P (hd.trans (Nat.sub_le ..)) hB
      ‖runProbe F p (Push.Local.weighted A F o X B.threshold (Y i) - Z.leads P.L (copy F i))‖ ≤ C*(P.L.val:ℝ)^d*δ := by
  classical
  let N : ℕ:=p.2.val
  choose! a ha H using fun n=>replicate T.stencil p π k hπ hk hj ht n
  let u:=∑ i∈Finset.range (N+1),a i
  have he : ∀ i∈Finset.range (N+1),0≤a i := fun i hi=> ha i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
  have hu:0≤u:=Finset.sum_nonneg he
  obtain ⟨D,hD,h'⟩:=pouch T b i N u R
  refine ⟨D,hD,fun P n B Y o X f δ hB hi hp hδ Hg hX hx HV => ?_⟩
  intro Z; let Q:=forecast T.stencil p (linesOf P k) B.threshold f
  have hQ : Oval.Envelope 0 N Q u := ⟨hu,fun b hb=> (H b hb P _ _ hB).trans (Finset.single_le_sum he (Finset.mem_range.mpr (Nat.lt_succ_of_le hb)))⟩
  have hS : ContDiff ℝ ω Q := forecast_truth _ _ _ _ _ (stored P k hk ht)
  let path:= A.testLinks d o (B.threshold • p.1)
  have hf : f∈Ioc 0 1:=⟨hB.fine,hB.fits⟩
  have hh := h' _ path Q f δ hi hδ (HV.charge p hp) hf (hS.contDiffAt.of_le le_top) hQ
  rw [map_sub, ← Push.Local.sample_eq F A _ _ Hg hx];
  unfold Push.Local.sample; rw [if_pos hX]
  unfold Z; rw [measured T h b P k π B.threshold f hk ht _ hB p i]
  let c:=(P.L.val:ℝ)^d; let V:=tint T i f ∘ Q
  have he : c • iteratedDeriv N V 0=iteratedDeriv N (c • V) 0 := (iteratedDeriv_const_smul
    (show ContDiffAt ℝ N V 0 from ((coat_smooth (column_smooth ..) ..).comp hS).contDiffAt.of_le le_top) _).symm
  change ‖iteratedDeriv N (Y i ∘ path) 0 - c • iteratedDeriv N V 0‖ ≤ _; rw [he]
  let F':=iteratedFDeriv ℝ N (Y i∘path) 0 - iteratedFDeriv ℝ N (c • V) 0
  let v := fun _ : Fin N=> (1:ℝ)
  change ‖F' v‖ ≤ _; apply (F'.unit_le_opNorm _).trans (hh.2 N le_rfl)
  exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i=>show ‖(1:ℝ)‖≤1 by simp
include h b hk hj ht hd hp hr
private lemma perColumn (π : ℝ) (hπ : 1≤π) (N : ℕ) : ∃ C:ℝ,0 ≤ C ∧ ∀ P : Flight j t, ∀ {n : Side} (B : BudgetPoint)
    (Y : F.Index→Config G n→ℂ) o X (f δ : ℝ) (hB : PPX.Blend π f B.threshold), i≠0 → 0≤δ → B.Regular X (Y i) →
    Nonwrapping X o → d≤B.order → B.order=N → B.power=r → Entry T A Y P.L (linesOf P k) o B X f R M δ →
      let Z := PPX.Seal.donne T h hk ht b P (hd.trans (Nat.sub_le ..)) hB
      let u := C*(P.L.val:ℝ)^d
      F.coeffSize (Push.Local.weighted A F o X B.threshold (Y i) - Z.leads P.L (copy F i)) ≤ u*δ ∧
        B.supBounds o X (Y i) (u*(unitStep P.L^((F.grades i).1)+δ)) := by
  classical
  choose a ha H using perProbe T A h b i k hk hj ht hd R M π hπ
  choose z hz Z using perVisit T A h b i k hk hj ht r hr hd R M hp
  let S:=∑ i∈probes F,a i; let Q:=∑ i∈Finset.range (N+1),z i
  let B':=headPrice F;
  obtain ⟨hy,hB⟩ := (Push.Local.probe_budget F).choose_spec.choose_spec
  change 1 ≤ B' at hy
  have he:= show 0≤S from Finset.sum_nonneg fun i _=> ha i
  have hw:= show 0≤Q from Finset.sum_nonneg fun i _=> hz i
  refine ⟨B'*S+Q,by positivity,fun P n B Y o X f δ hF hi hδ hR hn hd ho hp' hE=>?_⟩
  intro V p; let t:=(P.L.val:ℝ)^d; have ht':0≤t:=by unfold t; positivity
  let y:=Push.Local.weighted A F o X B.threshold (Y i) - V.leads P.L (copy F i)
  constructor
  · change F.coeffSize y≤p*δ
    apply (hB y (S*t*δ) (by positivity) _).trans
    · unfold p
      change B'*(S*t*δ) ≤ (B'*S+Q)*t*δ
      nlinarith only [mul_nonneg (mul_nonneg hw ht') hδ]
    intro i' hx
    apply (H i' P B Y o X f δ hF hi hx hδ hR hn hd hE).trans
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun i _=>ha i) hx) ht') hδ
  have hh:=unitStep_pos P.L
  refine ⟨by unfold p; positivity,fun U hU l hl hw' => ?_⟩
  have hv := Z l.length P B Y o X f δ hi hp' hδ hR ⟨hF.fine,hF.fits⟩ hE U hU l.get hl (fun i=> hw' _ (l.get_mem _))
  rw [List.ofFn_get] at hv; apply hv.trans
  apply mul_le_mul_of_nonneg_right _ (by positivity); unfold p
  refine mul_le_mul_of_nonneg_right ?_ ht'
  rw [ho] at hl
  exact (show z l.length ≤ Q from Finset.single_le_sum (fun i _=>hz i) (Finset.mem_range.mpr (Nat.lt_succ_of_le hl))).trans
    (le_add_of_nonneg_left (by positivity))

/-- The deterministic bill finite BEFORE purchasing L. All tests in the
real stencil norm at admitted d kept. `Entry` still has to pay actual L,δ.
-/
theorem yield_price (π : ℝ) (hπ : 1≤π) (N : ℕ) : ∃ C:ℝ,1 ≤ C ∧
    ∀ (P : Flight j t) {n : Side} (B : BudgetPoint) (Y : F.Index→Config G n→ℂ) o X (f δ : ℝ) (hB : PPX.Blend π f B.threshold) (i:F.Index),
    i≠0 → 0≤δ → B.Regular X (Y i) → Nonwrapping X o → d≤B.order → B.order=N → B.power=r → Entry T A Y P.L (linesOf P k) o B X f R M δ →
      let Z := PPX.Seal.donne T h hk ht b P (hd.trans (Nat.sub_le ..)) hB
      let u := C*(P.L.val:ℝ)^d
      F.coeffSize (Push.Local.weighted A F o X B.threshold (Y i) - Z.leads P.L (copy F i)) ≤ u*δ ∧
        B.supBounds o X (Y i) (u*(unitStep P.L^((F.grades i).1)+δ)) := by
  choose C hC H using fun i:F.Index=>perColumn T A h b i k hk hj ht r hr hd R M hp π hπ N
  let z:=∑ i,C i; have he : 0≤z := Finset.sum_nonneg fun i _=>hC i
  refine ⟨1+z,le_add_of_nonneg_right he,fun P n B Y o X f δ hb i hi hδ hR hn hD hN hr hE=>?_⟩
  intro Z u
  obtain ⟨hv,hv'⟩:= H i P B Y o X f δ hb hi hδ hR hn hD hN hr hE
  have hL: C i*(P.L.val:ℝ)^d ≤ u := mul_le_mul_of_nonneg_right ((show C i≤z from
    Finset.single_le_sum (fun i _=>hC i) (Finset.mem_univ i)).trans (le_add_of_nonneg_left zero_le_one)) (by positivity)
  have hu:=unitStep_pos P.L
  exact ⟨hv.trans (mul_le_mul_of_nonneg_right hL hδ),Push.Local.bound_weaken hv' (mul_le_mul_of_nonneg_right hL (by positivity))⟩
end
end YM.Planned.PrimaryIntegral295.Radical
