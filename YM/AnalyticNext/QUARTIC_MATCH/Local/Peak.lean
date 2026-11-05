import YM.AnalyticNext.QUARTIC_MATCH.Local.Rest
import YM.Work.B14

/-!
# Peak invoice. Same Wilson law and normalization

Charge even if the scribe at upstream reconstruction supplies a nontrivial
base. All unmasked paths at true width and residual quartic AFTER cubic path
paid at its achieved width when necessary. Not claiming this choice suffices
as thermal kinetic data.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch.Local
open Filter Function Lattice Laurent Matrix Hessian Analysis RG Precision Exterior Bid Wilson Branch Bloch
open Progress.StationaryScenes Work.F03 YM.Next.Free Work.F08 Pre.Centered Tree
open Joint Estimate Estimate.Purse Estimate.Logfee Estimate.Depot BoxChain Premium Evoke Budget Analyzers Mail Wages
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace
attribute [local instance] Gauge.frobInner
namespace Peak
section universal
variable {G : Gauge} {c : Side}
open Residual
lemma sameSign (i : ℕ) {X Y : Dir G c →ℝ} (hx : ContDiffAt ℝ ω X 0) (hy : ContDiffAt ℝ ω Y 0)
    (f : Dir G c→L[ℝ] Dir G c) {a : Fin i→ Dir G c} (he : X ∘ f=X) (hh : Y ∘ f=Y) :
    Tensor.coeff (X-Y) i 0 (fun i => f (a i)) = Tensor.coeff (X-Y) i 0 a := by
  unfold Tensor.coeff
  have hT : ContDiffAt ℝ i (X-Y) 0 := (hx.sub hy).of_le le_top
  have hf := Next.Foundations.jets_linear f hT; rw [show (X-Y) ∘ f=X-Y from funext fun j => congr_arg₂ (·-·) (congr_fun he j) (congr_fun hh j)] at hf
  exact congr_arg ((Nat.factorial i:ℝ)⁻¹ • ·) (DFunLike.congr_fun hf.symm a)
lemma fresh (G : Gauge) (c : Side) : ContDiffAt ℝ ω (wilsonAt (c:=c) (G:=G)) 0 := by
  unfold wilsonAt Wilson.energy
  exact ContDiffAt.sum fun i _ => price_smooth (A:=fun x => faceValue (represent x) i) (Push.writes ..)
lemma weight {p : Clip} {σ C Λ : ℝ} {W : PathData G} (i : ℕ) (h : W.Bounds p σ C Λ) :
    Law 0 (fun c => Tensor.coeff (wilsonAt-baseAt p W (c:=c)) i 0) := by
  constructor
  · intro c _ y v; exact sameSign i (fresh ..) (Residual.base_smooth h) (colors y) (by
      funext x; simp only [Function.comp_apply, wilsonAt,rep_colors, Wilson.energy_gauge]) (Residual.base_colors h y)
  · intro c _ y v; exact sameSign i (fresh ..) (Residual.base_smooth h) (shifts 1 y) (by
      funext x; simp only [Function.comp_apply,wilsonAt,rep_shifts,Wilson.energy_pull]) (Residual.base_orient ..)
  intro c d _ _ h' v
  let L := Sheets.reuses h' (k:=1) (G:=G)
  let P c := wilsonAt-baseAt (c:=c) p W
  have hP c : ContDiffAt ℝ i (P c) 0 := ((fresh G c).sub (base_smooth h)).of_le le_top
  have he := Next.Foundations.jets_linear L (hP d)
  rw [show (P d ∘ L)=_ from Sheets.peak_lift h' p W, iteratedFDeriv_const_smul_apply (hP c)] at he
  have hv : iteratedFDeriv ℝ i (P d) 0 (fun i => L (v i))=(Sheets.mult h':ℝ) • iteratedFDeriv ℝ i (P c) 0 v := DFunLike.congr_fun he.symm v
  unfold Tensor.coeff
  simp only [_root_.smul_apply,smul_eq_mul]; change (i.factorial:ℝ)⁻¹ * iteratedFDeriv ℝ i (P d) 0 (fun i => L (v i)) = _
  rw [hv,smul_eq_mul]; unfold P; ring
end universal
open Plaque Village
lemma seed (G : Gauge) (u : ℝ) (hp : 0<u) (i : ℕ) (hi : i ≤ 4) (w : Fin i) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ (c : Side), Alive w (Residual.wilsonAt (c:=c) (G:=G)) (rate u) C := by
  let b := boom u
  let a := allotted G b i
  let k := Evoke.factor b
  let g := (2*G.colorScale^2)⁻¹
  have hk : 0 ≤ k := zero_le_one.trans (factor_ge (booms hp).le)
  have hg := G.colorScale_pos
  have hh : 0 ≤ g := inv_nonneg.mpr (by positivity); have ha : 0 ≤ a := (allotted_pos ..).le
  let K := g*((2:ℝ)^i*(a*a))
  have hK : 0 ≤ K := mul_nonneg hh (by positivity)
  refine ⟨overall u * (Fintype.card PlaqAxes*K*k^i),mul_nonneg (zero_le_one.trans (Premium.cover_ge u)) (by positivity),?_⟩
  intro c x z
  let X j := (x j).1; let d j := sparse (x j) (z j); let D j := k*‖z j‖; have hD j : 0 ≤ D j := mul_nonneg hk (norm_nonneg _)
  let Q := Wages.account 1 none X (fun _ => b) D hD; let U := (Finset.univ:Finset (Fin i));
  have he i := coarse_enough Q (booms hp).le i (by simp [Purse.tagged,Q,Wages.account]) (x i) (z i) rfl (fun j => by
    change Green.wt (boom u/(↑(1:ℕ):ℝ)) j _ = _; simp only [Nat.cast_one,div_one,X])
  let V p (j : Site c) (a : Dir G c) := G.price (faceValue (represent a) (j,p))
  let p y (a : Dir G c) := ∑ j : PlaqAxes,V j y a
  have hT := travels (w:=none) X (fun _ => b) D hD 1 (fun _ => (abs_of_pos (booms hp)).le)
  have hV (u : PlaqAxes) (j : Site c) : ContDiffAt ℝ ω (V u j) 0 := price_smooth (A:=fun x => faceValue (represent x) (j,u)) (Push.writes ..)
  have hx₁ : Linkbill 1 Q d := by intro _ _; simpa only [d,PNat.val_ofNat, Nat.cast_one,inv_one] using (he _).1 _
  have hx₂ : BendBill 1 Q d := by intro _ _; simpa only [d,PNat.val_ofNat,Nat.cast_one,one_pow,inv_one] using (he _).2 _
  have ht : U.card ≤ i := by simp [U]
  let r := span (rate u) (X w) X
  have he q : Q.Jets U d (V q) 0 K := by
    let f := plasty q (G:=G) (n:=c)
    have ht' j := (Plaque.order q (G:=G) j).contDiffAt (x:=(0:Dir G c))
    have hh' (T : Finset (Fin i)) (h : T ⊆ U) : Q.Jets T d f 0 a := by
      simpa only [PNat.val_ofNat, Nat.cast_one,one_pow, div_one] using collectBudget hx₁ hT (booms hp).le T i ((Finset.card_le_card h).trans ht) hx₂ q
    let Φ := innerSL ℝ (E:=G.Mat)
    rw [show V q=fun i x => g • Φ (f i x) (f i x) from funext fun i => funext fun x => (exp_price G _).trans (show g*‖f i x‖^2 = g*inner ℝ (f i x) (f i x) by rw [real_inner_self_eq_norm_sq])]
    have hK := Jets.rate (Jets.priced Φ (fun a b => abs_real_inner_le_norm a b) ht' ht' hh' hh' i ht) g
      (fun i => (Φ.contDiff.contDiffAt.comp _ (ht' i)).clm_apply (ht' i)); rwa [abs_of_nonneg hh] at hK
  have hh := Jets.allotted Finset.univ V (fun i _ => hV i) (fun i _ => he i)
  have hf : Stamp Q U 1 u r (X w) := by simpa only [PNat.val_ofNat,Nat.cast_one,div_one] using journey hp Q w X 1 hi (fun _ _ => rfl)
  have hk := Premium.tariff (l:=1) hh (by norm_num [Q,Wages.account]) hp (by exact (span_pos (rate u) (X w) X).le) _ hf
  rw [← univEstimate d (Residual.wilsonAt (G:=G) (c:=c)) _ (fresh ..), show Residual.wilsonAt (G:=G) (c:=c)=fun a => ∑ x,p x a from
    funext fun a => Fintype.sum_prod_type (fun j => G.price (faceValue (represent a) j)), sum_bill Finset.univ _ _ p]
  · apply hk.trans_eq; unfold Q D Wages.account Purse.target U; simp [Finset.prod_mul_distrib]; ring
  exact fun i _ => ContDiffAt.sum fun j _ => hV j _
section matching
open Residual
variable (G : Gauge)
lemma budget_seed (p : ℕ) (i : Fin p) (hi : p≤4) (u D R3 R4 : ℝ) (he : 0<u) :
    ∃ R : ℝ,0 ≤ R ∧ ∀ (c : Side) (q : Clip) (W : PathData G) (σ C τ Λ : ℝ) (h : W.Bounds q τ C Λ),
      Rotate.Led W 1 p (boom u) σ D R3 R4 → Spatial ((Peak.weight p h).raw c) (rate u/4) R := by
  obtain ⟨R,hR,H⟩ := seed G u he p hi i
  obtain ⟨K,hK,h⟩ := Wages.budget G (w:=i) hi he D
  let x := max 1 (assistance 1 R3 R4)
  have hx : 0 ≤ x := zero_le_one.trans (le_max_left ..)
  refine ⟨(p.factorial:ℝ)⁻¹*(R+K*x),by positivity,?_⟩
  intro c q W σ C τ Λ hk hh
  have Hx := h (c:=c) q W hk hh
  rw [(Peak.weight p hk).raw_buys (Nat.zero_le _)]
  exact (H c).gives (Hx.earns (mul_le_mul_of_nonneg_left (le_max_right ..) hK)) (fresh ..) (base_smooth hk)
    (after he) (by positivity) _

lemma top_cost (p : ℕ) [NeZero p] (i : Fin (p+1)) (hp : 2 ≤ p) (hi : p+1 ≤ 4)
    (u D R3 R4 : ℝ) (he : 0<u) (P : Printed p) : ∃ σ C : ℝ,0<σ ∧ 0≤C ∧
      ∀ (q : Clip) (W : PathData G) (τ a η Λ : ℝ) (_h : W.Bounds q η a Λ),Rotate.Led W 1 (p+1) (boom u) τ D R3 R4 →
        ∀ (d : ℕ → Side), Tendsto (fun i => (d i).val) atTop atTop →
        (∀ n k,k<p+1 → iteratedFDeriv ℝ k (wilsonAt (G:=G) (c:=d n)) 0=iteratedFDeriv ℝ k (baseAt q W) 0) →
          ∃ A : rootArray G p, SumBudget (fun i => (letters P A i).budget σ) C ∧
            ∀ n l,l ≤ p+1 → SameJet l wilsonAt (baseAt q W (c:=d n) + impact (letters P A)) := by
  obtain ⟨R,hR,H⟩ := budget_seed G (p+1) i hi u D R3 R4 he
  obtain ⟨σ,C,ha,hc,L⟩ := Mail.writes G p P hp (rate u/4) (div_pos (after he) (by norm_num))
  refine ⟨σ,C*R,ha,mul_nonneg hc hR,?_⟩
  intro q W τ a η Λ h Hh d ht hl
  have hv c := H c _ _ _ _ _ _ h Hh
  obtain ⟨A,hA,hk⟩ := L 0 _ (Peak.weight (p+1) h) ⟨rate u/4,R,fun c _ => hv c⟩ d (fun _ => Nat.zero_le _) ht (fun n =>
    Residual.closed_peak _ h (hl n)) R fun i => hv (d i)
  exact ⟨A,hA,fun i => banks_add (base_smooth h) (fresh ..) (hl i) (letters P A) hA ha (hk i).1 (hk i).2⟩
end matching

end Peak
end YM.AnalyticNext.QuarticMatch.Local
