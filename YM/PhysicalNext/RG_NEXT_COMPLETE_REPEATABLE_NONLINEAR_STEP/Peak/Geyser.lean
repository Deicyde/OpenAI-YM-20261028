import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Peak.Rays
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Peak.Supple
/-!
 # Peak.Data. price conditioned on Glider.We can choose Glider and Collar before PPE.Cell capacities (for actual F' null inquiries only need before L). -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Peak
open Function Filter Set Lattice Wilson Pressure Precision RG Tree Next Next.SectorChange Next.Fluctuations Next.Foundations
    Exterior Bloch Bid Push.SectorMeasure MultiNext.SignedSource MultiNext.SignedSource.Banjo WardBin.Lies Planned.AtomRegular
open JointLoad.Heir
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
section payments
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S} {k : S.Choices} {V : Config G c} {F : Forest S.ratio}
    {P B : BudgetPoint} {o : Site f} {g : Site c → G.El} {X : Support f}
    {Q C M r x y : ℝ} {j l m n : ℕ} {A : Slab G c l} {w : Directions G f}

variable (hh : glider G T m B.power (2*C) M) (hq : Canvas P (S.ratio.parent o) (reach x) V g n C)
    (ht : temp x ≤ 2*B.threshold) (hP : P.threshold=temp x) (hB : P.power ≤ B.power) (hC : 1 ≤ C) (hl : l ≤ n)
    (h : ∀ i, P.dirBound (S.ratio.parent o) (A i)) (hu : loom P (reach x) C ≤ 1)
def trancheD (m : ℕ) (L : Side) (n : ℕ) (Q v w t : ℝ) := ((clinicFee n Q*v^2+w)/t)*(L.val:ℝ)^(m+1)
lemma trancheD_nn (m : ℕ) (L : Side) (n : ℕ) {Q v w t : ℝ} (hQ : 0≤Q) (hw : 0≤w) (ht : 0≤t) : 0≤trancheD m L n Q v w t := by unfold trancheD; positivity [le_trans (mul_nonneg (show (0:ℝ) ≤ 2 by norm_num) hQ) (clinicFee_le n hQ)]

variable (hT : Act T F x k n r Q) (hQ : 1≤Q) (hM : 1 ≤ M) (hn : 2 ≤ n) (hr : loom P (reach x) C ≤ r)
    (hw : ‖w‖ ≤ loom P (reach x) C) (hw' : ‖w‖ ≤ y)
include hq ht hP hB hC hl h hu hh hT hQ hM hn hr hw hw'

lemma first_promise (hj : j ≤ n) (v : Fin j → Panels l) (hv : ∀ i, ‖v i‖ ≤ 1) :
    let a := enters V (S.ratio.parent o) (reach x) g A w
    let K := M+trancheD m S.patch.L n Q (loom P (reach x) C) y B.threshold
    Promise m K ((S.patch.L.val:ℝ)⁻¹) B o X (iteratedFDeriv ℝ j (display T F x k true ∘ a) 0 v) := by
  intro a K; let L := (S.patch.L.val:ℝ); let s := loom P (reach x) C; let Z := trancheD m S.patch.L n Q s y B.threshold
  have h0 : 0≤y := (norm_nonneg _).trans hw'; have hZ : 0≤Z := trancheD_nn m _ _ (by positivity) h0 B.threshold_pos.le
  let z' := launch V (S.ratio.parent o) (reach x) g A
  let z := iteratedFDeriv ℝ j z' 0 v
  have hp := hh B X o z rfl (launch_cost hq ht hP hB hC hl h hu hj v hv)
  refine Quartet.sweet (M:=K) (Y:=Z) (by positivity) hZ le_rfl (by positivity) hp ⟨by positivity,fun i => ?_⟩
  have hfee := (timesEnter hq hT hP hn h hC hl hQ hu hr hw true).2 j hj v hv
  rw [spine_self,one_pow,mul_one] at hfee
  let b := iteratedFDeriv ℝ j (display T F x k true ∘ a) 0 v
  let a₀ := mainStroke T F true (iteratedFDeriv ℝ j a 0 v)
  have h : ‖a₀-route T z‖ ≤ y := by
    by_cases he : j=0
    · subst j; unfold a₀ z; rw [iteratedFDeriv_zero_apply,iteratedFDeriv_zero_apply]; change ‖(route T (z' 0)+w)-route T (z' 0)‖ ≤ _; simpa only [add_sub_cancel_left] using hw'
    unfold a₀ a; rw [enter_pos hq hj (by omega) v]; change ‖(route T z+0)-route T z‖ ≤ _; simpa
  have h := ((norm_sub_le_norm_sub_add_norm_sub b a₀ (route T z)).trans (add_le_add hfee h))
  have hL : L ≠ 0 := by unfold L; positivity
  change ‖(b-route T z) i‖ ≤ Z*L⁻¹^(m+1)* _
  apply ((norm_le_pi_norm ..).trans h).trans
  have he := B.threshold_pos.ne'
  calc
    _ = Z * L⁻¹^(m+1) * B.threshold := by rw [inv_pow]; unfold Z L trancheD s; field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left (le_mul_of_one_le_right B.threshold_pos.le (spine_one B.power i.1 o)) (by positivity)
end payments

section notice
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S} {Pt : Teller G} {k : S.Choices} {V : Config G c} {F : Forest S.ratio}
    {P B : BudgetPoint} {o : Site f} {g : Site c → G.El} {X : Support f} {Y : Support c} {Q C M r t x τ : ℝ} {I : Type}
    {A : Stores S} {n m l : ℕ} {D : Slab G c l} {q : Chi} {d u : ℝ} {f' : Config G f → ℝ}
variable (Q' : Rights G n) (a : Museum F x A X Y I) [Fintype I] (b : JointLoad.Folio.Bulletin x Pt T) (hr : Weft G S.patch.L P B Q C x)
    (hT : Act T F x k n r Q) (hq : Canvas P (S.ratio.parent o) (reach x) V g n C) (hC : 1 ≤ C) (hh : glider G T m B.power (2*C) M)
    (hQ : 1 ≤ Q) (hM : 1 ≤ M) (hn : 2≤n) (hk:m+1 ≤ n) (hK : n ≤ B.order) (hF : 100*(1+radiusB x) ≤ c.val)
    (hP : P.threshold=temp x) (ht : temp x ≤ 2*B.threshold) (hpow : P.power ≤ B.power)
    (h' : loom P (reach x) C < r) (hy : Q*loom P (reach x) C ≤ 1)
    (hS : Short S B X) (he : B.Regular X f') (h₀ : o∈X) (hf₀:Peak.lit o X f' m) (hE : B.supBounds o X f' τ)
    (h : ∀ i, P.dirBound (S.ratio.parent o) (D i)) (hl : l ≤ n)
    (U : Config G f) (w : Prices G I) (hU : Healthy B.threshold X (a.received k T q d u V U w))
    (hu : 0 ≤ u) (hw : u*‖tape w‖ ≤ loom P (reach x) C)

def tinyR (m:ℕ)(Q' : Rights G n) := patterns n * ((n+1:ℝ)*((m+1:ℝ)^n)*Q'.fee)
include b hr hT hq hC hh hQ hM hn hk hK hF hP ht hpow h' hy hS he h₀ hf₀ hE h hl hu hw hU

lemma airbud : let f₀ (V : Config G c) := f' (a.received k T q d u V U w)
    let K := M+trancheD m S.patch.L n Q (loom P (reach x) C) (u*‖tape w‖) B.threshold
    ContDiffAt ℝ n (f₀ ∘ journey V l D) 0 ∧ ∀ j ≤ n, ‖iteratedFDeriv ℝ j (f₀ ∘ journey V l D) 0‖ ≤ tinyR m Q' * K^n * ((S.patch.L.val:ℝ)⁻¹)^(m+1) * τ := by
  intro f₀ K
  have hw' := (a.extra_size g u hu w).trans hw
  have hK' : 1 ≤ K := le_trans hM (le_add_of_nonneg_right (trancheD_nn m _ _ (by positivity) (mul_nonneg hu (norm_nonneg _)) B.threshold_pos.le))
  let L := enters V (S.ratio.parent o) (reach x) g D (a.extra g u w)
  let z := display T F x k true ∘ L; let fSide := f; let f := f' ∘ increment (1:Config G _)
  obtain ⟨he',hz⟩ := plucked a b hr hT hS hq h₀ hC h' U w hw' D hQ (by omega) hy hU
  have hf : ContDiffAt ℝ n f (z 0) := (along he (by simpa only [one_smul,z,Function.comp_apply,L] using hz 1 (by simp))).of_le (Nat.cast_le.mpr hK)
  have hs := (depicted (q:=q) (d:=d) a b hr hT hS hq h₀ hC h' U w hw' D)
  have hs : f ∘ z =ᶠ[𝓝 0] f₀ ∘ journey V l D := by
    filter_upwards [hs] with i hi; exact (he.sites _ _ (agrees_mono hi (fun _ hv => Finset.mem_union_left _ hv))).trans ((he.symmetry _ _).trans (he.symmetry ..))
  have hE' : loom P (reach x) C ≤ 1 := le_trans (le_mul_of_one_le_left ((mul_nonneg hu (norm_nonneg _)).trans hw) hQ) hy
  have hg := (timesEnter hq hT hP (by omega) h hC hl hQ hE' h'.le hw' true).1
  have h (j) (hj : j ≤ n) := Peak.first_promise (X:=X) hh hq ht hP hpow hC hl h hE' hT hQ hM (by omega) h'.le hw' (a.extra_size g u hu w) hj
  refine ⟨(hf.comp (f:=z) _ hg).congr_of_eventuallyEq hs.symm,fun j hj => ?_⟩
  have h0 : Promise m K ((S.patch.L.val:ℝ)⁻¹) B o X (z 0) := by
    simpa only [iteratedFDeriv_zero_apply] using h 0 (Nat.zero_le _) 0 (by simp)
  have hF' : 4 ≤ fSide.val := S.sizes ▸ Nat.le_trans (show 4 ≤ c.val by omega) (Nat.le_mul_of_pos_right _ S.patch.L.property)
  rw [← (hs.iteratedFDeriv (𝕜:=ℝ) j).eq_of_nhds]; have hlarge := Q'.large; have hτ := hE.1
  refine (slots_bound (U:=z) hg hf hj (C:=(n+1:ℝ)*(((m+1:ℝ)*K)^n*((S.patch.L.val:ℝ)⁻¹)^(m+1))*Q'.fee*τ) (by positivity) (fun p v hv => facet he hf₀ hE (by positivity)
    (inv_le_one_of_one_le₀ (Nat.one_le_cast.mpr S.patch.L.property)) hK' Q' hK _ h0 he' hz hk (p.length_le.trans hj) _ (fun i => h _ ((p.partSize_le i).trans hj) _ (fun k => hv _)))).trans_eq ?_
  unfold tinyR; rw [mul_pow (m+1:ℝ)]; ring
end notice
end YM.PhysicalNext.Repeat.Peak
