import YM.AnalyticBridge.SELECTED_ORDERED_KERNELS.Confirmed
import YM.RG12.Spins.Muse
/-! Unscaled selected ordered marginal. Adaptation of Heir.Carillon proofs & Lute prices, key tˆl uncollapsed for pp Hessian. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Heir.Payed
open Function Filter Set Lattice Wilson Pressure RG Precision Tree Next Next.SectorChange Next.Fluctuations WardBin.Lies
    Matrix Multi Multi.Vacuum.Jets Multi.Puff ProofPorts.CommonComplexProduction ProofPorts.CommonComplexProduction.Score
    SelectedOrderedKernels SelectedOrderedKernels.Sector FreeResolvent Next.SectorChange.Rows Wisps
open AnalyticBridge.LocalGaussianLaws (gap_positive gapped_iff)
open AnalyticBridge.LocalGaussian (Peak)
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S} {Pt : Teller G} {k : S.Choices} {V : Config G c} {F : Forest S.ratio}
    {P B : BudgetPoint} {ι : Type} [Fintype ι] [DecidableEq ι] {A : Stores S} {o : Site c} {x t s d γ r g M Y Y' K σ : ℝ} {n R : ℕ}
    {J : Config G c → Matrix ι ι ℝ} {a : ι → Site c} {u : ℕ → ℝ}

section sector
variable {Z : ℝ} (hZ : 1 ≤ Z) (hh : ∀ j ≤ n,tender G j P.power (s/2) 1 (u j) ≤ Z) (hs : 0<s) (hγ : 0≤γ)
    (h : SelectedOrderedKernels.Book (native c) a a Prod.fst n s γ u J V) (ht : P.threshold ≤ 2*t) (hr : ∀ i, separation (a i) o ≤ R)
include hZ hh hs hγ h ht hr
omit [DecidableEq ι] in
lemma fixed_chimes (i j : ι) : Slope n (P.dirBound o) V 1 (t*canopy Z R P.power n) (Normalizer.entry J i j) ∧ ‖Normalizer.entry J i j V‖ ≤ canopy Z R P.power n := by
  have hT := P.threshold_pos; have ht₀ : 0<t := by linarith
  let L := TestD.evaluate i j
  have hc : ContDiffAt ℝ n ((fun W => J W i j) ∘ increment V) 0 := L.contDiff.contDiffAt.comp (f:=J ∘ increment V) 0 h.smooth
  have he : Multi.Puff.Crest n (Normalizer.entry J i j) V := crest_cast.mpr (Multi.Puff.into _ _ hc)
  have hK := zero_le_one.trans (canopy_one hZ R P.power n)
  have hf (l : List (Directions G c)) (hl : l.length ≤ n) (hv : ∀ B ∈ l,P.dirBound o B) :
      ‖leftDerivs (Normalizer.entry J i j) l V‖ ≤ tender G l.length P.power (s/2) t (u l.length)* ((1+(R:ℝ))^P.power)^l.length := by
    have hh : Normalizer.entry J i j=Complex.ofRealCLM ∘ (fun W => J W i j) := rfl
    have he := (h.entries l hl ht hs hv).1 i
    have hcc := tender_nn (G:=G) (j:=l.length) P.power (half_pos hs) ht₀.le (h.nonneg _ hl)
    have hx := Finset.single_le_sum (s:=Finset.univ) (a:=j) (f:=fun j => Wisps.rate γ (separation (a i) (a j)) * |leftDerivs (fun V => J V i j) l V|) (fun j _=>by have := rate_pos γ (separation (a i) (a j)); positivity) (Finset.mem_univ _)
    rw [hh, Push.Local.left_linear Complex.ofRealCLM l hc hl]; change ‖((leftDerivs (fun W => J W i j) l V:ℝ):ℂ)‖ ≤ _
    rw [Complex.norm_real]; refine (le_mul_of_one_le_left (norm_nonneg _) (Real.one_le_exp (by positivity))).trans (hx.trans (he.trans ?_))
    unfold Mark.hill; change _ * ((1+(separation (a i) o:ℝ))^P.power)^l.length ≤ _; gcongr; exact hr i
  refine ⟨⟨he,zero_le_one,mul_nonneg ht₀.le hK,fun l hl hv hL => ?_⟩,?_⟩
  · refine (hf l hv hL).trans ?_
    let d := tender G l.length P.power (s/2) 1 (u l.length)
    rw [show tender G l.length P.power (s/2) t (u l.length)=t*d by unfold d tender; simp [hl]; ring,one_pow,mul_one]
    have he := mul_le_mul (hh l.length hv) (pow_le_pow_right₀ (one_le_pow₀ (by simp)) hv : ((1+(R:ℝ))^P.power)^l.length ≤ _) (by positivity) (zero_le_one.trans hZ)
    unfold canopy; rw [mul_assoc]; exact mul_le_mul_of_nonneg_left he ht₀.le
  have h0 := hf [] (Nat.zero_le _) (fun _ hj => (List.not_mem_nil hj).elim)
  simp only [List.length_nil,leftDerivs,tender,pow_zero,↓reduceIte,mul_one] at h0
  have hh := hh 0 (Nat.zero_le _); simp only [tender,pow_zero,↓reduceIte,mul_one] at hh
  exact (h0.trans hh).trans (le_mul_of_one_le_right (zero_le_one.trans hZ) (one_le_pow₀ (one_le_pow₀ (by simp))))
end sector

lemma ringing (h : MarginalInputs T x A F k V n d M s r Y g Y') (hg : 0<g) (ht : P.threshold=1) (e : ι ↪ In x A F (G:=G)) (hr : ∀ i,separation (front A F (e i)) o ≤ R) :
    let Z := 1+peal G n P.power d s M r Y g Y'
    Carillon (eddy T x A F k e) V n P o (peakCost G n M r Y) Z 1 R := by
  intro Z
  have hc (j) (hj : j ≤ n) := Finset.single_le_sum (s:=Finset.range (n+1)) (a:=j) (f:=fun j => |kernelTax G n j P.power 0 d 1 (covFee G n j M r Y)| + |kernelTax G n j P.power 0 s 1 (invFee G n j M r Y g Y')|) (fun j _ => by positivity) (Finset.mem_range.mpr (by omega))
  simp only [kernelTax,Nat.cast_zero,add_zero,one_pow,mul_one] at hc
  have hZ : 1≤Z := le_add_of_nonneg_right (by unfold peal; positivity)
  have h' := h.priced.C.part e.injective
  have hI := h.priced.slices e e.injective 0 le_rfl; rw [eddy_is] at hI
  have hv : ContinuousAt (eddy T x A F k e) V := crest_tr (Puff.into n _ h'.smooth)
  have hz (V : Config G c) : (eddy T x A F k e V).IsSymm := (show (covariance T x A F k V).IsSymm from by
    unfold SelectedOrderedKernels.Sector.covariance fog Schur.clouded Matrix.IsSymm; rw [transpose_smul,transpose_add,transpose_transpose,add_comm]).submatrix _
  have he := h.ops e e.injective |>.1
  have hp := h'.zeroth; unfold eddy
  have hd := narrow_pos n h.priced.d_pos; have hs := narrow_pos n h.priced.δ_pos;
  refine ⟨?_, (Peak.from_rows (SelectedOrderedKernels.Sector.got_schur hp) (by have := h.priced.d_pos; positivity)).mono ?_,fun i j => ?_,fun i j => ?_,fun i j => ?_⟩
  · filter_upwards [hv.eventually (AnalyticBridge.RelativeLogdet.Differential.holds (A:=id) continuousAt_id he (g/2) (half_lt_self hg) (native c) (front A F ∘ e))] with v hp
    exact gap_positive (hz _) hp (half_pos hg)
  · unfold peakCost covFee; exact (le_abs_self _).trans (le_add_of_nonneg_left zero_le_one)
  all_goals first | refine (fixed_chimes hZ ?_ hd (by have := h.priced.d_pos; positivity) h' (show P.threshold≤2*(1:ℝ) by rw [ht]; norm_num) hr i j).1 | refine (fixed_chimes hZ ?_ hs (by have := h.priced.δ_pos; positivity) hI (show P.threshold≤2*(1:ℝ) by rw [ht]; norm_num) hr i j).1 | refine (fixed_chimes hZ ?_ hs (by have := h.priced.δ_pos; positivity) hI (show P.threshold≤2*(1:ℝ) by rw [ht]; norm_num) hr i j).2
  all_goals intro j hj; have HH := hc j hj; unfold Z peal; simp only [kernelTax,Nat.cast_zero, add_zero, one_pow,mul_one]; first | exact (le_abs_self _).trans ((le_add_of_nonneg_right (abs_nonneg _)).trans (HH.trans (le_add_of_nonneg_left zero_le_one))) | exact (le_abs_self _).trans ((le_add_of_nonneg_left (abs_nonneg _)).trans (HH.trans (le_add_of_nonneg_left zero_le_one)))


open AnalyticBridge.LocalGaussian.Moments
protected def fresh (P:BudgetPoint):BudgetPoint:={P with threshold:=1,threshold_pos:=zero_lt_one,threshold_le:=le_rfl}
lemma heard {P:BudgetPoint}{R M:ℝ}{U:Config G c}{f:Config G c→ℂ} (h:Band n ((Payed.fresh P).dirBound o) U R M f): Band n (P.dirBound o) U (P.threshold*R) M f:=by
    have ht:=P.threshold_pos
    refine ⟨h.readable,mul_nonneg ht.le h.sane,h.nonneg, fun l hl hL=>?_⟩
    let Q:=l.map (fun A=>P.threshold⁻¹ • A)
    have hq:Q.length=l.length:=List.length_map _
    have he(j)(hh:j∈Q):(Payed.fresh P).dirBound o j:=by
       obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hh
       intro t; change ‖P.threshold⁻¹ • i t‖ ≤ _; rw [norm_smul_of_nonneg (inv_pos.mpr ht).le]
       apply (mul_le_mul_of_nonneg_left (hL _ hi t) (inv_pos.mpr ht).le).trans_eq; rw [inv_mul_cancel_left₀ ht.ne']; simp [Payed.fresh]
    rw [show leftDerivs f l U=P.threshold^Q.length • leftDerivs f Q U from (by rw [← Push.RelayDifference.left_dilate]; simp [Q,ht.ne',Function.comp_def]),norm_smul, Real.norm_of_nonneg (pow_nonneg ht.le _),mul_pow]
    apply (mul_le_mul_of_nonneg_left (h.caps _ (hq.trans_le hl) he) (by positivity)).trans_eq; rw [hq]; ring
-- table Repriced.Plug eddy with amended inputs from Grain using margin identity.
variable {I:Type}[Fintype I][DecidableEq I]{Y Z:ℝ}{J: Config G c → Matrix (I × G.ColorIndex) (I × G.ColorIndex) ℝ}
lemma price (h:Carillon J (1:Config G c) n (Payed.fresh P) o K Z 1 R)(hZ:1≤Z) (z:Prices G I):
    let C:= canopy Z R P.power n; let W:= (n:ℝ)*2*(1+(Fintype.card (I×G.ColorIndex):ℝ)^2*(C+1)*C)
    Band n (P.dirBound o) (1:Config G c) (P.threshold*W*powers z^2) 1 (fun V=>(Carillon.vary (1:Config G c) J z V:ℂ)):=by
   intro H F
   refine ProofPorts.CommonComplexProduction.band_rise (heard (h.sing zero_le_one le_rfl hZ z)) le_rfl ?_
   have hx:=P.threshold_pos; rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ hx.le
   let d:=Fintype.card (I×G.ColorIndex); unfold Carillon.speed; rw [one_mul]; unfold F H; rw [mul_assoc (↑n:ℝ) 2 ..,mul_assoc (↑n:ℝ)]; rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ (by positivity)
   have he:= Lute.tape_control z; have hh: 1≤ powers z:= grows z
   change (1+((d:ℝ)^2*(H+‖z‖^2)*H))*_≤ 2*(1+(d:ℝ)^2*(H+1)*H)*powers z^2
   have hH:1≤ H :=canopy_one hZ ..; rw [mul_comm _ (2:ℝ)]; rw [mul_assoc 2 (1+_) _]; gcongr 2*?_; rw [add_mul,one_mul]; apply add_le_add (one_le_pow₀ hh)
   calc
    _ ≤ (d:ℝ)^2*((H+1)*powers z^2)*H := by gcongr ?_*?_ * _; rw [add_mul,one_mul]; exact add_le_add (le_mul_of_one_le_right (zero_le_one.trans hH) (one_le_pow₀ hh)) (pow_le_pow_left₀ (norm_nonneg _) (he.1.trans he.2) _)
    _ = _:=by ring
end YM.PhysicalNext.JointLoad.Heir.Payed
