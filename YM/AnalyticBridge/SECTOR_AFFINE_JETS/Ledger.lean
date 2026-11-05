import YM.AnalyticBridge.SECTOR_AFFINE_JETS.GuardLog

/-!
# The selected affine shift -- F0 even for Haar Y. Pass into real covariance

Uses both frozen and active edges in their true orientation. The extra
`all` matrices in proof aren't Gram inputs; Gram only uses the
ACTIVE subarray. No hypotheses on receiving pairs realizing annuli.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.SectorAffine.Offset
open Filter Function Lattice Wilson RG Precision Pressure Tree Exterior Bloch
open YM.Next YM.Next.Fluctuations YM.Next.SectorChange YM.Next.SectorChange.Rows
open YM.Push.Uniform (bolt Allows)
open YM.Push.SectorMeasure
open YM.FreeResolvent (Mark Bundle native Cost)
open YM.FreeResolvent.TestD Matrix
open scoped Topology ContDiff BigOperators InnerProductSpace Classical Matrix.Norms.Frobenius

variable {G : Gauge} {c f : Side} {S : StepData c f} {P : Patch} {T : Tube G S} {F : Forest S.ratio} {A : Stores S}
    {V : Config G c} {k : S.Choices} {x B d γ M C : ℝ} {n : ℕ}

section f0
variable (T : Tube G S) (x : ℝ) (A : Stores S) (F : Forest S.ratio) (k : S.Choices) (V : Config G c)

def allData : Matrix (Receipt G S) (Coord G f) ℝ := Matrix.of fun i j => tape.symm
    (selected T x V k (shots S x) A F (fineRay j)) i

def f0 (q : Chi) (d : ℝ) (Y : LinkArray G (Frozen A x F)) : Prices G (Slots S) :=
  tape.symm (Rows.restrict x (shots S x) A F
    (fixedBase T x V k+bump T x V k (Rows.input x A F (autoShell q d V Y))))

lemma pass {σ a Λ : ℝ} {c₀ : Clip} (hp : T.up.Bounds c₀ σ a Λ) (e : Directions G f) :
    allData T x A F k V *ᵥ (tape.symm e) = tape.symm
      (Rows.restrict x (shots S x) A F (bump T x V k e)) := by
  let W := shots S x
  let J : Directions G f →ₗ[ℝ] LogArray G (Slots S) := {
    toFun := selected T x V k W A F
    map_add' := fun a b => by unfold selected; rw [bump_add T x V k hp, restrict_add]
    map_smul' := fun w a => by unfold selected; rw [bump_smul T x V k hp, restrict_smul]; rfl }
  let L := colors.symm.toLinearMap ∘ₗ J ∘ₗ (colors (G:=G) (ι:=Bond f)).toLinearMap
  have he : LinearMap.toMatrix' L=allData T x A F k V := by
    ext i j; rw [LinearMap.toMatrix'_apply]
    change tape.symm (selected T x V k W A F (axisPrice j)) i=_
    rw [show _=fineRay j from on_axis j]; rfl
  rw [← he,LinearMap.toMatrix'_mulVec]
  change tape.symm (J (tape (tape.symm e))) = _; rw [tape.apply_symm_apply]; rfl

lemma f0_split {Pt : Teller G} (hp : Pt.Funds S T) (q : Chi) (d : ℝ) (Y : LinkArray G (Frozen A x F)) :
    f0 T x A F k V q d Y = tape.symm (Rows.restrict x (shots S x) A F (fixedBase T x V k)) +
      allData T x A F k V *ᵥ (tape.symm (Rows.input x A F (autoShell q d V Y))) := by
  obtain ⟨a,b,h₁,h₂⟩ := hp.feeds
  unfold f0; rw [restrict_add,pass _ _ _ _ _ _ h₁]; exact colors.symm.map_add ..

lemma correct_f0 (G : Gauge) (P : Patch) (Pt : Teller G) : ∀ᶠ x : ℝ in atTop,
    ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch=P → Pt.Funds S T →
    ∀ (A : Stores S) (F : Forest S.ratio) (V : Config G c), A.flags=RG.flags (temp x) V →
    ∀ (k : S.Choices) (q : Chi) (d : ℝ), f0 T x A F k V q d = Rows.source T x V k (shots S x) A F q d := by
  filter_upwards [correct_base G P Pt] with x hx
  intro c f S T hS hT A F V hA k q d
  funext Y; unfold f0 Rows.source
  rw [restrict_add, restrict_add,hx S T hS hT A F V hA k]
end f0

section costing
lemma nearby (hd : 0<d) : (native c).Volume (location (G:=G) S) d (FreeResolvent.torusPay
    (Co S.patch.L (Axis × G.ColorIndex)) d) := by
  let E := (Equiv.prodAssoc (Site f) Axis G.ColorIndex).trans (splitCo S.ratio (Axis × G.ColorIndex))
  have he := (FreeResolvent.volume c (Co S.ratio.count (Axis × G.ColorIndex)) d hd).comp E.injective
  rw [show location S (G:=G)=Prod.fst ∘ E from funext fun j => by simp only [Function.comp_apply,E,Equiv.trans_apply,split_co]; rfl]
  exact he

lemma allData_cost (G : Gauge) (P : Patch) (Pt : Teller G) (hk : P.Branches Pt.bind G) (n : ℕ) :
    ∃ d M : ℝ, 0<d ∧ 0<M ∧ ∀ᶠ x : ℝ in atTop,
    ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch=P → 100*(1+radiusB x) ≤ c.val →
    Pt.Funds S T → ∀ (A : Stores S) (F : Forest S.ratio) (V : Config G c), A.flags=RG.flags (temp x) V →
    ∀ k : S.Choices,
      Polar 0 (Wisps.down S) (location S) (fun z => allData T x A F k (pulse x V z)) n d M := by
  obtain ⟨r,d,M,hr,hd,hM,h⟩ := selected_priced G P Pt hk n
  let K := max (priceFiber P G d) (FreeResolvent.torusPay (Co P.L (Axis × G.ColorIndex)) d)
  have hk : 0<K := lt_of_lt_of_le (priceFiber_pos ..) (le_max_left ..)
  refine ⟨d,K*M,hd,mul_pos hk hM,?_⟩
  filter_upwards [monitors G P.L,h] with x hx ht
  intro c f S T hP hF hT A F V hv k
  let Q := fun z => allData T x A F k (field V z)
  have he i j := ht S T hP hF hT A F V hv 0 (by simpa using hr.le) k i j
  apply polar_compress (A:=Q) _ hx.1.le hx.2.1
  have hs : ContDiffAt ℝ n Q 0 := by
    let W : ((Rows.Receipt G S) → Coord G f → ℝ) ≃L[ℝ] Matrix (Rows.Receipt G S) (Coord G f) ℝ :=
      (Matrix.ofLinearEquiv ℝ).toContinuousLinearEquiv
    exact W.contDiff.contDiffAt.comp (0:PriceCoords G c) (show ContDiffAt ℝ n (fun x i j => Q x i j)
      _ from contDiffAt_pi.mpr fun i => contDiffAt_pi.mpr fun j => (he i j).smooth.of_le le_top)
  refine ⟨hs,fun l hl => ?_⟩
  have hA : (native c).Volume (location S (G:=G)) (2*d-d) K := by
    rw [show 2*d-d=d by ring]; unfold K; rw [← hP]; exact (nearby hd).le (le_max_right ..)
  have hB : (native c).Volume (Wisps.down S (G:=G)) (2*d-d) K := by
    rw [show 2*d-d=d by ring]; unfold K; rw [← hP]; exact (fiber_volume S G hd A F x).2.le (le_max_left ..)
  refine Mark.Bill.of_entry hA hB hM.le (fun i j => ?_) (fun i j => ?_)
  · rw [← entry bolt l (smooth_of_le hs hl)]; exact (he i j).each _ (.inl rfl) l hl
  rw [(native c).weight_symm,← entry bolt l (smooth_of_le hs hl)]; exact (he i j).each _ (.inr rfl) l hl

lemma f0_cost (G : Gauge) (P : Patch) (Pt : Teller G) (q : Chi) (hB : 0<B) (hP : P.Branches Pt.bind G) (n : ℕ) :
    ∃ d M : ℝ, 0<d ∧ 0<M ∧ ∀ᶠ x : ℝ in atTop,
    ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch=P → Pt.Funds S T → 100*(1+radiusB x) ≤ c.val →
    ∀ (F : Forest S.ratio) (A : Stores S) (V : Config G c), A.flags=RG.flags (temp x) V → ∀ (k:S.Choices),
    let t := fiery G x S.patch.L
    f0 T x A F k V q (B*t)=Rows.source T x V k (shots S x) A F q (B*t) ∧
    ∀ Y : LinkArray G (Frozen A x F), Parcel 0 (Wisps.down S) d n
      (fun z => f0 T x A F k (pulse x V z) q (B*t) Y) (M*t) := by
  obtain ⟨d,X,hd,hX,h⟩ := base_cost G P Pt hP n
  obtain ⟨c,Q,hc,hQ,h'⟩ := allData_cost G P Pt hP n
  let a : ℝ := c/(n+1:ℕ)
  have ha : 0<a := by unfold a; positivity
  have hm : a ≤ c ∧ n*a ≤ c := by
    have hz : a*(n+1:ℕ)=c := div_mul_cancel₀ _ (by positivity)
    have hn : 0≤(n:ℝ)*a := by positivity
    push_cast at hz; constructor <;> linarith
  obtain ⟨M,hM,H⟩ := shell_price G q P a ha B hB n
  refine ⟨min a d, X+((2:ℝ)^n*(M*Q)), lt_min ha hd,by positivity,?_⟩
  filter_upwards [h,h',H,correct_f0 G P Pt] with x hx ht hh hh'
  intro c' f S T hs he hF F A V hv k t
  refine ⟨hh' S T hs he A F V hv k q (B*t),fun Y => ?_⟩
  have hp : t=fiery G x P.L := by unfold t; rw [hs]
  have hn : 0≤M*t := mul_nonneg hM.le (temp_nonneg _)
  have hh : Parcel 0 (location S) a n (fun z => tape.symm (Rows.input x A F (autoShell q (B*t) (pulse x V z) Y)))
      (M*t) := by
    rintro ⟨i,j⟩
    simp_rw [tape_read,Rows.input]; split
    · split
      next hk => rw [hp]; exact (hh S F A V Y ⟨_,hk⟩).color j
      next hk => exact Point.zero hn
    exact Point.zero hn
  have hb := Parcel.mono (hp.symm ▸ hx S T hs he hF F A V hv k) (min_le_right a d) le_rfl
  have hu := (hh.deliver hn (ht S T hs hF he A F V hv k) hQ.le ha.le hm.1 hm.2).mono (min_le_left a d) le_rfl
  simp_rw [f0_split _ _ _ _ _ _ he]
  exact (hb.add hu).mono le_rfl (le_of_eq (by ring))
end costing
end YM.AnalyticBridge.SectorAffine.Offset
