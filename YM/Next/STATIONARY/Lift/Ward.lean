import YM.Next.STATIONARY.Lift.Pathways


set_option autoImplicit false
/-! Orbit convention (negative at the *input* axis). -/
noncomputable section
namespace YM.Stationary
open Function Lattice RG Exterior Wilson Precision Bloch Laurent Filter Finset Asymptotics
open Matrix (transpose mulVec of)
open scoped Matrix Topology ContDiff BigOperators NNReal
variable {G : Gauge} {m : Side}

lemma act_phase (s : Signed) (p : Momentum) (z : Cover) : mode (s.act p) (s.act z)=mode p z := by
  unfold Laurent.mode; congr 2
  rw [← Equiv.sum_comp s.perm]; exact sum_congr rfl fun k _ => by rw [s.act_at,s.act_at]; split <;> simp

lemma mirror_cell (s : Signed) (p q : Site m) : cell (s.act p) (s.act q)=cell p q := by
  let P := lift p; let Q := lift q
  have hp : wrap m (s.act P)=s.act p := by unfold P; rw [← wrap_signed,wrap_lift]
  have hq : wrap m (s.act Q)=s.act q := by unfold Q; rw [← wrap_signed,wrap_lift]
  rw [← hq,cell_wrap]
  obtain ⟨i,H⟩ := cover_of_eq _ _ ((wrap_lift (s.act p)).trans hp.symm)
  have hs : s.act (mon p)=mon (s.act p)+reciprocal i := by
    ext1 j; obtain ⟨j,rfl⟩ := s.perm.surjective j
    have hv : (if s.flip j then -P j else P j)=lift (s.act p) (s.perm j)+m.val • i (s.perm j) :=
      (s.act_at ..).symm.trans (congr_fun H _)
    rw [s.act_at,Pi.add_apply]; unfold mon reciprocal; simp only [Pi.smul_apply, smul_eq_mul]
    cases hj : s.flip j
    · simp only [hj,Bool.false_eq_true,↓reduceIte] at hv ⊢
      rw [show lift p j=P j from rfl,hv,nsmul_eq_mul]; push_cast; field_simp [side_ne]
    have he : P j=-(lift (s.act p) (s.perm j)+m.val • i (s.perm j)) := by
      simpa [hj] using congr_arg Neg.neg hv
    simp only [if_true]
    rw [show lift p j=P j from rfl,he,nsmul_eq_mul]; push_cast; field_simp [side_ne]
  have ht := act_phase s (mon p) Q
  rw [hs,mode_phase,mode_periodic,mul_one] at ht; exact ht

-- canonical direction and starting base
variable (s : Signed)

def flipCoords (R : Type) [CommRing R] : (Lines G m 1 → R) →ₗ[R] (Lines G m 1 → R) := LinearMap.pi (fun x =>
    let k := axisEquiv.symm x.2.1
    let q := s.perm k
    if s.flip k then -(LinearMap.proj (s.act x.1-step q,coord q,x.2.2)) else LinearMap.proj (s.act x.1,coord q,x.2.2))
lemma flip_price {R : Type} [CommRing R] (x : Lines G m 1 → R) (i k j) : flipCoords (G:=G) (m:=m) s R x (i,coord k,j)=
    if s.flip k then -x (s.act i-step (s.perm k), coord (s.perm k), j) else x (s.act i,coord (s.perm k),j) := by
  simp only [flipCoords, LinearMap.pi_apply,show axisEquiv.symm (coord k)=k from axisEquiv.symm_apply_apply _]; split <;> rfl
lemma flip_scalar (x : Link G m) : axes (flipCoords (G:=G) (m:=m) s ℝ x)=flipCoords (G:=G) (m:=m) s ℂ (axes x) := by
  ext1 ⟨p,i,j⟩; obtain ⟨i,rfl⟩ := axisEquiv.surjective i; unfold axes; simp only [coord_map,flip_price]; split <;> simp

lemma flip_links (x : Link G m) : pull s 0 (input G m x)=input G m (flipCoords s ℝ x) := by
  have he := Work.F03.represent_pulled s (arm G m 1 x) (1:ℝ); simp only [one_smul] at he
  unfold input; rw [he]; congr 1; ext ⟨i,k⟩ j
  obtain ⟨k,rfl⟩ := axisEquiv.surjective k
  simp only [coord_map,Bid.pulled,show axisEquiv.symm (coord k)=k from axisEquiv.symm_apply_apply _,arm_apply,flip_price]
  unfold affine Step.used Step.rotate posDir; cases h : s.flip k <;> simp [*,arm_apply]

def reflectFee (p : Momentum) (k : Axis) : ℂ := if s.flip k then -mode p (-(step (s.perm k))) else 1
lemma reflect_size (p : Site m) (k : Axis) : ‖reflectFee s (mon p) k‖=1 := by
  unfold reflectFee; split
  · rw [norm_neg,mode_real _ _ (real_frequency _)]
  exact norm_one
lemma flipped (i : Site m) (a : Axis) (j : G.ColorIndex) :
    flipCoords s ℂ (relay i (coord (s.perm a), j))=reflectFee s (mon i) a • relay (s⁻¹.act i) (coord a,j) := by
  ext1 ⟨p,x,b⟩; obtain ⟨x,rfl⟩ := axisEquiv.surjective x
  simp only [coord_map, flip_price, reflectFee, Pi.smul_apply, smul_eq_mul]
  by_cases he : x=a
  · subst x
    have hx : cell i (s.act p)=cell (s⁻¹.act i) p := by simpa only [s.act_inv] using mirror_cell s (s⁻¹.act i) p
    cases hk : s.flip a
    · simp [*,relay,tune,Pi.single_apply]
    simp only [if_true]; unfold relay tune
    simp only [sub_eq_add_neg,cell_add,hx]
    rw [show -(step (s.perm a) : Site m)=wrap m (-(step (s.perm a))) by rw [map_neg,wrap_step],cell_wrap]
    simp only [Pi.single_apply, Prod.mk.injEq,true_and]; ring
  cases hx : s.flip x <;> cases hv : s.flip a <;> simp [*,relay,tune,coord_iff]

section orbit
variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

theorem note_comp {g : Corn α → ℝ} (L : Corn β →L[ℝ] Corn α) (M : Phase β →ₗ[ℂ] Phase α)
    (h : ∀ x, axes (L x)=M (axes x)) (hf : AnalyticAt ℝ g 0) (n : ℕ) :
    noteAt (g ∘ L) n=(noteAt g n).compLinearMap fun _ => M := by
  apply enlarge_unique; intro v
  rw [note_real,MultilinearMap.compLinearMap_apply,
    show (fun i : Fin n => M ((axes ∘ v) i))= axes ∘ (L ∘ v) from funext fun i => (h (v i)).symm, note_real]
  unfold Tensor.coeff
  rw [_root_.smul_apply, _root_.smul_apply,wired L (by rw [map_zero]; exact hf), map_zero]
lemma note_sum {ι : Type} [Fintype ι] (f : ι → Corn α → ℝ) (h : ∀ i, AnalyticAt ℝ (f i) 0) (n : ℕ) :
    noteAt (fun p => ∑ i, f i p) n = ∑ i, noteAt (f i) n := by
  apply enlarge_unique; intro v
  rw [_root_.sum_apply]; simp_rw [note_real]
  rw [show (fun p => ∑ i, f i p)=∑ i,f i from funext fun x => (Finset.sum_apply ..).symm, Tensor.coeff_sum _ _ _ _ (fun i _ => (h i).contDiffAt),_root_.sum_apply,Complex.ofReal_sum]

lemma note_mean {ι : Type} [Fintype ι] (f : ι → Corn α → ℝ) (h : ∀ i, AnalyticAt ℝ (f i) 0) (n : ℕ) :
    noteAt (fun p => Patch.average fun i => f i p) n=(Fintype.card ι :ℂ)⁻¹ • ∑ i, noteAt (f i) n := by
  apply enlarge_unique; intro v
  rw [_root_.smul_apply,← note_sum f h]; simp_rw [note_real]
  unfold Patch.average Tensor.coeff; rw [_root_.smul_apply,_root_.smul_apply]
  have he : ContDiffAt ℝ n (fun p => ∑ i, f i p) 0 := ContDiffAt.sum fun i _ => (h i).contDiffAt
  rw [show (fun p => (Fintype.card ι:ℝ)⁻¹ * ∑ i, f i p) = (Fintype.card ι:ℝ)⁻¹ • (fun p => ∑ i, f i p) from rfl,
    iteratedFDeriv_const_smul_apply he]; simp; ring
end orbit
end YM.Stationary
end

/-!
# Attach a per-period approximation without a symmetry assumption about paths

Applies `Features` data purely to build paths. The unmasked branch runs the **same** paths
in the same orientation orbit. Needn't assert the lifted kernels have any covariance:
transfer comparing to the known rotated *score scalar* on that period.
Error in complex **Taylor coefficient** convention (multiply by factorial
for mixed derivative bounds). No comparison to masks.
-/
noncomputable section
namespace YM.Stationary
open Function Lattice RG Exterior Wilson Precision Bloch Laurent Filter Finset Asymptotics
open Matrix (transpose mulVec of)
open scoped Matrix Topology ContDiff BigOperators NNReal
variable {G : Gauge} {m : Side} {t n : ℕ} {σ A ε : ℝ}

-- flip as continuous map over ℝ
def orderTurn (s : Signed) : Link G m →L[ℝ] Link G m :=
    LinearMap.toContinuousLinearMap (flipCoords s ℝ)

/-- The `SameJet` comparison uses real pullback by signed permutation. -/
def Lit (n : ℕ) (F : Link G m → ℝ) : Prop := ∀ s : Signed,
    noteAt (F ∘ (orderTurn (G:=G) (m:=m) s)) n = noteAt F n

def aperture (ε : ℝ) (F H : Link G m → ℝ) (t : ℕ) : Prop := ∀ (p : Fin (t+1) → Site m) i v,
    let g := glyph p (G:=G) i v
    ‖noteAt F (t+1) g - noteAt H (t+1) g‖ ≤ ε

lemma aperture_eq {F H : Link G m → ℝ} (h : aperture 0 F H t) :
    iteratedFDeriv ℝ (t+1) F 0 = iteratedFDeriv ℝ (t+1) H 0 := by
  apply from_note _ _ _
  apply relay_ext
  intro p
  exact sub_eq_zero.mp (norm_le_zero_iff.mp
    (h (fun i => (p i).1) (fun i => (p i).2.2) (fun i => (p i).2.1)))

lemma priceNote (F : Link G m → ℝ) (hF : AnalyticAt ℝ F 0) (s : Signed) (p : Fin (t+1) → Site m)
    (b : Ink G (t+1)) (v : Fin (t+1) → Axis) :
    let q := glyph p b (fun i => coord (s.perm (v i)))
    noteAt (F ∘ orderTurn (G:=G) (m:=m) s) (t+1) q=
      (∏ i, reflectFee s (mon (p i)) (v i))*noteAt F _ (glyph (fun i => s⁻¹.act (p i)) b (fun i => coord (v i))) := by
  intro q; rw [note_comp (orderTurn s) _ (flip_scalar s) hF,MultilinearMap.compLinearMap_apply]
  unfold q glyph
  simp_rw [flipped]; exact (noteAt F _).map_smul_univ _ _

lemma aperture_flip {F H : Link G m → ℝ} (h : aperture ε F H t) (hF : AnalyticAt ℝ F 0) (hH : AnalyticAt ℝ H 0)
    (ha : Lit (t+1) H) (s : Signed) : aperture ε (F ∘ orderTurn s) H t := by
  intro p i v g
  let r j := s.perm.symm (axisEquiv.symm (v j))
  have he : v= fun i => coord (s.perm (r i)) := by ext1 j; simp only [r,Equiv.apply_symm_apply]; exact (axisEquiv.apply_symm_apply _).symm
  unfold g; rw [he,← ha s,priceNote F hF,priceNote H hH,← mul_sub,norm_mul,norm_prod]; simpa only [reflect_size, Finset.prod_const_one,one_mul] using h (fun i => s⁻¹.act (p i)) i (fun j => coord (r j))

private lemma mean_budget {ι : Type} [Fintype ι] [Nonempty ι] (f : ι→ℂ) (d M : ℂ) (he : M=(Fintype.card ι:ℂ)⁻¹ * ∑ i,f i) (h : ∀ i, ‖f i-d‖ ≤ ε) :
    ‖M-d‖ ≤ ε := by
  have hh := Fintype.card_pos (α:=ι)
  have hr : (Fintype.card ι:ℝ) ≠ 0 := by positivity
  have hC : (Fintype.card ι:ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  rw [he, show _ - d=(Fintype.card ι:ℂ)⁻¹ * (∑ i,(f i - d)) by simp [sum_sub_distrib,mul_sub, hC], norm_mul,norm_inv]
  calc
    _ ≤ ‖(Fintype.card ι:ℂ)‖⁻¹ * (∑ i : ι, ε) := mul_le_mul_of_nonneg_left ((norm_sum_le ..).trans (sum_le_sum fun i _ => h i)) (inv_nonneg.mpr (norm_nonneg _))
    _ = _ := by simp [hr]

section channel

def turnSeries (A : ℕ → Atom G n) (a : Link G m) := Patch.average fun i : Signed => uncut A (pull i 0 (input G m a))

def inputSeries (p : Clip) (W : PathData G) (a : Link G m) := secondTerm p W (input G m a)
lemma turns_frame (F : ℕ → Atom G n) (p : Link G m) : turnSeries F p=Patch.average fun i : Signed =>
    seriesScore m F (orderTurn i p) := by simp [turnSeries,flip_links,seriesScore,orderTurn]
lemma turns_analytic (F : ℕ → Atom G n) (hσ : 0<σ) (hf : SumBudget (fun i => (F i).budget σ) A) : AnalyticAt ℝ (turnSeries F (m:=m)) 0 := by
  apply ContDiffAt.analyticAt
  simp_rw [funext (turns_frame (m:=m) F)]; unfold Patch.average
  refine ContDiffAt.mul contDiffAt_const (ContDiffAt.sum fun i _ => ?_)
  refine ContDiffAt.comp (g:=seriesScore m F) (f:=⇑(orderTurn (G:=G) (m:=m) i)) (0:Link G m) ?_ (orderTurn (G:=G) (m:=m) i).contDiff.contDiffAt
  rw [map_zero]; exact (score_analytic m F hσ hf).contDiffAt
lemma turns_low (F : ℕ → Atom G n) (hσ : 0<σ) (hf : SumBudget (fun i => (F i).budget σ) A) : Rays n (turnSeries F (m:=m)) := by
  intro v
  simp_rw [turns_frame]; unfold Patch.average
  refine IsBigO.const_mul_left ?_ _
  apply Asymptotics.IsBigO.sum; intro i _
  simp_rw [map_smul]; exact ink_low m F hσ hf _

/-- Sum over all legs and translations on the *cover*, then compare on the
same p-grid as the new data. Inherently also treats nonopposite external waves,
harmonic, and the curvature support carries the true wrap costs. -/
theorem colors_align [NeZero t] (F : Link G m → ℝ) (he : AnalyticAt ℝ F 0) (hl : Lit (t+1) F) (L : Picture G t)
    (P : Skin G t) (hp : Shades P L σ A) (hs : 0<σ) (hr : Recorded L F ε) :
    aperture ε (turnSeries (issue P)) F t := by
  let Φ := issue P
  let T := seriesScore m Φ
  have hP := (artery_funded hp).1
  have hh : aperture ε T F t := by
    intro p i v g
    let E (d : Equiv.Perm (Fin (t+1))) := enlarge (volumeInk m Φ).toMultilinearMap (g ∘ d)
    apply mean_budget E _ _
    · simpa only [T,Φ,Fintype.card_perm,Fintype.card_fin,E] using ink_beat m (issue P) hs hP g
    intro d
    rw [← note_perm F he g d]
    unfold E
    rw [show g ∘ ⇑d=glyph (p ∘ d) (i ∘ d) (v ∘ d) from rfl, show Φ=_ from rfl, notesPath hs hp,norm_sub_rev]
    exact hr _ _ _
  intro p i v g
  have hg (s : Signed) : AnalyticAt ℝ (T ∘ orderTurn (G:=G) (m:=m) s) 0 := by
    have hx : AnalyticAt ℝ T (orderTurn s (0:Link G m)) := by rw [map_zero]; exact score_analytic m Φ hs hP
    exact hx.comp ((orderTurn _).analyticAt _)
  let D (s : Signed) := noteAt (T ∘ orderTurn s) (t+1) g
  apply mean_budget D _ _
  · rw [show turnSeries (m:=m) Φ = fun p => Patch.average (fun i : Signed => (T ∘ orderTurn i) p) from
      funext (turns_frame Φ), note_mean _ hg,_root_.smul_apply,_root_.sum_apply]; rfl
  exact fun s => aperture_flip hh (score_analytic m Φ hs hP) he hl s p i v
end channel
end YM.Stationary
end

/-! # Common torus reading and passage to continuous external variables -/
noncomputable section
namespace YM.Stationary
open Function Lattice RG Exterior Wilson Precision Bloch Laurent Filter Finset
open scoped Matrix Topology ContDiff BigOperators NNReal
variable {α : Type} [Fintype α] {G : Gauge} {m : Side} {t : ℕ}
    {η A : ℝ}

-- congruent radians
def rolls (p q : Phase α) := ∃ z : Shift α,q = p+reciprocal z

lemma rolls.exp {p q : Phase α} (h : rolls p q) (i : Shift α) : mode p i=mode q i := by obtain ⟨d,rfl⟩ := h; rw [mode_phase,mode_periodic, mul_one]
omit [Fintype α] in
lemma rolls.apply {p q : Phase α} {f : Phase α→ℂ} (h : rolls p q) (hp : Firm η A f) (hx : p ∈ strip η) : f p=f q := by obtain ⟨d,rfl⟩ := h; exact (hp.1.reset _ hx _).symm
omit [Fintype α] in
lemma rolls.refl (p : Phase α) : rolls p p := ⟨0,by ext; simp [reciprocal]⟩
omit [Fintype α] in
lemma rolls.symm {p q : Phase α} (h : rolls p q) : rolls q p := by
  obtain ⟨d,rfl⟩ := h; refine ⟨-d,?_⟩; ext1 i; simp [reciprocal]
omit [Fintype α] in
lemma rolls.trans {p q r : Phase α} (h : rolls p q) (hp : rolls q r) : rolls p r := by
  obtain ⟨d,rfl⟩ := h; obtain ⟨v,rfl⟩ := hp; refine ⟨d+v,?_⟩; ext1 i; simp [reciprocal,mul_add]; ring
omit [Fintype α] in
lemma rolls.neg {p q : Phase α} (h : rolls p q) : rolls (-p) (-q) := by
  obtain ⟨d,rfl⟩ := h; refine ⟨-d,?_⟩; ext1 i; simp [reciprocal]; ring
omit [Fintype α] in
lemma rolls.metric {p q : Phase α} (h : rolls p q) (hp : star p=p) : star q=q := by
  obtain ⟨d,rfl⟩ := h; rw [star_add,hp]; congr 1; ext1 i; simp [reciprocal]

lemma rolls_of_mode {p q : Momentum} (he : ∀ x, mode p x=mode q x) : rolls p q := by
  have H (a : Axis) : ∃ n : ℤ, q a = p a + 2*(Real.pi:ℂ)*n := by
    have hp := he (step a); rw [factor,factor] at hp
    obtain ⟨z,hz⟩ := Complex.exp_eq_exp_iff_exists_int.mp hp.symm
    use z; apply mul_left_cancel₀ Complex.I_ne_zero
    rw [mul_add]; linear_combination hz
  choose z hz using H
  exact ⟨z,funext hz⟩

omit [Fintype α] in
lemma rolls_keys {p q : Space t} (h : ∀ i : Fin t, rolls (projected (strand i) p) (projected (strand i) q)) : rolls p q := by
  choose x hx using h
  exact ⟨(fun i => x i.1 i.2), funext fun ⟨k,a⟩ => congr_fun (hx k) a⟩

-- harmonic reading at all momentum reps
lemma ties {p : Fin (t+1) → Site m} (hp : ∑ i,p i=0) (j) : rolls (plotted (outphase p) j) (mon (p j)) := rolls_of_mode (fun x => by rw [manyModes _ hp,cell_wrap])

-- canonical rounding with winding even along b not in cube
lemma mesh_stride (m : ℕ → Side) (h : Tendsto (fun i => (m i).val) atTop atTop) (p : Momentum) (he : star p=p) :
    ∃ (y : ∀ i, Site (m i)) (u : ℕ → Momentum), Tendsto u atTop (𝓝 p) ∧ ∀ i, rolls (mon (y i)) (u i) := by
  let a (i : ℕ) := (m i).val
  let b := 2*Real.pi
  have ha i : 0 < (a i:ℝ) := side_pos (m i)
  have hb : 0<b := by unfold b; positivity
  let r : Corn Axis := fun i => (p i).re
  have hr : axes r=p := axes_of_real he
  let v i : Cover := fun j => ⌊(a i:ℝ)*r j / b⌋
  let u i : Corn Axis := fun j => b*(v i j)/(a i:ℝ)
  refine ⟨fun i => wrap (m i) (v i),fun i => axes (u i),?_,?_⟩
  · rw [← hr]; refine axes_maps.continuous.continuousAt.tendsto.comp ?_
    refine tendsto_pi_nhds.mpr fun j => ?_
    have ht : Tendsto (fun i => b/(a i:ℝ)) atTop (𝓝 0) := tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp h)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le (h:=fun _ => r j) (g:=fun i => r j - b/(a i:ℝ)) (by simpa using tendsto_const_nhds.sub ht) tendsto_const_nhds ?_ ?_
    · intro i; unfold u
      have he := Int.lt_floor_add_one ((a i:ℝ)*r j / b); change _ < (↑(v i j):ℝ)+1 at he
      rw [div_lt_iff₀ hb] at he; rw [le_div_iff₀ (ha _),sub_mul,div_mul_cancel₀ _ (ha i).ne']
      linarith
    intro i; unfold u
    have he := (le_div_iff₀ hb).mp (Int.floor_le ((a i:ℝ)*r j / b)); change ↑(v i j)*b ≤ _ at he
    rw [div_le_iff₀ (ha _)]
    linarith
  intro i
  let X := wrap (m i) (v i)
  obtain ⟨q,H⟩ := cover_of_eq (lift X) (v i) (n:=m i) (wrap_lift X)
  -- Keep the full winding.
  refine ⟨q,?_⟩; ext1 j; unfold u mon; simp only [axes,Pi.add_apply,Pi.smul_apply,smul_eq_mul,reciprocal]
  change _ = (a i:ℂ)⁻¹ * (2 * (Real.pi:ℂ) * (lift X j:ℤ)) + _
  rw [show v i j=lift X j+(a i:ℤ)*q j from (congr_fun H j).trans (by simp [a])]
  have hn : (a i:ℂ)≠0 := side_ne _
  unfold b; push_cast; field_simp

lemma fleet (m : ℕ → Side) (h : Tendsto (fun i => (m i).val) atTop atTop) (p : Space t) (he : star p=p) :
    ∃ (y : ∀ i, Fin (t+1) → Site (m i)) (u : ℕ → Space t), Tendsto u atTop (𝓝 p) ∧ ∀ i,
        ∑ j,y i j=0 ∧ rolls (outphase (y i)) (u i) := by
  choose z v hz hv using fun j : Fin t => mesh_stride m h (projected (strand j) p) (funext fun k => congr_fun he (j,k))
  let Y (i : ℕ) : Fin (t+1) → Site (m i) := Fin.cons (- ∑ j,z j i) (fun j => z j i)
  let U (i : ℕ) : Space t := fun k => v k.1 i k.2
  refine ⟨Y,U, tendsto_pi_nhds.mpr (fun ⟨j,k⟩ => tendsto_pi_nhds.mp (hz j) k),fun i => ⟨?_,?_⟩⟩
  · simp [Y,Fin.sum_univ_succ]
  apply rolls_keys; intro j
  have hq : projected (strand j) (outphase (Y i))=mon (z j i) := by ext k; simp [Y,outphase,projected,strand]
  rw [hq]; exact hv j i
end YM.Stationary
end

/-! # Coarse gauge tests, actual logs near origin -/
noncomputable section
namespace YM.Stationary
open Function Lattice RG Exterior Wilson Precision Bloch Laurent Filter Finset
open Matrix (transpose mulVec of)
open scoped Matrix Topology ContDiff BigOperators NNReal Matrix.Norms.Frobenius
variable {G : Gauge} {n t : ℕ} {m : Side}

abbrev BaseSites (G : Gauge) (m : Side) := Corn (Lines G m 0)

def switchSite (p : BaseSites G m) : Site m → G.El := fun x => G.lieExp (arm G m 0 p (x,vac))

def content (U : Config G m) : Link G m := (arm G m 1).symm (fun i => G.plog (G.mat (U (i.1,axisEquiv.symm i.2))))

@[simp] lemma content_one : content (1:Config G m)=0 := by simp [content]; rfl
@[simp] lemma switch_zero : switchSite (0:BaseSites G m)=1 := by ext i; simp [switchSite]

lemma encode_link (a : Link G m) (x : Site m) (y : Axis) : input G m a (x,y)= G.lieExp (arm _ _ _ a (x,coord y)) := Work.F03.represent_link ..
lemma content_at (U : Config G m) (x : Site m) (i : Axis) : arm G m 1 (content U) (x,coord i) = G.plog (G.mat (U (x,i))) := by
  rw [content,(arm G m 1).apply_symm_apply]; simp only [show axisEquiv.symm (coord i)=i from axisEquiv.symm_apply_apply i]

lemma content_encodes : ∀ᶠ U in 𝓝 (1:Config G m), input G m (content U)=U := by
  have he (i : Edge (Site m)) : ∀ᶠ U : Config G m in 𝓝 1, G.lieExp (G.plog (G.mat (U i)))= U i :=
    (show Tendsto (fun U : Config G m => U i) (𝓝 1) (𝓝 1) from (continuous_apply i).tendsto (1:Config G m)).eventually G.plog_right
  filter_upwards [eventually_all.mpr he] with U hu
  funext ⟨x,i⟩; rw [encode_link, content_at]; exact hu _

lemma input_encodes : ∀ᶠ a : Link G m in 𝓝 0, content (input G m a)=a := by
  have he (i : Body 1 m) : ∀ᶠ x : Link G m in 𝓝 0, G.plog (G.mat (G.lieExp (arm G m 1 x i)))=arm G m 1 x i := by
    have h : Tendsto (fun x => arm G m 1 x i) (𝓝 0) (𝓝 0) := by
      simpa only [map_zero,Pi.zero_apply] using! ((continuous_apply i).comp (arm G m 1).continuous).tendsto 0
    exact h.eventually G.plog_left
  filter_upwards [eventually_all.mpr he] with v hv
  apply (arm G m 1).injective; funext ⟨x,y⟩; obtain ⟨i,rfl⟩ := axisEquiv.surjective y
  change arm _ _ _ _ (x,coord i) = _
  rw [content_at, encode_link]; exact hv _

section coord
variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {F : X → Config G m} {z : X}
lemma content_analytic (h : F z=1) (he : ∀ p, AnalyticAt ℝ (fun x => G.mat (F x p)) z) : AnalyticAt ℝ (content ∘ F) z := by
  unfold content Function.comp
  refine ((arm G m 1).symm.analyticAt _).comp (f:=fun a i => G.plog (G.mat (F a (i.1,axisEquiv.symm i.2)))) ?_
  refine (contDiffAt_pi (n:=ω) |>.mpr (fun i => ?_)).analyticAt
  refine ContDiffAt.comp (g:=G.plog) _ ?_ ((he (i.1,axisEquiv.symm i.2)).contDiffAt)
  rw [h,Pi.one_apply,G.mat_one]; exact G.plog_diff
end coord

abbrev Swatch (G : Gauge) (m : Side) := BaseSites G m × Link G m
def shiftLinks (p : Swatch G m) := Lattice.gauge (switchSite p.1) (input G m p.2)
def moveField (p : Swatch G m) := content (shiftLinks p)
@[simp] lemma shiftLinks_zero : shiftLinks (0:Swatch G m)=1 := by funext i; simp [shiftLinks,Lattice.gauge]
@[simp] lemma moveField_zero : moveField (0:Swatch G m)=0 := by rw [moveField,shiftLinks_zero,content_one]

lemma switch_cont : Continuous (switchSite (G:=G) (m:=m)) := by unfold switchSite; fun_prop
lemma input_cont : Continuous (input G m) := by
  refine continuous_pi fun i => ?_; rcases i with ⟨x,i⟩; simp_rw [encode_link]; fun_prop
lemma shiftLinks_cont : Continuous (shiftLinks (G:=G) (m:=m)) := by
  unfold shiftLinks Lattice.gauge; have hu := input_cont (G:=G) (m:=m); have hb := switch_cont (G:=G) (m:=m); fun_prop

lemma moveField_germ : ∀ᶠ p : Swatch G m in 𝓝 0, input G m (moveField p)=shiftLinks p := by
  have ht := shiftLinks_cont (G:=G) (m:=m) |>.tendsto 0
  rw [shiftLinks_zero] at ht; exact ht.eventually content_encodes

lemma moveField_analytic : AnalyticAt ℝ (moveField (G:=G) (m:=m)) 0 := by
  apply content_analytic shiftLinks_zero
  rintro ⟨i,k⟩; simp_rw [shiftLinks,Lattice.gauge,switchSite,encode_link,G.mat_mul,G.mat_inv]
  apply ContDiffAt.analyticAt
  have hx (j : Body 0 m) : ContDiffAt ℝ ω (fun x : Swatch G m => G.mat (G.lieExp (arm _ m 0 x.1 j))) 0 := G.exp_jet.contDiffAt.comp (f:=fun x : Swatch G m => (arm G m 0) x.1 j) (0:Swatch G m) (by fun_prop)
  have hy : ContDiffAt ℝ ω (fun x : Swatch G m => G.mat (G.lieExp (arm _ m 1 x.2 (i,coord k)))) 0 := G.exp_jet.contDiffAt.comp (f:=fun x : Swatch G m => (arm G m 1) x.2 (i,coord k)) (0:Swatch G m) (by fun_prop)
  exact ((hx _).mul hy).mul ((show G.Mat ≃L[ℝ] G.Mat from starL ℝ).contDiff.contDiffAt.comp _ (hx _))

lemma exp_ray (x : G.Color) : HasDerivAt (fun t : ℝ => G.mat (G.lieExp (t • x))) (G.colorMat x) 0 := by
  have he : HasFDerivAt (fun x => G.mat (G.lieExp x)) G.colorMat.toContinuousLinearMap ((0:ℝ) • x) := by
    rw [zero_smul]; exact G.expDiff_zero
  have hh : HasDerivAt (fun t : ℝ => t • x) x 0 := by simpa using! (hasDerivAt_id' (0:ℝ)).smul_const x
  exact he.comp_hasDerivAt 0 hh

def gradientA {R : Type} [CommRing R] (G : Gauge) (m : Side) : (Lines G m 0 → R) →ₗ[R] (Lines G m 1 → R) := LinearMap.pi (fun i => LinearMap.proj (φ:=fun _ : Lines G m 0 => R) (R:=R) (i.1+step (axisEquiv.symm i.2.1),vac,i.2.2)-LinearMap.proj (φ:=fun _ : Lines G m 0 => R) (R:=R) (i.1,vac,i.2.2))

lemma gradientC (p : BaseSites G m) (x : Site m) (i : Axis) : arm G m 1 (gradientA G m p) (x,coord i) = arm G m 0 p (x+step i,vac)-arm G m 0 p (x,vac) := by
  ext j; simp only [arm_apply,gradientA,LinearMap.pi_apply,LinearMap.sub_apply,show axisEquiv.symm (coord i)=i from axisEquiv.symm_apply_apply _]; rfl
lemma moveField_rate (p : Swatch G m) : fderiv ℝ moveField 0 p=p.2-gradientA G m p.1 := by
  let d := fderiv ℝ moveField 0 p
  let f (t : ℝ) := t • p
  have hf : Tendsto f (𝓝 0) (𝓝 0) := by
    unfold f; simpa using (show Continuous (fun t : ℝ => t • p) from by fun_prop).tendsto 0
  have he : ∀ᶠ t in 𝓝 0, input G m (moveField (f t)) = shiftLinks (f t) := hf.eventually moveField_germ
  have ht : HasDerivAt (moveField ∘ f) d 0 := Push.side _ moveField_analytic.differentiableAt p
  apply (arm G m 1).injective; funext ⟨x,i⟩; obtain ⟨a,rfl⟩ := axisEquiv.surjective i
  rw [coord_map]; apply G.colorMat_injective
  let L := ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : Body 1 m => G.Color) (x,coord a) ∘L (arm G m 1).toContinuousLinearMap
  have ha : HasFDerivAt (fun x => G.mat (G.lieExp x)) G.colorMat.toContinuousLinearMap (L (moveField (f 0))) := by
    rw [show f 0=0 by simp [f], moveField_zero,map_zero]; exact G.expDiff_zero
  have hh := ha.comp_hasDerivAt 0 (L.hasFDerivAt.comp_hasDerivAt 0 ht)
  have hw : HasDerivAt (fun t => G.mat (shiftLinks (f t) (x,a))) (G.colorMat (L d)) 0 := by
    refine hh.congr_of_eventuallyEq ?_
    filter_upwards [he] with t ht
    rw [← ht,encode_link]; rfl
  have hz (t) : G.mat (shiftLinks (f t) (x,a)) = G.mat (G.lieExp (t • arm G m 0 p.1 (x,vac))) * G.mat (G.lieExp (t • arm G m 1 p.2 (x,coord a))) * star (G.mat (G.lieExp (t • arm G m 0 p.1 (x+step a,vac)))) := by
    simp [shiftLinks,Lattice.gauge,switchSite,encode_link,f]
  simp_rw [hz] at hw
  refine hw.unique ?_
  have H := ((exp_ray (arm G m 0 p.1 (x,vac))).mul (exp_ray (arm G m 1 p.2 (x,coord a)))).mul (exp_ray (arm G m 0 p.1 (x+step a,vac))).star
  convert! H using 1
  simp only [map_sub,Pi.sub_apply, gradientC,Gauge.colorMat_skew,zero_smul,G.mat_lieExp_zero, G.mat_one,mul_one,one_mul,star_one,Pi.mul_apply]
  abel
end YM.Stationary
end

/-! # Pure real-mesh Ward from gauge & lower jets -/
noncomputable section
namespace YM.Stationary
open Function Lattice RG Exterior Wilson Precision Bloch Laurent Filter Finset
open Matrix (transpose mulVec of)
open scoped Matrix Topology ContDiff BigOperators NNReal Matrix.Norms.Frobenius
variable {G : Gauge} {n t : ℕ} {m : Side}

abbrev Quiets (F : Link G m → ℝ) (n : ℕ) := ∀ i : ℕ, i < n → 0 < i → iteratedFDeriv ℝ i F 0=0

def force (F : Link G m → ℝ) := (F ∘ moveField (G:=G) (m:=m)) =ᶠ[𝓝 0] (F ∘ Prod.snd (α:=BaseSites G m))

variable (F : Link G m → ℝ)

lemma adhesion (x : Fin n → Swatch G m) (h : force F) (hp : AnalyticAt ℝ F 0) (hz : Quiets F n) :
    iteratedFDeriv ℝ n F 0 (fun i => (x i).2-gradientA G m (x i).1)=iteratedFDeriv ℝ n F 0 fun i => (x i).2 := by
  have he := DFunLike.congr_fun ((h.iteratedFDeriv ℝ n).eq_of_nhds) x
  change iteratedFDeriv ℝ n (F ∘ _) 0 x=iteratedFDeriv ℝ n (F ∘ (ContinuousLinearMap.snd ℝ (BaseSites G m) (Link G m))) 0 x at he
  rw [quiet_comp _ moveField_analytic (by rw [moveField_zero]; exact hp)
    (by simpa only [moveField_zero] using hz), moveField_zero,wired _ (by rw [map_zero]; exact hp), map_zero] at he
  simp only [Function.comp_def,moveField_rate] at he; exact he

-- convert the coordinate planes, real-compatibility built into gradient formula
lemma adhesion_complex (x : Fin n → Phase (Lines G m 1)) (y : Fin n → Phase (Lines G m 0))
    (h : force F) (hp : AnalyticAt ℝ F 0) (hz : Quiets F n) :
    noteAt F n (fun i => x i-gradientA G m (y i))=noteAt F n x := by
  classical
  let K := Lines G m 1 ⊕ Lines G m 0
  let D : Phase K →ₗ[ℂ] Phase (Lines G m 1) := LinearMap.pi fun i => LinearMap.proj (Sum.inl i)
  let Y : Phase K →ₗ[ℂ] Phase (Lines G m 0) := LinearMap.pi fun i => LinearMap.proj (Sum.inr i)
  have he : (noteAt F n).compLinearMap (fun _ => D-gradientA G m ∘ₗ Y)=(noteAt F n).compLinearMap fun _ => D := by
    apply enlarge_unique; intro b
    let p (j : Fin n) : Swatch G m := (fun i => b j (Sum.inr i),fun i => b j (Sum.inl i))
    simp only [MultilinearMap.compLinearMap_apply, Function.comp_apply,LinearMap.sub_apply,LinearMap.comp_apply]
    rw [show (fun a => D (axes _) - _) = axes ∘ (fun i : Fin n => (p i).2-gradientA G m (p i).1) by
      funext i j; simp [gradientA,D,Y,p,axes],
      show (fun a : Fin n => D (axes (b a))) = axes ∘ (fun i => (p i).2) from rfl,
      note_real,note_real,Tensor.coeff,_root_.smul_apply,_root_.smul_apply,adhesion F p h hp hz]
  exact DFunLike.congr_fun he (fun i => Sum.elim (x i) (y i))

lemma note_kills (x : Fin n → Phase (Lines G m 1)) (y : Phase (Lines G m 0)) (i : Fin n)
    (h : force F) (hp : AnalyticAt ℝ F 0) (hz : Quiets F n) : noteAt F n (update x i (gradientA G m y))=0 := by
  have he := adhesion_complex F (update x i 0) (Pi.single i (-y)) h hp hz
  rw [show (fun a => update x i 0 a - gradientA G m ((Pi.single i (-y) : Fin n → Phase (Lines G m 0)) a))=update x i (gradientA G m y) from funext fun j => by
    by_cases h : j=i <;> simp [h], (noteAt F n).map_coord_zero (m:=update x i 0) i (by rw [update_self])] at he
  exact he

lemma gradient_wave (i : Site m) (k : G.ColorIndex) : gradientA G m (relay i (vac,k)) =
    ∑ j : TypeFace 1, symbol 0 (mon i) j vac • relay i (j,k) := by
  ext1 ⟨x,a,b⟩; obtain ⟨a,rfl⟩ := axisEquiv.surjective a
  rw [Finset.sum_apply, sum_eq_single (coord a)]
  · simp only [coord_map,gradientA,LinearMap.pi_apply,show axisEquiv.symm (coord a)=a from axisEquiv.symm_apply_apply _,LinearMap.sub_apply,LinearMap.proj_apply]
    have he : symbol 0 (mon i) (coord a) vac = Complex.exp (Complex.I * mon i a)-1 := by
      unfold symbol wedge Exterior.q
      rw [Matrix.sum_apply, sum_eq_single a]; rotate_left
      · intro k _ h; simp [Exterior.left,coord,h]
      · simp
      simp [Exterior.left,coord,vac_only,parity,pre,Finset.filter_singleton]
    rw [he]; by_cases h : b=k <;> simp [relay,tune,cell_step,h]; ring
  · intro j _ h; simp [relay,tune,Ne.symm h]
  simp

lemma ward_stripe (x : Fin (t+1) → Site m) (hx : ∑ i,x i=0)
    (w : Ink G (t+1)) (i : Run (t+1)) (j : Fin (t+1))
    (h : force F) (hp : AnalyticAt ℝ F 0) (hz : Quiets F (t+1)) :
    ∑ k : TypeFace 1, symbol 0 (plotted (outphase x) j) k vac * noteAt F _ (glyph x w (update i j k))=0 := by
  have he := note_kills F (glyph x w i) (relay (x j) (vac,w j)) j h hp hz
  rw [gradient_wave] at he
  rw [MultilinearMap.map_update_sum] at he
  rw [waved_symbol x hx]; apply Eq.trans _ he
  refine sum_congr rfl fun k _ => ?_
  have hu : glyph x w (update i j k)=update (glyph x w i) j (relay (x j) (k,w j)) := funext fun l => by by_cases h : l=j <;> simp [h,glyph]
  rw [hu]; simp
end YM.Stationary
end

/-!
# Constant color rotation and global uncut symmetries
-/
noncomputable section
namespace YM.Stationary
open Function Lattice RG Exterior Wilson Precision Bloch Laurent Filter Finset
open Matrix (transpose mulVec of)
open scoped Matrix Topology ContDiff BigOperators NNReal Matrix.Norms.Frobenius
variable {G : Gauge} {n t : ℕ} {m : Side} (u : G.El)

def constantColor : fieldDir G m 1 →ₗ[ℝ] fieldDir G m 1 := LinearMap.pi (fun p => G.adjoint u ∘ₗ LinearMap.proj p)
def stain : Link G m →L[ℝ] Link G m := (arm _ _ _).symm.toContinuousLinearMap ∘L
    LinearMap.toContinuousLinearMap (constantColor u) ∘L (arm G m 1).toContinuousLinearMap
lemma stain_cons (b : Link G m) : Lattice.gauge (fun _ => u) (input G m b)=input G m (stain u b) := by
  funext ⟨x,i⟩; apply G.mat_injective
  simp only [Lattice.gauge,G.mat_mul,G.mat_inv,encode_link,stain,ContinuousLinearMap.comp_apply]
  simp only [ContinuousLinearEquiv.coe_coe,(arm G m 1).apply_symm_apply]
  change _ = G.mat (G.lieExp (G.adjoint u _))
  rw [G.mat_lieExp,G.mat_lieExp,G.mat_adjoint,G.exp_conjugate]; rfl

def Stained (G : Gauge) (f : Link G m → ℝ) : Prop := ∀ u : G.El, f ∘ (stain u) =ᶠ[𝓝 0] f

section colors

def glass : Matrix G.ColorIndex G.ColorIndex ℝ := LinearMap.toMatrix'
    ((WithLp.linearEquiv 2 ℝ (G.ColorIndex → ℝ)).toLinearMap ∘ₗ
          G.adjoint u ∘ₗ (WithLp.linearEquiv 2 ℝ (G.ColorIndex → ℝ)).symm.toLinearMap)

def shine : Phase (Lines G m 1) →ₗ[ℂ] Phase (Lines G m 1) := LinearMap.pi (fun p => ∑ i,
    (glass u p.2.2 i : ℂ) • LinearMap.proj (p.1,p.2.1,i))
lemma matrices_real (a : G.Color) : (WithLp.ofLp (G.adjoint u a)) = glass u *ᵥ WithLp.ofLp a := by rw [glass, LinearMap.toMatrix'_mulVec]; rfl
lemma shine_entry (x : Phase (Lines G m 1)) (i : Lines G m 1) : shine u x i = ∑ j, (glass u i.2.2 j:ℂ)*x (i.1,i.2.1,j) := by simp [shine]
lemma shine_real (v : Link G m) : axes (stain u v)=shine u (axes v) := by
  funext ⟨x,i,j⟩; rw [shine_entry]
  unfold axes; rw [← arm_apply G m 1 (stain u v) x i j,stain,ContinuousLinearMap.comp_apply]; simp only [ContinuousLinearEquiv.coe_coe,(arm _ _ _).apply_symm_apply]

  change (((WithLp.ofLp (G.adjoint u (arm G m 1 v (x,i)))) j:ℝ):ℂ) = _
  rw [matrices_real,Matrix.mulVec,dotProduct]; push_cast; rfl
lemma prism_note (F : Link G m → ℝ) (hf : AnalyticAt ℝ F 0) (h : Stained G F) (v : Fin n → Phase (Lines G m 1)) :
    noteAt F n (shine u ∘ v) = noteAt F n v := by
  have ht := DFunLike.congr_fun (note_comp _ _ (shine_real u) hf n) v
  refine ht.symm.trans ?_
  rw [noteAt, beat, ((h u).iteratedFDeriv ℝ n).eq_of_nhds]; rfl
end colors

section film
variable {F : Link G m → ℝ} (p : Fin (t+1) → Site m) (i : Run (t+1))

def filmTone (a : Fin (t+1) → G.Color) : Fin (t+1) → Phase (Lines G m 1) := fun k => ∑ j : G.ColorIndex, (a k j:ℂ) • relay (p k) (i k,j)
lemma film_read (a : Fin (t+1) → G.Color) (k x j b) : filmTone p i a k (x,j,b)=
    if i k=j then (a k b:ℂ) * cell (p k) x else 0 := by
  unfold filmTone; rw [Finset.sum_apply]
  simp only [relay,tune,Pi.smul_apply,smul_eq_mul]; by_cases h : i k=j
  · simp_rw [h]; simp [Pi.single_apply]
  rw [if_neg h]; apply Finset.sum_eq_zero; intro a _; simp [Ne.symm h]
lemma film_tilt (a : Fin (t+1) → G.Color) : filmTone p i (fun j => G.adjoint u (a j))=shine u ∘ filmTone p i a := by
  funext b ⟨x,y,j⟩
  rw [Function.comp_apply,shine_entry,film_read]; simp_rw [film_read]; split
  next h =>
    change ((WithLp.ofLp (G.adjoint u (a b)) j:ℝ):ℂ)*cell _ _ = _
    rw [matrices_real,Matrix.mulVec,dotProduct]
    push_cast; rw [Finset.sum_mul]; simp [*,mul_assoc]
  simp_all only [mul_zero, Finset.sum_const_zero]
lemma film_test (F : Link G m → ℝ) (a : Fin (t+1) → G.Color) : noteAt F _ (filmTone p i a) =
    ∑ v : Ink G (t+1), noteAt F _ (glyph p v i) * ((∏ j, a j (v j): ℝ):ℂ) := by
  unfold filmTone; rw [MultilinearMap.map_sum]; apply sum_congr rfl; intro j _
  apply Eq.trans ((noteAt F (t+1)).map_smul_univ (fun k => (↑(a k (j k)):ℂ)) (glyph p j i))
  rw [smul_eq_mul,mul_comm]
  congr 1; push_cast; rfl
lemma film_proof (hf : AnalyticAt ℝ F 0) (h : Stained G F) : fixedInks G (fun v => noteAt F (t+1) (glyph p v i)) := by
  have ht (u : G.El) (v : Fin (t+1) → G.Color) : noteAt F _ (filmTone p i (fun j => G.adjoint u (v j)))=noteAt F _ (filmTone p i v) := by rw [film_tilt u,prism_note u F hf h]
  simp_rw [film_test] at ht
  constructor <;> intro u v
  · simpa only [Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero] using congr_arg Complex.re (ht u v)
  simpa only [Complex.im_sum,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_add] using congr_arg Complex.im (ht u v)
end film
end YM.Stationary
end

/-!
# Transfer to (one and the same) symbol

Independent of the holomorphic-integral computation. Only uses analytic estimates
when giving continuity and periodicity, and the comparison on the selected real
mesh. Use n=2 again with smaller remainder after choosing coupling term.
-/
noncomputable section
namespace YM.Stationary
open Function Lattice RG Exterior Wilson Precision Bloch Laurent Filter Finset
open Matrix (transpose mulVec of)
open scoped Matrix Topology ContDiff BigOperators NNReal
variable {G : Gauge} {n t : ℕ}

abbrev cents (m : Side) : ℝ := Fintype.card (Site m)
lemma cents_pos {m : Side} : 0 < cents m := by unfold cents; exact_mod_cast Fintype.card_pos

def standing (m : ℕ → Side) (F : ∀ i, Link G (m i) → ℝ) (p : ∀ i, Fin (t+1) → Site (m i)) (x : Ink G (t+1)) (b : Run (t+1)) (i : ℕ) :=
    (cents (m i):ℂ)⁻¹ * noteAt (F i) _ (glyph (p i) x b)

lemma projections_roll {p q : Space t} (h : rolls p q) (i : Fin (t+1)) : rolls (plotted p i) (plotted q i) := by
  obtain ⟨d,rfl⟩ := h
  refine Fin.cases ?_ (fun i => ?_) i <;> simp only [plotted,Fin.cons_zero,Fin.cons_succ]
  · refine ⟨missing d,?_⟩
    ext1 a
    simp [missing,Finset.sum_apply,reciprocal, Finset.mul_sum,sum_add_distrib]; abel
  exact ⟨d ∘ strand i,rfl⟩
lemma rolls_symbol {p q : Momentum} (h : rolls p q) (n) : symbol n p=symbol n q := by
  simp only [← reading,Row.read,Laurent.read,h.exp]
lemma reflection_negative {m : Side} (p : Fin (t+1) → Site m) : rolls (outphase (-p)) (-(outphase p)) := rolls_keys fun i => by
  apply rolls_of_mode; intro x
  change mode (mon (-(p i.succ))) x=mode (-(mon (p i.succ))) x
  rw [← cell_wrap,mode_inverse, ← cell_wrap]; rw [cell_duality,cell_inverse,cell_duality]
lemma glyph_flips {m : Side} (p : Fin (t+1) → Site m) i (b : Ink G (t+1)) :
    glyph (-p) b i=star (glyph p b i) := by
  funext a ⟨s,u,x⟩
  simp only [glyph,Pi.neg_apply,Pi.star_apply,relay,tune,star_mul,Complex.star_def,cell_bar]
  rw [cell_duality (-(p a)),cell_inverse,cell_duality]
  by_cases h : (u,x)=(i a,b a) <;> simp [*]

section service
variable {m : ℕ → Side} {η A : ℝ} {ε : ℕ → ℝ} {F : ∀ i, Link G (m i) → ℝ} {f : Picture G t}

lemma harvest (h : ∀ i j, Firm η A (f i j)) (hp : ∀ p, Recorded f (F p) (cents (m p)*ε p)) (hε : Tendsto ε atTop (𝓝 0))
    (r : Corn (Keys t)) (p : ∀ i, Fin (t+1) → Site (m i)) (u : ℕ → Space t)
    (hx : Tendsto u atTop (𝓝 (axes r))) (hy : ∀ i, ∑ j,p i j=0 ∧ rolls (outphase (p i)) (u i))
    (x : Ink G (t+1)) (b : Run (t+1)) : Tendsto (standing m F p x b) atTop (𝓝 (f x b (axes r))) := by
  have hk := h x b
  have he (i) : ‖standing m F p x b i - f x b (u i)‖ ≤ ε i := by
    obtain ⟨h1,h2⟩ := hy i
    have hc : 0<cents (m i) := cents_pos; have hn : (cents (m i):ℂ) ≠ 0 := by exact_mod_cast hc.ne'
    have hb := hp i (p i) x b
    rw [collected,if_pos h1,h2.apply hk (hk.in_range (out_real _)), show (↑(Fintype.card _):ℂ)=(cents (m i):ℂ) by simp [cents]] at hb
    unfold standing
    rw [show (cents (m i):ℂ)⁻¹ * _-f x b (u i)=(cents (m i):ℂ)⁻¹ * (noteAt (F i) (t+1) (glyph (p i) x b)-(cents (m i):ℂ)*f x b (u i)) by rw [mul_sub,inv_mul_cancel_left₀ hn], norm_mul,norm_inv,Complex.norm_real,Real.norm_of_nonneg hc.le]
    exact (mul_le_mul_of_nonneg_left hb (by positivity : 0≤(cents (m i))⁻¹)).trans_eq (inv_mul_cancel_left₀ hc.ne' _)
  have ht : Tendsto ((standing m F p x b)-(f x b) ∘ u) atTop (𝓝 0) := tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero (fun _ => norm_nonneg _) he hε)
  have hw := ht.add ((hk.analytic (hk.in_range (axes_real r))).continuousAt.tendsto.comp hx)
  simpa using! hw

private lemma plotted_cont (a : Fin (t+1)) : Continuous (fun p : Space t => plotted p a) := by
  refine Fin.cases ?_ (fun a => ?_) a <;> simp only [plotted,Fin.cons_zero,Fin.cons_succ]
  · apply continuous_pi; intro k; simp only [missing,Pi.neg_apply,Finset.sum_apply,Function.comp_apply]; fun_prop
  exact continuous_pi fun i => continuous_apply _


/-- Transfers of all output lift conditions except ray vanishing orders.
Uniformity from `Recorded`. `Quiets` does not require equality of constants. -/
theorem withdrew (hν : Tendsto (fun i => (m i).val) atTop atTop)
    (hd : Tendsto ε atTop (𝓝 0)) (h : ∀ i j, Firm η A (f i j)) (hp : ∀ p, Recorded f (F p) (cents (m p)*ε p))
    (he : ∀ p, AnalyticAt ℝ (F p) 0) (ha : ∀ p, Stained G (F p)) (hs : ∀ p, force (F p))
    (hΦ : ∀ p, Quiets (F p) (t+1)) : Features f η A := by
  constructor; exact h
  · intro x r i b
    obtain ⟨p,u,H,U⟩ := fleet m hν (axes r) (axes_real r)
    have hg (v : TypeFace 1) : Tendsto
        (fun y => symbol 0 (plotted (u y) i) v vac * standing m F p x (update b i v) y)
        atTop (𝓝 (symbol 0 (plotted (axes r) i) v vac * f x (update b i v) (axes r))) := by
      apply Tendsto.mul _ (harvest h hp hd r p u H U _ _)
      have ht : Continuous (fun z : Momentum => symbol 0 z v vac) := by simp only [symbol, Exterior.q,wedge,Matrix.sum_apply,Matrix.smul_apply]; fun_prop
      exact ((ht.comp (plotted_cont i)).continuousAt.tendsto.comp H)
    have hv := tendsto_finsetSum univ fun v _ => hg v
    refine tendsto_nhds_unique hv (?_)
    have hy (i' : ℕ) := ward_stripe (F i') (p i') (U i').1 x b i (hs i') (he i') (hΦ i')
    refine tendsto_const_nhds.congr' (Eventually.of_forall fun i' => ?_)
    symm
    simp_rw [← rolls_symbol (projections_roll (U i').2 i)]
    unfold standing; simp_rw [mul_left_comm _ (cents (m i'):ℂ)⁻¹]; rw [← Finset.mul_sum,hy i',mul_zero]
  · intro x i a hb
    let r : Corn _ := fun j => (a j).re; have hr : a=axes r := (axes_of_real hb).symm
    obtain ⟨p,u,H,U⟩ := fleet m hν (axes r) (axes_real r)
    have hy := harvest h hp hd r p u H U x i
    have hh : ∀ j, ∑ k,(-p j) k=0 ∧ rolls (outphase (-p j)) (-u j) := by
      intro j; refine ⟨?_,(reflection_negative _).trans (U j).2.neg⟩
      simp only [Pi.neg_apply,sum_neg_distrib,(U j).1,neg_zero]
    have hz := harvest h hp hd (-r) (fun i => -p i) (fun i => -u i) (axes_flip r |>.symm ▸ H.neg) hh x i
    have ht := hz.star
    rw [hr]; rw [axes_flip] at ht
    refine tendsto_nhds_unique (?_ : Tendsto (standing m F p x i) atTop _) hy
    convert ht using 1; ext1 z
    simp only [standing,star_mul,glyph_flips,← note_fixed]; simp [mul_comm]
  intro r i
  obtain ⟨p,u,H,U⟩ := fleet m hν (axes r) (axes_real r)
  have hv j : fixedInks G (fun x => standing m F p x i j) := by
    have hw := film_proof (p j) i (he j) (ha j)
    let k := (cents (m j))⁻¹
    have hI : (cents (m j):ℂ)⁻¹=(k:ℂ) := by simp [k]
    unfold standing
    rw [hI]; constructor
    · simpa only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] using!
        (paints G _).smul_mem k hw.1
    simpa only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero] using!
        (paints G _).smul_mem k hw.2
  have hy x := harvest h hp hd r p u H U x i
  have hx := (paints G (t+1)).closed_of_finiteDimensional
  refine ⟨hx.mem_of_tendsto (b:=atTop (α:=ℕ)) (tendsto_pi_nhds.mpr (fun x => ?_)) (Eventually.of_forall (fun j => (hv j).1)),
    hx.mem_of_tendsto (b:=atTop (α:=ℕ)) (tendsto_pi_nhds.mpr (fun x => ?_)) (Eventually.of_forall (fun j => (hv j).2))⟩
  exact Complex.continuous_re.continuousAt.tendsto.comp (hy x)
  exact Complex.continuous_im.continuousAt.tendsto.comp (hy x)
end service
end YM.Stationary
end
