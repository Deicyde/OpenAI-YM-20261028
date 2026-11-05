import YM.MultiNext.SIGNED_SOURCE_CONTINUATION.Operator
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Dissent
import YM.UVNext.PRICED_KERNELS.Read



/-!
# Licenses before L: linear tree and principal routes for E

Whole normalized arguments about the actual projected anchor; one taper
of order TWO in the fine gauge, otherwise just hold the tree-gauge cost
without a pre-L power loss even on far-away link reads. Polynomial weights
cross parent/spatial conventions including residual crossings. Pre-L costs
behind TAPS/JHs and Towers.Deep from the same epoch, not replacing
these kernels by asymptotic free aliases. No stencil truncation.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Heir
open Function Filter Lattice Wilson Pressure Precision RG Tree Matrix Next Next.Free Next.SectorChange
  Exterior Laurent Bloch Bid UVNext.PricedKernels MultiNext.SignedSource
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {c f n : Side} {Pt : Teller G} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}

section maps
variable (T) (F)
def pegs (A : Matrix (Body 1 f) (Body 1 c) ℝ) : Directions G c →L[ℝ] (Site f → G.Color) := LinearMap.toContinuousLinearMap {
  toFun v i := WithLp.toLp 2 (fun j : G.ColorIndex => (straighten S F A *ᵥ parts G 1 (Flat.labels v) j) (i,Exterior.vac))
  map_add' a b := by funext i; ext j; exact congr_fun (Matrix.mulVec_add (straighten S F A) (parts G 1 (Flat.labels a) j) (parts G 1 (Flat.labels b) j)) (i,Exterior.vac)
  map_smul' t a := by funext i; ext j; exact congr_fun (Matrix.mulVec_smul (straighten S F A) (t:ℝ) (parts G 1 (Flat.labels a) j)) (i,Exterior.vac) }

abbrev main := installed S.ratio T.R.A0
def route : Directions G c →L[ℝ] Directions G f := shaped (main T)
def woody : Directions G c →L[ℝ] Directions G f := shaped (extracted S F (main T))

theorem woody_eq : woody T F=treeMap T F+carriedCopy S := by unfold treeMap woody main; abel
lemma harvest (u : Directions G c) (i : Bond f) : pegs F (main T) u i.1 + woody T F u i - pegs F (main T) u (i.1+step i.2) = route T u i := by
  ext j
  change (straighten S F (main T) *ᵥ parts G 1 (Flat.labels u) j) (i.1,Exterior.vac)+ (extracted S F (main T) *ᵥ parts G 1 (Flat.labels u) j) (i.1, Exterior.coord i.2)-
    (straighten S F (main T) *ᵥ parts G 1 (Flat.labels u) j) (i.1+step i.2,Exterior.vac) = ((main T) *ᵥ parts G 1 (Flat.labels u) j) _
  rw [extracted,Matrix.add_mulVec,Pi.add_apply,← Matrix.mulVec_mulVec,Exterior.d_sites]; abel

lemma roll_as (v : Directions G c) (K : Matrix (Body 1 f) (Body 1 c) ℝ) (i : Bond f) : shaped K v i=Newt.load K (Flat.labels v) (i.1,Exterior.coord i.2) := by
  ext j; change (K *ᵥ parts G 1 (Flat.labels v) j) _ = _; unfold Newt.load parts Matrix.mulVec dotProduct; simp
lemma peg_as (v : Directions G c) (K : Matrix (Body 1 f) (Body 1 c) ℝ) (i : Site f) : pegs F K v i=Newt.load (straighten S F K) (Flat.labels v) (i,Exterior.vac) := by
  ext j; change (straighten S F K *ᵥ parts G 1 (Flat.labels v) j) _ = _; unfold Newt.load parts Matrix.mulVec dotProduct; simp
end maps

variable {r α C M η : ℝ} {b j : ℕ}

abbrev spine (b : ℕ) (x o : Site n) : ℝ := (1+(separation x o:ℝ))^b
lemma spine_one (b : ℕ) (x o : Site n) : 1≤spine b x o := one_le_pow₀ (by simp)
lemma spine_pos (b : ℕ) (x o : Site n) : 0 < spine b x o := zero_lt_one.trans_le (spine_one b x o)
lemma spine_self (b : ℕ) (x : Site n) : spine b x x=1 := by simp [spine]
abbrev Limb (b : ℕ) (o : Site c) (v : Directions G c) (t : ℝ) := ∀ i:Bond c, ‖v i‖ ≤ t * spine b i.1 o
private lemma ridge (b : ℕ) {α : ℝ} (hα : 0<α) : ∃ Z : ℝ, 0<Z ∧ ∀ {c f : Side} (g : Ratio c f) (j : Site c) (o x : Site f),
    spine b j (g.parent o) ≤ Z*spine b x o*gained (α/g.count.val) x (g.embed j) := by
  obtain ⟨C,hC,H⟩ := Newt.length_mom b hα
  refine ⟨Real.exp α * C * 2^b,by positivity,?_⟩
  intro c f g j o x
  have h := Corona.foreshorten g x o
  have h' := Corona.foreshorten g x (g.embed j)
  rw [g.embed_parent,separation_comm (g.parent x) j] at h'
  let L : ℝ := g.count.val; have hL : 1 ≤ L := Nat.one_le_cast.mpr g.count.property
  let R : ℝ := separation j (g.parent x)
  have hs : (separation (g.parent x) (g.parent o):ℝ) ≤ separation x o + (1:ℝ) := by
    have h : L*↑(separation (g.parent x) (g.parent o)) ≤ separation x o+L := by unfold L; exact_mod_cast h
    have hx : 0≤(separation x o:ℝ) := Nat.cast_nonneg _
    nlinarith only [h,hL,hx]
  have hx : L*R ≤ (separation x (g.embed j):ℝ)+L := by unfold L R; exact_mod_cast h'
  have ht : 1+(separation j (g.parent o):ℝ) ≤ 2*((1+R)*(1+(separation x o:ℝ))) := by
    have he : (separation j (g.parent o):ℝ) ≤ R+(separation (g.parent x) (g.parent o):ℝ) := by unfold R; exact_mod_cast separation_triangle j (g.parent x) (g.parent o)
    have hp : 0≤R := Nat.cast_nonneg _
    nlinarith [Nat.cast_nonneg (α:=ℝ) (separation x o)]
  have he : Real.exp (α*R) ≤ Real.exp α*gained (α/L) x (g.embed j) := by
    unfold gained; rw [← Real.exp_add]; apply Real.exp_monotone
    field_simp; linarith only [hx]
  have hz := Real.exp_pos (α*R)
  unfold spine
  calc
    _ ≤ (2*((1+R)*(1+(separation x o:ℝ))))^b := pow_le_pow_left₀ (by positivity) ht _
    _ = 2^b*((1+R)^b * spine b x o) := by simp [mul_pow]
    _ ≤ 2^b*((Real.exp α*gained (α/L) x (g.embed j) * C)*spine b x o) := by
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ((H _).trans (mul_le_mul_of_nonneg_right he hC.le)) (spine_pos ..).le) (by positivity)
    _ = _ := by unfold spine L; ring

private lemma collect_load {a : ℕ} (K : Matrix (Body a f) (Body 1 c) ℝ) (hk : Annuity (site f (TypeFace a)) (parent S.ratio (TypeFace 1)) K r C)
    (v : Directions G c) (i : Body a f) (hM : 0≤M) (hv : ∀ j: Bond c, ‖v j‖ ≤ M*gained r i.1 (S.ratio.embed j.1)) :
    ‖Newt.load K (Flat.labels v) i‖ ≤ M*C := by
  unfold Newt.load; apply (norm_sum_le ..).trans; simp_rw [norm_smul]; refine le_trans (Finset.sum_le_sum (g:=fun j => M*(gained r i.1 (S.ratio.embed j.1) * |K i j|)) (fun j _ => ?_)) ?_
  · exact (mul_le_mul_of_nonneg_left (hv _) (norm_nonneg _)).trans_eq (by dsimp only [Real.norm_eq_abs]; ring)
  rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (hk i) hM

private lemma annuities (Pt : Teller G) : ∃ D : ℝ, 0<D ∧ ∀ {c f : Side} (S : StepData c f) (T : Tube G S), Pt.Funds S T → ∀ F : Forest S.ratio,
    let pass {a} := Annuity (site f (TypeFace a)) (parent S.ratio (TypeFace 1)) (s:=Pt.η/S.patch.L.val)
    pass (extracted S F (main T)) D ∧ pass (straighten S F (main T)) D ∧ pass (main T) D := by
  let Z := stackFee Pt.η |Pt.C| (TypeFace 1); let C := hikeC Pt.j Pt.η
  have hz := stackFee_nonneg Pt.η (TypeFace 1) (abs_nonneg Pt.C); have hc := hikeC_pos Pt.j Pt.η
  let U := 1+dC 0 Pt.η * C
  have hu : 1 ≤ U := le_add_of_nonneg_right (mul_nonneg (dC_nonneg ..) hc.le)
  let D := 1+(U+C)*Z; refine ⟨D,by unfold D; positivity,?_⟩
  intro c f S T h F pass
  have H := (h.crosses.2.2.2 [] (by simp)).1
  let L := (S.patch.L.val:ℝ)
  have hL : 1 ≤ L := Nat.one_le_cast.mpr S.patch.L.property
  have ht : T.R.A0.strip Pt.η (Pt.C/L) := by simpa only [advanceC,List.length_nil,Nat.add_zero,pow_one] using H
  have hZ : pass (main T) (Z/L) := (Annuity.paid_cross ht Pt.width.le).cut le_rfl (by unfold Z stackFee; rw [mul_div_assoc, mul_div_assoc]; gcongr; exact le_abs_self _)
  have hC : hikeC S.patch.J Pt.η = C := h.atStep ▸ rfl
  have he : U*Z ≤ D ∧ C*Z≤D := by unfold D; constructor <;> nlinarith [mul_nonneg (zero_le_one.trans hu) hz, mul_nonneg hc.le hz]
  exact ⟨(extract_price S Pt.η Pt.width.le F (main T) Z hz hZ).cut le_rfl (hC.symm ▸ he.1),
    (straight_price S Pt.η Pt.width.le F (main T) Z hz hZ).cut le_rfl (hC.symm ▸ he.2), hZ.cut le_rfl ((div_le_self hz hL).trans ((le_mul_of_one_le_left hz hu).trans he.1))⟩

structure Matins (T : Tube G S) (F : Forest S.ratio) (b : ℕ) (M C : ℝ) : Prop where
  stage (v : Directions G c) (i : Bond f) (o : Site f) {t : ℝ} : 0 ≤ t → Limb b (S.ratio.parent o) v t → ‖woody T F v i‖ ≤ C*t*spine b i.1 o
  norm_phi : ‖pegs F (main T) (G:=G)‖ ≤ C
  taper (B : BudgetPoint) (X : Support f) (o : Site f) (v : Directions G c) : B.power=b → Limb b (S.ratio.parent o) v (M*B.threshold) →
    Banjo.Promise 2 C ((S.patch.L.val:ℝ)⁻¹) B o X (route T v)

private lemma accreditation (h : Pt.Funds S T) : T.R.Deep Pt.η Pt.C 2 := ⟨h.crosses.1,h.crosses.2.1,h.crosses.2.2.1,fun _ hl => h.crosses.2.2.2 _
    (hl.trans (by have := h.atStep; have := S.patch.order_cut; omega))⟩

theorem coaches (Pt : Teller G) (b : ℕ) (M : ℝ) (hb : 2 ≤ b) (hM : 0<M) : ∃ C : ℝ, 1≤C ∧
    ∀ {c f : Side} (S : StepData c f) (T : Tube G S), Pt.Funds S T → ∀ (F : Forest S.ratio), Matins T F b M C := by
  obtain ⟨D,hD,H⟩ := annuities Pt
  obtain ⟨Z,hZ,h⟩ := ridge b Pt.width
  obtain ⟨Q,hq,hQ⟩ := Newt.row_home G Pt.width Pt.C 2 b
  obtain ⟨Y,hy,hY⟩ := Newt.canal G 2 b hb
  have h0 : 0 ≤ M*Y*Q := by positivity
  let C := 1+D+Z*D+M*Y*Q; have hC : 1 ≤ C := by unfold C; nlinarith
  refine ⟨C,hC, fun S T ht F => ?_⟩
  obtain ⟨h1,h2,h3⟩ := H S T ht F
  let A := S.ratio
  have hL : 1 ≤ (S.patch.L.val:ℝ) := Nat.one_le_cast.mpr S.patch.L.property
  constructor
  · intro v i o t h0 hv; rw [woody,roll_as]; apply (collect_load _ h1 v (i.1,Exterior.coord i.2) (M:=t*(Z*spine b i.1 o))
      (mul_nonneg h0 (mul_pos hZ (spine_pos ..)).le) (fun j => (hv j).trans (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (h A ..) h0))).trans
    have he : Z*D≤C := by unfold C; nlinarith
    rw [show t*(Z*spine b i.1 o)*D = Z*D*t*spine b i.1 o by ring]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right he h0) (spine_pos ..).le
  · apply ContinuousLinearMap.opNorm_le_bound _ (zero_le_one.trans hC)
    intro v; refine (pi_norm_le_iff_of_nonneg (by positivity : 0≤C*‖v‖)).mpr fun i => ?_; rw [peg_as]; apply (collect_load _ h2 v (i,Exterior.vac) (norm_nonneg v) (fun j => ?_)).trans
    · rw [mul_comm]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); unfold C; nlinarith
    exact (norm_le_pi_norm ..).trans (le_mul_of_one_le_right (norm_nonneg _) (Real.one_le_exp (by have := Pt.width; positivity)))
  intro B X o v hB hv; let y := M⁻¹ • Flat.labels v
  have hpt i : ‖y i‖ ≤ B.threshold * spine b i.1 (A.parent o) := by
    unfold y; rw [Pi.smul_apply,norm_smul_of_nonneg (inv_pos.mpr hM).le]; exact (inv_mul_le_iff₀ hM).mpr ((hv _).trans_eq (mul_assoc ..))
  obtain ⟨w,hf,hg,hw⟩ := hY _ X o B _ _ _ hB hL (zero_le_one.trans hq)
    (hQ _ _ A _ (accreditation ht) B o S.patch.odd_side hB y hpt)
  let N : ℝ := S.patch.L.val
  refine ⟨fun i => M • w i,?_,fun i => ⟨by positivity,fun j => ?_⟩,fun i hi => ?_⟩
  · rw [← Finset.smul_sum,← hf]
    funext i; rw [route,roll_as,Pi.smul_apply]; change Newt.load _ _ _=M • Newt.load _ y _; unfold Newt.load y; rw [Finset.smul_sum]; exact Finset.sum_congr rfl fun j _ => by rw [smul_comm M,Pi.smul_apply,smul_inv_smul₀ hM.ne']
  · change ‖M • w i j‖ ≤ _; rw [norm_smul_of_nonneg hM.le]; refine (mul_le_mul_of_nonneg_left ((hg i).2 j) hM.le).trans ?_
    have he : M*(Y*Q) ≤ C := by unfold C; nlinarith
    calc
      _ = (M*(Y*Q)*N⁻¹^(i.val+1))*Lyre.width B o j := by unfold N; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right he (by unfold N; positivity)) (Lyre.width_pos ..).le
  rw [Mom.screen, map_smul]
  exact (Mom.Maps o X (i.val+1)).smul_mem _ (hw i hi)
end YM.PhysicalNext.JointLoad.Heir
