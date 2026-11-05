import YM.RG08.Fields.Mission

/-! # Puncture-laurent budgeting with arbitrary coarse p, all aliases.
Budget pair arithmetic for kbulk. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Drift
open Function Filter Set Lattice Wilson RG Exterior Precision Next.Free
open Laurent Bloch Matrix Work.F08
open scoped Topology BigOperators
variable {j n : ℕ} {k : ℝ}

lemma pineNorm {p : Momentum} (hp : p∈baseCube) : ‖p‖≤ domainRadius :=
    (pi_norm_le_iff_of_nonneg domainRadius_pos.le).mpr (fun _=> zone_in_disk p (mem_cube_real (base_subset_realCube zone_pos hp) zone_pos) _)
lemma aliasP_bound (L : Side) (l : Site L) {p} (hp : p∈baseCube) : ‖p‖ ≤ L.val*‖aliasAt p l‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i=> ?_
  let y : ℤ := lift l i
  have hA : ((p i).re:ℂ)=p i := by
    apply Complex.ext <;> simp [(physical_iff _|>.1 hp.1) i]
  have hx : ‖p i‖ ≤ Real.pi := hA ▸ (by rw [Complex.norm_real]; exact hp.2 i)
  have hL : 0<(L.val:ℝ):= by positivity
  refine le_trans ?_ (mul_le_mul_of_nonneg_left (norm_le_pi_norm (aliasAt p l) i) hL.le)
  rw [alias_value,norm_div, Complex.norm_natCast, mul_div_cancel₀ _ hL.ne']
  change ‖p i‖ ≤ ‖p i + 2 *(Real.pi:ℂ)* (y:ℂ)‖
  by_cases hy : y=0
  · simp [hy]
  have hb : (1:ℝ) ≤ y.natAbs := by exact_mod_cast (show 1≤y.natAbs by omega)
  have ha : ‖(2:ℂ)* (Real.pi:ℂ)*(y:ℂ)‖=2*Real.pi*y.natAbs := by
    simp only [norm_mul,Complex.norm_intCast, Complex.norm_real,Real.norm_eq_abs,abs_nat,abs_of_pos Real.pi_pos]
    norm_num
  have hm := norm_sub_le (p i + 2*(Real.pi:ℂ)*(y:ℂ)) (p i); rw [add_sub_cancel_left,ha] at hm
  nlinarith [Real.pi_pos]

def rim (p : Momentum) := max 1 (‖p‖⁻¹)
lemma rim_one (p : Momentum) : 1 ≤ rim p := le_max_left ..
lemma rim_live (p : Momentum) : 0 < rim p := zero_lt_one.trans_le (rim_one _)
lemma rim_alias (L : Side) (l : Site L) {p} (hp : p∈baseCube) (he : p≠0) : rim (aliasAt p l) ≤ L.val * rim p := by
  have hv : 0 < (L.val:ℝ) := by positivity
  have hx := aliasP_bound L l hp
  have he := norm_pos_iff.mpr he
  have hu : 0<‖aliasAt p l‖ := (mul_pos_iff_of_pos_left hv).mp (he.trans_le hx)
  refine max_le ?_ ?_
  · exact (rim_one p).trans (le_mul_of_one_le_left (rim_live _).le (by exact_mod_cast L.property))
  apply le_trans _ (mul_le_mul_of_nonneg_left (le_max_right ..) hv.le)
  apply le_of_mul_le_mul_right _ (inv_pos.mpr hv)
  rw [mul_comm (L.val:ℝ),mul_assoc,mul_inv_cancel₀ hv.ne',mul_one,← _root_.mul_inv_rev]
  exact (inv_le_inv₀ (mul_pos hv hu) he).2 hx

section Budget
variable {I : Type*} (Z : I→ℝ) (w : I→Momentum)
/-- Keep fixed exponent (arithmetic index). -/
def Wave (u : ℕ) (f g : I → ℂ) := ∃ c : ℝ, 0 ≤ c ∧ ∀ i, Ripple (f i) (g i) (c*rim (w i)^u) (Z i)
namespace Wave
variable {Z w} {u v : ℕ} {f g l h : I→ℂ}
lemma expand (hp : Wave Z w u f g) (hz : ∀ i,0≤Z i) (hm : u≤v) : Wave Z w v f g := by
    obtain ⟨c,hc,K⟩:=hp; exact ⟨c,hc,fun i=> (K i).tack (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (rim_one _) hm) hc) (hz i)⟩
lemma plus (hf : Wave Z w u f g) (hh : Wave Z w u l h) : Wave Z w u (fun i=> f i+l i) (fun i=> g i+h i) := by
  obtain ⟨c,hc,H⟩:=hf; obtain ⟨K,hK,G⟩:=hh; exact ⟨_,add_nonneg hc hK,fun i=> (add_mul c K _) ▸ ((H i).add (G i)) ⟩
lemma negative (hf : Wave Z w u f g) : Wave Z w u (fun i=> -f i) (fun i=> -g i) := by
  obtain ⟨c,hc,H⟩:=hf; refine ⟨c,hc,fun i=> ?_⟩
  constructor
  · rw [norm_neg]; exact (H i).up
  · rw [norm_neg]; exact (H i).down
  · rw [show -f i- -g i= -(f i-g i) by ring,norm_neg]; exact (H i).both
lemma difference (hf : Wave Z w u f g) (hh : Wave Z w u l h) : Wave Z w u (fun i=> f i-l i) (fun i => g i-h i) := by simpa only [sub_eq_add_neg] using (hf.plus hh.negative)
lemma same (hZ : ∀ i,0≤Z i) (c : ℝ) (hc : 0≤c) (H : ∀ i,‖f i‖ ≤ c) : Wave Z w 0 f f := by
  refine ⟨c,hc,fun i=>?_⟩; rw [pow_zero,mul_one]; exact Ripple.self (hZ i) (H i)
lemma constant (hZ : ∀ i,0≤Z i) (v : ℂ) : Wave Z w 0 (fun _=>v) (fun _=>v) := same hZ ‖v‖ (norm_nonneg _) fun _=>le_rfl
lemma times (hf : Wave Z w u f g) (hh : Wave Z w v l h) : Wave Z w (u+v) (fun i=> f i*l i) (fun i=> g i*h i) := by
  obtain ⟨c,hc,H⟩:=hf; obtain ⟨K,hK,G⟩:=hh
  refine ⟨2*(c*K),by positivity,fun i=>?_⟩; rw [pow_add,mul_assoc _ (_*_),mul_mul_mul_comm c K]
  exact (H i).mul (G i)
lemma collect {ι : Type*} [Fintype ι] {A B : ι → I → ℂ}
    (hZ : ∀ i,0≤Z i) (h : ∀ i, Wave Z w u (A i) (B i)) : Wave Z w u (fun i=> ∑ j,A j i) (fun i=> ∑ j,B j i) := by
  classical
  generalize (Finset.univ : Finset ι)=F; induction F using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact (constant (w:=w) hZ 0).expand hZ (Nat.zero_le _)
  | insert i F hx IH=> simp_rw [Finset.sum_insert hx]; exact (h i).plus IH
lemma invert {b : ℕ} (hf : Wave Z w u f g) (hv : ∀ i, f i≠0) (hg : ∀ i, g i≠0)
    (hx : ∃ c : ℝ, 0≤c ∧ ∀ i, ‖(f i)⁻¹‖ ≤ c*rim (w i)^b ∧ ‖(g i)⁻¹‖ ≤ c*rim (w i)^b) :
    Wave Z w (u+b+b) (fun i=> (f i)⁻¹) (fun i => (g i)⁻¹) := by
  obtain ⟨c,hc,H⟩:=hf; obtain ⟨K,hK,G⟩:=hx
  refine ⟨max K (c*K^2),hK.trans (le_max_left ..),fun i=>?_⟩
  have hk := rim_live (w i)
  have ht : K*rim (w i)^b ≤ max K (c*K^2)*rim (w i)^(u+b+b) := mul_le_mul (le_max_left ..) (pow_le_pow_right₀ (rim_one _) (by omega)) (pow_nonneg hk.le _) (hK.trans (le_max_left ..))
  refine ⟨(G i).1.trans ht,(G i).2.trans ht,?_⟩
  rw [show (f i)⁻¹-(g i)⁻¹=(g i-f i)*(f i)⁻¹*(g i)⁻¹ by field_simp [hv i,hg i],norm_mul,norm_mul,norm_sub_rev]
  refine (mul_le_mul (mul_le_mul (H i).both (G i).1 (norm_nonneg _) ((norm_nonneg _).trans (H i).both)) (G i).2 (norm_nonneg _)
    (mul_nonneg ((norm_nonneg _).trans (H i).both) ((norm_nonneg _).trans (G i).1))).trans ?_
  -- why Z ≥ 0 when f i nonzero
  have hM : 0<c*rim (w i)^u := (norm_pos_iff.mpr (hv i)).trans_le (H i).up
  have hy : 0≤Z i := nonneg_of_mul_nonneg_right ((norm_nonneg _).trans (H i).both) hM
  refine le_trans ?_ (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right ..) (pow_nonneg hk.le _)) hy)
  rw [pow_add, pow_add]; exact le_of_eq (by ring)
lemma intermittent (h : ∀ i,0≤Z i) (p : I→Momentum) (f : Momentum→ℂ) (hp : ∀ i,p i∈baseCube) (hf : Continuous f) : Wave Z w 0 (f∘p) (f∘p) := by
  let k:= Metric.closedBall (0 : Momentum) domainRadius; have he : IsCompact k:= isCompact_closedBall ..
  obtain ⟨a,ha,H⟩ := he.exists_isMaxOn (show k.Nonempty from ⟨0,by simp [k,domainRadius_pos.le]⟩) hf.norm.continuousOn
  exact same h ‖f a‖ (norm_nonneg _) fun i=> H (show p i∈ k by simpa [k] using pineNorm (hp i))
lemma punctured (h : ∀ i, 0≤Z i) {a : ℕ} {p : I→Momentum} {c : ℝ} (hc : 0≤c)
    (H : ∀ i,Ripple (f i) (g i) (c*rim (p i)^a) (Z i)) (ht : ∃ L : ℝ, 0≤L ∧ ∀ i,rim (p i) ≤ L * rim (w i)) :
    Wave Z w a f g := by
  obtain ⟨s,hs,K⟩:=ht; refine ⟨c*s^a,by positivity,fun i=> ?_⟩
  exact (H i).tack (by rw [mul_assoc,← mul_pow]; exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (rim_live _).le (K i) _) hc) (h i)
end Wave
variable {ι Ω α : Type*}
def Beam (u : ℕ) (A B : I → Matrix ι Ω ℂ) := ∀ i j, Wave Z w u (fun x=> A x i j) (fun x=> B x i j)
namespace Beam
variable {Z w} {u v : ℕ} {A B C D : I → Matrix ι Ω ℂ} {L H : I → Matrix Ω α ℂ} {f g : I→ℂ}
lemma times [Fintype Ω] (hZ : ∀ i, 0≤ Z i) (h : Beam Z w u A B) (hh : Beam Z w v L H) :
    Beam Z w (u+v) (fun i=> A i * L i) (fun i=> B i * H i) := fun i j=> Wave.collect hZ (fun c=> (h i c).times (hh c j))
lemma plus (h : Beam Z w u A B) (hh : Beam Z w u C D) : Beam Z w u (fun i=> A i+C i) (fun i=>B i+D i) :=
    fun i j => (h i j).plus (hh i j)
lemma minus (h : Beam Z w u A B) (hh : Beam Z w u C D) : Beam Z w u (fun i=> A i-C i) (fun i=>B i-D i) :=
    fun i j => (h i j).difference (hh i j)
lemma scale (h : Beam Z w u A B) (hp : Wave Z w v f g) : Beam Z w (v+u) (fun i => f i • A i) (fun i=> g i • B i) :=
    fun i j=> hp.times (h i j)
lemma home (hZ : ∀ i,0≤Z i) (M : Matrix ι Ω ℂ) : Beam Z w 0 (fun _=>M) (fun _=>M) := fun i j=> Wave.constant hZ (M i j)
lemma upright (h : Beam Z w u A B) (hZ : ∀ i,0≤Z i) (hp : u≤v) : Beam Z w v A B := fun i j=> (h i j).expand hZ hp
lemma circum [Fintype ι] [Fintype Ω] (h : Beam Z w u A B) (hZ : ∀ i, 0≤Z i) :
    ∃ c : ℝ, 0≤c ∧ ∀ i j x,Ripple (A x i j) (B x i j) (c*rim (w x)^u) (Z x) := by
  choose c hc H using h
  refine ⟨∑ i, ∑ j,c i j,Finset.sum_nonneg fun i _=> Finset.sum_nonneg fun j _=>hc i j,fun i j x=> ?_⟩
  have hh := (Finset.single_le_sum (fun j _=>hc i j) (Finset.mem_univ j)).trans
    (Finset.single_le_sum (fun i _=> Finset.sum_nonneg fun j (_:j∈(Finset.univ:Finset Ω))=>hc i j) (Finset.mem_univ i))
  exact (H i j x).tack (mul_le_mul_of_nonneg_right hh (pow_nonneg (rim_live _).le _)) (hZ x)
lemma mask_one_w (hZ : ∀ i,0≤Z i) {F B : I → Axis → ℂ} (hp : ∀ i, Wave Z w u (fun x => F x i) (fun x=> B x i)) :
    Beam Z w u (fun x=> mask 1 (F x)) (fun x => mask 1 (B x)) := by
  intro i j; simp_rw [mask_value]; by_cases he:i=j <;> simp only [he,↓reduceIte]
  · exact hp _
  exact (Wave.constant (w:=w) hZ _).expand hZ (Nat.zero_le _)
lemma turned (h : Beam Z w u A B) : Beam Z w u (fun x=> (A x)ᵀ) (fun x=> (B x)ᵀ) := fun i j=> h j i
end Beam
end Budget
end YM.RG08.Drift
