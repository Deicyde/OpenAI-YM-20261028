import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Inverse


set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# The compressed covariance from  has no null modes after delay

Any windows containing parent balls. Doesn't infer it is positive for
arbitrary cuts (symmetrization is NOT taking an inverse). Gap and price go
through boundary rows and don't license first truncating the data at each
window before forming D^tD. Works without assuming the error E small as
hypothesis. Integrated assembly for A next.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.SectorChange.Schur
open Function Filter Set Lattice Wilson RG Finset Pressure Precision Exterior Tree Matrix Gaussian Rows Wisps 
open scoped Topology BigOperators Classical

variable {V : Type} [Fintype V] [DecidableEq V]
variable {c : Side} {p : V → Site c}
variable (W : V → Set V)

def principal (A : Gaussian.Table V) (s : Set V) := A.submatrix ((↑) : s → V) ((↑) : s → V)

section gaps
variable {A : Gaussian.Table V} {η : ℝ} (h : Gapped A η) (s : Set V)

private def inject (a : Vec s) (i : V) := if h : i∈s then a ⟨i,h⟩ else 0

include h
lemma held_gap : Gapped (principal A s) η := by
  intro x
  let E := (univ.filter (· ∈ s) : Finset V)
  have ht (u : V → ℝ) (hu : ∀ i ∉ s,u i=0) : (∑ i : V, u i) = ∑ i : s, u i := calc
    _ = ∑ i ∈ E, u i := (sum_subset (subset_univ _) fun i hi hh => hu _ (fun h => hh (mem_filter.mpr ⟨hi,h⟩))).symm
    _ = ∑ i : s, u i := Finset.sum_subtype E (fun _ => by simp [E]) _
  have he i (hi : i∉s) : inject s x i=0 := dif_neg hi
  have hr (i : s) : inject s x i=x i := dif_pos i.property
  have hh := h (inject s x)
  unfold sumSq at hh ⊢; unfold dotProduct mulVec at hh ⊢; unfold dotProduct at hh ⊢
  rw [ht _ (fun i hi => by simp [he i hi]), ht _ (fun i hi => by simp [he i hi])] at hh
  simp_rw [hr] at hh
  apply hh.trans_eq
  refine sum_congr rfl fun i _ => ?_
  rw [ht _ (fun i hi => by simp [he i hi])]
  simp_rw [hr]; rfl

-- local copy also exported
lemma dissolves (hA : A.IsSymm) (he : 0<η) : A.PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨Matrix.isHermitian_iff_isSymm.mpr hA, fun x hx => ?_⟩
  simp only [star_trivial]; obtain ⟨i,hi⟩ := Function.ne_iff.mp hx
  exact (mul_pos he ((sq_pos_of_ne_zero hi).trans_le (single_le_sum (f:=fun i => x i ^2) (fun _ _ => sq_nonneg _) (mem_univ i)))).trans_le (h x)
lemma handles (hA : A.IsSymm) (he : 0<η) : IsUnit A.det :=
  (A.isUnit_iff_isUnit_det).mp (dissolves h hA he).isUnit
end gaps

def Bars (W : V → Set V) (p : V → Site c) (r : ℕ) := ∀ i j : V, separation (p i) (p j) ≤ r → j ∈ W i

/-- Ordered lift of each compressed inverse COLUMN on the true address
set. No changes to membership test in symmetrizing. -/
def per (A : Gaussian.Table V) : Gaussian.Table V := Matrix.of fun j i =>
  if h : i∈W i then inject (W i) ((principal A (W i))⁻¹.col ⟨i,h⟩) j else 0

def clouded (A : Gaussian.Table V) : Gaussian.Table V := (1/2:ℝ) • (per W A + (per W A).transpose)

lemma per_read (A : Gaussian.Table V) {i j : V} (h : i∈W i) (e : j∈W i) : per W A j i =
    (principal A (W i))⁻¹ ⟨j,e⟩ ⟨i,h⟩ := by unfold per inject; rw [Matrix.of_apply,dif_pos h,dif_pos e]; rfl
lemma per_zero (A : Gaussian.Table V) {i j : V} (h : j∉W i) : per W A j i = 0 := by unfold per inject; rw [Matrix.of_apply]; split <;> simp [h]

section price
variable {W} {A : Gaussian.Table V} {r : ℕ} {σ η K : ℝ} (hw : Bars W p r)
include hw

lemma per_self (i : V) : i ∈ W i := hw i i (by simp)

lemma per_check (hA : A.IsSymm) (hf : Gapped A η) (he : 0<η) (i : V) {j : V} (hj : j ∈ W i) :
    (A*per W A) j i = (1:Gaussian.Table V) j i := by
  let s:=W i; let e : s→V := (↑); let F:=principal A s
  have h : F.IsSymm := hA.submatrix _
  have hi := per_self hw i
  let x : s := ⟨i,hi⟩; let y : s := ⟨j,hj⟩
  have ht := handles (held_gap hf s) h he
  have hp : (F*F⁻¹) y x = (1 : Gaussian.Table V) j i := by
    rw [F.mul_nonsing_inv ht, Matrix.one_apply, Matrix.one_apply]
    by_cases h : j=i
    · have he : y=x := Subtype.ext h
      rw [if_pos he, if_pos h]
    · rw [if_neg h,if_neg (fun h0 => h (congr_arg e h0))]
  rw [← hp,Matrix.mul_apply,Matrix.mul_apply]
  calc
    _ = ∑ u ∈ univ.filter (·∈s), A j u*per W A u i := (sum_subset (subset_univ _) fun u hu hh => by rw [per_zero W _ (by simpa [s] using hh),mul_zero]).symm
    _ = _ := by
      rw [Finset.sum_subtype (univ.filter (·∈s)) (show ∀ u, u∈univ.filter (·∈s) ↔ u∈s from by simp)]
      refine sum_congr rfl fun u hu => ?_
      have hv : (u:V)∈W i:= u.property; rw [per_read W _ hi hv]; rfl

omit hw in
/-- Price Π alongside A⁻¹, uniform in windows and V. -/
lemma provides {σ η K : ℝ} (hs : 0 < σ) (he : 0 < η) (hk : 0 ≤ K) : ∃ v M : ℝ, 0<v ∧ v≤σ ∧ 0<M ∧
    ∀ {c : Side} {α : Type} [Fintype α] [DecidableEq α] (p : α→Site c) (W : α → Set α) (A : Gaussian.Table α),
    Pours A p p σ K → A.IsSymm → Gapped A η →
      ∀ i j, rate v (separation (p j) (p i))*|per W A j i| ≤ M ∧ rate v (separation (p j) (p i))*|A⁻¹ j i| ≤ M := by
  obtain ⟨v,M,hv,hv',hM,H⟩ := inverse_tilt he hk hs
  refine ⟨v,M,hv,hv',hM,?_⟩
  intro c α _ _ p W A h hA hF i j
  refine ⟨?_,H p A h hF hA i j⟩
  by_cases he : j∈W i
  swap
  · rw [per_zero W A he,abs_zero,mul_zero]; exact hM.le
  by_cases hi : i∈W i
  · rw [per_read W A hi he]; let e : W i → α := (↑)
    exact H (fun k => p (e k)) (principal A (W i)) (h.redact _ _) (held_gap hF _) (hA.submatrix e) ⟨i,hi⟩ ⟨j,he⟩
  unfold per; simp only [Matrix.of_apply,dif_neg hi,abs_zero,mul_zero]; exact hM.le
end price

-- `include hw` interferes provides (will move with omit)

/-- Coverage grows in absolute number of indices *only locally*. -/
def Revenue (p : V → Site c) (B : ℝ → ℝ) := ∀ v : ℝ, 0<v → ∀ i : Site c, ∑ j, rate (-v) (separation i (p j)) ≤ B v

lemma Revenue.per (B : ℝ → ℝ) (h : Revenue p B) {C v : ℝ} {L : Gaussian.Table V} (he : 0<v) (hp : 0≤C)
    (hf : ∀ i j,rate v (separation (p i) (p j))*|L i j| ≤ C) : Pours L p p (v/2) (B (v/2)*C) := by
  simpa using pure he hp hf (h (v/2) (by positivity)) (h (v/2) (by positivity))

private lemma ecost {A F : Gaussian.Table V} {W : V → Set V} {r : ℕ} (hW : Bars W p r)
    (hA : ∀ j : V, ∀ i ∈ W j, (A*F-1) i j = 0) {u C : ℝ} (hu : 0 < u) (h : Pours (A*F-1) p p u C) :
    Pours (A*F-1) p p 0 (rate (-u) r * C) := by
  let E := A*F-1
  have he i j : rate 0 (separation (p i) (p j))*|E i j| ≤ rate (-u) r*(rate u (separation (p i) (p j))*|E i j|) := by
    by_cases hi : separation (p j) (p i) ≤ r
    · simp [E,hA _ _ (hW _ _ hi)]
    · simp only [rate, zero_mul,Real.exp_zero, one_mul]
      refine le_trans ?_ (mul_assoc (Real.exp _) _ _).le
      nth_rw 1 [← one_mul |E i j|]
      gcongr
      rw [← Real.exp_add]; apply Real.one_le_exp
      rw [separation_comm]
      have hr : (r:ℝ) ≤ separation (p j) (p i) := by exact_mod_cast le_of_lt (lt_of_not_ge hi)
      nlinarith
  refine ⟨mul_nonneg (rate_pos ..).le h.pos,fun i => (sum_le_sum (fun j _ => he i j)).trans ?_, fun j => (sum_le_sum (fun i _ => he i j)).trans ?_⟩
  · rw [← mul_sum]; exact mul_le_mul_of_nonneg_left (h.row i) (rate_pos ..).le
  rw [← mul_sum]; exact mul_le_mul_of_nonneg_left (h.col j) (rate_pos ..).le

omit [DecidableEq V] in -- not omit
private lemma pays_id (p : V → Site c) [DecidableEq V] (v : ℝ) : Pours (-1 : Gaussian.Table V) p p v 1 := by
  constructor
  · norm_num
  · intro i
    simp [Matrix.one_apply,rate,apply_ite abs,mul_ite]
  intro i
  simp [Matrix.one_apply,rate,apply_ite abs,mul_ite]

private lemma inv_lower {A : Gaussian.Table V} {η σ K : ℝ} (h : Pours A p p σ K) (hs : 0 ≤ σ)
    (hA : A.IsSymm) (he : 0<η) (hg : Gapped A η) : Gapped A⁻¹ (η/(K+1)^2) := by
  let B := A⁻¹; let k := K+1
  have ht := handles hg hA he
  have hu : A * B = 1 := A.mul_nonsing_inv ht
  intro a
  let b := B *ᵥ a
  have ho : A *ᵥ b=a := by unfold b; rw [mulVec_mulVec,hu,one_mulVec]
  have hh := hg b
  rw [ho,dotProduct_comm] at hh
  have hp := h.pos
  have hm := estimate (h.weaker (t:=0) (e:=k) hs (by unfold k; linarith)) (k⁻¹ • a) b
  rw [ho,smul_dotProduct, smul_eq_mul, ← sumSq_dot] at hm
  have hl (x : ℝ) : sumSq (x • a)=x^2*sumSq a := by unfold sumSq; simp only [Pi.smul_apply,smul_eq_mul,mul_pow,mul_sum]
  have hk : 0<k := by unfold k; positivity
  rw [hl] at hm
  have hi := le_of_abs_le hm
  apply le_trans _ hh
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  change η*_ ≤ _ * k^2
  field_simp at hi -- clears k
  nlinarith
/-- Uniform C accuracy in the unweighted Pours, with exponential in
window radius. Thus C gapped also, *eventually* (does not infer positivity
for arbitrary window sizes). -/
theorem windows {σ η K : ℝ} (hs : 0 < σ) (he : 0 < η) (hk : 0 ≤ K) (B : ℝ → ℝ) (hB : ∀ v, 0 ≤ B v) :
    ∃ v C g : ℝ, 0<v ∧ 0<C ∧ 0 < g ∧ ∀ᶠ r : ℕ in atTop,
      ∀ {c : Side} {α : Type} [Fintype α] [DecidableEq α] (p : α → Site c) (A : Gaussian.Table α) (W : α → Set α),
      Revenue p B → Pours A p p σ K → A.IsSymm → Gapped A η → Bars W p r →
      Pours (clouded W A - A⁻¹) p p 0 (C*rate (-v) r) ∧ Gapped (clouded W A) g ∧ (clouded W A).PosDef := by
  obtain ⟨v,M,hv,hr,hM,h⟩ := provides hs he hk
  let u := v/2
  let m := B u * M
  have hu : 0<u := half_pos hv
  have hm : 0≤m := mul_nonneg (hB _) hM.le
  let D := K*m+1
  have hd : 0<D := by unfold D; positivity
  let E := m*D+1
  have hD : 0<E := by unfold E; positivity
  let G := η/(K+1)^2
  have hG : 0<G := by unfold G; positivity
  refine ⟨u,E,G/2, hu,hD,half_pos hG,?_⟩
  have ht : Tendsto (fun r : ℕ => E * rate (-u) r) atTop (𝓝 0) := by
    have hr := Real.tendsto_exp_atBot.comp
      (tendsto_natCast_atTop_atTop (R:=ℝ) |>.const_mul_atTop_of_neg (neg_lt_zero.mpr hu)) 
    simpa [rate] using hr.const_mul E
  filter_upwards [ht.eventually (gt_mem_nhds (half_pos hG))] with r h₀
  intro c α _ _ p A W hx hy hA hg hW
  let L := per W A
  have hi : u≤σ := (half_le_self hv.le).trans hr
  have hh (i j) := h p W A hy hA hg i j
  have hL : Pours L p p u m := Revenue.per B hx hv hM.le (fun i j => (hh j i).1)
  have hR : Pours A⁻¹ p p 0 m := (Revenue.per B hx hv hM.le (fun i j => (hh j i).2)).weaker hu.le le_rfl
  have ha : Pours (L-A⁻¹) p p 0 (E*rate (-u) r) := by
    have hc : Pours (A*L-1) p p u D := by
      rw [sub_eq_add_neg]; exact (((hy.weaker hi le_rfl).fuse hL hu.le).bind (pays_id p u))
    have H := ecost hW (A:=A) (F:=L) (fun j i H => (show ((A*L-1) i j)=0 by rw [Matrix.sub_apply,show (A*L) i j=_ from per_check hW hA hg he j H,sub_self])) hu hc 
    rw [show L-A⁻¹=A⁻¹*(A*L-1) from ?_]
    · exact (hR.fuse H le_rfl).weaker le_rfl (by unfold E; have := rate_pos (-u) r; nlinarith)
    rw [Matrix.mul_sub,← Matrix.mul_assoc,A.nonsing_inv_mul (handles hg hA he),Matrix.one_mul,Matrix.mul_one]
  let b := E*rate (-u) r
  have hh : Pours (clouded W A - A⁻¹) p p 0 b := by
    have hc := (ha.bind ha.turn).scale (1/2 : ℝ)
    rw [show clouded W A - A⁻¹ = (1/2:ℝ) • ((L-A⁻¹)+(L-A⁻¹).transpose) from ?_]
    · exact hc.weaker le_rfl (le_of_eq (by unfold b; rw [abs_of_nonneg (by norm_num)]; ring))
    ext i j
    have hi : A⁻¹ j i=A⁻¹ i j := congr_fun (congr_fun hA.inv.eq i) j
    change ((1/2:ℝ)*(L i j+L j i))-A⁻¹ i j= (1/2:ℝ)*((L i j-A⁻¹ i j)+(L j i-A⁻¹ j i))
    rw [hi]; ring
  have hf : Gapped (clouded W A) (G/2) := by
    intro a
    have hl := (abs_le.mp (estimate hh a a)).1
    rw [Matrix.sub_mulVec,dotProduct_sub] at hl
    have hy : G*sumSq a ≤ a ⬝ᵥ (A⁻¹ *ᵥ a) := inv_lower hy hs.le hA he hg a
    have hu := mul_le_mul_of_nonneg_right (show b ≤ G/2 from h₀.le) (sumSq_nn a)
    linarith only [hl,hy,hu]
  refine ⟨hh,hf,dissolves hf ?_ (half_pos hG)⟩
  unfold Matrix.IsSymm clouded
  ext i j
  change (1/2:ℝ)*(L j i+L i j) = (1/2:ℝ)*(L i j+L j i)
  rw [add_comm]
end YM.Next.SectorChange.Schur
