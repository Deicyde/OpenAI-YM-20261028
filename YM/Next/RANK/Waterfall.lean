import YM.Next.RANK.Bounty
import YM.Next.RANK.GlyphRise
import YM.Next.RANK.Headwater

/-!
# Assign short-square ratio among relevant sites

Multiple kept indicators may fail; alarms adjacent even when short-square shared,
store in each true site with tested masks. No division by a vacuum law ratio.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Alarm
open Function Filter RG Thirst Baler Lattice Wilson Finset MeasureTheory Relation Corona Value Glyph Marker PathData
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side} {p q : BudgetPoint} {r : ℕ}
variable {C : Clip} {t τ μ σ Λ : ℝ}
variable (P : PathData G)

def division (q : ℕ) (x : Site n) (t : ℝ) (U : Config G n) := halo q {x}∩ flags t U

def parting (q : ℕ) (C : Clip) (t τ : ℝ) (i : Signed) (x y : Site n) (U : Config G n) :=
    if y∈ halo q {x} then basin P q C t τ (pull i x U)/ (division q x τ U).card else 0

def allot (q : ℕ) (C : Clip) (t τ : ℝ) (y : Site n) (U : Config G n) :=
    (Fintype.card Signed:ℝ)⁻¹ * ∑ s : Signed, ∑ x, parting P q C t τ s x y U

lemma reprisal (V : Config G n) (h : Turnon C τ r) (ht : 0<τ) :
    ∑ i∈flags τ V,allot P r C t τ i V= rag (basin P r C t τ) V:= by
  have hx (s : Signed) (x : Site n) :
      ∑ i∈flags τ V,parting P r C t τ s x i V= basin P r C t τ (pull s x V):= by
    let d:= division r x τ V; let a:=basin P r C t τ (pull s x V); let Z := flags τ V
    unfold parting; rw [← sum_filter]; change ∑ i∈Z.filter _, a/↑d.card=a
    rw [show Z.filter (fun i=>i∈halo r {x})=d by ext;simp [d,division,Z,and_comm]]
    by_cases hh:Healthy τ (halo r {x}) V
    · have he : a=0:= basin_void P h ht (pull s x V) ((s_healthy s x ..).2 (by rw [swath_here];exact hh))
      simp [he]
    have hf : 0 < (↑d.card:ℝ) := by
      have hz : d≠ ∅:= mt Finset.disjoint_iff_inter_eq_empty.mpr hh
      exact_mod_cast Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hz)
    rw [Finset.sum_const,nsmul_eq_mul]; field_simp
  unfold allot rag; rw [← mul_sum,sum_comm]; apply congr_arg; apply sum_congr rfl; intro i _; rw [sum_comm]; exact sum_congr rfl fun a _=> hx ..

lemma allot_move (s : Signed) (x i : Site n) (V : Config G n) :
    allot P r C t τ i (pull s x V)=allot P r C t τ (affine s x i) V:= by
  unfold allot; apply congr_arg ((Fintype.card Signed:ℝ)⁻¹*·)
  refine Fintype.sum_equiv (Equiv.mulLeft s) _ _ fun p => Fintype.sum_equiv (sends s x) _ _ fun y=> ?_
  unfold parting; simp only [pull_pull]
  change (if i∈halo r {y} then _ else _)= (if affine s x i∈halo r {affine s x y} then _ else _)
  have he : halo (n:=n) r {affine s x y}= swath s x (halo r {y}) := by simp [swath_iffHalo, show swath s x {y}={affine s x y} from image_singleton .. ]
  have hh : division r (affine s x y) τ V= swath s x (division r y τ (pull s x V)):= by
    unfold division; nth_rw 1 [← s_flags s x τ V]; rw [he];exact (image_inter _ _ (sends s x).injective).symm
  have hv : (division r (affine s x y) τ V).card=(division r y τ (pull s x V)).card:= by rw [hh]; exact Finset.card_image_of_injective _ (sends s x).injective
  change (if _ then _/ _ else _)= (if _ then basin P r C t τ (pull (s*p) (affine s x y) V) /((division r (affine s x y) τ V).card:ℝ) else _); rw [hv]
  by_cases hu : i∈halo r {y}
  · rw [if_pos hu,if_pos (show affine s x i∈halo r {affine s x y} by rw [he,stay];exact hu)]
  rw [if_neg hu]; exact (if_neg (show affine s x i∉halo r {affine s x y} by rw [he,stay];exact hu)).symm
lemma allot_gauge (h : P.Bounds C σ μ Λ) (y : Site n) : GaugeInvariant (allot P r C t τ y) := by
  intro i U; simp only [allot,parting, division,gauge_flags,s_gauge,basin_gauge P h (i∘ _) _]
lemma allot_pos (y : Site n) (U : Config G n) : 0 ≤ allot P r C t τ y U := by
  refine mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (sum_nonneg fun i _=> sum_nonneg fun j _=> ?_)
  unfold parting; split;exact div_nonneg (basin_positive ..) (Nat.cast_nonneg _); exact le_rfl
lemma allot_meas (y : Site n) : Measurable (allot P r C t τ y):= by
  refine measurable_const.mul (Finset.measurable_fun_sum _ fun i _=> Finset.measurable_fun_sum _ fun j _=> ?_)
  unfold parting; split
  · refine Measurable.div ((basin_meas ..).comp (continuous_pull ..|>.measurable)) ?_
    have he : Measurable fun U : Config G n=> flags τ U := by
      -- use discrete measurable
      apply measurable_to_countable _; intro i; exact flags_measurable_eq ..
    exact (measurable_of_countable (f:=fun u : Support n=> (↑(halo r {j} ∩ u).card:ℝ))).comp he
  exact measurable_const
lemma allot_local (hU : Turnon C τ r) (ht : τ≤t) (hq : 8≤r) (hu : 0<τ) (y : Site n) :
    UsesFinal τ (halo (4*r) {y}) (allot P r C t τ y) := by
  let Y:= halo (4*r) {y}
  intro U V h H; apply congr_arg ((Fintype.card Signed:ℝ)⁻¹*·); apply sum_congr rfl; intro s _; apply sum_congr rfl; intro x _
  unfold parting; split_ifs with hx
  · obtain ⟨a,ha,hy⟩:= halo_spec.mp hx; rw [mem_singleton] at ha; subst a
    have hv : halo (2*r) {x} ⊆ Y:= by
      intro b hb; obtain ⟨c,hc,hp⟩:=halo_spec.mp hb; rw [mem_singleton] at hc; subst c
      exact halo_spec.mpr ⟨_,mem_singleton_self _,(separation_triangle y x b).trans (by rw [separation_comm y];omega)⟩
    have hq' : division r x τ U =division r x τ V :=
      Work.H03.reads_larger (fun z hz=> hv (halo_mono (show r≤2*r by omega) (le_refl _) hz)) (fun _ _ _ a=>a) U V h H
    rw [hq', show basin P r C t τ (pull s x U)=basin P r C t τ (pull s x V) from p_local s x (halo (2*r) ({0}:Support n)) (basin_loc P hU ht hq hu) U V
      (agrees_mono h (by intro z hz; rw [swath_here] at hz; exact hv hz))]
  rfl

variable (h : P.Bounds C σ μ Λ) (hv : τ ≤ t) (hq : 8≤r) (hu : 0<τ) (H : Turnon C τ r) (b : ℝ)

def pour (x : Site n) (U : Config G n) := if x ∈ flags τ U then Real.exp (-b*(sceneAt C t τ x U+allot P r C t τ x U)) else 0

def signal : Siren G n τ where
  chamber x := halo (4*r) {x}
  ample x:=halo_mono (by omega) (le_refl _)
  value:=@pour G n r C t τ P b
  meas x:=Measurable.ite (flags_open x τ).measurableSet (Real.continuous_exp.measurable.comp (measurable_const.mul (scene_meas x|>.add (allot_meas ..)))) measurable_const
  gauge x k U:=by simp only [pour,gauge_flags,scene_gauge x k U, allot_gauge P h x k U]
  rings i U H:=if_neg H
  legal x U V he hP:= by
    unfold pour; let Y:= halo (n:=n) (4*r) {x}
    have hx : x∈ Y:=halo_subset _ _ (mem_singleton_self ..)
    have hh : x∈flags τ U ↔ x∈flags τ V:=by simpa only [mem_inter,show x∈halo (n:=n) (4*r) {x} from hx,true_and] using iff_of_eq (congr_arg (fun z:Support n=>x∈z) hP)
    have hc : halo (n:=n) 8 {x} ⊆ Y:= halo_mono (by omega) (le_refl _)
    simp only [hh,scene_loc x U V (agrees_mono he (fun x h=> hc h)),allot_local P H hv hq hu x U V he hP]

-- exact equality, cashout
include H hu hv hq h
-- parameters included in `signal`
lemma pours (U : Config G n) :
    (∏ i∈ flags τ U,(signal P h hv hq hu H b (n:=n)).value i U)=Real.exp (-b*(Shift C t τ U+rag (basin P r C t τ) U)) := by
  let F x:= sceneAt C t τ x U + allot P r C t τ x U
  let S:=signal P h hv hq hu H b (n:=n)
  rw [show (∏ i∈ _,(signal ..).value i U)=(∏ i∈flags τ U,Real.exp (-b*F i)) from prod_congr rfl fun i hi=> if_pos hi,
    ← Real.exp_sum,← mul_sum]
  unfold F; rw [sum_add_distrib,scenes _ _ hv,reprisal P U H hu]
lemma systematic : Peace (signal P h hv hq hu H b (n:=n)):= by
  intro s x y
  refine ⟨?_,fun U=>?_⟩
  · change halo _ _=swath s x (halo (n:=n) (4*r) {y}); rw [swath_iffHalo]; simp only [swath,image_singleton]
  dsimp only [signal]
  simp only [pour, scene_moves s x y U, ← allot_move P s x y]
  split_ifs with hi hp hF; exacts [rfl,(hp (stay s x _|>.1 (s_flags s x .. |>.symm ▸ hi))).elim, (hi (s_flags s x .. ▸ stay s x _|>.2 hF)).elim,rfl]

def batch (u e : ℝ) (q : ℕ) := ((((4*q+(4*q)+1)^4:ℕ):ℝ)) * Real.exp (-u) * Real.exp (e*(9^4:ℕ))
omit hv hu hq H h in
lemma signals (x : Site n) (q) (e u : ℝ) (he : 0 ≤ e) (hv : 0<q) :
    Point (fun y : Site n=> halo (4*q) {y}) q (fun _=> Real.exp (-u)) e (fun y=> x∈ halo (4*q) {y}) (batch u e q) := by
  let F y:= halo (n:=n) (4*q) ({y}:Support n)
  have h (y) : 0≤ Real.exp (-u)*debt q e (F y):= mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
  apply (sum_pay _ _ _ h).2
  let Z : Support n:= univ.filter (fun i=> x∈halo (4*q) {i})
  have hz : Z⊆F x := by
    intro i hi; obtain ⟨j,hj,hv⟩:= halo_spec.mp (mem_filter.mp hi).2; rw [mem_singleton] at hj; subst i
    exact halo_spec.mpr ⟨x,mem_singleton_self _,(separation_comm ..).trans_le hv⟩
  calc
    _ = ∑ i∈Z,Real.exp (-u)*debt q e (F i):= by dsimp only [Z]; rw [sum_filter]; apply sum_congr rfl; intro i _; split_ifs<;>rfl

    _ ≤ ∑ i∈Z,(Real.exp (-u)* Real.exp (e*↑(9^4:ℕ))) :=sum_le_sum fun i _=>mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by exact_mod_cast tile i 4 q hv) he)) (Real.exp_pos _).le
    _ = (↑Z.card:ℝ) * (Real.exp (-u) * Real.exp (e*↑(9^4:ℕ))) := by simp only [sum_const,nsmul_eq_mul]
    _ ≤ batch u e q := by
      have hh : Z.card≤ (4*q+(4*q)+1)^4 := (card_le_card hz).trans (by simpa only [card_singleton,one_mul] using halo_size (n:=n) {x} (4*q))
      unfold batch; rw [mul_assoc]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast hh) (by positivity)
omit H h hu hv hq in
private lemma dribbles {b : ℝ} (hb : 0≤b) (u : ℝ) (hp : 2*τ ≤ t) (ht : 0<τ) (hr : 2*u ≤ b*C.linear/5 * τ^2) (x : Site n) (V : Config G n) :
    |pour P b x V (t:=t) (C:=C) (τ:=τ) (r:=r)| ≤ Real.exp (-u) * Real.exp (-u):= by
  unfold pour; split
  · rename_i h; rw [abs_of_nonneg (Real.exp_pos _).le,← Real.exp_add]; apply Real.exp_le_exp.mpr
    have hz := scene_pay C ht hp V x h
    linarith only [mul_le_mul_of_nonneg_left hz hb,hr,mul_nonneg hb (show 0≤allot P r C t τ x V from allot_pos ..)]
  rw [abs_zero]; positivity

omit H h hu hv hq in
lemma humid (B : PathData G) (p q : BudgetPoint) (h : B.Bounds C σ μ Λ) (hv : q.threshold≤p.threshold) (hq : 8≤ q.B) (H : Turnon C q.threshold q.B)
    {b e : ℝ} (hb : 0≤b) (he : 0≤e) (u : ℝ) (hp : 2*q.threshold ≤ p.threshold) (hr : 2*u ≤ b*C.linear/5 * q.threshold^2) :
    fertile (signal B h hv hq q.threshold_pos H b (n:=n)) (q:=q) u e (batch u e q.B) :=
  ⟨fun _=>Real.exp (-u),fun a=> ⟨(Real.exp_pos _).le,fun U=> dribbles B hb u hp q.threshold_pos hr a U⟩,fun x=> signals x _ e u he q.B_pos⟩
end YM.Next.Rank.Alarm
