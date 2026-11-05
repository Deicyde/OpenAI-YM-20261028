import YM.Next.STATIONARY.FrameEst.Averages
import YM.Next.STATIONARY.Spectral.Folding



set_option autoImplicit false
/-!
# Patch odds. Exact residue distribution and jets use absolute budgets
with probability weights reading physical POINTS on arbitrary coarse layout.
Accuracy counts fully, not replacing P.Rolls with independent uniform
for all payees (only the residue identity). -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Wilson Exterior Precision Bloch Laurent Matrix Finset Complex
open scoped Matrix Topology ContDiff BigOperators ComplexConjugate
variable {G : Gauge} {L c f : Side} (P : Patch)
private def proxy : Ratio 1 P.L := ⟨P.L,(by change _ = 1*_; rw [one_mul])⟩
def roulette : P.Small ≃ Site P.L where
  toFun a := wrap _ a.val
  invFun a := ⟨lift a, Ratio.half_box (proxy P) P.odd_side a⟩
  right_inv a := wrap_lift _
  left_inv a := Subtype.ext (Ratio.half_lift (proxy P) P.odd_side a.val a.property)
lemma roll_card : Fintype.card P.Small=(P.L.val)^4 := Eq.trans (Fintype.card_congr (roulette P)) (Lattice.site_card _)
lemma lottery {X : Type*} [AddCommMonoid X] [Module ℝ X] (F : P.Points → X) :
    ∑ x : P.Points,P.weight x • F x=(Fintype.card P.Rolls:ℝ)⁻¹ • ∑ i : P.Rolls,F (P.addRoll i) := by
  simp only [Patch.weight,Finset.sum_smul,ite_smul,zero_smul]; rw [sum_comm]; simp [Finset.smul_sum]
lemma lottery_residue (s : Site P.L) {X : Type*} [AddCommMonoid X] [Module ℝ X] (F : Site P.L → X) :
    ∑ i : P.Points,P.weight i • F (wrap _ i.val+s)=(inch P.L)^4 • ∑ i : Site P.L,F i := by
  rw [lottery P (fun i => F (wrap _ i.val+s))]
  let k := P.J-1
  have he : k+1=P.J := Nat.sub_add_cancel (by have := P.order_cut; omega)
  let f : (Fin (k+1) → P.Small) ≃ P.Rolls := Equiv.arrowCongr (finCongr he) (Equiv.refl P.Small)
  let l : P.Rolls ≃ P.Small×(Fin k→ P.Small) := f.symm.trans (Fin.consEquiv _).symm
  have h (i : P.Small) (z : Fin k→ P.Small) : (P.addRoll (l.symm (i,z))).val=i.val+∑ t : Fin k,(z t).val := by
    change ∑ t : Fin P.J, _ = _; rw [← Equiv.sum_comp (finCongr he),Fin.sum_univ_succ]; simp [l,f]
  have hv (j : Fin k→ P.Small) : ∑ i : P.Small,F (wrap _ (P.addRoll (l.symm (i,j))).val + s) = ∑ i : Site P.L,F i := by
    simp_rw [h,map_add,add_assoc]; exact Equiv.sum_comp ((roulette P).trans (Equiv.addRight _)) _
  rw [← Equiv.sum_comp l.symm,Fintype.sum_prod_type, Finset.sum_comm]; simp_rw [hv]
  rw [Finset.sum_const,card_univ, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]; congr 1
  rw [Fintype.card_congr l,Fintype.card_prod, roll_card P]; unfold inch
  have hh : (Fintype.card (Fin k→ P.Small):ℝ)≠0 := by exact_mod_cast Fintype.card_pos.ne'
  push_cast; field_simp

lemma lottery_exp (p : Momentum) :
    ∑ a : P.Points,(P.weight a:ℂ)*mode p a.val = (((inch P.L:ℂ))^4*∑ a : Site P.L,mode p (lift a))^P.J := by
  have hp := lottery P (fun a => mode p a.val)
  simp only [Complex.real_smul] at hp
  rw [hp]; push_cast
  have hh (b : P.Rolls) : mode p (P.addRoll b).val = ∏ i, mode p (b i).val := by
    suffices he : ∀ a : Finset (Fin P.J), mode p (∑ i∈a,(b i).val)= ∏ i∈a,mode p (b i).val from he univ
    intro a; induction a using Finset.induction with
    | empty => simp
    | insert i a he ih => rw [prod_insert he,sum_insert he,mode_shift,ih]
  let T : Fin P.J → P.Small→ℂ := fun _ a => mode p a.val
  simp_rw [hh]; rw [show (∑ b:P.Rolls,∏ i,T i (b i))=_ from (Fintype.prod_sum T).symm]; unfold T; rw [prod_const,card_univ,Fintype.card_fin]
  unfold Patch.Rolls; rw [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, ← inv_pow, ← mul_pow]
  have ht := roll_card P
  rw [ht]; congr 1; rw [← Equiv.sum_comp (roulette P).symm (fun a : P.Small => mode p a.val)]
  all_goals simp [inch,roulette]

-- path costs for offset shifts along connector; within coarse footprint, output θ.
lemma rent_fit (x : P.Points) (a : Axis) (k : ℕ) (he : k≤P.L.val) : x.val+k • step a∈box ((P.J+5)*P.L.val) := by
  obtain ⟨h,hp⟩ := box_test.mp x.property
  unfold Patch.radius at h hp
  rw [box_test]
  constructor <;> intro i <;> have H := h i <;> have hv := hp i
  all_goals rw [Pi.add_apply,Pi.smul_apply,nsmul_eq_mul, step_apply]; split <;> simp only [mul_zero,mul_one]
  all_goals push_cast at *; have hK : (k:ℤ) ≤ P.L.val := by exact_mod_cast he
            nlinarith [Nat.cast_nonneg (α:=ℤ) k, Nat.cast_nonneg (α:=ℤ) P.L.val]
lemma scrap_oath {α : Type} (F : Phase (Co P.L α)) {p : Momentum} {σ : ℝ} (hp : p∈strip σ)
    (x : P.Points) (j : Axis) (a : α) {k : ℕ} (hk : k≤P.L.val) :
    ‖scrap p F (x.val+k • step j) a‖≤ Real.exp (σ * (4+4*(P.J+5:ℝ))) * ‖F (wrap _ (x.val+k • step j),a)‖ := by
  let z := x.val+k • step j
  have ht : 0<σ := (abs_nonneg _).trans_lt (hp 0)
  unfold scrap; rw [norm_mul]
  exact mul_le_mul_of_nonneg_right ((reward p (rent P.L z) σ (fun i => (hp i).le)).trans (Real.exp_monotone (mul_le_mul_of_nonneg_left (rent_pay P _ (rent_fit P x j k hk)) ht.le))) (norm_nonneg _)
end YM.Stationary
end

/-!
# Virtual patch. `Cast` centers by focus of weighted mean, not the
unweighted one. Cover inputs smooth matrix paths; use actual constructed
fixed-mesh score to prove analyticity. Branches and kernel choices visible;
no complex-group continuation assumed.
-/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Audience Exterior Precision Bloch Wilson Laurent Matrix Finset
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {α : Type} [Fintype α] [Nonempty α] {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {G : Gauge} {P : Patch} {n : ℕ} {R : X→ℕ→Prop} (K : KernelChoices) {C : ℝ}

namespace Audience

def salon (P : Patch) : Audience P.Points := ⟨P.weight,P.weight_nonneg,P.weight_sum⟩
def portrait (j : ℕ) : ℝ := (2*((j:ℝ)+3)+1)^4
lemma painted (j : ℕ) : 1≤portrait j := one_le_pow₀ (le_add_of_nonneg_left (by positivity))
lemma portrait_card (r : ℕ) : Fintype.card ↥(Lattice.box r) = (2*r+1)^4 := by
  let z : ↥(Lattice.box r) ≃ (Axis→↥(Lattice.layers r)) := {
    toFun x i := ⟨_,(Lattice.box_iff_layers x.val r).mp x.property i⟩
    invFun a := ⟨fun i => (a i).val,(Lattice.box_iff_layers _ _).mpr fun i => (a i).property⟩
    left_inv x := rfl
    right_inv a := rfl }
  rw [Fintype.card_congr z,Fintype.card_fun,Fintype.card_coe,Lattice.card_layers]; simp
lemma medium (P : Patch) : (inch P.L)^4 * Fintype.card P.Points ≤ portrait P.J := by
  change (inch P.L)^4 * ↑(Fintype.card ↥(Lattice.box P.radius)) ≤_
  rw [portrait_card]; push_cast; rw [← mul_pow]; apply pow_le_pow_left₀ (by positivity [inch_pos P.L])
  rw [Patch.radius]; push_cast; have he : inch P.L * (2*((P.J:ℝ)+3)*P.L.val) =2*((P.J:ℝ)+3) := by rw [mul_left_comm,inch_unit,mul_one];
  rw [mul_add,mul_one,← mul_assoc 2, he]; exact add_le_add_right (inch_le _) _
lemma salon_vote (i : P.Points) : P.weight i ≤ (inch P.L)^4 := by
  let f (x : Site P.L) := if x=wrap _ i.val then (1:ℝ) else 0
  have ht := lottery_residue P 0 f
  simp only [add_zero,smul_eq_mul] at ht
  have hx := single_le_sum (s:=univ) (f:=fun j : P.Points => P.weight j * f (wrap _ j.val)) (fun j _ => mul_nonneg (P.weight_nonneg j) (by unfold f; split <;> norm_num)) (mem_univ i)
  rw [ht] at hx; simpa [f] using hx
lemma salon_stamp (P : Patch) (i : P.Points) : (salon P).weight i ≤ portrait P.J * (balcony P.Points).weight i := by
  change P.weight i≤portrait _ * _⁻¹; rw [← div_eq_mul_inv]; apply le_trans (salon_vote i)
  have ht : 0 < (Fintype.card P.Points:ℝ) := by exact_mod_cast Fintype.card_pos
  exact (le_div_iff₀ ht).mpr (medium P)
end Audience

lemma dome_select {K} (h : P.Branches K G) {U V : CoverConfig G} (he : P.usesMin K U) (hx : ∀ i∈P.sites,∀ j,U (i,j)=V (i,j)) : P.selected U=P.selected V := by
  have hp (f) : P.score U f=P.score V f := by
    have ht i j k : P.via f U i j k=P.via f V i j k := by unfold Patch.via; rw [show travel U i.val (route i.val j.val k)=travel V i.val (route i.val j.val k) from (perimeter (P:=P) (i,j) (allAxes k) ((List.nodup_finRange _).map k.injective) hx)]
    simp_rw [Patch.score,ht]
  have ht := (P.min_exists V).choose_spec
  exact (h.frame_unique U he).unique (P.min_exists U).choose_spec ⟨ht.1,fun i hj => by rw [hp,hp]; exact ht.2 _ hj⟩
-- read actual rooted frame in a sufficiently large step. The step is NOT needed to compute widths, only germ equality.
variable {U : X→CoverConfig G} {K}

lemma min_applies (h : Army U 0) (p : U 0=1) : ∀ᶠ x in 𝓝 0, P.usesMin K (U x) := by
  refine h.cont.eventually (((P.min_open (C:=K)).mem_nhds (x:=U 0) (?_ : P.usesMin _ _)))
  intro i j l r
  simp only [p,Patch.via,Patch.axial,Pressure.one,mul_one,inv_one,G.chord_one]; exact K.frame_cut_pos

lemma tagged_here (h : Army U 0) (p : U 0=1) : ∀ᶠ x in 𝓝 0,∀ i,P.frame K (U x) i=P.selected (U x) := (min_applies (P:=P) (K:=K) h p).mono fun i he t => by rw [Patch.frame,if_pos he]

lemma select_zero {K} (h : P.Branches K G) : P.selected (1:CoverConfig G)=1 := by
  let S : StepData 1 P.L := ⟨P,K,(by change (P.L.val:ℕ)=1*P.L.val; rw [one_mul])⟩
  let t : S.SitesChoice := fun _ => (P.center,1)
  funext i
  apply G.mat_injective
  have he := Push.hats_zero S (0:Site (1:Side)) t (h:=h) i
  change G.mat (P.frame K (Push.product S 0 (0:Push.In G P.L)) _ i)=_ at he
  rw [Patch.frame, if_pos (Push.picks S _), Push.product_zero] at he
  exact he
lemma vaulted (h : P.Branches K G) (hu : Army U 0) (hp : U 0=1) : Army (fun x => P.selected (U x)) 0 := by
  let Z := 2*P.radius+1
  let L : Side := ⟨Z*P.L.val,Nat.mul_pos (by omega) P.L.pos⟩
  let c : Side := ⟨Z,by omega⟩
  let S : StepData c L := ⟨P,K,rfl⟩
  let F := fun x e => U x (lift (e:Edge (Site L)).1,e.2)
  let v := fun x => expandAt (S.ratio.embed 0) (F x)
  have he : S.ratio.embed 0=0 := map_zero S.ratio.root
  have hF : Army F (0:X) := fun i => hu _
  have hV : F 0=1 := by funext i; simp [F,hp]
  have hv : Army v (0:X) := fun i => hF _
  have hW : v 0=1 := by funext i; unfold v expandAt; rw [hV]; rfl
  have hw x : ∀ i∈P.sites, ∀ j,U x (i,j)= v x (i,j) := by
    intro i hi j; unfold v F expandAt; rw [he,add_zero]
    have hx := box_test.mp hi
    have hy : Z ≤ L.val := Nat.le_mul_of_pos_right _ P.L.pos
    dsimp only
    rw [lift_eq_iff.mpr (show (wrap L i=wrap L i) ∧ _ from ⟨rfl,fun k => by
      have ht := hx.1 k; have he := hx.2 k; unfold Z at hy; omega⟩)]
  let t : S.Choices := (fun _ => (P.center,1),fun _ => P.center)
  intro i
  apply (Army.frame (S:=S) h t hF hV 0 i).congr_of_eventuallyEq
  filter_upwards [tagged_here (P:=P) (K:=K) hv hW, min_applies (P:=P) (K:=K) hu hp] with x hx hh
  change _=G.mat (P.frame K (v x) (t.1 0) i); rw [hx,dome_select h hh (hw _)]

def entryHat (P : Patch) (U : CoverConfig G) := (salon P).partakes (fun i => G.mat (P.selected U i))
def entryCap (P : Patch) (U : CoverConfig G) : G.El := G.focus (entryHat P U)
def choirCap (P : Patch) (U : CoverConfig G) : P.Frame G := fun i => (entryCap P U)⁻¹ * P.selected U i
lemma focus_zero (G : Gauge) : G.focus 1=1 := (mem_of_mem_nhds G.nearest_is_focus 1 (fun i => by simp)).symm
lemma entry_zero (h : P.Branches K G) : entryHat P (1:CoverConfig G)=1 := by simp [entryHat,select_zero h]
lemma cap_ground (h : P.Branches K G) : choirCap P (1:CoverConfig G)=1 := by funext i; simp [choirCap,entryCap,entry_zero h,focus_zero,select_zero h]
lemma cap_sensation (h : P.Branches K G) (hx : Army U 0) (hp : U 0=1) :
    ContDiffAt ℝ ω (entryHat P ∘ U) 0 := ContDiffAt.sum fun i _ => (vaulted h hx hp i).const_smul _
lemma cap_fold (h : P.Branches K G) (hx : Army U 0) (hp : U 0=1) : ContDiffAt ℝ ω (fun i => G.mat (entryCap P (U i))) 0 :=
    (show ContDiffAt ℝ ω (fun i => G.mat (G.focus i)) (entryHat P (U 0)) by rw [hp, entry_zero h]; exact G.focus_diff).comp (f:=entryHat P ∘ U) (0:X) (cap_sensation h hx hp)
lemma cap_thaw (h : P.Branches K G) (hx : Army U 0) (hp : U 0=1) : Army (choirCap P∘U) 0 := by
  let F : X→P.Frame G := fun i _ => entryCap P (U i)
  have he : Army F 0 := fun i => cap_fold h hx hp
  exact he.inv.mul (vaulted h hx hp)
end YM.Stationary
end

/-!
# Center-normal frame identities. `chorus_compute` eliminates the whole
weighted center (which otherwise has large counting-norm derivative on a
rooted chart). This preparatory step cares about ORDERED patches.
-/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Audience Exterior Precision Bloch Wilson Laurent Matrix Finset
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {α : Type} [Fintype α] [Nonempty α] {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {G : Gauge} {P : Patch} {n : ℕ} {R : X→ℕ→Prop} {K : KernelChoices} {C : ℝ}
variable {U : X→CoverConfig G} (h : P.Branches K G) (p : Army U 0) (hp : U 0=1)

lemma onward_focus (G : Gauge) : ∀ᶠ x in 𝓝 (1:G.Mat),G.Nearest (G.focus x) x := G.nearest_is_focus.mono fun x hx => by obtain ⟨v,hv⟩ := G.nearest_exists x; rw [← hx v hv]; exact hv

def bell (G : Gauge) : G.Mat→G.Mat := fun x => G.mat (G.focus x)
def tollMat (G : Gauge) : G.Mat→L[ℝ] G.Mat := G.lie.starProjection
def ringTone (G : Gauge) (x : G.Mat) := bell G x - tollMat G x
lemma toll_first (G : Gauge) : fderiv ℝ (ringTone G) 1=0 := (G.focus_deriv.hasFDerivAt.sub (tollMat G).hasFDerivAt |>.fderiv).trans (sub_self _)
lemma toll_nice (G : Gauge) : ContDiffAt ℝ ω (ringTone G) 1 := G.focus_diff.sub (tollMat G).contDiff.contDiffAt
lemma tolled (G : Gauge) (u) : tollMat G (tollMat G u)=tollMat G u := G.lie.starProjection_eq_self_iff.mpr (G.lie.starProjection_apply_mem _)

def chorusF (P : Patch) (U : CoverConfig G) (i) := G.mat (choirCap P U i)
def affray (P : Patch) (U : CoverConfig G) (v : TPair P) (i : Lattice.Order) := star (G.mat (travel U v.1.val (route v.1.val v.2.val i)))
def echoes (P : Patch) (U : CoverConfig G) (v : TPair P) := (balcony Lattice.Order).partakes (fun i => affray P U v i)
def jury (P : Patch) (U : CoverConfig G) := (balcony P.Points).partakes (chorusF P U)
def cymbal (P : Patch) (U : CoverConfig G) (x : P.Points) := (balcony P.Points).partakes (fun i => chorusF P U i *(echoes P U (x,i)-1))
def tuning (P : Patch) (U : CoverConfig G) (x : P.Points) := (Pressure.Road.pairs P U).feedback (choirCap P U) x
lemma tuning_eq (U : CoverConfig G) (x : P.Points) : tuning P U x=jury P U+cymbal P U x := by
  unfold tuning YM.Branch.Pairs.feedback Pressure.Road.pairs
  rw [jury,cymbal,← Audience.partakes_add]; unfold partakes; unfold Branch.avg; simp_rw [balcony,smul_sum]; refine sum_congr rfl fun i _ => ?_
  have he (v : Lattice.Order→G.Mat) (q : G.Mat) : ∑ j : Lattice.Order,(balcony Lattice.Order).weight j • (q*v j) = q*((balcony Lattice.Order).partakes v) := by
    simp only [partakes,Finset.mul_sum,mul_smul_comm]
  rw [← smul_sum]; apply congr_arg
  simp_rw [G.mat_mul,G.mat_inv]; unfold chorusF
  change ∑ j : Lattice.Order,(balcony Lattice.Order).weight j • (G.mat (choirCap P U i)*affray P U (x,i) j)=_
  rw [show ∑ j : Lattice.Order,_=G.mat (choirCap P U i)*echoes P U (x,i) from he (affray P U (x,i)) _]
  rw [mul_sub,mul_one]; abel

lemma frequent (P : Audience α) (a : α→X→G.Mat) (h : ∀ i,ContinuousAt (a i) 0) : ContinuousAt (fun x => P.partakes (fun i => a i x)) 0 := by
  refine tendsto_finsetSum _ (fun i _ => ?_); exact ContinuousAt.tendsto ((h i).const_smul (P.weight i))
include h p hp
lemma chorus_eq : ∀ᶠ z in 𝓝 0, ∀ i, chorusF P (U z) i=bell G (tuning P (U z) i) := by
  have hx (v : TPair P) (b) : ContinuousAt (fun z => affray P (U z) v b) 0 := by
    let F (T : CoverConfig G) := travel T v.1.val (route v.1.val v.2.val b)
    exact (G.continuous_mat.continuousAt.comp ((show Continuous F from continuous_travel _ _).continuousAt.comp p.cont)).star
  have ht : Army (choirCap P ∘ U) 0 := cap_thaw h p hp
  have hi i : Tendsto (fun z => tuning P (U z) i) (𝓝 0) (𝓝 1) := by
    have hy a : echoes P (U 0) a=1 := by simp [hp, echoes, affray,Pressure.one]
    have he : tuning P (U 0) i=1 := by
      simp_rw [tuning_eq,jury,cymbal,hy]
      rw [show chorusF P (U 0)=(fun _ => 1) by funext i; simp [hp,chorusF,cap_ground h]]
      simp
    rw [← he]; change ContinuousAt _ _
    simp_rw [tuning_eq]
    refine ContinuousAt.add (frequent (balcony P.Points) (fun j z => chorusF P (U z) j) (fun j => (ht j).continuousAt)) (frequent (balcony P.Points) (fun j z => chorusF P (U z) j*(echoes P (U z) (i,j)-1)) (fun j => ((ht j).continuousAt).mul ?_))
    exact (frequent (balcony Lattice.Order) (fun b z => affray P (U z) (i,j) b) (hx (i,j))).sub continuousAt_const
  refine eventually_all.mpr fun i => ?_
  filter_upwards [min_applies (P:=P) (K:=K) p hp,(hi i).eventually G.nearest_is_focus] with z hv hg
  have he := Pressure.Road.strips P K (U z) hv (P.center,1) (fun _ => 1)
  rw [show Lattice.gauge (fun _ => 1) (U z)=U z from funext fun x => by simp [Lattice.gauge]] at he
  let W := Pressure.Road.pairs P (U z)
  have hS : W.Solves (P.selected (U z)) := by simpa only [W,Patch.frame,if_pos hv,inv_one,mul_one] using he
  have hs : W.Solves (choirCap P (U z)) := fun x => by
    change W.cost (fun i => (entryCap P (U z))⁻¹ * P.selected (U z) i) ≤ _; rw [W.moves]; exact hS x
  exact congr_arg G.mat (hg _ (W.self_consistent hs _))
lemma chorus_normal : ∀ᶠ z in 𝓝 0,(salon P).partakes (fun i => tollMat G (chorusF P (U z) i))=tollMat G 1 := by
  have ht : Tendsto (entryHat P∘U) (𝓝 0) (𝓝 1) := by
    have he := (cap_sensation h p hp).continuousAt.tendsto; rw [show (entryHat P ∘ U) 0=1 by simp [hp, entry_zero h]] at he; exact he
  filter_upwards [ht.eventually (onward_focus G)] with z hz
  let c := entryCap P (U z)
  have he : (salon P).partakes (chorusF P (U z))=G.mat c⁻¹*entryHat P (U z) := by unfold partakes; simp [c, chorusF,choirCap,entryHat,partakes,mul_smul_comm,Finset.mul_sum]
  rw [partakes]
  rw [show ∑ i : P.Points,_= tollMat G ((salon P).partakes (chorusF P (U z))) from (by simp only [partakes,map_sum,map_smul]) ,he,G.mat_inv]
  have ht := G.nearest_normal (u:=c) (X:=entryHat P (U z)) hz
  have hy : G.lie.starProjection (star (G.mat c)*entryHat P (U z)-1)=0 := G.lie.starProjection_apply_eq_zero_iff.mpr ht
  rw [map_sub] at hy; exact sub_eq_zero.mp hy

omit p hp h in
def solo (P : Patch) (U : CoverConfig G) (i : P.Points) : G.Mat := tollMat G (cymbal P U i)+ringTone G (tuning P U i)
lemma chorus_compute : ∀ᶠ z in 𝓝 0, ∀ i, chorusF P (U z) i = (tollMat G 1-(salon P).partakes (fun j => tollMat G (solo P (U z) j)))+solo P (U z) i := by
  filter_upwards [chorus_eq h p hp, chorus_normal h p hp] with z hz ht
  let d := tollMat G (jury P (U z))
  have he j : chorusF P (U z) j=d+solo P (U z) j := by rw [hz,solo,ringTone]; simp only [tuning_eq,map_add]; unfold d; abel
  have hx : (salon P).partakes (fun i => tollMat G (chorusF P (U z) i))=d+(salon P).partakes (fun j => tollMat G (solo P (U z) j)) := by simp_rw [he,map_add,partakes_add,partakes_still]; rw [show tollMat G d=d from tolled G _]
  intro i; rw [hx] at ht; rw [he, ← ht, add_sub_cancel_right]
end YM.Stationary
end

/-!
# Pre-L Gallop for canonical centered frames; no K-cost at positive
Taylor order here. Patch-calc order bounded BEFORE ratio. No loss of
lattice powers due to the shared mean. `subbass` is an induction in harmonic
order and makes no uniform continuation claim for individual reps.
-/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Audience Exterior Precision Bloch Wilson Laurent Matrix Finset
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {α β : Type} [Fintype α] [Fintype β] {X Y Z : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z] {G : Gauge} {P : Patch} {n m : ℕ} {R : X→ℕ→Prop} {K : KernelChoices} {C D F : ℝ} {A : Audience α} {B : Audience β}
variable {U : X→CoverConfig G}

lemma pre_final {f : α→X→Y} (h : Gallop A R f m C) (hp : Tested A R f (m+1) D) (hd : 0≤D) : Gallop A R f (m+1) (C+D) := ⟨h.listen, add_nonneg h.stamp hd, fun j hu hx => by
    by_cases H : j=m+1
    · subst j; exact hp.raises (le_add_of_nonneg_left h.stamp)
    exact (h.reaches j hu (by omega)).raises (le_add_of_nonneg_right hd)⟩
lemma all_average {f : α→X→Y} (h : Gallop A R f m C) : Gallop B R (fun _ x => A.partakes (fun i => f i x)) m C := h.rightS.shares (v:=fun _ i => f i)
lemma varying_average [Nonempty β] {f : β→α→X→Y} (h : ∀ i,Gallop A R (f i) m C) : Gallop A R (fun i x => B.partakes (fun j => f j i x)) m C := by
  have he (j : β) := (h j).splitS (B.weight j)
  simp_rw [Real.norm_eq_abs, abs_of_nonneg (B.wage _)] at he
  unfold Audience.partakes
  have ht (s : Finset β) : Gallop A R (fun i x => ∑ j∈s, B.weight j • f j i x) m (∑ j∈s,B.weight j*C) := by
    classical
    induction s using Finset.induction with
    | empty => simp; apply Gallop.goes (c:=fun _ => (0:Y)) le_rfl
    | insert j s hs ih => simpa only [sum_insert hs] using (he j).doubles ih
  simpa only [← Finset.sum_mul,B.enough,one_mul] using ht univ

section math

-- product f*(g-1), only m f derivatives.
def finale (G : Gauge) (M : ℝ) (D : ℝ) (m : ℕ) := choirSquare G M D 1 0 m + (D + apollo (chomp G.Mat) 0 (M+D) (m+1))
lemma finale_reach {f g : α→X→G.Mat} (h : Gallop A R f m C) (q : Gallop A R g (m+1) D) (hp : ∀ i,f i 0=1) (hu : ∀ i,g i 0=1) : Gallop A R (fun i x => f i x*(g i x-1)) (m+1) (finale G C D m) := by
  let F i x := g i x-1
  have hF : Gallop A R F (m+1) D := q.leans _
  have hZ : ∀ i,F i 0=0 := by simp [F,hu]
  apply pre_final (A:=A) (f:=fun i x => f i x*F i x) (square_sing h (hF.raises (by omega) le_rfl) hp hZ) ?_ (add_nonneg q.stamp (apollo_pos _ _ (add_nonneg h.stamp q.stamp) _))
  let M := chomp G.Mat
  let Y i x := f i x-1
  have he : Gallop A R Y m C := h.leans _
  have ha := streak he (D:=D) (μ:=1) (f:=Y) (g:=F) (by rw [one_mul]; exact hF.raises (by omega) le_rfl) (by simp [Y,hp]) hZ (by norm_num)
  simp only [one_mul] at ha
  have hx (i) (x) : f i x * F i x= F i x + Y i x*F i x := by unfold Y; rw [sub_mul,one_mul]; abel
  simp_rw [hx]
  exact Tested.plus hF.listen (fun i => (he.listen i).mul (hF.listen i)) (hF.reaches _ (Nat.zero_lt_succ _) le_rfl) ha

lemma echoes_cost (h : Singer P R U n C) (hp : U 0=1) : Gallop (balcony (TPair P)) R (fun i x => echoes P (U x) i) n (aria G P.J n C 4) :=
    varying_average (f:=fun o i x => affray P (U x) i o) (fun o => by
      rw [← show (allAxes o).length=4 by simp [allAxes]]; exact Gallop.notes_star G (singer_axes h hp (allAxes o) ((List.nodup_finRange _).map o.injective)))

lemma toll_fee {F : α → X→G.Mat} (h : Gallop A R F m C) : Gallop A R (fun i => tollMat G ∘ F i) m C := by
  refine ⟨(h.line (tollMat G)).listen,h.stamp,fun k hp hx u b hb ht => (h.reaches k hp hx u b hb ht).softer ?_⟩
  intro i
  have he : iteratedFDeriv ℝ k (tollMat G ∘ F i) 0 u=tollMat G (iteratedFDeriv ℝ k (F i) 0 u) := DFunLike.congr_fun ((tollMat G).iteratedFDeriv_comp_left (h.listen i) le_top) u
  rw [he]; exact G.lie.norm_starProjection_apply_le _
def bass (G : Gauge) (C D : ℝ) (m : ℕ) := let p := finale G C D m; p+(encore (ringTone G) 1 (C+p) m + apollo (ringTone G) 1 (C+p) (m+1))
lemma bass_cost (h : Gallop (balcony P.Points) R (fun i x => chorusF P (U x) i) m C) (p : P.Branches K G) (hp : U 0=1)
    (hx : Gallop (balcony (TPair P)) R (fun i x => echoes P (U x) i) (m+1) D) : Gallop (balcony P.Points) R (fun i x => solo P (U x) i) (m+1) (bass G C D m) := by
  let A := balcony P.Points
  let L i x := cymbal P (U x) i
  let w := finale G C D m
  have hi i : echoes P (U 0) i=1 := by simp [echoes,hp,affray,Pressure.one]
  have hB i : chorusF P (U 0) i=1 := by simp [hp,chorusF,cap_ground p]
  rw [show balcony (TPair P)=A.circus A from balcony_circus.symm] at hx
  have he : Gallop A R L (m+1) w := Gallop.shares (A:=A) (B:=A) (v:=fun i j x => chorusF P (U x) j*(echoes P (U x) (i,j)-1)) (finale_reach h.rightS hx (fun i => hB _) hi)
  let T i x := tuning P (U x) i
  have hu : Gallop A R (fun _ x => jury P (U x)) m C := all_average h
  have ht : Gallop A R T m (C+w) := (hu.doubles (he.raises (by omega) le_rfl)).renew (fun i => Eventually.of_forall fun x => tuning_eq ..)
  have hX i : T i 0=1 := by
    unfold T; rw [tuning_eq]; unfold jury cymbal; rw [show chorusF P (U 0)=(fun _ => 1) from funext hB]; simp only [hi]; simp
  unfold bass; dsimp only
  exact (toll_fee he).doubles (pre_final (ht.comp hX (toll_nice G)) (tested_lite (toll_nice G) ht hX (toll_first G)) (apollo_pos _ _ ht.stamp _))

def subbass (G : Gauge) (j : ℕ) (C : ℝ) : ℕ → ℝ
    | 0 => 0
    | m+1 => let c := bass G (subbass G j C m) (aria G j (m+1) C 4) m; portrait j*(c)+c
lemma pre_choir (h : P.Branches K G) (p : Army U 0) (hp : U 0=1) (ht : Singer P R U m C) : Gallop (balcony P.Points) R (fun i x => chorusF P (U x) i) m (subbass G P.J C m) := by
  let A := balcony P.Points
  induction m with
  | zero => exact Gallop.blank (fun i => cap_thaw h p hp i) le_rfl
  | succ m ih =>
    have he := bass_cost (ih (fun i => (ht i).raises (by omega) le_rfl)) h hp (echoes_cost ht hp)
    let c := bass G (subbass G P.J C m) (aria G P.J (m+1) C 4) m
    have hx : Gallop A R (fun _ x => (salon P).partakes (fun i => tollMat G (solo P (U x) i))) (m+1) (portrait P.J * (c)) := all_average ((toll_fee he).budget (painted P.J) (salon_stamp P))
    have hq := ((Gallop.goes (A:=A) (fun _ => tollMat G 1) le_rfl).minuses hx).doubles he
    rw [zero_add] at hq; exact hq.renew (fun i => (chorus_compute h p hp).mono fun _ hz => hz i)
end math
end YM.Stationary
end
