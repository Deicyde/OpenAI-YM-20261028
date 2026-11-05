import YM.RG08.UV.Ledger
import YM.RG08.Action.Primo
/-!
# Mesh domains. `Y(k,Z)` includes reference shifts. Families over ANY
 announced UV windows with uniform funding (incl moving onset at reporting
scale). Neither constants nor gains are for per-cutoff tailored shapes. -/
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
noncomputable section
namespace YM.RG08
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG
open scoped BigOperators Topology Real Classical
variable {I J : Type} {y v w δ h : I→ℝ} {p : J→ℝ} {α β : I→Type} {r : ℕ}

lemma Weighed.transfer (hk : Weighed y h) (f : J→I): Weighed (fun i=> y (f i)) (fun i=> h (f i)) :=
  ⟨_,_,hk.choose_spec.choose_spec.1,fun i=> hk.choose_spec.choose_spec.2 (f i)⟩
lemma Weighed.sway (he : Weighed y h) (hg : Audience y)(hx : Weighed h v) : Weighed y v := by
  obtain ⟨C,l,hC,H⟩:=hx; exact ((Weighed.constant y hC).times (he.powers l)).mono (fun i=> (H i).1) (fun i=> (H i).2)
lemma Voucher.mold {U : ∀ i,Shale (α i) r} (he : Voucher y δ U w) (f : J→I) : Voucher (fun i=> y (f i)) (fun i=>δ (f i)) (fun i=> U (f i)) (fun i=> w (f i)) := ⟨_,he.choose_spec.1.transfer f,fun b=>he.choose_spec.2 (f b)⟩
lemma Voucher.age {U : ∀ i, Shale (α i) r} (hv : Voucher v δ U w)(h : Weighed y v) (hp : Audience y) : Voucher y δ U w := ⟨_,h.sway hp hv.choose_spec.1,hv.choose_spec.2⟩
lemma Voucher.subsume {U : ∀ i, Shale (α i) r} (hv : Voucher y (v*δ) U w) (h : Weighed y v) : Voucher y δ U w := ⟨_,hv.choose_spec.1.times h,fun i=> by simpa only [Pi.mul_apply,mul_assoc] using hv.choose_spec.2 i⟩
lemma NutWallet.move {P:I→Patch} {G : Gauge} {ν : G.ColorIndex} {D : ChartRatio G} {κ : KernelChoices} {E : ℕ} (hx : NutWallet P ν D κ E y v) (f : J→I) : NutWallet (fun i=> P (f i)) ν D κ E (fun i=> y (f i)) (fun i=> v (f i)) := ⟨fun i=> hx.pos _,fun i=>hx.small _,hx.crop.transfer f, fun j hj k hk=> (hx.post j hj k hk).transfer f⟩

structure Windows where
  start : ℕ
  k : ℕ
  Z : ℝ
  pos : 0 ≤ Z
structure Launch (u : I→Windows) where
  b : I
  i : ℕ
  geC : (u b).start ≤ i
structure Wings (u : I→Windows) (k : ℕ) extends Launch u where
  N : ℕ
  M : ℕ
  cut : i+k ≤ N
  side : N ≤ M
variable {u : I→Windows} (X : Chain)

def Launch.farY (t : Launch u) := age X.S (u t.b).Z (u t.b).k t.i
lemma Launch.you : Audience (Launch.farY X (u:=u)) := fun t=>age_one (u t.b).pos ..
abbrev Wings.menu (t : Wings u r) := t.toLaunch.farY X
abbrev Wings.chop (θ : ℝ) (t : Wings u r) := gain X.S θ t.i t.N
@[simp] lemma Wings.a_zero : Wings.chop (u:=u) (r:=r) X 0=1 := by funext t; simp [Wings.chop,gain]
lemma Wings.sh : Audience (Wings.menu (u:=u) (r:=r) X) := fun i=> Launch.you ..

namespace Wings

def up (t : Wings u 1) : Wings u 0 := ⟨⟨t.b,t.i+1,t.geC.trans (Nat.le_succ _)⟩,t.N,t.M,t.cut,t.side⟩
def low (t : Wings u 1) : Wings u 0 := ⟨t.toLaunch,t.N,t.M, Nat.le_trans (Nat.le_succ _) t.cut,t.side⟩
def wingR (t : Wings u r) : Wings u r := {t with N:=t.M, cut := t.cut.trans t.side,side:=le_rfl}
def roof (t : Wings u 0) : Wings u 0 := {t with i:=t.N,geC:=t.geC.trans t.cut,cut:= le_rfl}
lemma aged_up (h : Weighed (Launch.farY (u:=u) X) (fun i=> ((X.S.block i.i).val:ℝ))) : Weighed (Wings.menu (r:=1) (u:=u) X) (fun t:Wings u 1 => t.up.menu X) := by
  let L t:= ((X.S.block (t:Wings u 1).i).val:ℝ)
  let y : Wings u 1→ℝ:=menu X
  have hv : Weighed y L:= h.transfer toLaunch
  have hp : Weighed y y := by simpa only [pow_one] using Weighed.power y (Wings.sh _) 1
  refine (hp.times hv).mono (fun i=> zero_le_one.trans (sh X _)) (fun i=> le_trans (age_larger (u i.b).pos (u i.b).k (S:=X.S) (i:=i.i) (Nat.le_succ _)) ?_)
  have hx : 0<L i:= Nat.cast_pos.mpr (X.S.block i.i).property
  have he:=Real.add_one_le_exp (Real.log (L i)); rw [Real.exp_log hx,add_comm] at he
  exact mul_le_mul_of_nonneg_left (by rw [show i.up.i=i.i+1 from rfl,X.S.scale_succ _,add_sub_cancel_left]; exact he) (hp.positive i)
lemma continued' (θ : ℝ) (h : θ≤1) (i : Wings u 1) : Wings.chop X θ i.up ≤ (X.S.block i.i).val * Wings.chop X θ i := by
  let L:= ((X.S.block i.i).val:ℝ); have he : 0<L:=Nat.cast_pos.mpr (X.S.block i.i).property
  have hL : 0 ≤ Real.log L:= Real.log_nonneg (by unfold L; exact_mod_cast (X.S.block i.i).property)
  unfold Wings.chop gain; change Real.exp _ ≤ L*Real.exp _
  rw [← Real.exp_log he,← Real.exp_add]; apply Real.exp_monotone
  change (-θ)*(X.S.scale i.N-X.S.scale (i.i+1))≤_
  rw [X.S.scale_succ]; change (-θ)*(X.S.scale i.N-(X.S.scale i.i+Real.log L))≤_; nlinarith

lemma receipt (h : Weighed (Launch.farY (u:=u) X) (fun i=> ((X.S.block i.i).val:ℝ))) {α : Type} {V : Wings u 0 → Shale α r} {σ:Wings u 0→ℝ} {θ : ℝ}(hp : θ ≤ 1)(he : Voucher (menu X) (Wings.chop X θ) V σ) : Voucher (Wings.menu X) (Wings.chop X θ) (fun i:Wings u 1=> V i.up) (fun i => σ i.up) :=
    (((he.mold up).age (aged_up X h) (Wings.sh X)).raise (show _ ≤ (fun i:Wings u 1=> ((X.S.block i.i).val:ℝ))*Wings.chop X θ from continued' X _ hp)).subsume (h.transfer toLaunch)

-- Long propagation structure only. D applied with TRUE gain i->i+1.
variable {F : Wings u 0→ Shale I r}
structure Presses {α : Type} (F : Wings u 0→Shale α r)(θ:ℝ)(σ : ℕ→ℝ) : Prop where
    top : Voucher (fun i=> i.roof.menu X) 1 (fun i:Wings u 0=>F i.roof) (fun i=>σ i.N)
    beat : ∃ R : Wings u 1 → Shale α r, Voucher (menu X) (Wings.chop X θ) ((fun i:Wings u 1=> F i.low) - R) (fun i=>σ i.i) ∧
       ∀ i D, Glow (F i.up) (σ (i.i+1)) D → Glow (R i) (σ i.i) (D*gain X.S (1/2) i.i (i.i+1))
lemma pathway {α : Type} {F : Wings u 0→Shale α r} {θ : ℝ} {σ} (h : Presses X F θ σ) (he : θ ≤ 1/4) : Voucher (menu X) (Wings.chop X θ) F (fun i=>σ i.i) := by
  obtain ⟨⟨C,⟨E,p,hE,H₀⟩,hx⟩,R,⟨W,⟨B,s,hB,hC⟩,hp⟩,hv⟩ := h
  let A:=E+B; have hh:0≤A:=add_nonneg hE hB
  obtain ⟨D,hD,H⟩:= solve_bed _ he _ hh (max p s)
  refine ⟨_,(Weighed.constant (menu X) hD).times (Weighed.powers (show Weighed (menu X) (menu X) from ?_) (max p s)),fun i=>?_⟩
  · simpa only [pow_one] using Weighed.power (menu (u:=u) (r:=0) X) (Wings.sh X) 1
  let G l (hL : (u i.b).start ≤ l) (ha:l ≤ i.N) : Wings u 0:= {i with i:=l, geC:=hL,cut:=ha}
  let T l D:=∀ h₁ h₂,Glow (F (G l h₁ h₂)) (σ l) D
  apply (H X.S (u i.b).pos (u i.b).start i.N (u i.b).k T (i.geC.trans i.cut) ?_ ?_ ?_ i.i i.geC i.cut i.geC i.cut)
  · intro k hk he x ht w hw h₁ h₂; exact glow_less (ht _ _) le_rfl hw
  · intro hL ha; have hs := (H₀ i).2; have hy : E ≤ A:=le_add_of_nonneg_right hB
    refine glow_less (hx i) le_rfl ?_
    simp only [Pi.one_apply,mul_one]; apply hs.trans; change E* (i.roof.menu X)^p≤ A*(i.roof.menu X)^(max p s)
    have hg : 1 ≤ i.roof.menu X:= sh X _; gcongr; exact le_max_left ..
  intro k h₁ h₂ v hv' hP hh
  let l : Wings u 1:=⟨⟨i.b,k,h₁⟩,i.N,i.M,h₂,i.side⟩
  have hr : Glow (F l.low-R l) (σ k) (W l*chop X θ l):=hp l
  have hz := hv l v (hv' l.up.geC l.cut)
  have hS:= hz.add hr (fun i=> (ling_pos _ _).le); rw [add_sub_cancel] at hS
  apply glow_less hS le_rfl; apply add_le_add (le_refl _); change W l*chop X θ l ≤ A*l.menu X ^ (max p s)*chop X θ l -- parentheses
  apply mul_le_mul_of_nonneg_right _ (gain_pos ..).le; apply (hC l).2.trans; have hy : 1 ≤ l.menu X:= sh X l; have hh:B ≤ A:= le_add_of_nonneg_left hE; gcongr; exact le_max_right ..
end Wings
end YM.RG08
