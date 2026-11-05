import YM.RemainderComparison.Gaussian.Treasury
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Prism.Glisten

/-!
# Taylor precision with actual normalization. REAL; F(x,X) model at
 open halo, A(x) actual projection around ONE point, with aperture at
 that point. Keep same probes before projection.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Exchange
open Function Filter Set Metric MeasureTheory Finset Germ Trace
open Lattice RG Push.AbsoluteSums Pressure Next.Scheduling
open ConnectedActivityE6 Blaze Brush PhysicalNext.Repeat Lantern
open scoped Topology ENNReal ContDiff BigOperators Classical Interval
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {j k n : ℕ} {g A B d v u C : ℝ}
variable {x:E} 
local notation "Xs" => ℝ×E

/-- Proxy before truncating composition algebra. -/
structure Queue (U : ℝ×E→F) (P : E→F) (g : ℝ) (x:E) (v u : ℝ) (j k : ℕ) (C : ℝ) : Prop where
  cost : 0≤C
  site : (g,x)∈Germ.patch E v u
  coupling : 0 < g
  scope : ∀ z∈Germ.patch E v u, Brush (j+(k+1)) C 1 U z
  return' : Brush j (g^(k+1) * C) 1 (fun y=> P y-U (g,y)) x
local notation "d'" => g^(k+1)
variable {P P' : E→F} {U U' : ℝ×E→F}
namespace Queue

lemma grows (h : Queue U P g x v u j k A) (hp : A ≤ B) : Queue U P g x v u j k B :=
  ⟨h.cost.trans hp,h.site,h.coupling,fun z hz=> (h.scope z hz).climb hp le_rfl, h.return'.climb (mul_le_mul_of_nonneg_left hp (pow_nonneg h.coupling.le _)) le_rfl⟩
lemma rough (h : Queue U P g x v u j k A) (hp : g ≤ 1) : Brush j (A+A) 1 P x := by
  have ht : Brush j A 1 (fun y=> U (g,y)) x:= Trace.trace_arc ((h.scope _ h.site).smaller (by omega))
  have hh := (h.return'.climb (mul_le_of_le_one_left h.cost (pow_le_one₀ h.coupling.le hp)) le_rfl).gathering ht
  exact hh.shimmy (Eventually.of_forall fun y=> by simp)
lemma projects [FiniteDimensional ℝ E] [CompleteSpace F] [SecondCountableTopology F] (h : Queue U P g x v u j k A) :
    Brush j (g^(k+1) * (A+A)) 1 (fun y=> P y - Trace.trunc k U (g,y)) x := by
  have hh := Trace.vertically U k ((show ∀ᶠ y in 𝓝 (g,x), y∈ Germ.patch E v u from (patch_open ..).mem_nhds h.site).mono (fun i hi t ht=> h.scope _ (Germ.keeps hi ht)))
  rw [abs_of_pos h.coupling] at hh
  rw [mul_add]; exact (h.return'.gathering hh).shimmy (Eventually.of_forall (fun i=> by simp))
lemma constant (e:F) (hx : (g,x)∈ Germ.patch E v u) (he: 0<g) : Queue (fun _=>e) (fun _=>e) g x v u j k ‖e‖ := by
  refine ⟨norm_nonneg _, hx, he, fun _ _=> Brush.certified zero_le_one _, ?_⟩
  simp only [sub_self]
  exact (Brush.certified zero_le_one _).climb (by rw [norm_zero]; positivity) le_rfl
lemma adds (h : Queue U P g x v u j k A) (he : Queue U' P' g x v u j k B) : Queue (U+U') (P+P') g x v u j k (A+B) := by
  refine ⟨ add_nonneg h.cost he.cost,h.site,h.coupling, fun z hz=> (h.scope z hz).gathering (he.scope z hz), ?_⟩
  rw [mul_add]; exact (h.return'.gathering he.return').shimmy (Eventually.of_forall fun i=> by simp; abel)
lemma sub_fit (h : Queue U P g x v u j k A) (he : Queue U' P' g x v u j k B) : Queue (U-U') (P-P') g x v u j k (A+B):= by
  refine ⟨ add_nonneg h.cost he.cost,h.site,h.coupling, fun z hz=> (h.scope z hz).separating (he.scope z hz), ?_⟩
  rw [mul_add]; exact (h.return'.separating he.return').shimmy (Eventually.of_forall fun i=> by simp; abel)

def tfee (j _ : ℕ) (A B : ℝ):= A*(B+B)*3^j+A*B*3^j
def productPrice (j k : ℕ) (A B : ℝ):= A*B*3^(j+(k+1))+tfee j k A B
lemma productQ {K : ℝ×E→ℝ} {k':E→ℝ} (h : Queue K k' g x v u j k A) (hf : Queue U P g x v u j k B) (hp : g ≤ 1) :
    Queue (fun i=> K i • U i) (fun i=> k' i • P i) g x v u j k (productPrice j k A B) := by
  have hA:=h.cost; have hB:=hf.cost; let q:=A*B*3^(j+(k+1)); let p:=tfee j k A B
  have hq : 0 ≤ q:= by unfold q; positivity
  have hp':0≤p:= by unfold p tfee; positivity
  have hk := (h.scope _ h.site)
  refine ⟨add_nonneg hq hp', h.site,h.coupling, fun i hi => (Trace.paint (h.scope i hi) (hf.scope i hi)).climb (le_add_of_nonneg_right hp') le_rfl,?_⟩
  have hh := (Trace.paint h.return' (hf.rough hp)).gathering (Trace.paint (Trace.trace_arc (hk.smaller (show j ≤ j+(k+1) by omega))) hf.return')
  apply (hh.climb _ le_rfl).shimmy ; swap
  · change _ ≤ _ * (q+p); refine le_trans (b:=g^(k+1)*p) (le_of_eq ?_) (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hq) (pow_nonneg h.coupling.le _)); unfold p tfee; ring
  filter_upwards with i; simp only [sub_smul,smul_sub]; abel
lemma transfer_err (h : Queue U P g x v u j k A) {B' : E→F} (ht:B' =ᶠ[𝓝 x] P) : Queue U B' g x v u j k A := ⟨h.cost,h.site,h.coupling,h.scope,h.return'.shimmy (ht.sub (EventuallyEq.refl _ _))⟩
end Queue

section scalar
variable {U : ℝ×E→ℝ} {P:E→ℝ} (h : Queue U P g x v u j k A) (hp : ∀ y∈ Germ.patch E v u,U y∈ Set.Icc (1/2:ℝ) 2)
variable (H:∀ z∈Set.Icc (1/4:ℝ) 3, Brush (j+(k+1)) C 1 (fun i:ℝ=> i⁻¹) z)

include hp h
lemma chase (he:d'* A ≤ 1/4) : P x∈ Set.Icc (1/4:ℝ) 3 := by
  obtain ⟨hu,hv⟩:=hp _ h.site; obtain ⟨hl,hh⟩:= abs_le.mp (h.return'.bound.trans he); constructor <;> linarith
include H
local notation "J" => j+(k+1)
local notation "σ" => Lantern.clump (j+(k+1)) A C
lemma stand : ∀ w∈Germ.patch E v u, Brush (j+(k+1)) σ 1 (fun y=> (U y)⁻¹) w:= fun w hw=> by
  obtain ⟨he,hh⟩:=hp w hw; exact Lantern.composite (h.scope _ hw) (H _ (show _ from ⟨le_trans (by norm_num) he, le_trans hh (by norm_num)⟩))

def inverse_fee (j k : ℕ) (A C : ℝ) := clump (j+(k+1)) A C+(clump j (A+A) C*A*3^j*clump (j+(k+1)) A C)*3^j

lemma inverse_at (he:d'*A ≤ 1/4) (hg : g≤1) : Queue (fun x => (U x)⁻¹) (fun i=> (P i)⁻¹) g x v u j k (inverse_fee j k A C) := by
  have hw := h.site; have h₀:=h.coupling
  let f y:=U (g,y); let s:=σ; let p:= clump j (A+A) C; let B:=p*A*3^j*s*3^j
  have hc:0 ≤ C:= (H 1 (by norm_num)).nonneg; have ht:= h.cost
  have hs:0 ≤ s:= by unfold s Lantern.clump; positivity
  have ht':0≤p:= by unfold p Lantern.clump; positivity
  have hB: 0≤B:=by unfold B; positivity
  have hF : Brush j A 1 f x:= Trace.trace_arc ((h.scope _ hw).smaller (by omega))
  have hh:= chase h hp he; have hf' := stand h hp H
  have hh' : P x ≠0:= (show 0<P x by linarith only [hh.1]).ne'
  have hy: U (g,x)>0:= lt_of_lt_of_le (by norm_num) (hp _ hw).1
  refine ⟨ add_nonneg hs hB,hw,h₀,fun i hi=> (hf' i hi).climb (le_add_of_nonneg_right hB) le_rfl,?_⟩
  have hφ: Brush j (clump j (A+A) C) 1 (fun i=> (P i)⁻¹) x:= Lantern.composite (h.rough hg) ((H _ hh).smaller (by omega))
  have hU: Brush j s 1 (fun i=> (f i)⁻¹) x:= Trace.trace_arc ((hf' _ hw).smaller (by omega))
  have heq : ∀ᶠ i in 𝓝 x, P i≠0 ∧ f i≠0:= ((h.rough hg).smooth.continuousAt.eventually_ne hh').and (hF.smooth.continuousAt.eventually_ne hy.ne')
  have he := (Trace.paint (Trace.paint hφ h.return') hU)
  refine ((he.climb ?_ le_rfl).opposite).shimmy ?_
  · change _ ≤ _*(s+B); refine le_trans (b:=d'*B) (le_of_eq ?_) (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hs) (pow_nonneg h.coupling.le _)); unfold B p s; ring
  filter_upwards [heq] with i ⟨h1,h2⟩
  change (P i)⁻¹-(f i)⁻¹= -((P i)⁻¹*(P i-f i)*(f i)⁻¹)
  field_simp; ring

def lf (j k : ℕ) (A C D m : ℝ) := clump (j+(k+1)) A D + m*(A*clump (j+(k+1)) A C*3^j)
lemma logs (he : d'*A ≤ 1/4) (hb:d'*A*(clump (j+(k+1)) A C)*3^j ≤ 1/2)
    (hm: Prism.Anthem j) (hL : ∀ y∈Set.Icc (1/2:ℝ) 2, Brush (j+(k+1)) B 1 Real.log y) (hg:g≤1) : Queue (Real.log ∘ U) (Real.log ∘ P) g x v u j k (lf j k A C B hm.logE) := by
  have hw := h.site; have hA:= h.cost; have h₀:=h.coupling
  let B':=clump J A B; let f y:=U (g,y); let y z:=P z/f z; let p':=hm.logE*(A*σ*3^j)
  have ht := stand h hp H _ hw; have hs := ht.nonneg; have hF : Brush j A 1 f x := Trace.trace_arc ((h.scope _ hw).smaller (by omega))
  have ha : Brush j σ 1 (fun i=> (f i)⁻¹) x:= Trace.trace_arc (ht.smaller (by omega)); have hK i (hi:i∈Germ.patch E v u): Brush J B' 1 (Real.log ∘ U) i:= Lantern.composite (h.scope _ hi) (hL _ (hp i hi))
  have hy: f x≠0:=(show 0<f x from lt_of_lt_of_le (by norm_num : (0:ℝ)<1/2) (hp _ hw).1).ne'
  have he' := chase h hp he; have hQ:P x≠0:=(show 0<P x from lt_of_lt_of_le (by norm_num : (0:ℝ)<1/4) he'.1).ne'
  have hC := (hK _ hw).nonneg
  have hh:0≤p':=by have hx:= hm.plus; unfold p'; positivity
  refine ⟨add_nonneg hC hh,hw,h.coupling,fun i hi=> (hK i hi).climb (le_add_of_nonneg_right hh) le_rfl,?_⟩
  have heq : ∀ᶠ i in 𝓝 x, f i≠0 ∧ P i≠0:= (hF.smooth.continuousAt.eventually_ne hy).and ((h.rough hg).smooth.continuousAt.eventually_ne hQ)
  have hr : Brush j (d'*A*σ*3^j) 1 (fun z=> y z-1) x:= by
    refine (Trace.paint h.return' ha).shimmy ?_
    filter_upwards [heq] with i ⟨hi,_⟩; change P i/f i-1=(P i-f i)*(f i)⁻¹; field_simp
  refine ((hm.treat E x _ y hr hb).climb ?_ le_rfl).shimmy ?_
  · change _ ≤ d'*(B'+p'); refine le_trans (le_of_eq (b:=d'*p') ?_) (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hC) (pow_pos h.coupling _).le)
    unfold p'; ring
  filter_upwards [heq] with i hi using (Real.log_div hi.2 hi.1).symm
end scalar
end YM.RemainderComparison.Exchange
