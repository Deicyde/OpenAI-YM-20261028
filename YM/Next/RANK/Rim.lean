import YM.Next.RANK.BoundParticle
import YM.Next.RANK.Scars


/-!
# Covariance factor and stencil budgets from two-field lookup

Assume exact real discrete *full* data supported at lattice sites. K estimates
relative to `arcs` (Taylor projection of continuum covariance). Prove simultaneous
factor for the endpoint port (no orientation quotient needed at seams).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Beamer
open Lattice CellsInt Function Configuration Labels Rise Particle Common Finset Normal
open scoped Classical Topology BigOperators

variable {G : Gauge} {d n k T : ℕ} {A B : Type*} {S : Type*}

variable (d) (f : S → Address G) (r : ℝ)

def arbor (i : KeyIn G d) : Horizon G := (r^generation i.val)⁻¹ • tester i.val
lemma overhead (i : KeyIn G d) : shutter (arbor d r i) := shut_scale _ _ (shutters (axes G _ _))

def arc (C : KeyIn G d → KeyIn G d → ℝ) : Bridge G := ∑ i, ∑ j,C i j •
    (fun x y => arbor d r i x * arbor d r j y)

private lemma turnstile (C : KeyIn G d → KeyIn G d → ℝ) : (fun i j => arc d r C j i)= arc d r (fun i j => C j i) := by
  unfold arc; ext i j
  simp only [Pi.smul_apply,Finset.sum_apply,smul_eq_mul]; rw [sum_comm]; exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => congr_arg (C _ _ * ·) (mul_comm ..)
lemma choke (C : KeyIn G d → KeyIn G d → ℝ) (x : Address G) : shutter (fun y => arc d r C x y) := by
  have he : (fun y => arc d r C x y) = ∑ i : KeyIn G d, ∑ j : KeyIn G d,C i j • (arbor d r i x • arbor d r j) := by funext y; simp only [arc,Finset.sum_apply, Pi.smul_apply,smul_eq_mul]
  rw [he]
  exact (signal G).sum_mem fun i _ => (signal G).sum_mem fun j _ => (signal G).smul_mem _ ((signal G).smul_mem _ (overhead d r j))
lemma chokes (C : KeyIn G d → KeyIn G d → ℝ) (x : Address G) : shutter (fun y => arc d r C y x) := by
  have he : (fun y => arc d r C y x)=arc d r (fun i j => C j i) x := congr_fun (turnstile d r C) x
  rw [he]; exact choke d r _ x

-- weights for lifted factor
def fixedKey (x : S) (i : KeyIn G d) := ((arbor d r i (f x)):ℂ)
def features (x : S) : KeyIn G d⊕S →₀ ℂ := ∑ i : KeyIn G d, Finsupp.single (Sum.inl i) (fixedKey d f r x i)+
    Finsupp.single (.inr x) (((r:ℂ)^(d+1))⁻¹)

lemma weighted (u : KeyIn G d⊕S → ℝ) (x : S) : Finsupp.linearCombination ℂ (fun i : KeyIn G d ⊕ S => (u i:ℂ)) (features d f r x) =
    (↑((∑ i : KeyIn G d,arbor d r i (f x)*u (.inl i))+(r^(d+1))⁻¹*u (.inr x)) : ℂ) := by
  simp [features, fixedKey,Finsupp.linearCombination_single]

lemma proves (hr : 0<r) (u : Horizon G) (x : S) :
    Finsupp.linearCombination ℂ (fun i => ((passcode f r d i u):ℂ)) (features d f r x) = (u (f x) : ℂ) := by
  rw [weighted]
  simp_rw [item,stub]
  have he (k) : arbor d r k (f x)*(r^generation k.val* predicts k u)=predicts k u*tester (G:=G) k.val (f x) := by unfold arbor; rw [Pi.smul_apply,smul_eq_mul]; field_simp
  simp_rw [he]; apply congr_arg (fun z : ℝ => (z:ℂ)); rw [← Beamer.clouds]
  rw [← mul_assoc (r^_)⁻¹, inv_mul_cancel₀ (by positivity), one_mul,Pi.sub_apply,add_sub_cancel]

lemma exact_fee (C : KeyIn G d → KeyIn G d → ℝ) (u v : KeyIn G d⊕S) (hr : 0 < r) :
    mourn (passcode f r d u) (passcode f r d v) (arc d r C) = ∑ i : KeyIn G d, ∑ j : KeyIn G d,
      C i j * ((if u=.inl i then 1 else 0)*(if v=.inl j then 1 else 0)) := by
  let a := passcode f r d u;let b := passcode f r d v
  unfold arc; simp_rw [map_sum,map_smul]; refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  simp only [smul_eq_mul]; congr 1
  change a (fun x => b (fun y => arbor d r i x* arbor d r j y))=_
  rw [show (fun x => b (fun y => arbor d r i x*arbor d r j y))=(b (arbor d r j)) • (arbor d r i) from funext fun x => by
    change b (arbor d r i x • arbor d r j)=_*_; rw [map_smul,smul_eq_mul,mul_comm]]
  rw [map_smul, smul_eq_mul,show a (arbor d r i)=_ from testPass f r d i u hr,show b (arbor d r j)=_ from testPass f r d j v hr,mul_comm]

section
variable (Γ : Fin n → Fin n → Bridge G) (μ : Fin n→ Horizon G)
variable (H : ∀ i j, ∀ x y, Γ i j x y=Γ j i y x)

def prize : Normal.Symmetric (Fin n × S) where
  cov x y:= Γ x.1 y.1 (f x.2) (f y.2)
  symm i j := congr_arg (fun a : ℝ => (a:ℂ)) (H i.1 j.1 _ _)

def primary : Normal.Symmetric (Fin n × (KeyIn G d ⊕ S)) where
  cov x y := mourn (passcode f r d x.2) (passcode f r d y.2) (Γ x.1 y.1)
  symm x y := congr_arg (fun a : ℝ => (a:ℂ)) (by
    rw [moves _ _ _ (bright_pass f r ..),show (fun i j => Γ x.1 y.1 j i)=Γ y.1 x.1 from funext fun i => funext fun j => H ..])

def seen : Fin n × (KeyIn G d⊕ S) → ℂ := fun i => (passcode f r d i.2 (μ i.1):ℂ)

lemma scanned (i : Fin n × S) (hr : 0<r) : Normal.reads (perSlot (fun _ => features d f r)) (seen d f r μ) i = μ i.1 (f i.2) := by
  unfold reads perSlot; rw [Finsupp.linearCombination_mapDomain]; exact proves d f r hr (μ i.1) i.2
lemma shaped (hr : 0<r) : scope (perSlot (fun _ => features d f r)) (primary d f r Γ H) = prize f Γ H := by
  apply Normal.Symmetric.ext; funext i j
  let Q := primary d f r Γ H
  let M := fun _ : Fin n => features d f r
  let D := perSlot M
  change Finsupp.linearCombination ℂ (Finsupp.linearCombination ℂ Q.cov (Finsupp.mapDomain _ (M i.1 i.2))) (Finsupp.mapDomain _ (M j.1 j.2))=(Γ i.1 j.1 (f i.2) (f j.2):ℂ)
  rw [Finsupp.linearCombination_mapDomain,Finsupp.linearCombination_mapDomain]
  let F := Γ i.1 j.1
  have hz (p) : (Finsupp.linearCombination ℂ (Q.cov ∘ (fun a => (i.1,a))) (M i.1 i.2)) (j.1,p)=(passcode f r d p (F (f i.2)):ℂ) := by
    change (LinearMap.proj (R:=ℂ) (φ:=fun _ => ℂ) (j.1,p)) (Finsupp.linearCombination ℂ (Q.cov ∘ (fun a => (i.1,a))) (M i.1 i.2))=_
    rw [LinearMap.map_finsupp_linearCombination]; exact proves d f r hr (fun x => passcode f r d p (F x)) i.2
  rw [show (Finsupp.linearCombination ℂ (Q.cov ∘ fun a => (i.1,a)) _ : Fin n × (KeyIn G d ⊕ S) → ℂ) ∘ (fun b => (j.1,b)) = _ from funext hz]; exact proves d f r hr (F (f i.2)) j.2
end
end YM.Next.Rank.Beamer
