import YM.Planned.STATIONARY_JET_PORT.Jets
import YM.Push.STATIONARY_UNIFORM.Touch

set_option warningAsError false

/-! Two ended localized analytic jet algebra. -/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.JetPort
open Push.Uniform Filter Function Set Metric Lattice Matrix
open scoped Topology ContDiff BigOperators Classical
variable {n : Side}

/-- Distance to another fixed differentiated leg, if using one. -/
def reel (o : Option (Site n)) (x : Site n) : ℕ := o.elim 0 (separation x)
def thread (o : Option (Site n)) (a : ℝ) (x : Site n) := Real.exp (-a*reel o x)
lemma thread_pos (o : Option (Site n)) (a : ℝ) (x : Site n) : 0<thread o a x := Real.exp_pos _
lemma thread_le (o : Option (Site n)) {a : ℝ} (ha : 0 ≤ a) (x : Site n) : thread o a x ≤ 1 :=
  Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha) (Nat.cast_nonneg _))
lemma thread_mono (o : Option (Site n)) {a r : ℝ} (hr : r ≤ a) (x : Site n) : thread o a x ≤ thread o r x :=
  Real.exp_monotone (mul_le_mul_of_nonneg_right (neg_le_neg hr) (by positivity))
@[simp] lemma thread_none (a : ℝ) (x : Site n) : thread none a x = 1 := by simp [thread,reel]
lemma thread_leg (x : Site n) (a : ℝ) (y : Site n) : thread (some x) a y = Decay a y x := rfl
lemma decay_mono {a r : ℝ} (hr : r ≤ a) (x y : Site n) : Decay a x y ≤ Decay r x y :=
  Real.exp_monotone (mul_le_mul_of_nonneg_right (neg_le_neg hr) (by positivity))
lemma decay_div (a : ℝ) (x y : Site n) : Decay a x y = Decay (a/2) x y * Decay (a/2) x y := by
  unfold Decay; rw [← Real.exp_add]; congr 1; ring
lemma glaze_snoc {ι : Type} {k : ℕ} (l : ι → Site n) (q : Fin k → ι) (d : ι) (y) (a : ℝ) :
    glaze l y (Fin.snoc (α:=fun _ : Fin (k+1) => ι) q d) a = Decay a y (l d) * glaze l y q a := by
  unfold glaze Decay spanSites; rw [Fin.sum_univ_castSucc]; simp only [Fin.snoc_castSucc,Fin.snoc_last, Nat.cast_add,mul_add,Real.exp_add]; rw [mul_comm]
lemma glaze_last {ι : Type} {k : ℕ} (l : ι → Site n) (q : Fin (k+1) → ι) (y) (a : ℝ) :
    glaze l y q a = Decay a y (l (q (Fin.last k))) * glaze l y (fun i : Fin k => q i.castSucc) a := by
  unfold glaze Decay spanSites; rw [Fin.sum_univ_castSucc]; simp only [Nat.cast_add,mul_add,Real.exp_add]; rw [mul_comm]

def slip (N : ℕ) (a : ℝ) := a/(2*(N+2 : ℝ))
lemma slip_pos (N : ℕ) {a : ℝ} (ha : 0<a) : 0<slip N a := by unfold slip; positivity
lemma slip_le (N : ℕ) {a : ℝ} (ha : 0 ≤ a) : slip N a ≤ a := by
  apply div_le_self ha; have : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg _; linarith

/-- Transport the entire old bound of the second factor to the first row:
up to N derivative positions, its other end and optionally one more position
for an already differentiated leg. -/
lemma tow {ι : Type} (l : ι → Site n) (x y z : Site n) (o : Option (Site n)) {N k : ℕ} (hk : k ≤ N) (q : Fin k → ι)
    {a : ℝ} (ha : 0<a) :
    Decay (a/2) x y * (Decay a y z * thread o a y * glaze l y q a) ≤
      Decay (slip N a) x z * thread o (slip N a) x * glaze l x q (slip N a) := by
  let D := separation x y
  let s (x : Site n) := separation x z + reel o x + spanSites l x q
  have ht : spanSites l x q ≤ N*D + spanSites l y q := by
    calc
      _ ≤ ∑ i, (D+separation y (l (q i))) := Finset.sum_le_sum fun i _ => separation_triangle ..
      _ ≤ _ := by
        rw [Finset.sum_add_distrib]; unfold spanSites
        apply Nat.add_le_add_right _ _
        simpa [Finset.sum_const,nsmul_eq_mul] using Nat.mul_le_mul_right D hk
  have he : reel o x ≤ D+reel o y := by
    cases o
    · simp [reel]
    · exact separation_triangle ..
  have hs : s x ≤ (N+2)*D + s y := by
    have hz : separation x z ≤ D+separation y z := separation_triangle ..
    unfold s; rw [add_mul]; omega
  have hx : (s x : ℝ) ≤ (N+2:ℝ)*D + s y := by exact_mod_cast hs
  have hu : slip N a*(N+2:ℝ)=a/2 := by unfold slip; field_simp
  have hh : slip N a * (s x : ℝ) ≤ a/2*D+a*(s y:ℝ) := by
    refine (mul_le_mul_of_nonneg_left hx (slip_pos N ha).le).trans ?_
    rw [mul_add,← mul_assoc,hu]
    exact add_le_add_right (mul_le_mul_of_nonneg_right (slip_le N ha.le) (Nat.cast_nonneg _)) _
  unfold Decay thread glaze
  simp_rw [← Real.exp_add]; apply Real.exp_monotone
  unfold s D at hh; push_cast at hh
  linarith only [hh]

/-- Combine the extra costs, keep at most one thread. -/
def splice {α : Type} (o p : Option α) : Option α := o.elim p some
lemma spool (o e : Option (Site n)) {a : ℝ} (ha : 0 ≤ a) (x : Site n) :
    thread o a x * thread e a x ≤ thread (splice o e) a x := by
  cases o
  · simp [splice]
  exact mul_le_of_le_one_right (thread_pos ..).le (thread_le e ha x)

variable {ι τ σ π : Type} [Fintype ι] {l : ι → Site n} {m : τ → Site n} {u : σ → Site n}
    {v : π → Site n} {N K : ℕ} {a r C D : ℝ} {o e : Option (Site n)}
    {F : Positions ι → Matrix τ σ ℝ} {p : Positions ι}

def Cable (l : ι → Site n) (m : τ → Site n) (u : σ → Site n) (o : Option (Site n)) (a : ℝ) (N : ℕ)
    (F : Positions ι → Matrix τ σ ℝ) (p : Positions ι) (C : ℝ) : Prop :=
  ∀ (i : τ) (j : σ), Beacon l a N (fun x => F x i j) (m i) p (C*Decay a (m i) (u j)*thread o a (m i))

def bornMatrix (F : Positions ι → Matrix τ σ ℝ) (p : Positions ι) := ∀ (i : τ) (j : σ), ContDiffAt ℝ ω (fun x => F x i j) p

lemma Cable.paid {k : ℕ} (h : Cable l m u o a N F p C) (i j) (q : Fin k → ι) (hk : k ≤ N) :
    ‖entry (fun x => F x i j) p q‖ ≤ C*(Decay a (m i) (u j)*thread o a (m i)*glaze l (m i) q a) :=
  (h i j k hk q).trans_eq (by unfold glaze; ring)

lemma Cable.cost (h : Cable l m u o a N F p C) (ht : C ≤ D) : Cable l m u o a N F p D := by
  intro i j; exact (h i j).mono (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ht (decay_pos ..).le)
    (thread_pos ..).le)
lemma Cable.rate (h : Cable l m u o a N F p C) (hc : 0 ≤ C) (hr : r ≤ a) : Cable l m u o r N F p C := by
  intro i j k hk q; refine (h i j k hk q).trans ?_
  change _ * glaze _ _ _ _ ≤ _ * glaze _ _ _ _
  refine mul_le_mul ?_ (glaze_mono _ _ _ hr) (Real.exp_pos _).le ?_
  · exact mul_le_mul (mul_le_mul_of_nonneg_left (decay_mono hr _ _) hc) (thread_mono _ hr _) (thread_pos ..).le
      (mul_nonneg hc (decay_pos ..).le)
  exact mul_nonneg (mul_nonneg hc (decay_pos ..).le) (thread_pos ..).le

lemma Cable.germ (h : Cable l m u o a N F p C) {G : Positions ι → Matrix τ σ ℝ} (he : F =ᶠ[𝓝 p] G) :
    Cable l m u o a N G p C := by
  intro i j k hk q; rw [show entry (fun x => G x i j) p q = entry (fun x => F x i j) p q from ?_]
  · exact h i j _ hk _
  have ht : (fun x => G x i j) =ᶠ[𝓝 p] (fun x => F x i j) := he.symm.mono fun x hx => by dsimp only; rw [hx]
  unfold entry; rw [(ht.iteratedFDeriv ℝ k).eq_of_nhds]
lemma Cable.scale (hF : bornMatrix F p) (h : Cable l m u o a N F p C) (b : ℝ) :
    Cable l m u o a N (fun x => b • F x) p (|b| *C) := by
  intro i j; simpa only [mul_assoc,Matrix.smul_apply] using beacon_scale b (hF i j) (h i j)
lemma Cable.neg (hF : bornMatrix F p) (h : Cable l m u o a N F p C) :
    Cable l m u o a N (fun x => -(F x)) p C := by simpa using h.scale hF (-1)

def conductor (N K : ℕ) (a : ℝ) := fusion N*(1+(K:ℝ)*countCost (a/2))
lemma conductor_pos (N K : ℕ) {a : ℝ} (ha : 0<a) : 0 < conductor N K a :=
  mul_pos fusion_pos (by have ht := count_pos (half_pos ha); positivity)

section Multiply
variable [Fintype σ] {G : Positions ι → Matrix σ π ℝ}

lemma bornMatrix.multiply (hF : bornMatrix F p) (hG : bornMatrix G p) :
    bornMatrix (fun x => F x * G x) p := fun i j => by
  simp_rw [Matrix.mul_apply]; exact ContDiffAt.sum fun k _ => (hF i k).mul (hG k j)

lemma Cable.multiply (hF : bornMatrix F p) (hG : bornMatrix G p)
    (h : Cable l m u o a N F p C) (H : Cable l u v e a N G p D) (ha : 0<a) (hc : 0<C) (hd : 0<D)
    (hm : Multiplicity u K) :
    Cable l m v (splice o e) (slip N a) N (fun x => F x * G x) p (C*D*conductor N K a) := by
  intro i k
  let s := slip N a; let x := m i; let z := v k
  let B := thread (splice o e) s x
  let E := Decay s x z
  let Z j := Decay (a/2) x (u j)
  let bill j := C*D*fusion N * Z j * E * B
  have hh j : Beacon l s N (fun y => F y i j) x p (C*Decay a x (u j) * thread o s x) := by
    intro k hk q
    apply (h i j k hk q).trans
    change C*Decay a x _ * thread o a x * glaze l x q a ≤ _*glaze l x q s
    refine mul_le_mul (mul_le_mul_of_nonneg_left (thread_mono _ (slip_le N ha.le) _) (mul_nonneg hc.le (decay_pos ..).le))
      (glaze_mono _ _ _ (slip_le N ha.le)) (Real.exp_pos _).le ?_
    exact mul_nonneg (mul_nonneg hc.le (decay_pos ..).le) (thread_pos ..).le
  have hg j : Beacon l s N (fun y => G y j k) x p (D*(Z j)⁻¹*E*thread e s x) := by
    intro k' hk' q
    apply (H.paid j k q hk').trans
    have ht : 0 < Z j := decay_pos ..
    have he := tow l x (u j) z e hk' q ha
    change Z j * _ ≤ E * thread e s x * glaze l x q s at he
    have hw := mul_le_mul_of_nonneg_left he (mul_nonneg hd.le (inv_pos.mpr ht).le)
    rw [← mul_assoc, mul_assoc D (Z j)⁻¹, inv_mul_cancel₀ ht.ne',mul_one] at hw
    simpa only [glaze,x,z,Z,E,mul_assoc] using hw
  simp_rw [Matrix.mul_apply]
  refine (beacon_sum (s:=Finset.univ) (C:=bill) (fun j _ => (beacon_mul (hF i j) (hG j k)
    (hh j) (hg j) (mul_pos (mul_pos hc (decay_pos ..)) (thread_pos ..)) (mul_pos
      (mul_pos (mul_pos hd (inv_pos.mpr (decay_pos ..))) (decay_pos ..)) (thread_pos ..))).mono ?_)
    (fun j _ => (hF i j).mul (hG j k))).mono ?_
  · have ht : 0 < Z j := decay_pos ..
    have he : thread o s x * thread e s x ≤ B := spool o e (slip_pos N ha).le x
    rw [decay_div a x (u j)]
    have hv := mul_le_mul_of_nonneg_left he (show 0 ≤ C*D*fusion N * Z j * E from by
      have : 0 < E := decay_pos ..
      have hz := fusion_pos (N:=N); positivity)
    unfold bill; change fusion N * (C * (Z j * Z j) * thread o s x) * _ ≤ _
    apply le_trans (le_of_eq ?_) hv
    field_simp
  · have ht := hm.count u (half_pos ha) x
    calc
      ∑ j, bill j = C*D*fusion N * (∑ j, Z j) * E * B := by
        unfold bill; rw [← Finset.sum_mul,← Finset.sum_mul,← Finset.mul_sum]
      _ ≤ C*D*fusion N * (1+(K:ℝ)*countCost (a/2))*E*B := by
        have hz : 0 < E := decay_pos ..
        have hy : 0 < B := thread_pos ..
        have H : 0 < fusion N := fusion_pos
        gcongr
        exact ht.trans (le_add_of_nonneg_left zero_le_one)
      _ = _ := by unfold conductor E B x z s; ring
end Multiply
end YM.Planned.JetPort
