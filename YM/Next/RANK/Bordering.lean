import YM.Next.RANK.Porter
import YM.Work.F05.Actions

/-! Path monomials and mask changes; use native tests. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Alarm
open Function Filter RG Thirst Baler Lattice Wilson Finset MeasureTheory Relation Corona Value Glyph Marker PathData
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side} {p q : BudgetPoint} {r : ℕ}
variable {C : Clip} {t τ μ A σ Λ : ℝ}
variable (P : PathData G)

-- any moving threshold

lemma sail (r : ℝ) (X : Support n) {V : Type*} [Zero V] (F : Config G n→ V) (hx : LocalOn X F) : LocalOn (halo 8 X) (masked r X F) := by
  intro U V hp
  have hh := flags_agree r U V X (agrees_mono hp (fun _ h=>inspect X h)); have h : Healthy r X U ↔ Healthy r X V := by simp only [Healthy,disjoint_iff_inter_eq_empty,hh]
  by_cases ht : Healthy r X U
  · rw [masked_eq _ _ _ _ ht,masked_eq _ _ _ _ (h.1 ht)]; exact hx U V (agrees_mono hp (fun _ hx=>halo_subset _ X hx))
  rw [masked_ne _ _ _ _ ht,masked_ne _ _ _ _ (mt h.2 ht)]
lemma sails (r : ℝ) (X : Support n) {V : Type*} [Zero V] (F : Config G n→ V) (hx : GaugeInvariant F) : GaugeInvariant (masked r X F):= by
  intro k U; have he : Healthy r X (Lattice.gauge k U) ↔ Healthy r X U:=by rw [Healthy, Healthy,gauge_flags]
  by_cases h : Healthy r X U
  · rw [masked_eq _ _ _ _ (he.2 h),masked_eq _ _ _ _ h,hx k U]
  rw [masked_ne _ _ _ _ (mt he.1 h),masked_ne _ _ _ _ h]
lemma awake_mask (X : Support n) {V : Type*} [AddCommGroup V] (F : Config G n→V) (h : τ ≤ t) (U) (hx : Healthy τ (halo 8 X) U) : masked t X F U -masked τ X F U=0:= by
  have he : Healthy τ X U:=Disjoint.mono_left (halo_subset _ _) hx; rw [masked_eq _ _ _ _ (threshold_fit _ _ h _ he),masked_eq _ _ _ _ he,sub_self]

def home (B : Atom G r) (p q : BudgetPoint) (U : Config G n):=B.placed p U 0-B.placed q U 0
lemma unmasked_space (B : Atom G r) (x : Site n) : LocalOn (B.footprint x) (fun U=> B.unmasked U x):= by
  intro U V hp
  apply congr_arg B.poly; ext1 i
  refine LocalOn.expandAt (B.leg i|>.stencil) (B.leg i|>.eval) (Slot.covered (B.leg i)) x U V (agrees_mono hp fun y hy=> ?_)
  obtain ⟨c,hc,rfl⟩:=hy; exact mem_image_of_mem (fun p=> wrap n p+x) (Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hc⟩))
lemma atom_loc (B : Atom G r) (p q : BudgetPoint) : LocalOn (halo 8 (B.footprint (0:Site n))) (home (n:=n) B p q) := by
  intro U V hp; apply congr_arg₂ (·-·); exacts [(sail _ _ _ (unmasked_space B _) U V hp),(sail _ _ _ (unmasked_space B _) U V hp)]
lemma scorn (B : Atom G r) (p : BudgetPoint) (hb : B.Invariant) (x : Site n) : GaugeInvariant (fun U=> B.placed p U x):= by
  apply sails; intro i U; simp only [Atom.unmasked, Work.F05.slot_gauge]; exact hb ..

def centum (P : Atom G r) (p q : BudgetPoint) (h : P.Invariant) (he : q.threshold ≤ p.threshold) : Wickless G n q.threshold where
  extent:= halo 8 (P.footprint 0)
  active:= ⟨0,halo_subset _ _ (stationed 0 r P)⟩
  value:=home P p q
  inv i U:=congr_arg₂ (·-·) (scorn P p h _ i U) (scorn P q h _ i U)
  meas:=Measurable.sub (masked_measurable _ _ _ ((P.unmasked_cont _).measurable)) (masked_measurable _ _ _ ((P.unmasked_cont _).measurable))
  sees U V x _:= atom_loc P p q U V x
  untouched:=by intro U hh; exact awake_mask _ _ he U hh

lemma level (F : ℕ → Atom G r) (p q : BudgetPoint) (hσ : 0<σ) (hb : SumBudget (fun i=> (F i).budget σ) A) (ha : ∀ i,(F i).Invariant)
    (hp : q.threshold ≤ p.threshold) (U : Config G n) : atomGift F p q U=∑' i,(centum (F i) p q (ha i) hp).value U :=
  ((atom_dominated F p 0 hσ hb).summable U|>.tsum_sub ((atom_dominated F q 0 hσ hb).summable U)).symm

private lemma billable (B : Atom G r) (e : ℝ) (he : 0≤e) (h : 8 ≤ q.B) (hσ : 200000*e ≤ σ * q.B) :
    B.magnitude*Thirst.debt q.B e (halo 8 (B.footprint (0:Site n)))≤ B.budget σ * Real.exp (200000*e*(r+2)) := by
  let M:=q.B; let X:= B.footprint (0:Site n)
  have hh : M*coverNumber M (halo 8 X) ≤ 100000*(M+B.length+(r+1)) := by
    apply (widen 1 M 8 (by decide) q.B_pos h X).trans; rw [one_mul]; apply Nat.mul_le_mul_left; have hz:=landed (0:Site n) r B; change coverNumber 1 X≤ _ at hz; omega
  have hz : debt M e (halo 8 X) ≤ Real.exp (σ*B.length) * Real.exp (200000*e*(r+2)):= by
    unfold debt; rw [←Real.exp_add]; apply Real.exp_le_exp.mpr
    have hy : 1 ≤ M:= q.B_pos; let c:ℝ:= r
    have ht := mul_le_mul_of_nonneg_left (show (M:ℝ)*coverNumber M (halo 8 X) ≤ 100000*(M+B.length + (c+1)) by dsimp only [c]; exact_mod_cast hh) he
    have hp := mul_le_mul_of_nonneg_right hσ (Nat.cast_nonneg B.length); change _ ≤ σ*M*_ at hp
    change _≤ σ*B.length+200000*e*(c+2)
    have he₁ : 1≤(M:ℝ):= by exact_mod_cast hy
    apply le_of_mul_le_mul_left _ (zero_lt_one.trans_le he₁)
    dsimp only [c] at *; linarith only [ht,hp, he, mul_nonneg he (Nat.cast_nonneg r), mul_le_mul_of_nonneg_right he₁ he,mul_le_mul_of_nonneg_right he₁ (mul_nonneg he (Nat.cast_nonneg r)),mul_nonneg (zero_le_one.trans he₁) he, mul_nonneg he (Nat.cast_nonneg B.length)]
  rw [Atom.budget,mul_assoc]; apply mul_le_mul_of_nonneg_left hz; unfold Atom.magnitude; positivity

def sourceCharge (r : ℕ) (e m t : ℝ):= m*t^r*Real.exp (200000*e*(r+2))
lemma cent_cost (F : ℕ → Atom G r) (p q : BudgetPoint) (hb : SumBudget (fun i=> (F i).budget σ) A) (ha : ∀ i,(F i).Invariant)
    (hp : q.threshold ≤ p.threshold) (hq : 8 ≤ q.B) (e : ℝ) (he : 0≤e) (hσ : 200000*e ≤ σ * q.B) :
    Dial (fun i=>centum (F i) p q (ha i) hp (n:=n)) q e (2*sourceCharge r e A p.threshold) := by
  let X:= fun i=>centum (F i) p q (ha i) hp (n:=n)
  let f i:=2*(F i).magnitude *p.threshold^r
  let g i:=f i*Thirst.debt q.B e (X i).extent
  have hh i: 0 ≤ f i:= by have hp:=p.threshold_pos; unfold f Atom.magnitude; positivity
  have hg i: 0≤g i:= mul_nonneg (hh i) (Real.exp_pos _).le
  let C:= Real.exp (200000*e*(r+2)); let w:=2*p.threshold^r
  have hW : 0≤w := mul_nonneg (by norm_num) (pow_nonneg p.threshold_pos.le _)
  have ht (i) : g i ≤ w*C*(F i).budget σ := by
    change 2*_ * _ * debt q.B _ _ ≤ _
    have hs := billable (F i) e he hq hσ (n:=n); change _*debt _ _ (X i).extent≤ _ * C at hs
    have hp:=mul_le_mul_of_nonneg_left hs hW; dsimp only [w] at *; linarith only [hp]
  have Hv:= hb.2.1.mul_left (w*C)
  have hz:=Hv.of_nonneg_of_le hg ht
  refine ⟨fun i=>halo_subset _ _ (stationed ..),f,fun i=>⟨hh _,fun U=> ?_⟩,hg,hz,?_⟩
  · change |_ - _| ≤ f i
    apply (abs_sub ..).trans
    have h₁:= healthy_atom (F i) p U (0:Site n); have h₂:= healthy_atom (F i) q U (0:Site n)
    unfold f; linarith only [h₁,h₂,mul_le_mul_of_nonneg_left (pow_le_pow_left₀ q.threshold_pos.le hp r) (show 0 ≤ (F i).magnitude by unfold Atom.magnitude; positivity)]
  apply (hz.tsum_le_tsum ht Hv).trans; rw [tsum_mul_left]; apply (mul_le_mul_of_nonneg_left hb.2.2 (mul_nonneg hW (Real.exp_pos _).le)).trans
  dsimp only [w,C]; unfold sourceCharge; linarith only
end YM.Next.Rank.Alarm
